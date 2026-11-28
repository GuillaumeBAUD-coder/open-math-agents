import OMAStatements.S_oeis_a185089
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.LinearCombination

/-!
The Narayana sum is a coefficient of a quadratic polynomial power.
An Euler derivative gives a recurrence for the central coefficients of
those powers, hence for the Little Schröder numbers. Applying their moment
functional to the Fibonacci-type profile gives the transformed recurrence.
-/

namespace OMA.S_oeis_a185089

open Finset Polynomial

private abbrev R := ℤ[X]

private noncomputable def P : R := 1+3*Polynomial.X+2*Polynomial.X^2

private noncomputable def J2 : R := Polynomial.C 2*Polynomial.X+1

private theorem j2_coeff (n k : ℕ) : (J2^n).coeff k = (2:ℤ)^k*(n.choose k:ℤ) := by
  induction n generalizing k with
  | zero =>
    cases k <;> simp [Polynomial.coeff_one]
  | succ n ih =>
    rw [pow_succ' J2, show J2*J2^n = Polynomial.C 2*Polynomial.X*J2^n+J2^n by
      nth_rw 1 [J2]
      rw [add_mul,one_mul], coeff_add, mul_assoc, coeff_C_mul]
    cases k with
    | zero => simp [coeff_X_mul_zero, ih]
    | succ k =>
      rw [coeff_X_mul, ih, ih, Nat.choose_succ_succ]
      push_cast
      rw [pow_succ]
      ring

private theorem numerator_dvd (m k : ℕ) (hk : 1 ≤ k) :
    m ∣ m.choose k * m.choose (k-1) := by
  cases m with
  | zero =>
    have h : 0 < k := by omega
    rw [Nat.choose_eq_zero_of_lt h, zero_mul]
  | succ m =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => simp [Nat.choose_one_right]
      | succ k =>
        have h1 := congrArg (fun v : ℕ => (v : ℤ)) (Nat.succ_mul_choose_eq m (k+1))
        have h2 := congrArg (fun v : ℕ => (v : ℤ)) (Nat.succ_mul_choose_eq m k)
        push_cast at h1 h2
        have hd : ((m+1 : ℕ) : ℤ) ∣
            ((m+1).choose (k+2) : ℤ) * ((m+1).choose (k+1) : ℤ) := by
          refine ⟨(m.choose (k+1) : ℤ)*((m+1).choose (k+1) : ℤ) -
            (m.choose k : ℤ)*((m+1).choose (k+2) : ℤ), ?_⟩
          push_cast
          linear_combination -((m+1).choose (k+1) : ℤ)*h1 +
            ((m+1).choose (k+2) : ℤ)*h2
        exact_mod_cast hd

private theorem shifted_sum (m : ℕ) (f : ℕ → ℤ) :
    (∑ k ∈ Icc 1 m, f k) = ∑ k ∈ range m, f (k+1) := by
  let e : ℕ ↪ ℕ := ⟨fun k => k+1, by intro a b h; change a+1=b+1 at h; omega⟩
  have h : (range m).map e = Icc 1 m := by
    ext k
    rw [mem_map, mem_Icc]
    constructor
    · rintro ⟨i,hi,rfl⟩
      have hh := mem_range.1 hi
      change 1 ≤ i+1 ∧ i+1 ≤ m
      omega
    · rintro ⟨h1,h2⟩
      refine ⟨k-1, mem_range.2 (by omega), ?_⟩
      change k-1+1=k
      omega
  rw [←h, sum_map]
  rfl

private theorem schroeder_coeff (m : ℕ) (hm : 1 ≤ m) :
    (P^m).coeff (m-1) = (m:ℤ)*(s m:ℤ) := by
  have hP : P=J2*(1+Polynomial.X) := by
    unfold P J2
    rw [show Polynomial.C (2:ℤ) = 2 by exact map_ofNat Polynomial.C 2]
    ring
  rw [hP, mul_pow, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (J2^m).coeff i * ((1+Polynomial.X : R)^m).coeff j)]
  simp only [j2_coeff, Polynomial.coeff_one_add_X_pow]
  have hd : m ∣ ∑ k ∈ Icc 1 m, m.choose k*m.choose (k-1)*2^(k-1) := by
    apply dvd_sum
    intro k hk
    exact dvd_mul_of_dvd_left (numerator_dvd m k (mem_Icc.1 hk).1) _
  have hs : (m:ℤ)*(s m:ℤ) =
      (∑ k ∈ Icc 1 m, (m.choose k : ℤ)*(m.choose (k-1) : ℤ)*(2:ℤ)^(k-1)) := by
    have ht : m*s m = ∑ k ∈ Icc 1 m, m.choose k*m.choose (k-1)*2^(k-1) := by
      rw [s, if_neg (by omega), Nat.mul_div_cancel' hd]
    exact_mod_cast ht
  rw [hs, shifted_sum m, show (m-1).succ=m by omega]
  apply sum_congr rfl
  intro i hi
  have hi' := mem_range.mp hi
  have hb : m-1-i ≤ m := by omega
  rw [← Nat.choose_symm hb, show m-(m-1-i)=i+1 by omega, Nat.add_sub_cancel]
  ring


private noncomputable def b (m : ℕ) : ℤ := (P^m).coeff m

private theorem euler_zero (f : R) (k : ℕ) :
    (Polynomial.X * derivative f - Polynomial.C (k:ℤ)*f).coeff k = 0 := by
  cases k with
  | zero => simp [coeff_X_mul_zero]
  | succ k =>
    rw [coeff_sub, coeff_X_mul, coeff_derivative, coeff_C_mul]
    push_cast
    ring

private theorem central_rec (m : ℕ) :
    ((m:ℤ)+2)*b (m+2) = 3*(2*(m:ℤ)+3)*b (m+1) - ((m:ℤ)+1)*b m := by
  let H : R := 2*Polynomial.X^2-1
  let g := H*P^(m+1)
  have h :
      Polynomial.X * derivative g - Polynomial.C ((m:ℤ)+2)*g =
        Polynomial.C ((m:ℤ)+2)*P^(m+2) -
          Polynomial.C (3*(2*(m:ℤ)+3))*(Polynomial.X*P^(m+1)) +
          Polynomial.C ((m:ℤ)+1)*(Polynomial.X^2*P^m) := by
    unfold g
    rw [derivative_mul, derivative_pow_succ, pow_add P m 2, pow_add P m 1]
    simp only [P, H, derivative_mul, derivative_pow, derivative_one, derivative_ofNat,
      derivative_X, map_add, map_mul, map_sub, map_one, map_ofNat, Nat.cast_ofNat]
    ring
  have h0 := euler_zero g (m+2)
  rw [show ((m+2 : ℕ) : ℤ) = (m:ℤ)+2 by push_cast; rfl, h] at h0
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul, coeff_X_pow_mul, b] at h0
  unfold b
  linear_combination h0

private theorem neighbor_coeff (m : ℕ) :
    (P^(m+1)).coeff (m+2) = 2*(P^(m+1)).coeff m := by
  have h :=
    euler_zero (P^(m+2)) (m+2)
  have he :
      Polynomial.X * derivative (P^(m+2)) -
          Polynomial.C ((m+2 : ℕ) : ℤ)*P^(m+2) =
        Polynomial.C ((m+2 : ℕ) : ℤ) *
          (Polynomial.C 2 * (Polynomial.X^2*P^(m+1)) - P^(m+1)) := by
    rw [show m+2=(m+1)+1 by omega, derivative_pow_succ, pow_succ P (m+1)]
    simp only [P, derivative_mul, derivative_pow, derivative_one, derivative_ofNat,
      map_add, map_sub, map_mul, map_ofNat, map_one, map_natCast, derivative_X,
      Nat.cast_one, Nat.cast_add]
    ring
  rw [he, coeff_C_mul, coeff_sub, coeff_C_mul, coeff_X_pow_mul] at h
  have hh : ((m+2 : ℕ) : ℤ) ≠ 0 := by positivity
  have hz := (mul_eq_zero.mp h).resolve_left hh
  omega

private theorem schroeder_related (m : ℕ) :
    b (m+2)-3*b (m+1)=4*((m:ℤ)+1)*(s (m+1):ℤ) := by
  have h :=
    schroeder_coeff (m+1) (by omega)
  rw [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at h
  have he : b (m+2) = (P^(m+1)).coeff (m+2) +
      3*(P^(m+1)).coeff (m+1) + 2*(P^(m+1)).coeff m := by
    unfold b
    rw [show P^(m+2) = P*P^(m+1) by rw [pow_succ'], show P*P^(m+1) =
      P^(m+1)+Polynomial.C 3*(Polynomial.X*P^(m+1))+
        Polynomial.C 2*(Polynomial.X^2*P^(m+1)) by
          unfold P; simp only [map_ofNat]; ring]
    simp only [coeff_add, coeff_C_mul, coeff_X_mul, coeff_X_pow_mul]
  rw [neighbor_coeff] at he
  unfold b at *
  linear_combination he + 4*h

private theorem schroeder_rec (n : ℕ) (hn : 1 ≤ n) :
    ((n:ℤ)+2)*(s (n+1):ℤ) = 3*(2*(n:ℤ)+1)*(s n:ℤ) - ((n:ℤ)-1)*(s (n-1):ℤ) := by
  by_cases h : n=1
  · subst n
    decide +kernel
  · obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le (show 2≤n by omega)
    have hr0 := central_rec (m+1)
    have hr1 := central_rec (m+2)
    have hs0 := schroeder_related m
    have hs1 := schroeder_related (m+1)
    have hs2 := schroeder_related (m+2)
    have hne : 4*((m:ℤ)+2)*((m:ℤ)+3) ≠ 0 := by positivity
    simp only [Nat.add_comm 2 m, Nat.add_assoc, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
      show m+2-1=m+1 by omega] at *
    apply mul_left_cancel₀ hne
    linear_combination ((m:ℤ)+2)*hr1 - 3*((m:ℤ)+3)*hr0 -
      ((m:ℤ)+2)*((m:ℤ)+4)*hs2 + 3*(2*(m:ℤ)+5)*((m:ℤ)+3)*hs1 -
      ((m:ℤ)+2)*((m:ℤ)+3)*hs0


private noncomputable def profile : ℕ → R
  | 0 => 1
  | 1 => 1
  | n+2 => profile (n+1)+Polynomial.X*profile n

private theorem profile_coeff (n k : ℕ) :
    (profile n).coeff k = ((n-k).choose k : ℤ) := by
  induction n using Nat.strong_induction_on generalizing k with
  | h n ih =>
    cases n with
    | zero =>
      cases k <;> simp [profile, coeff_one]
    | succ n =>
      cases n with
      | zero =>
        cases k with
        | zero => simp [profile, coeff_one]
        | succ k => simp [profile, coeff_one, Nat.choose_eq_zero_of_lt]
      | succ n =>
        change (profile (n+2)).coeff k = (((n+2)-k).choose k : ℤ)
        rw [profile, coeff_add]
        cases k with
        | zero => rw [coeff_X_mul_zero, ih (n+1) (by omega)]; simp
        | succ k =>
          rw [coeff_X_mul, ih (n+1) (by omega), ih n (by omega)]
          by_cases hk : k ≤ n
          · rw [show n+1-(k+1)=n-k by omega, show n+2-(k+1)=(n-k)+1 by omega,
              Nat.choose_succ_succ, Nat.cast_add, add_comm]
          · have hh : k ≥ 1 := by omega
            rw [show n+1-(k+1)=0 by omega, show n-k=0 by omega,
              show n+2-(k+1)=0 by omega]
            simp [Nat.choose_eq_zero_of_lt (show 0<k by omega)]

private theorem profile_sum (n : ℕ) :
    profile n = ∑ k ∈ range (n/2+1), monomial k ((n-k).choose k : ℤ) := by
  apply Polynomial.ext
  intro k
  rw [profile_coeff, finset_sum_coeff]
  by_cases hk : k ∈ range (n/2+1)
  · rw [sum_eq_single_of_mem k hk]
    · simp
    · intro j _ hj
      simp [coeff_monomial, hj]
  · have hl : n-k<k := by have h := not_lt.1 (fun h => hk (mem_range.2 h)); omega
    rw [Nat.choose_eq_zero_of_lt hl, Nat.cast_zero]
    symm
    apply sum_eq_zero
    intro j hj
    have hne : k≠j := by intro h; exact hk (h ▸ hj)
    simp [coeff_monomial, hne.symm]

private noncomputable def M : R →ₗ[ℤ] ℤ := Polynomial.lsum (fun k => (s k:ℤ) • LinearMap.id)

private theorem M_monomial (k : ℕ) (c : ℤ) : M (monomial k c) = (s k:ℤ)*c := by
  simp [M, Polynomial.lsum, Finsupp.lsum_single, smul_eq_mul]

private theorem a_profile (n : ℕ) : (a n : ℤ) = M (profile n) := by
  rw [profile_sum, map_sum, a, Nat.cast_sum]
  apply sum_congr rfl
  intro k _
  rw [Nat.cast_mul, M_monomial, mul_comm]


private theorem M_divX_const (c : ℤ) : (monomial 0 c).divX = 0 := by
  apply Polynomial.ext
  intro k
  simp only [coeff_divX,coeff_monomial,coeff_zero, show (0:ℕ) ≠ k+1 by omega, if_false]

private theorem M_divX_succ (k : ℕ) (c : ℤ) : (monomial (k+1) c).divX = monomial k c := by
  apply Polynomial.ext
  intro j
  simp [coeff_divX, coeff_monomial]

private theorem moment (g : R) :
    M (((Polynomial.X^2-6*Polynomial.X+1)*derivative g) +
      (2*Polynomial.X-3)*g-g.divX) = -g.coeff 0 := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, map_sub, mul_add, Polynomial.divX_add, coeff_add] at hp hq ⊢
    linear_combination hp + hq
  | monomial k a =>
    rw [show (6 : R)=Polynomial.C 6 by exact (map_ofNat Polynomial.C 6).symm,
      show (2 : R)=Polynomial.C 2 by exact (map_ofNat Polynomial.C 2).symm,
      show (3 : R)=Polynomial.C 3 by exact (map_ofNat Polynomial.C 3).symm]
    cases k with
    | zero =>
      rw [M_divX_const, derivative_monomial]
      simp only [Nat.cast_zero, mul_zero, monomial_zero_right, zero_add, sub_zero,
        sub_mul, mul_assoc, Polynomial.X_mul_monomial, Polynomial.C_mul_monomial,
        map_sub, M_monomial, coeff_monomial, if_true]
      have h0 : s 0 = 1 := by decide +kernel
      have h1 : s 1 = 1 := by decide +kernel
      rw [h0,h1]
      ring
    | succ k =>
      rw [M_divX_succ, derivative_monomial_succ]
      simp only [sub_mul, add_mul, mul_assoc, one_mul, Polynomial.X_mul_monomial,
        Polynomial.X_pow_mul_monomial, Polynomial.C_mul_monomial, map_sub, map_add,
        M_monomial, coeff_monomial, show k+1 ≠ 0 by omega, if_false, neg_zero]
      have h := schroeder_rec (k+1) (by omega)
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] at h
      linear_combination a*h

private noncomputable def z : PowerSeries R := PowerSeries.X
private noncomputable def C (p : R) := PowerSeries.C (R := R) p
private noncomputable def cf (n : ℕ) := PowerSeries.coeff (R := R) n
private noncomputable def G : PowerSeries R := PowerSeries.mk profile
private noncomputable def Gz := PowerSeries.derivative R G
private noncomputable def Gy : PowerSeries R := PowerSeries.mk fun n => (profile n).derivative
private noncomputable def J : PowerSeries R := PowerSeries.mk fun _ => 1
private noncomputable def Gdiv : PowerSeries R := PowerSeries.mk fun n => (profile n).divX
private noncomputable def U : PowerSeries R := 1-z
private noncomputable def L : PowerSeries R := U-C Polynomial.X*z^2

private theorem cf_zpow (n k : ℕ) (f : PowerSeries R) :
    cf n (z^k*f) = if k ≤ n then cf (n-k) f else 0 :=
  PowerSeries.coeff_X_pow_mul' f k n

private theorem cf_zmul (n : ℕ) (f : PowerSeries R) :
    cf (n+1) (z*f) = cf n f := by
  simpa only [cf,z,pow_one] using PowerSeries.coeff_X_pow_mul f 1 n

private theorem cf_z_zero (f : PowerSeries R) : cf 0 (z*f)=0 := by
  simpa only [pow_one, show ¬1 ≤ (0:ℕ) by decide, if_false] using cf_zpow 0 1 f

private theorem cf_C (n : ℕ) (p : R) (f : PowerSeries R) :
    cf n (C p*f) = p*cf n f := PowerSeries.coeff_C_mul n f p

private theorem cf_one_series (n : ℕ) : cf n 1 = if n=0 then 1 else 0 :=
  PowerSeries.coeff_one n

@[simp] private theorem cf_G (n : ℕ) : cf n G = profile n :=
  PowerSeries.coeff_mk _ _

@[simp] private theorem cf_Gy (n : ℕ) : cf n Gy = (profile n).derivative :=
  PowerSeries.coeff_mk _ _

@[simp] private theorem cf_J (n : ℕ) : cf n J = 1 :=
  PowerSeries.coeff_mk _ _

@[simp] private theorem cf_Gdiv (n : ℕ) : cf n Gdiv = (profile n).divX :=
  PowerSeries.coeff_mk _ _

private theorem cf_L (f : PowerSeries R) (n : ℕ) :
    cf n (L*f) = cf n f - (if 1 ≤ n then cf (n-1) f else 0) -
      Polynomial.X*(if 2 ≤ n then cf (n-2) f else 0) := by
  rw [L,U,sub_mul,sub_mul,one_mul,map_sub,map_sub,mul_assoc,cf_C,
    show z*f=z^1*f by rw [pow_one],cf_zpow,cf_zpow]

private theorem L_G : L*G=1 := by
  apply PowerSeries.ext
  intro n
  change cf n (L*G)=cf n 1
  rw [cf_L, cf_one_series]
  cases n with
  | zero => simp [profile]
  | succ n =>
    cases n with
    | zero => simp [profile]
    | succ n =>
      simp only [show 1≤n+1+1 by omega, show 2≤n+1+1 by omega, if_true,
        show n+1+1-1=n+1 by omega, show n+1+1-2=n by omega, cf_G, Nat.succ_ne_zero, if_false]
      change profile (n+2)-profile (n+1)-Polynomial.X*profile n=0
      rw [profile]
      ring

private theorem L_Gz : L*Gz=(1+2*C Polynomial.X*z)*G := by
  have h := congrArg (PowerSeries.derivative R) L_G
  simp only [Derivation.leibniz, Derivation.map_one_eq_zero, L,U,z,C,
    map_sub, PowerSeries.derivative_X, PowerSeries.derivative_C, Derivation.leibniz_pow,
    show (2:ℕ)-1=1 by decide, pow_one, two_nsmul] at h
  simp only [smul_eq_mul, zero_mul, mul_zero, mul_one, add_zero] at h
  dsimp [L,U,z,C,Gz]
  linear_combination h

private theorem L_Gy : L*Gy=z^2*G := by
  apply PowerSeries.ext
  intro n
  change cf n (L*Gy)=cf n (z^2*G)
  rw [cf_L,cf_zpow]
  cases n with
  | zero => simp [profile]
  | succ n =>
    cases n with
    | zero => simp [profile]
    | succ n =>
      simp only [show 1≤n+1+1 by omega, show 2≤n+1+1 by omega, if_true,
        show n+1+1-1=n+1 by omega, show n+1+1-2=n by omega, cf_G,cf_Gy]
      change (profile (n+2)).derivative-(profile (n+1)).derivative-
        Polynomial.X*(profile n).derivative=profile n
      rw [profile, map_add, Polynomial.derivative_mul, Polynomial.derivative_X]
      ring

private theorem U_J : U*J=1 := by
  apply PowerSeries.ext
  intro n
  change cf n (U*J)=cf n 1
  rw [U,sub_mul,one_mul,map_sub,cf_J,cf_one_series]
  cases n with
  | zero => simp [cf_z_zero]
  | succ n => simp [cf_zmul]

private theorem Cx_Gdiv : C Polynomial.X*Gdiv+J=G := by
  apply PowerSeries.ext
  intro n
  change cf n (C Polynomial.X*Gdiv+J)=cf n G
  rw [map_add,cf_C,cf_Gdiv,cf_J,cf_G]
  have h := Polynomial.X_mul_divX_add (profile n)
  rw [profile_coeff n 0, Nat.choose_zero_right, Nat.cast_one, map_one] at h
  exact h

private theorem U_Gdiv : U*Gdiv=z^2*G := by
  have hC : C Polynomial.X ≠ 0 := by
    have hcf : cf 0 (C Polynomial.X) = Polynomial.X := by
      unfold cf C
      simp
    intro h
    rw [h, map_zero] at hcf
    exact Polynomial.X_ne_zero hcf.symm
  apply mul_left_cancel₀ hC
  have h : U*G=1+C Polynomial.X*z^2*G := by
    have hL := L_G
    unfold L at hL
    linear_combination hL
  linear_combination U*Cx_Gdiv - U_J + h


private noncomputable def F : PowerSeries R :=
  C (Polynomial.X^2-6*Polynomial.X+1)*Gy+C (2*Polynomial.X-3)*G-Gdiv

private noncomputable def Q : PowerSeries R := 1-3*z-3*z^2+11*z^3-5*z^4-z^5
private noncomputable def B : PowerSeries R := 2-6*z+13*z^3-9*z^4-z^5
private noncomputable def K : PowerSeries R := -2+3*z+z^2-z^3

private theorem certificate :
    z*Q*Gz+B*G+K=(2-z)*z^2*(U*F+1) := by
  have hL : L ≠ 0 := by
    intro h
    have h1 := L_G
    rw [h,zero_mul] at h1
    exact zero_ne_one h1
  apply mul_left_cancel₀ hL
  have hi := L_G
  have hz := L_Gz
  have hy := L_Gy
  have hd := U_Gdiv
  simp only [Q, B, K, F, L, U, C, map_add, map_sub, map_one, map_mul, map_pow,
    map_ofNat] at *
  let y := PowerSeries.C (R := R) Polynomial.X
  linear_combination
    z*(1-3*z-3*z^2+11*z^3-5*z^4-z^5)*hz -
    (2-z)*z^2*(1-z)*(y^2-6*y+1)*hy +
    (2-z)*z^2*(1-z-y*z^2)*hd +
    (2-z)*(1-z)*(1-z-y*z^2)*hi

private theorem M_one : M 1=1 := by
  have h0 : s 0=1 := by decide +kernel
  have h := M_monomial 0 1
  simpa [h0] using h

private theorem M_cf_F (n : ℕ) : M (cf n F) = -1 := by
  rw [F, map_sub (cf n), map_add (cf n), cf_C, cf_C, cf_Gy, cf_G, cf_Gdiv, moment,
    profile_coeff n 0, Nat.choose_zero_right, Nat.cast_one]

private theorem M_cf_right (n : ℕ) : M (cf n (U*F+1))=0 := by
  rw [U, sub_mul, one_mul, map_add (cf n), map_sub (cf n), map_add M, map_sub M,
    M_cf_F,cf_one_series]
  cases n with
  | zero => simp [cf_z_zero, M_one]
  | succ n => simp [cf_zmul,M_cf_F]

private theorem M_cf_right_pow (n k : ℕ) (hk : k≤n) :
    M (cf n (z^k*(U*F+1)))=0 := by
  rw [cf_zpow, if_pos hk, M_cf_right]

private theorem M_cf_nsmul (n k : ℕ) (f : PowerSeries R) :
    M (cf n ((k : PowerSeries R)*f)) = (k:ℤ)*M (cf n f) := by
  rw [← nsmul_eq_mul,map_nsmul,map_nsmul,nsmul_eq_mul]

private theorem M_cf_ofNat (n k : ℕ) [k.AtLeastTwo] (f : PowerSeries R) :
    M (cf n (OfNat.ofNat k*f)) = OfNat.ofNat k * M (cf n f) :=
  M_cf_nsmul n k f

private theorem M_cf_G (n k : ℕ) (hk : k≤n) :
    M (cf n (z^k*G))=(a (n-k):ℤ) := by
  rw [cf_zpow,if_pos hk,cf_G,a_profile]

private theorem M_cf_Gz (n k : ℕ) (hk : k≤n) :
    M (cf n (z^(k+1)*Gz))=((n:ℤ)-k)*(a (n-k):ℤ) := by
  rw [cf_zpow]
  split
  next hh =>
    have he : n-(k+1)+1=n-k := by omega
    change M (PowerSeries.coeff (R := R) (n-(k+1)) (PowerSeries.derivative R G)) = _
    rw [PowerSeries.coeff_derivative, he]
    have hc : ((n-(k+1) : ℕ) : R)+1=((n-k : ℕ) : R) := by exact_mod_cast he
    rw [hc]
    change M (cf (n-k) G * ((n-k : ℕ) : R)) = _
    rw [mul_comm, ← nsmul_eq_mul, map_nsmul,nsmul_eq_mul,Nat.cast_sub hk,cf_G,a_profile]
  next hh =>
    have he : n=k := by omega
    simp [he]

private theorem K_large (n : ℕ) (hn : 3<n) : M (cf n K)=0 := by
  have h0 : n≠0 := by omega
  have hx (k : ℕ) (hk : k<n) : cf n (z^k)=0 := by
    unfold cf z
    rw [PowerSeries.coeff_X_pow, if_neg (by omega)]
  have ht : (2 : PowerSeries R)=1+1 := by ring
  have htwo : cf n (2:PowerSeries R)=0 := by
    rw [ht,map_add,cf_one_series,if_neg h0,add_zero]
  have hs : K=-(2:PowerSeries R)+(3:PowerSeries R)*(z^1)+z^2-z^3 := by
    unfold K
    ring
  rw [hs,map_sub (cf n),map_add (cf n),map_add (cf n),map_neg (cf n),htwo]
  simp only [map_add,map_sub,map_neg,map_zero,neg_zero,zero_add]
  rw [M_cf_ofNat n 3]
  simp only [hx 1 (by omega),hx 2 (by omega),hx 3 (by omega), map_zero,
    mul_zero, add_zero, sub_zero]


private theorem recurrence (m : ℕ) :
    let n := (m:ℤ)+5
    (n+2)*a (m+5)-3*(n+1)*a (m+4)+3*(2-n)*a (m+3) +
      (11*n-20)*a (m+2)+(11-5*n)*a (m+1)+(4-n)*a m=0 := by
  have hz : z*Q*Gz =
      z^(0+1)*Gz-(3:ℕ)*(z^(1+1)*Gz)-(3:ℕ)*(z^(2+1)*Gz) +
        (11:ℕ)*(z^(3+1)*Gz)-(5:ℕ)*(z^(4+1)*Gz)-z^(5+1)*Gz := by
    unfold Q
    push_cast
    ring
  have hb : B*G =
      (2:ℕ)*(z^0*G)-(6:ℕ)*(z^1*G)+(13:ℕ)*(z^3*G)-(9:ℕ)*(z^4*G)-z^5*G := by
    unfold B
    push_cast
    ring
  have hr : (2-z)*z^2*(U*F+1) =
      (2:ℕ)*(z^2*(U*F+1))-z^3*(U*F+1) := by
    push_cast
    ring
  have h : M (cf (m+5) (z*Q*Gz+B*G+K)) =
      M (cf (m+5) ((2-z)*z^2*(U*F+1))) :=
    congrArg (fun f => M (cf (m+5) f)) certificate
  rw [hz,hb,hr] at h
  have h0 : 0 ≤ m+5 := Nat.zero_le _
  have h1 : 1 ≤ m+5 := by omega
  have h2 : 2 ≤ m+5 := by omega
  have h3 : 3 ≤ m+5 := by omega
  have h4 : 4 ≤ m+5 := by omega
  have h5 : 5 ≤ m+5 := by omega
  simp only [map_add, K_large _ (by omega : 3<m+5)] at h
  simp only [map_add,map_sub,M_cf_ofNat (m+5) 2,M_cf_ofNat (m+5) 3,
    M_cf_ofNat (m+5) 5,M_cf_ofNat (m+5) 6,M_cf_ofNat (m+5) 9,
    M_cf_ofNat (m+5) 11,M_cf_ofNat (m+5) 13,
    M_cf_Gz _ _ h0,M_cf_Gz _ _ h1,M_cf_Gz _ _ h2,M_cf_Gz _ _ h3,M_cf_Gz _ _ h4,M_cf_Gz _ _ h5,
    M_cf_G _ _ h0,M_cf_G _ _ h1,M_cf_G _ _ h3,M_cf_G _ _ h4,M_cf_G _ _ h5,
    M_cf_right_pow _ _ h2,M_cf_right_pow _ _ h3,
    show m+5-1=m+4 by omega,show m+5-2=m+3 by omega,show m+5-3=m+2 by omega,
    show m+5-4=m+1 by omega,show m+5-5=m by omega,
    Nat.cast_add,Nat.cast_ofNat,Nat.cast_zero,Nat.sub_zero,sub_zero,mul_zero,zero_sub,neg_zero,add_zero] at h
  dsimp
  linear_combination h

end OMA.S_oeis_a185089

open OMA.S_oeis_a185089 in
theorem OMA.solution : type_of% @OMA.S_oeis_a185089.main := by
  intro n hn
  let m := n-5
  have h : n=m+5 := by omega
  rw [h]
  simpa only [Nat.cast_add,Nat.cast_ofNat,show m+5-1=m+4 by omega,
    show m+5-2=m+3 by omega,show m+5-3=m+2 by omega,
    show m+5-4=m+1 by omega,show m+5-5=m by omega] using recurrence m
