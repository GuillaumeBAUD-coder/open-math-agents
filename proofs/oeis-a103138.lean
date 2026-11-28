import OMAStatements.S_oeis_a103138

-- Credit: @CubeJerry (the owner of the agent is credited as the solver)

/-!
A proof of Mathar's recurrence for A103138 from the original Catalan/binomial
definition. Finite creative telescoping first proves the Schroeder recurrence.
The signed generating series then satisfies a differential equation, whose
quadratic invariant yields the equation for the stated generating function.
Taking coefficients gives exactly the proposed four-term recurrence.
-/

namespace OMA.T103138

noncomputable def F (n k : ℕ) : ℚ :=
  (n.choose k : ℚ) * ((n+k).choose k : ℚ) / ((k : ℚ)+1)

def right (n k : ℚ) : ℚ := (n+k+1)*(n-k)/((k+1)*(k+2))
def back (n k : ℚ) : ℚ := (n-k)/(n+k)
def R (n k : ℚ) : ℚ := -2*k*(k+1)*(2*n-1)/((n+k)*(n+k-1))

lemma F_zero_of_lt (n k : ℕ) (h : n < k) : F n k = 0 := by
  simp [F, Nat.choose_eq_zero_of_lt h]

lemma term_eq (n k : ℕ) (hk : k ≤ n) :
    (catalan k : ℚ) * ((n+k).choose (n-k) : ℚ) = F n k := by
  have hs : (n+k).choose (n-k) = (n+k).choose (2*k) :=
    Nat.choose_symm_of_eq_add (by omega)
  have hc : (k+1)*catalan k*(n+k).choose (n-k) = n.choose k*(n+k).choose k := by
    rw [succ_mul_catalan_eq_centralBinom, Nat.centralBinom, hs]
    have h := Nat.choose_mul (n := n+k) (k := 2*k) (s := k) (by omega)
    rw [show n+k-k=n by omega, show 2*k-k=k by omega] at h
    simpa only [mul_comm] using h
  unfold F
  apply (eq_div_iff (by positivity)).2
  have hcq := congrArg (fun t : ℕ => (t : ℚ)) hc
  push_cast at hcq
  nlinarith only [hcq]

lemma repr (n : ℕ) :
    (OMA.S_oeis_a103138.schroeder n : ℚ) = ∑ k ∈ Finset.range (n+1), F n k := by
  unfold OMA.S_oeis_a103138.schroeder
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  exact term_eq n k (by have := Finset.mem_range.mp hk; omega)

lemma rightF (n k : ℕ) : F n (k+1) = F n k * right n k := by
  by_cases hk : k ≤ n
  · have hc : (n.choose (k+1) : ℚ) =
        (n.choose k : ℚ) * ((n:ℚ)-k) / ((k:ℚ)+1) := by
      apply (eq_div_iff (by positivity)).2
      have h := congrArg (fun t : ℕ => (t : ℚ)) (Nat.choose_succ_right_eq n k)
      push_cast [Nat.cast_sub hk] at h
      exact h
    have hd : ((n+k+1).choose (k+1) : ℚ) =
        ((n+k).choose k : ℚ) * ((n:ℚ)+k+1) / ((k:ℚ)+1) := by
      apply (eq_div_iff (by positivity)).2
      have h := congrArg (fun t : ℕ => (t : ℚ)) (Nat.add_one_mul_choose_eq (n+k) k)
      push_cast at h
      nlinarith only [h]
    unfold F right
    rw [show n+(k+1)=n+k+1 by omega, hc, hd]
    push_cast
    field_simp
    ring
  · rw [F_zero_of_lt n (k+1) (by omega), F_zero_of_lt n k (by omega)]
    simp

lemma backF (n k : ℕ) : F n k = F (n+1) k * back ((n:ℚ)+1) k := by
  by_cases hk : k ≤ n+1
  · have hc : (n.choose k : ℚ) =
        ((n+1).choose k : ℚ) * (((n:ℚ)+1)-k) / ((n:ℚ)+1) := by
      apply (eq_div_iff (by positivity)).2
      have h := congrArg (fun t : ℕ => (t : ℚ)) (Nat.choose_mul_succ_eq n k)
      push_cast [Nat.cast_sub hk] at h
      exact h
    have hd : ((n+k).choose k : ℚ) =
        ((n+k+1).choose k : ℚ) * ((n:ℚ)+1) / ((n:ℚ)+k+1) := by
      apply (eq_div_iff (by positivity)).2
      have h := congrArg (fun t : ℕ => (t : ℚ)) (Nat.choose_mul_succ_eq (n+k) k)
      rw [show n+k+1-k=n+1 by omega] at h
      push_cast at h
      exact h
    unfold F back
    rw [hc, hd, show n+1+k=n+k+1 by omega]
    push_cast
    field_simp
    ring
  · rw [F_zero_of_lt n k (by omega), F_zero_of_lt (n+1) k (by omega)]
    simp

lemma certQ (n k : ℚ) (hn : 2 ≤ n) (hk : 0 ≤ k) :
    right n k * R n (k+1) - R n k =
      (n+1) - 3*(2*n-1)*back n k + (n-2)*back n k*back (n-1) k := by
  unfold right back R
  field_simp (disch := first | positivity | linarith)
  ring

lemma schroeder_zero : OMA.S_oeis_a103138.schroeder 0 = 1 := by
  norm_num [OMA.S_oeis_a103138.schroeder]

lemma schroeder_one : OMA.S_oeis_a103138.schroeder 1 = 2 := by
  norm_num [OMA.S_oeis_a103138.schroeder, Finset.sum_range_succ]




open scoped BigOperators

lemma sum_extend_zero (t : ℕ → ℕ → ℚ)
    (hz : ∀ m k : ℕ, m < k → t m k = 0)
    (m N : ℕ) (hm : m ≤ N) :
    (∑ k ∈ Finset.range (N + 1), t m k) =
      ∑ k ∈ Finset.range (m + 1), t m k := by
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k hk hkm
  apply hz
  simp only [Finset.mem_range, not_lt] at hkm
  omega

lemma sum_certificate (t : ℕ → ℕ → ℚ)
    (hz : ∀ m k : ℕ, m < k → t m k = 0)
    (n : ℕ) (hn : 2 ≤ n) (c₀ c₁ c₂ : ℚ) (G : ℕ → ℚ)
    (hG₀ : G 0 = 0) (hG₁ : G (n + 1) = 0)
    (hcert : ∀ k : ℕ, k ≤ n →
      c₀ * t n k + c₁ * t (n - 1) k + c₂ * t (n - 2) k =
        G (k + 1) - G k) :
    c₀ * (∑ k ∈ Finset.range (n + 1), t n k) +
      c₁ * (∑ k ∈ Finset.range (n - 1 + 1), t (n - 1) k) +
      c₂ * (∑ k ∈ Finset.range (n - 2 + 1), t (n - 2) k) = 0 := by
  rw [← sum_extend_zero t hz (n - 1) n (by omega),
    ← sum_extend_zero t hz (n - 2) n (by omega)]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    (∑ k ∈ Finset.range (n + 1),
        (c₀ * t n k + c₁ * t (n - 1) k + c₂ * t (n - 2) k)) =
        ∑ k ∈ Finset.range (n + 1), (G (k + 1) - G k) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hcert k (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk)
    _ = 0 := by rw [Finset.sum_range_sub, hG₀, hG₁, sub_self]

lemma sum_ratio_certificate (t : ℕ → ℕ → ℚ)
    (hz : ∀ m k : ℕ, m < k → t m k = 0)
    (n : ℕ) (hn : 2 ≤ n) (c₀ c₁ c₂ : ℚ) (R : ℕ → ℚ)
    (r b : ℕ → ℕ → ℚ)
    (hR₀ : R 0 = 0)
    (hr : ∀ k : ℕ, k ≤ n → t n (k + 1) = t n k * r n k)
    (hb₁ : ∀ k : ℕ, k ≤ n → t (n - 1) k = t n k * b n k)
    (hb₂ : ∀ k : ℕ, k ≤ n → t (n - 2) k = t (n - 1) k * b (n - 1) k)
    (hcert : ∀ k : ℕ, k ≤ n →
      r n k * R (k + 1) - R k =
        c₀ + c₁ * b n k + c₂ * b n k * b (n - 1) k) :
    c₀ * (∑ k ∈ Finset.range (n + 1), t n k) +
      c₁ * (∑ k ∈ Finset.range (n - 1 + 1), t (n - 1) k) +
      c₂ * (∑ k ∈ Finset.range (n - 2 + 1), t (n - 2) k) = 0 := by
  apply sum_certificate t hz n hn c₀ c₁ c₂ (fun k => t n k * R k)
  · simp [hR₀]
  · rw [hz n (n + 1) (by omega), zero_mul]
  intro k hk
  calc
    c₀ * t n k + c₁ * t (n - 1) k + c₂ * t (n - 2) k =
        t n k * (c₀ + c₁ * b n k + c₂ * b n k * b (n - 1) k) := by
      rw [hb₂ k hk, hb₁ k hk]
      ring
    _ = t n k * (r n k * R (k + 1) - R k) := by rw [hcert k hk]
    _ = t n (k + 1) * R (k + 1) - t n k * R k := by rw [hr k hk]; ring


lemma schroeder_recurrence (n : ℕ) (hn : 2 ≤ n) :
    ((n:ℚ)+1)*(OMA.S_oeis_a103138.schroeder n : ℚ) -
      3*(2*(n:ℚ)-1)*(OMA.S_oeis_a103138.schroeder (n-1) : ℚ) +
      ((n:ℚ)-2)*(OMA.S_oeis_a103138.schroeder (n-2) : ℚ) = 0 := by
  rw [repr n, repr (n-1), repr (n-2)]
  have hs :
      ((n:ℚ)+1)*(∑ k ∈ Finset.range (n+1), F n k) +
      (-3*(2*(n:ℚ)-1))*(∑ k ∈ Finset.range (n-1+1), F (n-1) k) +
      ((n:ℚ)-2)*(∑ k ∈ Finset.range (n-2+1), F (n-2) k) = 0 := by
    apply sum_ratio_certificate F F_zero_of_lt n hn
      ((n:ℚ)+1) (-3*(2*(n:ℚ)-1)) ((n:ℚ)-2) (fun k => R n k)
      (fun m k => right m k) (fun m k => back m k)
    · simp [R]
    · intro k hk
      exact rightF n k
    · intro k hk
      have hc : ((n-1 : ℕ) : ℚ)+1 = (n:ℚ) := by
        exact_mod_cast Nat.sub_add_cancel (show 1 ≤ n by omega)
      simpa only [Nat.sub_add_cancel (show 1 ≤ n by omega), hc] using backF (n-1) k
    · intro k hk
      have hc : ((n-2 : ℕ) : ℚ)+1 = ((n-1 : ℕ) : ℚ) := by
        exact_mod_cast (show n-2+1=n-1 by omega)
      simpa only [show n-2+1=n-1 by omega, hc] using backF (n-2) k
    · intro k hk
      have h := certQ (n:ℚ) (k:ℚ) (by exact_mod_cast hn) (by positivity)
      push_cast
      rw [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
      linear_combination h
  linear_combination hs

lemma schroeder_recurrenceZ (m : ℕ) :
    ((m:ℤ)+3)*(OMA.S_oeis_a103138.schroeder (m+2) : ℤ) -
      (6*(m:ℤ)+9)*(OMA.S_oeis_a103138.schroeder (m+1) : ℤ) +
      (m:ℤ)*(OMA.S_oeis_a103138.schroeder m : ℤ) = 0 := by
  have h := schroeder_recurrence (m+2) (by omega)
  rw [show m+2-1=m+1 by omega, show m+2-2=m by omega] at h
  push_cast at h
  have hq :
      ((m:ℚ)+3)*(OMA.S_oeis_a103138.schroeder (m+2) : ℚ) -
      (6*(m:ℚ)+9)*(OMA.S_oeis_a103138.schroeder (m+1) : ℚ) +
      (m:ℚ)*(OMA.S_oeis_a103138.schroeder m : ℚ) = 0 := by
    linear_combination h
  exact_mod_cast hq

end OMA.T103138

namespace OMA.T103138

open PowerSeries

noncomputable def signedSeries (s : ℕ → ℤ) : PowerSeries ℤ :=
  mk (fun n => (-1)^n * s n)

lemma coeff_X_derivative (f : PowerSeries ℤ) (n : ℕ) :
    coeff n (X * derivative ℤ f) = (n : ℤ) * coeff n f := by
  cases n with
  | zero => simp
  | succ n =>
    simp only [coeff_succ_X_mul, coeff_derivative, Nat.cast_add,
      Nat.cast_one]
    ring

lemma signed_series_ode (s : ℕ → ℤ) (h0 : s 0 = 1) (h1 : s 1 = 2)
    (hrec : ∀ n : ℕ, ((n : ℤ)+3)*s (n+2) - (6*n+9)*s (n+1) + (n : ℤ)*s n = 0) :
    X*(1+6*X+X^2) * derivative ℤ (signedSeries s) +
      (1+3*X) * signedSeries s = 1-X := by
  have he : X*(1+6*X+X^2) * derivative ℤ (signedSeries s) +
      (1+3*X) * signedSeries s =
      X * derivative ℤ (signedSeries s) +
        C 6 * (X * (X * derivative ℤ (signedSeries s))) +
        X * (X * (X * derivative ℤ (signedSeries s))) +
        signedSeries s + C 3 * (X * signedSeries s) := by
    simp only [map_ofNat]
    ring
  rw [he]
  ext n
  simp only [map_add, map_sub, coeff_C_mul]
  cases n with
  | zero => simp [signedSeries, h0]
  | succ n =>
    cases n with
    | zero =>
      norm_num [signedSeries, coeff_derivative, h0, h1]
    | succ n =>
      simp only [coeff_succ_X_mul, coeff_derivative, coeff_X_derivative, coeff_one, coeff_X]
      have hn0 : n + 1 + 1 ≠ 0 := by omega
      have hn1 : n + 1 + 1 ≠ 1 := by omega
      simp only [hn0, hn1, ↓reduceIte, sub_zero]
      simp only [signedSeries, coeff_mk]
      have hpow : (-1:ℤ)^(n+1) = -((-1)^n) := by rw [pow_succ]; ring
      have hpow2 : (-1:ℤ)^(n+1+1) = (-1)^n := by rw [pow_succ, hpow]; ring
      rw [hpow2, hpow]
      push_cast
      have hr := hrec n
      linear_combination (-1:ℤ)^n * hr

end OMA.T103138

namespace OMA.T103138
open PowerSeries
lemma sNeg_ode :
    X*(1+6*X+X^2) * derivative ℤ OMA.S_oeis_a103138.sNeg +
      (1+3*X) * OMA.S_oeis_a103138.sNeg = 1-X := by
  have h0 : (OMA.S_oeis_a103138.schroeder 0 : ℤ) = 1 := by
    exact_mod_cast schroeder_zero
  have h1 : (OMA.S_oeis_a103138.schroeder 1 : ℤ) = 2 := by
    exact_mod_cast schroeder_one
  simpa only [signedSeries, OMA.S_oeis_a103138.sNeg] using
    signed_series_ode (fun n => (OMA.S_oeis_a103138.schroeder n : ℤ)) h0 h1
      schroeder_recurrenceZ
end OMA.T103138

namespace OMA.T103138
open PowerSeries

lemma derivative_nat (n : ℕ) [n.AtLeastTwo] :
    derivative ℤ (no_index (OfNat.ofNat n : PowerSeries ℤ)) = 0 :=
  Derivation.map_natCast _ n

lemma zero_of_homogeneous_ode (E W B : PowerSeries ℤ)
    (hW : constantCoeff W = 1) (hE : constantCoeff E = 0)
    (h : W * derivative ℤ E = B * E) : E = 0 := by
  ext n
  simp only [map_zero]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa only [coeff_zero_eq_constantCoeff_apply] using hE
    | succ n =>
      have hleft : coeff n (W * derivative ℤ E) = coeff (n+1) E * (n+1) := by
        rw [mul_comm W, coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j => coeff i (derivative ℤ E) * coeff j W) n]
        rw [Finset.sum_range_succ]
        have hs : (∑ k ∈ Finset.range n,
            coeff k (derivative ℤ E) * coeff (n-k) W) = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          rw [coeff_derivative, ih (k+1) (by simp only [Finset.mem_range] at hk; omega)]
          ring
        rw [hs, zero_add, Nat.sub_self, coeff_zero_eq_constantCoeff_apply, hW,
          mul_one, coeff_derivative]
      have hright : coeff n (B * E) = 0 := by
        rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => coeff i B * coeff j E) n]
        apply Finset.sum_eq_zero
        intro k hk
        rw [ih (n-k) (by omega), mul_zero]
      have hc := congrArg (coeff n) h
      rw [hleft, hright] at hc
      exact (mul_eq_zero.mp hc).resolve_right (by omega)

lemma quadratic_of_ode (Y : PowerSeries ℤ) (hY : constantCoeff Y = 0)
    (h : (1+6*X+X^2) * derivative ℤ Y - (3+X)*Y = 1-X) :
    Y^2 + (1+X)*Y - X = 0 := by
  let W : PowerSeries ℤ := 1+6*X+X^2
  let Z : PowerSeries ℤ := 1+X+2*Y
  have hZ : W * derivative ℤ Z = (3+X)*Z := by
    dsimp [W,Z]
    simp only [map_add, derivative_one, derivative_X, Derivation.leibniz,
      derivative_nat, zero_mul, one_mul, mul_one, zero_add, add_zero]
    linear_combination 2*h
  have hW : derivative ℤ W = 2*(3+X) := by
    dsimp [W]
    simp only [map_add, derivative_one, derivative_X, Derivation.leibniz,
      Derivation.leibniz_pow, derivative_nat, zero_mul, one_mul, mul_one,
      zero_add, add_zero, smul_eq_mul, nsmul_eq_mul]
    norm_num
    ring
  have hE : W * derivative ℤ (Z^2-W) = (2*(3+X))*(Z^2-W) := by
    simp only [map_sub, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]
    rw [hW]
    norm_num
    linear_combination 2*Z*hZ
  have hz : Z^2-W = 0 := zero_of_homogeneous_ode (Z^2-W) W (2*(3+X))
    (by simp [W]) (by simp [W,Z,hY]) hE
  have hfour : (4 : PowerSeries ℤ) * (Y^2+(1+X)*Y-X) = 0 := by
    linear_combination hz
  exact (mul_eq_zero.mp hfour).resolve_left (by
    intro hc
    have hc₀ := congrArg constantCoeff hc
    norm_num only [map_ofNat, map_zero] at hc₀)

lemma gf_ode_of_signed_ode (T : PowerSeries ℤ)
    (h : X*(1+6*X+X^2)*derivative ℤ T + (1+3*X)*T = 1-X) :
    let A := (1-X*T)*(X*T)
    X*(2+13*X+8*X^2+X^3)*derivative ℤ A +
      (-7*X-11*X^2-2*X^3)*A = 2*X-6*X^2 := by
  let Y : PowerSeries ℤ := X*T
  have hY : (1+6*X+X^2)*derivative ℤ Y - (3+X)*Y = 1-X := by
    dsimp [Y]
    rw [Derivation.leibniz, derivative_X]
    linear_combination h
  have hQ := quadratic_of_ode Y (by simp [Y]) hY
  have hA : (1-X*T)*(X*T) = (2+X)*Y-X := by
    dsimp [Y] at hQ ⊢
    linear_combination -hQ
  dsimp only
  rw [hA]
  simp only [map_sub, Derivation.leibniz, map_add,
    derivative_nat, derivative_X, zero_add]
  linear_combination X*(X+2)^2*hY

end OMA.T103138

namespace OMA.T103138

open PowerSeries

lemma coeff_euler (f : PowerSeries ℤ) (n : ℕ) :
    coeff n (X * derivative ℤ f) = (n : ℤ) * coeff n f := by
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

lemma coeff_shift (f : PowerSeries ℤ) (n d : ℕ) (hd : d ≤ n) :
    coeff n (X ^ d * f) = coeff (n - d) f := by
  rw [coeff_X_pow_mul', if_pos hd]

lemma ode_coeff_recurrence (f : PowerSeries ℤ)
    (hode : (2 + 13*X + 8*X^2 + X^3) * (X * derivative ℤ f) -
      (7*X + 11*X^2 + 2*X^3) * f = 2*X - 6*X^2)
    (n : ℕ) (hn : 3 ≤ n) :
    2 * (n : ℤ) * coeff n f + (13 * n - 20 : ℤ) * coeff (n - 1) f +
      (8 * n - 27 : ℤ) * coeff (n - 2) f +
      ((n : ℤ) - 5) * coeff (n - 3) f = 0 := by
  have h := congrArg (coeff n) hode
  have h1 : 1 ≤ n := by omega
  have h2 : 2 ≤ n := by omega
  have hn1 : n ≠ 1 := by omega
  have hn2 : n ≠ 2 := by omega
  simp only [add_mul, mul_assoc, map_sub, map_add] at h
  simp only [show (2 : PowerSeries ℤ) = C 2 by norm_num,
    show (13 : PowerSeries ℤ) = C 13 by norm_num,
    show (8 : PowerSeries ℤ) = C 8 by norm_num,
    show (7 : PowerSeries ℤ) = C 7 by norm_num,
    show (11 : PowerSeries ℤ) = C 11 by norm_num,
    show (6 : PowerSeries ℤ) = C 6 by norm_num,
    coeff_C_mul] at h
  have hx : ∀ g : PowerSeries ℤ, coeff n (X * g) = coeff (n - 1) g := by
    intro g
    simpa only [pow_one] using coeff_shift g n 1 h1
  rw [coeff_euler, hx] at h
  simp only [coeff_X_pow_mul', if_pos h2, if_pos hn] at h
  simp only [coeff_euler, hx, coeff_X_pow, coeff_X, hn1, hn2,
    if_false, mul_zero, sub_zero,
    Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub hn] at h
  norm_num at h
  linear_combination h

end OMA.T103138

open PowerSeries OMA.T103138

theorem OMA.solution : type_of% @OMA.S_oeis_a103138.main := by
  intro n hn
  have hode :
      X*(2+13*X+8*X^2+X^3)*derivative ℤ OMA.S_oeis_a103138.gf +
        (-7*X-11*X^2-2*X^3)*OMA.S_oeis_a103138.gf = 2*X-6*X^2 :=
    gf_ode_of_signed_ode OMA.S_oeis_a103138.sNeg sNeg_ode
  exact ode_coeff_recurrence OMA.S_oeis_a103138.gf
    (by linear_combination hode) n hn
