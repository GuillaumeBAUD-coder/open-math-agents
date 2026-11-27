import FormalConjectures.ErdosProblems.«1184»

/-!
Erdős's improved uniform lower bound for large prime factors in a short interval
(Theorem 2 in *Problems and results on consecutive integers*, 1976).

Partial summation gives large reciprocal mass in a fixed power interval of primes.
A second moment then shows that, uniformly in the starting point, most integers in
the interval have a prime factor in that range. Splitting the logarithmic mass of
the interval product at k sharpens the binomial-coefficient count.
-/

-- Credit: @zarnab222-dev

open Finset

namespace IntervalSieve

private theorem interval_count_eq (n k d : ℕ) :
    n / d + ((Finset.Icc 1 k).filter fun i => d ∣ n + i).card = (n+k)/d := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : Finset.Icc 1 (k+1) = insert (k+1) (Finset.Icc 1 k) := by
      ext i
      simp only [mem_Icc, mem_insert]
      omega
    have hn : k+1 ∉ Finset.Icc 1 k := by simp
    rw [he, ← Nat.add_assoc n k 1, Nat.succ_div]
    by_cases h : d ∣ n + k + 1
    · simp [Finset.filter_insert, h, ← Nat.add_assoc, hn]
      omega
    · simp [Finset.filter_insert, ← Nat.add_assoc, h, ih]

private theorem interval_count_error (n k d : ℕ) (hd : 0 < d) :
    let c : ℝ := ∑ i ∈ Finset.Icc 1 k, if d ∣ n+i then 1 else 0
    (k : ℝ) * (d : ℝ)⁻¹ - 1 ≤ c ∧ c ≤ (k : ℝ) * (d : ℝ)⁻¹ + 1 := by
  dsimp only
  simp only [Finset.sum_boole]
  let c := ((Finset.Icc 1 k).filter fun i => d ∣ n+i).card
  have he : n / d + c = (n+k)/d := interval_count_eq n k d
  have he' : ((n % d : ℕ) : ℝ) + k = ((n+k)%d : ℕ) + (d:ℝ) * c := by
    exact_mod_cast (show n % d + k = (n+k)%d + d*c by
      have h := Nat.mod_add_div n d
      have h' := Nat.mod_add_div (n+k) d
      rw [← he, Nat.mul_add] at h'
      omega)
  have h1 : ((n+k)%d : ℕ) < (d:ℝ) := by exact_mod_cast Nat.mod_lt (n+k) hd
  have h2 : (n % d : ℕ) < (d:ℝ) := by exact_mod_cast Nat.mod_lt n hd
  have hz : (0:ℝ) < d := by exact_mod_cast hd
  change (k:ℝ) * (d:ℝ)⁻¹ - 1 ≤ c ∧ (c:ℝ) ≤ (k:ℝ) * (d:ℝ)⁻¹ + 1
  rw [← div_eq_mul_inv]
  constructor
  · rw [sub_le_iff_le_add, div_le_iff₀ hz]
    nlinarith [Nat.cast_nonneg (α:=ℝ) (n % d)]
  · rw [← sub_le_iff_le_add, le_div_iff₀ hz]
    nlinarith [Nat.cast_nonneg (α:=ℝ) ((n+k) % d)]

/-- The count of offsets with no divisor from `P`, controlled by the reciprocal-prime sum. -/
theorem misses_mul_reciprocal_sum_sq (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime) (n k : ℕ) :
    let A : ℝ := ∑ p ∈ P, (p : ℝ)⁻¹
    (((Finset.Icc 1 k).filter fun i => ∀ p ∈ P, ¬ p ∣ n+i).card : ℝ) * A^2
      ≤ (k : ℝ)*A + 3*(P.card : ℝ)^2 := by
  classical
  let I := Finset.Icc 1 k
  let z (p i : ℕ) : ℝ := if p ∣ n+i then 1 else 0
  let a (p : ℕ) := (p : ℝ)⁻¹
  let A := ∑ p ∈ P, a p
  let X (i : ℕ) := ∑ p ∈ P, z p i
  let miss (i : ℕ) := ∀ p ∈ P, ¬ p ∣ n+i
  change ((I.filter miss).card : ℝ) * A^2 ≤ (k : ℝ)*A + 3*(P.card : ℝ)^2
  have ha : 0 ≤ A := Finset.sum_nonneg fun p _ => by dsimp [a]; positivity
  have hb : A ≤ (P.card : ℝ) := by
    calc
      A ≤ ∑ p ∈ P, (1:ℝ) := Finset.sum_le_sum fun p h =>
        inv_le_one_of_one_le₀ (by exact_mod_cast (hp p h).one_le)
      _ = _ := by simp
  have hfirst : (k : ℝ)*A - P.card ≤ ∑ i ∈ I, X i := by
    dsimp only [X]
    rw [Finset.sum_comm]
    have h := Finset.sum_le_sum (s := P) fun p h =>
      (interval_count_error n k p (hp p h).pos).1
    simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      nsmul_eq_mul, mul_one, A, a, z, I] using h
  have hpair (p : ℕ) (h₁ : p ∈ P) (q : ℕ) (h₂ : q ∈ P) :
      ∑ i ∈ I, z p i*z q i ≤ (k:ℝ)*a p*a q +
        (if p=q then (k:ℝ)*a p else 0) + 1 := by
    by_cases h : p=q
    · subst q
      have he (i : ℕ) : z p i*z p i = z p i := by
        dsimp [z]; split_ifs <;> norm_num
      simp only [he, if_true]
      have ht := (interval_count_error n k p (hp p h₁).pos).2
      change ∑ i ∈ I, z p i ≤ (k:ℝ)*a p + 1 at ht
      have hv : 0 ≤ (k:ℝ)*a p*a p := by dsimp [a]; positivity
      linarith
    · have hc := (Nat.coprime_primes (hp p h₁) (hp q h₂)).2 h
      have he (i : ℕ) : z p i*z q i = if p*q ∣ n+i then 1 else 0 := by
        have hh : p*q ∣ n+i ↔ p ∣ n+i ∧ q ∣ n+i := by
          constructor
          · intro hi
            exact ⟨(dvd_mul_right p q).trans hi, (dvd_mul_left q p).trans hi⟩
          · rintro ⟨hp', hq'⟩
            exact hc.mul_dvd_of_dvd_of_dvd hp' hq'
        dsimp only [z]
        by_cases hp' : p ∣ n+i <;> by_cases hq' : q ∣ n+i <;> simp [hh,hp',hq']
      simp only [he, if_neg h, add_zero]
      have ht := (interval_count_error n k (p*q) (Nat.mul_pos (hp p h₁).pos (hp q h₂).pos)).2
      simpa only [Nat.cast_mul, mul_inv_rev, I, a, mul_comm, mul_left_comm, mul_assoc] using ht
  have hsecond : ∑ i ∈ I, (X i)^2 ≤ (k:ℝ)*A*A + (k:ℝ)*A + (P.card:ℝ)^2 := by
    calc
      ∑ i ∈ I, (X i)^2 = ∑ p ∈ P, ∑ i ∈ I, ∑ q ∈ P, z p i*z q i := by
        dsimp only [X]
        simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = ∑ p ∈ P, ∑ q ∈ P, ∑ i ∈ I, z p i*z q i :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ ≤ ∑ p ∈ P, ∑ q ∈ P, ((k:ℝ)*a p*a q + (if p=q then (k:ℝ)*a p else 0) + 1) :=
        Finset.sum_le_sum fun p h₁ => Finset.sum_le_sum fun q h₂ => hpair p h₁ q h₂
      _ = ∑ p ∈ P, ((k:ℝ)*a p*A + (k:ℝ)*a p + P.card) := by
        refine Finset.sum_congr rfl fun p h => ?_
        simp [Finset.sum_add_distrib, ← Finset.mul_sum, A, h]
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const,
          nsmul_eq_mul, pow_two, A]
  have hpt (i : ℕ) : (if miss i then A^2 else 0) ≤ (X i-A)^2 := by
    split_ifs with hi
    · have he : X i=0 := Finset.sum_eq_zero fun p hp' => by simp [z, hi p hp']
      simp [he]
    · positivity
  have hsum := Finset.sum_le_sum (s := I) fun i _ => hpt i
  have hcard : I.card=k := by simp [I]
  have he (i : ℕ) : (X i-A)^2 = (X i)^2 - (2*A)*X i + A^2 := by ring
  simp_rw [he] at hsum
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hcard] at hsum
  nlinarith only [hsum, hsecond, mul_nonneg ha (sub_nonneg.mpr hfirst),
    mul_nonneg (sub_nonneg.mpr hb) (Nat.cast_nonneg (α:=ℝ) P.card)]

/-- With primes at most `b` and `b² ≤ k`, the missed proportion is at most `4/A`. -/
theorem misses_le_of_prime_bound (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime) (n k b : ℕ)
    (hb : ∀ p ∈ P, p ≤ b) (hk : b^2 ≤ k)
    (hA : 1 ≤ ∑ p ∈ P, (p : ℝ)⁻¹) :
    (((Finset.Icc 1 k).filter fun i => ∀ p ∈ P, ¬ p ∣ n+i).card : ℝ)
      ≤ 4 * k / (∑ p ∈ P, (p : ℝ)⁻¹) := by
  let A := ∑ p ∈ P, (p : ℝ)⁻¹
  let m := ((Finset.Icc 1 k).filter fun i => ∀ p ∈ P, ¬ p ∣ n+i).card
  change (1:ℝ) ≤ A at hA
  change (m:ℝ) ≤ 4*k/A
  have hpos : 0 < A := by linarith
  have hc : P.card ≤ b := by
    calc
      P.card ≤ (Finset.Icc 1 b).card :=
        Finset.card_le_card fun p h => Finset.mem_Icc.mpr ⟨(hp p h).one_le, hb p h⟩
      _ = b := by simp
  have hs : (P.card:ℝ)^2 ≤ k := by exact_mod_cast (Nat.pow_le_pow_left hc 2).trans hk
  have he : (m:ℝ)*A^2 ≤ (k:ℝ)*A + 3*(P.card:ℝ)^2 :=
    misses_mul_reciprocal_sum_sq P hp n k
  rw [le_div_iff₀ hpos]
  apply (mul_le_mul_iff_left₀ hpos).mp
  nlinarith only [he, hs, mul_nonneg (Nat.cast_nonneg (α:=ℝ) k) (sub_nonneg.mpr hA)]

/-- Uniform sieve bound with the power cutoff used by the prime annulus. -/
theorem misses_le_of_fourth_root (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime) (n k : ℕ)
    (hk : 1 ≤ k) (hb : ∀ p ∈ P, (p:ℝ) ≤ (k:ℝ)^(1/4:ℝ))
    (hA : 1 ≤ ∑ p ∈ P, (p : ℝ)⁻¹) :
    (((Finset.Icc 1 k).filter fun i => ∀ p ∈ P, ¬ p ∣ n+i).card : ℝ)
      ≤ 4 * k / (∑ p ∈ P, (p : ℝ)⁻¹) := by
  let b := ⌊(k:ℝ)^(1/4:ℝ)⌋₊
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hpos : 0 ≤ (k:ℝ)^(1/4:ℝ) := by positivity
  apply misses_le_of_prime_bound P hp n k b (fun p h => (Nat.le_floor_iff hpos).2 (hb p h)) _ hA
  have h₁ : (b:ℝ) ≤ (k:ℝ)^(1/4:ℝ) := Nat.floor_le hpos
  have h₂ := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ b) h₁ 2
  have he : ((k:ℝ)^(1/4:ℝ))^2 = (k:ℝ)^(1/2:ℝ) := by
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  rw [he] at h₂
  have h₃ : (k:ℝ)^(1/2:ℝ) ≤ k := by
    simpa using Real.rpow_le_rpow_of_exponent_le hk' (show (1/2:ℝ) ≤ 1 by norm_num)
  exact_mod_cast h₂.trans h₃

end IntervalSieve

open Finset MeasureTheory Real Filter

namespace IntervalSieve

private theorem crude_prime_count_lower (x : ℝ) (hx : 64 ≤ x) :
    x / (4 * log x) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hx' : 1 < x := by linarith
  have h₂ := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
  norm_num at h₂
  have h₈ := Real.log_le_sub_one_of_pos (x := 8) (by norm_num)
  have hlog := Real.log_le_sub_one_of_pos (x := (x+2)/8) (by linarith)
  rw [Real.log_div (by linarith) (by norm_num)] at hlog
  have h := Chebyshev.pi_ge' hx'
  apply le_trans _ h
  have he : x/(4*log x) = (x/4)/log x := by ring
  rw [he]
  apply div_le_div_of_nonneg_right _ (Real.log_pos hx').le
  nlinarith [mul_nonneg (sub_nonneg.mpr hx'.le) (sub_nonneg.mpr h₂)]

private theorem prime_reciprocal_annulus_lower (a b : ℝ) (ha : 64 ≤ a) (hab : a ≤ b) :
    (log (log b) - log (log a))/4 - 2 ≤
      ∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ := by
  let c (n : ℕ) : ℝ := if n.Prime then 1 else 0
  have count (t : ℝ) : ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k = (Nat.primeCounting ⌊t⌋₊ : ℝ) := by
    simp [c, Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range,
      Nat.range_succ_eq_Icc_zero]
  have apos : 0 < a := by linarith
  have bpos : 0 < b := by linarith
  have pos (x : ℝ) (hx : x ∈ Set.Icc a b) : 1 < x := by linarith [hx.1]
  have hn (x : ℝ) (hx : x ∈ Set.Icc a b) : x ≠ 0 := by linarith [pos x hx]
  have hdinv (t : ℝ) (ht : t ∈ Set.Icc a b) :
      deriv (fun x : ℝ => x⁻¹) t = -(t^2)⁻¹ := by
    simp
  have hsqr : ContinuousOn (fun t : ℝ => (t^2)⁻¹) (Set.Icc a b) := by
    exact (continuousOn_id.pow 2).inv₀ fun t ht => pow_ne_zero _ (hn t ht)
  have hint : IntegrableOn (deriv fun x : ℝ => x⁻¹) (Set.Icc a b) :=
    (hsqr.neg.congr fun t ht => hdinv t ht).integrableOn_Icc
  have hab' := sum_mul_eq_sub_sub_integral_mul c apos.le hab
    (f := fun x : ℝ => x⁻¹)
    (fun t ht => (hasDerivAt_inv (hn t ht)).differentiableAt) hint
  have lhs : ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (k : ℝ)⁻¹ * c k =
      ∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ := by
    simp [Finset.sum_filter, c, mul_ite]
  rw [lhs, count, count, ← intervalIntegral.integral_of_le hab] at hab'
  have intEq :
      (∫ t in a..b, deriv (fun x : ℝ => x⁻¹) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =
      -(∫ t in a..b, (t^2)⁻¹ * (Nat.primeCounting ⌊t⌋₊ : ℝ)) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hab] at ht
    rw [count, hdinv t ht, neg_mul]
  rw [intEq, sub_neg_eq_add] at hab'
  have hu : a⁻¹ * (Nat.primeCounting ⌊a⌋₊ : ℝ) ≤ 2 := by
    have hc : Nat.primeCounting ⌊a⌋₊ ≤ ⌊a⌋₊ + 1 := Nat.count_le _
    have hx : (Nat.primeCounting ⌊a⌋₊ : ℝ) ≤ (⌊a⌋₊ : ℝ) + 1 := by exact_mod_cast hc
    rw [mul_comm, ← div_eq_mul_inv, div_le_iff₀ apos]
    linarith [Nat.floor_le apos.le]
  have hb : 0 ≤ b⁻¹ * (Nat.primeCounting ⌊b⌋₊ : ℝ) := by positivity
  let g (x : ℝ) := (4*x*log x)⁻¹
  have hgc : ContinuousOn g (Set.Icc a b) := by
    refine ((continuousOn_const.mul continuousOn_id).mul
      (Real.continuousOn_log.mono ?_)).inv₀ ?_
    · exact fun x hx => hn x hx
    · intro x hx
      exact mul_ne_zero (mul_ne_zero (by norm_num) (hn x hx)) (Real.log_pos (pos x hx)).ne'
  have hgint : IntervalIntegrable g volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hgc.integrableOn_Icc
  have htint : IntervalIntegrable
      (fun t : ℝ => (t^2)⁻¹ * (Nat.primeCounting ⌊t⌋₊ : ℝ)) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    simpa only [count] using integrableOn_mul_sum_Icc (m := 0) c apos.le hsqr.integrableOn_Icc
  have hcompare : ∫ t in a..b, g t ≤ ∫ t in a..b, (t^2)⁻¹ * (Nat.primeCounting ⌊t⌋₊ : ℝ) := by
    apply intervalIntegral.integral_mono_on hab hgint htint
    intro t ht
    have h₁ := crude_prime_count_lower t (ha.trans ht.1)
    have h₂ : 0 < t := by linarith [pos t ht]
    calc
      g t = (t^2)⁻¹ * (t / (4 * log t)) := by
        dsimp [g]
        field_simp [h₂.ne', (Real.log_pos (pos t ht)).ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left h₁ (by positivity)
  have hf : (∫ t in a..b, g t) = log (log b)/4 - log (log a)/4 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hgint
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have h := ((Real.hasDerivAt_log (hn t ht)).log (Real.log_pos (pos t ht)).ne').div_const 4
    simpa only [g, div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using h
  rw [hf] at hcompare
  linarith

/-- Every prescribed reciprocal mass fits eventually in a fixed power range inside `k^(1/4)`. -/
theorem eventually_prime_annulus_mass (M : ℝ) (hM : 0 < M) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/4 ∧ ∀ᶠ k : ℕ in atTop, ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ (k:ℝ)^δ < p ∧ (p:ℝ) ≤ (k:ℝ)^(1/4:ℝ)) ∧
      M ≤ ∑ p ∈ P, (p : ℝ)⁻¹ := by
  let δ := (1/4:ℝ) * exp (-(4*(M+2)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hd : δ ≤ 1/4 := by
    have ht : exp (-(4*(M+2))) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    dsimp [δ]
    linarith
  refine ⟨δ, hδ, hd, ?_⟩
  have ht : Tendsto (fun k : ℕ => (k:ℝ)^δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop 64, eventually_ge_atTop 2] with k h₁ hk
  have hk' : (1:ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hkl : 0 < log (k:ℝ) := Real.log_pos hk'
  have hkpos : 0 < (k:ℝ) := by linarith
  have h₂ := Real.rpow_le_rpow_of_exponent_le hk'.le hd
  let P := (Finset.Ioc ⌊(k:ℝ)^δ⌋₊ ⌊(k:ℝ)^(1/4:ℝ)⌋₊).filter Nat.Prime
  refine ⟨P, ?_, ?_⟩
  · intro p hp
    obtain ⟨hi, hprime⟩ := Finset.mem_filter.mp hp
    obtain ⟨hl, hu⟩ := Finset.mem_Ioc.mp hi
    exact ⟨hprime, (Nat.floor_lt (by positivity)).mp hl,
      (Nat.le_floor_iff (by positivity)).mp hu⟩
  · have he := prime_reciprocal_annulus_lower _ _ h₁ h₂
    rw [Real.log_rpow hkpos, Real.log_rpow hkpos, Real.log_mul (by norm_num) hkl.ne',
        Real.log_mul hδ.ne' hkl.ne'] at he
    have hl : log δ = log (1/4 : ℝ) - 4*(M+2) := by
      dsimp only [δ]
      rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
      ring
    rw [hl] at he
    change M ≤ ∑ p ∈ (Finset.Ioc ⌊(k:ℝ)^δ⌋₊ ⌊(k:ℝ)^(1/4:ℝ)⌋₊).filter Nat.Prime, (p:ℝ)⁻¹
    linarith

end IntervalSieve

open Finset Filter Real
namespace ErdInterval


private lemma smoothLog_exact {k m : ℕ} (hs : ∀ p ∈ m.primeFactors, p ≤ k) :
    (∑ p ∈ Nat.primesLE k, (m.factorization p : ℝ) * Real.log p) = Real.log m := by
  rw [Real.log_nat_eq_sum_factorization]
  change _ = ∑ p ∈ m.primeFactors, (m.factorization p : ℝ) * Real.log p
  symm
  apply Finset.sum_subset (fun p hp => Nat.mem_primesLE.mpr ⟨hs p hp, Nat.prime_of_mem_primeFactors hp⟩)
  intro p _ hp
  have h : m.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
  simp [h]

private lemma interval_factor_budget (n k : ℕ) (hk : 0 < k) :
    (∑ i ∈ Icc 1 k, ∑ p ∈ Nat.primesLE k, ((n+i).factorization p : ℝ) * Real.log p) ≤
      (k : ℝ) * Real.log k + (Nat.primeCounting k : ℝ) * Real.log (n+k : ℕ) := by
  let I := Icc 1 k
  let P := Nat.primesLE k
  have nz : ∀ i ∈ I, n+i ≠ 0 := by
    intro i hi
    have := (mem_Icc.mp hi).1
    omega
  have hprod : ∀ j : ℕ, (∏ i ∈ Icc 1 j, (n+i)) = (n+1).ascFactorial j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [prod_Icc_succ_top (by omega), ih, Nat.ascFactorial_succ]
      ring
  have fac (p : ℕ) : (∑ i ∈ I, (n+i).factorization p) =
      k.factorial.factorization p + ((n+k).choose k).factorization p := by
    have aux := congrArg (fun (a : ℕ →₀ ℕ) => a p) (Nat.factorization_prod nz)
    change ((∏ i ∈ Icc 1 k, (n+i)).factorization p) = _ at aux
    rw [hprod, Nat.ascFactorial_eq_factorial_mul_choose, Nat.factorization_mul
      (Nat.factorial_ne_zero _) (Nat.choose_pos (by omega)).ne'] at aux
    simpa [Finsupp.finsetSum_apply] using aux.symm
  have each (p : ℕ) (hp : p ∈ P) :
      ((Nat.choose (n+k) k).factorization p : ℝ) * Real.log p ≤ Real.log (n+k : ℕ) := by
    have := Nat.pow_factorization_choose_le (p := p) (k := k) (by omega : 0 < n+k)
    have hpos : 0 < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos
    have bound := Real.log_le_log (pow_pos hpos _) (show (p : ℝ)^((n+k).choose k).factorization p ≤ (n+k : ℕ) by exact_mod_cast this)
    simpa [Real.log_pow] using bound
  have fact : (∑ p ∈ P, (k.factorial.factorization p : ℝ)*Real.log p) = Real.log k.factorial :=
    smoothLog_exact (fun p hp => (Nat.Prime.dvd_factorial (Nat.prime_of_mem_primeFactors hp)).mp
      (Nat.dvd_of_mem_primeFactors hp))
  have factBound : Real.log k.factorial ≤ k * Real.log k := by
    have hb : (k.factorial : ℝ) ≤ (k : ℝ)^k := by exact_mod_cast Nat.factorial_le_pow k
    simpa [Real.log_pow] using Real.log_le_log (by exact_mod_cast Nat.factorial_pos k) hb
  change (∑ i ∈ I, ∑ p ∈ P, _) ≤ _
  rw [sum_comm]
  calc
    _ = ∑ p ∈ P, ((k.factorial.factorization p : ℝ) +
        ((n+k).choose k).factorization p) * Real.log p := by
      apply sum_congr rfl
      intro p hp
      rw [← sum_mul, ← Nat.cast_sum, fac, Nat.cast_add]
    _ = (∑ p ∈ P, (k.factorial.factorization p : ℝ)*Real.log p) +
        ∑ p ∈ P, (((n+k).choose k).factorization p : ℝ)*Real.log p := by
      simp only [add_mul, sum_add_distrib]
    _ ≤ _ := by
      rw [fact]
      apply add_le_add factBound
      calc
        _ ≤ ∑ _p ∈ P, Real.log (n+k : ℕ) := sum_le_sum each
        _ = _ := by simp [P, Nat.primesLE_card_eq_primeCounting]

private lemma weight_lower {k m p : ℕ} (hm : m ≠ 0) (hp : p ∈ Nat.primesLE k) (hd : p ∣ m) :
    Real.log p ≤ ∑ q ∈ Nat.primesLE k, (m.factorization q : ℝ) * Real.log q := by
  have hprime := Nat.prime_of_mem_primesLE hp
  have hfac : (1 : ℝ) ≤ m.factorization p := by exact_mod_cast hprime.factorization_pos_of_dvd hm hd
  have hl : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_le)
  calc
    _ ≤ (m.factorization p : ℝ) * Real.log p := by nlinarith
    _ ≤ _ := single_le_sum (f := fun q => (m.factorization q : ℝ) * Real.log q) (fun q hq => mul_nonneg (by positivity)
      (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hq).one_le))) hp

/-- The logarithmic mass of small factors bounds the count of smooth terms.
A medium prime in a nonsmooth term consumes some of the same mass. -/
private lemma weighted_interval (n k : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (P : Finset ℕ) (hP : P ⊆ Nat.primesLE k) (b : ℝ) (hb : 0 ≤ b)
    (hlog : ∀ p ∈ P, b ≤ Real.log p) :
    ((k : ℝ) - Erdos1184.f n k) * (Real.log (n+k : ℕ) - Real.log 2) +
      ((Erdos1184.f n k : ℝ) - (((Icc 1 k).filter (fun i => ∀ p ∈ P, ¬ p ∣ n+i)).card : ℝ)) * b ≤
    (k : ℝ) * Real.log k + (Nat.primeCounting k : ℝ) * Real.log (n+k : ℕ) := by
  classical
  let I := Icc 1 k
  let a := Real.log (n+k : ℕ) - Real.log 2
  let R (i : ℕ) := k < (n+i).maxPrimeFac
  let B (i : ℕ) := ∀ p ∈ P, ¬ p ∣ n+i
  let w (i : ℕ) := ∑ p ∈ Nat.primesLE k, ((n+i).factorization p : ℝ) * Real.log p
  have w0 (i : ℕ) : 0 ≤ w i := sum_nonneg (fun p hp => mul_nonneg (by positivity)
    (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le)))
  have per (i : ℕ) (hi : i ∈ I) :
      a + (if R i then b-a else 0) - (if B i then b else 0) ≤ w i := by
    have hit := (mem_Icc.mp hi).1
    have hm : n+i ≠ 0 := by omega
    by_cases hR : R i
    · by_cases hB : B i
      · simpa [hR,hB] using w0 i
      · have hex : ∃ p ∈ P, p ∣ n+i := by simpa [B] using hB
        obtain ⟨p,hp,hd⟩ := hex
        simpa [hR,hB] using (hlog p hp).trans (weight_lower hm (hP hp) hd)
    · have hal : a ≤ w i := by
        dsimp only [w]
        rw [smoothLog_exact (fun p hp => le_trans (Nat.le_maxPrimeFac hm
          (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)) (not_lt.mp hR))]
        have hl : Real.log (n+k : ℕ) ≤ Real.log (2 * (n+i : ℕ) : ℕ) := by
          apply Real.log_le_log (by positivity)
          exact_mod_cast (by omega : n+k ≤ 2*(n+i))
        push_cast at hl
        rw [Real.log_mul (by norm_num) (by positivity)] at hl
        dsimp only [a]
        push_cast
        linarith
      by_cases hB : B i <;> simp [hR,hB] <;> linarith
  have total := (sum_le_sum per).trans (interval_factor_budget n k (by omega))
  have cardI : I.card = k := by simp [I]
  have countR : (I.filter R).card = Erdos1184.f n k := rfl
  simp only [sum_sub_distrib, sum_add_distrib] at total
  rw [← sum_filter R (fun _ => b-a), ← sum_filter B (fun _ => b)] at total
  simp only [sum_const, nsmul_eq_mul,cardI,countR] at total
  change ((k : ℝ) - ↑(Erdos1184.f n k)) * a + (↑(Erdos1184.f n k) - ↑((I.filter B).card)) * b ≤ _
  linarith



private lemma fraction_gap {α δ γ ε x z b e h : ℝ}
    (hα : 1 < α) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hscale : α*(1-γ) = 1) (hc : 16*α*ε = δ*γ)
    (hx : 0 ≤ x) (he : 0 ≤ e) (hea : e ≤ α*ε) (hb : b ≤ ε)
    (hz : α ≤ z) (hh : h ≤ γ/2)
    (hbudget : (1-x)*(z-e) + (x-h)*δ ≤ 1+b*z) : γ+ε < x := by
  by_contra! hsmall
  have ha := le_of_lt hα
  have hε : 0 ≤ ε := by
    by_contra! hc'
    have := mul_neg_of_pos_of_neg (by linarith : 0 < 16*α) hc'
    nlinarith [mul_pos hδ hγ]
  have hδε := mul_nonneg hδ.le hε
  have hδγ : δ*γ ≤ 1 := (mul_le_mul_of_nonneg_right hδ1 hγ.le).trans (by simpa using hγ1)
  have hαx := mul_nonneg (by linarith : 0 ≤ α) (sub_nonneg.mpr hsmall)
  have hαb := mul_nonneg (by linarith : 0 ≤ α) (sub_nonneg.mpr hb)
  have hpos : 0 ≤ 1-x-b := by
    by_contra! hn
    have := mul_neg_of_pos_of_neg (by linarith : 0 < α) hn
    nlinarith
  have bound := mul_nonneg hpos (sub_nonneg.mpr hz)
  have hand := mul_nonneg (by linarith : 0 ≤ α-δ) (sub_nonneg.mpr hsmall)
  have hdh := mul_nonneg hδ.le (sub_nonneg.mpr hh)
  nlinarith [mul_nonneg hx he, mul_pos hδ hγ]

/-- Prime density and the constant loss from replacing an endpoint by half of it
both tend to zero. -/
private lemma small_errors {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, 1 < k ∧
      (Nat.primeCounting k : ℝ) ≤ ε*k ∧ Real.log 2 ≤ ε*Real.log k := by
  have hp := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num))
  have ht := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [hp, ht.eventually_ge_atTop ((Real.log 4+1)/ε),
    ht.eventually_ge_atTop (Real.log 2/ε), eventually_gt_atTop 1] with k hp h1 h2 hk
  simp only [Nat.floor_natCast] at hp
  change (Real.log 4+1)/ε ≤ Real.log (k : ℝ) at h1
  change Real.log 2/ε ≤ Real.log (k : ℝ) at h2
  have hl := Real.log_pos (by exact_mod_cast hk : (1 : ℝ) < k)
  refine ⟨hk,hp.trans ?_, ?_⟩
  · apply (div_le_iff₀ hl).mpr
    have := mul_le_mul_of_nonneg_right ((div_le_iff₀ hε).mp h1) (Nat.cast_nonneg k : (0:ℝ) ≤ k)
    nlinarith
  · linarith [(div_le_iff₀ hε).mp h2]

private lemma finish_lower
    (sieve : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ᶠ k : ℕ in atTop,
      ∀ n : ℕ, ∃ P : Finset ℕ, P ⊆ Nat.primesLE k ∧
        (∀ p ∈ P, δ * Real.log k ≤ Real.log p) ∧
        ((((Icc 1 k).filter (fun i => ∀ p ∈ P, ¬ p ∣ n+i)).card : ℝ)) ≤ η*k) :
    type_of% @Erdos1184.erdos_1184.variants.lower := by
  intro α hα
  have hα0 : 0 < α := by linarith
  let γ := 1-1/α
  have hγ : 0 < γ := by dsimp [γ]; rw [sub_pos,div_lt_one hα0]; exact hα
  have hγ1 : γ ≤ 1 := by dsimp [γ]; linarith [one_div_pos.mpr hα0]
  have hscale : α*(1-γ) = 1 := by dsimp [γ]; field_simp; ring
  obtain ⟨δ,hδ,hδ1,hs⟩ := sieve (γ/2) (by positivity)
  let ε := δ*γ/(16*α)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hc : 16*α*ε = δ*γ := by dsimp [ε]; field_simp
  refine ⟨ε,hε,?_⟩
  have grow := (tendsto_rpow_atTop (sub_pos.mpr hα)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hs, small_errors hε, grow.eventually_ge_atTop 2] with k hs he hg
  obtain ⟨hk,hπ,he⟩ := he
  intro n hn
  have hK : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hL : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast hk)
  have hNk : (k : ℝ)^α ≤ (n+k : ℕ) := by push_cast; linarith
  have hkn : k ≤ n := by
    change 2 ≤ (k : ℝ)^(α-1) at hg
    have hh := mul_le_mul_of_nonneg_right hg hK.le
    rw [← Real.rpow_add_one hK.ne', sub_add_cancel] at hh
    push_cast at hNk
    exact_mod_cast (by linarith : (k : ℝ) ≤ n)
  have hN : α * Real.log k ≤ Real.log (n+k : ℕ) := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hK α) hNk
    simpa [Real.log_rpow hK] using hh
  obtain ⟨P,hP,hlog,hm⟩ := hs n
  let m := ((Icc 1 k).filter (fun i => ∀ p ∈ P, ¬ p ∣ n+i)).card
  let f := Erdos1184.f n k
  let L := Real.log (k : ℝ)
  let Z := Real.log (n+k : ℕ)
  change (m : ℝ) ≤ γ/2 * k at hm
  have hw := weighted_interval n k hk hkn P hP (δ*L) (mul_nonneg hδ.le hL.le) hlog
  change ((k : ℝ)-f)*(Z-Real.log 2)+((f : ℝ)-m)*(δ*L) ≤ k*L+(Nat.primeCounting k : ℝ)*Z at hw
  have he' : Real.log 2/L ≤ α*ε := by
    apply (div_le_iff₀ hL).mpr
    change Real.log 2 ≤ ε*L at he
    have hεL : 0 ≤ ε*L := mul_nonneg hε.le hL.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hα.le) hεL]
  have hbudget :
      (1-(f:ℝ)/k)*(Z/L-Real.log 2/L) + ((f:ℝ)/k-(m:ℝ)/k)*δ ≤
        1+((Nat.primeCounting k : ℝ)/k)*(Z/L) := by
    have hLL : L ≠ 0 := hL.ne'
    calc
      _ = (((k:ℝ)-f)*(Z-Real.log 2)+((f:ℝ)-m)*(δ*L))/((k:ℝ)*L) := by
        field_simp [hK.ne',hLL]
      _ ≤ ((k:ℝ)*L+(Nat.primeCounting k:ℝ)*Z)/((k:ℝ)*L) :=
        div_le_div_of_nonneg_right hw (mul_nonneg hK.le hL.le)
      _ = _ := by field_simp [hK.ne',hLL]
  have got := fraction_gap hα hδ hδ1 hγ hγ1 hscale hc
    (div_nonneg (Nat.cast_nonneg f) hK.le)
    (div_nonneg (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)) hL.le) he'
    ((div_le_iff₀ hK).mpr hπ) ((le_div_iff₀ hL).mpr hN)
    ((div_le_iff₀ hK).mpr hm) hbudget
  change (k:ℝ) * (γ+ε) < (f:ℝ)
  simpa [mul_comm] using (lt_div_iff₀ hK).mp got

end ErdInterval

open ErdInterval IntervalSieve

theorem OMA.solution : type_of% @Erdos1184.erdos_1184.variants.lower := by
  apply finish_lower
  intro η hη
  let M := max 1 (4/η)
  have hM1 : 1 ≤ M := le_max_left ..
  have hMη : 4/η ≤ M := le_max_right ..
  obtain ⟨δ,hδ,hδ1,hwindow⟩ := eventually_prime_annulus_mass M (lt_of_lt_of_le zero_lt_one hM1)
  refine ⟨δ,hδ,by linarith,?_⟩
  filter_upwards [hwindow, eventually_ge_atTop 1] with k hwindow hk
  obtain ⟨P,hP,hA⟩ := hwindow
  have hKr : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hK : 0 < (k:ℝ) := by linarith
  have hbound : (k:ℝ)^(1/4:ℝ) ≤ k := by
    simpa using Real.rpow_le_rpow_of_exponent_le hKr (show (1/4:ℝ) ≤ 1 by norm_num)
  have hpos : 0 < ∑ p ∈ P, (p:ℝ)⁻¹ := lt_of_lt_of_le zero_lt_one (hM1.trans hA)
  intro n
  refine ⟨P,fun p hp => Nat.mem_primesLE.mpr
    ⟨by exact_mod_cast ((hP p hp).2.2.trans hbound),(hP p hp).1⟩,?_,?_⟩
  · intro p hp
    have he := Real.log_le_log (Real.rpow_pos_of_pos hK δ) (hP p hp).2.1.le
    simpa [Real.log_rpow hK] using he
  · refine (misses_le_of_fourth_root P (fun p hp => (hP p hp).1) n k hk
      (fun p hp => (hP p hp).2.2) (hM1.trans hA)).trans ?_
    rw [div_le_iff₀ hpos]
    have he := (div_le_iff₀ hη).mp (hMη.trans hA)
    nlinarith only [mul_le_mul_of_nonneg_right he hK.le]
