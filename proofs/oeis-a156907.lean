import OMAStatements.S_oeis_a156907
import Mathlib

namespace OMA.S_oeis_a156907

open PowerSeries BigOperators

/-! ### Part 1: `p`-integrality of rationals -/

private def isPInt (p : ℕ) (q : ℚ) : Prop :=
  ∃ (num : ℤ) (den : ℕ), ¬ p ∣ den ∧ q = (num : ℚ) / (den : ℚ)

private lemma isPInt_int {p : ℕ} (hp : p.Prime) (z : ℤ) : isPInt p (z : ℚ) :=
  ⟨z, 1, hp.not_dvd_one, by simp⟩

private lemma isPInt_zero {p : ℕ} (hp : p.Prime) : isPInt p 0 :=
  ⟨0, 1, hp.not_dvd_one, by simp⟩

private lemma isPInt_neg {p : ℕ} {x : ℚ} (hx : isPInt p x) : isPInt p (-x) := by
  obtain ⟨a, b, hb, rfl⟩ := hx
  exact ⟨-a, b, hb, by push_cast; ring⟩

private lemma isPInt_add {p : ℕ} (hp : p.Prime) {x y : ℚ} (hx : isPInt p x) (hy : isPInt p y) :
    isPInt p (x + y) := by
  obtain ⟨a, b, hb, rfl⟩ := hx
  obtain ⟨c, d, hd, rfl⟩ := hy
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by intro h; subst h; exact hb (dvd_zero p))
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by intro h; subst h; exact hd (dvd_zero p))
  refine ⟨a * d + c * b, b * d, fun h => (hp.dvd_mul.mp h).elim hb hd, ?_⟩
  push_cast; field_simp [hb0, hd0]

private lemma isPInt_sub {p : ℕ} (hp : p.Prime) {x y : ℚ} (hx : isPInt p x) (hy : isPInt p y) :
    isPInt p (x - y) := by
  rw [sub_eq_add_neg]; exact isPInt_add hp hx (isPInt_neg hy)

private lemma isPInt_mul {p : ℕ} (hp : p.Prime) {x y : ℚ} (hx : isPInt p x) (hy : isPInt p y) :
    isPInt p (x * y) := by
  obtain ⟨a, b, hb, rfl⟩ := hx
  obtain ⟨c, d, hd, rfl⟩ := hy
  refine ⟨a * c, b * d, fun h => (hp.dvd_mul.mp h).elim hb hd, ?_⟩
  push_cast; ring

private lemma isPInt_pow {p : ℕ} (hp : p.Prime) {x : ℚ} (hx : isPInt p x) :
    ∀ k : ℕ, isPInt p (x ^ k)
  | 0 => by simpa using isPInt_int hp 1
  | k + 1 => by rw [pow_succ]; exact isPInt_mul hp (isPInt_pow hp hx k) hx

private lemma isPInt_sum {ι : Type*} {p : ℕ} (hp : p.Prime) (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, isPInt p (f i)) : isPInt p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPInt_zero hp
  | @insert a s has ih =>
      rw [Finset.sum_insert has]
      exact isPInt_add hp (hf a (Finset.mem_insert_self a s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma isPInt_div_nat {p : ℕ} (hp : p.Prime) {x : ℚ} (hx : isPInt p x)
    {u : ℕ} (hu : ¬ p ∣ u) : isPInt p (x / (u : ℚ)) := by
  obtain ⟨a, b, hb, rfl⟩ := hx
  refine ⟨a, b * u, fun h => (hp.dvd_mul.mp h).elim hb hu, ?_⟩
  rw [div_div, Nat.cast_mul]

private lemma not_dvd_den_of_isPInt {p : ℕ} (hp : p.Prime) {q : ℚ} (hq : isPInt p q) :
    ¬ p ∣ q.den := by
  obtain ⟨a, b, hb, heq⟩ := hq
  have hb0 : b ≠ 0 := fun h => hb (h ▸ dvd_zero p)
  have h1 : (q.num : ℚ) * (b : ℚ) = (a : ℚ) * (q.den : ℚ) := by
    have hq_eq : q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
    rw [hq_eq] at heq
    have hqd0 : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
    have hbq0 : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
    field_simp [hqd0, hbq0] at heq
    linarith
  have hz : q.num * (b : ℤ) = a * (q.den : ℤ) := by exact_mod_cast h1
  intro hpd
  have hpdz : (p : ℤ) ∣ (q.den : ℤ) := Int.natCast_dvd_natCast.mpr hpd
  have hprod : (p : ℤ) ∣ q.num * (b : ℤ) := by rw [hz]; exact dvd_mul_of_dvd_right hpdz a
  have hpn : (p : ℤ) ∣ q.num := by
    have hcop : IsCoprime (p : ℤ) (b : ℤ) := (hp.coprime_iff_not_dvd.mpr hb).isCoprime
    exact hcop.dvd_of_dvd_mul_right hprod
  have hp_num : p ∣ q.num.natAbs := by
    obtain ⟨t, ht⟩ := hpn
    exact ⟨t.natAbs, by
      have := congr_arg Int.natAbs ht
      simpa [Int.natAbs_mul] using this⟩
  have hcop_q : Nat.Coprime q.num.natAbs q.den := q.reduced
  exact hp.not_dvd_one (hcop_q ▸ Nat.dvd_gcd hp_num hpd)

private lemma isInt_of_forall_prime_isPInt {q : ℚ} (h : ∀ p : ℕ, p.Prime → isPInt p q) :
    ∃ z : ℤ, q = (z : ℚ) := by
  have hden : q.den = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    exact not_dvd_den_of_isPInt hp (h p hp) hpd
  refine ⟨q.num, ?_⟩
  rw [← Rat.num_div_den q, hden]
  simp

private lemma isPInt_mul_p_inv {p : ℕ} (hp : p.Prime) {x : ℚ} (hx : isPInt p x) :
    isPInt p ((p : ℚ) * x / (p : ℚ)) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rwa [mul_div_cancel_left₀ _ hp0]

private lemma isPInt_of_isPInt_div_p {p : ℕ} (hp : p.Prime) {x : ℚ}
    (hx : isPInt p (x / (p : ℚ))) : isPInt p x := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have heq : x = (p : ℚ) * (x / (p : ℚ)) := by field_simp [hp0]
  rw [heq]
  exact isPInt_mul hp (isPInt_int hp p) hx

/-! ### Part 2: `p`-adic valuation of factorials `v_p(k!) ≤ k - 1` -/

private lemma factorization_factorial_rec {p : ℕ} (hp : p.Prime) :
    ∀ k : ℕ, (Nat.factorial k).factorization p = k / p + (Nat.factorial (k / p)).factorization p := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.factorial_succ, Nat.factorization_mul (Nat.succ_ne_zero k) (Nat.factorial_ne_zero k),
          Finsupp.add_apply, ih]
      by_cases hdiv : p ∣ k + 1
      · obtain ⟨q, hq⟩ := hdiv
        have hq_pos : 1 ≤ q := by
          by_contra h0; have : q = 0 := by omega
          rw [this, mul_zero] at hq; omega
        have hdiv1 : (k + 1) / p = q := by rw [hq, Nat.mul_div_cancel_left _ hp.pos]
        have hdiv0 : k / p = q - 1 := by
          have hkeq : k = p * (q - 1) + (p - 1) := by
            cases q with
            | zero => omega
            | succ q' => rw [Nat.mul_succ] at hq; simp only [Nat.add_sub_cancel]; have := hp.two_le; omega
          rw [hkeq, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt (by have := hp.two_le; omega), add_zero]
        have hfac_q : Nat.factorial q = q * Nat.factorial (q - 1) := by
          cases q with
          | zero => omega
          | succ q' => simp [Nat.factorial_succ]
        rw [Nat.succ_eq_add_one, hdiv1, hdiv0, hq, Nat.factorization_mul hp.ne_zero (by omega), Finsupp.add_apply,
            hp.factorization_self, hfac_q, Nat.factorization_mul (by omega) (Nat.factorial_ne_zero _),
            Finsupp.add_apply]
        omega
      · have hdiv_eq : (k + 1) / p = k / p := by
          have hmod : (k + 1) % p ≠ 0 := fun h => hdiv (Nat.dvd_of_mod_eq_zero h)
          have h1 := Nat.div_add_mod k p
          have h2 := Nat.div_add_mod (k + 1) p
          have hlt1 := Nat.mod_lt k hp.pos
          have hlt2 := Nat.mod_lt (k + 1) hp.pos
          have hp1 : 1 ≤ (k + 1) % p := Nat.pos_of_ne_zero hmod
          by_contra hne
          have hlt : k / p < (k + 1) / p := lt_of_le_of_ne (Nat.div_le_div_right (by omega)) (Ne.symm hne)
          have : p * (k / p + 1) ≤ p * ((k + 1) / p) := Nat.mul_le_mul_left p hlt
          nlinarith
        rw [hdiv_eq, Nat.factorization_eq_zero_of_not_dvd hdiv, zero_add]

private lemma factorization_factorial_lt {p : ℕ} (hp : p.Prime) :
    ∀ k : ℕ, 1 ≤ k → (Nat.factorial k).factorization p ≤ k - 1 := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rw [factorization_factorial_rec hp]
    by_cases hlt : k < p
    · rw [Nat.div_eq_of_lt hlt]; simp
    · have hq_pos : 1 ≤ k / p := Nat.div_pos (by omega) hp.pos
      have hq_lt : k / p < k := Nat.div_lt_self (by omega) hp.one_lt
      have ih' := ih (k / p) hq_lt hq_pos
      have h2q : 2 * (k / p) ≤ k := by
        have := Nat.mul_div_le k p
        have := hp.two_le
        nlinarith
      omega

private lemma isPInt_pow_div_factorial {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) :
    isPInt p ((p : ℚ) ^ (k - 1) / (Nat.factorial k : ℚ)) := by
  set F := Nat.factorial k
  set v := F.factorization p
  set u := F / p ^ v
  have hF_pos : 0 < F := Nat.factorial_pos k
  have hpow_dvd : p ^ v ∣ F := Nat.ordProj_dvd F p
  have hFu : p ^ v * u = F := Nat.mul_div_cancel' hpow_dvd
  have hpu : ¬ p ∣ u := by
    intro h
    have hpow1 : p ^ (v + 1) ∣ F := by
      rw [← hFu, pow_succ]; exact Nat.mul_dvd_mul_left (p ^ v) h
    have hle := (hp.pow_dvd_iff_le_factorization hF_pos.ne').mp hpow1
    omega
  have hv_le : v ≤ k - 1 := factorization_factorial_lt hp k hk
  refine ⟨((p ^ (k - 1 - v) : ℕ) : ℤ), u, hpu, ?_⟩
  have hF_cast : (F : ℚ) = (p : ℚ) ^ v * (u : ℚ) := by exact_mod_cast hFu.symm
  have hpv0 : (p : ℚ) ^ v ≠ 0 := by
    have : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    positivity
  have hu0 : (u : ℚ) ≠ 0 := by
    exact_mod_cast (show u ≠ 0 by intro h; rw [h, mul_zero] at hFu; omega)
  have hexp : (p : ℚ) ^ (k - 1) = (p : ℚ) ^ (k - 1 - v) * (p : ℚ) ^ v := by
    rw [← pow_add]; congr 1; omega
  rw [show (Nat.factorial k : ℚ) = (F : ℚ) from rfl, hF_cast, hexp]
  push_cast
  field_simp [hpv0, hu0]

/-! ### Part 3: Formal `expSeries` and `substPow p` (i.e. `F(X^p)`) -/

private noncomputable def expCoeffs (G : PowerSeries ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      (∑ k : Fin (n + 1),
        ((k.val + 1 : ℕ) : ℚ) * PowerSeries.coeff (k.val + 1) G * expCoeffs G (n - k.val)) /
        ((n + 1 : ℕ) : ℚ)
termination_by n => n
decreasing_by
  have := k.isLt
  omega

private noncomputable def expSeries (G : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (expCoeffs G)

private lemma coeff_zero_expSeries (G : PowerSeries ℚ) :
    PowerSeries.coeff 0 (expSeries G) = 1 := by
  rw [expSeries, PowerSeries.coeff_mk, expCoeffs]

private lemma expSeries_ode (G : PowerSeries ℚ) :
    PowerSeries.X * PowerSeries.derivative ℚ (expSeries G) =
      expSeries G * (PowerSeries.X * PowerSeries.derivative ℚ G) := by
  apply PowerSeries.ext; intro n
  cases n with
  | zero =>
      rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
          ← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_zero_X_mul, mul_zero]
  | succ n =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, expSeries,
          PowerSeries.coeff_mk, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j => PowerSeries.coeff i (PowerSeries.mk (expCoeffs G)) *
              PowerSeries.coeff j (PowerSeries.X * PowerSeries.derivative ℚ G))]
      rw [expCoeffs]
      have hpos : ((n : ℚ) + 1) ≠ 0 := by positivity
      push_cast
      rw [div_mul_cancel₀ _ hpos]
      rw [Finset.sum_range_succ, Nat.sub_self, PowerSeries.coeff_zero_X_mul, mul_zero, add_zero]
      rw [Fin.sum_univ_eq_sum_range
        (fun k => ((k : ℚ) + 1) * PowerSeries.coeff (k + 1) G * expCoeffs G (n - k)) (n + 1)]
      rw [← Finset.sum_range_reflect
        (fun k => ((k : ℚ) + 1) * PowerSeries.coeff (k + 1) G * expCoeffs G (n - k)) (n + 1)]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hilt : i < n + 1 := Finset.mem_range.mp hi
      rw [PowerSeries.coeff_mk]
      have h1 : n + 1 - 1 - i + 1 = n + 1 - i := by omega
      have h2 : n - (n + 1 - 1 - i) = i := by omega
      have h3 : n + 1 - i = (n - i) + 1 := by omega
      rw [h1, h2, h3, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
      have h4 : ((n + 1 - 1 - i : ℕ) : ℚ) + 1 = ((n - i : ℕ) : ℚ) + 1 := by
        rw [show n + 1 - 1 - i = n - i by omega]
      rw [h4]
      ring

private lemma eq_expSeries_upTo {G F : PowerSeries ℚ} {N : ℕ}
    (h0 : PowerSeries.coeff 0 F = 1)
    (hode : ∀ n, 1 ≤ n → n ≤ N →
      PowerSeries.coeff n (PowerSeries.X * PowerSeries.derivative ℚ F) =
      PowerSeries.coeff n (F * (PowerSeries.X * PowerSeries.derivative ℚ G))) :
    ∀ n ≤ N, PowerSeries.coeff n F = PowerSeries.coeff n (expSeries G) := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => rw [h0, coeff_zero_expSeries]
    | succ n =>
        have hF := hode (n + 1) (by omega) hn
        have hE := congr_arg (PowerSeries.coeff (n + 1)) (expSeries_ode G)
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun i j => PowerSeries.coeff i F *
                PowerSeries.coeff j (PowerSeries.X * PowerSeries.derivative ℚ G))] at hF
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun i j => PowerSeries.coeff i (expSeries G) *
                PowerSeries.coeff j (PowerSeries.X * PowerSeries.derivative ℚ G))] at hE
        rw [Finset.sum_range_succ, Nat.sub_self, PowerSeries.coeff_zero_X_mul, mul_zero, add_zero] at hF hE
        have hsum :
            ∑ k ∈ Finset.range (n + 1),
              PowerSeries.coeff k F * PowerSeries.coeff (n + 1 - k) (PowerSeries.X * PowerSeries.derivative ℚ G) =
            ∑ k ∈ Finset.range (n + 1),
              PowerSeries.coeff k (expSeries G) *
                PowerSeries.coeff (n + 1 - k) (PowerSeries.X * PowerSeries.derivative ℚ G) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [ih k (Finset.mem_range.mp hk) (by have := Finset.mem_range.mp hk; omega)]
        rw [hsum, ← hE] at hF
        have hpos : ((n : ℚ) + 1) ≠ 0 := by positivity
        exact mul_right_cancel₀ hpos hF

private lemma eq_expSeries_of_ode {G F : PowerSeries ℚ}
    (h0 : PowerSeries.coeff 0 F = 1)
    (hode : PowerSeries.X * PowerSeries.derivative ℚ F =
      F * (PowerSeries.X * PowerSeries.derivative ℚ G)) :
    F = expSeries G := by
  apply PowerSeries.ext; intro n
  exact eq_expSeries_upTo h0 (fun m _ _ => congr_arg (PowerSeries.coeff m) hode) n (le_refl n)

private lemma expSeries_add (G₁ G₂ : PowerSeries ℚ) :
    expSeries (G₁ + G₂) = expSeries G₁ * expSeries G₂ := by
  symm
  apply eq_expSeries_of_ode
  · rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff,
        coeff_zero_expSeries, coeff_zero_expSeries, mul_one]
  · rw [Derivation.leibniz, map_add, mul_add, mul_add]
    simp only [smul_eq_mul]
    have h1 := expSeries_ode G₁
    have h2 := expSeries_ode G₂
    calc
      PowerSeries.X * (expSeries G₁ * PowerSeries.derivative ℚ (expSeries G₂)) +
          PowerSeries.X * (expSeries G₂ * PowerSeries.derivative ℚ (expSeries G₁))
        = expSeries G₁ * (PowerSeries.X * PowerSeries.derivative ℚ (expSeries G₂)) +
            expSeries G₂ * (PowerSeries.X * PowerSeries.derivative ℚ (expSeries G₁)) := by ring
      _ = expSeries G₁ * (expSeries G₂ * (PowerSeries.X * PowerSeries.derivative ℚ G₂)) +
            expSeries G₂ * (expSeries G₁ * (PowerSeries.X * PowerSeries.derivative ℚ G₁)) := by
            rw [h1, h2]
      _ = expSeries G₁ * expSeries G₂ *
            (PowerSeries.X * PowerSeries.derivative ℚ G₁ +
             PowerSeries.X * PowerSeries.derivative ℚ G₂) := by ring

private lemma expSeries_zero : expSeries 0 = 1 := by
  symm
  apply eq_expSeries_of_ode
  · simp
  · simp

private lemma expSeries_nsmul (G : PowerSeries ℚ) (m : ℕ) :
    expSeries (PowerSeries.C (m : ℚ) * G) = (expSeries G) ^ m := by
  induction m with
  | zero => simp [expSeries_zero]
  | succ m ih =>
      rw [Nat.cast_succ, map_add, map_one, add_mul, one_mul, expSeries_add, ih, pow_succ]

/-- Formal substitution `F(X^p)`. -/
private noncomputable def substPow (p : ℕ) (F : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => if p ∣ n then PowerSeries.coeff (n / p) F else 0

private lemma coeff_substPow (p : ℕ) (F : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (substPow p F) = if p ∣ n then PowerSeries.coeff (n / p) F else 0 := by
  rw [substPow, PowerSeries.coeff_mk]

private lemma substPow_mul {p : ℕ} (hp : 0 < p) (F G : PowerSeries ℚ) :
    substPow p (F * G) = substPow p F * substPow p G := by
  apply PowerSeries.ext; intro n
  rw [coeff_substPow]
  conv_rhs =>
    rw [PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i (substPow p F) * PowerSeries.coeff j (substPow p G))]
  by_cases hdiv : p ∣ n
  · obtain ⟨m, rfl⟩ := hdiv
    simp only [dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ hp]
    rw [PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i F * PowerSeries.coeff j G)]
    have hsub : (Finset.range (m + 1)).image (fun k => p * k) ⊆ Finset.range (p * m + 1) := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      have hkl : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      exact Finset.mem_range.mpr (by nlinarith)
    rw [← Finset.sum_subset hsub]
    · rw [Finset.sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hp hab)]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkl : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hsub_eq : p * m - p * k = p * (m - k) := (Nat.mul_sub_left_distrib p m k).symm
      rw [coeff_substPow, coeff_substPow, hsub_eq]
      simp [dvd_mul_right, Nat.mul_div_cancel_left _ hp]
    · intro x hx hnot
      rw [coeff_substPow]
      split_ifs with hpx
      · exfalso; apply hnot
        obtain ⟨k, rfl⟩ := hpx
        have hxl : p * k ≤ p * m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
        have hkl : k ≤ m := Nat.le_of_mul_le_mul_left hxl hp
        exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
      · rw [zero_mul]
  · simp only [hdiv, ↓reduceIte]
    symm
    refine Finset.sum_eq_zero fun k hk => ?_
    have hkl : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [coeff_substPow, coeff_substPow]
    split_ifs with h1 h2
    · exfalso; apply hdiv
      rw [← Nat.add_sub_of_le hkl]
      exact dvd_add h1 h2
    · ring
    · ring
    · ring

private lemma substPow_pow {p : ℕ} (hp : 0 < p) (F : PowerSeries ℚ) :
    ∀ k : ℕ, substPow p (F ^ k) = (substPow p F) ^ k := by
  intro k
  induction k with
  | zero =>
      apply PowerSeries.ext; intro j
      rw [pow_zero, pow_zero, coeff_substPow, PowerSeries.coeff_one]
      by_cases hj : j = 0
      · subst hj; simp
      · rw [PowerSeries.coeff_one, if_neg hj]
        by_cases hdiv : p ∣ j
        · rw [if_pos hdiv]
          obtain ⟨q, rfl⟩ := hdiv
          rw [Nat.mul_div_cancel_left _ hp, if_neg (fun h => hj (by rw [h, mul_zero]))]
        · rw [if_neg hdiv]
  | succ k ih => rw [pow_succ, pow_succ, substPow_mul hp, ih]

private lemma X_mul_deriv_substPow {p : ℕ} (hp : 0 < p) (F : PowerSeries ℚ) :
    PowerSeries.X * PowerSeries.derivative ℚ (substPow p F) =
      PowerSeries.C (p : ℚ) * substPow p (PowerSeries.X * PowerSeries.derivative ℚ F) := by
  apply PowerSeries.ext; intro n
  cases n with
  | zero =>
      rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_C_mul, coeff_substPow]
      simp [PowerSeries.coeff_zero_X_mul]
  | succ n =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, coeff_substPow,
          PowerSeries.coeff_C_mul, coeff_substPow]
      by_cases hdiv : p ∣ n + 1
      · simp only [hdiv, ↓reduceIte]
        obtain ⟨m, hm⟩ := hdiv
        have hm_pos : 1 ≤ m := by
          by_contra h0; have : m = 0 := by omega
          rw [this, mul_zero] at hm; omega
        obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
        have hdiv_eq : (n + 1) / p = m' + 1 := by rw [hm, Nat.mul_div_cancel_left _ hp]
        rw [hdiv_eq, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
        have hcast : ((n : ℚ) + 1) = (p : ℚ) * ((m' : ℚ) + 1) := by exact_mod_cast hm
        rw [hcast]; ring
      · simp [hdiv]

private lemma expSeries_substPow {p : ℕ} (hp : 0 < p) (G : PowerSeries ℚ) :
    expSeries (substPow p G) = substPow p (expSeries G) := by
  symm
  apply eq_expSeries_of_ode
  · rw [coeff_substPow]; simp [coeff_zero_expSeries]
  · rw [X_mul_deriv_substPow hp, X_mul_deriv_substPow hp, expSeries_ode, substPow_mul hp]
    ring

/-! ### Part 4: Dwork's Lemma -/

private lemma exp_p_mul_div_p_isPInt {p N : ℕ} (hp : p.Prime) {F : PowerSeries ℚ}
    (hF0 : PowerSeries.coeff 0 F = 0)
    (hFp : ∀ n ≤ N, isPInt p (PowerSeries.coeff n F)) :
    ∀ n, 1 ≤ n → n ≤ N → isPInt p (PowerSeries.coeff n (expSeries (PowerSeries.C (p : ℚ) * F)) / (p : ℚ)) := by
  have hFpow_pInt : ∀ (k n : ℕ), n ≤ N → isPInt p (PowerSeries.coeff n (F ^ k)) := by
    intro k
    induction k with
    | zero =>
        intro n _
        rw [pow_zero, PowerSeries.coeff_one]
        split_ifs
        · exact isPInt_int hp 1
        · exact isPInt_zero hp
    | succ k ih =>
        intro n hn
        rw [pow_succ, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun i j => PowerSeries.coeff i (F ^ k) * PowerSeries.coeff j F)]
        refine isPInt_sum hp _ _ fun j hj => ?_
        have hjl : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        exact isPInt_mul hp (ih j (by omega)) (hFp (n - j) (by omega))
  have hFpow_zero : ∀ (k n : ℕ), n < k → PowerSeries.coeff n (F ^ k) = 0 := by
    intro k
    induction k with
    | zero => intro n hn; omega
    | succ k ih =>
        intro n hn
        rw [pow_succ, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun i j => PowerSeries.coeff i (F ^ k) * PowerSeries.coeff j F)]
        refine Finset.sum_eq_zero fun j hj => ?_
        have hjl : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        by_cases hjn : j = n
        · subst hjn; rw [Nat.sub_self, hF0, mul_zero]
        · rw [ih j (by omega), zero_mul]
  let Etrunc : PowerSeries ℚ :=
    ∑ k ∈ Finset.range (N + 1),
      PowerSeries.C ((p : ℚ) ^ k / (Nat.factorial k : ℚ)) * F ^ k
  have hE0 : PowerSeries.coeff 0 Etrunc = 1 := by
    simp only [Etrunc, map_sum, PowerSeries.coeff_C_mul]
    rw [Finset.sum_range_succ']
    have htail :
        ∑ k ∈ Finset.range N,
          ((p : ℚ) ^ (k + 1) / (Nat.factorial (k + 1) : ℚ)) * PowerSeries.coeff 0 (F ^ (k + 1)) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [hFpow_zero (k + 1) 0 (by omega), mul_zero]
    rw [htail, zero_add]
    simp
  have hE_ode : ∀ n, 1 ≤ n → n ≤ N →
      PowerSeries.coeff n (PowerSeries.X * PowerSeries.derivative ℚ Etrunc) =
      PowerSeries.coeff n (Etrunc * (PowerSeries.X * PowerSeries.derivative ℚ (PowerSeries.C (p : ℚ) * F))) := by
    have hderiv_E :
        PowerSeries.derivative ℚ Etrunc =
          PowerSeries.C (p : ℚ) *
            (∑ k ∈ Finset.range N, PowerSeries.C ((p : ℚ) ^ k / (Nat.factorial k : ℚ)) * F ^ k) *
            PowerSeries.derivative ℚ F := by
      simp only [Etrunc, map_sum]
      rw [Finset.sum_range_succ']
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, map_one, one_mul,
        Derivation.map_one_eq_zero, add_zero, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Derivation.leibniz, PowerSeries.derivative_C, smul_eq_mul, smul_eq_mul,
          mul_zero, add_zero, Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul]
      simp only [Nat.add_sub_cancel]
      have hc : PowerSeries.C ((p : ℚ) ^ (k + 1) / (Nat.factorial (k + 1) : ℚ)) *
          ((k + 1 : ℕ) : PowerSeries ℚ) =
          PowerSeries.C (p : ℚ) * PowerSeries.C ((p : ℚ) ^ k / (Nat.factorial k : ℚ)) := by
        rw [show ((k + 1 : ℕ) : PowerSeries ℚ) = PowerSeries.C ((k + 1 : ℕ) : ℚ) by rw [map_natCast],
            ← map_mul, ← map_mul]
        congr 1
        rw [pow_succ', Nat.factorial_succ, Nat.cast_mul]
        have hpos : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
        field_simp [hpos]
      calc
        PowerSeries.C ((p : ℚ) ^ (k + 1) / (Nat.factorial (k + 1) : ℚ)) *
            (((k + 1 : ℕ) : PowerSeries ℚ) * (F ^ k * PowerSeries.derivative ℚ F))
          = (PowerSeries.C ((p : ℚ) ^ (k + 1) / (Nat.factorial (k + 1) : ℚ)) *
              ((k + 1 : ℕ) : PowerSeries ℚ)) * (F ^ k * PowerSeries.derivative ℚ F) := by ring
        _ = PowerSeries.C (p : ℚ) * PowerSeries.C ((p : ℚ) ^ k / (Nat.factorial k : ℚ)) *
              (F ^ k * PowerSeries.derivative ℚ F) := by rw [hc]
        _ = PowerSeries.C (p : ℚ) * (PowerSeries.C ((p : ℚ) ^ k / (Nat.factorial k : ℚ)) * F ^ k) *
              PowerSeries.derivative ℚ F := by ring
    have hE_split : Etrunc =
        (∑ k ∈ Finset.range N, PowerSeries.C ((p : ℚ) ^ k / (Nat.factorial k : ℚ)) * F ^ k) +
        PowerSeries.C ((p : ℚ) ^ N / (Nat.factorial N : ℚ)) * F ^ N :=
      Finset.sum_range_succ _ N
    have hderiv_C : PowerSeries.derivative ℚ (PowerSeries.C (p : ℚ) * F) =
        PowerSeries.C (p : ℚ) * PowerSeries.derivative ℚ F := by
      rw [Derivation.leibniz, PowerSeries.derivative_C, smul_eq_mul, smul_eq_mul, mul_zero, add_zero]
    intro n hn1 hnN
    rw [hderiv_E, hderiv_C]
    have hdiff :
        Etrunc * (PowerSeries.X * (PowerSeries.C (p : ℚ) * PowerSeries.derivative ℚ F)) -
        PowerSeries.X * (PowerSeries.C (p : ℚ) *
          (∑ k ∈ Finset.range N, PowerSeries.C ((p : ℚ) ^ k / (Nat.factorial k : ℚ)) * F ^ k) *
          PowerSeries.derivative ℚ F) =
        PowerSeries.C ((p : ℚ) ^ (N + 1) / (Nat.factorial N : ℚ)) *
          (F ^ N * (PowerSeries.X * PowerSeries.derivative ℚ F)) := by
      rw [hE_split]
      have hcp : PowerSeries.C ((p : ℚ) ^ N / (Nat.factorial N : ℚ)) * PowerSeries.C (p : ℚ) =
          PowerSeries.C ((p : ℚ) ^ (N + 1) / (Nat.factorial N : ℚ)) := by
        rw [← map_mul]; congr 1; rw [pow_succ]; ring
      linear_combination (F ^ N * PowerSeries.X * PowerSeries.derivative ℚ F) * hcp
    have hzero : PowerSeries.coeff n
        (PowerSeries.C ((p : ℚ) ^ (N + 1) / (Nat.factorial N : ℚ)) *
          (F ^ N * (PowerSeries.X * PowerSeries.derivative ℚ F))) = 0 := by
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j => PowerSeries.coeff i (F ^ N) * PowerSeries.coeff j (PowerSeries.X * PowerSeries.derivative ℚ F))]
      have hsum0 :
          ∑ k ∈ Finset.range (n + 1),
            PowerSeries.coeff k (F ^ N) * PowerSeries.coeff (n - k) (PowerSeries.X * PowerSeries.derivative ℚ F) = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        have hkl : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        by_cases hkn : k = n
        · subst hkn; rw [Nat.sub_self, PowerSeries.coeff_zero_X_mul, mul_zero]
        · rw [hFpow_zero N k (by omega), zero_mul]
      rw [hsum0, mul_zero]
    have hsub := congr_arg (PowerSeries.coeff n) hdiff
    rw [map_sub, hzero] at hsub
    linarith
  have hE_eq := eq_expSeries_upTo hE0 hE_ode
  intro n hn1 hnN
  rw [← hE_eq n hnN]
  simp only [Etrunc, map_sum, PowerSeries.coeff_C_mul]
  rw [Finset.sum_range_succ', add_div, Finset.sum_div]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul,
    PowerSeries.coeff_one, show n ≠ 0 by omega, ↓reduceIte, zero_div, add_zero]
  refine isPInt_sum hp _ _ fun k _ => ?_
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hrew : ((p : ℚ) ^ (k + 1) / (Nat.factorial (k + 1) : ℚ)) * PowerSeries.coeff n (F ^ (k + 1)) / (p : ℚ) =
      ((p : ℚ) ^ k / (Nat.factorial (k + 1) : ℚ)) * PowerSeries.coeff n (F ^ (k + 1)) := by
    rw [pow_succ]; field_simp [hp0]
  rw [hrew]
  exact isPInt_mul hp (by simpa using isPInt_pow_div_factorial hp (show 1 ≤ k + 1 by omega))
    (hFpow_pInt (k + 1) n hnN)

/-- Freshman's dream for `p`-integral power series: if `H` has `p`-integral coefficients `≤ n`,
then `([X^n] H^p - (if p ∣ n then ([X^(n/p)] H)^p else 0)) / p` is `p`-integral! -/
private lemma freshman_dream_series {p n : ℕ} (hp : p.Prime) {H : PowerSeries ℚ}
    (hHp : ∀ j ≤ n, isPInt p (PowerSeries.coeff j H)) :
    isPInt p ((PowerSeries.coeff n (H ^ p) -
      if p ∣ n then (PowerSeries.coeff (n / p) H) ^ p else 0) / (p : ℚ)) := by
  have hden_nd : ∀ j ∈ Finset.range (n + 1), ¬ p ∣ (PowerSeries.coeff j H).den := fun j hj =>
    not_dvd_den_of_isPInt hp (hHp j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
  set D : ℕ := ∏ j ∈ Finset.range (n + 1), (PowerSeries.coeff j H).den
  have hD_nd : ¬ p ∣ D := by
    intro h
    obtain ⟨j, hj, hjd⟩ := hp.prime.dvd_finsetProd_iff _ |>.mp h
    exact hden_nd j hj hjd
  have hD0 : (D : ℚ) ≠ 0 := by
    exact_mod_cast (show D ≠ 0 by intro h; rw [h] at hD_nd; exact hD_nd (dvd_zero p))
  -- Build the integer polynomial `Pz ∈ ℤ[X]` agreeing with `D * H` through degree `n`!
  have hDH_int : ∀ j, ∃ z : ℤ, (if j ≤ n then (D : ℚ) * PowerSeries.coeff j H else 0) = (z : ℚ) := by
    intro j
    by_cases hjn : j ≤ n
    · simp only [hjn, ↓reduceIte]
      have hmem : j ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
      have hdiv : (PowerSeries.coeff j H).den ∣ D := Finset.dvd_prod_of_mem _ hmem
      obtain ⟨c, hc⟩ := hdiv
      set x := PowerSeries.coeff j H
      have hq : x = (x.num : ℚ) / (x.den : ℚ) := (Rat.num_div_den x).symm
      have hqd0 : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
      refine ⟨x.num * (c : ℤ), ?_⟩
      calc (D : ℚ) * x
        _ = (x.den : ℚ) * (c : ℚ) * ((x.num : ℚ) / (x.den : ℚ)) := by
              rw [hc, Nat.cast_mul]; congr 1
        _ = ((x.num * (c : ℤ) : ℤ) : ℚ) := by
              push_cast; field_simp [hqd0]
    · exact ⟨0, by simp [hjn]⟩
  choose z hz using hDH_int
  let Pz : Polynomial ℤ := ∑ j ∈ Finset.range (n + 1), Polynomial.C (z j) * Polynomial.X ^ j
  have hPz_coeff : ∀ j ≤ n, (Pz.coeff j : ℚ) = (D : ℚ) * PowerSeries.coeff j H := by
    intro j hj
    simp only [Pz, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [Finset.sum_eq_single j]
    · simp only [↓reduceIte, mul_one]; have := hz j; simpa [hj] using this.symm
    · intro b _ hne; simp [hne.symm]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have hPz_pow : ((Pz ^ p).coeff n : ℚ) = (D : ℚ) ^ p * PowerSeries.coeff n (H ^ p) := by
    have hagree : ∀ (t r : ℕ), r ≤ n →
        PowerSeries.coeff r ((Polynomial.toPowerSeries (Pz.map (Int.castRingHom ℚ))) ^ t) =
        PowerSeries.coeff r ((PowerSeries.C (D : ℚ) * H) ^ t) := by
      intro t
      induction t with
      | zero => intro r _; rfl
      | succ t iht =>
          intro r hr
          rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
              Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (fun a b => PowerSeries.coeff a ((Polynomial.toPowerSeries (Pz.map (Int.castRingHom ℚ))) ^ t) *
                  PowerSeries.coeff b (Polynomial.toPowerSeries (Pz.map (Int.castRingHom ℚ)))),
              Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (fun a b => PowerSeries.coeff a ((PowerSeries.C (D : ℚ) * H) ^ t) *
                  PowerSeries.coeff b (PowerSeries.C (D : ℚ) * H))]
          refine Finset.sum_congr rfl fun a ha => ?_
          have hal : a ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
          rw [iht a (by omega), Polynomial.coeff_coe, Polynomial.coeff_map, Int.coe_castRingHom,
              PowerSeries.coeff_C_mul]
          dsimp only
          rw [hPz_coeff (r - a) (by omega)]
    have h := hagree p n (le_refl n)
    rw [← Polynomial.coe_pow, ← Polynomial.map_pow, Polynomial.coeff_coe, Polynomial.coeff_map,
        Int.coe_castRingHom, mul_pow, ← map_pow, PowerSeries.coeff_C_mul] at h
    exact h
  -- Reduce `Pz ^ p` modulo `p` in `(ZMod p)[X]` using `Finset.sum_pow_char`!
  have : Fact p.Prime := ⟨hp⟩
  have hmod : (p : ℤ) ∣ ((Pz ^ p).coeff n - if p ∣ n then (z (n / p)) ^ p else 0) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hpoly_mod : (Pz.map (Int.castRingHom (ZMod p))) ^ p =
        ∑ j ∈ Finset.range (n + 1), Polynomial.C ((z j : ZMod p) ^ p) * Polynomial.X ^ (p * j) := by
      have h1 : Pz.map (Int.castRingHom (ZMod p)) =
          ∑ j ∈ Finset.range (n + 1), Polynomial.C (z j : ZMod p) * Polynomial.X ^ j := by
        simp [Pz, Polynomial.map_sum]
      rw [h1, ← frobenius_def, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [frobenius_def, mul_pow, ← map_pow, ← pow_mul, mul_comm j p]
    have hc := congr_arg (fun Q : Polynomial (ZMod p) => Q.coeff n) hpoly_mod
    rw [← Polynomial.map_pow, Polynomial.coeff_map, Int.coe_castRingHom] at hc
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] at hc
    rw [Int.cast_sub, hc]
    by_cases hdiv : p ∣ n
    · simp only [hdiv, ↓reduceIte, Int.cast_pow]
      obtain ⟨m, rfl⟩ := hdiv
      have hm_le : m ≤ p * m := Nat.le_mul_of_pos_left m hp.pos
      rw [Finset.sum_eq_single m]
      · simp [Nat.mul_div_cancel_left _ hp.pos]
      · intro b _ hne
        have : p * m ≠ p * b := fun h => hne (Nat.eq_of_mul_eq_mul_left hp.pos h).symm
        simp [this]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    · simp only [hdiv, ↓reduceIte, Int.cast_zero, sub_zero]
      refine Finset.sum_eq_zero fun b _ => ?_
      have : n ≠ p * b := fun h => hdiv ⟨b, h⟩
      simp [this]
  obtain ⟨t, ht⟩ := hmod
  have hDp_nd : ¬ p ∣ D ^ p := fun h => hD_nd (hp.dvd_of_dvd_pow h)
  refine ⟨t, D ^ p, hDp_nd, ?_⟩
  have ht_q : ((Pz ^ p).coeff n : ℚ) - (if p ∣ n then ((z (n / p) : ℚ) ^ p) else 0) =
      (p : ℚ) * (t : ℚ) := by
    have : ((Pz ^ p).coeff n - if p ∣ n then (z (n / p)) ^ p else 0 : ℤ) = (p : ℤ) * t := ht
    have hq : (((Pz ^ p).coeff n - if p ∣ n then (z (n / p)) ^ p else 0 : ℤ) : ℚ) = (p : ℚ) * (t : ℚ) := by
      exact_mod_cast this
    rw [← hq]
    split_ifs <;> push_cast <;> ring
  rw [hPz_pow] at ht_q
  have hrhs : (if p ∣ n then (z (n / p) : ℚ) ^ p else 0) =
      (D : ℚ) ^ p * (if p ∣ n then (PowerSeries.coeff (n / p) H) ^ p else 0) := by
    split_ifs
    · have hle : n / p ≤ n := Nat.div_le_self n p
      have hzn := hz (n / p)
      simp only [hle, ↓reduceIte] at hzn
      rw [← mul_pow, hzn]
    · ring
  rw [hrhs] at ht_q
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hDp0 : (D : ℚ) ^ p ≠ 0 := pow_ne_zero p hD0
  push_cast
  field_simp [hp0, hDp0]
  linarith

/-- Fermat's Little Theorem for `p`-integral rationals: `(x^p - x) / p` is `p`-integral! -/
private lemma fermat_pInt {p : ℕ} (hp : p.Prime) {x : ℚ} (hx : isPInt p x) :
    isPInt p ((x ^ p - x) / (p : ℚ)) := by
  obtain ⟨a, b, hb, rfl⟩ := hx
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by intro h; subst h; exact hb (dvd_zero p))
  have : Fact p.Prime := ⟨hp⟩
  have hmod : (p : ℤ) ∣ (a ^ p - a * (b : ℤ) ^ (p - 1)) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card]
    have hb_ne : (b : ZMod p) ≠ 0 := by
      intro h; exact hb ((ZMod.natCast_eq_zero_iff b p).mp h)
    rw [ZMod.pow_card_sub_one_eq_one hb_ne, mul_one, sub_self]
  obtain ⟨t, ht⟩ := hmod
  have hbp_nd : ¬ p ∣ b ^ p := fun h => hb (hp.dvd_of_dvd_pow h)
  refine ⟨t, b ^ p, hbp_nd, ?_⟩
  have ht_q : (a : ℚ) ^ p - (a : ℚ) * (b : ℚ) ^ (p - 1) = (p : ℚ) * (t : ℚ) := by exact_mod_cast ht
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hbp0 : (b : ℚ) ^ p ≠ 0 := pow_ne_zero p hb0
  have hbp_split : (b : ℚ) ^ p = (b : ℚ) * (b : ℚ) ^ (p - 1) := by
    rw [← pow_succ']; congr 1; have := hp.two_le; omega
  push_cast
  rw [div_pow]
  field_simp [hp0, hb0, hbp0]
  linear_combination (b : ℚ) * ht_q - (a : ℚ) * hbp_split

/-- **Dwork's Lemma (truncated)**: if `G(0) = 0` and `(G(X^p) - p * G(X)) / p` has `p`-integral
coefficients through degree `N`, then `expSeries G` has `p`-integral coefficients through degree `N`! -/
private lemma dwork_lemma {p N : ℕ} (hp : p.Prime) {G : PowerSeries ℚ}
    (hG0 : PowerSeries.coeff 0 G = 0)
    (hG : ∀ m, 1 ≤ m → m ≤ N →
      isPInt p (PowerSeries.coeff m (substPow p G - PowerSeries.C (p : ℚ) * G) / (p : ℚ))) :
    ∀ n ≤ N, isPInt p (PowerSeries.coeff n (expSeries G)) := by
  set H := expSeries G
  let F : PowerSeries ℚ := PowerSeries.mk fun m =>
    if m = 0 then 0 else PowerSeries.coeff m (substPow p G - PowerSeries.C (p : ℚ) * G) / (p : ℚ)
  have hF0 : PowerSeries.coeff 0 F = 0 := by simp [F]
  have hFp : ∀ m ≤ N, isPInt p (PowerSeries.coeff m F) := by
    intro m hm
    rw [PowerSeries.coeff_mk]
    split_ifs with h0
    · exact isPInt_zero hp
    · exact hG m (by omega) hm
  have hCF_eq : PowerSeries.C (p : ℚ) * F = substPow p G - PowerSeries.C (p : ℚ) * G := by
    apply PowerSeries.ext; intro m
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    by_cases hm0 : m = 0
    · subst hm0
      simp only [↓reduceIte, mul_zero, map_sub, coeff_substPow, dvd_zero, Nat.zero_div,
        PowerSeries.coeff_C_mul, hG0, sub_zero]
    · simp only [hm0, ↓reduceIte]
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      field_simp [hp0]
  set E := expSeries (PowerSeries.C (p : ℚ) * F)
  have hE0 : PowerSeries.coeff 0 E = 1 := coeff_zero_expSeries _
  have hEp : ∀ m, 1 ≤ m → m ≤ N → isPInt p (PowerSeries.coeff m E / (p : ℚ)) :=
    exp_p_mul_div_p_isPInt hp hF0 hFp
  have hH_rel : substPow p H = H ^ p * E := by
    rw [← expSeries_substPow hp.pos G, ← expSeries_nsmul G p, ← expSeries_add]
    congr 1
    rw [hCF_eq]; ring
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
        rw [coeff_zero_expSeries]; exact isPInt_int hp 1
    | succ n' =>
        set n := n' + 1
        let Htrunc : PowerSeries ℚ := PowerSeries.mk fun j => if j < n then PowerSeries.coeff j H else 0
        have hHt_pInt : ∀ j, isPInt p (PowerSeries.coeff j Htrunc) := by
          intro j; rw [PowerSeries.coeff_mk]
          split_ifs with hj
          · exact ih j hj (by omega)
          · exact isPInt_zero hp
        have hHt_pow_pInt : ∀ (k j : ℕ), isPInt p (PowerSeries.coeff j (Htrunc ^ k)) := by
          intro k
          induction k with
          | zero =>
              intro j; rw [pow_zero, PowerSeries.coeff_one]
              split_ifs
              · exact isPInt_int hp 1
              · exact isPInt_zero hp
          | succ k ihk =>
              intro j
              rw [pow_succ, PowerSeries.coeff_mul,
                  Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                    (fun i r => PowerSeries.coeff i (Htrunc ^ k) * PowerSeries.coeff r Htrunc)]
              exact isPInt_sum hp _ _ fun i _ => isPInt_mul hp (ihk i) (hHt_pInt (j - i))
        have hHt0 : PowerSeries.coeff 0 Htrunc = 1 := by
          rw [PowerSeries.coeff_mk, if_pos (by omega : 0 < n), coeff_zero_expSeries]
        let R : PowerSeries ℚ := H - Htrunc
        have hR_lt : ∀ j < n, PowerSeries.coeff j R = 0 := by
          intro j hj
          rw [map_sub, PowerSeries.coeff_mk, if_pos hj, sub_self]
        have hR_n : PowerSeries.coeff n R = PowerSeries.coeff n H := by
          rw [map_sub, PowerSeries.coeff_mk, if_neg (by omega), sub_zero]
        have hR_pow_zero : ∀ (k j : ℕ), 2 ≤ k → j ≤ n → PowerSeries.coeff j (R ^ k) = 0 := by
          intro k j hk hj
          obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le hk
          rw [pow_add, sq, PowerSeries.coeff_mul,
              Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (fun i r => PowerSeries.coeff i (R * R) * PowerSeries.coeff r (R ^ k'))]
          refine Finset.sum_eq_zero fun i hi => ?_
          have hil : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hRR : PowerSeries.coeff i (R * R) = 0 := by
            rw [PowerSeries.coeff_mul,
                Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                  (fun a b => PowerSeries.coeff a R * PowerSeries.coeff b R)]
            refine Finset.sum_eq_zero fun a ha => ?_
            have hal : a ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
            by_cases han : a < n
            · rw [hR_lt a han, zero_mul]
            · rw [hR_lt (i - a) (by omega), mul_zero]
          rw [hRR, zero_mul]
        -- Expand `H ^ p = (R + Htrunc) ^ p` and read off coefficients `≤ n`!
        have hHp_eq : H ^ p = ∑ k ∈ Finset.range (p + 1),
            PowerSeries.C ((Nat.choose p k : ℕ) : ℚ) * (R ^ k * Htrunc ^ (p - k)) := by
          have hHR : H = R + Htrunc := by simp [R]
          rw [hHR, add_pow]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [show ((Nat.choose p k : ℕ) : PowerSeries ℚ) = PowerSeries.C ((Nat.choose p k : ℕ) : ℚ) by
            rw [map_natCast]]
          ring
        have hHp_lt : ∀ j < n, PowerSeries.coeff j (H ^ p) = PowerSeries.coeff j (Htrunc ^ p) := by
          intro j hj
          rw [hHp_eq, map_sum, Finset.sum_range_succ']
          have htail :
              ∑ k ∈ Finset.range p,
                PowerSeries.coeff j (PowerSeries.C ((Nat.choose p (k + 1) : ℕ) : ℚ) *
                  (R ^ (k + 1) * Htrunc ^ (p - (k + 1)))) = 0 := by
            refine Finset.sum_eq_zero fun k _ => ?_
            rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul,
                Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                  (fun a b => PowerSeries.coeff a (R ^ (k + 1)) * PowerSeries.coeff b (Htrunc ^ (p - (k + 1))))]
            have hsum0 :
                ∑ a ∈ Finset.range (j + 1),
                  PowerSeries.coeff a (R ^ (k + 1)) * PowerSeries.coeff (j - a) (Htrunc ^ (p - (k + 1))) = 0 := by
              refine Finset.sum_eq_zero fun a ha => ?_
              have hal : a ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
              have hRa : PowerSeries.coeff a (R ^ (k + 1)) = 0 := by
                rw [pow_succ', PowerSeries.coeff_mul,
                    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                      (fun u v => PowerSeries.coeff u R * PowerSeries.coeff v (R ^ k))]
                refine Finset.sum_eq_zero fun u hu => ?_
                have hul : u ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu)
                rw [hR_lt u (by omega), zero_mul]
              rw [hRa, zero_mul]
            rw [hsum0, mul_zero]
          rw [htail, zero_add]
          simp
        have hHp_n : PowerSeries.coeff n (H ^ p) =
            PowerSeries.coeff n (Htrunc ^ p) + (p : ℚ) * PowerSeries.coeff n H := by
          rw [hHp_eq, map_sum, Finset.sum_range_succ']
          obtain ⟨p', hp'⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
          rw [hp', Finset.sum_range_succ']
          have htail :
              ∑ k ∈ Finset.range p',
                PowerSeries.coeff n (PowerSeries.C ((Nat.choose (p' + 1) (k + 1 + 1) : ℕ) : ℚ) *
                  (R ^ (k + 1 + 1) * Htrunc ^ (p' + 1 - (k + 1 + 1)))) = 0 := by
            refine Finset.sum_eq_zero fun k _ => ?_
            rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul,
                Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                  (fun a b => PowerSeries.coeff a (R ^ (k + 1 + 1)) *
                    PowerSeries.coeff b (Htrunc ^ (p' + 1 - (k + 1 + 1))))]
            have hsum0 :
                ∑ a ∈ Finset.range (n + 1),
                  PowerSeries.coeff a (R ^ (k + 1 + 1)) *
                    PowerSeries.coeff (n - a) (Htrunc ^ (p' + 1 - (k + 1 + 1))) = 0 := by
              refine Finset.sum_eq_zero fun a ha => ?_
              have hal : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
              rw [hR_pow_zero (k + 1 + 1) a (by omega) hal, zero_mul]
            rw [hsum0, mul_zero]
          rw [htail, zero_add, ← hp']
          have hterm1 : PowerSeries.coeff n (PowerSeries.C ((Nat.choose p 1 : ℕ) : ℚ) *
              (R ^ 1 * Htrunc ^ (p - 1))) = (p : ℚ) * PowerSeries.coeff n H := by
            rw [Nat.choose_one_right, pow_one, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul,
                Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                  (fun a b => PowerSeries.coeff a R * PowerSeries.coeff b (Htrunc ^ (p - 1))),
                Finset.sum_range_succ]
            have h0 : ∑ a ∈ Finset.range n, PowerSeries.coeff a R * PowerSeries.coeff (n - a) (Htrunc ^ (p - 1)) = 0 := by
              refine Finset.sum_eq_zero fun a ha => ?_
              rw [hR_lt a (Finset.mem_range.mp ha), zero_mul]
            rw [h0, zero_add, hR_n, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
                ← PowerSeries.coeff_zero_eq_constantCoeff, hHt0, one_pow, mul_one]
          rw [hterm1]
          simp [add_comm]
        -- Extract `[X^n]` from `substPow p H = H ^ p * E`!
        have hrel_n := congr_arg (PowerSeries.coeff n) hH_rel
        rw [coeff_substPow, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun i j => PowerSeries.coeff i (H ^ p) * PowerSeries.coeff j E),
            Finset.sum_range_succ, Nat.sub_self, hE0, mul_one, hHp_n] at hrel_n
        have hsum_tail :
            ∑ k ∈ Finset.range n, PowerSeries.coeff k (H ^ p) * PowerSeries.coeff (n - k) E =
            ∑ k ∈ Finset.range n, PowerSeries.coeff k (Htrunc ^ p) * PowerSeries.coeff (n - k) E := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [hHp_lt k (Finset.mem_range.mp hk)]
        rw [hsum_tail] at hrel_n
        have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
        have hHn_eq : PowerSeries.coeff n H =
            ((if p ∣ n then PowerSeries.coeff (n / p) H else 0) - PowerSeries.coeff n (Htrunc ^ p)) / (p : ℚ) -
            ∑ k ∈ Finset.range n, PowerSeries.coeff k (Htrunc ^ p) * (PowerSeries.coeff (n - k) E / (p : ℚ)) := by
          have hdiv_sum :
              ∑ k ∈ Finset.range n, PowerSeries.coeff k (Htrunc ^ p) * (PowerSeries.coeff (n - k) E / (p : ℚ)) =
              (∑ k ∈ Finset.range n, PowerSeries.coeff k (Htrunc ^ p) * PowerSeries.coeff (n - k) E) / (p : ℚ) := by
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl fun k _ => by ring
          rw [hdiv_sum]
          field_simp [hp0]
          linarith
        rw [hHn_eq]
        refine isPInt_sub hp ?_ ?_
        · -- First term: combine `freshman_dream_series` and `fermat_pInt`!
          have hfr := freshman_dream_series (n := n) hp (fun j _ => hHt_pInt j)
          have hHt_div : (if p ∣ n then (PowerSeries.coeff (n / p) Htrunc) ^ p else 0) =
              if p ∣ n then (PowerSeries.coeff (n / p) H) ^ p else 0 := by
            split_ifs with hdiv
            · have hlt : n / p < n := Nat.div_lt_self (by omega) hp.one_lt
              rw [PowerSeries.coeff_mk, if_pos hlt]
            · rfl
          rw [hHt_div] at hfr
          by_cases hdiv : p ∣ n
          · simp only [hdiv, ↓reduceIte] at hfr ⊢
            have hlt : n / p < n := Nat.div_lt_self (by omega) hp.one_lt
            have hfer := fermat_pInt hp (ih (n / p) hlt (by omega))
            have hrew : (PowerSeries.coeff (n / p) H - PowerSeries.coeff n (Htrunc ^ p)) / (p : ℚ) =
                -((PowerSeries.coeff (n / p) H ^ p - PowerSeries.coeff (n / p) H) / (p : ℚ)) -
                ((PowerSeries.coeff n (Htrunc ^ p) - PowerSeries.coeff (n / p) H ^ p) / (p : ℚ)) := by
              ring
            rw [hrew]
            exact isPInt_sub hp (isPInt_neg hfer) hfr
          · simp only [hdiv, ↓reduceIte, sub_zero] at hfr ⊢
            have hrew : (0 - PowerSeries.coeff n (Htrunc ^ p)) / (p : ℚ) =
                -(PowerSeries.coeff n (Htrunc ^ p) / (p : ℚ)) := by ring
            rw [hrew]
            exact isPInt_neg hfr
        · -- Second term: `∑_{k < n} coeff k (Htrunc ^ p) * (coeff (n - k) E / p)`
          refine isPInt_sum hp _ _ fun k hk => ?_
          have hkl : k < n := Finset.mem_range.mp hk
          exact isPInt_mul hp (hHt_pow_pInt p k) (hEp (n - k) (by omega) (by omega))

/-! ### Part 5: Binomial lifting in `PowerSeries ℤ` & Dwork criterion for `∑ f_n(X)^n X^n / n` -/

private lemma pow_prime_pow_sub_dvd_series {p : ℕ} (hp : p.Prime)
    {A B : PowerSeries ℚ}
    (hA : ∀ j, ∃ z : ℤ, PowerSeries.coeff j A = (z : ℚ))
    (hB : ∀ j, ∃ z : ℤ, PowerSeries.coeff j B = (z : ℚ))
    (hAB : ∀ j, isPInt p ((PowerSeries.coeff j A - PowerSeries.coeff j B) / (p : ℚ))) :
    ∀ (v : ℕ) (j : ℕ), isPInt p ((PowerSeries.coeff j (A ^ (p ^ v)) - PowerSeries.coeff j (B ^ (p ^ v))) /
      ((p ^ (v + 1) : ℕ) : ℚ)) := by
  -- Work via `D := A - B = C p * U` where `U` has integer coefficients!
  have hAB_int : ∀ j, ∃ t : ℤ, PowerSeries.coeff j A - PowerSeries.coeff j B = (p : ℚ) * (t : ℚ) := by
    intro j
    obtain ⟨za, hza⟩ := hA j
    obtain ⟨zb, hzb⟩ := hB j
    have hnd := not_dvd_den_of_isPInt hp (hAB j)
    have hdiv : (p : ℤ) ∣ (za - zb) := by
      obtain ⟨num, den, hden, heq⟩ := hAB j
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hden0 : (den : ℚ) ≠ 0 := by
        exact_mod_cast (show den ≠ 0 by intro h; subst h; exact hden (dvd_zero p))
      rw [hza, hzb] at heq
      have h1 : ((za : ℚ) - (zb : ℚ)) * (den : ℚ) = (num : ℚ) * (p : ℚ) := by
        field_simp [hp0, hden0] at heq; linarith
      have hz : (za - zb) * (den : ℤ) = num * (p : ℤ) := by exact_mod_cast h1
      have hcop : IsCoprime (p : ℤ) (den : ℤ) := (hp.coprime_iff_not_dvd.mpr hden).isCoprime
      exact hcop.dvd_of_dvd_mul_right (by rw [hz]; exact dvd_mul_left (p : ℤ) num)
    obtain ⟨t, ht⟩ := hdiv
    refine ⟨t, ?_⟩
    rw [hza, hzb]; exact_mod_cast ht
  -- Lift `A = B + C (p : ℚ) * U` by induction on `v`!
  have hlift : ∀ v : ℕ, ∃ U : PowerSeries ℚ,
      (∀ j, ∃ z : ℤ, PowerSeries.coeff j U = (z : ℚ)) ∧
      A ^ (p ^ v) = B ^ (p ^ v) + PowerSeries.C ((p ^ (v + 1) : ℕ) : ℚ) * U := by
    intro v
    induction v with
    | zero =>
        choose t ht using hAB_int
        refine ⟨PowerSeries.mk (fun j => (t j : ℚ)), fun j => ⟨t j, by simp⟩, ?_⟩
        apply PowerSeries.ext; intro j
        rw [pow_zero, pow_one, pow_one, zero_add, pow_one, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
        linarith [ht j]
    | succ v ih =>
        obtain ⟨U, hU_int, hU_eq⟩ := ih
        have hB_pow_int : ∀ (k j : ℕ), ∃ z : ℤ, PowerSeries.coeff j (B ^ k) = (z : ℚ) := by
          intro k
          induction k with
          | zero =>
              intro j; rw [pow_zero, PowerSeries.coeff_one]
              split_ifs <;> [exact ⟨1, by simp⟩; exact ⟨0, by simp⟩]
          | succ k ihk =>
              intro j
              rw [pow_succ, PowerSeries.coeff_mul,
                  Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                    (fun i r => PowerSeries.coeff i (B ^ k) * PowerSeries.coeff r B)]
              choose z1 hz1 using ihk
              choose z2 hz2 using hB
              refine ⟨∑ i ∈ Finset.range (j + 1), z1 i * z2 (j - i), ?_⟩
              rw [Int.cast_sum]
              refine Finset.sum_congr rfl fun i _ => by rw [hz1 i, hz2 (j - i), Int.cast_mul]
        have hU_pow_int : ∀ (k j : ℕ), ∃ z : ℤ, PowerSeries.coeff j (U ^ k) = (z : ℚ) := by
          intro k
          induction k with
          | zero =>
              intro j; rw [pow_zero, PowerSeries.coeff_one]
              split_ifs <;> [exact ⟨1, by simp⟩; exact ⟨0, by simp⟩]
          | succ k ihk =>
              intro j
              rw [pow_succ, PowerSeries.coeff_mul,
                  Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                    (fun i r => PowerSeries.coeff i (U ^ k) * PowerSeries.coeff r U)]
              choose z1 hz1 using ihk
              choose z2 hz2 using hU_int
              refine ⟨∑ i ∈ Finset.range (j + 1), z1 i * z2 (j - i), ?_⟩
              rw [Int.cast_sum]
              refine Finset.sum_congr rfl fun i _ => by rw [hz1 i, hz2 (j - i), Int.cast_mul]
        have hmul_int : ∀ {X Y : PowerSeries ℚ},
            (∀ j, ∃ z : ℤ, PowerSeries.coeff j X = (z : ℚ)) →
            (∀ j, ∃ z : ℤ, PowerSeries.coeff j Y = (z : ℚ)) →
            ∀ j, ∃ z : ℤ, PowerSeries.coeff j (X * Y) = (z : ℚ) := by
          intro X Y hX hY j
          rw [PowerSeries.coeff_mul,
              Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (fun i r => PowerSeries.coeff i X * PowerSeries.coeff r Y)]
          choose zx hzx using hX
          choose zy hzy using hY
          refine ⟨∑ i ∈ Finset.range (j + 1), zx i * zy (j - i), ?_⟩
          rw [Int.cast_sum]
          refine Finset.sum_congr rfl fun i _ => by rw [hzx i, hzy (j - i), Int.cast_mul]
        -- Expand `A ^ (p^(v+1)) = (B^(p^v) + p^(v+1) * U)^p`!
        let c (k : ℕ) : ℕ :=
          if k + 1 = p then p ^ ((v + 1) * p - (v + 2))
          else (Nat.choose p (k + 1) / p) * p ^ ((v + 1) * k)
        let V : PowerSeries ℚ :=
          ∑ k ∈ Finset.range p,
            PowerSeries.C ((c k : ℕ) : ℚ) * (U ^ (k + 1) * (B ^ (p ^ v)) ^ (p - (k + 1)))
        refine ⟨V, ?_, ?_⟩
        · intro j
          simp only [V, map_sum, PowerSeries.coeff_C_mul]
          have hterm : ∀ k,
              ∃ z : ℤ, ((c k : ℕ) : ℚ) * PowerSeries.coeff j (U ^ (k + 1) * (B ^ (p ^ v)) ^ (p - (k + 1))) = (z : ℚ) := by
            intro k
            have hB_int' : ∀ r, ∃ z : ℤ, PowerSeries.coeff r ((B ^ (p ^ v)) ^ (p - (k + 1))) = (z : ℚ) := by
              rw [← pow_mul]; exact hB_pow_int _
            obtain ⟨z, hz⟩ := hmul_int (hU_pow_int (k + 1)) hB_int' j
            exact ⟨(c k : ℤ) * z, by rw [hz]; push_cast; ring⟩
          choose zf hzf using hterm
          refine ⟨∑ k ∈ Finset.range p, zf k, ?_⟩
          rw [Int.cast_sum]
          exact Finset.sum_congr rfl fun k _ => hzf k
        · rw [pow_succ, pow_mul, pow_mul, hU_eq, add_comm (B ^ (p ^ v)), add_pow, Finset.sum_range_succ']
          simp only [pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul]
          rw [add_comm _ ((B ^ (p ^ v)) ^ p)]
          congr 1
          simp only [V, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k hk => ?_
          have hklt : k < p := Finset.mem_range.mp hk
          rw [mul_pow, ← map_pow, ← mul_assoc, ← map_mul]
          have hcoeff_eq :
              PowerSeries.C (((p ^ (v + 1) : ℕ) : ℚ) ^ (k + 1)) *
                ((Nat.choose p (k + 1) : ℕ) : PowerSeries ℚ) =
              PowerSeries.C (((p ^ (v + 2) : ℕ) : ℚ) * ((c k : ℕ) : ℚ)) := by
            rw [show ((Nat.choose p (k + 1) : ℕ) : PowerSeries ℚ) =
              PowerSeries.C ((Nat.choose p (k + 1) : ℕ) : ℚ) by rw [map_natCast], ← map_mul]
            congr 1
            norm_cast
            simp only [c]
            by_cases hkp : k + 1 = p
            · simp only [hkp, ↓reduceIte, Nat.choose_self, mul_one]
              rw [← pow_mul, ← pow_add]
              congr 1
              have hp2 : 2 ≤ p := hp.two_le
              have hle : v + 2 ≤ (v + 1) * p := by nlinarith
              omega
            · simp only [hkp, ↓reduceIte]
              have hch : p ∣ Nat.choose p (k + 1) := hp.dvd_choose_self (by omega) (by omega)
              have hch_eq : p * (Nat.choose p (k + 1) / p) = Nat.choose p (k + 1) := Nat.mul_div_cancel' hch
              rw [← pow_mul]
              have hexp : (v + 1) * (k + 1) = (v + 1) + (v + 1) * k := by ring
              rw [hexp, pow_add, pow_succ (a := p) (v + 1)]
              calc
                p ^ (v + 1) * p ^ ((v + 1) * k) * Nat.choose p (k + 1)
                  = p ^ (v + 1) * p ^ ((v + 1) * k) * (p * (Nat.choose p (k + 1) / p)) := by rw [hch_eq]
                _ = p ^ (v + 1) * p * (Nat.choose p (k + 1) / p * p ^ ((v + 1) * k)) := by ring
          calc
            PowerSeries.C (((p ^ (v + 1) : ℕ) : ℚ) ^ (k + 1)) * U ^ (k + 1) *
                (B ^ (p ^ v)) ^ (p - (k + 1)) * ((Nat.choose p (k + 1) : ℕ) : PowerSeries ℚ)
              = (PowerSeries.C (((p ^ (v + 1) : ℕ) : ℚ) ^ (k + 1)) *
                  ((Nat.choose p (k + 1) : ℕ) : PowerSeries ℚ)) *
                  (U ^ (k + 1) * (B ^ (p ^ v)) ^ (p - (k + 1))) := by ring
            _ = PowerSeries.C (((p ^ (v + 2) : ℕ) : ℚ) * ((c k : ℕ) : ℚ)) *
                  (U ^ (k + 1) * (B ^ (p ^ v)) ^ (p - (k + 1))) := by rw [hcoeff_eq]
  intro v j
  obtain ⟨U, hU_int, hU_eq⟩ := hlift v
  obtain ⟨z, hz⟩ := hU_int j
  have hdiff : PowerSeries.coeff j (A ^ (p ^ v)) - PowerSeries.coeff j (B ^ (p ^ v)) =
      ((p ^ (v + 1) : ℕ) : ℚ) * (z : ℚ) := by
    have := congr_arg (PowerSeries.coeff j) hU_eq
    rw [map_add, PowerSeries.coeff_C_mul, hz] at this
    linarith
  rw [hdiff]
  have hpv0 : ((p ^ (v + 1) : ℕ) : ℚ) ≠ 0 := by
    have : 0 < p ^ (v + 1) := pow_pos hp.pos _
    exact_mod_cast this.ne'
  rw [mul_div_cancel_left₀ _ hpv0]
  exact isPInt_int hp z

/-- General Dwork integrality theorem for `G = ∑_{n=1}^N (f n)^n * X^n / n`:
if each `f n` has integer coefficients and `(f (p * n))^p ≡ f(n)(X^p) (mod p)` for all primes `p`
and `1 ≤ n ≤ N / p`, then `expSeries G` has integer coefficients through degree `N`! -/
private lemma dwork_pow_logSeries_isInt (N : ℕ) (f : ℕ → PowerSeries ℚ)
    (hf_int : ∀ n j, ∃ z : ℤ, PowerSeries.coeff j (f n) = (z : ℚ))
    (hf_cong : ∀ (p n j : ℕ), p.Prime → 1 ≤ n → n * p ≤ N →
      isPInt p ((PowerSeries.coeff j ((f (p * n)) ^ p) - PowerSeries.coeff j (substPow p (f n))) / (p : ℚ))) :
    ∀ k ≤ N, ∃ z : ℤ,
      PowerSeries.coeff k (expSeries (∑ n ∈ Finset.Icc 1 N,
        PowerSeries.C ((1 : ℚ) / (n : ℚ)) * ((f n) ^ n * PowerSeries.X ^ n))) = (z : ℚ) := by
  set G : PowerSeries ℚ := ∑ n ∈ Finset.Icc 1 N,
    PowerSeries.C ((1 : ℚ) / (n : ℚ)) * ((f n) ^ n * PowerSeries.X ^ n)
  have hG0 : PowerSeries.coeff 0 G = 0 := by
    simp only [G, map_sum, PowerSeries.coeff_C_mul]
    refine Finset.sum_eq_zero fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    rw [mul_comm ((f n) ^ n), PowerSeries.coeff_X_pow_mul']
    simp [show ¬ n ≤ 0 by omega]
  intro k hk
  apply isInt_of_forall_prime_isPInt
  intro p hp
  apply dwork_lemma hp hG0 _ k hk
  intro m hm1 hmN
  -- Compute `[X^m] (substPow p G - C p * G) / p`!
  have hsubst_G : substPow p G = ∑ n ∈ Finset.Icc 1 N,
      PowerSeries.C ((1 : ℚ) / (n : ℚ)) * ((substPow p (f n)) ^ n * PowerSeries.X ^ (p * n)) := by
    apply PowerSeries.ext; intro r
    simp only [G, coeff_substPow, map_sum, PowerSeries.coeff_C_mul]
    by_cases hpr : p ∣ r
    · simp only [hpr, ↓reduceIte]
      obtain ⟨r', rfl⟩ := hpr
      rw [Nat.mul_div_cancel_left _ hp.pos]
      refine Finset.sum_congr rfl fun n _ => ?_
      congr 1
      rw [mul_comm ((f n) ^ n), PowerSeries.coeff_X_pow_mul',
          mul_comm ((substPow p (f n)) ^ n), PowerSeries.coeff_X_pow_mul',
          ← substPow_pow hp.pos (f n) n, coeff_substPow]
      by_cases hnr : n ≤ r'
      · have hpn : p * n ≤ p * r' := Nat.mul_le_mul_left p hnr
        have hsub : p * r' - p * n = p * (r' - n) := (Nat.mul_sub_left_distrib p r' n).symm
        simp only [hnr, hpn, ↓reduceIte, hsub, dvd_mul_right, Nat.mul_div_cancel_left _ hp.pos]
      · have hpn : ¬ p * n ≤ p * r' := fun h => hnr (Nat.le_of_mul_le_mul_left h hp.pos)
        simp [hnr, hpn]
    · simp only [hpr, ↓reduceIte]
      symm
      refine Finset.sum_eq_zero fun n _ => ?_
      rw [mul_comm ((substPow p (f n)) ^ n), PowerSeries.coeff_X_pow_mul']
      split_ifs with hpn
      · rw [← substPow_pow hp.pos (f n) n, coeff_substPow]
        have hndiv : ¬ p ∣ r - p * n := fun h => hpr (by
          rw [← Nat.sub_add_cancel hpn]; exact dvd_add h (dvd_mul_right p n))
        simp [hndiv]
      · ring
  -- Split `Icc 1 N` in `C p * G` into multiples of `p` and non-multiples of `p`!
  have hG_split :
      PowerSeries.coeff m (substPow p G - PowerSeries.C (p : ℚ) * G) / (p : ℚ) =
      (∑ n ∈ (Finset.Icc 1 (N / p)),
        ((PowerSeries.coeff m ((substPow p (f n)) ^ n * PowerSeries.X ^ (p * n)) -
          PowerSeries.coeff m (((f (p * n)) ^ p) ^ n * PowerSeries.X ^ (p * n))) /
          ((p * n : ℕ) : ℚ))) -
      (∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ p ∣ n),
        (PowerSeries.coeff m ((f n) ^ n * PowerSeries.X ^ n) / (n : ℚ))) := by
    rw [map_sub, hsubst_G, PowerSeries.coeff_C_mul]
    simp only [G, map_sum, PowerSeries.coeff_C_mul]
    -- Restrict the `substPow p G` sum to `Icc 1 (N / p)` since for `n > N / p`, `p * n > N ≥ m`!
    have hsubst_trim :
        ∑ n ∈ Finset.Icc 1 N, (1 / (n : ℚ)) * PowerSeries.coeff m ((substPow p (f n)) ^ n * PowerSeries.X ^ (p * n)) =
        ∑ n ∈ Finset.Icc 1 (N / p), (1 / (n : ℚ)) * PowerSeries.coeff m ((substPow p (f n)) ^ n * PowerSeries.X ^ (p * n)) := by
      symm
      refine Finset.sum_subset (by
        intro n hn; simp only [Finset.mem_Icc] at hn ⊢
        exact ⟨hn.1, le_trans hn.2 (Nat.div_le_self N p)⟩) ?_
      intro n hn hnot
      simp only [Finset.mem_Icc] at hn hnot
      have hgt : N < p * n := by
        have hlt : N / p < n := by omega
        have := Nat.lt_mul_of_div_lt hlt hp.pos
        linarith
      rw [mul_comm ((substPow p (f n)) ^ n), PowerSeries.coeff_X_pow_mul', if_neg (by omega), mul_zero]
    -- Split `G` sum into `p ∣ n` and `¬ p ∣ n`!
    have hG_part :
        ∑ n ∈ Finset.Icc 1 N, (1 / (n : ℚ)) * PowerSeries.coeff m ((f n) ^ n * PowerSeries.X ^ n) =
        (∑ n ∈ Finset.Icc 1 (N / p),
          (1 / ((p * n : ℕ) : ℚ)) * PowerSeries.coeff m (((f (p * n)) ^ p) ^ n * PowerSeries.X ^ (p * n))) +
        (∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ p ∣ n),
          (1 / (n : ℚ)) * PowerSeries.coeff m ((f n) ^ n * PowerSeries.X ^ n)) := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) (fun n => p ∣ n)]
      congr 1
      symm
      refine Finset.sum_nbij (fun n => p * n) ?_ ?_ ?_ ?_
      · intro n hn
        simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
        refine ⟨⟨by have := hp.pos; nlinarith, ?_⟩, dvd_mul_right p n⟩
        have := Nat.mul_le_mul_left p hn.2
        exact le_trans this (Nat.mul_div_le N p)
      · intro a _ b _ hab; exact Nat.eq_of_mul_eq_mul_left hp.pos hab
      · intro k hk
        obtain ⟨hkIcc, ⟨n, rfl⟩⟩ := Finset.mem_filter.mp hk
        obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hkIcc
        refine ⟨n, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
        · by_contra h0; have : n = 0 := by omega
          rw [this, mul_zero] at hk1; omega
        · exact (Nat.le_div_iff_mul_le hp.pos).mpr (by linarith)
      · intro n _; rw [← pow_mul]
    rw [hsubst_trim, hG_part]
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [mul_add, sub_add_eq_sub_sub, sub_div, sub_div, Finset.mul_sum, Finset.mul_sum,
        Finset.sum_div, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun n _ => ?_
      push_cast; field_simp [hp0]
    · refine Finset.sum_congr rfl fun n _ => ?_
      field_simp [hp0]
  rw [hG_split]
  refine isPInt_sub hp ?_ ?_
  · -- First sum: for each `n ∈ Icc 1 (N / p)`, apply `pow_prime_pow_sub_dvd_series`!
    refine isPInt_sum hp _ _ fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnN : n * p ≤ N := by
      have := (Finset.mem_Icc.mp hn).2
      have := Nat.mul_le_mul_left p this
      linarith [Nat.mul_div_le N p]
    rw [mul_comm ((substPow p (f n)) ^ n), PowerSeries.coeff_X_pow_mul',
        mul_comm (((f (p * n)) ^ p) ^ n), PowerSeries.coeff_X_pow_mul']
    by_cases hle : p * n ≤ m
    · simp only [hle, ↓reduceIte]
      set v := n.factorization p
      set u := n / p ^ v
      have hpow_dvd : p ^ v ∣ n := Nat.ordProj_dvd n p
      have hnu : p ^ v * u = n := Nat.mul_div_cancel' hpow_dvd
      have hpu : ¬ p ∣ u := by
        intro h
        have hpow1 : p ^ (v + 1) ∣ n := by
          rw [← hnu, pow_succ]; exact Nat.mul_dvd_mul_left (p ^ v) h
        have hle' := (hp.pow_dvd_iff_le_factorization (by omega)).mp hpow1
        omega
      have hA_int : ∀ j, ∃ z : ℤ, PowerSeries.coeff j ((f (p * n)) ^ p) = (z : ℚ) := by
        have hpow_int : ∀ (t j : ℕ), ∃ z : ℤ, PowerSeries.coeff j ((f (p * n)) ^ t) = (z : ℚ) := by
          intro t
          induction t with
          | zero => intro j; rw [pow_zero, PowerSeries.coeff_one]; split_ifs <;> [exact ⟨1, by simp⟩; exact ⟨0, by simp⟩]
          | succ t iht =>
              intro j
              rw [pow_succ, PowerSeries.coeff_mul,
                  Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                    (fun a b => PowerSeries.coeff a ((f (p * n)) ^ t) * PowerSeries.coeff b (f (p * n)))]
              choose z1 hz1 using iht
              choose z2 hz2 using hf_int (p * n)
              exact ⟨∑ a ∈ Finset.range (j + 1), z1 a * z2 (j - a), by
                rw [Int.cast_sum]; refine Finset.sum_congr rfl fun a _ => by rw [hz1 a, hz2 (j - a), Int.cast_mul]⟩
        exact hpow_int p
      have hB_int : ∀ j, ∃ z : ℤ, PowerSeries.coeff j (substPow p (f n)) = (z : ℚ) := by
        intro j; rw [coeff_substPow]
        split_ifs
        · exact hf_int n (j / p)
        · exact ⟨0, by simp⟩
      have hlift := pow_prime_pow_sub_dvd_series hp hA_int hB_int
        (fun j => hf_cong p n j hp hn1 hnN) v
      -- Now raise to the `u`-th power: `A^(p^v * u) - B^(p^v * u) = (A^(p^v) - B^(p^v)) * ∑ ...`!
      set A' := ((f (p * n)) ^ p) ^ (p ^ v)
      set B' := (substPow p (f n)) ^ (p ^ v)
      have hA'B'_int : ∀ (t j : ℕ), ∃ z : ℤ, PowerSeries.coeff j (A' ^ t) = (z : ℚ) := by
        intro t
        have : A' ^ t = (f (p * n)) ^ (p * p ^ v * t) := by simp only [A', ← pow_mul]
        rw [this]
        induction (p * p ^ v * t) with
        | zero => intro j; rw [pow_zero, PowerSeries.coeff_one]; split_ifs <;> [exact ⟨1, by simp⟩; exact ⟨0, by simp⟩]
        | succ s ihs =>
            intro j
            rw [pow_succ, PowerSeries.coeff_mul,
                Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                  (fun a b => PowerSeries.coeff a ((f (p * n)) ^ s) * PowerSeries.coeff b (f (p * n)))]
            choose z1 hz1 using ihs
            choose z2 hz2 using hf_int (p * n)
            exact ⟨∑ a ∈ Finset.range (j + 1), z1 a * z2 (j - a), by
              rw [Int.cast_sum]; refine Finset.sum_congr rfl fun a _ => by rw [hz1 a, hz2 (j - a), Int.cast_mul]⟩
      have hB'_int : ∀ (t j : ℕ), ∃ z : ℤ, PowerSeries.coeff j (B' ^ t) = (z : ℚ) := by
        intro t
        have : B' ^ t = (substPow p (f n)) ^ (p ^ v * t) := by simp only [B', ← pow_mul]
        rw [this]
        induction (p ^ v * t) with
        | zero => intro j; rw [pow_zero, PowerSeries.coeff_one]; split_ifs <;> [exact ⟨1, by simp⟩; exact ⟨0, by simp⟩]
        | succ s ihs =>
            intro j
            rw [pow_succ, PowerSeries.coeff_mul,
                Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                  (fun a b => PowerSeries.coeff a ((substPow p (f n)) ^ s) * PowerSeries.coeff b (substPow p (f n)))]
            choose z1 hz1 using ihs
            choose z2 hz2 using hB_int
            exact ⟨∑ a ∈ Finset.range (j + 1), z1 a * z2 (j - a), by
              rw [Int.cast_sum]; refine Finset.sum_congr rfl fun a _ => by rw [hz1 a, hz2 (j - a), Int.cast_mul]⟩
      have hfactor : A' ^ u - B' ^ u = (A' - B') * ∑ i ∈ Finset.range u, A' ^ i * B' ^ (u - 1 - i) := by
        simpa [mul_comm] using (geom_sum₂_mul A' B' u).symm
      have hpn_eq : ((p * n : ℕ) : ℚ) = ((p ^ (v + 1) : ℕ) : ℚ) * (u : ℚ) := by
        have : p * n = p ^ (v + 1) * u := by rw [← hnu, pow_succ', mul_assoc]
        exact_mod_cast this
      have hrew : (PowerSeries.coeff (m - p * n) ((substPow p (f n)) ^ n) -
          PowerSeries.coeff (m - p * n) (((f (p * n)) ^ p) ^ n)) / ((p * n : ℕ) : ℚ) =
          -((PowerSeries.coeff (m - p * n) (A' ^ u - B' ^ u)) / ((p ^ (v + 1) : ℕ) : ℚ)) / (u : ℚ) := by
        have h1 : ((f (p * n)) ^ p) ^ n = A' ^ u := by
          simp only [A', ← pow_mul, mul_assoc, hnu]
        have h2 : (substPow p (f n)) ^ n = B' ^ u := by
          simp only [B', ← pow_mul, hnu]
        rw [h1, h2, map_sub, hpn_eq]
        ring
      rw [hrew]
      refine isPInt_div_nat hp (isPInt_neg ?_) hpu
      rw [hfactor, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun a b => PowerSeries.coeff a (A' - B') *
              PowerSeries.coeff b (∑ i ∈ Finset.range u, A' ^ i * B' ^ (u - 1 - i))),
          Finset.sum_div]
      refine isPInt_sum hp _ _ fun a _ => ?_
      rw [mul_div_right_comm, map_sub]
      refine isPInt_mul hp (hlift a) ?_
      rw [map_sum]
      refine isPInt_sum hp _ _ fun i _ => ?_
      rw [PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun x y => PowerSeries.coeff x (A' ^ i) * PowerSeries.coeff y (B' ^ (u - 1 - i)))]
      refine isPInt_sum hp _ _ fun x _ => ?_
      obtain ⟨z1, hz1⟩ := hA'B'_int i x
      obtain ⟨z2, hz2⟩ := hB'_int (u - 1 - i) (m - p * n - a - x)
      rw [hz1, hz2]
      exact isPInt_mul hp (isPInt_int hp z1) (isPInt_int hp z2)
    · simp [hle, isPInt_zero hp]
  · -- Second sum: `¬ p ∣ n`, and `(f n)^n` has integer coefficients!
    refine isPInt_sum hp _ _ fun n hn => ?_
    have hnp : ¬ p ∣ n := (Finset.mem_filter.mp hn).2
    refine isPInt_div_nat hp ?_ hnp
    rw [mul_comm, PowerSeries.coeff_X_pow_mul']
    split_ifs
    · have hpow_int : ∀ (t j : ℕ), ∃ z : ℤ, PowerSeries.coeff j ((f n) ^ t) = (z : ℚ) := by
        intro t
        induction t with
        | zero => intro j; rw [pow_zero, PowerSeries.coeff_one]; split_ifs <;> [exact ⟨1, by simp⟩; exact ⟨0, by simp⟩]
        | succ t iht =>
            intro j
            rw [pow_succ, PowerSeries.coeff_mul,
                Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                  (fun a b => PowerSeries.coeff a ((f n) ^ t) * PowerSeries.coeff b (f n))]
            choose z1 hz1 using iht
            choose z2 hz2 using hf_int n
            exact ⟨∑ a ∈ Finset.range (j + 1), z1 a * z2 (j - a), by
              rw [Int.cast_sum]; refine Finset.sum_congr rfl fun a _ => by rw [hz1 a, hz2 (j - a), Int.cast_mul]⟩
      obtain ⟨z, hz⟩ := hpow_int n (m - n)
      rw [hz]; exact isPInt_int hp z
    · exact isPInt_zero hp


/-! ### Part 6: Application to OEIS OEIS_A156907 -/

private lemma scaleX_sub_one_eq_X_mul (k N : ℕ) (b : ℕ → ℚ) :
    scaleX ((2 : ℚ) ^ k) (PowerSeries.mk fun j => if j = 0 then 1 else if j < N + 1 then b (j - 1) else 0) - 1 =
      (PowerSeries.C ((2 : ℚ) ^ k) *
        scaleX ((2 : ℚ) ^ k) (PowerSeries.mk fun j => if j < N then b j else 0)) * PowerSeries.X := by
  apply PowerSeries.ext; intro r
  rw [map_sub, scaleX, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_one, mul_comm _ PowerSeries.X]
  cases r with
  | zero =>
      rw [PowerSeries.coeff_zero_X_mul]; simp
  | succ r =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul, scaleX, PowerSeries.coeff_mk,
          PowerSeries.coeff_mk]
      simp only [Nat.succ_ne_zero, ↓reduceIte, sub_zero, Nat.add_sub_cancel]
      have hlt_iff : r + 1 < N + 1 ↔ r < N := by omega
      simp only [hlt_iff]
      split_ifs
      · rw [pow_succ']
        ring
      · ring

private lemma coeff_logSeriesTrunc_congr (f₁ f₂ : PowerSeries ℚ) (N₁ N₂ k : ℕ)
    (hf10 : PowerSeries.coeff 0 f₁ = 1) (hf20 : PowerSeries.coeff 0 f₂ = 1)
    (hk1 : k ≤ N₁) (hk2 : k ≤ N₂)
    (hf : ∀ j ≤ k, PowerSeries.coeff j f₁ = PowerSeries.coeff j f₂) :
    PowerSeries.coeff k (logSeriesTrunc f₁ N₁) = PowerSeries.coeff k (logSeriesTrunc f₂ N₂) := by
  have hsub0 : ∀ (f : PowerSeries ℚ) (n : ℕ), PowerSeries.coeff 0 f = 1 →
      PowerSeries.coeff 0 (scaleX ((2 : ℚ) ^ n) f - 1) = 0 := by
    intro f n hf0
    rw [map_sub, scaleX, PowerSeries.coeff_mk, pow_zero, one_mul, hf0, PowerSeries.coeff_one]
    simp
  have hpow0 : ∀ (g : PowerSeries ℚ), PowerSeries.coeff 0 g = 0 →
      ∀ (t r : ℕ), r < t → PowerSeries.coeff r (g ^ t) = 0 := by
    intro g hg0 t
    induction t with
    | zero => intro r hr; omega
    | succ t iht =>
        intro r hr
        rw [pow_succ, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun a b => PowerSeries.coeff a (g ^ t) * PowerSeries.coeff b g)]
        refine Finset.sum_eq_zero fun a ha => ?_
        have hal : a ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        by_cases har : a = r
        · subst har; rw [Nat.sub_self, hg0, mul_zero]
        · rw [iht a (by omega), zero_mul]
  have htrim : ∀ (f : PowerSeries ℚ) (N : ℕ), PowerSeries.coeff 0 f = 1 → k ≤ N →
      PowerSeries.coeff k (logSeriesTrunc f N) = PowerSeries.coeff k (logSeriesTrunc f k) := by
    intro f N hf0 hkN
    simp only [logSeriesTrunc, map_sum, PowerSeries.coeff_C_mul]
    symm
    refine Finset.sum_subset (Finset.Icc_subset_Icc_right hkN) ?_
    intro n hn hnot
    simp only [Finset.mem_Icc] at hn hnot
    rw [hpow0 _ (hsub0 f n hf0) n k (by omega), mul_zero]
  rw [htrim f₁ N₁ hf10 hk1, htrim f₂ N₂ hf20 hk2]
  simp only [logSeriesTrunc, map_sum, PowerSeries.coeff_C_mul]
  refine Finset.sum_congr rfl fun n hn => ?_
  congr 1
  have hpow_eq : ∀ (t r : ℕ), r ≤ k →
      PowerSeries.coeff r ((scaleX ((2 : ℚ) ^ n) f₁ - 1) ^ t) =
      PowerSeries.coeff r ((scaleX ((2 : ℚ) ^ n) f₂ - 1) ^ t) := by
    intro t
    induction t with
    | zero => intro r _; rfl
    | succ t iht =>
        intro r hr
        rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun a b => PowerSeries.coeff a ((scaleX ((2 : ℚ) ^ n) f₁ - 1) ^ t) *
                PowerSeries.coeff b (scaleX ((2 : ℚ) ^ n) f₁ - 1)),
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun a b => PowerSeries.coeff a ((scaleX ((2 : ℚ) ^ n) f₂ - 1) ^ t) *
                PowerSeries.coeff b (scaleX ((2 : ℚ) ^ n) f₂ - 1))]
        refine Finset.sum_congr rfl fun a ha => ?_
        have hal : a ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        rw [iht a (by omega), map_sub, map_sub, scaleX, scaleX, PowerSeries.coeff_mk,
            PowerSeries.coeff_mk, hf (r - a) (by omega)]
  exact hpow_eq n k (le_refl k)

private lemma b_eq_expCoeffs (N : ℕ) :
    ∀ k ≤ N,
      b156907 k = expCoeffs (logSeriesTrunc
        (PowerSeries.mk fun j => if j = 0 then 1 else if j < N + 1 then b156907 (j - 1) else 0) N) k := by
  set AprevN : PowerSeries ℚ :=
    PowerSeries.mk fun j => if j = 0 then 1 else if j < N + 1 then b156907 (j - 1) else 0
  intro k hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => rw [b156907, expCoeffs]
    | succ k' =>
        rw [b156907, expCoeffs]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        have hjlt : j.val < k' + 1 := j.isLt
        rw [ih (k' - j.val) (by omega) (by omega)]
        congr 1
        congr 1
        exact coeff_logSeriesTrunc_congr _ AprevN (k' + 1) N (j.val + 1)
          (by simp) (by simp [AprevN]) (by omega) (by omega)
          (fun r hr => by
            simp only [AprevN, PowerSeries.coeff_mk]
            split_ifs <;> first | rfl | omega)

private lemma b_isInt : ∀ n : ℕ, ∃ z : ℤ, b156907 n = (z : ℚ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h N ih =>
    set Bprev : PowerSeries ℚ := PowerSeries.mk fun j => if j < N then b156907 j else 0
    have hBprev_int : ∀ j, ∃ z : ℤ, PowerSeries.coeff j Bprev = (z : ℚ) := by
      intro j
      rw [PowerSeries.coeff_mk]
      split_ifs with hj
      · exact ih j hj
      · exact ⟨0, by simp⟩
    let f : ℕ → PowerSeries ℚ := fun m => PowerSeries.C ((2 : ℚ) ^ m) * scaleX ((2 : ℚ) ^ m) Bprev
    have hf_int : ∀ m j, ∃ z : ℤ, PowerSeries.coeff j (f m) = (z : ℚ) := by
      intro m j
      obtain ⟨z, hz⟩ := hBprev_int j
      simp only [f, PowerSeries.coeff_C_mul, scaleX, PowerSeries.coeff_mk, hz]
      exact ⟨(2 : ℤ) ^ m * ((2 : ℤ) ^ m) ^ j * z, by push_cast; ring⟩
    have hf_cong : ∀ (p m j : ℕ), p.Prime → 1 ≤ m → m * p ≤ N →
        isPInt p ((PowerSeries.coeff j ((f (p * m)) ^ p) - PowerSeries.coeff j (substPow p (f m))) / (p : ℚ)) := by
      intro p m j hp _ _
      have hfr := freshman_dream_series (p := p) (n := j) hp (fun r _ => by
        obtain ⟨z, hz⟩ := hf_int (p * m) r
        rw [hz]; exact isPInt_int hp z)
      rw [coeff_substPow]
      by_cases hdiv : p ∣ j
      · simp only [hdiv, ↓reduceIte] at hfr ⊢
        have hrew : (PowerSeries.coeff j ((f (p * m)) ^ p) - PowerSeries.coeff (j / p) (f m)) / (p : ℚ) =
            (PowerSeries.coeff j ((f (p * m)) ^ p) - (PowerSeries.coeff (j / p) (f (p * m))) ^ p) / (p : ℚ) +
            ((PowerSeries.coeff (j / p) (f (p * m))) ^ p - PowerSeries.coeff (j / p) (f m)) / (p : ℚ) := by
          ring
        rw [hrew]
        refine isPInt_add hp hfr ?_
        obtain ⟨z, hz⟩ := hBprev_int (j / p)
        simp only [f, PowerSeries.coeff_C_mul, scaleX, PowerSeries.coeff_mk, hz]
        have : Fact p.Prime := ⟨hp⟩
        have hmod : (p : ℤ) ∣ ((((2 : ℤ) ^ (p * m) * ((2 : ℤ) ^ (p * m)) ^ (j / p) * z) ^ p) -
            ((2 : ℤ) ^ m * ((2 : ℤ) ^ m) ^ (j / p) * z)) := by
          rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
          push_cast
          rw [mul_pow, mul_pow, ZMod.pow_card, ZMod.pow_card, ZMod.pow_card,
              ← pow_mul, ← pow_mul, ← pow_add, ← pow_add,
              show p * m + p * m * (j / p) = (m + m * (j / p)) * p by ring,
              pow_mul, ZMod.pow_card, sub_self]
        obtain ⟨t, ht⟩ := hmod
        have ht_q : ((2 : ℚ) ^ (p * m) * ((2 : ℚ) ^ (p * m)) ^ (j / p) * (z : ℚ)) ^ p -
            ((2 : ℚ) ^ m * ((2 : ℚ) ^ m) ^ (j / p) * (z : ℚ)) = (p : ℚ) * (t : ℚ) := by
          exact_mod_cast ht
        rw [← mul_assoc, ← mul_assoc, ht_q]
        exact isPInt_mul_p_inv hp (isPInt_int hp t)
      · simp only [hdiv, ↓reduceIte, sub_zero] at hfr ⊢
        exact hfr
    have hint := dwork_pow_logSeries_isInt N f hf_int hf_cong N (le_refl N)
    have hlog_eq : logSeriesTrunc
        (PowerSeries.mk fun j => if j = 0 then 1 else if j < N + 1 then b156907 (j - 1) else 0) N =
        ∑ n ∈ Finset.Icc 1 N, PowerSeries.C ((1 : ℚ) / (n : ℚ)) * ((f n) ^ n * PowerSeries.X ^ n) := by
      simp only [logSeriesTrunc]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [scaleX_sub_one_eq_X_mul k N b156907, mul_pow]
    rw [b_eq_expCoeffs N N (le_refl N), hlog_eq]
    simpa [expSeries] using hint

theorem main_proof :
    ∀ n : ℕ, ∃ z : ℤ, a156907 n = (z : ℚ) := by
  intro n
  cases n with
  | zero => exact ⟨1, by simp [a156907]⟩
  | succ n => rw [a156907]; exact b_isInt n

end OMA.S_oeis_a156907

theorem OMA.solution : type_of% @OMA.S_oeis_a156907.main :=
  OMA.S_oeis_a156907.main_proof
