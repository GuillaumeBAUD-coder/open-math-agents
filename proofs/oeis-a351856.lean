import OMAStatements.S_oeis_a351856

-- Problem: A351856: Number of nonnegative integer solutions to 2*n = x1 + x2 + ... + xn + 2*y1 + 2*y2 + ... + 2*yn.
-- Upstream: formal-conjectures statements/oeis-a351856.lean:0 (declaration OMA.S_oeis_a351856.main)
-- Credit: @smorshenniygus (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace A351856Proof

open Polynomial Finset

/-! ### Section 1: p-adic divisibility in ℚ -/

private def IsPDvdZ (p K : ℕ) (q : ℚ) : Prop :=
  ∃ N D : ℤ, ¬ (p : ℤ) ∣ D ∧ ((p ^ K : ℕ) : ℤ) ∣ N ∧ q = (N : ℚ) / (D : ℚ)

private lemma int_ne_zero_of_not_dvd {p : ℕ} {D : ℤ} (hD : ¬ (p : ℤ) ∣ D) : D ≠ 0 := by
  intro h0
  exact hD (h0 ▸ dvd_zero _)

private lemma rat_ne_zero_of_not_dvd {p : ℕ} {D : ℤ} (hD : ¬ (p : ℤ) ∣ D) : (D : ℚ) ≠ 0 :=
  Int.cast_ne_zero.mpr (int_ne_zero_of_not_dvd hD)

private lemma not_dvd_one_int {p : ℕ} (hp : p.Prime) : ¬ (p : ℤ) ∣ (1 : ℤ) :=
  fun h => hp.not_dvd_one (Int.ofNat_dvd.mp h)

private lemma isPDvdZ_zero {p K : ℕ} (hp : p.Prime) : IsPDvdZ p K 0 :=
  ⟨0, 1, not_dvd_one_int hp, dvd_zero _, by simp⟩

private lemma isPDvdZ_mono {p K1 K2 : ℕ} {q : ℚ} (hle : K1 ≤ K2) (h : IsPDvdZ p K2 q) :
    IsPDvdZ p K1 q := by
  rcases h with ⟨N, D, hD, hN, hq⟩
  exact ⟨N, D, hD, dvd_trans (Int.ofNat_dvd.mpr (Nat.pow_dvd_pow p hle)) hN, hq⟩

private lemma isPDvdZ_neg {p K : ℕ} {q : ℚ} (h : IsPDvdZ p K q) : IsPDvdZ p K (-q) := by
  rcases h with ⟨N, D, hD, hN, rfl⟩
  refine ⟨-N, D, hD, dvd_neg.mpr hN, ?_⟩
  push_cast
  ring

private lemma isPDvdZ_add {p K : ℕ} (hp : p.Prime) {q1 q2 : ℚ}
    (h1 : IsPDvdZ p K q1) (h2 : IsPDvdZ p K q2) : IsPDvdZ p K (q1 + q2) := by
  rcases h1 with ⟨N1, D1, hD1, hN1, rfl⟩
  rcases h2 with ⟨N2, D2, hD2, hN2, rfl⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hD12 : ¬ (p : ℤ) ∣ D1 * D2 := fun h => (hpZ.dvd_or_dvd h).elim hD1 hD2
  have h1ne : (D1 : ℚ) ≠ 0 := rat_ne_zero_of_not_dvd hD1
  have h2ne : (D2 : ℚ) ≠ 0 := rat_ne_zero_of_not_dvd hD2
  refine ⟨N1 * D2 + N2 * D1, D1 * D2, hD12,
    dvd_add (dvd_mul_of_dvd_left hN1 D2) (dvd_mul_of_dvd_left hN2 D1), ?_⟩
  push_cast
  field_simp

private lemma isPDvdZ_sub {p K : ℕ} (hp : p.Prime) {q1 q2 : ℚ}
    (h1 : IsPDvdZ p K q1) (h2 : IsPDvdZ p K q2) : IsPDvdZ p K (q1 - q2) := by
  rw [sub_eq_add_neg]
  exact isPDvdZ_add hp h1 (isPDvdZ_neg h2)

private lemma isPDvdZ_sum {ι : Type*} {p K : ℕ} (hp : p.Prime) (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, IsPDvdZ p K (f i)) : IsPDvdZ p K (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPDvdZ_zero hp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isPDvdZ_add hp (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma isPDvdZ_mul {p K1 K2 : ℕ} (hp : p.Prime) {q1 q2 : ℚ}
    (h1 : IsPDvdZ p K1 q1) (h2 : IsPDvdZ p K2 q2) : IsPDvdZ p (K1 + K2) (q1 * q2) := by
  rcases h1 with ⟨N1, D1, hD1, hN1, rfl⟩
  rcases h2 with ⟨N2, D2, hD2, hN2, rfl⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hD12 : ¬ (p : ℤ) ∣ D1 * D2 := fun h => (hpZ.dvd_or_dvd h).elim hD1 hD2
  have hN12 : ((p ^ (K1 + K2) : ℕ) : ℤ) ∣ N1 * N2 := by
    rw [pow_add, Nat.cast_mul]
    exact mul_dvd_mul hN1 hN2
  refine ⟨N1 * N2, D1 * D2, hD12, hN12, ?_⟩
  push_cast
  ring

private lemma isPDvdZ_intCast {p K : ℕ} (hp : p.Prime) (n : ℤ)
    (hn : ((p ^ K : ℕ) : ℤ) ∣ n) : IsPDvdZ p K (n : ℚ) :=
  ⟨n, 1, not_dvd_one_int hp, hn, by simp⟩

private lemma isPDvdZ_intCast_zero {p : ℕ} (hp : p.Prime) (n : ℤ) : IsPDvdZ p 0 (n : ℚ) :=
  isPDvdZ_intCast hp n (by simp)

private lemma isPDvdZ_natCast {p K : ℕ} (hp : p.Prime) (n : ℕ)
    (hn : p ^ K ∣ n) : IsPDvdZ p K (n : ℚ) :=
  ⟨(n : ℤ), 1, not_dvd_one_int hp, Int.ofNat_dvd.mpr hn, by simp⟩

private lemma isPDvdZ_natCast_zero {p : ℕ} (hp : p.Prime) (n : ℕ) : IsPDvdZ p 0 (n : ℚ) :=
  isPDvdZ_natCast hp n (by simp)

private lemma isPDvdZ_pow {p K : ℕ} (hp : p.Prime) {q : ℚ} (h : IsPDvdZ p K q) (m : ℕ) :
    IsPDvdZ p (m * K) (q ^ m) := by
  induction m with
  | zero =>
    simpa using isPDvdZ_natCast_zero hp 1
  | succ m ih =>
    rw [pow_succ, Nat.succ_mul]
    exact isPDvdZ_mul hp ih h

private lemma isPDvdZ_div_nat {p K d : ℕ} (hp : p.Prime) (hd : d ≠ 0) {q : ℚ}
    (hq : IsPDvdZ p (K + padicValNat p d) q) : IsPDvdZ p K (q / (d : ℚ)) := by
  have : Fact p.Prime := ⟨hp⟩
  rcases hq with ⟨N, D, hD, hN, rfl⟩
  set v := padicValNat p d
  have hdv : p ^ v ∣ d := pow_padicValNat_dvd
  rcases hdv with ⟨u, hu⟩
  have hu_ndvd : ¬ p ∣ u := by
    intro hpu
    have hdv1 : p ^ (v + 1) ∣ d := by
      rcases hpu with ⟨w, rfl⟩
      refine ⟨w, ?_⟩
      rw [hu, pow_succ]
      ring
    have hle := (padicValNat_dvd_iff_le hd).mp hdv1
    omega
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hDu : ¬ (p : ℤ) ∣ D * (u : ℤ) := by
    intro h
    rcases hpZ.dvd_or_dvd h with h1 | h2
    · exact hD h1
    · exact hu_ndvd (Int.ofNat_dvd.mp h2)
  rcases hN with ⟨M, hM⟩
  have hN' : ((p ^ K : ℕ) : ℤ) ∣ ((p ^ K : ℕ) : ℤ) * M := dvd_mul_right _ _
  refine ⟨((p ^ K : ℕ) : ℤ) * M, D * (u : ℤ), hDu, hN', ?_⟩
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpv_ne : (p : ℚ) ^ v ≠ 0 := pow_ne_zero v hp_ne
  have hD_ne : (D : ℚ) ≠ 0 := rat_ne_zero_of_not_dvd hD
  have hu_ne : (u : ℚ) ≠ 0 := by
    intro hu0
    have : u = 0 := Nat.cast_eq_zero.mp hu0
    exact hu_ndvd (this ▸ dvd_zero p)
  have hd_eq : (d : ℚ) = (p : ℚ) ^ v * (u : ℚ) := by exact_mod_cast hu
  have hN_eq : (N : ℚ) = (p : ℚ) ^ K * (p : ℚ) ^ v * (M : ℚ) := by
    have : (N : ℤ) = ((p ^ K : ℕ) : ℤ) * ((p ^ v : ℕ) : ℤ) * M := by
      rw [hM, pow_add, Nat.cast_mul, mul_assoc]
    exact_mod_cast this
  rw [hd_eq, hN_eq]
  push_cast
  field_simp

private lemma isPDvdZ_div_coprime_nat {p K d : ℕ} (hp : p.Prime) (hd : ¬ p ∣ d) {q : ℚ}
    (hq : IsPDvdZ p K q) : IsPDvdZ p K (q / (d : ℚ)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hd0 : d ≠ 0 := fun h => hd (h ▸ dvd_zero p)
  have hv : padicValNat p d = 0 := padicValNat.eq_zero_of_not_dvd hd
  exact isPDvdZ_div_nat hp hd0 (by simpa [hv] using hq)

private lemma isPDvdZ_inv_sub_one {p K : ℕ} (_hp : p.Prime) (hK : 1 ≤ K) {u : ℚ}
    (hu : IsPDvdZ p K u) : IsPDvdZ p K ((1 + u)⁻¹ - 1) ∧ 1 + u ≠ 0 := by
  rcases hu with ⟨N, D, hD, hN, rfl⟩
  have hpN : (p : ℤ) ∣ N :=
    dvd_trans (Int.ofNat_dvd.mpr (dvd_pow_self p (by omega : K ≠ 0))) hN
  have hDN : ¬ (p : ℤ) ∣ (D + N) := by
    intro h
    have : (p : ℤ) ∣ D := (dvd_add_left hpN).mp h
    exact hD this
  have hD_ne : (D : ℚ) ≠ 0 := rat_ne_zero_of_not_dvd hD
  have hDN_ne : (D : ℚ) + (N : ℚ) ≠ 0 := by
    have := rat_ne_zero_of_not_dvd hDN
    push_cast at this
    exact this
  have h1u : 1 + (N : ℚ) / (D : ℚ) = ((D : ℚ) + (N : ℚ)) / (D : ℚ) := by
    field_simp
  have h1u_ne : 1 + (N : ℚ) / (D : ℚ) ≠ 0 := by
    rw [h1u]
    exact div_ne_zero hDN_ne hD_ne
  refine ⟨⟨-N, D + N, hDN, dvd_neg.mpr hN, ?_⟩, h1u_ne⟩
  rw [h1u]
  push_cast
  field_simp
  ring

private lemma isPDvdZ_dvd_int {p K : ℕ} (hp : p.Prime) {m : ℤ}
    (h : IsPDvdZ p K (m : ℚ)) : ((p ^ K : ℕ) : ℤ) ∣ m := by
  rcases h with ⟨N, D, hD, hN, hm⟩
  have hD_ne : (D : ℚ) ≠ 0 := rat_ne_zero_of_not_dvd hD
  have hq : (m : ℚ) * (D : ℚ) = (N : ℚ) := (eq_div_iff hD_ne).mp hm
  have hz : m * D = N := by exact_mod_cast hq
  have hpK_dvd : ((p ^ K : ℕ) : ℤ) ∣ m * D := hz ▸ hN
  have hcop : IsCoprime ((p ^ K : ℕ) : ℤ) D := by
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hcop1 : IsCoprime (p : ℤ) D := hpZ.coprime_iff_not_dvd.mpr hD
    simpa [Nat.cast_pow] using hcop1.pow_left (m := K)
  exact hcop.dvd_of_dvd_mul_right hpK_dvd

/-! ### Section 2: Truncated logarithm modulo p^K -/

private lemma coeff_eq_zero_of_mul_unit_coeff_zero {A B : ℚ[X]} {K : ℕ}
    (hA0 : A.coeff 0 = 1) (hAB : ∀ j < K, (A * B).coeff j = 0) :
    ∀ j < K, B.coeff j = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    have h0 := hAB j hj
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => A.coeff a * B.coeff b) j] at h0
    rw [Finset.sum_range_succ'] at h0
    simp only [Nat.sub_zero, hA0, one_mul] at h0
    have hrest : ∑ k ∈ Finset.range j, A.coeff (k + 1) * B.coeff (j - (k + 1)) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro k hk
      have hkj : j - (k + 1) < j := by
        have := Finset.mem_range.mp hk
        omega
      rw [ih (j - (k + 1)) hkj (by omega), mul_zero]
    rw [hrest, zero_add] at h0
    exact h0

private lemma poly_isPDvdZ_zero_mul {p : ℕ} (hp : p.Prime) {f g : ℚ[X]}
    (hf : ∀ m, IsPDvdZ p 0 (f.coeff m)) (hg : ∀ m, IsPDvdZ p 0 (g.coeff m)) :
    ∀ m, IsPDvdZ p 0 ((f * g).coeff m) := by
  intro m
  rw [coeff_mul]
  refine isPDvdZ_sum hp _ _ ?_
  intro x _
  simpa using isPDvdZ_mul hp (hf x.1) (hg x.2)

private lemma poly_isPDvdZ_zero_pow {p : ℕ} (hp : p.Prime) {f : ℚ[X]}
    (hf : ∀ m, IsPDvdZ p 0 (f.coeff m)) (k : ℕ) :
    ∀ m, IsPDvdZ p 0 ((f ^ k).coeff m) := by
  induction k with
  | zero =>
    intro m
    rw [pow_zero, coeff_one]
    split_ifs
    · exact isPDvdZ_natCast_zero hp 1
    · exact isPDvdZ_zero hp
  | succ k ih =>
    rw [pow_succ]
    exact poly_isPDvdZ_zero_mul hp ih hf

private lemma legendre_sum_bound {p : ℕ} (hp : p.Prime) (n b : ℕ) :
    (p - 1) * (∑ i ∈ Finset.Ico 1 (b + 1), n / p ^ i) + n / p ^ b ≤ n := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ b + 1), Nat.mul_add]
    have hdiv : p * (n / p ^ (b + 1)) ≤ n / p ^ b := by
      rw [pow_succ, ← Nat.div_div_eq_div_mul]
      exact Nat.mul_div_le (n / p ^ b) p
    have hadd : (p - 1) * (n / p ^ (b + 1)) + n / p ^ (b + 1) = p * (n / p ^ (b + 1)) := by
      cases p with
      | zero => exact absurd hp.ne_zero (by simp)
      | succ p => simp [Nat.succ_mul]
    omega

private lemma legendre_bound {p n : ℕ} (hp : p.Prime) :
    (p - 1) * padicValNat p n.factorial ≤ n := by
  have : Fact p.Prime := ⟨hp⟩
  have hlt : Nat.log p n < n + 1 := Nat.lt_succ_of_le (Nat.log_le_self p n)
  rw [padicValNat_factorial hlt]
  exact le_trans (Nat.le_add_right _ _) (legendre_sum_bound hp n n)

private def PolyEqMod (N : ℕ) (P Q : ℚ[X]) : Prop :=
  ∀ k ≤ N, P.coeff k = Q.coeff k

private lemma polyEqMod_refl (N : ℕ) (P : ℚ[X]) : PolyEqMod N P P :=
  fun _ _ => rfl

private lemma polyEqMod_symm {N : ℕ} {P Q : ℚ[X]} (h : PolyEqMod N P Q) : PolyEqMod N Q P :=
  fun k hk => (h k hk).symm

private lemma polyEqMod_trans {N : ℕ} {P Q R : ℚ[X]}
    (h1 : PolyEqMod N P Q) (h2 : PolyEqMod N Q R) : PolyEqMod N P R :=
  fun k hk => (h1 k hk).trans (h2 k hk)

private lemma polyEqMod_mono {N1 N2 : ℕ} {P Q : ℚ[X]} (hle : N1 ≤ N2)
    (h : PolyEqMod N2 P Q) : PolyEqMod N1 P Q :=
  fun k hk => h k (le_trans hk hle)

private lemma polyEqMod_add {N : ℕ} {P1 P2 Q1 Q2 : ℚ[X]}
    (h1 : PolyEqMod N P1 Q1) (h2 : PolyEqMod N P2 Q2) :
    PolyEqMod N (P1 + P2) (Q1 + Q2) := by
  intro k hk
  simp only [coeff_add, h1 k hk, h2 k hk]

private lemma polyEqMod_sub {N : ℕ} {P1 P2 Q1 Q2 : ℚ[X]}
    (h1 : PolyEqMod N P1 Q1) (h2 : PolyEqMod N P2 Q2) :
    PolyEqMod N (P1 - P2) (Q1 - Q2) := by
  intro k hk
  simp only [coeff_sub, h1 k hk, h2 k hk]

private lemma polyEqMod_mul {N : ℕ} {P1 P2 Q1 Q2 : ℚ[X]}
    (h1 : PolyEqMod N P1 Q1) (h2 : PolyEqMod N P2 Q2) :
    PolyEqMod N (P1 * P2) (Q1 * Q2) := by
  intro k hk
  rw [coeff_mul, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hxk : x ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
  rw [h1 x (by omega), h2 (k - x) (by omega)]

private lemma polyEqMod_pow {N : ℕ} {P Q : ℚ[X]} (h : PolyEqMod N P Q) (m : ℕ) :
    PolyEqMod N (P ^ m) (Q ^ m) := by
  induction m with
  | zero => exact polyEqMod_refl N 1
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact polyEqMod_mul ih h

private lemma polyEqMod_sum {ι : Type*} {N : ℕ} (s : Finset ι) (f g : ι → ℚ[X])
    (h : ∀ i ∈ s, PolyEqMod N (f i) (g i)) :
    PolyEqMod N (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  intro k hk
  rw [Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact h i hi k hk

private lemma polyEqMod_cancel_unit {N : ℕ} {U P Q : ℚ[X]} (hU : U.coeff 0 ≠ 0)
    (h : PolyEqMod N (U * P) (U * Q)) : PolyEqMod N P Q := by
  set U' : ℚ[X] := C (U.coeff 0)⁻¹ * U
  have hU' : U'.coeff 0 = 1 := by
    dsimp [U']
    rw [coeff_C_mul, inv_mul_cancel₀ hU]
  have hdiff : ∀ k < N + 1, (U' * (P - Q)).coeff k = 0 := by
    intro k hk
    dsimp [U']
    rw [mul_assoc, coeff_C_mul, mul_sub, coeff_sub, h k (Nat.lt_succ_iff.mp hk), sub_self, mul_zero]
  have hzero := coeff_eq_zero_of_mul_unit_coeff_zero hU' hdiff
  intro k hk
  have := hzero k (Nat.lt_succ_of_le hk)
  rw [coeff_sub] at this
  linarith

private lemma coeff_X_mul_nat (P : ℚ[X]) (k : ℕ) :
    (X * P).coeff k = if k = 0 then 0 else P.coeff (k - 1) := by
  cases k with
  | zero => simp
  | succ k => simp [coeff_X_mul]

private lemma coeff_pow_eq_zero_of_lt {u : ℚ[X]} (hu0 : u.coeff 0 = 0) {e k : ℕ} (hk : k < e) :
    (u ^ e).coeff k = 0 := by
  have hX : X ∣ u := Polynomial.X_dvd_iff.mpr hu0
  rcases hX with ⟨v, rfl⟩
  rw [mul_pow, coeff_X_pow_mul']
  simp [not_le.mpr hk]

private lemma coeff_comp_of_coeff_zero {P u : ℚ[X]} (hu0 : u.coeff 0 = 0) {k N : ℕ} (hk : k ≤ N) :
    (P.comp u).coeff k = ∑ e ∈ Finset.range (N + 1), P.coeff e * (u ^ e).coeff k := by
  set M := max (P.natDegree + 1) (N + 1)
  have hP : P = ∑ e ∈ Finset.range M, C (P.coeff e) * X ^ e := by
    have h1 := Polynomial.as_sum_range' P M (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _))
    simpa only [Polynomial.C_mul_X_pow_eq_monomial] using h1
  conv_lhs => rw [hP]
  rw [Polynomial.sum_comp]
  simp_rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp]
  rw [Polynomial.finsetSum_coeff]
  simp_rw [coeff_C_mul]
  symm
  refine Finset.sum_subset (Finset.range_mono (le_max_right _ _)) ?_
  intro e _ he
  have hlt : k < e := by
    have : N + 1 ≤ e := by
      rw [Finset.mem_range] at he
      omega
    omega
  rw [coeff_pow_eq_zero_of_lt hu0 hlt, mul_zero]

private lemma polyEqMod_comp {N : ℕ} {P Q u : ℚ[X]} (hu0 : u.coeff 0 = 0)
    (h : PolyEqMod N P Q) : PolyEqMod N (P.comp u) (Q.comp u) := by
  intro k hk
  rw [coeff_comp_of_coeff_zero hu0 hk, coeff_comp_of_coeff_zero hu0 hk]
  refine Finset.sum_congr rfl ?_
  intro e he
  rw [h e (Nat.lt_succ_iff.mp (Finset.mem_range.mp he))]

private lemma polyEqMod_eq_one_of_sq {N : ℕ} {P : ℚ[X]} (hP0 : P.coeff 0 = 1)
    (hsq : PolyEqMod N (P ^ 2) 1) : PolyEqMod N P 1 := by
  have hU : (P + 1).coeff 0 ≠ 0 := by
    simp [coeff_add, hP0]
  refine polyEqMod_cancel_unit hU ?_
  have hmul : (P + 1) * P = P ^ 2 + P := by ring
  have h1 : (P + 1) * 1 = P + 1 := by ring
  rw [hmul, h1]
  have hsub : PolyEqMod N (P ^ 2 + P) (1 + P) := polyEqMod_add hsq (polyEqMod_refl N P)
  have hcomm : (1 : ℚ[X]) + P = P + 1 := add_comm 1 P
  rwa [hcomm] at hsub

private lemma polyEqMod_of_deriv_eq {N : ℕ} {P Q : ℚ[X]}
    (h0 : P.coeff 0 = Q.coeff 0)
    (hd : ∀ k < N, P.derivative.coeff k = Q.derivative.coeff k) :
    PolyEqMod N P Q := by
  intro k hk
  cases k with
  | zero => exact h0
  | succ k =>
    have hdk := hd k (by omega)
    rw [coeff_derivative, coeff_derivative] at hdk
    have hne : ((k : ℚ) + 1) ≠ 0 := by positivity
    exact mul_right_cancel₀ hne hdk

private noncomputable def invOneSubPowSucc (m N : ℕ) : ℚ[X] :=
  ∑ b ∈ Finset.range (N + 1), C (((m + b).choose b : ℕ) : ℚ) * X ^ b

private lemma coeff_invOneSubPowSucc (m N k : ℕ) (hk : k ≤ N) :
    (invOneSubPowSucc m N).coeff k = (((m + k).choose k : ℕ) : ℚ) := by
  unfold invOneSubPowSucc
  rw [Polynomial.finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (Finset.range (N + 1)) k]
  simp [Finset.mem_range.mpr (Nat.lt_succ_of_le hk)]

private lemma one_sub_X_mul_invOneSubPowSucc_zero (N : ℕ) :
    PolyEqMod N ((1 - X : ℚ[X]) * invOneSubPowSucc 0 N) 1 := by
  intro k hk
  rw [sub_mul, one_mul, coeff_sub, coeff_X_mul_nat]
  cases k with
  | zero =>
    simp [coeff_invOneSubPowSucc 0 N 0 (Nat.zero_le N)]
  | succ k =>
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    rw [coeff_invOneSubPowSucc 0 N (k + 1) hk, coeff_invOneSubPowSucc 0 N k (by omega)]
    simp [Nat.choose_self, Polynomial.coeff_one]

private lemma one_sub_X_mul_invOneSubPowSucc_succ (m N : ℕ) :
    PolyEqMod N ((1 - X : ℚ[X]) * invOneSubPowSucc (m + 1) N) (invOneSubPowSucc m N) := by
  intro k hk
  rw [sub_mul, one_mul, coeff_sub, coeff_X_mul_nat]
  cases k with
  | zero =>
    simp [coeff_invOneSubPowSucc _ N 0 (Nat.zero_le N)]
  | succ k =>
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    rw [coeff_invOneSubPowSucc (m + 1) N (k + 1) hk,
        coeff_invOneSubPowSucc (m + 1) N k (by omega),
        coeff_invOneSubPowSucc m N (k + 1) hk]
    have hp : (m + 1 + (k + 1)).choose (k + 1) = (m + 1 + k).choose k + (m + 1 + k).choose (k + 1) := by
      have heq : m + 1 + (k + 1) = (m + 1 + k) + 1 := by omega
      rw [heq, Nat.choose_succ_succ]
    have heq2 : m + 1 + k = m + (k + 1) := by omega
    rw [heq2] at hp
    have hpQ : (((m + 1 + (k + 1)).choose (k + 1) : ℕ) : ℚ) =
        (((m + (k + 1)).choose k : ℕ) : ℚ) + (((m + (k + 1)).choose (k + 1) : ℕ) : ℚ) := by
      exact_mod_cast hp
    rw [heq2]
    linarith

private lemma one_sub_X_pow_mul_invOneSubPowSucc (m N : ℕ) :
    PolyEqMod N ((1 - X : ℚ[X]) ^ (m + 1) * invOneSubPowSucc m N) 1 := by
  induction m with
  | zero => simpa using one_sub_X_mul_invOneSubPowSucc_zero N
  | succ m ih =>
    have hrew : (1 - X : ℚ[X]) ^ (m + 1 + 1) * invOneSubPowSucc (m + 1) N =
        (1 - X : ℚ[X]) ^ (m + 1) * ((1 - X : ℚ[X]) * invOneSubPowSucc (m + 1) N) := by ring
    rw [hrew]
    exact polyEqMod_trans
      (polyEqMod_mul (polyEqMod_refl N _) (one_sub_X_mul_invOneSubPowSucc_succ m N)) ih

private lemma polyEqMod_of_log_deriv_eq {M : ℕ} {P Q : ℚ[X]}
    (hP0 : P.coeff 0 = 1) (hQ0 : Q.coeff 0 = 1)
    (hd : ∀ k < M, (P.derivative * Q - P * Q.derivative).coeff k = 0) :
    PolyEqMod M P Q := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero => rw [hP0, hQ0]
    | succ k =>
      have hdk := hd k (by omega)
      rw [coeff_sub, coeff_mul, coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hdk
      rw [Finset.sum_range_succ] at hdk
      rw [Finset.sum_range_succ'] at hdk
      have hmid : (∑ i ∈ Finset.range k, P.derivative.coeff i * Q.coeff (k - i)) =
          ∑ i ∈ Finset.range k, P.coeff (i + 1) * Q.derivative.coeff (k - (i + 1)) := by
        refine Finset.sum_nbij (fun i => k - 1 - i) ?_ ?_ ?_ ?_
        · intro i hi
          have hik : i < k := Finset.mem_range.mp hi
          exact Finset.mem_range.mpr (by omega)
        · intro i1 hi1 i2 hi2 heq
          have h1 : i1 < k := Finset.mem_range.mp hi1
          have h2 : i2 < k := Finset.mem_range.mp hi2
          dsimp only at heq; omega
        · intro j hj
          have hjk : j < k := Finset.mem_range.mp hj
          exact ⟨k - 1 - j, Finset.mem_range.mpr (by omega), by dsimp; omega⟩
        · intro i hi
          have hik : i < k := Finset.mem_range.mp hi
          have h1 : k - 1 - i + 1 = k - i := by omega
          have h2 : k - (k - i) = i := by omega
          rw [h1, h2, coeff_derivative, coeff_derivative]
          rw [ih (i + 1) (by omega) (by omega), ih (k - i) (by omega) (by omega)]
          ring
      rw [hmid, Nat.sub_self, Nat.sub_zero, coeff_derivative, coeff_derivative, hP0, hQ0] at hdk
      have hdiff : ((k : ℚ) + 1) * (P.coeff (k + 1) - Q.coeff (k + 1)) = 0 := by linarith
      have hne : ((k : ℚ) + 1) ≠ 0 := by positivity
      have := (mul_eq_zero.mp hdiff).resolve_left hne
      linarith

private lemma coeff_comp_X_pow {p : ℕ} (hp : 1 ≤ p) (P : ℚ[X]) (k : ℕ) :
    (P.comp (X ^ p)).coeff k = if p ∣ k then P.coeff (k / p) else 0 := by
  have hu0 : (X ^ p : ℚ[X]).coeff 0 = 0 := by rw [coeff_X_pow, if_neg (by omega)]
  rw [coeff_comp_of_coeff_zero hu0 (N := k) le_rfl]
  have hpow : ∀ e : ℕ, ((X ^ p : ℚ[X]) ^ e).coeff k = if p * e = k then 1 else 0 := by
    intro e
    rw [← pow_mul, coeff_X_pow]
    by_cases h : p * e = k
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  simp_rw [hpow]
  by_cases hd : p ∣ k
  · rw [if_pos hd]
    rcases hd with ⟨q, rfl⟩
    have hq_le : q ≤ p * q := Nat.le_mul_of_pos_left q hp
    rw [Nat.mul_div_cancel_left q hp]
    rw [Finset.sum_eq_single q]
    · simp
    · intro e _ hne
      have : p * e ≠ p * q := fun h => hne (Nat.eq_of_mul_eq_mul_left hp h)
      simp [this]
    · intro hnot
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hq_le)) hnot
  · rw [if_neg hd]
    refine Finset.sum_eq_zero ?_
    intro e _
    have hne : p * e ≠ k := fun h => hd ⟨e, h.symm⟩
    simp [hne]

private lemma zmod_sum_units_inv_sq_eq_zero {p K : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    have : NeZero (p ^ K) := ⟨pow_ne_zero K hp.ne_zero⟩
    (∑ u : (ZMod (p ^ K))ˣ, (((u⁻¹ : (ZMod (p ^ K))ˣ) : ZMod (p ^ K)) ^ 2)) = 0 := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero K hp.ne_zero⟩
  have hcop2 : Nat.Coprime 2 (p ^ K) := (hp.coprime_iff_not_dvd.mpr (fun h => by
    have := Nat.le_of_dvd (by omega) h; omega)).symm.pow_right K
  have hcop3 : Nat.Coprime 3 (p ^ K) := (hp.coprime_iff_not_dvd.mpr (fun h => by
    have := Nat.le_of_dvd (by omega) h; omega)).symm.pow_right K
  set u2 : (ZMod (p ^ K))ˣ := ZMod.unitOfCoprime 2 hcop2
  set u3 : (ZMod (p ^ K))ˣ := ZMod.unitOfCoprime 3 hcop3
  set S : ZMod (p ^ K) := ∑ u : (ZMod (p ^ K))ˣ, (((u⁻¹ : (ZMod (p ^ K))ˣ) : ZMod (p ^ K)) ^ 2)
  have hshift : S = ∑ u : (ZMod (p ^ K))ˣ, ((((u2 * u)⁻¹ : (ZMod (p ^ K))ˣ) : ZMod (p ^ K)) ^ 2) :=
    (Equiv.sum_comp (Equiv.mulLeft u2) (fun u : (ZMod (p ^ K))ˣ => (((u⁻¹ : (ZMod (p ^ K))ˣ) : ZMod (p ^ K)) ^ 2))).symm
  have hS_eq : S = (((u2⁻¹ : (ZMod (p ^ K))ˣ) : ZMod (p ^ K)) ^ 2) * S := by
    calc S = ∑ u : (ZMod (p ^ K))ˣ, ((((u2 * u)⁻¹ : (ZMod (p ^ K))ˣ) : ZMod (p ^ K)) ^ 2) := hshift
      _ = ∑ u : (ZMod (p ^ K))ˣ, (((u2⁻¹ : (ZMod (p ^ K))ˣ) : ZMod (p ^ K)) ^ 2) *
            (((u⁻¹ : (ZMod (p ^ K))ˣ) : ZMod (p ^ K)) ^ 2) := by
            refine Finset.sum_congr rfl fun u _ => ?_
            rw [mul_inv_rev, Units.val_mul, mul_comm, mul_pow]
      _ = (((u2⁻¹ : (ZMod (p ^ K))ˣ) : ZMod (p ^ K)) ^ 2) * S := by rw [← Finset.mul_sum]
  have hu2_val : (u2 : ZMod (p ^ K)) = 2 := ZMod.coe_unitOfCoprime 2 hcop2
  have hu2_mul : (u2 : ZMod (p ^ K)) * ((u2⁻¹ : (ZMod (p ^ K))ˣ) : ZMod (p ^ K)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h4S : (4 : ZMod (p ^ K)) * S = S := by
    have h4 : (4 : ZMod (p ^ K)) = (u2 : ZMod (p ^ K)) ^ 2 := by
      rw [hu2_val]; norm_num
    calc (4 : ZMod (p ^ K)) * S
        = (u2 : ZMod (p ^ K)) ^ 2 * ((((u2⁻¹ : (ZMod (p ^ K))ˣ) : ZMod (p ^ K)) ^ 2) * S) := by rw [h4, ← hS_eq]
      _ = ((u2 : ZMod (p ^ K)) * ((u2⁻¹ : (ZMod (p ^ K))ˣ) : ZMod (p ^ K))) ^ 2 * S := by rw [← mul_assoc, ← mul_pow]
      _ = S := by rw [hu2_mul, one_pow, one_mul]
  have h3S : (3 : ZMod (p ^ K)) * S = 0 := by
    have : (3 : ZMod (p ^ K)) * S = (4 : ZMod (p ^ K)) * S - S := by ring
    rw [this, h4S, sub_self]
  have hu3_val : (u3 : ZMod (p ^ K)) = 3 := ZMod.coe_unitOfCoprime 3 hcop3
  have hu3_mul : ((u3⁻¹ : (ZMod (p ^ K))ˣ) : ZMod (p ^ K)) * (3 : ZMod (p ^ K)) = 1 := by
    rw [← hu3_val, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc S = 1 * S := (one_mul S).symm
    _ = ((u3⁻¹ : (ZMod (p ^ K))ˣ) : ZMod (p ^ K)) * ((3 : ZMod (p ^ K)) * S) := by
          rw [← mul_assoc, hu3_mul]
    _ = 0 := by rw [h3S, mul_zero]

private lemma isPDvdZ_sum_inv_sq_block {p K : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hK : 1 ≤ K) :
    IsPDvdZ p K (∑ u ∈ (Finset.Ico 1 (p ^ K)).filter (fun u => ¬ p ∣ u), (1 : ℚ) / ((u : ℚ) ^ 2)) := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero K hp.ne_zero⟩
  set s := (Finset.Ico 1 (p ^ K)).filter (fun u => ¬ p ∣ u)
  have hndvd : ∀ u ∈ s, ¬ p ∣ u ^ 2 := by
    intro u hu hd
    exact (Finset.mem_filter.mp hu).2 (hp.dvd_of_dvd_pow hd)
  set N : ℕ := ∑ u ∈ s, ∏ r ∈ s.erase u, r ^ 2
  set D : ℕ := ∏ u ∈ s, u ^ 2
  have hD_ndvd : ¬ p ∣ D := by
    intro hd
    rcases (hp.prime.dvd_finsetProd_iff _).mp hd with ⟨u, hu, hdu⟩
    exact hndvd u hu hdu
  have hD_ne : (D : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (fun h0 => hD_ndvd (h0 ▸ dvd_zero p))
  have hsum_eq : (∑ u ∈ s, (1 : ℚ) / ((u : ℚ) ^ 2)) = (N : ℚ) / (D : ℚ) := by
    rw [eq_div_iff hD_ne, Finset.sum_mul]
    dsimp [N]
    push_cast
    refine Finset.sum_congr rfl ?_
    intro u hu
    have hu_ne : (u : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by
      have := (Finset.mem_Ico.mp (Finset.mem_filter.mp hu).1).1; omega)
    have hD_split : (D : ℚ) = (u : ℚ) ^ 2 * ∏ r ∈ s.erase u, (r : ℚ) ^ 2 := by
      dsimp [D]
      rw [← Finset.mul_prod_erase s (fun r => r ^ 2) hu]
      push_cast; rfl
    rw [hD_split]
    field_simp
  have hN_dvd : p ^ K ∣ N := by
    rw [← ZMod.natCast_eq_zero_iff]
    have hD_cast : ∀ (u : (ZMod (p ^ K))ˣ), (u : ZMod (p ^ K)).val ∈ s →
        (∏ r ∈ s.erase (u : ZMod (p ^ K)).val, (r : ZMod (p ^ K)) ^ 2) =
        (D : ZMod (p ^ K)) * (((u⁻¹ : (ZMod (p ^ K))ˣ) : ZMod (p ^ K)) ^ 2) := by
      intro u hu
      have hu_mul : (u : ZMod (p ^ K)) * ((u⁻¹ : (ZMod (p ^ K))ˣ) : ZMod (p ^ K)) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hD_eq : (D : ZMod (p ^ K)) =
          ((u : ZMod (p ^ K)).val : ZMod (p ^ K)) ^ 2 *
            ∏ r ∈ s.erase (u : ZMod (p ^ K)).val, (r : ZMod (p ^ K)) ^ 2 := by
        dsimp [D]
        rw [← Finset.mul_prod_erase s (fun r => r ^ 2) hu]
        push_cast; rfl
      rw [ZMod.natCast_zmod_val] at hD_eq
      calc (∏ r ∈ s.erase (u : ZMod (p ^ K)).val, (r : ZMod (p ^ K)) ^ 2)
          = ((u : ZMod (p ^ K)) * ((u⁻¹ : (ZMod (p ^ K))ˣ) : ZMod (p ^ K))) ^ 2 *
              ∏ r ∈ s.erase (u : ZMod (p ^ K)).val, (r : ZMod (p ^ K)) ^ 2 := by
              rw [hu_mul, one_pow, one_mul]
        _ = ((u : ZMod (p ^ K)) ^ 2 * ∏ r ∈ s.erase (u : ZMod (p ^ K)).val, (r : ZMod (p ^ K)) ^ 2) *
              (((u⁻¹ : (ZMod (p ^ K))ˣ) : ZMod (p ^ K)) ^ 2) := by ring
        _ = (D : ZMod (p ^ K)) * (((u⁻¹ : (ZMod (p ^ K))ˣ) : ZMod (p ^ K)) ^ 2) := by rw [← hD_eq]
    have hN_cast : (N : ZMod (p ^ K)) =
        (D : ZMod (p ^ K)) * ∑ u : (ZMod (p ^ K))ˣ, (((u⁻¹ : (ZMod (p ^ K))ˣ) : ZMod (p ^ K)) ^ 2) := by
      dsimp [N]
      rw [Nat.cast_sum, Finset.mul_sum]
      symm
      refine Finset.sum_nbij (fun u : (ZMod (p ^ K))ˣ => (u : ZMod (p ^ K)).val) ?_ ?_ ?_ ?_
      · intro u _
        have hlt : (u : ZMod (p ^ K)).val < p ^ K := ZMod.val_lt _
        have hcop : Nat.Coprime (u : ZMod (p ^ K)).val (p ^ K) := by
          have hunit : IsUnit ((u : ZMod (p ^ K)).val : ZMod (p ^ K)) := by
            rw [ZMod.natCast_zmod_val]; exact u.isUnit
          exact (ZMod.isUnit_iff_coprime _ _).mp hunit
        have hnd : ¬ p ∣ (u : ZMod (p ^ K)).val := by
          intro hd
          have hp_dvd_pk : p ∣ p ^ K := dvd_pow_self p (by omega)
          exact hp.not_dvd_one (hcop ▸ Nat.dvd_gcd hd hp_dvd_pk)
        have hpos : 1 ≤ (u : ZMod (p ^ K)).val := by
          by_contra h0; push Not at h0
          have hv0 : (u : ZMod (p ^ K)).val = 0 := by omega
          exact hnd (hv0 ▸ dvd_zero p)
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hpos, hlt⟩, hnd⟩
      · intro u1 _ u2 _ heq
        ext
        exact ZMod.val_injective (p ^ K) heq
      · intro a ha
        rcases Finset.mem_filter.mp ha with ⟨hIco, hnd⟩
        rcases Finset.mem_Ico.mp hIco with ⟨_, halt⟩
        have hcop : Nat.Coprime a (p ^ K) :=
          (hp.coprime_iff_not_dvd.mpr hnd).symm.pow_right K
        refine ⟨ZMod.unitOfCoprime a hcop, Finset.mem_univ _, ?_⟩
        dsimp only
        rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt halt]
      · intro u _
        have hmem : (u : ZMod (p ^ K)).val ∈ s := by
          have hlt : (u : ZMod (p ^ K)).val < p ^ K := ZMod.val_lt _
          have hcop : Nat.Coprime (u : ZMod (p ^ K)).val (p ^ K) := by
            have hunit : IsUnit ((u : ZMod (p ^ K)).val : ZMod (p ^ K)) := by
              rw [ZMod.natCast_zmod_val]; exact u.isUnit
            exact (ZMod.isUnit_iff_coprime _ _).mp hunit
          have hnd : ¬ p ∣ (u : ZMod (p ^ K)).val := by
            intro hd
            have hp_dvd_pk : p ∣ p ^ K := dvd_pow_self p (by omega)
            exact hp.not_dvd_one (hcop ▸ Nat.dvd_gcd hd hp_dvd_pk)
          have hpos : 1 ≤ (u : ZMod (p ^ K)).val := by
            by_contra h0; push Not at h0
            have hv0 : (u : ZMod (p ^ K)).val = 0 := by omega
            exact hnd (hv0 ▸ dvd_zero p)
          exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hpos, hlt⟩, hnd⟩
        push_cast
        exact (hD_cast u hmem).symm
    rw [hN_cast, zmod_sum_units_inv_sq_eq_zero hp hp5, mul_zero]
  exact ⟨(N : ℤ), (D : ℤ), fun h => hD_ndvd (Int.ofNat_dvd.mp h), Int.ofNat_dvd.mpr hN_dvd, by push_cast; exact hsum_eq⟩

private lemma isPDvdZ_sum_inv_pair {p j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (_hj : 1 ≤ j) :
    IsPDvdZ p (1 + padicValNat p j)
      (∑ d ∈ (Finset.Ico 1 (p * j)).filter (fun d => ¬ p ∣ d),
        (1 : ℚ) / ((d : ℚ) * ((p * j - d : ℕ) : ℚ))) := by
  have : Fact p.Prime := ⟨hp⟩
  set K := 1 + padicValNat p j
  have hK1 : 1 ≤ K := by omega
  have hpK_dvd : p ^ K ∣ p * j := by
    have h1 : p ^ padicValNat p j ∣ j := pow_padicValNat_dvd
    have h2 : p ^ K = p * p ^ padicValNat p j := by
      dsimp [K]; rw [add_comm, pow_succ, mul_comm]
    rw [h2]
    exact Nat.mul_dvd_mul_left p h1
  set S := (Finset.Ico 1 (p * j)).filter (fun d => ¬ p ∣ d)
  have hdiff : IsPDvdZ p K (∑ d ∈ S, ((1 : ℚ) / ((d : ℚ) * ((p * j - d : ℕ) : ℚ)) + (1 : ℚ) / ((d : ℚ) ^ 2))) := by
    refine isPDvdZ_sum hp S _ ?_
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hIco, hnd⟩
    rcases Finset.mem_Ico.mp hIco with ⟨hd1, hdpj⟩
    have hnd_sub : ¬ p ∣ (p * j - d) := by
      intro hsub
      have hadd : (p * j - d) + d = p * j := Nat.sub_add_cancel (le_of_lt hdpj)
      exact hnd ((Nat.dvd_add_right hsub).mp (hadd.symm ▸ dvd_mul_right p j))
    have hdenom_ndvd : ¬ p ∣ (d ^ 2 * (p * j - d)) := by
      intro hdvd
      rcases hp.dvd_mul.mp hdvd with h1 | h2
      · exact hnd (hp.dvd_of_dvd_pow h1)
      · exact hnd_sub h2
    have hrew : (1 : ℚ) / ((d : ℚ) * ((p * j - d : ℕ) : ℚ)) + (1 : ℚ) / ((d : ℚ) ^ 2) =
        ((p * j : ℕ) : ℚ) / (((d ^ 2 * (p * j - d) : ℕ) : ℚ)) := by
      have hd_ne : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hsub_ne : ((p * j - d : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hden : (((d ^ 2 * (p * j - d) : ℕ) : ℚ)) = (d : ℚ) ^ 2 * ((p * j - d : ℕ) : ℚ) := by
        push_cast; rfl
      have hcast : ((p * j - d : ℕ) : ℚ) = ((p * j : ℕ) : ℚ) - (d : ℚ) := by
        rw [Nat.cast_sub (le_of_lt hdpj)]
      rw [hden]
      rw [hcast] at hsub_ne ⊢
      field_simp
      ring
    rw [hrew]
    exact isPDvdZ_div_coprime_nat hp hdenom_ndvd (isPDvdZ_natCast hp (p * j) hpK_dvd)
  have hsq : IsPDvdZ p K (∑ d ∈ S, (1 : ℚ) / ((d : ℚ) ^ 2)) := by
    rcases hpK_dvd with ⟨m, hm⟩
    have hblock_shift : ∀ b : ℕ,
        IsPDvdZ p K (∑ u ∈ (Finset.Ico 1 (p ^ K)).filter (fun u => ¬ p ∣ u),
          (1 : ℚ) / (((b * p ^ K + u : ℕ) : ℚ) ^ 2)) := by
      intro b
      set U := (Finset.Ico 1 (p ^ K)).filter (fun u => ¬ p ∣ u)
      have h0 := isPDvdZ_sum_inv_sq_block hp hp5 hK1
      have hshift_diff : IsPDvdZ p K (∑ u ∈ U,
          ((1 : ℚ) / (((b * p ^ K + u : ℕ) : ℚ) ^ 2) - (1 : ℚ) / ((u : ℚ) ^ 2))) := by
        refine isPDvdZ_sum hp U _ ?_
        intro u hu
        rcases Finset.mem_filter.mp hu with ⟨hIco, hnd⟩
        rcases Finset.mem_Ico.mp hIco with ⟨hu1, _⟩
        have hnd_sh : ¬ p ∣ (b * p ^ K + u) := by
          intro hsh
          have hp_pk : p ∣ b * p ^ K := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) b
          exact hnd ((Nat.dvd_add_right hp_pk).mp hsh)
        have hden_ndvd : ¬ p ∣ ((b * p ^ K + u) ^ 2 * u ^ 2) := by
          intro hdvd
          rcases hp.dvd_mul.mp hdvd with h1 | h2
          · exact hnd_sh (hp.dvd_of_dvd_pow h1)
          · exact hnd (hp.dvd_of_dvd_pow h2)
        have hnum_dvd : ((p ^ K : ℕ) : ℤ) ∣
            ((u : ℤ) ^ 2 - ((b * p ^ K + u : ℕ) : ℤ) ^ 2) := by
          refine ⟨-(b : ℤ) * ((b : ℤ) * ((p ^ K : ℕ) : ℤ) + 2 * (u : ℤ)), ?_⟩
          push_cast; ring
        have hrew : (1 : ℚ) / (((b * p ^ K + u : ℕ) : ℚ) ^ 2) - (1 : ℚ) / ((u : ℚ) ^ 2) =
            ((((u : ℤ) ^ 2 - ((b * p ^ K + u : ℕ) : ℤ) ^ 2 : ℤ) : ℚ)) /
              ((((b * p ^ K + u) ^ 2 * u ^ 2 : ℕ) : ℚ)) := by
          have hu_ne : (u : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          have hsh_ne : ((b * p ^ K + u : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          push_cast
          field_simp
        rw [hrew]
        exact isPDvdZ_div_coprime_nat hp hden_ndvd (isPDvdZ_intCast hp _ hnum_dvd)
      have hcomb := isPDvdZ_add hp hshift_diff h0
      rw [← Finset.sum_add_distrib] at hcomb
      simpa using hcomb
    have hsplit_S : (∑ d ∈ S, (1 : ℚ) / ((d : ℚ) ^ 2)) =
        ∑ b ∈ Finset.range m,
          ∑ u ∈ (Finset.Ico 1 (p ^ K)).filter (fun u => ¬ p ∣ u),
            (1 : ℚ) / (((b * p ^ K + u : ℕ) : ℚ) ^ 2) := by
      have hpK_pos : 0 < p ^ K := pow_pos hp.pos K
      rw [Finset.sum_sigma']
      symm
      refine Finset.sum_nbij (fun x : Σ _ : ℕ, ℕ => x.1 * p ^ K + x.2) ?_ ?_ ?_ ?_
      · intro x hx
        rcases Finset.mem_sigma.mp hx with ⟨hb, hu⟩
        have hbm : x.1 < m := Finset.mem_range.mp hb
        rcases Finset.mem_filter.mp hu with ⟨hIco, hnd⟩
        rcases Finset.mem_Ico.mp hIco with ⟨hu1, hult⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, ?_⟩, ?_⟩
        · have hle : x.1 * p ^ K + p ^ K ≤ m * p ^ K := by
            have : (x.1 + 1) * p ^ K ≤ m * p ^ K := Nat.mul_le_mul_right (p ^ K) (by omega)
            linarith
          have : m * p ^ K = p * j := by linarith [hm, mul_comm m (p ^ K)]
          omega
        · intro hd
          have hp_pk : p ∣ x.1 * p ^ K := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) x.1
          exact hnd ((Nat.dvd_add_right hp_pk).mp hd)
      · intro x1 hx1 x2 hx2 heq
        dsimp only at heq
        rcases Finset.mem_filter.mp (Finset.mem_sigma.mp hx1).2 with ⟨hIco1, _⟩
        rcases Finset.mem_filter.mp (Finset.mem_sigma.mp hx2).2 with ⟨hIco2, _⟩
        have hu1 : x1.2 < p ^ K := (Finset.mem_Ico.mp hIco1).2
        have hu2 : x2.2 < p ^ K := (Finset.mem_Ico.mp hIco2).2
        have hq : x1.1 = x2.1 := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have : (x1.1 + 1) * p ^ K ≤ x2.1 * p ^ K := Nat.mul_le_mul_right (p ^ K) (by omega)
            nlinarith
          · have : (x2.1 + 1) * p ^ K ≤ x1.1 * p ^ K := Nat.mul_le_mul_right (p ^ K) (by omega)
            nlinarith
        have hr : x1.2 = x2.2 := by rw [hq] at heq; omega
        cases x1; cases x2; simp only at hq hr; subst hq; subst hr; rfl
      · intro d hd
        rcases Finset.mem_filter.mp hd with ⟨hIco, hnd⟩
        rcases Finset.mem_Ico.mp hIco with ⟨hd1, hdpj⟩
        set b := d / p ^ K
        set u := d % p ^ K
        have hbu : b * p ^ K + u = d := by
          dsimp [b, u]
          rw [mul_comm]
          exact Nat.div_add_mod d (p ^ K)
        have hult : u < p ^ K := Nat.mod_lt d hpK_pos
        have hbm : b < m := by
          dsimp [b]
          exact (Nat.div_lt_iff_lt_mul hpK_pos).mpr (by rw [mul_comm, ← hm]; exact hdpj)
        have hnd_u : ¬ p ∣ u := by
          intro hdu
          have hp_pk : p ∣ b * p ^ K := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) b
          exact hnd (hbu ▸ dvd_add hp_pk hdu)
        have hu1 : 1 ≤ u := by
          by_contra h0
          have hu0 : u = 0 := Nat.lt_one_iff.mp (Nat.not_le.mp h0)
          exact hnd_u (hu0 ▸ dvd_zero p)
        exact ⟨⟨b, u⟩, Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr hbm,
          Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hu1, hult⟩, hnd_u⟩⟩, hbu⟩
      · intro _ _; rfl
    rw [hsplit_S]
    exact isPDvdZ_sum hp (Finset.range m) _ fun b _ => hblock_shift b
  have hsub := isPDvdZ_sub hp hdiff hsq
  rw [← Finset.sum_sub_distrib] at hsub
  simpa using hsub

private lemma padicValNat_negChoose_ge_sub {p B b : ℕ} (hp : p.Prime) (hB : 1 ≤ B) (hb : 1 ≤ b) :
    padicValNat p B - padicValNat p b ≤ padicValNat p ((B - 1 + b).choose b) := by
  have : Fact p.Prime := ⟨hp⟩
  have hid : b * (B - 1 + b).choose b = B * (B - 1 + b).choose (b - 1) := by
    have hfac1 := Nat.choose_mul_factorial_mul_factorial (show b ≤ B - 1 + b by omega)
    have hfac2 := Nat.choose_mul_factorial_mul_factorial (show b - 1 ≤ B - 1 + b by omega)
    have hsub1 : B - 1 + b - b = B - 1 := by omega
    have hsub2 : B - 1 + b - (b - 1) = B := by omega
    rw [hsub1] at hfac1
    rw [hsub2] at hfac2
    have hfb : b.factorial = b * (b - 1).factorial := (Nat.mul_factorial_pred (by omega)).symm
    have hfB : B.factorial = B * (B - 1).factorial := (Nat.mul_factorial_pred (by omega)).symm
    have hpos : 0 < (b - 1).factorial * (B - 1).factorial :=
      mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
    have heq : b * (B - 1 + b).choose b * ((b - 1).factorial * (B - 1).factorial) =
        B * (B - 1 + b).choose (b - 1) * ((b - 1).factorial * (B - 1).factorial) := by
      calc b * (B - 1 + b).choose b * ((b - 1).factorial * (B - 1).factorial)
          = (B - 1 + b).choose b * (b * (b - 1).factorial) * (B - 1).factorial := by ring
        _ = (B - 1 + b).choose b * b.factorial * (B - 1).factorial := by rw [← hfb]
        _ = (B - 1 + b).factorial := hfac1
        _ = (B - 1 + b).choose (b - 1) * (b - 1).factorial * B.factorial := hfac2.symm
        _ = (B - 1 + b).choose (b - 1) * (b - 1).factorial * (B * (B - 1).factorial) := by rw [hfB]
        _ = B * (B - 1 + b).choose (b - 1) * ((b - 1).factorial * (B - 1).factorial) := by ring
    exact Nat.eq_of_mul_eq_mul_right hpos heq
  have hch1 : (B - 1 + b).choose b ≠ 0 := Nat.ne_of_gt (Nat.choose_pos (by omega))
  have hch2 : (B - 1 + b).choose (b - 1) ≠ 0 := Nat.ne_of_gt (Nat.choose_pos (by omega))
  have hv := congr_arg (padicValNat p) hid
  rw [padicValNat.mul (by omega) hch1, padicValNat.mul (by omega) hch2] at hv
  omega


/-! ### Section 2: Cardinality of `antidiagonalTuple` and generating polynomial for A351856 -/

private lemma hockey_stick (k m : ℕ) :
    ∑ b ∈ Finset.range (m + 1), (k + b).choose b = (k + 1 + m).choose m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : k + 1 + (m + 1) = (k + 1 + m) + 1 := by omega
    have h2 : k + (m + 1) = k + 1 + m := by omega
    rw [h1, h2, Nat.choose_succ_succ]

private lemma card_antidiagonalTuple_eq (k m : ℕ) :
    (Finset.Nat.antidiagonalTuple (k + 1) m).card = (k + m).choose m := by
  induction k generalizing m with
  | zero =>
    rw [Finset.Nat.antidiagonalTuple_one, Finset.card_singleton, Nat.zero_add, Nat.choose_self]
  | succ k ih =>
    have hbij : (Finset.Nat.antidiagonalTuple (k + 2) m).card =
        ((Finset.range (m + 1)).sigma (fun a => Finset.Nat.antidiagonalTuple (k + 1) (m - a))).card := by
      symm
      refine Finset.card_bij (fun x _ => Fin.cons x.1 x.2) ?_ ?_ ?_
      · intro x hx
        rcases Finset.mem_sigma.mp hx with ⟨ha, hf⟩
        have ham : x.1 ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        have hsum : ∑ i, x.2 i = m - x.1 := Finset.Nat.mem_antidiagonalTuple.mp hf
        rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ, hsum]
        omega
      · intro x1 _ x2 _ heq
        have h0 : x1.1 = x2.1 := by
          have := congr_fun heq 0
          simpa using this
        have ht : x1.2 = x2.2 := by
          have := congr_arg Fin.tail heq
          simpa using this
        cases x1; cases x2; simp only at h0 ht; subst h0; subst ht; rfl
      · intro f hf
        have hsum : ∑ i, f i = m := Finset.Nat.mem_antidiagonalTuple.mp hf
        rw [Fin.sum_univ_succ] at hsum
        have hf0 : f 0 ≤ m := by omega
        have htail : Fin.tail f ∈ Finset.Nat.antidiagonalTuple (k + 1) (m - f 0) := by
          rw [Finset.Nat.mem_antidiagonalTuple]
          have : ∑ i, Fin.tail f i = ∑ i : Fin (k + 1), f i.succ := rfl
          omega
        refine ⟨⟨f 0, Fin.tail f⟩, Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hf0), htail⟩, ?_⟩
        exact Fin.cons_self_tail f
    rw [hbij, Finset.card_sigma]
    simp_rw [ih]
    have hrefl : ∑ a ∈ Finset.range (m + 1), (k + (m - a)).choose (m - a) =
        ∑ b ∈ Finset.range (m + 1), (k + b).choose b := by
      refine Finset.sum_nbij (fun a => m - a) ?_ ?_ ?_ ?_
      · intro a ha
        have ham : a ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        exact Finset.mem_range.mpr (by omega)
      · intro a1 ha1 a2 ha2 heq
        have h1 : a1 ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha1)
        have h2 : a2 ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha2)
        dsimp only at heq; omega
      · intro b hb
        have hbm : b ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
        exact ⟨m - b, Finset.mem_range.mpr (by omega), by dsimp; omega⟩
      · intro _ _; rfl
    rw [hrefl, hockey_stick]

private def cCoeff (n m : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (m / 2 + 1), (n - 1 + (m - 2 * j)).choose (m - 2 * j) * (n - 1 + j).choose j

private noncomputable def cPoly (n M : ℕ) : ℚ[X] :=
  invOneSubPowSucc (n - 1) M * (invOneSubPowSucc (n - 1) M).comp (X ^ 2)

private lemma coeff_cPoly {n M m : ℕ} (hm : m ≤ M) :
    (cPoly n M).coeff m = (cCoeff n m : ℚ) := by
  unfold cPoly cCoeff
  rw [mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  push_cast
  have hfilt : (∑ x ∈ Finset.range (m + 1),
      ((invOneSubPowSucc (n - 1) M).comp (X ^ 2)).coeff x * (invOneSubPowSucc (n - 1) M).coeff (m - x)) =
      ∑ x ∈ (Finset.range (m + 1)).filter (fun x => 2 ∣ x),
        ((invOneSubPowSucc (n - 1) M).comp (X ^ 2)).coeff x * (invOneSubPowSucc (n - 1) M).coeff (m - x) := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro x hx hnot
    have hnd : ¬ 2 ∣ x := fun hd => hnot (Finset.mem_filter.mpr ⟨hx, hd⟩)
    rw [coeff_comp_X_pow (by omega : 1 ≤ 2), if_neg hnd, zero_mul]
  rw [hfilt]
  symm
  refine Finset.sum_nbij (fun j => 2 * j) ?_ ?_ ?_ ?_
  · intro j hj
    have hjm : j ≤ m / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), dvd_mul_right 2 j⟩
  · intro j1 _ j2 _ heq; dsimp only at heq; omega
  · intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxr, hd⟩
    rcases hd with ⟨j, rfl⟩
    have hxm : 2 * j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hxr)
    exact ⟨j, Finset.mem_range.mpr (by omega), rfl⟩
  · intro j hj
    have hjm : j ≤ m / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [coeff_comp_X_pow (by omega : 1 ≤ 2), if_pos (dvd_mul_right 2 j),
        Nat.mul_div_cancel_left j (by omega : 0 < 2),
        coeff_invOneSubPowSucc (n - 1) M j (by omega),
        coeff_invOneSubPowSucc (n - 1) M (m - 2 * j) (by omega), mul_comm]

private lemma a_eq_cCoeff {n : ℕ} (hn : 1 ≤ n) :
    OMA.S_oeis_a351856.a n = (cCoeff n (2 * n) : ℤ) := by
  unfold OMA.S_oeis_a351856.a cCoeff
  have hdiv : 2 * n / 2 = n := Nat.mul_div_cancel_left n (by omega)
  rw [hdiv]
  push_cast
  refine Finset.sum_congr rfl ?_
  intro j _
  have hn1 : n = (n - 1) + 1 := by omega
  conv_lhs => rw [hn1]
  rw [card_antidiagonalTuple_eq, card_antidiagonalTuple_eq, ← hn1]

/-! ### Section 3: p-adic Exponential Factorization for `cPoly` -/

private def gVal (d : ℕ) : ℚ :=
  if d % 2 = 1 then 1 else 3

private lemma gVal_mul_odd {p : ℕ} (hp_odd : p % 2 = 1) (d : ℕ) :
    gVal (p * d) = gVal d := by
  unfold gVal
  have hmod : (p * d) % 2 = d % 2 := by
    rw [Nat.mul_mod, hp_odd, one_mul, Nat.mod_mod]
  rw [hmod]

private noncomputable def GPoly (M : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range M, C (gVal (k + 1)) * X ^ k

private noncomputable def GPolyP (p M : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (M / p), C (gVal (k + 1)) * X ^ (p * (k + 1) - 1)

private noncomputable def LExp (p M : ℕ) : ℚ[X] :=
  ∑ d ∈ (Finset.Icc 1 M).filter (fun d => ¬ p ∣ d), C (gVal d / (d : ℚ)) * X ^ d

private noncomputable def EExp (p n M : ℕ) : ℚ[X] :=
  ∑ m ∈ Finset.range (M + 1), C (((n * p : ℕ) : ℚ) ^ m / (m.factorial : ℚ)) * (LExp p M) ^ m

private lemma coeff_GPoly (M k : ℕ) :
    (GPoly M).coeff k = if k < M then gVal (k + 1) else 0 := by
  unfold GPoly
  rw [Polynomial.finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (Finset.range M) k]
  simp [Finset.mem_range]

private lemma coeff_GPolyP {p M k : ℕ} (hp : 1 ≤ p) :
    (GPolyP p M).coeff k = if p ∣ (k + 1) ∧ k < M then gVal ((k + 1) / p) else 0 := by
  unfold GPolyP
  rw [Polynomial.finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  by_cases hcond : p ∣ (k + 1) ∧ k < M
  · rcases hcond with ⟨hdvd, hkM⟩
    rw [if_pos ⟨hdvd, hkM⟩]
    rcases hdvd with ⟨q, hq⟩
    have hq1 : 1 ≤ q := by
      by_contra h0; push Not at h0; interval_cases q; omega
    have hq_mem : q - 1 ∈ Finset.range (M / p) := by
      rw [Finset.mem_range]
      have hle : p * q ≤ M := by omega
      have hdiv : q ≤ M / p := (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact hle)
      omega
    have hq_div : (k + 1) / p = q := by
      rw [hq, Nat.mul_div_cancel_left q (by omega)]
    rw [Finset.sum_eq_single (q - 1)]
    · have heq : p * (q - 1 + 1) - 1 = k := by
        have : q - 1 + 1 = q := by omega
        rw [this]; omega
      rw [if_pos heq.symm, show q - 1 + 1 = q by omega, hq_div]
    · intro b _ hne
      have hne' : k ≠ p * (b + 1) - 1 := by
        intro heq
        have h1 : k + 1 = p * (b + 1) := by
          have : 1 ≤ p * (b + 1) := Nat.mul_pos hp (Nat.succ_pos b)
          omega
        have : q = b + 1 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < p) (hq.symm.trans h1)
        exact hne (by omega)
      rw [if_neg hne']
    · intro hnot; exact absurd hq_mem hnot
  · rw [if_neg hcond]
    refine Finset.sum_eq_zero ?_
    intro b hb
    have hb_lt : b < M / p := Finset.mem_range.mp hb
    have hne : k ≠ p * (b + 1) - 1 := by
      intro heq
      have h1 : k + 1 = p * (b + 1) := by
        have : 1 ≤ p * (b + 1) := Nat.mul_pos hp (Nat.succ_pos b)
        omega
      have hle : p * (b + 1) ≤ M := by
        have := Nat.mul_le_mul_left p (show b + 1 ≤ M / p by omega)
        exact le_trans this (Nat.mul_div_le M p)
      exact hcond ⟨⟨b + 1, h1⟩, by omega⟩
    rw [if_neg hne]

private lemma LExp_coeff_zero (p M : ℕ) : (LExp p M).coeff 0 = 0 := by
  unfold LExp
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero ?_
  intro d hd
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
  rw [coeff_C_mul_X_pow, if_neg (by omega)]

private lemma LExp_deriv_eq {p : ℕ} (hp : p.Prime) (hp_odd : p % 2 = 1) (M : ℕ) :
    (LExp p M).derivative = GPoly M - GPolyP p M := by
  ext k
  have hL : (LExp p M).derivative.coeff k =
      if ¬ p ∣ (k + 1) ∧ k < M then gVal (k + 1) else 0 := by
    unfold LExp
    rw [coeff_derivative, Polynomial.finsetSum_coeff]
    simp_rw [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq ((Finset.Icc 1 M).filter (fun d => ¬ p ∣ d)) (k + 1)]
    by_cases hcond : ¬ p ∣ (k + 1) ∧ k < M
    · have hmem : k + 1 ∈ (Finset.Icc 1 M).filter (fun d => ¬ p ∣ d) :=
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hcond.1⟩
      rw [if_pos hmem, if_pos hcond]
      have hne : ((k : ℚ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
    · have hnot : k + 1 ∉ (Finset.Icc 1 M).filter (fun d => ¬ p ∣ d) := by
        intro hm
        rcases Finset.mem_filter.mp hm with ⟨hI, hnd⟩
        exact hcond ⟨hnd, by have := (Finset.mem_Icc.mp hI).2; omega⟩
      rw [if_neg hnot, if_neg hcond, zero_mul]
  rw [hL, coeff_sub, coeff_GPoly, coeff_GPolyP hp.one_le]
  by_cases hk : k < M
  · by_cases hdvd : p ∣ (k + 1)
    · rw [if_neg (by tauto), if_pos hk, if_pos ⟨hdvd, hk⟩]
      rcases hdvd with ⟨q, hq⟩
      rw [hq, Nat.mul_div_cancel_left q hp.pos, gVal_mul_odd hp_odd q, sub_self]
    · rw [if_pos ⟨hdvd, hk⟩, if_pos hk, if_neg (by tauto), sub_zero]
  · rw [if_neg (by tauto), if_neg hk, if_neg (by tauto), sub_zero]

private lemma one_sub_X_sq_mul_GPoly (M : ℕ) :
    ∀ k < M, ((1 - X ^ 2 : ℚ[X]) * GPoly M).coeff k = (1 + C (3 : ℚ) * X).coeff k := by
  intro k hk
  rw [sub_mul, one_mul, coeff_sub, coeff_X_pow_mul', coeff_add, coeff_one, coeff_C_mul, coeff_X]
  rcases k with _ | _ | k
  · simp [coeff_GPoly M 0, hk, gVal]
  · simp [coeff_GPoly M 1, hk, gVal]
  · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      show 2 ≤ k + 2 by omega, show (1 : ℕ) ≠ k + 1 + 1 by omega, mul_zero, add_zero]
    rw [coeff_GPoly M (k + 2), coeff_GPoly M (k + 2 - 2), if_pos hk, if_pos (by omega)]
    unfold gVal
    have hmod : (k + 2 + 1) % 2 = (k + 2 - 2 + 1) % 2 := by omega
    rw [hmod, sub_self]

private lemma one_sub_X_two_p_mul_GPolyP {p : ℕ} (hp : 1 ≤ p) (M : ℕ) :
    ∀ k < M, ((1 - X ^ (2 * p) : ℚ[X]) * GPolyP p M).coeff k =
      (X ^ (p - 1) * (1 + C (3 : ℚ) * X ^ p)).coeff k := by
  intro k hk
  rw [sub_mul, one_mul, coeff_sub, coeff_X_pow_mul']
  have hRHS : (X ^ (p - 1) * (1 + C (3 : ℚ) * X ^ p)).coeff k =
      (if k = p - 1 then (1 : ℚ) else 0) + (if k = 2 * p - 1 then (3 : ℚ) else 0) := by
    have hrew : X ^ (p - 1) * (1 + C (3 : ℚ) * X ^ p) =
        C (1 : ℚ) * X ^ (p - 1) + C (3 : ℚ) * X ^ (2 * p - 1) := by
      have hexp : p - 1 + p = 2 * p - 1 := by omega
      calc X ^ (p - 1) * (1 + C (3 : ℚ) * X ^ p)
          = C (1 : ℚ) * X ^ (p - 1) + C (3 : ℚ) * (X ^ (p - 1) * X ^ p) := by simp [map_one]; ring
        _ = C (1 : ℚ) * X ^ (p - 1) + C (3 : ℚ) * X ^ (2 * p - 1) := by rw [← pow_add, hexp]
    rw [hrew, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
  rw [hRHS, coeff_GPolyP hp]
  by_cases hk2p : 2 * p ≤ k
  · rw [if_pos hk2p, coeff_GPolyP hp]
    have hne1 : k ≠ p - 1 := by omega
    have hne2 : k ≠ 2 * p - 1 := by omega
    rw [if_neg hne1, if_neg hne2, add_zero]
    have hdvd_iff : p ∣ (k - 2 * p + 1) ↔ p ∣ (k + 1) := by
      have heq : k + 1 = (k - 2 * p + 1) + 2 * p := by omega
      rw [heq]
      exact (Nat.dvd_add_left (dvd_mul_left p 2)).symm
    by_cases hd : p ∣ (k + 1)
    · have hd' : p ∣ (k - 2 * p + 1) := hdvd_iff.mpr hd
      rw [if_pos ⟨hd, hk⟩, if_pos ⟨hd', by omega⟩]
      have hdiv : (k + 1) / p = (k - 2 * p + 1) / p + 2 := by
        have heq : k + 1 = (k - 2 * p + 1) + 2 * p := by omega
        rw [heq, Nat.add_mul_div_right _ _ (by omega)]
      rw [hdiv]
      unfold gVal
      have hmod : ((k - 2 * p + 1) / p + 2) % 2 = ((k - 2 * p + 1) / p) % 2 := by omega
      rw [hmod, sub_self]
    · have hd' : ¬ p ∣ (k - 2 * p + 1) := fun h => hd (hdvd_iff.mp h)
      rw [if_neg (by tauto), if_neg (by tauto), sub_self]
  · rw [if_neg hk2p, sub_zero]
    by_cases h1 : k = p - 1
    · subst h1
      have hne : p - 1 ≠ 2 * p - 1 := by omega
      rw [if_pos rfl, if_neg hne, add_zero]
      have hadd : p - 1 + 1 = p := by omega
      rw [hadd, if_pos ⟨dvd_rfl, hk⟩, Nat.div_self (by omega)]
      simp [gVal]
    · by_cases h2 : k = 2 * p - 1
      · subst h2
        rw [if_neg h1, if_pos rfl, zero_add]
        have hadd : 2 * p - 1 + 1 = 2 * p := by omega
        rw [hadd, if_pos ⟨dvd_mul_left p 2, hk⟩, Nat.mul_div_cancel _ (by omega)]
        simp [gVal]
      · rw [if_neg h1, if_neg h2, add_zero]
        have hnd : ¬ p ∣ (k + 1) := by
          intro hd
          rcases hd with ⟨q, hq⟩
          have hq2 : q ≤ 2 := by nlinarith
          interval_cases q <;> omega
        rw [if_neg (by tauto)]

private lemma EExp_deriv_eq (p n M : ℕ) :
    ∀ k < M, ((EExp p n M).derivative - C ((n * p : ℕ) : ℚ) * (LExp p M).derivative * EExp p n M).coeff k = 0 := by
  intro k hk
  have hd : (EExp p n M).derivative =
      C ((n * p : ℕ) : ℚ) * (LExp p M).derivative *
        (EExp p n M - C (((n * p : ℕ) : ℚ) ^ M / (M.factorial : ℚ)) * (LExp p M) ^ M) := by
    unfold EExp
    conv_rhs => rw [Finset.sum_range_succ, add_sub_cancel_right]
    rw [Polynomial.derivative_sum]
    have hsplit : (∑ m ∈ Finset.range (M + 1),
        (C (((n * p : ℕ) : ℚ) ^ m / (m.factorial : ℚ)) * (LExp p M) ^ m).derivative) =
        ∑ m ∈ Finset.range M,
          C ((n * p : ℕ) : ℚ) * (LExp p M).derivative *
            (C (((n * p : ℕ) : ℚ) ^ m / (m.factorial : ℚ)) * (LExp p M) ^ m) := by
      rw [Finset.sum_range_succ']
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, map_one, mul_one,
        Polynomial.derivative_one, add_zero]
      refine Finset.sum_congr rfl ?_
      intro m _
      rw [Polynomial.derivative_C_mul, Polynomial.derivative_pow]
      have hfac : (((m + 1).factorial : ℕ) : ℚ) = ((m + 1 : ℕ) : ℚ) * (m.factorial : ℚ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hne : ((m + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      have hcoef : C (((n * p : ℕ) : ℚ) ^ (m + 1) / (((m + 1).factorial : ℕ) : ℚ)) * ((m + 1 : ℕ) : ℚ[X]) =
          C ((n * p : ℕ) : ℚ) * C (((n * p : ℕ) : ℚ) ^ m / (m.factorial : ℚ)) := by
        rw [← Polynomial.C_eq_natCast, ← map_mul, ← map_mul]
        congr 1
        rw [pow_succ, hfac]
        field_simp
      calc C (((n * p : ℕ) : ℚ) ^ (m + 1) / (((m + 1).factorial : ℕ) : ℚ)) *
            (((m + 1 : ℕ) : ℚ[X]) * (LExp p M) ^ (m + 1 - 1) * (LExp p M).derivative)
          = (C (((n * p : ℕ) : ℚ) ^ (m + 1) / (((m + 1).factorial : ℕ) : ℚ)) * ((m + 1 : ℕ) : ℚ[X])) *
            (LExp p M) ^ m * (LExp p M).derivative := by
              rw [Nat.add_sub_cancel]; ring
        _ = C ((n * p : ℕ) : ℚ) * (LExp p M).derivative *
            (C (((n * p : ℕ) : ℚ) ^ m / (m.factorial : ℚ)) * (LExp p M) ^ m) := by
              rw [hcoef]; ring
    rw [hsplit, ← Finset.mul_sum]
  rw [hd]
  have hrew : C ((n * p : ℕ) : ℚ) * (LExp p M).derivative *
        (EExp p n M - C (((n * p : ℕ) : ℚ) ^ M / (M.factorial : ℚ)) * (LExp p M) ^ M) -
      C ((n * p : ℕ) : ℚ) * (LExp p M).derivative * EExp p n M =
      -(C ((n * p : ℕ) : ℚ) * (LExp p M).derivative *
        C (((n * p : ℕ) : ℚ) ^ M / (M.factorial : ℚ))) * (LExp p M) ^ M := by ring
  rw [hrew, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_eq_zero ?_
  intro x hx
  have hxk : x ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
  rw [coeff_pow_eq_zero_of_lt (LExp_coeff_zero p M) (by omega), mul_zero]

private lemma EExp_coeff_zero (p n M : ℕ) : (EExp p n M).coeff 0 = 1 := by
  unfold EExp
  rw [Polynomial.finsetSum_coeff, Finset.sum_range_succ']
  have hrest : ∑ m ∈ Finset.range M,
      (C (((n * p : ℕ) : ℚ) ^ (m + 1) / (((m + 1).factorial : ℕ) : ℚ)) * (LExp p M) ^ (m + 1)).coeff 0 = 0 := by
    refine Finset.sum_eq_zero ?_
    intro m _
    rw [coeff_C_mul, coeff_pow_eq_zero_of_lt (LExp_coeff_zero p M) (Nat.succ_pos m), mul_zero]
  rw [hrest, zero_add]
  simp

private lemma cPoly_factorization {p n M : ℕ} (hp : p.Prime) (hp_odd : p % 2 = 1) (hn : 1 ≤ n) :
    PolyEqMod M (cPoly (n * p) M) ((cPoly n M).comp (X ^ p) * EExp p n M) := by
  set U : ℚ[X] := (1 - X ^ p : ℚ[X]) ^ n * (1 - X ^ (2 * p) : ℚ[X]) ^ n
  set V : ℚ[X] := (1 - X : ℚ[X]) ^ (n * p) * (1 - X ^ 2 : ℚ[X]) ^ (n * p) * EExp p n M
  have hU0 : U.coeff 0 = 1 := by
    dsimp [U]
    rw [Polynomial.coeff_zero_eq_eval_zero, eval_mul, eval_pow, eval_pow]
    simp [zero_pow hp.ne_zero, zero_pow (by have := hp.pos; omega : 2 * p ≠ 0)]
  have hV0 : V.coeff 0 = 1 := by
    dsimp [V]
    have hE0 : (EExp p n M).eval 0 = 1 := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, EExp_coeff_zero]
    rw [Polynomial.coeff_zero_eq_eval_zero, eval_mul, eval_mul, eval_pow, eval_pow, hE0]
    simp [zero_pow (by omega : 2 ≠ 0)]
  have hUV : PolyEqMod M U V := by
    refine polyEqMod_of_log_deriv_eq hU0 hV0 ?_
    set W : ℚ[X] := (1 - X ^ 2 : ℚ[X]) * (1 - X ^ (2 * p) : ℚ[X])
    have hW0 : W.coeff 0 ≠ 0 := by
      dsimp [W]
      rw [Polynomial.coeff_zero_eq_eval_zero]
      simp [zero_pow (by omega : 2 ≠ 0), zero_pow (by have := hp.pos; omega : 2 * p ≠ 0)]
    suffices hW : ∀ k < M, (W * (U.derivative * V - U * V.derivative)).coeff k = 0 by
      have hW' : ∀ k < M, ((C (W.coeff 0)⁻¹ * W) * (U.derivative * V - U * V.derivative)).coeff k = 0 := by
        intro k hk
        rw [mul_assoc, coeff_C_mul, hW k hk, mul_zero]
      have hW0' : (C (W.coeff 0)⁻¹ * W).coeff 0 = 1 := by
        rw [coeff_C_mul, inv_mul_cancel₀ hW0]
      exact coeff_eq_zero_of_mul_unit_coeff_zero hW0' hW'
    have hX2p : (X : ℚ[X]) ^ (2 * p - 1) = (X : ℚ[X]) ^ (p - 1) * (X : ℚ[X]) ^ p := by
      rw [← pow_add]
      congr 1; have := hp.pos; omega
    have hUderiv : W * U.derivative =
        -C ((n * p : ℕ) : ℚ) * (1 - X ^ 2 : ℚ[X]) * X ^ (p - 1) * (1 + C (3 : ℚ) * X ^ p) * U := by
      have hdU : U.derivative =
          -((n * p : ℕ) : ℚ[X]) * (1 - X ^ p : ℚ[X]) ^ (n - 1) * X ^ (p - 1) * (1 - X ^ (2 * p) : ℚ[X]) ^ n -
          ((2 * n * p : ℕ) : ℚ[X]) * (1 - X ^ p : ℚ[X]) ^ n * (1 - X ^ (2 * p) : ℚ[X]) ^ (n - 1) * X ^ (2 * p - 1) := by
        dsimp [U]
        rw [Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_pow]
        simp only [Polynomial.derivative_sub, Polynomial.derivative_one,
          Polynomial.derivative_X_pow, zero_sub, Polynomial.C_eq_natCast]
        push_cast
        ring
      rw [hdU]
      have h1 : (1 - X ^ (2 * p) : ℚ[X]) * (1 - X ^ p : ℚ[X]) ^ (n - 1) =
          (1 + X ^ p : ℚ[X]) * (1 - X ^ p : ℚ[X]) ^ n := by
        have hsq : (1 - X ^ (2 * p) : ℚ[X]) = (1 + X ^ p : ℚ[X]) * (1 - X ^ p : ℚ[X]) := by
          have : (X : ℚ[X]) ^ (2 * p) = ((X : ℚ[X]) ^ p) ^ 2 := by rw [← pow_mul, mul_comm]
          rw [this]; ring
        have hpow : (1 - X ^ p : ℚ[X]) ^ n = (1 - X ^ p : ℚ[X]) * (1 - X ^ p : ℚ[X]) ^ (n - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel hn]
        rw [hsq, hpow]; ring
      have h2 : (1 - X ^ (2 * p) : ℚ[X]) * (1 - X ^ (2 * p) : ℚ[X]) ^ (n - 1) =
          (1 - X ^ (2 * p) : ℚ[X]) ^ n := by
        rw [← pow_succ', Nat.sub_add_cancel hn]
      dsimp [W, U]
      rw [mul_sub]
      have t1 : (1 - X ^ 2 : ℚ[X]) * (1 - X ^ (2 * p) : ℚ[X]) *
          (-((n * p : ℕ) : ℚ[X]) * (1 - X ^ p : ℚ[X]) ^ (n - 1) * X ^ (p - 1) * (1 - X ^ (2 * p) : ℚ[X]) ^ n) =
          -((n * p : ℕ) : ℚ[X]) * (1 - X ^ 2 : ℚ[X]) * X ^ (p - 1) *
            ((1 - X ^ (2 * p) : ℚ[X]) * (1 - X ^ p : ℚ[X]) ^ (n - 1)) * (1 - X ^ (2 * p) : ℚ[X]) ^ n := by ring
      have t2 : (1 - X ^ 2 : ℚ[X]) * (1 - X ^ (2 * p) : ℚ[X]) *
          (((2 * n * p : ℕ) : ℚ[X]) * (1 - X ^ p : ℚ[X]) ^ n * (1 - X ^ (2 * p) : ℚ[X]) ^ (n - 1) * X ^ (2 * p - 1)) =
          ((2 * n * p : ℕ) : ℚ[X]) * (1 - X ^ 2 : ℚ[X]) * (1 - X ^ p : ℚ[X]) ^ n *
            ((1 - X ^ (2 * p) : ℚ[X]) * (1 - X ^ (2 * p) : ℚ[X]) ^ (n - 1)) * X ^ (2 * p - 1) := by ring
      rw [t1, t2, h1, h2, hX2p]
      simp only [map_natCast, map_ofNat]
      push_cast
      ring
    have hVderiv : ∀ k < M,
        (W * V.derivative -
          C ((n * p : ℕ) : ℚ) *
            (-(1 - X ^ (2 * p) : ℚ[X]) * (1 + C (3 : ℚ) * X) + W * (LExp p M).derivative) * V).coeff k = 0 := by
      have hnp : 1 ≤ n * p := Nat.mul_pos hn hp.pos
      have hdV0 : ((1 - X : ℚ[X]) ^ (n * p) * (1 - X ^ 2 : ℚ[X]) ^ (n * p)).derivative =
          -((n * p : ℕ) : ℚ[X]) * (1 - X : ℚ[X]) ^ (n * p - 1) * (1 - X ^ 2 : ℚ[X]) ^ (n * p) -
          ((2 * n * p : ℕ) : ℚ[X]) * (1 - X : ℚ[X]) ^ (n * p) * (1 - X ^ 2 : ℚ[X]) ^ (n * p - 1) * X := by
        rw [Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_pow]
        simp only [Polynomial.derivative_sub, Polynomial.derivative_one,
          Polynomial.derivative_X, Polynomial.derivative_X_pow, zero_sub, Polynomial.C_eq_natCast]
        push_cast
        ring
      have h1 : (1 - X ^ 2 : ℚ[X]) * (1 - X : ℚ[X]) ^ (n * p - 1) =
          (1 + X : ℚ[X]) * (1 - X : ℚ[X]) ^ (n * p) := by
        have hpow : (1 - X : ℚ[X]) ^ (n * p) = (1 - X : ℚ[X]) * (1 - X : ℚ[X]) ^ (n * p - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel hnp]
        rw [hpow]; ring
      have h2 : (1 - X ^ 2 : ℚ[X]) * (1 - X ^ 2 : ℚ[X]) ^ (n * p - 1) =
          (1 - X ^ 2 : ℚ[X]) ^ (n * p) := by
        rw [← pow_succ', Nat.sub_add_cancel hnp]
      have hW0 : W * ((1 - X : ℚ[X]) ^ (n * p) * (1 - X ^ 2 : ℚ[X]) ^ (n * p)).derivative =
          -C ((n * p : ℕ) : ℚ) * (1 - X ^ (2 * p) : ℚ[X]) * (1 + C (3 : ℚ) * X) *
            ((1 - X : ℚ[X]) ^ (n * p) * (1 - X ^ 2 : ℚ[X]) ^ (n * p)) := by
        rw [hdV0]
        dsimp [W]
        rw [mul_sub]
        have t1 : (1 - X ^ 2 : ℚ[X]) * (1 - X ^ (2 * p) : ℚ[X]) *
            (-((n * p : ℕ) : ℚ[X]) * (1 - X : ℚ[X]) ^ (n * p - 1) * (1 - X ^ 2 : ℚ[X]) ^ (n * p)) =
            -((n * p : ℕ) : ℚ[X]) * (1 - X ^ (2 * p) : ℚ[X]) *
              ((1 - X ^ 2 : ℚ[X]) * (1 - X : ℚ[X]) ^ (n * p - 1)) * (1 - X ^ 2 : ℚ[X]) ^ (n * p) := by ring
        have t2 : (1 - X ^ 2 : ℚ[X]) * (1 - X ^ (2 * p) : ℚ[X]) *
            (((2 * n * p : ℕ) : ℚ[X]) * (1 - X : ℚ[X]) ^ (n * p) * (1 - X ^ 2 : ℚ[X]) ^ (n * p - 1) * X) =
            ((2 * n * p : ℕ) : ℚ[X]) * (1 - X ^ (2 * p) : ℚ[X]) * (1 - X : ℚ[X]) ^ (n * p) *
              ((1 - X ^ 2 : ℚ[X]) * (1 - X ^ 2 : ℚ[X]) ^ (n * p - 1)) * X := by ring
        rw [t1, t2, h1, h2]
        simp only [map_natCast, map_ofNat]
        push_cast
        ring
      have hdiff_eq : W * V.derivative -
          C ((n * p : ℕ) : ℚ) *
            (-(1 - X ^ (2 * p) : ℚ[X]) * (1 + C (3 : ℚ) * X) + W * (LExp p M).derivative) * V =
          W * ((1 - X : ℚ[X]) ^ (n * p) * (1 - X ^ 2 : ℚ[X]) ^ (n * p)) *
            ((EExp p n M).derivative - C ((n * p : ℕ) : ℚ) * (LExp p M).derivative * EExp p n M) := by
        have hVdef : V = ((1 - X : ℚ[X]) ^ (n * p) * (1 - X ^ 2 : ℚ[X]) ^ (n * p)) * EExp p n M := rfl
        conv_lhs => rw [hVdef, Polynomial.derivative_mul]
        calc W * (((1 - X : ℚ[X]) ^ (n * p) * (1 - X ^ 2 : ℚ[X]) ^ (n * p)).derivative * EExp p n M +
              (1 - X : ℚ[X]) ^ (n * p) * (1 - X ^ 2 : ℚ[X]) ^ (n * p) * (EExp p n M).derivative) -
            C ((n * p : ℕ) : ℚ) *
              (-(1 - X ^ (2 * p) : ℚ[X]) * (1 + C (3 : ℚ) * X) + W * (LExp p M).derivative) *
              ((1 - X : ℚ[X]) ^ (n * p) * (1 - X ^ 2 : ℚ[X]) ^ (n * p) * EExp p n M)
            = (W * ((1 - X : ℚ[X]) ^ (n * p) * (1 - X ^ 2 : ℚ[X]) ^ (n * p)).derivative) * EExp p n M +
              W * ((1 - X : ℚ[X]) ^ (n * p) * (1 - X ^ 2 : ℚ[X]) ^ (n * p)) * (EExp p n M).derivative -
            C ((n * p : ℕ) : ℚ) *
              (-(1 - X ^ (2 * p) : ℚ[X]) * (1 + C (3 : ℚ) * X) + W * (LExp p M).derivative) *
              ((1 - X : ℚ[X]) ^ (n * p) * (1 - X ^ 2 : ℚ[X]) ^ (n * p) * EExp p n M) := by ring
          _ = W * ((1 - X : ℚ[X]) ^ (n * p) * (1 - X ^ 2 : ℚ[X]) ^ (n * p)) *
              ((EExp p n M).derivative - C ((n * p : ℕ) : ℚ) * (LExp p M).derivative * EExp p n M) := by
              rw [hW0]; ring
      intro k hk
      rw [hdiff_eq, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      refine Finset.sum_eq_zero ?_
      intro x hx
      have hxk : x ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
      rw [EExp_deriv_eq p n M (k - x) (by omega), mul_zero]
    have hLcancel : ∀ k < M,
        ((1 - X ^ (2 * p) : ℚ[X]) * (1 + C (3 : ℚ) * X) -
         (1 - X ^ 2 : ℚ[X]) * X ^ (p - 1) * (1 + C (3 : ℚ) * X ^ p) -
         W * (LExp p M).derivative).coeff k = 0 := by
      intro k hk
      rw [LExp_deriv_eq hp hp_odd M]
      have hrew : (1 - X ^ (2 * p) : ℚ[X]) * (1 + C (3 : ℚ) * X) -
          (1 - X ^ 2 : ℚ[X]) * X ^ (p - 1) * (1 + C (3 : ℚ) * X ^ p) -
          W * (GPoly M - GPolyP p M) =
          (1 - X ^ (2 * p) : ℚ[X]) * ((1 + C (3 : ℚ) * X) - (1 - X ^ 2 : ℚ[X]) * GPoly M) -
          (1 - X ^ 2 : ℚ[X]) * (X ^ (p - 1) * (1 + C (3 : ℚ) * X ^ p) -
            (1 - X ^ (2 * p) : ℚ[X]) * GPolyP p M) := by
        dsimp [W]; ring
      rw [hrew, coeff_sub, coeff_mul, coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      have h1 : ∑ x ∈ Finset.range (k + 1),
          (1 - X ^ (2 * p) : ℚ[X]).coeff x *
            ((1 + C (3 : ℚ) * X) - (1 - X ^ 2 : ℚ[X]) * GPoly M).coeff (k - x) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro x hx
        have hxk : x ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
        have h0 : ((1 + C (3 : ℚ) * X) - (1 - X ^ 2 : ℚ[X]) * GPoly M).coeff (k - x) = 0 := by
          rw [coeff_sub, one_sub_X_sq_mul_GPoly M (k - x) (by omega), sub_self]
        rw [h0, mul_zero]
      have h2 : ∑ x ∈ Finset.range (k + 1),
          (1 - X ^ 2 : ℚ[X]).coeff x *
            (X ^ (p - 1) * (1 + C (3 : ℚ) * X ^ p) -
              (1 - X ^ (2 * p) : ℚ[X]) * GPolyP p M).coeff (k - x) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro x hx
        have hxk : x ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
        have h0 : (X ^ (p - 1) * (1 + C (3 : ℚ) * X ^ p) -
              (1 - X ^ (2 * p) : ℚ[X]) * GPolyP p M).coeff (k - x) = 0 := by
          rw [coeff_sub, one_sub_X_two_p_mul_GPolyP hp.one_le M (k - x) (by omega), sub_self]
        rw [h0, mul_zero]
      rw [h1, h2, sub_self]
    intro k hk
    set RemV : ℚ[X] := W * V.derivative -
      C ((n * p : ℕ) : ℚ) *
        (-(1 - X ^ (2 * p) : ℚ[X]) * (1 + C (3 : ℚ) * X) + W * (LExp p M).derivative) * V
    have hsplit : W * (U.derivative * V - U * V.derivative) =
        C ((n * p : ℕ) : ℚ) * U * V *
          ((1 - X ^ (2 * p) : ℚ[X]) * (1 + C (3 : ℚ) * X) -
           (1 - X ^ 2 : ℚ[X]) * X ^ (p - 1) * (1 + C (3 : ℚ) * X ^ p) -
           W * (LExp p M).derivative) -
        U * RemV := by
      have hWV : W * V.derivative =
          RemV + C ((n * p : ℕ) : ℚ) *
            (-(1 - X ^ (2 * p) : ℚ[X]) * (1 + C (3 : ℚ) * X) + W * (LExp p M).derivative) * V := by
        dsimp [RemV]; ring
      calc W * (U.derivative * V - U * V.derivative)
          = (W * U.derivative) * V - U * (W * V.derivative) := by ring
        _ = (-C ((n * p : ℕ) : ℚ) * (1 - X ^ 2 : ℚ[X]) * X ^ (p - 1) * (1 + C (3 : ℚ) * X ^ p) * U) * V -
            U * (RemV + C ((n * p : ℕ) : ℚ) *
              (-(1 - X ^ (2 * p) : ℚ[X]) * (1 + C (3 : ℚ) * X) + W * (LExp p M).derivative) * V) := by
              rw [hUderiv, hWV]
        _ = C ((n * p : ℕ) : ℚ) * U * V *
              ((1 - X ^ (2 * p) : ℚ[X]) * (1 + C (3 : ℚ) * X) -
               (1 - X ^ 2 : ℚ[X]) * X ^ (p - 1) * (1 + C (3 : ℚ) * X ^ p) -
               W * (LExp p M).derivative) -
            U * RemV := by ring
    rw [hsplit, coeff_sub, coeff_mul, coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have h1 : ∑ x ∈ Finset.range (k + 1),
        (C ((n * p : ℕ) : ℚ) * U * V).coeff x *
          ((1 - X ^ (2 * p) : ℚ[X]) * (1 + C (3 : ℚ) * X) -
           (1 - X ^ 2 : ℚ[X]) * X ^ (p - 1) * (1 + C (3 : ℚ) * X ^ p) -
           W * (LExp p M).derivative).coeff (k - x) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro x hx
      have hxk : x ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
      rw [hLcancel (k - x) (by omega), mul_zero]
    have h2 : ∑ x ∈ Finset.range (k + 1), U.coeff x * RemV.coeff (k - x) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro x hx
      have hxk : x ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
      rw [hVderiv (k - x) (by omega), mul_zero]
    rw [h1, h2, sub_self]
  -- Multiply U ≡ V by cPoly (n * p) M * (cPoly n M).comp (X ^ p)
  have hinv_p1 : PolyEqMod M ((1 - X ^ p : ℚ[X]) ^ n * (invOneSubPowSucc (n - 1) M).comp (X ^ p)) 1 := by
    have hcomp := polyEqMod_comp (u := (X ^ p : ℚ[X])) (by rw [coeff_X_pow, if_neg (Ne.symm hp.ne_zero)])
      (one_sub_X_pow_mul_invOneSubPowSucc (n - 1) M)
    rw [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.sub_comp, Polynomial.one_comp,
        Polynomial.X_comp] at hcomp
    have hn1 : n - 1 + 1 = n := by omega
    rwa [hn1] at hcomp
  have hinv_p2 : PolyEqMod M ((1 - X ^ (2 * p) : ℚ[X]) ^ n * ((invOneSubPowSucc (n - 1) M).comp (X ^ 2)).comp (X ^ p)) 1 := by
    have hcomp := polyEqMod_comp (u := (X ^ (2 * p) : ℚ[X]))
      (by rw [coeff_X_pow, if_neg (by have := hp.pos; omega)])
      (one_sub_X_pow_mul_invOneSubPowSucc (n - 1) M)
    rw [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.sub_comp, Polynomial.one_comp,
        Polynomial.X_comp] at hcomp
    have hcc : ((invOneSubPowSucc (n - 1) M).comp (X ^ 2)).comp (X ^ p) =
        (invOneSubPowSucc (n - 1) M).comp (X ^ (2 * p)) := by
      rw [Polynomial.comp_assoc, Polynomial.X_pow_comp, ← pow_mul, mul_comm]
    have hn1 : n - 1 + 1 = n := by omega
    rw [hcc, ← hn1]
    exact hcomp
  have hinv_np1 : PolyEqMod M ((1 - X : ℚ[X]) ^ (n * p) * invOneSubPowSucc (n * p - 1) M) 1 := by
    have hnp : 1 ≤ n * p := Nat.mul_pos hn hp.pos
    have h1 : n * p - 1 + 1 = n * p := by omega
    simpa [h1] using one_sub_X_pow_mul_invOneSubPowSucc (n * p - 1) M
  have hinv_np2 : PolyEqMod M ((1 - X ^ 2 : ℚ[X]) ^ (n * p) * (invOneSubPowSucc (n * p - 1) M).comp (X ^ 2)) 1 := by
    have hcomp := polyEqMod_comp (u := (X ^ 2 : ℚ[X])) (by rw [coeff_X_pow, if_neg (by omega)])
      (one_sub_X_pow_mul_invOneSubPowSucc (n * p - 1) M)
    rw [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.sub_comp, Polynomial.one_comp,
        Polynomial.X_comp] at hcomp
    have hnp : 1 ≤ n * p := Nat.mul_pos hn hp.pos
    have h1 : n * p - 1 + 1 = n * p := by omega
    rwa [h1] at hcomp
  have hLHS : PolyEqMod M (U * (cPoly (n * p) M * (cPoly n M).comp (X ^ p))) (cPoly (n * p) M) := by
    dsimp [U, cPoly]
    rw [Polynomial.mul_comp]
    have hrew : (1 - X ^ p : ℚ[X]) ^ n * (1 - X ^ (2 * p) : ℚ[X]) ^ n *
        (invOneSubPowSucc (n * p - 1) M * (invOneSubPowSucc (n * p - 1) M).comp (X ^ 2) *
          ((invOneSubPowSucc (n - 1) M).comp (X ^ p) * ((invOneSubPowSucc (n - 1) M).comp (X ^ 2)).comp (X ^ p))) =
        (invOneSubPowSucc (n * p - 1) M * (invOneSubPowSucc (n * p - 1) M).comp (X ^ 2)) *
        ((1 - X ^ p : ℚ[X]) ^ n * (invOneSubPowSucc (n - 1) M).comp (X ^ p)) *
        ((1 - X ^ (2 * p) : ℚ[X]) ^ n * ((invOneSubPowSucc (n - 1) M).comp (X ^ 2)).comp (X ^ p)) := by ring
    rw [hrew]
    simpa using polyEqMod_mul (polyEqMod_mul (polyEqMod_refl M _) hinv_p1) hinv_p2
  have hRHS : PolyEqMod M (V * (cPoly (n * p) M * (cPoly n M).comp (X ^ p)))
      ((cPoly n M).comp (X ^ p) * EExp p n M) := by
    dsimp [V, cPoly]
    have hrew : (1 - X : ℚ[X]) ^ (n * p) * (1 - X ^ 2 : ℚ[X]) ^ (n * p) * EExp p n M *
        (invOneSubPowSucc (n * p - 1) M * (invOneSubPowSucc (n * p - 1) M).comp (X ^ 2) *
          (invOneSubPowSucc (n - 1) M * (invOneSubPowSucc (n - 1) M).comp (X ^ 2)).comp (X ^ p)) =
        ((invOneSubPowSucc (n - 1) M * (invOneSubPowSucc (n - 1) M).comp (X ^ 2)).comp (X ^ p) * EExp p n M) *
        ((1 - X : ℚ[X]) ^ (n * p) * invOneSubPowSucc (n * p - 1) M) *
        ((1 - X ^ 2 : ℚ[X]) ^ (n * p) * (invOneSubPowSucc (n * p - 1) M).comp (X ^ 2)) := by ring
    rw [hrew]
    simpa using polyEqMod_mul (polyEqMod_mul (polyEqMod_refl M _) hinv_np1) hinv_np2
  exact polyEqMod_trans (polyEqMod_symm hLHS)
    (polyEqMod_trans (polyEqMod_mul hUV (polyEqMod_refl M _)) hRHS)

private lemma cCoeff_diff_eq_sum {p n j M : ℕ} (hp : p.Prime) (hp_odd : p % 2 = 1)
    (hn : 1 ≤ n) (hjM : p * j ≤ M) :
    (cCoeff (n * p) (p * j) : ℚ) - (cCoeff n j : ℚ) =
      ∑ i ∈ Finset.range j, (cCoeff n i : ℚ) * (EExp p n M).coeff (p * (j - i)) := by
  have hfac := cPoly_factorization (M := M) hp hp_odd hn (p * j) hjM
  rw [coeff_cPoly hjM, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hfac
  have hsum : (∑ a ∈ Finset.range (p * j + 1),
      ((cPoly n M).comp (X ^ p)).coeff a * (EExp p n M).coeff (p * j - a)) =
      ∑ i ∈ Finset.range (j + 1), (cCoeff n i : ℚ) * (EExp p n M).coeff (p * (j - i)) := by
    have hfilt : (∑ a ∈ Finset.range (p * j + 1),
        ((cPoly n M).comp (X ^ p)).coeff a * (EExp p n M).coeff (p * j - a)) =
        ∑ a ∈ (Finset.range (p * j + 1)).filter (fun a => p ∣ a),
          ((cPoly n M).comp (X ^ p)).coeff a * (EExp p n M).coeff (p * j - a) := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro a ha hnot
      have hnd : ¬ p ∣ a := fun hd => hnot (Finset.mem_filter.mpr ⟨ha, hd⟩)
      rw [coeff_comp_X_pow hp.one_le, if_neg hnd, zero_mul]
    rw [hfilt]
    symm
    refine Finset.sum_nbij (fun i => p * i) ?_ ?_ ?_ ?_
    · intro i hi
      have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, dvd_mul_right p i⟩
      have := Nat.mul_le_mul_left p hij
      omega
    · intro i1 _ i2 _ heq
      exact Nat.eq_of_mul_eq_mul_left hp.pos heq
    · intro a ha
      rcases Finset.mem_filter.mp ha with ⟨har, hd⟩
      rcases hd with ⟨i, rfl⟩
      have hij : i ≤ j := by
        have hlt : p * i < p * j + 1 := Finset.mem_range.mp har
        have hle : p * i ≤ p * j := by omega
        exact Nat.le_of_mul_le_mul_left hle hp.pos
      exact ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hij), rfl⟩
    · intro i hi
      have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [coeff_comp_X_pow hp.one_le, if_pos (dvd_mul_right p i),
          Nat.mul_div_cancel_left i hp.pos,
          coeff_cPoly (le_trans (Nat.le_mul_of_pos_left i hp.pos) (le_trans (Nat.mul_le_mul_left p hij) hjM)),
          ← Nat.mul_sub_left_distrib]
  rw [hsum, Finset.sum_range_succ, Nat.sub_self, Nat.mul_zero, EExp_coeff_zero, mul_one] at hfac
  linarith

/-! ### Section 4: p-adic Valuation Bounds and Final Proof -/

private lemma isPDvdZ_LExp_sq_coeff {p j M : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hj : 1 ≤ j) (hjM : p * j ≤ M) :
    IsPDvdZ p (1 + padicValNat p j) (((LExp p M) ^ 2).coeff (p * j)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp_odd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with rfl | hodd
    · omega
    · exact hodd
  have hLcoeff : ∀ d ≤ M, (LExp p M).coeff d =
      if 1 ≤ d ∧ ¬ p ∣ d then gVal d / (d : ℚ) else 0 := by
    intro d hdM
    unfold LExp
    rw [Polynomial.finsetSum_coeff]
    simp_rw [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq ((Finset.Icc 1 M).filter (fun e => ¬ p ∣ e)) d]
    by_cases hc : 1 ≤ d ∧ ¬ p ∣ d
    · rw [if_pos (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hc.1, hdM⟩, hc.2⟩), if_pos hc]
    · rw [if_neg (fun hm => hc ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1, (Finset.mem_filter.mp hm).2⟩), if_neg hc]
  have hsq_eq : ((LExp p M) ^ 2).coeff (p * j) =
      ∑ d ∈ (Finset.Ico 1 (p * j)).filter (fun d => ¬ p ∣ d),
        (gVal d * gVal (p * j - d)) * ((1 : ℚ) / ((d : ℚ) * ((p * j - d : ℕ) : ℚ))) := by
    rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have hfilt : (∑ d ∈ Finset.range (p * j + 1), (LExp p M).coeff d * (LExp p M).coeff (p * j - d)) =
        ∑ d ∈ (Finset.Ico 1 (p * j)).filter (fun d => ¬ p ∣ d),
          (LExp p M).coeff d * (LExp p M).coeff (p * j - d) := by
      symm
      refine Finset.sum_subset ?_ ?_
      · intro d hd
        have hlt := (Finset.mem_Ico.mp (Finset.mem_filter.mp hd).1).2
        exact Finset.mem_range.mpr (by omega)
      · intro d hd hnot
        have hd_le : d ≤ p * j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
        by_cases hc : 1 ≤ d ∧ d < p * j ∧ ¬ p ∣ d
        · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hc.1, hc.2.1⟩, hc.2.2⟩) hnot
        · by_cases hd0 : d = 0
          · subst hd0; rw [LExp_coeff_zero, zero_mul]
          · by_cases hdpj : d = p * j
            · subst hdpj; rw [Nat.sub_self, LExp_coeff_zero, mul_zero]
            · have hpd : p ∣ d := by
                by_contra hnd; exact hc ⟨by omega, by omega, hnd⟩
              rw [hLcoeff d (by omega), if_neg (by tauto), zero_mul]
    rw [hfilt]
    refine Finset.sum_congr rfl ?_
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hIco, hnd⟩
    rcases Finset.mem_Ico.mp hIco with ⟨hd1, hdpj⟩
    have hnd_sub : ¬ p ∣ (p * j - d) := by
      intro hsub
      have hadd : (p * j - d) + d = p * j := Nat.sub_add_cancel (le_of_lt hdpj)
      exact hnd ((Nat.dvd_add_right hsub).mp (hadd.symm ▸ dvd_mul_right p j))
    rw [hLcoeff d (by omega), if_pos ⟨hd1, hnd⟩, hLcoeff (p * j - d) (by omega),
        if_pos ⟨by omega, hnd_sub⟩]
    ring
  rw [hsq_eq]
  set S := (Finset.Ico 1 (p * j)).filter (fun d => ¬ p ∣ d)
  by_cases hj_odd : j % 2 = 1
  · have hpj_odd : (p * j) % 2 = 1 := by rw [Nat.mul_mod, hp_odd, hj_odd]
    have hconst : (∑ d ∈ S, (gVal d * gVal (p * j - d)) * ((1 : ℚ) / ((d : ℚ) * ((p * j - d : ℕ) : ℚ)))) =
        ((3 : ℕ) : ℚ) * ∑ d ∈ S, (1 : ℚ) / ((d : ℚ) * ((p * j - d : ℕ) : ℚ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro d hd
      have hdpj : d < p * j := (Finset.mem_Ico.mp (Finset.mem_filter.mp hd).1).2
      have hprod : gVal d * gVal (p * j - d) = 3 := by
        unfold gVal
        have hpar : d % 2 = 0 ∨ d % 2 = 1 := Nat.mod_two_eq_zero_or_one d
        rcases hpar with h0 | h1
        · have hsub1 : (p * j - d) % 2 = 1 := by omega
          rw [if_neg (by omega), if_pos hsub1]; norm_num
        · have hsub0 : (p * j - d) % 2 = 0 := by omega
          rw [if_pos h1, if_neg (by omega)]; norm_num
      rw [hprod]; norm_num
    rw [hconst]
    simpa [Nat.zero_add] using isPDvdZ_mul hp (isPDvdZ_natCast_zero hp 3) (isPDvdZ_sum_inv_pair hp hp5 hj)
  · have hj_even : j % 2 = 0 := by omega
    set j0 := j / 2
    have hj_eq : j = 2 * j0 := by omega
    have hj0_pos : 1 ≤ j0 := by omega
    have hv_eq : padicValNat p j = padicValNat p j0 := by
      rw [hj_eq, padicValNat.mul (by omega) (by omega),
          padicValNat.eq_zero_of_not_dvd (fun h => by have := Nat.le_of_dvd (by omega) h; omega),
          zero_add]
    set Seven := S.filter (fun d => d % 2 = 0)
    have hsplit : (∑ d ∈ S, (gVal d * gVal (p * j - d)) * ((1 : ℚ) / ((d : ℚ) * ((p * j - d : ℕ) : ℚ)))) =
        ((1 : ℕ) : ℚ) * (∑ d ∈ S, (1 : ℚ) / ((d : ℚ) * ((p * j - d : ℕ) : ℚ))) +
        ((8 : ℕ) : ℚ) * (∑ d ∈ Seven, (1 : ℚ) / ((d : ℚ) * ((p * j - d : ℕ) : ℚ))) := by
      have hdecomp := (Finset.sum_filter_add_sum_filter_not S (fun d => d % 2 = 0)
        (fun d => (gVal d * gVal (p * j - d)) * ((1 : ℚ) / ((d : ℚ) * ((p * j - d : ℕ) : ℚ))))).symm
      have hdecomp1 := (Finset.sum_filter_add_sum_filter_not S (fun d => d % 2 = 0)
        (fun d => (1 : ℚ) / ((d : ℚ) * ((p * j - d : ℕ) : ℚ)))).symm
      have hev : (∑ d ∈ Seven, (gVal d * gVal (p * j - d)) * ((1 : ℚ) / ((d : ℚ) * ((p * j - d : ℕ) : ℚ)))) =
          (9 : ℚ) * ∑ d ∈ Seven, (1 : ℚ) / ((d : ℚ) * ((p * j - d : ℕ) : ℚ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro d hd
        rcases Finset.mem_filter.mp hd with ⟨hdS, hd0⟩
        have hdpj : d < p * j := (Finset.mem_Ico.mp (Finset.mem_filter.mp hdS).1).2
        have hpj0 : (p * j) % 2 = 0 := by rw [Nat.mul_mod, hj_even, mul_zero]; rfl
        have hsub0 : (p * j - d) % 2 = 0 := by omega
        unfold gVal
        rw [if_neg (by omega), if_neg (by omega)]; ring
      have hodd : (∑ d ∈ S.filter (fun d => ¬ d % 2 = 0),
          (gVal d * gVal (p * j - d)) * ((1 : ℚ) / ((d : ℚ) * ((p * j - d : ℕ) : ℚ)))) =
          (1 : ℚ) * ∑ d ∈ S.filter (fun d => ¬ d % 2 = 0), (1 : ℚ) / ((d : ℚ) * ((p * j - d : ℕ) : ℚ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro d hd
        rcases Finset.mem_filter.mp hd with ⟨hdS, hd1⟩
        have hdpj : d < p * j := (Finset.mem_Ico.mp (Finset.mem_filter.mp hdS).1).2
        have hpj0 : (p * j) % 2 = 0 := by rw [Nat.mul_mod, hj_even, mul_zero]; rfl
        have hsub1 : (p * j - d) % 2 = 1 := by omega
        unfold gVal
        rw [if_pos (by omega), if_pos hsub1]; ring
      rw [hdecomp, hdecomp1, hev, hodd]
      norm_num
      ring
    have hpj_eq : p * j = 2 * (p * j0) := by rw [hj_eq]; ring
    have heven_eq : (∑ d ∈ Seven, (1 : ℚ) / ((d : ℚ) * ((p * j - d : ℕ) : ℚ))) =
        (∑ e ∈ (Finset.Ico 1 (p * j0)).filter (fun e => ¬ p ∣ e),
          (1 : ℚ) / ((e : ℚ) * ((p * j0 - e : ℕ) : ℚ))) / ((4 : ℕ) : ℚ) := by
      rw [Finset.sum_div]
      symm
      refine Finset.sum_nbij (fun e => 2 * e) ?_ ?_ ?_ ?_
      · intro e he
        rcases Finset.mem_filter.mp he with ⟨hIco, hnd⟩
        rcases Finset.mem_Ico.mp hIco with ⟨he1, he_lt⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩, by omega⟩
        intro hd
        rcases hp.dvd_mul.mp hd with h2 | he'
        · have := Nat.le_of_dvd (by omega) h2; omega
        · exact hnd he'
      · intro e1 _ e2 _ heq; dsimp only at heq; omega
      · intro d hd
        rcases Finset.mem_filter.mp hd with ⟨hdS, hd0⟩
        rcases Finset.mem_filter.mp hdS with ⟨hIco, hnd⟩
        rcases Finset.mem_Ico.mp hIco with ⟨hd1, hdpj⟩
        refine ⟨d / 2, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩, by dsimp; omega⟩
        intro hde
        have hd_eq : d = 2 * (d / 2) := by omega
        exact hnd (hd_eq ▸ dvd_mul_of_dvd_right hde 2)
      · intro e he
        have he_lt : e < p * j0 := (Finset.mem_Ico.mp (Finset.mem_filter.mp he).1).2
        have hsub : p * j - 2 * e = 2 * (p * j0 - e) := by omega
        rw [hsub]
        push_cast
        ring
    rw [hsplit, heven_eq]
    have h1 : IsPDvdZ p (1 + padicValNat p j)
        (((1 : ℕ) : ℚ) * ∑ d ∈ S, (1 : ℚ) / ((d : ℚ) * ((p * j - d : ℕ) : ℚ))) := by
      simpa [Nat.zero_add] using isPDvdZ_mul hp (isPDvdZ_natCast_zero hp 1) (isPDvdZ_sum_inv_pair hp hp5 hj)
    have h2 : IsPDvdZ p (1 + padicValNat p j)
        (((8 : ℕ) : ℚ) * ((∑ e ∈ (Finset.Ico 1 (p * j0)).filter (fun e => ¬ p ∣ e),
          (1 : ℚ) / ((e : ℚ) * ((p * j0 - e : ℕ) : ℚ))) / ((4 : ℕ) : ℚ))) := by
      have h4ndvd : ¬ p ∣ 4 := fun h => by have := Nat.le_of_dvd (by omega) h; omega
      have h2a := isPDvdZ_div_coprime_nat hp h4ndvd (isPDvdZ_sum_inv_pair hp hp5 hj0_pos)
      rw [← hv_eq] at h2a
      simpa [Nat.zero_add] using isPDvdZ_mul hp (isPDvdZ_natCast_zero hp 8) h2a
    exact isPDvdZ_add hp h1 h2

private lemma isPDvdZ_EExp_coeff {p n j M : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (_hn : 1 ≤ n) (hj : 1 ≤ j) (hjM : p * j ≤ M) :
    IsPDvdZ p (3 + 2 * padicValNat p n + min (padicValNat p n) (padicValNat p j))
      ((EExp p n M).coeff (p * j)) := by
  have : Fact p.Prime := ⟨hp⟩
  set s := padicValNat p n
  set K := 3 + 2 * s + min s (padicValNat p j)
  have hL0 : ∀ d : ℕ, IsPDvdZ p 0 ((LExp p M).coeff d) := by
    intro d
    unfold LExp
    rw [Polynomial.finsetSum_coeff]
    refine isPDvdZ_sum hp _ _ ?_
    intro e he
    rw [coeff_C_mul_X_pow]
    by_cases hde : d = e
    · rw [if_pos hde]
      have hnd : ¬ p ∣ e := (Finset.mem_filter.mp he).2
      have hg0 : IsPDvdZ p 0 (gVal e) := by
        unfold gVal
        split_ifs
        · exact isPDvdZ_natCast_zero hp 1
        · exact isPDvdZ_natCast_zero hp 3
      exact isPDvdZ_div_coprime_nat hp hnd hg0
    · rw [if_neg hde]; exact isPDvdZ_zero hp
  unfold EExp
  rw [Polynomial.finsetSum_coeff]
  refine isPDvdZ_sum hp (Finset.range (M + 1)) _ ?_
  intro m _
  rw [coeff_C_mul]
  rcases m with _ | _ | _ | m
  · have hpj_ne : p * j ≠ 0 := mul_ne_zero hp.ne_zero (by omega)
    simp only [pow_zero, coeff_one, if_neg hpj_ne, mul_zero]
    exact isPDvdZ_zero hp
  · have hLpj : (LExp p M).coeff (p * j) = 0 := by
      unfold LExp
      rw [Polynomial.finsetSum_coeff]
      refine Finset.sum_eq_zero ?_
      intro d hd
      rw [coeff_C_mul_X_pow]
      have hnd : ¬ p ∣ d := (Finset.mem_filter.mp hd).2
      have hne : p * j ≠ d := fun h => hnd (h ▸ dvd_mul_right p j)
      rw [if_neg hne]
    simp only [Nat.zero_add, pow_one, hLpj, mul_zero]
    exact isPDvdZ_zero hp
  · have hnp_dvd : p ^ (2 * (s + 1)) ∣ (n * p) ^ 2 := by
      have h1 : p ^ (s + 1) ∣ n * p := by
        rw [pow_succ]; exact Nat.mul_dvd_mul_right pow_padicValNat_dvd p
      have h2 := pow_dvd_pow_of_dvd h1 2
      rwa [← pow_mul, mul_comm] at h2
    have h2ndvd : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by omega) h; omega
    have hfac2 : IsPDvdZ p (2 * (s + 1)) (((n * p : ℕ) : ℚ) ^ 2 / ((Nat.factorial 2 : ℕ) : ℚ)) := by
      have h1 : IsPDvdZ p (2 * (s + 1)) ((((n * p) ^ 2 : ℕ) : ℚ)) := isPDvdZ_natCast hp _ hnp_dvd
      have h2 := isPDvdZ_div_coprime_nat hp (d := 2) h2ndvd h1
      simpa using h2
    have hLsq := isPDvdZ_LExp_sq_coeff hp hp5 hj hjM
    have hprod := isPDvdZ_mul hp hfac2 hLsq
    refine isPDvdZ_mono ?_ hprod
    dsimp [K]; omega
  · set k := m + 3
    have hLpow : IsPDvdZ p 0 (((LExp p M) ^ k).coeff (p * j)) :=
      poly_isPDvdZ_zero_pow hp hL0 k (p * j)
    have hnp_dvd : p ^ (k * (s + 1)) ∣ (n * p) ^ k := by
      have h1 : p ^ (s + 1) ∣ n * p := by
        rw [pow_succ]; exact Nat.mul_dvd_mul_right pow_padicValNat_dvd p
      have h2 := pow_dvd_pow_of_dvd h1 k
      rwa [← pow_mul, mul_comm] at h2
    have hnum : IsPDvdZ p (k * (s + 1)) (((n * p : ℕ) : ℚ) ^ k) := by
      simpa using isPDvdZ_natCast hp ((n * p) ^ k) hnp_dvd
    have hleg : (p - 1) * padicValNat p k.factorial ≤ k := legendre_bound hp
    have hval_le : 3 * s + 3 + padicValNat p k.factorial ≤ k * (s + 1) := by
      have h4 : 4 * padicValNat p k.factorial ≤ k :=
        le_trans (Nat.mul_le_mul_right _ (by omega : 4 ≤ p - 1)) hleg
      have hks : 3 * s ≤ k * s := Nat.mul_le_mul_right s (by omega : 3 ≤ k)
      have hkm : 3 + padicValNat p k.factorial ≤ k := by
        by_cases hk5 : k ≤ 4
        · have hlt : k < p := by omega
          have h0 : padicValNat p k.factorial = 0 :=
            padicValNat.eq_zero_of_not_dvd (fun hd => by
              have := hp.dvd_factorial.mp hd; omega)
          omega
        · omega
      nlinarith
    have hdiv := isPDvdZ_div_nat hp (Nat.factorial_ne_zero k) (isPDvdZ_mono hval_le hnum)
    have hprod := isPDvdZ_mul hp hdiv hLpow
    refine isPDvdZ_mono ?_ hprod
    dsimp [K]; omega

private lemma isPDvdZ_cCoeff {p n i : ℕ} (hp : p.Prime) (_hp5 : 5 ≤ p) (hn : 1 ≤ n) (hi1 : 1 ≤ i) :
    IsPDvdZ p (padicValNat p n - padicValNat p i) (cCoeff n i : ℚ) := by
  have : Fact p.Prime := ⟨hp⟩
  unfold cCoeff
  push_cast
  refine isPDvdZ_sum hp (Finset.range (i / 2 + 1)) _ ?_
  intro j hj
  have hji : 2 * j ≤ i := by
    have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj); omega
  set a := i - 2 * j
  have hab : a + 2 * j = i := by omega
  by_cases hv : padicValNat p n ≤ padicValNat p i
  · rw [Nat.sub_eq_zero_of_le hv]
    exact isPDvdZ_mul hp (isPDvdZ_natCast_zero hp _) (isPDvdZ_natCast_zero hp _)
  · have hnotboth : ¬ (p ^ (padicValNat p i + 1) ∣ a ∧ p ^ (padicValNat p i + 1) ∣ 2 * j) := by
      intro ⟨hda, hdj⟩
      have hdi : p ^ (padicValNat p i + 1) ∣ i := by
        have := dvd_add hda hdj
        rwa [hab] at this
      have := (padicValNat_dvd_iff_le (by omega : i ≠ 0)).mp hdi
      omega
    by_cases ha_nd : ¬ p ^ (padicValNat p i + 1) ∣ a
    · have ha1 : 1 ≤ a := by
        by_contra h0; push Not at h0
        have ha0 : a = 0 := by omega
        exact ha_nd (ha0 ▸ dvd_zero _)
      have hva : padicValNat p a ≤ padicValNat p i := by
        by_contra hgt; push Not at hgt
        exact ha_nd ((padicValNat_dvd_iff_le (by omega)).mpr (by omega))
      have hch := padicValNat_negChoose_ge_sub hp hn ha1
      have hdvd : p ^ (padicValNat p n - padicValNat p i) ∣ (n - 1 + a).choose a :=
        dvd_trans (Nat.pow_dvd_pow p (by omega)) pow_padicValNat_dvd
      simpa [Nat.add_zero] using isPDvdZ_mul hp (isPDvdZ_natCast hp _ hdvd) (isPDvdZ_natCast_zero hp _)
    · push Not at ha_nd
      have h2j_nd : ¬ p ^ (padicValNat p i + 1) ∣ 2 * j := fun hdj => hnotboth ⟨ha_nd, hdj⟩
      have hj_nd : ¬ p ^ (padicValNat p i + 1) ∣ j := fun hdj => h2j_nd (dvd_mul_of_dvd_right hdj 2)
      have hj1 : 1 ≤ j := by
        by_contra h0; push Not at h0
        have hj0 : j = 0 := by omega
        exact hj_nd (hj0 ▸ dvd_zero _)
      have hvj : padicValNat p j ≤ padicValNat p i := by
        by_contra hgt; push Not at hgt
        exact hj_nd ((padicValNat_dvd_iff_le (by omega)).mpr (by omega))
      have hch := padicValNat_negChoose_ge_sub hp hn hj1
      have hdvd : p ^ (padicValNat p n - padicValNat p i) ∣ (n - 1 + j).choose j :=
        dvd_trans (Nat.pow_dvd_pow p (by omega)) pow_padicValNat_dvd
      simpa [Nat.zero_add] using isPDvdZ_mul hp (isPDvdZ_natCast_zero hp _) (isPDvdZ_natCast hp _ hdvd)

private lemma cCoeff_diff_dvd {p n j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hn : 1 ≤ n) (hj1 : 1 ≤ j) :
    IsPDvdZ p (3 + 2 * padicValNat p n + min (padicValNat p n) (padicValNat p j))
      ((cCoeff (n * p) (p * j) : ℚ) - (cCoeff n j : ℚ)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp_odd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with rfl | hodd
    · omega
    · exact hodd
  set s := padicValNat p n
  set K := 3 + 2 * s + min s (padicValNat p j)
  rw [cCoeff_diff_eq_sum (M := p * j) hp hp_odd hn le_rfl]
  refine isPDvdZ_sum hp (Finset.range j) _ ?_
  intro i hi
  have hij : i < j := Finset.mem_range.mp hi
  have hji1 : 1 ≤ j - i := by omega
  have hE := isPDvdZ_EExp_coeff (M := p * j) hp hp5 hn hji1 (Nat.mul_le_mul_left p (by omega))
  cases i with
  | zero =>
    rw [Nat.sub_zero] at hE
    simpa [Nat.zero_add] using isPDvdZ_mul hp (isPDvdZ_natCast_zero hp (cCoeff n 0)) hE
  | succ i' =>
    set i := i' + 1
    have hci := isPDvdZ_cCoeff hp hp5 hn (by omega : 1 ≤ i)
    have hprod := isPDvdZ_mul hp hci hE
    refine isPDvdZ_mono ?_ hprod
    by_cases h1 : s ≤ padicValNat p (j - i)
    · dsimp [K]; omega
    · by_cases h2 : padicValNat p j ≤ padicValNat p (j - i)
      · dsimp [K]; omega
      · have hvi_le : padicValNat p i ≤ padicValNat p (j - i) := by
          by_contra hgt; push Not at hgt
          have hdi : p ^ (padicValNat p (j - i) + 1) ∣ i :=
            (padicValNat_dvd_iff_le (by omega : i ≠ 0)).mpr (by omega)
          have hdj : p ^ (padicValNat p (j - i) + 1) ∣ j :=
            (padicValNat_dvd_iff_le (by omega : j ≠ 0)).mpr (by omega)
          have hdji : p ^ (padicValNat p (j - i) + 1) ∣ (j - i) :=
            Nat.dvd_sub hdj hdi
          have := (padicValNat_dvd_iff_le (by omega : j - i ≠ 0)).mp hdji
          omega
        dsimp [K]; omega

private lemma main_proof :
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      ((p : ℤ) ^ (3 * k) ∣ OMA.S_oeis_a351856.a (n * p ^ k) - OMA.S_oeis_a351856.a (n * p ^ (k - 1))) := by
  intro p hp hp5 n k hn hk
  have : Fact p.Prime := ⟨hp⟩
  set N := n * p ^ (k - 1)
  have hN1 : 1 ≤ N := Nat.mul_pos hn (pow_pos hp.pos (k - 1))
  have hNp_eq : n * p ^ k = N * p := by
    dsimp [N]
    rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hk]
  have hNp1 : 1 ≤ N * p := Nat.mul_pos hN1 hp.pos
  rw [hNp_eq, a_eq_cCoeff hNp1, a_eq_cCoeff hN1]
  have h2Np : 2 * (N * p) = p * (2 * N) := by ring
  rw [h2Np]
  have hvN : k - 1 ≤ padicValNat p N :=
    (padicValNat_dvd_iff_le (by omega : N ≠ 0)).mp (dvd_mul_left (p ^ (k - 1)) n)
  have hv2N : padicValNat p (2 * N) = padicValNat p N := by
    rw [padicValNat.mul (by omega) (by omega),
        padicValNat.eq_zero_of_not_dvd (fun h => by have := Nat.le_of_dvd (by omega) h; omega),
        zero_add]
  have hdiff := cCoeff_diff_dvd hp hp5 hN1 (by omega : 1 ≤ 2 * N)
  rw [hv2N, min_self] at hdiff
  have hle : 3 * k ≤ 3 + 2 * padicValNat p N + padicValNat p N := by omega
  have hpow : ((p : ℤ) ^ (3 * k)) = ((p ^ (3 * k) : ℕ) : ℤ) := by push_cast; rfl
  rw [hpow]
  refine isPDvdZ_dvd_int hp ?_
  push_cast
  exact isPDvdZ_mono hle hdiff

end A351856Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a351856.main :=
  A351856Proof.main_proof
