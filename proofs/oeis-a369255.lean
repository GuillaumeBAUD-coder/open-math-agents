import OMAStatements.S_oeis_a369255
import Mathlib

open Finset

namespace OMA.S_oeis_a369255

/-- The multiplicative function whose value at `p ^ e` is the `e`-th coefficient of `P`. -/
noncomputable def E (P : PowerSeries ℤ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n = 0 then 0 else n.factorization.prod fun _ k => PowerSeries.coeff k P, by simp⟩

lemma E_apply {P : PowerSeries ℤ} {n : ℕ} (hn : n ≠ 0) :
    E P n = n.factorization.prod fun _ k => PowerSeries.coeff k P := by
  simp [E, hn]

lemma E_mult (P : PowerSeries ℤ) : (E P).IsMultiplicative := by
  refine ⟨by simp [E], ?_⟩
  intro m n h
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [E_apply (mul_ne_zero hm hn), E_apply hm, E_apply hn, Nat.factorization_mul_of_coprime h,
    Finsupp.prod_add_index_of_disjoint]
  simpa [Nat.support_factorization] using h.disjoint_primeFactors

lemma E_pp {P : PowerSeries ℤ} (hP : PowerSeries.coeff 0 P = 1) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    E P (p ^ e) = PowerSeries.coeff e P := by
  rw [E_apply (pow_ne_zero _ hp.ne_zero), hp.factorization_pow, Finsupp.prod_single_index hP]

lemma E_mul {P Q : PowerSeries ℤ} (hP : PowerSeries.coeff 0 P = 1)
    (hQ : PowerSeries.coeff 0 Q = 1) : E P * E Q = E (P * Q) := by
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ ((E_mult P).mul (E_mult Q))
    _ (E_mult _)]
  intro p e hp
  have hPQ : PowerSeries.coeff 0 (P * Q) = 1 := by
    simp only [PowerSeries.coeff_zero_eq_constantCoeff, map_mul] at *
    rw [hP, hQ, mul_one]
  rw [E_pp hPQ hp, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => E P a * E Q b), Nat.divisors_prime_pow hp,
    Finset.sum_map, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i P * PowerSeries.coeff j Q)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ e := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.pow_div hi' hp.pos, E_pp hP hp, E_pp hQ hp]

lemma E_one : E 1 = 1 := by
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ (E_mult _) _
    ArithmeticFunction.isMultiplicative_one]
  intro p e hp
  rw [E_pp (by simp) hp, ArithmeticFunction.one_apply, PowerSeries.coeff_one]
  simp [pow_eq_one_iff, hp.ne_one]

/-- The series `1 / (1 - X ^ k)`. -/
noncomputable def Pk (k : ℕ) : PowerSeries ℤ := PowerSeries.mk fun e => if k ∣ e then 1 else 0

/-- The series `(1 + X ^ 2) / (1 - X) ^ 2`. -/
noncomputable def Pf : PowerSeries ℤ := PowerSeries.mk fun e => if e = 0 then 1 else 2 * (e : ℤ)

lemma Pk_mul (k : ℕ) (hk : 0 < k) : Pk k * (1 - PowerSeries.X ^ k) = 1 := by
  ext n
  rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_one]
  simp only [Pk, PowerSeries.coeff_mk]
  by_cases hkn : k ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + k := ⟨n - k, by omega⟩
    have h0 : m + k ≠ 0 := by omega
    simp [hk.ne', h0]
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hk.ne']
    · have : ¬ k ∣ n := Nat.not_dvd_of_pos_of_lt hn (by omega)
      simp [this, hkn, hn.ne']

lemma Pf_mul : Pf * ((1 - PowerSeries.X) * (1 - PowerSeries.X)) = 1 + PowerSeries.X ^ 2 := by
  have e : Pf * ((1 - PowerSeries.X) * (1 - PowerSeries.X))
      = Pf - Pf * PowerSeries.X ^ 1 - Pf * PowerSeries.X ^ 1 + Pf * PowerSeries.X ^ 2 := by ring
  rw [e]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_one,
    PowerSeries.coeff_X_pow, Pf, PowerSeries.coeff_mk]
  rcases n with _ | _ | _ | m
  · simp
  · simp
  · simp
  · have h1 : m + 1 + 1 + 1 - 1 = m + 2 := by omega
    have h2 : m + 1 + 1 + 1 - 2 = m + 1 := by omega
    simp [h1, h2]
    ring

lemma coeff0_Pk (k : ℕ) : PowerSeries.coeff 0 (Pk k) = 1 := by simp [Pk]

lemma coeff0_Pf : PowerSeries.coeff 0 Pf = 1 := by simp [Pf]

lemma moebius_eq : (ArithmeticFunction.moebius : ArithmeticFunction ℤ) = E (1 - PowerSeries.X) := by
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    ArithmeticFunction.isMultiplicative_moebius _ (E_mult _)]
  intro p e hp
  rw [E_pp (by simp) hp]
  rcases e with _ | e
  · simp
  · rw [ArithmeticFunction.moebius_apply_prime_pow hp (Nat.succ_ne_zero _)]
    rcases e with _ | e
    · simp
    · simp [PowerSeries.coeff_one, PowerSeries.coeff_X]

/-- `μ ^ 2`, the indicator of squarefree numbers. -/
noncomputable def musq : ArithmeticFunction ℤ :=
  ArithmeticFunction.moebius.pmul ArithmeticFunction.moebius

lemma musq_eq : musq = E (1 + PowerSeries.X) := by
  rw [musq, ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (ArithmeticFunction.isMultiplicative_moebius.pmul ArithmeticFunction.isMultiplicative_moebius)
    _ (E_mult _)]
  intro p e hp
  rw [E_pp (by simp) hp, ArithmeticFunction.pmul_apply]
  rcases e with _ | e
  · simp
  · rw [ArithmeticFunction.moebius_apply_prime_pow hp (Nat.succ_ne_zero _)]
    rcases e with _ | e
    · simp
    · simp [PowerSeries.coeff_one, PowerSeries.coeff_X]

/-- The indicator of `k`-th powers. -/
noncomputable def chi (k : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n ≠ 0 ∧ ∃ m : ℕ, m ^ k = n then 1 else 0, by simp⟩

lemma pow_iff {k n : ℕ} (hk : 0 < k) (hn : n ≠ 0) :
    (∃ m : ℕ, m ^ k = n) ↔ ∀ p ∈ n.factorization.support, k ∣ n.factorization p := by
  constructor
  · rintro ⟨m, rfl⟩ p _
    rw [Nat.factorization_pow]
    simp
  · intro h
    refine ⟨∏ p ∈ n.factorization.support, p ^ (n.factorization p / k), ?_⟩
    conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hn]
    rw [Finsupp.prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [← pow_mul, Nat.div_mul_cancel (h p hp)]

lemma chi_eq {k : ℕ} (hk : 0 < k) : chi k = E (Pk k) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [E_apply hn, Finsupp.prod]
  simp only [chi, ArithmeticFunction.coe_mk, Pk, PowerSeries.coeff_mk, Finset.prod_boole]
  simp only [hn, ne_eq, not_false_eq_true, true_and, pow_iff hk hn]

/-- `A322327` as an arithmetic function. -/
noncomputable def fAF : ArithmeticFunction ℤ := ⟨fun n => (a322327 n : ℤ), by simp [a322327]⟩

lemma fAF_eq : fAF = E Pf := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [E_apply hn, Finsupp.prod, Nat.support_factorization]
  simp only [fAF, ArithmeticFunction.coe_mk, a322327, hn, if_false, Nat.cast_prod]
  refine Finset.prod_congr rfl fun p hp => ?_
  have : n.factorization p ≠ 0 := by
    rw [← Finsupp.mem_support_iff, Nat.support_factorization]
    exact hp
  simp [Pf, this]

/-- `ζ` with integer values. -/
noncomputable def Z : ArithmeticFunction ℤ := (ArithmeticFunction.zeta : ArithmeticFunction ℤ)

/-- `μ`. -/
noncomputable def M : ArithmeticFunction ℤ := ArithmeticFunction.moebius

lemma r1 : Z * M = 1 := ArithmeticFunction.coe_zeta_mul_coe_moebius

lemma c1 : PowerSeries.coeff 0 (1 - PowerSeries.X : PowerSeries ℤ) = 1 := by simp

lemma c2 : PowerSeries.coeff 0 (1 + PowerSeries.X : PowerSeries ℤ) = 1 := by simp

lemma c3 (k : ℕ) (hk : 0 < k) :
    PowerSeries.coeff 0 (1 - PowerSeries.X ^ k : PowerSeries ℤ) = 1 := by
  simp [PowerSeries.coeff_X_pow, hk.ne']

lemma c4 : PowerSeries.coeff 0 (1 + PowerSeries.X ^ 2 : PowerSeries ℤ) = 1 := by
  simp [PowerSeries.coeff_X_pow]

lemma r2 : chi 2 * E (1 - PowerSeries.X ^ 2) = 1 := by
  rw [chi_eq (by norm_num), E_mul (coeff0_Pk 2) (c3 2 (by norm_num)), Pk_mul 2 (by norm_num), E_one]

lemma r4 : chi 4 * E (1 - PowerSeries.X ^ 4) = 1 := by
  rw [chi_eq (by norm_num), E_mul (coeff0_Pk 4) (c3 4 (by norm_num)), Pk_mul 4 (by norm_num), E_one]

lemma rf : fAF * (M * M) = E (1 + PowerSeries.X ^ 2) := by
  rw [fAF_eq, M, moebius_eq, E_mul c1 c1, E_mul coeff0_Pf, Pf_mul]
  simp

lemma p2 : E (1 - PowerSeries.X ^ 2) = M * musq := by
  rw [M, moebius_eq, musq_eq, E_mul c1 c2]
  congr 1
  ring

lemma p4 : E (1 - PowerSeries.X ^ 4) = E (1 - PowerSeries.X ^ 2) * E (1 + PowerSeries.X ^ 2) := by
  rw [E_mul (c3 2 (by norm_num)) c4]
  congr 1
  ring

/-- Twice the target function. -/
noncomputable def T : ArithmeticFunction ℤ := chi 4 * (M + musq)

lemma idA : Z * (Z * Z + chi 2) = T * fAF := by
  have h1 := r1
  have h2 := r2
  have h4 := r4
  have hf := rf
  have q2 := p2
  have q4 := p4
  unfold T
  generalize E (1 - PowerSeries.X ^ 2) = N2 at *
  generalize E (1 - PowerSeries.X ^ 4) = N4 at *
  generalize E (1 + PowerSeries.X ^ 2) = W at *
  generalize chi 2 = X2 at *
  generalize chi 4 = X4 at *
  generalize fAF = F at *
  generalize musq = S at *
  generalize Z = z at *
  generalize M = m at *
  have hF : F = W * z * z := by
    linear_combination (-(F * (z * m + 1))) * h1 + (z * z) * hf
  have hX : X2 = X4 * W := by
    linear_combination (-X2) * h4 + (X4 * W) * h2 + (X2 * X4) * q4
  have hS : S * X2 = z := by
    linear_combination z * h2 + (-(z * X2)) * q2 + (-(S * X2)) * h1
  rw [hF]
  linear_combination (-(z * z)) * hS + (-(z * X2)) * h1 + ((m + S) * z * z) * hX

lemma idB : (Z * (M + musq)) * (chi 4 * M) = T := by
  unfold T
  linear_combination ((M + musq) * chi 4) * r1

lemma prodQ (s : Finset ℕ) (u v : ℕ → ℤ)
    (h : ∀ i ∈ s, (u i = v i ∨ u i = -v i) ∧ (v i = 0 ∨ v i = 1)) :
    ((∏ i ∈ s, u i) = (∏ i ∈ s, v i) ∨ (∏ i ∈ s, u i) = -(∏ i ∈ s, v i)) ∧
      ((∏ i ∈ s, v i) = 0 ∨ (∏ i ∈ s, v i) = 1) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    refine ⟨?_, ?_⟩
    · rcases h1.1 with e1 | e1 <;> rcases h2.1 with e2 | e2 <;> rw [e1, e2]
      · left; ring
      · right; ring
      · right; ring
      · left; ring
    · rcases h1.2 with e1 | e1 <;> rcases h2.2 with e2 | e2 <;> rw [e1, e2] <;> simp

lemma T_val {n : ℕ} (hn : n ≠ 0) : T n = 0 ∨ T n = 2 := by
  have e : T = E (Pk 4 * (1 - PowerSeries.X ^ 1)) + E (Pk 4 * (1 + PowerSeries.X ^ 1)) := by
    rw [T, mul_add, chi_eq (by norm_num), M, moebius_eq, musq_eq, E_mul (coeff0_Pk 4) c1,
      E_mul (coeff0_Pk 4) c2, pow_one]
  rw [e, ArithmeticFunction.add_apply, E_apply hn, E_apply hn, Finsupp.prod, Finsupp.prod]
  have key := prodQ n.factorization.support
    (fun p => PowerSeries.coeff (n.factorization p) (Pk 4 * (1 - PowerSeries.X ^ 1)))
    (fun p => PowerSeries.coeff (n.factorization p) (Pk 4 * (1 + PowerSeries.X ^ 1))) (by
      intro p _
      generalize n.factorization p = k
      rw [mul_sub, mul_add, mul_one, map_sub, map_add, PowerSeries.coeff_mul_X_pow']
      simp only [Pk, PowerSeries.coeff_mk]
      by_cases h1 : 4 ∣ k <;> by_cases h2 : 1 ≤ k <;> by_cases h3 : 4 ∣ k - 1 <;>
        simp [h1, h2, h3] <;> omega)
  rcases key with ⟨h1 | h1, h2 | h2⟩ <;> rw [h1, h2] <;> simp

lemma fAF_one : fAF 1 = 1 := by simp [fAF, a322327]

lemma fAF_even {m : ℕ} (hm : 1 < m) : (2 : ℤ) ∣ fAF m := by
  obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.2 hm
  have h0 : m ≠ 0 := by omega
  have : (2 : ℕ) ∣ a322327 m := by
    simp only [a322327, h0, if_false]
    exact dvd_trans (dvd_mul_right 2 _) (Finset.dvd_prod_of_mem _ hp)
  simpa [fAF] using Int.natCast_dvd_natCast.2 this

lemma mod4 {n : ℕ} (hn : n ≠ 0) : ∃ k : ℤ, (T * fAF) n = T n + 4 * k := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal' (fun a b => T a * fAF b),
    ← Finset.add_sum_erase _ _ (Nat.one_mem_divisors.2 hn), Nat.div_one, fAF_one, mul_one]
  have : (4 : ℤ) ∣ ∑ d ∈ n.divisors.erase 1, T (n / d) * fAF d := by
    refine Finset.dvd_sum fun d hd => ?_
    rw [Finset.mem_erase, Nat.mem_divisors] at hd
    have hd0 : d ≠ 0 := fun h => hn (by rw [h] at hd; simpa using hd.2.1)
    have h2 := fAF_even (m := d) (by omega)
    have hq : n / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd.2.1)
      (Nat.pos_of_ne_zero hd0)).ne'
    obtain ⟨c, hc⟩ := h2
    rcases T_val hq with h | h <;> rw [h, hc]
    · simp
    · exact ⟨c, by ring⟩
  obtain ⟨k, hk⟩ := this
  exact ⟨k, by rw [hk]⟩

lemma inv_count (D : Finset ℕ) (σ : ℕ → ℕ) (hσ : ∀ d ∈ D, σ d ∈ D)
    (hσσ : ∀ d ∈ D, σ (σ d) = d) :
    2 * (D.filter (fun d => d ≤ σ d)).card = D.card + (D.filter (fun d => d = σ d)).card := by
  have hbij : (D.filter (fun d => σ d ≤ d)).card = (D.filter (fun d => d ≤ σ d)).card := by
    refine Finset.card_bij (fun d _ => σ d) ?_ ?_ ?_
    · intro d hd
      rw [Finset.mem_filter] at hd ⊢
      exact ⟨hσ d hd.1, by rw [hσσ d hd.1]; exact hd.2⟩
    · intro a ha b hb h
      rw [Finset.mem_filter] at ha hb
      rw [← hσσ a ha.1, ← hσσ b hb.1, h]
    · intro b hb
      rw [Finset.mem_filter] at hb
      exact ⟨σ b, Finset.mem_filter.2 ⟨hσ b hb.1, by rw [hσσ b hb.1]; exact hb.2⟩, hσσ b hb.1⟩
  have hu : D.filter (fun d => d ≤ σ d) ∪ D.filter (fun d => σ d ≤ d) = D := by
    ext d
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      rcases le_total d (σ d) with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
  have hi : D.filter (fun d => d ≤ σ d) ∩ D.filter (fun d => σ d ≤ d)
      = D.filter (fun d => d = σ d) := by
    ext d
    simp only [Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1.1, le_antisymm h1.2 h2.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2.le⟩, h1, h2.ge⟩
  have := Finset.card_union_add_card_inter (D.filter (fun d => d ≤ σ d))
    (D.filter (fun d => σ d ≤ d))
  rw [hu, hi, hbij] at this
  omega

lemma ZZ_apply {n : ℕ} : (Z * Z) n = (n.divisors.card : ℤ) := by
  rw [Z, ArithmeticFunction.coe_zeta_mul_apply, Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, this]

lemma div_mem {n d : ℕ} (hn : n ≠ 0) (hd : d ∈ n.divisors) : n / d ∈ n.divisors :=
  Nat.mem_divisors.2 ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), hn⟩

lemma two_s {n : ℕ} (hn : n ≠ 0) : 2 * (a038548 n : ℤ) = (Z * Z) n + chi 2 n := by
  have h := inv_count n.divisors (fun d => n / d) (fun d hd => div_mem hn hd)
    (fun d hd => Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hn)
  have e1 : n.divisors.filter (fun d => d ≤ n / d) = n.divisors.filter (fun d => d * d ≤ n) := by
    refine Finset.filter_congr fun d hd => ?_
    exact Nat.le_div_iff_mul_le (Nat.pos_of_mem_divisors hd)
  have e2 : ((n.divisors.filter (fun d => d = n / d)).card : ℤ) = chi 2 n := by
    simp only [chi, ArithmeticFunction.coe_mk, hn, ne_eq, not_false_eq_true, true_and]
    split_ifs with hm
    · obtain ⟨m, rfl⟩ := hm
      have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
      have : (m ^ 2).divisors.filter (fun d => d = m ^ 2 / d) = {m} := by
        ext d
        simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨hd, _⟩, h⟩
          have h2 : d * d = m * m := by
            nth_rewrite 2 [h]
            rw [Nat.mul_div_cancel' hd, sq]
          exact Nat.mul_self_inj.1 h2
        · rintro rfl
          exact ⟨⟨dvd_pow_self d two_ne_zero, hn⟩, by rw [sq, Nat.mul_div_cancel _ hm0]⟩
      rw [this]
      simp
    · have : n.divisors.filter (fun d => d = n / d) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro d hd h
        apply hm
        refine ⟨d, ?_⟩
        rw [sq]
        nth_rewrite 2 [h]
        exact Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
      rw [this]
      simp
  rw [ZZ_apply, ← e2]
  unfold a038548
  rw [← e1]
  exact_mod_cast h

/-- The unitary divisors of `n`. -/
def Uset (n : ℕ) : Finset ℕ := n.divisors.filter (fun d => Nat.Coprime d (n / d))

lemma U_card {n : ℕ} (hn : n ≠ 0) : (Uset n).card = 2 ^ n.primeFactors.card := by
  have hprod : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
    have := Nat.prod_factorization_pow_eq_self hn
    rwa [Finsupp.prod, Nat.support_factorization] at this
  have g1 : ∀ S ⊆ n.primeFactors, (∏ p ∈ S, p ^ n.factorization p) *
      (∏ p ∈ n.primeFactors \ S, p ^ n.factorization p) = n := by
    intro S hS
    rw [mul_comm, Finset.prod_sdiff hS, hprod]
  have g2 : ∀ S ⊆ n.primeFactors, Nat.Coprime (∏ p ∈ S, p ^ n.factorization p)
      (∏ p ∈ n.primeFactors \ S, p ^ n.factorization p) := by
    intro S hS
    refine Nat.Coprime.prod_left fun p hp => Nat.Coprime.prod_right fun q hq => ?_
    have hpp := Nat.prime_of_mem_primeFactors (hS hp)
    have hqp := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.1 hq).1
    have hne : p ≠ q := by
      rintro rfl
      exact (Finset.mem_sdiff.1 hq).2 hp
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hpp hqp).2 hne)
  have g3 : ∀ S ⊆ n.primeFactors, ∀ p ∈ n.primeFactors,
      (p ∣ ∏ q ∈ S, q ^ n.factorization q) → p ∈ S := by
    intro S hS p hp h
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hv : n.factorization p ≠ 0 := by
      rw [← Finsupp.mem_support_iff, Nat.support_factorization]
      exact hp
    by_contra hpS
    have h' : p ∣ ∏ q ∈ n.primeFactors \ S, q ^ n.factorization q :=
      dvd_trans (dvd_pow_self p hv) (Finset.dvd_prod_of_mem _ (Finset.mem_sdiff.2 ⟨hp, hpS⟩))
    have h1 := Nat.dvd_gcd h h'
    rw [Nat.Coprime.gcd_eq_one (g2 S hS)] at h1
    exact hpp.one_lt.ne' (Nat.dvd_one.1 h1)
  have g4 : ∀ S ⊆ n.primeFactors, ∀ p ∈ S, p ∣ ∏ q ∈ S, q ^ n.factorization q := by
    intro S hS p hp
    have hv : n.factorization p ≠ 0 := by
      rw [← Finsupp.mem_support_iff, Nat.support_factorization]
      exact hS hp
    exact dvd_trans (dvd_pow_self p hv) (Finset.dvd_prod_of_mem _ hp)
  have himg : (n.primeFactors.powerset).image (fun S => ∏ p ∈ S, p ^ n.factorization p)
      = Uset n := by
    ext d
    simp only [Finset.mem_image, Finset.mem_powerset, Uset, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨S, hS, rfl⟩
      have h1 := g1 S hS
      have hpos : 0 < ∏ p ∈ S, p ^ n.factorization p :=
        Nat.pos_of_ne_zero (fun h => hn (by rw [← h1, h, zero_mul]))
      have hdiv : n / (∏ p ∈ S, p ^ n.factorization p)
          = ∏ p ∈ n.primeFactors \ S, p ^ n.factorization p :=
        Nat.div_eq_of_eq_mul_right hpos h1.symm
      exact ⟨⟨Dvd.intro _ h1, hn⟩, by rw [hdiv]; exact g2 S hS⟩
    · rintro ⟨⟨hd, _⟩, hc⟩
      have hd0 : d ≠ 0 := fun h => hn (by rw [h] at hd; exact Nat.eq_zero_of_zero_dvd hd)
      have hq0 : n / d ≠ 0 :=
        (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd) (Nat.pos_of_ne_zero hd0)).ne'
      refine ⟨d.primeFactors, Nat.primeFactors_mono hd hn, ?_⟩
      have hd' : ∏ p ∈ d.primeFactors, p ^ d.factorization p = d := by
        have := Nat.prod_factorization_pow_eq_self hd0
        rwa [Finsupp.prod, Nat.support_factorization] at this
      conv_rhs => rw [← hd']
      refine Finset.prod_congr rfl fun p hp => ?_
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
      have hnq : ¬ p ∣ n / d := by
        intro h
        have h1 := Nat.dvd_gcd hpd h
        rw [Nat.Coprime.gcd_eq_one hc] at h1
        exact hpp.one_lt.ne' (Nat.dvd_one.1 h1)
      have e : n.factorization p = d.factorization p + (n / d).factorization p := by
        conv_lhs => rw [← Nat.mul_div_cancel' hd, Nat.factorization_mul hd0 hq0]
        rfl
      rw [e, Nat.factorization_eq_zero_of_not_dvd hnq, add_zero]
  rw [← himg, Finset.card_image_of_injOn, Finset.card_powerset]
  intro S hS S' hS' h
  have hS1 : S ⊆ n.primeFactors := Finset.mem_powerset.1 hS
  have hS2 : S' ⊆ n.primeFactors := Finset.mem_powerset.1 hS'
  simp only at h
  ext p
  constructor
  · intro hp
    exact g3 S' hS2 p (hS1 hp) (h ▸ g4 S hS1 p hp)
  · intro hp
    exact g3 S hS1 p (hS2 hp) (h ▸ g4 S' hS2 p hp)

lemma Z_eq : Z = E (Pk 1) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [E_apply hn, Finsupp.prod]
  simp [Z, Pk, ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hn]

lemma Zmusq_apply {n : ℕ} (hn : n ≠ 0) : (Z * musq) n = 2 ^ n.primeFactors.card := by
  rw [Z_eq, musq_eq, E_mul (coeff0_Pk 1) c2, E_apply hn, Finsupp.prod, Nat.support_factorization,
    ← Finset.prod_const]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hv : n.factorization p ≠ 0 := by
    rw [← Finsupp.mem_support_iff, Nat.support_factorization]
    exact hp
  obtain ⟨k, hk⟩ : ∃ k, n.factorization p = k + 1 := ⟨n.factorization p - 1, by omega⟩
  rw [hk, mul_add, mul_one, map_add, PowerSeries.coeff_succ_mul_X]
  simp [Pk]

lemma two_c {n : ℕ} (hn : n ≠ 0) : 2 * (a007875 n : ℤ) = (Z * (M + musq)) n := by
  have hσ : ∀ d ∈ Uset n, n / d ∈ Uset n := by
    intro d hd
    rw [Uset, Finset.mem_filter] at hd ⊢
    refine ⟨div_mem hn hd.1, ?_⟩
    rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd.1) hn]
    exact hd.2.symm
  have h := inv_count (Uset n) (fun d => n / d) hσ
    (fun d hd => Nat.div_div_self (Nat.dvd_of_mem_divisors (Finset.mem_filter.1 hd).1) hn)
  have e1 : (Uset n).filter (fun d => d ≤ n / d)
      = n.divisors.filter (fun d => d ≤ n / d ∧ Nat.Coprime d (n / d)) := by
    rw [Uset, Finset.filter_filter]
    refine Finset.filter_congr fun d _ => ?_
    exact and_comm
  have e2 : ((Uset n).filter (fun d => d = n / d)).card = if n = 1 then 1 else 0 := by
    split_ifs with h1
    · subst h1
      rfl
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro d hd h'
      rw [Uset, Finset.mem_filter] at hd
      have hc := hd.2
      rw [← h', Nat.coprime_self] at hc
      apply h1
      have := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd.1)
      rw [← h', hc] at this
      omega
  rw [mul_add, r1, ArithmeticFunction.add_apply, Zmusq_apply hn, ArithmeticFunction.one_apply]
  unfold a007875
  rw [← e1]
  rw [e2, U_card hn] at h
  split_ifs at h ⊢ <;>
  · have h' := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h'
    linarith

/-- `A355837` as an arithmetic function. -/
noncomputable def invAF : ArithmeticFunction ℤ := ⟨a355837, by rw [a355837]; simp⟩

lemma f_inv : fAF * invAF = 1 := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rcases eq_or_ne n 1 with rfl | h1
  · rw [ArithmeticFunction.mul_apply_one, fAF_one]
    simp only [invAF, ArithmeticFunction.coe_mk, one_mul, ArithmeticFunction.one_apply]
    rw [a355837]
    simp
  · rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal' (fun a b => fAF a * invAF b),
      ← Finset.add_sum_erase _ _ (Nat.mem_divisors_self n hn), Nat.div_self (Nat.pos_of_ne_zero hn),
      fAF_one, one_mul, ArithmeticFunction.one_apply_ne h1]
    have : invAF n = - ∑ d ∈ n.divisors.erase n, fAF (n / d) * invAF d := by
      simp only [invAF, fAF, ArithmeticFunction.coe_mk]
      rw [a355837]
      simp only [hn, h1, dif_neg, if_false, not_false_eq_true]
      rw [← Finset.sum_attach (n.divisors.erase n) (fun d => (a322327 (n / d) : ℤ) * a355837 d)]
    rw [this]
    ring

lemma g_eq (n : ℕ) : a219009 n = (chi 4 * M) n := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => chi 4 a * M b)]
  unfold a219009
  refine Finset.sum_congr rfl fun d hd => ?_
  have : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  simp only [chi, ArithmeticFunction.coe_mk, this, ne_eq, not_false_eq_true, true_and, M]
  congr

lemma two_A (m : ℕ) : 2 * (a140773 m : ℤ) = (Z * (Z * Z + chi 2)) m := by
  conv_rhs => rw [Z, ArithmeticFunction.coe_zeta_mul_apply]
  unfold a140773
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [ArithmeticFunction.add_apply]
  exact two_s (Nat.pos_of_mem_divisors hd).ne'

end OMA.S_oeis_a369255

open OMA.S_oeis_a369255 in
theorem OMA.solution : type_of% @OMA.S_oeis_a369255.main := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have h1 : 2 * (∑ d ∈ n.divisors, (a007875 d : ℤ) * a219009 (n / d)) = T n := by
    rw [← idB, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun a b => (Z * (M + musq)) a * (chi 4 * M) b),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [← mul_assoc, two_c (Nat.pos_of_mem_divisors hd).ne', g_eq]
  have h2 : 2 * (∑ d ∈ n.divisors, (a140773 d : ℤ) * a355837 (n / d)) = T n := by
    have e : T = (Z * (Z * Z + chi 2)) * invAF := by
      rw [idA, mul_assoc, f_inv, mul_one]
    rw [e, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun a b => (Z * (Z * Z + chi 2)) a * invAF b),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← mul_assoc, two_A]
    rfl
  obtain ⟨k, hk⟩ := mod4 hn0
  rw [← idA, ← two_A n] at hk
  have hT := T_val hn0
  have ha : (a n : ℤ) = (a140773 n : ℤ) % 2 := by simp [a]
  constructor <;> omega
