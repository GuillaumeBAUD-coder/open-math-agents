import OMAStatements.S_oeis_a143138
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Log
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace A143138Proof

open OMA.S_oeis_a143138 Polynomial

lemma dvd_prod_of_subset {α : Type*} [DecidableEq α] (s t : Finset α) (f : α → ℕ)
    (h : s ⊆ t) : (∏ x ∈ s, f x) ∣ (∏ x ∈ t, f x) := by
  refine ⟨∏ x ∈ t \ s, f x, ?_⟩
  rw [mul_comm, Finset.prod_sdiff h]

def wWeight (j : ℕ) : ℕ := (2 * j).factorial / j.factorial

lemma factorial_add_eq_mul_prod (j m : ℕ) :
    (j + m).factorial = j.factorial * ∏ x ∈ Finset.Ico (j + 1) (j + m + 1), x := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : j + (m + 1) = (j + m) + 1 := by omega
    rw [h1, Nat.factorial_succ, ih, Finset.prod_Ico_succ_top (by omega : j + 1 ≤ j + m + 1)]
    ring

lemma wWeight_eq_prod (j : ℕ) :
    wWeight j = ∏ x ∈ Finset.Ico (j + 1) (2 * j + 1), x := by
  unfold wWeight
  have h2 : 2 * j = j + j := by omega
  rw [h2, factorial_add_eq_mul_prod j j, Nat.mul_div_right _ (Nat.factorial_pos j)]

lemma pow_dvd_wWeight {p : ℕ} (hp : 2 ≤ p) :
    ∀ t j : ℕ, p ^ t ≤ 2 * j → p ^ t ∣ wWeight j
  | 0, j, _ => by simp
  | t + 1, j, hle => by
    rw [wWeight_eq_prod]
    by_cases hj : j < p ^ (t + 1)
    · apply Finset.dvd_prod_of_mem
      rw [Finset.mem_Ico]
      omega
    · push Not at hj
      set a := j / p
      have hp0 : 0 < p := by omega
      have hpa : p ^ t ≤ a := by
        rw [Nat.le_div_iff_mul_le hp0]
        simpa [pow_succ] using hj
      have ha1 : 1 ≤ a := le_trans (Nat.one_le_pow t p hp0) hpa
      have ih := pow_dvd_wWeight hp t a (by omega)
      rw [wWeight_eq_prod] at ih
      have hsub : (Finset.Ico (a + 1) (2 * a + 1)).image (fun y => p * y) ⊆
          Finset.Ico (j + 1) (2 * j + 1) := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
        rw [Finset.mem_Ico] at hy ⊢
        have hlt : j < p * (a + 1) := by
          have hmod : p * a + j % p = j := Nat.div_add_mod j p
          have hrem : j % p < p := Nat.mod_lt j hp0
          nlinarith
        have hup : p * a ≤ j := Nat.mul_div_le j p
        constructor <;> nlinarith
      have hdvd1 := dvd_prod_of_subset _ _ (fun x => x) hsub
      rw [Finset.prod_image (fun y _ z _ hyz => Nat.eq_of_mul_eq_mul_left hp0 hyz)] at hdvd1
      rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico] at hdvd1
      have hcard : 2 * a + 1 - (a + 1) = a := by omega
      rw [hcard] at hdvd1
      have hp_dvd_pa : p ∣ p ^ a := dvd_pow_self p (by omega)
      have hmul : p * p ^ t ∣ p ^ a * ∏ x ∈ Finset.Ico (a + 1) (2 * a + 1), x :=
        mul_dvd_mul hp_dvd_pa ih
      rw [pow_succ']
      exact dvd_trans hmul hdvd1

lemma prime_dvd_factorial {p n : ℕ} (hp : p.Prime) : p ∣ n.factorial ↔ p ≤ n := by
  induction n with
  | zero =>
    simp only [Nat.factorial_zero, Nat.dvd_one, Nat.le_zero]
    have := hp.two_le
    omega
  | succ n ih =>
    rw [Nat.factorial_succ, hp.dvd_mul, ih]
    constructor
    · rintro (h1 | h2)
      · exact Nat.le_of_dvd (by omega) h1
      · omega
    · intro hle
      by_cases h : p ≤ n
      · exact Or.inr h
      · have heq : p = n + 1 := by omega
        exact Or.inl (heq ▸ dvd_refl p)

lemma prime_dvd_choose {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    p ∣ p.choose k := by
  have hmul : p.choose k * k.factorial * (p - k).factorial = p.factorial :=
    Nat.choose_mul_factorial_mul_factorial (le_of_lt hkp)
  have hpf : p ∣ p.factorial := (prime_dvd_factorial hp).mpr (le_refl p)
  rw [← hmul, mul_assoc] at hpf
  have hcop1 : p.Coprime k.factorial :=
    hp.coprime_iff_not_dvd.mpr fun hd => Nat.not_le_of_gt hkp ((prime_dvd_factorial hp).mp hd)
  have hcop2 : p.Coprime (p - k).factorial :=
    hp.coprime_iff_not_dvd.mpr fun hd =>
      Nat.not_le_of_gt (by omega : p - k < p) ((prime_dvd_factorial hp).mp hd)
  exact (hcop1.mul_right hcop2).dvd_of_dvd_mul_right hpf

lemma fermat_little_nat {p : ℕ} (hp : p.Prime) (x : ℕ) : p ∣ x ^ p - x := by
  induction x with
  | zero =>
    rw [zero_pow hp.ne_zero]
    simp
  | succ x ih =>
    have hge : x ≤ x ^ p := Nat.le_self_pow hp.ne_zero x
    have hpow : (x + 1) ^ p = ∑ i ∈ Finset.range (p + 1), p.choose i * x ^ i := by
      rw [add_pow]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [one_pow, mul_one, Nat.cast_id]
      exact mul_comm _ _
    have hmid : p ∣ ∑ i ∈ Finset.range (p - 1), p.choose (i + 1) * x ^ (i + 1) := by
      apply Finset.dvd_sum
      intro i hi
      rw [Finset.mem_range] at hi
      exact dvd_mul_of_dvd_left (prime_dvd_choose hp (by omega) (by omega)) _
    have hp2 : 2 ≤ p := hp.two_le
    have hsplit : (∑ i ∈ Finset.range (p + 1), p.choose i * x ^ i) =
        x ^ p + 1 + ∑ i ∈ Finset.range (p - 1), p.choose (i + 1) * x ^ (i + 1) := by
      rw [Finset.sum_range_succ]
      have hp1 : p = (p - 1) + 1 := by omega
      conv_lhs => enter [1, 1]; rw [hp1]
      rw [Finset.sum_range_succ']
      simp [Nat.choose_self, Nat.choose_zero_right]
      ring
    have hsub : (x + 1) ^ p - (x + 1) =
        (x ^ p - x) + ∑ i ∈ Finset.range (p - 1), p.choose (i + 1) * x ^ (i + 1) := by
      rw [hpow, hsplit]
      omega
    rw [hsub]
    exact dvd_add ih hmid

lemma pow_eq_sum_stirlingSecond (n x : ℕ) :
    x ^ n = ∑ r ∈ Finset.range (n + 1), r.factorial * x.choose r * Nat.stirlingSecond n r := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmul : x ^ (n + 1) =
        ∑ r ∈ Finset.range (n + 1), (r.factorial * x.choose r * Nat.stirlingSecond n r) * x := by
      rw [pow_succ, ih, Finset.sum_mul]
    have hterm : ∀ r : ℕ, (r.factorial * x.choose r * Nat.stirlingSecond n r) * x =
        r.factorial * x.choose r * (r * Nat.stirlingSecond n r) +
        (r + 1).factorial * x.choose (r + 1) * Nat.stirlingSecond n r := by
      intro r
      by_cases hrx : r ≤ x
      · have hch : (x - r) * x.choose r = (r + 1) * x.choose (r + 1) := by
          have := Nat.choose_succ_right_eq x r
          linarith
        have hsplitx : Nat.stirlingSecond n r * x =
            Nat.stirlingSecond n r * r + Nat.stirlingSecond n r * (x - r) := by
          rw [← mul_add, Nat.add_sub_of_le hrx]
        calc
          (r.factorial * x.choose r * Nat.stirlingSecond n r) * x
              = r.factorial * x.choose r * (Nat.stirlingSecond n r * x) := by ring
          _ = r.factorial * x.choose r * (Nat.stirlingSecond n r * r) +
              r.factorial * ((x - r) * x.choose r) * Nat.stirlingSecond n r := by
                rw [hsplitx]; ring
          _ = r.factorial * x.choose r * (r * Nat.stirlingSecond n r) +
              (r + 1).factorial * x.choose (r + 1) * Nat.stirlingSecond n r := by
                rw [hch, Nat.factorial_succ]; ring
      · push Not at hrx
        rw [Nat.choose_eq_zero_of_lt hrx, Nat.choose_eq_zero_of_lt (by omega : x < r + 1)]
        simp
    rw [hmul, Finset.sum_congr rfl fun r _ => hterm r, Finset.sum_add_distrib]
    have hleft : (∑ r ∈ Finset.range (n + 1), r.factorial * x.choose r * (r * Nat.stirlingSecond n r)) =
        ∑ r ∈ Finset.range (n + 1),
          (r + 1).factorial * x.choose (r + 1) * ((r + 1) * Nat.stirlingSecond n (r + 1)) := by
      rw [Finset.sum_range_succ' _ n]
      simp only [zero_mul, mul_zero, add_zero]
      rw [Finset.sum_range_succ _ n]
      rw [Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self n)]
      simp only [mul_zero, add_zero]
    rw [hleft, ← Finset.sum_add_distrib]
    rw [Finset.sum_range_succ' _ (n + 1)]
    simp only [Nat.stirlingSecond_succ_zero, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Nat.stirlingSecond_succ_succ]
    ring

lemma prime_dvd_stirlingSecond {p r : ℕ} (hp : p.Prime) (hr1 : 1 < r) (hrp : r < p) :
    p ∣ Nat.stirlingSecond p r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    have hpow := pow_eq_sum_stirlingSecond p r
    have htrunc : (∑ k ∈ Finset.range (p + 1), k.factorial * r.choose k * Nat.stirlingSecond p k) =
        ∑ k ∈ Finset.range (r + 1), k.factorial * r.choose k * Nat.stirlingSecond p k := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro k _ hkr
      rw [Finset.mem_range, not_lt] at hkr
      rw [Nat.choose_eq_zero_of_lt hkr]
      simp
    rw [htrunc] at hpow
    rw [Finset.sum_range_succ] at hpow
    have hp0 : p = (p - 1) + 1 := by omega
    have hs0 : Nat.stirlingSecond p 0 = 0 := by rw [hp0]; exact Nat.stirlingSecond_succ_zero _
    have hs1 : Nat.stirlingSecond p 1 = 1 := by rw [hp0]; exact Nat.stirlingSecond_one_right _
    have hlow : (∑ k ∈ Finset.range r, k.factorial * r.choose k * Nat.stirlingSecond p k) =
        r + ∑ j ∈ Finset.range (r - 2),
          (j + 2).factorial * r.choose (j + 2) * Nat.stirlingSecond p (j + 2) := by
      have hr2 : r = (r - 2) + 1 + 1 := by omega
      conv_lhs => enter [1, 1]; rw [hr2]
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      simp [hs0, hs1, Nat.choose_one_right]
      ring
    rw [hlow, Nat.choose_self, mul_one] at hpow
    have hmid : p ∣ ∑ j ∈ Finset.range (r - 2),
        (j + 2).factorial * r.choose (j + 2) * Nat.stirlingSecond p (j + 2) := by
      apply Finset.dvd_sum
      intro j hj
      rw [Finset.mem_range] at hj
      exact dvd_mul_of_dvd_right (ih (j + 2) (by omega) (by omega) (by omega)) _
    have hfermat := fermat_little_nat hp r
    have hsub : r ^ p - r =
        (∑ j ∈ Finset.range (r - 2),
          (j + 2).factorial * r.choose (j + 2) * Nat.stirlingSecond p (j + 2)) +
        r.factorial * Nat.stirlingSecond p r := by
      omega
    rw [hsub] at hfermat
    have hdvd_prod : p ∣ r.factorial * Nat.stirlingSecond p r :=
      (Nat.dvd_add_right hmid).mp hfermat
    have hcop : p.Coprime r.factorial :=
      hp.coprime_iff_not_dvd.mpr fun hd => Nat.not_le_of_gt hrp ((prime_dvd_factorial hp).mp hd)
    exact hcop.dvd_of_dvd_mul_left hdvd_prod

noncomputable def applyPoly (P : Polynomial ℤ) (f : ℕ → ℤ) (m : ℕ) : ℤ :=
  P.sum fun i a => a * f (m + i)

lemma applyPoly_zero (f : ℕ → ℤ) (m : ℕ) : applyPoly 0 f m = 0 :=
  Polynomial.sum_zero_index _

lemma applyPoly_zero_seq (P : Polynomial ℤ) (m : ℕ) : applyPoly P (fun _ => 0) m = 0 := by
  unfold applyPoly
  simp [Polynomial.sum_def]

lemma applyPoly_add (P Q : Polynomial ℤ) (f : ℕ → ℤ) (m : ℕ) :
    applyPoly (P + Q) f m = applyPoly P f m + applyPoly Q f m :=
  Polynomial.sum_add_index P Q _ (fun _ => zero_mul _) (fun _ a1 a2 => add_mul a1 a2 _)

lemma applyPoly_neg (P : Polynomial ℤ) (f : ℕ → ℤ) (m : ℕ) :
    applyPoly (-P) f m = -applyPoly P f m := by
  have h := applyPoly_add P (-P) f m
  rw [add_neg_cancel, applyPoly_zero] at h
  linarith

lemma applyPoly_sub (P Q : Polynomial ℤ) (f : ℕ → ℤ) (m : ℕ) :
    applyPoly (P - Q) f m = applyPoly P f m - applyPoly Q f m := by
  rw [sub_eq_add_neg, applyPoly_add, applyPoly_neg, sub_eq_add_neg]

lemma applyPoly_monomial (d : ℕ) (c : ℤ) (f : ℕ → ℤ) (m : ℕ) :
    applyPoly (Polynomial.monomial d c) f m = c * f (m + d) :=
  Polynomial.sum_monomial_index c _ (zero_mul _)

lemma applyPoly_C (c : ℤ) (f : ℕ → ℤ) (m : ℕ) :
    applyPoly (Polynomial.C c) f m = c * f m :=
  (Polynomial.sum_C_index (f := fun i a => a * f (m + i)) (zero_mul _)).trans (by simp)

lemma applyPoly_X_pow (d : ℕ) (f : ℕ → ℤ) (m : ℕ) :
    applyPoly (Polynomial.X ^ d) f m = f (m + d) := by
  rw [Polynomial.X_pow_eq_monomial, applyPoly_monomial, one_mul]

lemma applyPoly_X (f : ℕ → ℤ) (m : ℕ) :
    applyPoly Polynomial.X f m = f (m + 1) := by
  simpa using applyPoly_X_pow 1 f m

lemma applyPoly_one (f : ℕ → ℤ) (m : ℕ) :
    applyPoly 1 f m = f m := by
  simpa using applyPoly_X_pow 0 f m

lemma applyPoly_mul (P Q : Polynomial ℤ) (f : ℕ → ℤ) (m : ℕ) :
    applyPoly (P * Q) f m = applyPoly P (applyPoly Q f) m := by
  induction P using Polynomial.induction_on' with
  | add P1 P2 ih1 ih2 =>
    rw [add_mul, applyPoly_add, applyPoly_add, ih1, ih2]
  | monomial d c =>
    rw [applyPoly_monomial]
    induction Q using Polynomial.induction_on' with
    | add Q1 Q2 ihQ1 ihQ2 =>
      have hfun : applyPoly (Q1 + Q2) f = fun n => applyPoly Q1 f n + applyPoly Q2 f n := by
        ext n; exact applyPoly_add Q1 Q2 f n
      rw [mul_add, applyPoly_add, ihQ1, ihQ2, hfun]
      dsimp only
      ring
    | monomial i b =>
      rw [Polynomial.monomial_mul_monomial, applyPoly_monomial]
      have hfun : applyPoly (Polynomial.monomial i b) f = fun n => b * f (n + i) := by
        ext n; exact applyPoly_monomial i b f n
      rw [hfun]
      dsimp only
      have hadd : m + (d + i) = m + d + i := by omega
      rw [hadd]
      ring

lemma dvd_applyPoly_C_mul (q : ℤ) (W : Polynomial ℤ) (f : ℕ → ℤ) (m : ℕ) :
    q ∣ applyPoly (Polynomial.C q * W) f m := by
  rw [applyPoly_mul, applyPoly_C]
  exact dvd_mul_right q _

noncomputable def fallFact : ℕ → Polynomial ℤ
  | 0 => 1
  | k + 1 => fallFact k * (Polynomial.X - Polynomial.C (k : ℤ))

def stirlingSeq (r m : ℕ) : ℤ := (Nat.stirlingSecond m r : ℤ)

lemma applyPoly_fallFact_stirlingSeq (r : ℕ) :
    applyPoly (fallFact (r + 1)) (stirlingSeq r) = fun _ => 0 := by
  induction r with
  | zero =>
    have hf1 : fallFact 1 = Polynomial.X := by
      simp [fallFact]
    rw [hf1]
    ext m
    rw [applyPoly_X]
    simp [stirlingSeq]
  | succ r ih =>
    ext m
    have hstep : applyPoly (Polynomial.X - Polynomial.C ((r + 1 : ℕ) : ℤ))
        (stirlingSeq (r + 1)) = stirlingSeq r := by
      ext n
      rw [applyPoly_sub, applyPoly_X, applyPoly_C]
      unfold stirlingSeq
      rw [Nat.stirlingSecond_succ_succ]
      push_cast
      ring
    change applyPoly (fallFact (r + 1) * (Polynomial.X - Polynomial.C ((r + 1 : ℕ) : ℤ)))
        (stirlingSeq (r + 1)) m = 0
    rw [applyPoly_mul, hstep, ih]

lemma fallFact_dvd_of_le {a b : ℕ} (h : a ≤ b) : fallFact a ∣ fallFact b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.add_succ]
    exact dvd_mul_of_dvd_left ih _

lemma applyPoly_fallFact_stirlingSeq_of_lt {r M : ℕ} (hr : r < M) :
    applyPoly (fallFact M) (stirlingSeq r) = fun _ => 0 := by
  rcases fallFact_dvd_of_le hr with ⟨Q, hQ⟩
  ext m
  rw [hQ, mul_comm, applyPoly_mul, applyPoly_fallFact_stirlingSeq, applyPoly_zero_seq]

lemma X_pow_eq_sum_stirling (n : ℕ) :
    (Polynomial.X : Polynomial ℤ) ^ n =
      ∑ r ∈ Finset.range (n + 1), Polynomial.C (Nat.stirlingSecond n r : ℤ) * fallFact r := by
  induction n with
  | zero => simp [fallFact]
  | succ n ih =>
    rw [pow_succ, ih, Finset.sum_mul]
    have hterm : ∀ r : ℕ,
        (Polynomial.C (Nat.stirlingSecond n r : ℤ) * fallFact r) * Polynomial.X =
          Polynomial.C ((r * Nat.stirlingSecond n r : ℕ) : ℤ) * fallFact r +
          Polynomial.C (Nat.stirlingSecond n r : ℤ) * fallFact (r + 1) := by
      intro r
      have hf : fallFact (r + 1) = fallFact r * (Polynomial.X - Polynomial.C (r : ℤ)) := rfl
      rw [hf]
      push_cast
      rw [map_mul]
      ring
    rw [Finset.sum_congr rfl fun r _ => hterm r, Finset.sum_add_distrib]
    have hleft : (∑ r ∈ Finset.range (n + 1),
          Polynomial.C ((r * Nat.stirlingSecond n r : ℕ) : ℤ) * fallFact r) =
        ∑ r ∈ Finset.range (n + 1),
          Polynomial.C (((r + 1) * Nat.stirlingSecond n (r + 1) : ℕ) : ℤ) * fallFact (r + 1) := by
      rw [Finset.sum_range_succ' _ n]
      simp only [zero_mul, Nat.cast_zero, map_zero, add_zero]
      rw [Finset.sum_range_succ _ n]
      rw [Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self n)]
      simp only [mul_zero, Nat.cast_zero, map_zero, zero_mul, add_zero]
    rw [hleft, ← Finset.sum_add_distrib]
    rw [Finset.sum_range_succ' _ (n + 1)]
    simp only [Nat.stirlingSecond_succ_zero, Nat.cast_zero, map_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Nat.stirlingSecond_succ_succ]
    push_cast
    simp only [map_add, map_mul, map_one]
    ring

def PolyMod (q : ℤ) (A B : Polynomial ℤ) : Prop :=
  ∃ W : Polynomial ℤ, A - B = Polynomial.C q * W

lemma PolyMod_refl (q : ℤ) (A : Polynomial ℤ) : PolyMod q A A :=
  ⟨0, by simp⟩

lemma PolyMod_symm {q : ℤ} {A B : Polynomial ℤ} (h : PolyMod q A B) : PolyMod q B A := by
  rcases h with ⟨W, hW⟩
  exact ⟨-W, by linear_combination -hW⟩

lemma PolyMod_trans {q : ℤ} {A B G : Polynomial ℤ}
    (h1 : PolyMod q A B) (h2 : PolyMod q B G) : PolyMod q A G := by
  rcases h1 with ⟨W1, hW1⟩
  rcases h2 with ⟨W2, hW2⟩
  exact ⟨W1 + W2, by linear_combination hW1 + hW2⟩

lemma PolyMod_mul {q : ℤ} {A1 B1 A2 B2 : Polynomial ℤ}
    (h1 : PolyMod q A1 B1) (h2 : PolyMod q A2 B2) : PolyMod q (A1 * A2) (B1 * B2) := by
  rcases h1 with ⟨W1, hW1⟩
  rcases h2 with ⟨W2, hW2⟩
  refine ⟨W1 * A2 + B1 * W2, ?_⟩
  linear_combination A2 * hW1 + B1 * hW2

lemma PolyMod_pow {q : ℤ} {A B : Polynomial ℤ} (h : PolyMod q A B) (n : ℕ) :
    PolyMod q (A ^ n) (B ^ n) := by
  induction n with
  | zero => simp [PolyMod_refl]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact PolyMod_mul ih h

lemma PolyMod_prod_range {q : ℤ} (m : ℕ) (f g : ℕ → Polynomial ℤ)
    (h : ∀ i < m, PolyMod q (f i) (g i)) :
    PolyMod q (∏ i ∈ Finset.range m, f i) (∏ i ∈ Finset.range m, g i) := by
  induction m with
  | zero => simp [PolyMod_refl]
  | succ m ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    exact PolyMod_mul (ih fun i hi => h i (by omega)) (h m (Nat.lt_succ_self m))

lemma fallFact_prime_mod {p : ℕ} (hp : p.Prime) :
    PolyMod (p : ℤ) (fallFact p) (Polynomial.X ^ p - Polynomial.X) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hx := X_pow_eq_sum_stirling p
  rw [Finset.sum_range_succ] at hx
  have hp0 : p = (p - 1) + 1 := by omega
  have hs0 : Nat.stirlingSecond p 0 = 0 := by rw [hp0]; exact Nat.stirlingSecond_succ_zero _
  have hs1 : Nat.stirlingSecond p 1 = 1 := by rw [hp0]; exact Nat.stirlingSecond_one_right _
  have hsp : Nat.stirlingSecond p p = 1 := Nat.stirlingSecond_self p
  have hlow : (∑ r ∈ Finset.range p, Polynomial.C (Nat.stirlingSecond p r : ℤ) * fallFact r) =
      Polynomial.X + ∑ j ∈ Finset.range (p - 2),
        Polynomial.C (Nat.stirlingSecond p (j + 2) : ℤ) * fallFact (j + 2) := by
    have hpr : p = (p - 2) + 1 + 1 := by omega
    conv_lhs => enter [1, 1]; rw [hpr]
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp [hs0, hs1, fallFact]
    ring
  rw [hlow, hsp, Nat.cast_one, map_one, one_mul] at hx
  have hmid : ∃ W : Polynomial ℤ,
      (∑ j ∈ Finset.range (p - 2),
        Polynomial.C (Nat.stirlingSecond p (j + 2) : ℤ) * fallFact (j + 2)) =
      Polynomial.C (p : ℤ) * W := by
    refine ⟨∑ j ∈ Finset.range (p - 2),
      Polynomial.C ((Nat.stirlingSecond p (j + 2) / p : ℕ) : ℤ) * fallFact (j + 2), ?_⟩
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hd := prime_dvd_stirlingSecond hp (by omega : 1 < j + 2) (by omega : j + 2 < p)
    have hmul_div : p * (Nat.stirlingSecond p (j + 2) / p) = Nat.stirlingSecond p (j + 2) :=
      Nat.mul_div_cancel' hd
    have hC : Polynomial.C (Nat.stirlingSecond p (j + 2) : ℤ) =
        Polynomial.C (p : ℤ) * Polynomial.C ((Nat.stirlingSecond p (j + 2) / p : ℕ) : ℤ) := by
      rw [← map_mul]
      congr 1
      exact_mod_cast hmul_div.symm
    rw [hC, mul_assoc]
  rcases hmid with ⟨W, hW⟩
  refine ⟨-W, ?_⟩
  linear_combination -hx - hW

lemma fallFact_add (a b : ℕ) :
    fallFact (a + b) =
      fallFact a * ∏ j ∈ Finset.range b, (Polynomial.X - Polynomial.C ((a + j : ℕ) : ℤ)) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.add_succ, fallFact, ih, Finset.prod_range_succ, mul_assoc]

lemma fallFact_mul_eq_prod (M p : ℕ) :
    fallFact (M * p) =
      ∏ k ∈ Finset.range M, ∏ j ∈ Finset.range p,
        (Polynomial.X - Polynomial.C ((k * p + j : ℕ) : ℤ)) := by
  induction M with
  | zero => simp [fallFact]
  | succ M ih =>
    rw [Nat.succ_mul, fallFact_add (M * p) p, ih, Finset.prod_range_succ]

lemma PolyMod_pow_prime {p : ℕ} (hp : p.Prime) (A B : Polynomial ℤ) :
    PolyMod (p : ℤ) ((A - B) ^ p) (A ^ p - B ^ p) := by
  rcases hp.eq_two_or_odd with rfl | hodd
  · refine ⟨B ^ 2 - A * B, ?_⟩
    push_cast
    rw [map_ofNat]
    ring
  · have hp2 : 2 ≤ p := hp.two_le
    have hodd' : Odd p := Nat.odd_iff.mpr hodd
    have hpow : (A - B) ^ p =
        ∑ i ∈ Finset.range (p + 1),
          Polynomial.C (p.choose i : ℤ) * A ^ i * (-B) ^ (p - i) := by
      have hsub : A - B = A + (-B) := sub_eq_add_neg A B
      rw [hsub, add_pow]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hcast : (p.choose i : Polynomial ℤ) = Polynomial.C (p.choose i : ℤ) := by simp
      rw [hcast]
      ring
    rw [Finset.sum_range_succ] at hpow
    have hp1 : p = (p - 1) + 1 := by have := hp.two_le; omega
    conv_rhs at hpow => enter [1, 1]; rw [hp1]
    rw [Finset.sum_range_succ'] at hpow
    have hnegB : (-B) ^ p = -(B ^ p) := hodd'.neg_pow B
    simp only [Nat.choose_self, Nat.cast_one, map_one, one_mul, Nat.sub_self, pow_zero, mul_one,
      Nat.choose_zero_right, Nat.sub_zero] at hpow
    rw [hnegB] at hpow
    refine ⟨∑ k ∈ Finset.range (p - 1),
        Polynomial.C ((p.choose (k + 1) / p : ℕ) : ℤ) *
          A ^ (k + 1) * (-B) ^ (p - (k + 1)), ?_⟩
    rw [Finset.mul_sum]
    have hsum : (∑ x ∈ Finset.range (p - 1),
          Polynomial.C (p.choose (x + 1) : ℤ) * A ^ (x + 1) * (-B) ^ (p - (x + 1))) =
        ∑ k ∈ Finset.range (p - 1),
          Polynomial.C (p : ℤ) *
            (Polynomial.C ((p.choose (k + 1) / p : ℕ) : ℤ) *
              A ^ (k + 1) * (-B) ^ (p - (k + 1))) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      have hd := prime_dvd_choose hp (by omega : 0 < k + 1) (by omega : k + 1 < p)
      have hC : Polynomial.C (p.choose (k + 1) : ℤ) =
          Polynomial.C (p : ℤ) * Polynomial.C ((p.choose (k + 1) / p : ℕ) : ℤ) := by
        rw [← map_mul]
        congr 1
        exact_mod_cast (Nat.mul_div_cancel' hd).symm
      rw [hC]
      ring
    linear_combination hpow + hsum

lemma PolyMod_pow_prime_pow {p : ℕ} (hp : p.Prime) (A B : Polynomial ℤ) (t : ℕ) :
    PolyMod (p : ℤ) ((A - B) ^ (p ^ t)) (A ^ (p ^ t) - B ^ (p ^ t)) := by
  induction t with
  | zero => simp [PolyMod_refl]
  | succ t ih =>
    rw [pow_succ, pow_mul]
    have h1 := PolyMod_pow ih p
    have h2 := PolyMod_pow_prime hp (A ^ (p ^ t)) (B ^ (p ^ t))
    rw [← pow_mul, ← pow_mul] at h2
    exact PolyMod_trans h1 h2

def ModIdeal (D : Polynomial ℤ) (q : ℤ) (P : Polynomial ℤ) : Prop :=
  ∃ Q W : Polynomial ℤ, P = D * Q + Polynomial.C q * W

lemma ModIdeal_add {D : Polynomial ℤ} {q : ℤ} {P1 P2 : Polynomial ℤ}
    (h1 : ModIdeal D q P1) (h2 : ModIdeal D q P2) : ModIdeal D q (P1 + P2) := by
  rcases h1 with ⟨Q1, W1, rfl⟩
  rcases h2 with ⟨Q2, W2, rfl⟩
  exact ⟨Q1 + Q2, W1 + W2, by ring⟩

lemma ModIdeal_sum {D : Polynomial ℤ} {q : ℤ} (m : ℕ) (f : ℕ → Polynomial ℤ)
    (h : ∀ i < m, ModIdeal D q (f i)) :
    ModIdeal D q (∑ i ∈ Finset.range m, f i) := by
  induction m with
  | zero => exact ⟨0, 0, by simp⟩
  | succ m ih =>
    rw [Finset.sum_range_succ]
    exact ModIdeal_add (ih fun i hi => h i (by omega)) (h m (Nat.lt_succ_self m))

lemma geom_sum_mul_sub_one (Y : Polynomial ℤ) (n : ℕ) :
    (∑ i ∈ Finset.range n, Y ^ i) * (Y - 1) = Y ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    ring

lemma fallFact_base_ideal {p : ℕ} (hp : p.Prime) (t : ℕ) :
    ModIdeal (fallFact (p ^ (t + 1))) (p : ℤ)
      (Polynomial.X ^ (p ^ t) * (Polynomial.X ^ ((p - 1) * p ^ t) - 1)) := by
  have hblock : ∀ k < p ^ t,
      PolyMod (p : ℤ)
        (∏ j ∈ Finset.range p, (Polynomial.X - Polynomial.C ((k * p + j : ℕ) : ℤ)))
        (Polynomial.X ^ p - Polynomial.X) := by
    intro k _
    have h1 : PolyMod (p : ℤ)
        (∏ j ∈ Finset.range p, (Polynomial.X - Polynomial.C ((k * p + j : ℕ) : ℤ)))
        (∏ j ∈ Finset.range p, (Polynomial.X - Polynomial.C (j : ℤ))) := by
      apply PolyMod_prod_range
      intro j _
      refine ⟨-Polynomial.C (k : ℤ), ?_⟩
      push_cast
      rw [map_add, map_mul]
      ring
    have hff : (∏ j ∈ Finset.range p, (Polynomial.X - Polynomial.C (j : ℤ))) = fallFact p := by
      simpa [fallFact] using (fallFact_add 0 p).symm
    rw [hff] at h1
    exact PolyMod_trans h1 (fallFact_prime_mod hp)
  have hprod := PolyMod_prod_range (p ^ t) _ _ hblock
  rw [Finset.prod_const, Finset.card_range, ← fallFact_mul_eq_prod (p ^ t) p] at hprod
  have hpt : p ^ t * p = p ^ (t + 1) := by rw [pow_succ]
  rw [hpt] at hprod
  have hfresh := PolyMod_pow_prime_pow hp (Polynomial.X ^ p) Polynomial.X t
  have hexp : (Polynomial.X ^ p : Polynomial ℤ) ^ (p ^ t) - Polynomial.X ^ (p ^ t) =
      Polynomial.X ^ (p ^ t) * (Polynomial.X ^ ((p - 1) * p ^ t) - 1) := by
    rw [← pow_mul]
    have hmul : p * p ^ t = p ^ t + (p - 1) * p ^ t := by
      have hp1 : 1 ≤ p := hp.one_le
      calc
        p * p ^ t = (1 + (p - 1)) * p ^ t := by congr 1; omega
        _ = p ^ t + (p - 1) * p ^ t := by ring
    rw [hmul, pow_add]
    ring
  rw [hexp] at hfresh
  have hmod := PolyMod_symm (PolyMod_trans hprod hfresh)
  rcases hmod with ⟨W, hW⟩
  refine ⟨1, W, ?_⟩
  linear_combination hW

lemma fallFact_lift_ideal {p : ℕ} (hp : p.Prime) (t b : ℕ) (hb : 1 ≤ b) :
    ModIdeal (fallFact (p ^ (t + 1))) ((p : ℤ) ^ b)
      ((Polynomial.X ^ (p ^ t)) ^ b *
        (Polynomial.X ^ ((p - 1) * p ^ (t + b - 1)) - 1)) := by
  set D := fallFact (p ^ (t + 1))
  set U0 : Polynomial ℤ := Polynomial.X ^ (p ^ t)
  set Z : Polynomial ℤ := Polynomial.X ^ ((p - 1) * p ^ t)
  have hbase : ModIdeal D (p : ℤ) (U0 * (Z - 1)) := fallFact_base_ideal hp t
  obtain ⟨m, rfl⟩ : ∃ m, b = m + 1 := ⟨b - 1, by omega⟩
  have hm_eq : ∀ k : ℕ, (Polynomial.X : Polynomial ℤ) ^ ((p - 1) * p ^ (t + k)) = Z ^ (p ^ k) := by
    intro k
    dsimp [Z]
    rw [← pow_mul]
    congr 1
    rw [pow_add]
    ring
  have hsub1 : t + (m + 1) - 1 = t + m := by omega
  rw [hsub1, hm_eq m]
  clear hb hsub1
  induction m with
  | zero =>
    simpa [pow_zero, pow_one] using hbase
  | succ m ih =>
    set Y := Z ^ (p ^ m)
    have hY_base : ModIdeal D (p : ℤ) (U0 * (Y - 1)) := by
      rcases hbase with ⟨Q0, W0, h0⟩
      have hdvd : Y - 1 = (∑ i ∈ Finset.range (p ^ m), Z ^ i) * (Z - 1) :=
        (geom_sum_mul_sub_one Z (p ^ m)).symm
      refine ⟨Q0 * ∑ i ∈ Finset.range (p ^ m), Z ^ i,
        W0 * ∑ i ∈ Finset.range (p ^ m), Z ^ i, ?_⟩
      calc
        U0 * (Y - 1) = (U0 * (Z - 1)) * ∑ i ∈ Finset.range (p ^ m), Z ^ i := by
          rw [hdvd]; ring
        _ = D * (Q0 * ∑ i ∈ Finset.range (p ^ m), Z ^ i) +
            Polynomial.C (p : ℤ) * (W0 * ∑ i ∈ Finset.range (p ^ m), Z ^ i) := by
          rw [h0]; ring
    have hYi : ∀ i < p, ModIdeal D (p : ℤ) (U0 * (Y ^ i - 1)) := by
      intro i _
      rcases hY_base with ⟨Q1, W1, h1⟩
      have hdvd : Y ^ i - 1 = (∑ j ∈ Finset.range i, Y ^ j) * (Y - 1) :=
        (geom_sum_mul_sub_one Y i).symm
      refine ⟨Q1 * ∑ j ∈ Finset.range i, Y ^ j, W1 * ∑ j ∈ Finset.range i, Y ^ j, ?_⟩
      calc
        U0 * (Y ^ i - 1) = (U0 * (Y - 1)) * ∑ j ∈ Finset.range i, Y ^ j := by
          rw [hdvd]; ring
        _ = D * (Q1 * ∑ j ∈ Finset.range i, Y ^ j) +
            Polynomial.C (p : ℤ) * (W1 * ∑ j ∈ Finset.range i, Y ^ j) := by
          rw [h1]; ring
    have hsum_mod : ModIdeal D (p : ℤ) (U0 * ∑ i ∈ Finset.range p, Y ^ i) := by
      have h1 := ModIdeal_sum p (fun i => U0 * (Y ^ i - 1)) hYi
      have h2 : ModIdeal D (p : ℤ) (Polynomial.C (p : ℤ) * U0) := ⟨0, U0, by ring⟩
      have h3 := ModIdeal_add h1 h2
      have heq : (∑ i ∈ Finset.range p, U0 * (Y ^ i - 1)) + Polynomial.C (p : ℤ) * U0 =
          U0 * ∑ i ∈ Finset.range p, Y ^ i := by
        rw [Finset.mul_sum]
        have hcast : Polynomial.C (p : ℤ) * U0 = ∑ _i ∈ Finset.range p, U0 := by
          rw [Finset.sum_const, Finset.card_range]
          have hcp : (p : Polynomial ℤ) = Polynomial.C (p : ℤ) := by simp
          rw [← hcp]
          ring
        rw [hcast, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rwa [heq] at h3
    rcases ih with ⟨Qa, Wa, ha⟩
    rcases hsum_mod with ⟨Qb, Wb, hb_eq⟩
    refine ⟨Qa * D * Qb + Qa * Polynomial.C (p : ℤ) * Wb +
        Polynomial.C ((p : ℤ) ^ (m + 1)) * Wa * Qb, Wa * Wb, ?_⟩
    have hYp : Z ^ (p ^ (m + 1)) - 1 = (Y - 1) * ∑ i ∈ Finset.range p, Y ^ i := by
      rw [pow_succ, pow_mul, ← geom_sum_mul_sub_one Y p, mul_comm]
    have hprod : U0 ^ (m + 1 + 1) * (Z ^ (p ^ (m + 1)) - 1) =
        (U0 ^ (m + 1) * (Y - 1)) * (U0 * ∑ i ∈ Finset.range p, Y ^ i) := by
      rw [hYp, pow_succ]
      ring
    have hCp : Polynomial.C ((p : ℤ) ^ (m + 1 + 1)) =
        Polynomial.C ((p : ℤ) ^ (m + 1)) * Polynomial.C (p : ℤ) := by
      rw [← map_mul, pow_succ]
    rw [hprod, ha, hb_eq, hCp]
    ring

lemma stirlingSecond_periodic_prime_pow {p : ℕ} (hp : p.Prime) {t b r : ℕ}
    (hb : 1 ≤ b) (hr : r < p ^ (t + 1)) {m : ℕ} (hm : b * p ^ t ≤ m) :
    ((p : ℤ) ^ b) ∣
      (Nat.stirlingSecond (m + (p - 1) * p ^ (t + b - 1)) r : ℤ) -
        (Nat.stirlingSecond m r : ℤ) := by
  rcases fallFact_lift_ideal hp t b hb with ⟨Q, W, hP⟩
  set m0 := m - b * p ^ t
  have hm0 : m0 + b * p ^ t = m := Nat.sub_add_cancel hm
  have happ := congr_fun (congr_arg (fun P => applyPoly P (stirlingSeq r)) hP) m0
  have hlhs : applyPoly
      ((Polynomial.X ^ (p ^ t)) ^ b * (Polynomial.X ^ ((p - 1) * p ^ (t + b - 1)) - 1))
      (stirlingSeq r) m0 =
      (Nat.stirlingSecond (m + (p - 1) * p ^ (t + b - 1)) r : ℤ) -
        (Nat.stirlingSecond m r : ℤ) := by
    have hpow : (Polynomial.X ^ (p ^ t) : Polynomial ℤ) ^ b = Polynomial.X ^ (p ^ t * b) := by
      rw [← pow_mul]
    rw [hpow, mul_sub, mul_one, ← pow_add, applyPoly_sub, applyPoly_X_pow, applyPoly_X_pow]
    unfold stirlingSeq
    have ha1 : m0 + (p ^ t * b + (p - 1) * p ^ (t + b - 1)) =
        m + (p - 1) * p ^ (t + b - 1) := by
      have hc : p ^ t * b = b * p ^ t := mul_comm _ _
      omega
    have ha2 : m0 + p ^ t * b = m := by
      have hc : p ^ t * b = b * p ^ t := mul_comm _ _
      omega
    rw [ha1, ha2]
  have hrhs : applyPoly
      (fallFact (p ^ (t + 1)) * Q + Polynomial.C ((p : ℤ) ^ b) * W)
      (stirlingSeq r) m0 =
      applyPoly (Polynomial.C ((p : ℤ) ^ b) * W) (stirlingSeq r) m0 := by
    rw [applyPoly_add, mul_comm (fallFact _), applyPoly_mul,
      applyPoly_fallFact_stirlingSeq_of_lt hr, applyPoly_zero_seq, zero_add]
  rw [hlhs, hrhs] at happ
  rw [happ]
  exact dvd_applyPoly_C_mul _ W (stirlingSeq r) m0

lemma stirlingSecond_periodic_prime_pow_mult {p : ℕ} (hp : p.Prime) {t b r : ℕ}
    (hb : 1 ≤ b) (hr : r < p ^ (t + 1)) (s : ℕ) {m : ℕ} (hm : b * p ^ t ≤ m) :
    ((p : ℤ) ^ b) ∣
      (Nat.stirlingSecond (m + s * ((p - 1) * p ^ (t + b - 1))) r : ℤ) -
        (Nat.stirlingSecond m r : ℤ) := by
  induction s with
  | zero => simp
  | succ s ih =>
    set T0 := (p - 1) * p ^ (t + b - 1)
    have hstep := stirlingSecond_periodic_prime_pow hp hb hr (by omega : b * p ^ t ≤ m + s * T0)
    have hsplit : (Nat.stirlingSecond (m + (s + 1) * T0) r : ℤ) - (Nat.stirlingSecond m r : ℤ) =
        ((Nat.stirlingSecond (m + s * T0 + T0) r : ℤ) - (Nat.stirlingSecond (m + s * T0) r : ℤ)) +
        ((Nat.stirlingSecond (m + s * T0) r : ℤ) - (Nat.stirlingSecond m r : ℤ)) := by
      have ha : m + (s + 1) * T0 = m + s * T0 + T0 := by ring
      rw [ha]
      ring
    rw [hsplit]
    exact dvd_add hstep ih

lemma sequence_trunc {p e n : ℕ} (hp : 2 ≤ p) (hn2 : 2 ≤ n) (hnpe : p ^ e ≤ n) :
    ((p ^ e : ℕ) : ℤ) ∣
      (OMA.S_oeis_a143138.sequence n : ℤ) -
        ∑ j ∈ Finset.Ico 1 (p ^ e),
          (wWeight j : ℤ) * (Nat.stirlingSecond (n - 1 + j) (2 * j) : ℤ) := by
  unfold OMA.S_oeis_a143138.sequence
  have hcast : ((∑ j ∈ Finset.range n,
        ((2 * j).factorial / j.factorial) * Nat.stirlingSecond (n - 1 + j) (2 * j) : ℕ) : ℤ) =
      ∑ j ∈ Finset.range n,
        (wWeight j : ℤ) * (Nat.stirlingSecond (n - 1 + j) (2 * j) : ℤ) := by
    unfold wWeight
    push_cast
    rfl
  rw [hcast]
  have hsplit : Finset.range n =
      insert 0 (Finset.Ico 1 (p ^ e) ∪ Finset.Ico (p ^ e) n) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_union, Finset.mem_Ico]
    have h1 : 1 ≤ p ^ e := Nat.one_le_pow e p (by omega)
    omega
  have hdisj1 : 0 ∉ Finset.Ico 1 (p ^ e) ∪ Finset.Ico (p ^ e) n := by
    simp only [Finset.mem_union, Finset.mem_Ico]
    have h1 : 1 ≤ p ^ e := Nat.one_le_pow e p (by omega)
    omega
  have hdisj2 : Disjoint (Finset.Ico 1 (p ^ e)) (Finset.Ico (p ^ e) n) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    rw [Finset.mem_Ico] at hj1 hj2
    omega
  rw [hsplit, Finset.sum_insert hdisj1, Finset.sum_union hdisj2]
  have hj0 : (wWeight 0 : ℤ) * (Nat.stirlingSecond (n - 1 + 0) (2 * 0) : ℤ) = 0 := by
    have hn1 : n - 1 + 0 = (n - 2) + 1 := by omega
    rw [hn1, mul_zero, Nat.stirlingSecond_succ_zero]
    simp
  rw [hj0, zero_add, add_sub_cancel_left]
  apply Finset.dvd_sum
  intro j hj
  rw [Finset.mem_Ico] at hj
  have hdvd : p ^ e ∣ wWeight j := pow_dvd_wWeight hp e j (by omega)
  exact dvd_mul_of_dvd_left (by exact_mod_cast hdvd) _

lemma sequence_prime_pow {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    ∃ N : ℕ, ∀ T : ℕ, (p ^ e).totient ∣ T → ∀ n ≥ N,
      ((p ^ e : ℕ) : ℤ) ∣
        (OMA.S_oeis_a143138.sequence (n + T) : ℤ) - (OMA.S_oeis_a143138.sequence n : ℤ) := by
  refine ⟨e * p ^ e + p ^ e + 2, ?_⟩
  intro T hT n hn
  rcases hT with ⟨s, rfl⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hnpe : p ^ e ≤ n := by omega
  have hnpe_add : p ^ e ≤ n + (p ^ e).totient * s := le_trans hnpe (Nat.le_add_right _ _)
  have ht1 := sequence_trunc hp2 (by omega : 2 ≤ n + (p ^ e).totient * s) hnpe_add
  have ht2 := sequence_trunc hp2 (by omega : 2 ≤ n) hnpe
  set S1 := ∑ j ∈ Finset.Ico 1 (p ^ e),
    (wWeight j : ℤ) * (Nat.stirlingSecond (n + (p ^ e).totient * s - 1 + j) (2 * j) : ℤ)
  set S2 := ∑ j ∈ Finset.Ico 1 (p ^ e),
    (wWeight j : ℤ) * (Nat.stirlingSecond (n - 1 + j) (2 * j) : ℤ)
  have hmid : ((p ^ e : ℕ) : ℤ) ∣ S1 - S2 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.dvd_sum
    intro j hj
    rw [Finset.mem_Ico] at hj
    rw [← mul_sub]
    by_cases h2j : p ^ e ≤ 2 * j
    · have hdvd : p ^ e ∣ wWeight j := pow_dvd_wWeight hp2 e j h2j
      exact dvd_mul_of_dvd_left (by exact_mod_cast hdvd) _
    · push Not at h2j
      set t := Nat.log p (2 * j)
      have hpt_le : p ^ t ≤ 2 * j := Nat.pow_log_le_self p (by omega)
      have hlt_pt1 : 2 * j < p ^ (t + 1) := Nat.lt_pow_succ_log_self hp.one_lt (2 * j)
      have hte : t < e := (Nat.pow_lt_pow_iff_right hp.one_lt).mp (lt_of_le_of_lt hpt_le h2j)
      set b := e - t
      have hb : 1 ≤ b := by omega
      have htb : t + b - 1 = e - 1 := by omega
      have htot : (p ^ e).totient * s = s * ((p - 1) * p ^ (t + b - 1)) := by
        rw [Nat.totient_prime_pow hp (by omega), htb]
        ring
      have harg : n + (p ^ e).totient * s - 1 + j =
          (n - 1 + j) + s * ((p - 1) * p ^ (t + b - 1)) := by
        rw [← htot]
        omega
      have hm_bound : b * p ^ t ≤ n - 1 + j := by
        have hble : b ≤ e := Nat.sub_le e t
        have hple : p ^ t ≤ p ^ e := Nat.pow_le_pow_right hp.pos (le_of_lt hte)
        have hmul : b * p ^ t ≤ e * p ^ e := Nat.mul_le_mul hble hple
        omega
      rw [harg]
      have hdvd_w : ((p : ℤ) ^ t) ∣ (wWeight j : ℤ) := by
        exact_mod_cast pow_dvd_wWeight hp2 t j hpt_le
      have hdvd_s := stirlingSecond_periodic_prime_pow_mult hp hb hlt_pt1 s hm_bound
      have hprod := mul_dvd_mul hdvd_w hdvd_s
      have hpe : ((p ^ e : ℕ) : ℤ) = (p : ℤ) ^ t * (p : ℤ) ^ b := by
        push_cast
        rw [← pow_add]
        congr 1
        omega
      rwa [hpe]
  have hcomb :
      (OMA.S_oeis_a143138.sequence (n + (p ^ e).totient * s) : ℤ) -
        (OMA.S_oeis_a143138.sequence n : ℤ) =
      ((OMA.S_oeis_a143138.sequence (n + (p ^ e).totient * s) : ℤ) - S1) -
      ((OMA.S_oeis_a143138.sequence n : ℤ) - S2) + (S1 - S2) := by ring
  rw [hcomb]
  exact dvd_add (dvd_sub ht1 ht2) hmid

lemma strip_prime {p : ℕ} (hp : p.Prime) :
    ∀ k : ℕ, 0 < k → ∃ e m : ℕ, p ^ e * m = k ∧ ¬ p ∣ m := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    by_cases hpk : p ∣ k
    · rcases hpk with ⟨k', rfl⟩
      have hk'0 : 0 < k' := by
        by_contra h0
        simp at h0
        subst h0
        omega
      have hk'_lt : k' < p * k' := by
        have hp2 := hp.two_le
        nlinarith
      rcases ih k' hk'_lt hk'0 with ⟨e', m, heq, hnd⟩
      refine ⟨e' + 1, m, ?_, hnd⟩
      rw [pow_succ', mul_assoc, heq]
    · exact ⟨0, k, by simp, hpk⟩

lemma coprime_mul_dvd_int {a b : ℕ} {z : ℤ} (hc : a.Coprime b)
    (ha : (a : ℤ) ∣ z) (hb : (b : ℤ) ∣ z) : ((a * b : ℕ) : ℤ) ∣ z :=
  Int.ofNat_dvd_left.mpr
    (hc.mul_dvd_of_dvd_of_dvd (Int.ofNat_dvd_left.mp ha) (Int.ofNat_dvd_left.mp hb))

lemma sequence_all_mod :
    ∀ k : ℕ, 0 < k → ∃ N : ℕ, ∀ T : ℕ, k.totient ∣ T → ∀ n ≥ N,
      (k : ℤ) ∣
        (OMA.S_oeis_a143138.sequence (n + T) : ℤ) - (OMA.S_oeis_a143138.sequence n : ℤ) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    by_cases hk1 : k = 1
    · subst hk1
      exact ⟨0, fun _ _ _ _ => one_dvd _⟩
    · have hk2 : 1 < k := by omega
      set p := k.minFac
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have hpk : p ∣ k := Nat.minFac_dvd k
      rcases strip_prime hp k hk with ⟨e, m, heq, hnd⟩
      have he1 : 1 ≤ e := by
        by_contra he0
        have hez : e = 0 := by omega
        subst hez
        simp at heq
        subst heq
        exact hnd hpk
      have hcop : (p ^ e).Coprime m := (hp.coprime_iff_not_dvd.mpr hnd).pow_left e
      rcases sequence_prime_pow hp he1 with ⟨N1, hN1⟩
      by_cases hm1 : m = 1
      · subst hm1
        rw [mul_one] at heq
        rw [← heq]
        exact ⟨N1, hN1⟩
      · have hm0 : 0 < m := by
          by_contra h0
          simp at h0
          subst h0
          simp at heq
          omega
        have hpe2 : 2 ≤ p ^ e := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
        have hmlt : m < k := by
          rw [← heq]
          nlinarith
        rcases ih m hmlt hm0 with ⟨N2, hN2⟩
        refine ⟨max N1 N2, ?_⟩
        intro T hT n hn
        have htot : k.totient = (p ^ e).totient * m.totient := by
          rw [← heq, Nat.totient_mul hcop]
        rw [htot] at hT
        have hT1 : (p ^ e).totient ∣ T := dvd_of_mul_right_dvd hT
        have hT2 : m.totient ∣ T := dvd_of_mul_left_dvd hT
        have hd1 := hN1 T hT1 n (le_trans (le_max_left _ _) hn)
        have hd2 := hN2 T hT2 n (le_trans (le_max_right _ _) hn)
        have hmul := coprime_mul_dvd_int hcop hd1 hd2
        rwa [heq] at hmul

lemma main_proof (k : ℕ) (hk : 0 < k) :
    ∃ N : ℕ, ∀ n ≥ N,
      (OMA.S_oeis_a143138.sequence (n + k.totient)) % k =
        OMA.S_oeis_a143138.sequence n % k := by
  rcases sequence_all_mod k hk with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hdvd := hN k.totient (dvd_refl _) n hn
  set a := OMA.S_oeis_a143138.sequence (n + k.totient)
  set b := OMA.S_oeis_a143138.sequence n
  by_cases hba : b ≤ a
  · have hcast : (a : ℤ) - (b : ℤ) = ((a - b : ℕ) : ℤ) := by omega
    rw [hcast] at hdvd
    rcases Int.ofNat_dvd.mp hdvd with ⟨q, hq⟩
    have ha : a = b + k * q := by omega
    rw [ha, Nat.add_mul_mod_self_left]
  · have hcast : (b : ℤ) - (a : ℤ) = ((b - a : ℕ) : ℤ) := by omega
    have hdvd' : (k : ℤ) ∣ (b : ℤ) - (a : ℤ) := by
      have hneg : -((a : ℤ) - (b : ℤ)) = (b : ℤ) - (a : ℤ) := by ring
      rw [← hneg]
      exact dvd_neg.mpr hdvd
    rw [hcast] at hdvd'
    rcases Int.ofNat_dvd.mp hdvd' with ⟨q, hq⟩
    have hb : b = a + k * q := by omega
    rw [hb, Nat.add_mul_mod_self_left]

end A143138Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a143138.main :=
  A143138Proof.main_proof
