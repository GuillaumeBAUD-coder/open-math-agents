import OMAStatements.S_oeis_a247250
import Mathlib

/-!
# Primitive prime divisors in the Pell sequence (OEIS A247250)

We prove that every Pell number `pell n` for `n ≥ 2` has a primitive prime divisor.
Using the companion sequence `H n` with `H n + pell n * √2 = (1 + √2) ^ n`, we establish:
1. Strong divisibility `Nat.gcd (pell m) (pell n) = pell (Nat.gcd m n)`.
2. Exact lifting of the exponent `v_p(pell (k * m)) = v_p(pell m) + v_p(k)` for every prime `p`
   dividing `pell m` (including `p = 2`), via a linear recurrence modulo `(pell m) ^ 2`.
3. If `pell n` has no primitive prime divisor, the Möbius alternating product `A / B` of `pell d`
   over `d ∣ n` satisfies `A ∣ B * n`, hence `A ≤ B * n`.
4. Via Binet's formula and the cyclotomic polynomial `Φ_n` over `ℂ`,
   `A / B = α ^ φ(n) * ‖Φ_n(β / α)‖ ≥ 2 ^ φ(n)`, since `α - |β| = (1 + √2) - (√2 - 1) = 2`.
5. Finally `n < 2 ^ φ(n)` for all `n ≥ 7` (from `n ≤ 2 * φ(n) ^ 2`), leaving `2 ≤ n ≤ 6`
   which are handled by explicit prime witnesses.
-/

namespace PellPrimitive

open Finset OMA.S_oeis_a247250
open scoped Classical

/-- Companion sequence `H n` satisfying `H n + pell n * √2 = (1 + √2)^n`. -/
private def H : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * H (n + 1) + H n

private lemma pell_H_succ (n : ℕ) :
    pell (n + 1) = H n + pell n ∧ H (n + 1) = H n + 2 * pell n := by
  induction n with
  | zero => decide
  | succ k ih =>
    constructor
    · change 2 * pell (k + 1) + pell k = H (k + 1) + pell (k + 1)
      omega
    · change 2 * H (k + 1) + H k = H (k + 1) + 2 * pell (k + 1)
      omega

private lemma pell_pos {n : ℕ} (hn : 0 < n) : 0 < pell n := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases k with _ | k
    · decide
    · have h1 := ih (by omega)
      change 0 < 2 * pell (k + 1) + pell k
      omega

private lemma pell_ne_zero {n : ℕ} (hn : 0 < n) : pell n ≠ 0 :=
  (pell_pos hn).ne'

private lemma pell_H_add (m n : ℕ) :
    pell (m + n) = pell m * H n + H m * pell n ∧
    H (m + n) = H m * H n + 2 * pell m * pell n := by
  induction n with
  | zero =>
    simp [pell, H]
  | succ k ih =>
    have h1 := pell_H_succ (m + k)
    have h2 := pell_H_succ k
    rw [Nat.add_succ]
    constructor <;> nlinarith [ih.1, ih.2, h1.1, h1.2, h2.1, h2.2]

private lemma pell_H_cassini (n : ℕ) :
    (H n : ℤ) ^ 2 - 2 * (pell n : ℤ) ^ 2 = (-1 : ℤ) ^ n := by
  induction n with
  | zero => decide
  | succ k ih =>
    have h := pell_H_succ k
    have hp : (pell (k + 1) : ℤ) = (H k : ℤ) + (pell k : ℤ) := by exact_mod_cast h.1
    have hH : (H (k + 1) : ℤ) = (H k : ℤ) + 2 * (pell k : ℤ) := by exact_mod_cast h.2
    rw [hp, hH, pow_succ (-1 : ℤ) k, ← ih]
    ring

private lemma pell_H_coprime (n : ℕ) : Nat.Coprime (pell n) (H n) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  set d := Nat.gcd (pell n) (H n)
  have hd1 : (d : ℤ) ∣ (pell n : ℤ) := Int.ofNat_dvd.mpr (Nat.gcd_dvd_left _ _)
  have hd2 : (d : ℤ) ∣ (H n : ℤ) := Int.ofNat_dvd.mpr (Nat.gcd_dvd_right _ _)
  have hd3 : (d : ℤ) ∣ (-1 : ℤ) ^ n := by
    rw [← pell_H_cassini n]
    exact dvd_sub (dvd_pow hd2 (by decide)) (dvd_mul_of_dvd_right (dvd_pow hd1 (by decide)) 2)
  have h1 : (d : ℤ) ∣ 1 := by
    have : ((-1 : ℤ) ^ n) ∣ 1 := by
      rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · rw [show k + k = 2 * k by omega, pow_mul]; norm_num
      · rw [pow_succ, pow_mul]; norm_num
    exact hd3.trans this
  have h2 : d ∣ 1 := Int.ofNat_dvd.mp h1
  exact Nat.eq_one_of_dvd_one h2

private lemma pell_add_gcd (m n : ℕ) :
    Nat.gcd (pell (m + n)) (pell m) = Nat.gcd (pell n) (pell m) := by
  rw [(pell_H_add m n).1]
  have h1 : Nat.gcd (pell m * H n + H m * pell n) (pell m) =
      Nat.gcd (H m * pell n) (pell m) := by
    rw [Nat.add_comm, Nat.mul_comm (pell m) (H n)]
    exact Nat.gcd_add_mul_right_left (pell m) (H m * pell n) (H n)
  rw [h1]
  exact (pell_H_coprime m).symm.gcd_mul_left_cancel (pell n)

private lemma pell_gcd (m n : ℕ) :
    Nat.gcd (pell m) (pell n) = pell (Nat.gcd m n) := by
  induction h : m + n using Nat.strong_induction_on generalizing m n with
  | h s ih =>
    rcases m with _ | m
    · simp [pell]
    rcases n with _ | n
    · simp [pell]
    rcases le_total (m + 1) (n + 1) with hle | hle
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      rw [hk, Nat.gcd_comm, pell_add_gcd, Nat.gcd_comm,
        Nat.gcd_comm (m + 1) (m + 1 + k), Nat.add_comm (m + 1) k,
        Nat.gcd_add_self_left, Nat.gcd_comm]
      exact ih (k + (m + 1)) (by omega) k (m + 1) rfl
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      rw [hk, pell_add_gcd, Nat.add_comm (n + 1) k, Nat.gcd_add_self_left]
      exact ih (k + (n + 1)) (by omega) k (n + 1) rfl

private lemma pell_dvd_of_dvd {m n : ℕ} (h : m ∣ n) : pell m ∣ pell n := by
  have hg : Nat.gcd m n = m := Nat.gcd_eq_left h
  have h1 : Nat.gcd (pell m) (pell n) = pell m := by rw [pell_gcd, hg]
  rw [← h1]
  exact Nat.gcd_dvd_right _ _

/-- Lifting the exponent via a linear recurrence modulo `(pell m)^2`. -/
private lemma pell_mul_quot_mod (m k : ℕ) :
    ∃ a : ℕ, pell (k * m) = pell m * a ∧
      (k = 0 → a = 0) ∧
      (0 < k → a ≡ k * (H m) ^ (k - 1) [MOD (pell m) ^ 2]) ∧
      H (k * m) ≡ (H m) ^ k [MOD (pell m) ^ 2] := by
  induction k with
  | zero =>
    refine ⟨0, by simp [pell], fun _ => rfl, fun h => (Nat.lt_irrefl 0 h).elim, ?_⟩
    simpa [H] using Nat.ModEq.rfl
  | succ k ih =>
    obtain ⟨a, ha_eq, ha0, ha_mod, hH_mod⟩ := ih
    refine ⟨a * H m + H (k * m), ?_, by omega, ?_, ?_⟩
    · rw [Nat.succ_mul, (pell_H_add (k * m) m).1, ha_eq]
      ring
    · intro _
      rcases k with _ | k
      · simpa [ha0 rfl, H] using Nat.ModEq.rfl
      · have hkpos : 0 < k + 1 := Nat.succ_pos k
        have h1 : a * H m ≡ ((k + 1) * H m ^ k) * H m [MOD (pell m) ^ 2] :=
          (ha_mod hkpos).mul_right (H m)
        have h2 : a * H m + H ((k + 1) * m) ≡
            (k + 1) * H m ^ k * H m + H m ^ (k + 1) [MOD (pell m) ^ 2] :=
          h1.add hH_mod
        have h3 : (k + 1) * H m ^ k * H m + H m ^ (k + 1) =
            (k + 2) * H m ^ (k + 1) := by ring
        simpa only [Nat.add_sub_cancel, h3] using h2
    · rw [Nat.succ_mul, (pell_H_add (k * m) m).2, ha_eq]
      have h1 : H (k * m) * H m ≡ H m ^ k * H m [MOD (pell m) ^ 2] :=
        hH_mod.mul_right (H m)
      have h2 : 2 * (pell m * a) * pell m = (pell m) ^ 2 * (2 * a) := by ring
      rw [h2, pow_succ]
      have h3 : H (k * m) * H m + pell m ^ 2 * (2 * a) ≡ H (k * m) * H m [MOD (pell m) ^ 2] := by
        rw [Nat.ModEq, Nat.add_mul_mod_self_left]
      exact h3.trans h1

private lemma factorization_pell_mul_coprime {p m k : ℕ} (hp : p.Prime)
    (hm : 0 < m) (hpm : p ∣ pell m) (hk : 0 < k) (hpk : ¬ p ∣ k) :
    (pell (k * m)).factorization p = (pell m).factorization p := by
  obtain ⟨a, ha_eq, _, ha_mod, _⟩ := pell_mul_quot_mod m k
  have hp2 : p ^ 2 ∣ (pell m) ^ 2 := pow_dvd_pow_of_dvd hpm 2
  have ha_mod_p : a ≡ k * (H m) ^ (k - 1) [MOD p] :=
    (ha_mod hk).of_dvd ((dvd_pow_self p (by decide : 2 ≠ 0)).trans hp2)
  have hpa : ¬ p ∣ a := by
    intro hd
    have hd2 : p ∣ k * (H m) ^ (k - 1) := (Nat.ModEq.dvd_iff ha_mod_p dvd_rfl).mp hd
    rcases hp.dvd_mul.mp hd2 with hk' | hH'
    · exact hpk hk'
    · have hH : p ∣ H m := hp.dvd_of_dvd_pow hH'
      have hcop := pell_H_coprime m
      have h1 : p ∣ Nat.gcd (pell m) (H m) := Nat.dvd_gcd hpm hH
      rw [hcop.gcd_eq_one] at h1
      exact hp.not_dvd_one h1
  have ha_ne : a ≠ 0 := by rintro rfl; exact hpa (dvd_zero p)
  rw [ha_eq, Nat.factorization_mul (pell_ne_zero hm) ha_ne, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hpa, add_zero]

private lemma factorization_pell_mul_prime {p m : ℕ} (hp : p.Prime)
    (hm : 0 < m) (hpm : p ∣ pell m) :
    (pell (p * m)).factorization p = (pell m).factorization p + 1 := by
  obtain ⟨a, ha_eq, _, ha_mod, _⟩ := pell_mul_quot_mod m p
  have hp2 : p ^ 2 ∣ (pell m) ^ 2 := pow_dvd_pow_of_dvd hpm 2
  have ha_mod_p2 : a ≡ p * (H m) ^ (p - 1) [MOD p ^ 2] :=
    (ha_mod hp.pos).of_dvd hp2
  have hpa : p ∣ a := by
    have h1 : p ∣ p * (H m) ^ (p - 1) := dvd_mul_right p _
    exact (Nat.ModEq.dvd_iff (ha_mod_p2.of_dvd (dvd_pow_self p (by decide : 2 ≠ 0))) dvd_rfl).mpr h1
  have hp2a : ¬ p ^ 2 ∣ a := by
    intro hd
    have hd2 : p ^ 2 ∣ p * (H m) ^ (p - 1) := (Nat.ModEq.dvd_iff ha_mod_p2 dvd_rfl).mp hd
    rw [sq] at hd2
    have hH1 : p ∣ (H m) ^ (p - 1) := (Nat.mul_dvd_mul_iff_left hp.pos).mp hd2
    have hH : p ∣ H m := hp.dvd_of_dvd_pow hH1
    have h1 : p ∣ Nat.gcd (pell m) (H m) := Nat.dvd_gcd hpm hH
    rw [(pell_H_coprime m).gcd_eq_one] at h1
    exact hp.not_dvd_one h1
  have ha_ne : a ≠ 0 := by rintro rfl; exact hp2a (dvd_zero _)
  have hva : a.factorization p = 1 := by
    have hge : 1 ≤ a.factorization p := (hp.pow_dvd_iff_le_factorization ha_ne).mp (by simpa using hpa)
    have hlt : ¬ 2 ≤ a.factorization p := fun h => hp2a ((hp.pow_dvd_iff_le_factorization ha_ne).mpr h)
    omega
  rw [ha_eq, Nat.factorization_mul (pell_ne_zero hm) ha_ne, Finsupp.add_apply, hva]

private lemma factorization_pell_mul {p m k : ℕ} (hp : p.Prime)
    (hm : 0 < m) (hpm : p ∣ pell m) (hk : 0 < k) :
    (pell (k * m)).factorization p = (pell m).factorization p + k.factorization p := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hpk : p ∣ k
    · obtain ⟨k', rfl⟩ := hpk
      have hk' : 0 < k' := Nat.pos_of_mul_pos_left hk
      have hlt : k' < p * k' := lt_mul_of_one_lt_left hk' hp.one_lt
      have hpm' : p ∣ pell (k' * m) := hpm.trans (pell_dvd_of_dvd (dvd_mul_left m k'))
      rw [show p * k' * m = p * (k' * m) by ring]
      rw [factorization_pell_mul_prime hp (Nat.mul_pos hk' hm) hpm']
      rw [ih k' hlt hk']
      rw [Nat.factorization_mul hp.ne_zero hk'.ne', Finsupp.add_apply, hp.factorization_self]
      omega
    · rw [factorization_pell_mul_coprime hp hm hpm hk hpk,
        Nat.factorization_eq_zero_of_not_dvd hpk, add_zero]

private lemma moebius_cases (k : ℕ) :
    ArithmeticFunction.moebius k = 0 ∨
    ArithmeticFunction.moebius k = 1 ∨
    ArithmeticFunction.moebius k = -1 := by
  by_cases hsq : Squarefree k
  · rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
    rcases neg_one_pow_eq_or ℤ (ArithmeticFunction.cardFactors k) with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · exact Or.inl (ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq)

private lemma sum_divisors_div_self {α : Type*} [AddCommMonoid α] (f : ℕ → α) (t : ℕ) :
    ∑ d ∈ t.divisors, f (t / d) = ∑ d ∈ t.divisors, f d := by
  rcases eq_or_ne t 0 with rfl | ht0
  · simp
  · refine Finset.sum_bij (fun d _ => t / d) ?_ ?_ ?_ ?_
    · intro d hd
      exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), ht0⟩
    · intro d1 hd1 d2 hd2 heq
      have h1 := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd1)
      have h2 := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd2)
      have hpos : 0 < t / d1 := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ht0)
        (Nat.dvd_of_mem_divisors hd1)) (Nat.pos_of_mem_divisors hd1)
      rw [heq] at h1
      exact Nat.eq_of_mul_eq_mul_right (heq ▸ hpos) (h1.trans h2.symm)
    · intro d hd
      refine ⟨t / d, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), ht0⟩, ?_⟩
      exact Nat.div_div_self (Nat.dvd_of_mem_divisors hd) ht0
    · intro _ _; rfl

private lemma sum_moebius_div_eq_ite {t : ℕ} (ht : 0 < t) :
    (∑ e ∈ t.divisors, (ArithmeticFunction.moebius (t / e) : ℤ)) =
      if t = 1 then 1 else 0 := by
  rw [sum_divisors_div_self]
  have h1 := ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℤ)
  have h2 := congrArg (fun f : ArithmeticFunction ℤ => f t) h1
  simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.intCoe_apply, Int.cast_id, ArithmeticFunction.zeta_apply,
    ArithmeticFunction.one_apply] at h2
  have h3 : (∑ x ∈ t.divisorsAntidiagonal,
      (ArithmeticFunction.moebius x.1 : ℤ) * ((if x.2 = 0 then 0 else 1 : ℕ) : ℤ)) =
      ∑ x ∈ t.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℤ) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hx2 : x.2 ≠ 0 := by
      intro h0
      have hm := (Nat.mem_divisorsAntidiagonal.mp hx).1
      rw [h0, mul_zero] at hm
      omega
    simp [hx2]
  rw [h3, Nat.sum_divisorsAntidiagonal (f := fun d _ => (ArithmeticFunction.moebius d : ℤ))] at h2
  exact h2

private lemma sum_moebius_div_eq_zero {t : ℕ} (ht : 1 < t) :
    (∑ e ∈ t.divisors, (ArithmeticFunction.moebius (t / e) : ℤ)) = 0 := by
  rw [sum_moebius_div_eq_ite (by omega), if_neg (by omega)]

/-- Möbius sum of `p`-adic valuations over divisors of `t > 1`. -/
private lemma sum_moebius_div_mul_factorization {p t : ℕ} (hp : p.Prime) (ht : 1 < t) :
    (∑ e ∈ t.divisors, (ArithmeticFunction.moebius (t / e) : ℤ) * (e.factorization p : ℤ)) =
      if ∃ a : ℕ, 0 < a ∧ t = p ^ a then 1 else 0 := by
  have ht0 : t ≠ 0 := by omega
  let a := t.factorization p
  let s := t / p ^ a
  have hpa_dvd : p ^ a ∣ t := Nat.ordProj_dvd t p
  have ht_eq : t = p ^ a * s := (Nat.mul_div_cancel' hpa_dvd).symm
  have hs_pos : 0 < s := Nat.pos_of_mul_pos_left (ht_eq ▸ (by omega : 0 < t))
  have hps : ¬ p ∣ s := by
    intro h
    have h1 : p ^ (a + 1) ∣ t := by
      rw [ht_eq, pow_succ]
      exact Nat.mul_dvd_mul_left (p ^ a) h
    have h2 := (hp.pow_dvd_iff_le_factorization ht0).mp h1
    omega
  have hcop : Nat.Coprime (p ^ a) s := (hp.coprime_iff_not_dvd.mpr hps).pow_left a
  have hdiv : t.divisors = ((p ^ a).divisors ×ˢ s.divisors).image (fun q => q.1 * q.2) := by
    rw [ht_eq, hcop.divisors_mul]
    ext x
    simp [Finset.mem_image, Finset.mem_product]
  have hinj : Set.InjOn (fun q : ℕ × ℕ => q.1 * q.2)
      (((p ^ a).divisors ×ˢ s.divisors : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro q1 hq1 q2 hq2 heq
    dsimp only at heq
    have h1 := Finset.mem_product.mp hq1
    have h2 := Finset.mem_product.mp hq2
    have h11 := Nat.dvd_of_mem_divisors h1.1
    have h12 := Nat.dvd_of_mem_divisors h1.2
    have h21 := Nat.dvd_of_mem_divisors h2.1
    have h22 := Nat.dvd_of_mem_divisors h2.2
    have hc12 : Nat.Coprime q1.1 q2.2 := hcop.coprime_dvd_left h11 |>.coprime_dvd_right h22
    have hc21 : Nat.Coprime q2.1 q1.2 := hcop.coprime_dvd_left h21 |>.coprime_dvd_right h12
    have d1 : q1.1 ∣ q2.1 := hc12.dvd_of_dvd_mul_right (by rw [← heq]; exact dvd_mul_right q1.1 q1.2)
    have d2 : q2.1 ∣ q1.1 := hc21.dvd_of_dvd_mul_right (by rw [heq]; exact dvd_mul_right q2.1 q2.2)
    have eq1 : q1.1 = q2.1 := Nat.dvd_antisymm d1 d2
    have hq1_pos : 0 < q1.1 := Nat.pos_of_mem_divisors h1.1
    have heq' : q1.1 * q1.2 = q1.1 * q2.2 := by rw [← eq1] at heq; exact heq
    have eq2 : q1.2 = q2.2 := Nat.eq_of_mul_eq_mul_left hq1_pos heq'
    exact Prod.ext eq1 eq2
  rw [hdiv, Finset.sum_image hinj, Finset.sum_product]
  have hterm : ∀ x ∈ (p ^ a).divisors, ∀ y ∈ s.divisors,
      (ArithmeticFunction.moebius (t / (x * y)) : ℤ) * ((x * y).factorization p : ℤ) =
        ((ArithmeticFunction.moebius (p ^ a / x) : ℤ) * (x.factorization p : ℤ)) *
          (ArithmeticFunction.moebius (s / y) : ℤ) := by
    intro x hx y hy
    have hx_dvd : x ∣ p ^ a := Nat.dvd_of_mem_divisors hx
    have hy_dvd : y ∣ s := Nat.dvd_of_mem_divisors hy
    have hx0 : x ≠ 0 := (Nat.pos_of_mem_divisors hx).ne'
    have hy0 : y ≠ 0 := (Nat.pos_of_mem_divisors hy).ne'
    have hdiv_eq : t / (x * y) = (p ^ a / x) * (s / y) := by
      rw [ht_eq]
      obtain ⟨u, hu⟩ := hx_dvd
      obtain ⟨v, hv⟩ := hy_dvd
      rw [hu, hv, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hx0),
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hy0)]
      have hmul : x * u * (y * v) = (x * y) * (u * v) := by ring
      rw [hmul, Nat.mul_div_cancel_left _ (Nat.mul_pos (Nat.pos_of_ne_zero hx0) (Nat.pos_of_ne_zero hy0))]
    have hcop_q : Nat.Coprime (p ^ a / x) (s / y) :=
      hcop.coprime_dvd_left (Nat.div_dvd_of_dvd hx_dvd) |>.coprime_dvd_right (Nat.div_dvd_of_dvd hy_dvd)
    have hpy : ¬ p ∣ y := fun h => hps (h.trans hy_dvd)
    rw [hdiv_eq, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_q,
      Nat.factorization_mul hx0 hy0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpy, add_zero]
    ring
  have hsplit : (∑ x ∈ (p ^ a).divisors, ∑ y ∈ s.divisors,
      (ArithmeticFunction.moebius (t / (x * y)) : ℤ) * ((x * y).factorization p : ℤ)) =
      (∑ x ∈ (p ^ a).divisors, (ArithmeticFunction.moebius (p ^ a / x) : ℤ) * (x.factorization p : ℤ)) *
        (∑ y ∈ s.divisors, (ArithmeticFunction.moebius (s / y) : ℤ)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y hy => hterm x hx y hy
  rw [hsplit, sum_moebius_div_eq_ite hs_pos]
  by_cases hs1 : s = 1
  · have ha_pos : 0 < a := by
      by_contra ha0
      have ha0' : a = 0 := by omega
      rw [ha0', hs1, pow_zero, mul_one] at ht_eq
      omega
    have hex : ∃ b : ℕ, 0 < b ∧ t = p ^ b := ⟨a, ha_pos, by rw [ht_eq, hs1, mul_one]⟩
    rw [if_pos hs1, if_pos hex, mul_one]
    rw [Nat.divisors_prime_pow hp, Finset.sum_map]
    have hval : ∀ j ∈ Finset.range (a + 1),
        (ArithmeticFunction.moebius (p ^ a / p ^ j) : ℤ) * ((p ^ j).factorization p : ℤ) =
          if j = a then (a : ℤ) else if j = a - 1 then -((a - 1 : ℕ) : ℤ) else 0 := by
      intro j hj
      have hjle : j ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [Nat.pow_div hjle hp.pos, Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]
      by_cases hja : j = a
      · subst hja; simp
      · by_cases hja1 : j = a - 1
        · subst hja1
          have hsub : a - (a - 1) = 1 := by omega
          rw [hsub, pow_one, ArithmeticFunction.moebius_apply_prime hp, if_neg hja, if_pos rfl]
          ring
        · have hnsq : ¬ Squarefree (p ^ (a - j)) := by
            rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]
            omega
          rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq, if_neg hja, if_neg hja1]
          simp
    have hsum_eq : (∑ j ∈ Finset.range (a + 1),
        (ArithmeticFunction.moebius (p ^ a / p ^ j) : ℤ) * ((p ^ j).factorization p : ℤ)) =
        ∑ j ∈ Finset.range (a + 1),
          if j = a then (a : ℤ) else if j = a - 1 then -((a - 1 : ℕ) : ℤ) else 0 :=
      Finset.sum_congr rfl hval
    change (∑ j ∈ Finset.range (a + 1),
        (ArithmeticFunction.moebius (p ^ a / p ^ j) : ℤ) * ((p ^ j).factorization p : ℤ)) = 1
    rw [hsum_eq]
    have ha_mem : a ∈ Finset.range (a + 1) := Finset.mem_range.mpr (Nat.lt_succ_self a)
    have ha1_mem : a - 1 ∈ Finset.range (a + 1) := Finset.mem_range.mpr (by omega)
    have hne : a ≠ a - 1 := by omega
    have hadd := Finset.add_sum_erase (Finset.range (a + 1))
      (fun j => if j = a then (a : ℤ) else if j = a - 1 then -((a - 1 : ℕ) : ℤ) else 0) ha_mem
    have hclean : (∑ j ∈ (Finset.range (a + 1)).erase a,
        if j = a then (a : ℤ) else if j = a - 1 then -((a - 1 : ℕ) : ℤ) else 0) =
        ∑ j ∈ (Finset.range (a + 1)).erase a,
          if j = a - 1 then -((a - 1 : ℕ) : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [if_neg (Finset.mem_erase.mp hj).1]
    have hrest : (∑ j ∈ (Finset.range (a + 1)).erase a,
        if j = a - 1 then -((a - 1 : ℕ) : ℤ) else 0) = -((a - 1 : ℕ) : ℤ) := by
      rw [Finset.sum_ite_eq', if_pos (Finset.mem_erase.mpr ⟨hne.symm, ha1_mem⟩)]
    rw [hclean, hrest, if_pos rfl] at hadd
    omega
  · have hnex : ¬ ∃ b : ℕ, 0 < b ∧ t = p ^ b := by
      rintro ⟨b, _, htb⟩
      have hba : a = b := by
        dsimp only [a]
        rw [htb, Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]
      have hs_eq : s = 1 := by
        dsimp only [s]
        rw [htb, hba, Nat.div_self (pow_pos hp.pos b)]
      exact hs1 hs_eq
    rw [if_neg hs1, if_neg hnex, mul_zero]

/-- If `pell n` has no primitive prime divisor, then the positive Möbius product divides `n` times
the negative Möbius product. -/
private lemma moebius_prod_dvd_of_no_prim {n : ℕ} (hn : 1 < n)
    (hnoprim : ∀ p : ℕ, p.Prime → p ∣ pell n → ∃ m : ℕ, 0 < m ∧ m < n ∧ p ∣ pell m) :
    let Dpos := n.divisors.filter (fun d => ArithmeticFunction.moebius (n / d) = 1)
    let Dneg := n.divisors.filter (fun d => ArithmeticFunction.moebius (n / d) = -1)
    (∏ d ∈ Dpos, pell d) ∣ (∏ d ∈ Dneg, pell d) * n := by
  intro Dpos Dneg
  set A := ∏ d ∈ Dpos, pell d
  set B := ∏ d ∈ Dneg, pell d
  have hA0 : A ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro d hd
    exact pell_ne_zero (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1)
  have hB0 : B ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro d hd
    exact pell_ne_zero (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1)
  have hn0 : n ≠ 0 := by omega
  rw [← Nat.factorization_le_iff_dvd hA0 (mul_ne_zero hB0 hn0)]
  intro p
  by_cases hp : p.Prime
  swap
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  rw [Nat.factorization_mul hB0 hn0, Finsupp.add_apply]
  have hA_fac : (A.factorization p : ℤ) =
      ∑ d ∈ Dpos, ((pell d).factorization p : ℤ) := by
    dsimp only [A]
    rw [Nat.factorization_prod (fun d hd => pell_ne_zero (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1)),
      Finsupp.finsetSum_apply, Nat.cast_sum]
  have hB_fac : (B.factorization p : ℤ) =
      ∑ d ∈ Dneg, ((pell d).factorization p : ℤ) := by
    dsimp only [B]
    rw [Nat.factorization_prod (fun d hd => pell_ne_zero (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1)),
      Finsupp.finsetSum_apply, Nat.cast_sum]
  have hdiff : (A.factorization p : ℤ) - (B.factorization p : ℤ) =
      ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℤ) * ((pell d).factorization p : ℤ) := by
    rw [hA_fac, hB_fac]
    have hsplit : ∀ d ∈ n.divisors,
        (ArithmeticFunction.moebius (n / d) : ℤ) * ((pell d).factorization p : ℤ) =
          (if ArithmeticFunction.moebius (n / d) = 1 then ((pell d).factorization p : ℤ) else 0) -
          (if ArithmeticFunction.moebius (n / d) = -1 then ((pell d).factorization p : ℤ) else 0) := by
      intro d _
      rcases moebius_cases (n / d) with h | h | h <;> simp [h]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib,
      Finset.sum_filter, Finset.sum_filter]
  suffices hle : (A.factorization p : ℤ) - (B.factorization p : ℤ) ≤ (n.factorization p : ℤ) by
    omega
  rw [hdiff]
  by_cases hpn : p ∣ pell n
  swap
  · have hz : (∑ d ∈ n.divisors,
        (ArithmeticFunction.moebius (n / d) : ℤ) * ((pell d).factorization p : ℤ)) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      have hnd : ¬ p ∣ pell d := fun h => hpn (h.trans (pell_dvd_of_dvd (Nat.dvd_of_mem_divisors hd)))
      simp [Nat.factorization_eq_zero_of_not_dvd hnd]
    rw [hz]
    exact Nat.cast_nonneg _
  · have hex : ∃ m : ℕ, 0 < m ∧ p ∣ pell m := ⟨n, by omega, hpn⟩
    let r := Nat.find hex
    have hr_pos : 0 < r := (Nat.find_spec hex).1
    have hpr : p ∣ pell r := (Nat.find_spec hex).2
    have hr_min : ∀ m : ℕ, 0 < m → p ∣ pell m → r ≤ m := fun m hm hpm => Nat.find_min' hex ⟨hm, hpm⟩
    have hr_dvd_iff : ∀ m : ℕ, 0 < m → (p ∣ pell m ↔ r ∣ m) := by
      intro m hm
      constructor
      · intro hpm
        have hg_pos : 0 < Nat.gcd r m := Nat.gcd_pos_of_pos_left m hr_pos
        have hpg : p ∣ pell (Nat.gcd r m) := by
          rw [← pell_gcd]
          exact Nat.dvd_gcd hpr hpm
        have hle := hr_min (Nat.gcd r m) hg_pos hpg
        have hge := Nat.gcd_le_left m hr_pos
        have heq : Nat.gcd r m = r := le_antisymm hge hle
        exact heq ▸ Nat.gcd_dvd_right r m
      · intro hrm
        exact hpr.trans (pell_dvd_of_dvd hrm)
    have hr_dvd_n : r ∣ n := (hr_dvd_iff n (by omega)).mp hpn
    have hr_lt_n : r < n := by
      obtain ⟨m, hm0, hmn, hpm⟩ := hnoprim p hp hpn
      exact lt_of_le_of_lt (hr_min m hm0 hpm) hmn
    let t := n / r
    have ht_eq : r * t = n := Nat.mul_div_cancel' hr_dvd_n
    have ht1 : 1 < t := by
      by_contra h
      have hle : t ≤ 1 := by omega
      have : n ≤ r := by nlinarith
      omega
    have hfilt : (∑ d ∈ n.divisors,
        (ArithmeticFunction.moebius (n / d) : ℤ) * ((pell d).factorization p : ℤ)) =
        ∑ d ∈ n.divisors.filter (fun d => r ∣ d),
          (ArithmeticFunction.moebius (n / d) : ℤ) * ((pell d).factorization p : ℤ) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro d hd hnd
      have hnr : ¬ r ∣ d := fun h => hnd (Finset.mem_filter.mpr ⟨hd, h⟩)
      have hnpd : ¬ p ∣ pell d := fun h => hnr ((hr_dvd_iff d (Nat.pos_of_mem_divisors hd)).mp h)
      simp [Nat.factorization_eq_zero_of_not_dvd hnpd]
    rw [hfilt]
    have hbij : n.divisors.filter (fun d => r ∣ d) = t.divisors.image (fun e => e * r) := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
      constructor
      · rintro ⟨⟨hdn, _⟩, ⟨e, rfl⟩⟩
        refine ⟨e, ⟨?_, by omega⟩, mul_comm e r⟩
        rw [← ht_eq] at hdn
        exact (Nat.mul_dvd_mul_iff_left hr_pos).mp hdn
      · rintro ⟨e, ⟨het, _⟩, rfl⟩
        refine ⟨⟨?_, hn0⟩, dvd_mul_left r e⟩
        rw [← ht_eq, mul_comm e r]
        exact Nat.mul_dvd_mul_left r het
    rw [hbij, Finset.sum_image (fun e1 _ e2 _ h => Nat.eq_of_mul_eq_mul_right hr_pos h)]
    have hre : ∀ e ∈ t.divisors,
        (ArithmeticFunction.moebius (n / (e * r)) : ℤ) * ((pell (e * r)).factorization p : ℤ) =
          (ArithmeticFunction.moebius (t / e) : ℤ) * ((pell r).factorization p : ℤ) +
          (ArithmeticFunction.moebius (t / e) : ℤ) * (e.factorization p : ℤ) := by
      intro e he
      have he0 : 0 < e := Nat.pos_of_mem_divisors he
      have hdiv_eq : n / (e * r) = t / e := by
        rw [← ht_eq, mul_comm r t, Nat.mul_div_mul_right t e hr_pos]
      rw [hdiv_eq, factorization_pell_mul hp hr_pos hpr he0, Nat.cast_add, mul_add]
    rw [Finset.sum_congr rfl hre, Finset.sum_add_distrib, ← Finset.sum_mul,
      sum_moebius_div_eq_zero ht1, zero_mul, zero_add,
      sum_moebius_div_mul_factorization hp ht1]
    split_ifs with hpow
    · obtain ⟨a, ha0, hta⟩ := hpow
      have hpn_dvd : p ∣ n := by
        rw [← ht_eq, hta]
        exact dvd_mul_of_dvd_right (dvd_pow_self p ha0.ne') r
      have h1 : 1 ≤ n.factorization p :=
        (hp.pow_dvd_iff_le_factorization hn0).mp (by simpa using hpn_dvd)
      exact_mod_cast h1
    · exact Nat.cast_nonneg _

/-- Binet identity for `H` and `pell`. -/
private lemma binet_real (d : ℕ) :
    (H d : ℝ) + (pell d : ℝ) * Real.sqrt 2 = (1 + Real.sqrt 2) ^ d ∧
    (H d : ℝ) - (pell d : ℝ) * Real.sqrt 2 = (1 - Real.sqrt 2) ^ d := by
  induction d with
  | zero => simp [H, pell]
  | succ k ih =>
    have hs := pell_H_succ k
    have hp : (pell (k + 1) : ℝ) = (H k : ℝ) + (pell k : ℝ) := by exact_mod_cast hs.1
    have hH : (H (k + 1) : ℝ) = (H k : ℝ) + 2 * (pell k : ℝ) := by exact_mod_cast hs.2
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    constructor
    · rw [pow_succ, ← ih.1, hp, hH]
      nlinarith [hsq]
    · rw [pow_succ, ← ih.2, hp, hH]
      nlinarith [hsq]

private lemma pell_binet_complex (d : ℕ) :
    ((2 * Real.sqrt 2 : ℝ) : ℂ) * (pell d : ℂ) =
      ((1 + Real.sqrt 2 : ℝ) : ℂ) ^ d - ((1 - Real.sqrt 2 : ℝ) : ℂ) ^ d := by
  have hr : 2 * Real.sqrt 2 * (pell d : ℝ) =
      (1 + Real.sqrt 2) ^ d - (1 - Real.sqrt 2) ^ d := by
    have h := binet_real d
    linarith [h.1, h.2]
  exact_mod_cast hr

/-- Cyclotomic lower bound on the Möbius alternating product of Pell numbers. -/
private lemma moebius_prod_lower_bound {n : ℕ} (hn : 1 < n) :
    let Dpos := n.divisors.filter (fun d => ArithmeticFunction.moebius (n / d) = 1)
    let Dneg := n.divisors.filter (fun d => ArithmeticFunction.moebius (n / d) = -1)
    ((∏ d ∈ Dneg, pell d : ℕ) : ℝ) * (2 : ℝ) ^ n.totient ≤ ((∏ d ∈ Dpos, pell d : ℕ) : ℝ) := by
  intro Dpos Dneg
  set α : ℝ := 1 + Real.sqrt 2
  set β : ℝ := 1 - Real.sqrt 2
  set αc : ℂ := (α : ℂ)
  set βc : ℂ := (β : ℂ)
  have hsqrt_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt_gt1 : (1 : ℝ) < Real.sqrt 2 := by
    have : (1 : ℝ) ^ 2 < Real.sqrt 2 ^ 2 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
    nlinarith [hsqrt_pos]
  have hα_pos : 0 < α := by dsimp [α]; linarith
  have hαc_ne : αc ≠ 0 := Complex.ofReal_ne_zero.mpr hα_pos.ne'
  set z : ℂ := βc / αc
  have hz_norm : ‖z‖ = (Real.sqrt 2 - 1) / α := by
    dsimp only [z, αc, βc]
    rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hα_pos, abs_of_neg (show β < 0 by dsimp [β]; linarith)]
    dsimp [β]
    ring
  have hcyc_lower : ∀ k : ℕ, 0 < k →
      ((2 : ℝ) / α) ^ k.totient ≤ ‖(Polynomial.cyclotomic k ℂ).eval z‖ := by
    intro k hk
    have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / k)) k :=
      Complex.isPrimitiveRoot_exp k hk.ne'
    have hfact := Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hprim
    rw [hfact, Polynomial.eval_prod, norm_prod]
    have hcard : (primitiveRoots k ℂ).card = k.totient := hprim.card_primitiveRoots
    rw [← hcard, ← Finset.prod_const]
    apply Finset.prod_le_prod (fun _ _ => by positivity)
    intro ζ hζ
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    have hζ_prim : IsPrimitiveRoot ζ k := (mem_primitiveRoots hk).mp hζ
    have hζ_norm : ‖ζ‖ = 1 := hζ_prim.norm'_eq_one hk.ne'
    have htri : ‖ζ‖ - ‖z‖ ≤ ‖z - ζ‖ := by
      have := norm_sub_norm_le ζ z
      rw [norm_sub_rev] at this
      linarith
    rw [hζ_norm, hz_norm] at htri
    have heq : 1 - (Real.sqrt 2 - 1) / α = 2 / α := by
      dsimp [α]
      field_simp [hα_pos.ne']
      ring
    linarith
  have hpell_norm : ∀ d : ℕ, 0 < d →
      2 * Real.sqrt 2 * (pell d : ℝ) =
        α ^ d * ∏ k ∈ d.divisors, ‖(Polynomial.cyclotomic k ℂ).eval z‖ := by
    intro d hd
    have h1 := pell_binet_complex d
    have h2 : αc ^ d - βc ^ d = -(αc ^ d) * (z ^ d - 1) := by
      dsimp only [z]
      rw [div_pow]
      field_simp [pow_ne_zero d hαc_ne]
      ring
    have h3 : z ^ d - 1 = ∏ k ∈ d.divisors, (Polynomial.cyclotomic k ℂ).eval z := by
      have hpoly := Polynomial.prod_cyclotomic_eq_X_pow_sub_one hd ℂ
      have hev := congrArg (Polynomial.eval z) hpoly
      simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_one] at hev
      exact hev.symm
    have hnorm := congrArg norm h1
    rw [h2, h3, norm_mul, norm_mul, norm_neg, norm_pow, norm_prod,
      Complex.norm_real, Complex.norm_real, Complex.norm_natCast,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity), abs_of_pos hα_pos] at hnorm
    exact hnorm
  set f : ℕ → ℝ := fun k => ‖(Polynomial.cyclotomic k ℂ).eval z‖
  have hDpos_eq : (2 * Real.sqrt 2) ^ Dpos.card * ((∏ d ∈ Dpos, pell d : ℕ) : ℝ) =
      α ^ (∑ d ∈ Dpos, d) * ∏ d ∈ Dpos, ∏ k ∈ d.divisors, f k := by
    rw [Nat.cast_prod, ← Finset.prod_const, ← Finset.prod_mul_distrib,
      ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro d hd
    exact hpell_norm d (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1)
  have hDneg_eq : (2 * Real.sqrt 2) ^ Dneg.card * ((∏ d ∈ Dneg, pell d : ℕ) : ℝ) =
      α ^ (∑ d ∈ Dneg, d) * ∏ d ∈ Dneg, ∏ k ∈ d.divisors, f k := by
    rw [Nat.cast_prod, ← Finset.prod_const, ← Finset.prod_mul_distrib,
      ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro d hd
    exact hpell_norm d (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1)
  have hmob_sum : ∀ g : ℕ → ℤ,
      (∑ d ∈ Dpos, g d) - (∑ d ∈ Dneg, g d) =
        ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℤ) * g d := by
    intro g
    have hsplit : ∀ d ∈ n.divisors,
        (ArithmeticFunction.moebius (n / d) : ℤ) * g d =
          (if ArithmeticFunction.moebius (n / d) = 1 then g d else 0) -
          (if ArithmeticFunction.moebius (n / d) = -1 then g d else 0) := by
      intro d _
      rcases moebius_cases (n / d) with h | h | h <;> simp [h]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, Finset.sum_filter, Finset.sum_filter]
  have hcard_eq : Dpos.card = Dneg.card := by
    have h := hmob_sum (fun _ => (1 : ℤ))
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
    rw [sum_moebius_div_eq_zero hn] at h
    omega
  have hfilter_mob : ∀ k ∈ n.divisors,
      (∑ d ∈ n.divisors.filter (fun d => k ∣ d), (ArithmeticFunction.moebius (n / d) : ℤ)) =
        if k = n then 1 else 0 := by
    intro k hk
    have hk0 : 0 < k := Nat.pos_of_mem_divisors hk
    have hkn : k ∣ n := Nat.dvd_of_mem_divisors hk
    let t := n / k
    have hkt : k * t = n := Nat.mul_div_cancel' hkn
    have ht0 : t ≠ 0 := by
      intro h
      rw [h, mul_zero] at hkt
      omega
    have hbij : n.divisors.filter (fun d => k ∣ d) = t.divisors.image (fun e => e * k) := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
      constructor
      · rintro ⟨⟨hdn, _⟩, ⟨e, rfl⟩⟩
        refine ⟨e, ⟨?_, ht0⟩, mul_comm e k⟩
        rw [← hkt] at hdn
        exact (Nat.mul_dvd_mul_iff_left hk0).mp hdn
      · rintro ⟨e, ⟨het, _⟩, rfl⟩
        refine ⟨⟨?_, by omega⟩, dvd_mul_left k e⟩
        rw [← hkt, mul_comm e k]
        exact Nat.mul_dvd_mul_left k het
    rw [hbij, Finset.sum_image (fun e1 _ e2 _ h => Nat.eq_of_mul_eq_mul_right hk0 h)]
    have hdiv : ∀ e ∈ t.divisors, (ArithmeticFunction.moebius (n / (e * k)) : ℤ) =
        (ArithmeticFunction.moebius (t / e) : ℤ) := by
      intro e _
      rw [← hkt, mul_comm k t, Nat.mul_div_mul_right t e hk0]
    rw [Finset.sum_congr rfl hdiv, sum_moebius_div_eq_ite (Nat.pos_of_ne_zero ht0)]
    by_cases hkeq : k = n
    · subst hkeq
      have ht1 : t = 1 := Nat.div_self hk0
      rw [if_pos ht1, if_pos rfl]
    · have htne1 : t ≠ 1 := by
        intro ht1
        rw [ht1, mul_one] at hkt
        exact hkeq hkt
      rw [if_neg htne1, if_neg hkeq]
  have hdeg_eq : (∑ d ∈ Dpos, d) = (∑ d ∈ Dneg, d) + n.totient := by
    have h := hmob_sum (fun d => (d : ℤ))
    have htot : (∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℤ) * (d : ℤ)) =
        (n.totient : ℤ) := by
      have hphi : ∀ m : ℕ, ∑ k ∈ m.divisors, (k.totient : ℤ) = (m : ℤ) := by
        intro m
        exact_mod_cast Nat.sum_totient m
      have hsub : (∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℤ) * (d : ℤ)) =
          ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℤ) *
            ∑ k ∈ d.divisors, (k.totient : ℤ) :=
        Finset.sum_congr rfl fun d _ => by rw [hphi d]
      rw [hsub]
      simp_rw [Finset.mul_sum]
      have hswap : (∑ d ∈ n.divisors, ∑ k ∈ d.divisors,
          (ArithmeticFunction.moebius (n / d) : ℤ) * (k.totient : ℤ)) =
          ∑ k ∈ n.divisors, (k.totient : ℤ) *
            ∑ d ∈ n.divisors.filter (fun d => k ∣ d), (ArithmeticFunction.moebius (n / d) : ℤ) := by
        have h1 : ∀ d ∈ n.divisors,
            (∑ k ∈ d.divisors, (ArithmeticFunction.moebius (n / d) : ℤ) * (k.totient : ℤ)) =
            ∑ k ∈ n.divisors, if k ∣ d then (ArithmeticFunction.moebius (n / d) : ℤ) * (k.totient : ℤ) else 0 := by
          intro d hd
          rw [← Finset.sum_filter]
          apply Finset.sum_congr _ (fun _ _ => rfl)
          ext k
          simp only [Finset.mem_filter, Nat.mem_divisors]
          have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
          have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
          exact ⟨fun h => ⟨⟨h.1.trans hdn, by omega⟩, h.1⟩, fun h => ⟨h.2, hd0⟩⟩
        rw [Finset.sum_congr rfl h1, Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum, ← Finset.sum_filter]
        exact Finset.sum_congr rfl fun d _ => mul_comm _ _
      rw [hswap]
      have hterm : ∀ k ∈ n.divisors,
          (k.totient : ℤ) * (∑ d ∈ n.divisors.filter (fun d => k ∣ d),
            (ArithmeticFunction.moebius (n / d) : ℤ)) = if k = n then (n.totient : ℤ) else 0 := by
        intro k hk
        rw [hfilter_mob k hk]
        split_ifs with hkn
        · subst hkn; simp
        · simp
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq',
        if_pos (Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩)]
    rw [htot] at h
    have hpos_cast : ((∑ d ∈ Dpos, d : ℕ) : ℤ) = ∑ d ∈ Dpos, (d : ℤ) := by push_cast; rfl
    have hneg_cast : ((∑ d ∈ Dneg, d : ℕ) : ℤ) = ∑ d ∈ Dneg, (d : ℤ) := by push_cast; rfl
    omega
  have hprod_cyc : (∏ d ∈ Dpos, ∏ k ∈ d.divisors, f k) =
      (∏ d ∈ Dneg, ∏ k ∈ d.divisors, f k) * f n := by
    have hrewrite : ∀ S : Finset ℕ, S ⊆ n.divisors →
        (∏ d ∈ S, ∏ k ∈ d.divisors, f k) =
        ∏ k ∈ n.divisors, (f k) ^ ((S.filter (fun d => k ∣ d)).card) := by
      intro S hS
      have h1 : ∀ d ∈ S, (∏ k ∈ d.divisors, f k) =
          ∏ k ∈ n.divisors, if k ∣ d then f k else 1 := by
        intro d hd
        rw [← Finset.prod_filter]
        apply Finset.prod_congr _ (fun _ _ => rfl)
        ext k
        simp only [Finset.mem_filter, Nat.mem_divisors]
        have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors (hS hd)).ne'
        have hdn : d ∣ n := Nat.dvd_of_mem_divisors (hS hd)
        exact ⟨fun h => ⟨⟨h.1.trans hdn, by omega⟩, h.1⟩, fun h => ⟨h.2, hd0⟩⟩
      rw [Finset.prod_congr rfl h1, Finset.prod_comm]
      apply Finset.prod_congr rfl
      intro k _
      rw [← Finset.prod_filter, Finset.prod_const]
    rw [hrewrite Dpos (Finset.filter_subset _ _), hrewrite Dneg (Finset.filter_subset _ _)]
    have hcount : ∀ k ∈ n.divisors,
        (Dpos.filter (fun d => k ∣ d)).card =
          (Dneg.filter (fun d => k ∣ d)).card + if k = n then 1 else 0 := by
      intro k hk
      have h := hmob_sum (fun d => if k ∣ d then (1 : ℤ) else 0)
      have hl : (∑ d ∈ Dpos, if k ∣ d then (1 : ℤ) else 0) = ((Dpos.filter (fun d => k ∣ d)).card : ℤ) := by
        simp [Finset.sum_boole]
      have hr : (∑ d ∈ Dneg, if k ∣ d then (1 : ℤ) else 0) = ((Dneg.filter (fun d => k ∣ d)).card : ℤ) := by
        simp [Finset.sum_boole]
      rw [hl, hr] at h
      have hf : (∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℤ) *
          if k ∣ d then (1 : ℤ) else 0) =
          ∑ d ∈ n.divisors.filter (fun d => k ∣ d), (ArithmeticFunction.moebius (n / d) : ℤ) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro d _
        split_ifs <;> simp
      rw [hf, hfilter_mob k hk] at h
      split_ifs at h ⊢ <;> omega
    have hsplit_p : (∏ k ∈ n.divisors, f k ^ (Dpos.filter (fun d => k ∣ d)).card) =
        ∏ k ∈ n.divisors, (f k ^ (Dneg.filter (fun d => k ∣ d)).card *
          if k = n then f n else 1) := by
      apply Finset.prod_congr rfl
      intro k hk
      rw [hcount k hk]
      split_ifs with hkn
      · subst hkn; rw [pow_add, pow_one]
      · simp
    rw [hsplit_p, Finset.prod_mul_distrib, Finset.prod_ite_eq',
      if_pos (Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩)]
  have hmain_eq : ((∏ d ∈ Dpos, pell d : ℕ) : ℝ) =
      ((∏ d ∈ Dneg, pell d : ℕ) : ℝ) * (α ^ n.totient * f n) := by
    have hcpos : (0 : ℝ) < (2 * Real.sqrt 2) ^ Dneg.card := by positivity
    apply mul_left_cancel₀ hcpos.ne'
    calc (2 * Real.sqrt 2) ^ Dneg.card * ((∏ d ∈ Dpos, pell d : ℕ) : ℝ)
        = (2 * Real.sqrt 2) ^ Dpos.card * ((∏ d ∈ Dpos, pell d : ℕ) : ℝ) := by rw [hcard_eq]
      _ = α ^ (∑ d ∈ Dpos, d) * ∏ d ∈ Dpos, ∏ k ∈ d.divisors, f k := hDpos_eq
      _ = (α ^ (∑ d ∈ Dneg, d) * ∏ d ∈ Dneg, ∏ k ∈ d.divisors, f k) *
            (α ^ n.totient * f n) := by
          rw [hdeg_eq, pow_add, hprod_cyc]; ring
      _ = (2 * Real.sqrt 2) ^ Dneg.card *
            (((∏ d ∈ Dneg, pell d : ℕ) : ℝ) * (α ^ n.totient * f n)) := by
          rw [← hDneg_eq]; ring
  rw [hmain_eq]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hlow := hcyc_lower n (by omega)
  have hmul := mul_le_mul_of_nonneg_left hlow (pow_nonneg hα_pos.le n.totient)
  have hsimp : α ^ n.totient * (2 / α) ^ n.totient = (2 : ℝ) ^ n.totient := by
    rw [← mul_pow, mul_div_cancel₀ _ hα_pos.ne']
  linarith

private lemma totient_prod_pairwise_coprime {S : Finset ℕ} {g : ℕ → ℕ}
    (hcop : Set.Pairwise (S : Set ℕ) fun a b => Nat.Coprime (g a) (g b)) :
    (∏ a ∈ S, g a).totient = ∏ a ∈ S, (g a).totient := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.prod_insert hx]
    have hcop_x : Nat.Coprime (g x) (∏ a ∈ s, g a) :=
      Nat.Coprime.prod_right fun a ha =>
        hcop (Finset.mem_insert_self x s) (Finset.mem_insert_of_mem ha) (fun h => hx (h ▸ ha))
    rw [Nat.totient_mul hcop_x, ih (hcop.mono (Finset.subset_insert x s))]

/-- Elementary multiplicative bound `n ≤ 2 * φ(n)^2` for all `n ≥ 1`. -/
private lemma le_two_mul_totient_sq (n : ℕ) (hn : 0 < n) : n ≤ 2 * n.totient ^ 2 := by
  have hprime : ∀ p k : ℕ, p.Prime → 1 ≤ k →
      p ^ k ≤ (if p = 2 then 2 else 1) * ((p ^ k).totient) ^ 2 := by
    intro p k hp hk
    rw [Nat.totient_prime_pow hp hk]
    by_cases hp2 : p = 2
    · subst hp2
      simp only [↓reduceIte]
      have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by
        conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ, mul_comm]
      have hpos : 1 ≤ 2 ^ (k - 1) := Nat.one_le_pow _ _ (by decide)
      have hsub : 2 - 1 = 1 := rfl
      rw [h2k, hsub, mul_one, sq]
      nlinarith
    · rw [if_neg hp2, one_mul]
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      have h1 : p ≤ (p - 1) ^ 2 := by
        obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp3
        rw [show 3 + q - 1 = q + 2 by omega]
        nlinarith
      have h2 : p ^ (k - 1) ≤ (p ^ (k - 1)) ^ 2 := by
        rw [sq]
        exact Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hp.pos)
      have hpk : p ^ k = p ^ (k - 1) * p := by
        conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
      rw [hpk, mul_pow]
      exact Nat.mul_le_mul h2 h1
  have hprod : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
    Nat.prod_primeFactors_pow_factorization hn.ne'
  have htot : n.totient = ∏ p ∈ n.primeFactors, (p ^ n.factorization p).totient := by
    conv_lhs => rw [hprod]
    apply totient_prod_pairwise_coprime
    intro p hp q hq hpq
    exact ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq).pow _ _
  calc n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := hprod
    _ ≤ ∏ p ∈ n.primeFactors, ((if p = 2 then 2 else 1) * ((p ^ n.factorization p).totient) ^ 2) := by
        apply Finset.prod_le_prod'
        intro p hp
        have hp' := Nat.prime_of_mem_primeFactors hp
        have hk : 1 ≤ n.factorization p :=
          (hp'.pow_dvd_iff_le_factorization hn.ne').mp (by simpa using Nat.dvd_of_mem_primeFactors hp)
        exact hprime p (n.factorization p) hp' hk
    _ = (∏ p ∈ n.primeFactors, if p = 2 then 2 else 1) *
          (∏ p ∈ n.primeFactors, ((p ^ n.factorization p).totient) ^ 2) := Finset.prod_mul_distrib
    _ ≤ 2 * (∏ p ∈ n.primeFactors, (p ^ n.factorization p).totient) ^ 2 := by
        rw [Finset.prod_pow]
        apply Nat.mul_le_mul_right
        by_cases h2 : 2 ∈ n.primeFactors
        · rw [Finset.prod_ite_eq', if_pos h2]
        · rw [Finset.prod_ite_eq', if_neg h2]; decide
    _ = 2 * n.totient ^ 2 := by rw [← htot]

private lemma two_mul_sq_lt_two_pow (k : ℕ) (hk : 7 ≤ k) : 2 * k ^ 2 < 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have hstep : 2 * (m + 1) ^ 2 ≤ 4 * m ^ 2 := by nlinarith
    rw [pow_succ 2 m]
    omega

private lemma lt_two_pow_totient {n : ℕ} (hn : 7 ≤ n) : n < 2 ^ n.totient := by
  by_cases h7 : 7 ≤ n.totient
  · exact lt_of_le_of_lt (le_two_mul_totient_sq n (by omega)) (two_mul_sq_lt_two_pow n.totient h7)
  · have hle : n ≤ 72 := by
      have h1 := le_two_mul_totient_sq n (by omega)
      have h2 : n.totient ≤ 6 := by omega
      nlinarith
    have hfin : ∀ m ∈ Finset.Icc 7 72, m < 2 ^ m.totient := by decide +kernel
    exact hfin n (Finset.mem_Icc.mpr ⟨hn, hle⟩)

private lemma small_cases {n : ℕ} (hn1 : 1 < n) (hn6 : n ≤ 6) :
    ∃ p : ℕ, p.Prime ∧ p ∣ pell n ∧ ∀ m : ℕ, 0 < m → m < n → ¬ p ∣ pell m := by
  interval_cases n
  · refine ⟨2, by decide, by decide, fun m hm1 hm2 => ?_⟩
    interval_cases m; decide
  · refine ⟨5, by decide, by decide, fun m hm1 hm2 => ?_⟩
    interval_cases m <;> decide
  · refine ⟨3, by decide, by decide, fun m hm1 hm2 => ?_⟩
    interval_cases m <;> decide
  · refine ⟨29, by decide, by decide, fun m hm1 hm2 => ?_⟩
    interval_cases m <;> decide
  · refine ⟨7, by decide, by decide, fun m hm1 hm2 => ?_⟩
    interval_cases m <;> decide

theorem primitive_prime_divisor : ∀ n : ℕ, 1 < n → ∃ p : ℕ, p.Prime ∧ p ∣ pell n ∧
    ∀ m : ℕ, 0 < m → m < n → ¬ p ∣ pell m := by
  intro n hn
  by_cases h6 : n ≤ 6
  · exact small_cases hn h6
  · have hn7 : 7 ≤ n := by omega
    by_contra hno
    push Not at hno
    have hdvd := moebius_prod_dvd_of_no_prim hn hno
    set Dpos := n.divisors.filter (fun d => ArithmeticFunction.moebius (n / d) = 1)
    set Dneg := n.divisors.filter (fun d => ArithmeticFunction.moebius (n / d) = -1)
    set A := ∏ d ∈ Dpos, pell d
    set B := ∏ d ∈ Dneg, pell d
    have hBpos : 0 < B :=
      Finset.prod_pos fun d hd => pell_pos (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1)
    have hABn : A ≤ B * n := Nat.le_of_dvd (Nat.mul_pos hBpos (by omega)) hdvd
    have hlow := moebius_prod_lower_bound hn
    have hABnR : (A : ℝ) ≤ (B : ℝ) * (n : ℝ) := by exact_mod_cast hABn
    have hBposR : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hBpos
    have hpowR : (2 : ℝ) ^ n.totient ≤ (n : ℝ) := by
      have : (B : ℝ) * (2 : ℝ) ^ n.totient ≤ (B : ℝ) * (n : ℝ) := hlow.trans hABnR
      exact le_of_mul_le_mul_left this hBposR
    have hpow : 2 ^ n.totient ≤ n := by exact_mod_cast hpowR
    have hlt := lt_two_pow_totient hn7
    omega

end PellPrimitive

theorem OMA.solution : type_of% @OMA.S_oeis_a247250.main :=
  PellPrimitive.primitive_prime_divisor
