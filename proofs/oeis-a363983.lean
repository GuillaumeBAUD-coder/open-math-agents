import OMAStatements.S_oeis_a363983

/-!
# A363983 supercongruence

At indices divisible by p, the three binomial factors scale by Kazandzidis
congruences. At the other indices, two factors supply p^(2r). The remaining
sum gains p^r by comparing the weights within each half block and cancelling
complete inverse-square sums. Reflection gives the inverse-square cancellation
on a half block from the cancellation on a full block.

The general Kazandzidis arithmetic comes from DiscoCharlie's checked A363986
proof (lefttosolve2/open-math-agents#34346). The general scaling, cancellation
and harmonic-sum infrastructure is adapted from our A363990 and A361712
proofs (#38660 and #40199). The half-block variation and its application to
A363983 are proved below.
-/

noncomputable section

section

/-!
Arithmetic excerpt of Public34346.lean, OMA PR34346, DiscoCharlie/open-math-agents,
head 22dd6669aa8ac9cccf968efd096d475f9500cbfa, agent antigravity/Gemini4Neon.
Only general positive-top Kazandzidis arithmetic is retained; no m=2 sequence identity.
Original source and attribution remain in the adjacent Public34346.lean.
-/

namespace OeisA363986Part23
open Finset Polynomial

/-- `p^M` divides `q : ℚ` in `ℤ_{(p)}`, i.e., `q = p^M * a / b` with `0 < b` and `p ⊥ b`. -/
def pDvdRat (p M : ℕ) (q : ℚ) : Prop :=
  ∃ a : ℤ, ∃ b : ℕ, 0 < b ∧ Nat.Coprime p b ∧ q = (p : ℚ) ^ M * (a : ℚ) / (b : ℚ)

lemma pDvdRat_zero (p M : ℕ) : pDvdRat p M 0 :=
  ⟨0, 1, Nat.one_pos, Nat.coprime_one_right p, by simp⟩

lemma pDvdRat_mono {p M1 M2 : ℕ} {q : ℚ} (h : M1 ≤ M2) (hq : pDvdRat p M2 q) :
    pDvdRat p M1 q := by
  rcases hq with ⟨a, b, hb, hcop, rfl⟩
  refine ⟨(p : ℤ) ^ (M2 - M1) * a, b, hb, hcop, ?_⟩
  push_cast
  rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]

lemma pDvdRat_neg {p M : ℕ} {q : ℚ} (hq : pDvdRat p M q) : pDvdRat p M (-q) := by
  rcases hq with ⟨a, b, hb, hcop, rfl⟩
  exact ⟨-a, b, hb, hcop, by push_cast; ring⟩

lemma pDvdRat_add {p M : ℕ} {q1 q2 : ℚ} (h1 : pDvdRat p M q1) (h2 : pDvdRat p M q2) :
    pDvdRat p M (q1 + q2) := by
  rcases h1 with ⟨a1, b1, hb1, hc1, rfl⟩
  rcases h2 with ⟨a2, b2, hb2, hc2, rfl⟩
  refine ⟨a1 * b2 + a2 * b1, b1 * b2, Nat.mul_pos hb1 hb2, hc1.mul_right hc2, ?_⟩
  have hb1q : (b1 : ℚ) ≠ 0 := by positivity
  have hb2q : (b2 : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

lemma pDvdRat_sub {p M : ℕ} {q1 q2 : ℚ} (h1 : pDvdRat p M q1) (h2 : pDvdRat p M q2) :
    pDvdRat p M (q1 - q2) := by
  rw [sub_eq_add_neg]; exact pDvdRat_add h1 (pDvdRat_neg h2)

lemma pDvdRat_mul {p M1 M2 : ℕ} {q1 q2 : ℚ} (h1 : pDvdRat p M1 q1) (h2 : pDvdRat p M2 q2) :
    pDvdRat p (M1 + M2) (q1 * q2) := by
  rcases h1 with ⟨a1, b1, hb1, hc1, rfl⟩
  rcases h2 with ⟨a2, b2, hb2, hc2, rfl⟩
  refine ⟨a1 * a2, b1 * b2, Nat.mul_pos hb1 hb2, hc1.mul_right hc2, ?_⟩
  push_cast
  rw [pow_add]
  ring

lemma pDvdRat_pow {p M : ℕ} {q : ℚ} (hq : pDvdRat p M q) (k : ℕ) :
    pDvdRat p (k * M) (q ^ k) := by
  induction k with
  | zero => exact ⟨1, 1, Nat.one_pos, Nat.coprime_one_right p, by simp⟩
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact pDvdRat_mul ih hq

lemma pDvdRat_sum {ι : Type*} {s : Finset ι} {p M : ℕ} {f : ι → ℚ}
    (hf : ∀ i ∈ s, pDvdRat p M (f i)) : pDvdRat p M (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pDvdRat_zero p M
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact pDvdRat_add (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma pDvdRat_of_int {p M : ℕ} (z : ℤ) (hz : (p : ℤ) ^ M ∣ z) : pDvdRat p M (z : ℚ) := by
  rcases hz with ⟨a, rfl⟩
  exact ⟨a, 1, Nat.one_pos, Nat.coprime_one_right p, by push_cast; ring⟩

lemma pDvdRat_of_int_zero (p : ℕ) (z : ℤ) : pDvdRat p 0 (z : ℚ) :=
  pDvdRat_of_int z (by simp)

lemma pDvdRat_inv_nat {p d : ℕ} (hd : 0 < d) (hcop : Nat.Coprime p d) :
    pDvdRat p 0 ((d : ℚ)⁻¹) :=
  ⟨1, d, hd, hcop, by push_cast; rw [pow_zero, one_mul, one_div]⟩

lemma int_dvd_of_pDvdRat {p M : ℕ} {z : ℤ} (hz : pDvdRat p M (z : ℚ)) : (p : ℤ) ^ M ∣ z := by
  rcases hz with ⟨a, b, hb, hcop, heq⟩
  have hbq : (b : ℚ) ≠ 0 := by positivity
  have hmulq : (z : ℚ) * (b : ℚ) = (p : ℚ) ^ M * (a : ℚ) := by
    rw [heq, div_mul_cancel₀ _ hbq]
  have hmul : z * (b : ℤ) = (p : ℤ) ^ M * a := by exact_mod_cast hmulq
  have hdvd : (p : ℤ) ^ M ∣ (b : ℤ) * z := ⟨a, by linarith⟩
  have hcopZ : IsCoprime ((p : ℤ) ^ M) (b : ℤ) :=
    (Nat.isCoprime_iff_coprime.mpr hcop).pow_left
  exact hcopZ.dvd_of_dvd_mul_left hdvd

lemma pDvdRat_div_nat {p M d E : ℕ} (hp : p.Prime) (hd : 0 < d)
    (hvp : padicValNat p d ≤ E) (hEM : E ≤ M) {q : ℚ} (hq : pDvdRat p M q) :
    pDvdRat p (M - E) (q / (d : ℚ)) := by
  have : Fact p.Prime := ⟨hp⟩
  rcases hq with ⟨a, b, hb, hcop, rfl⟩
  set v := padicValNat p d
  obtain ⟨d', hd'⟩ := pow_padicValNat_dvd (p := p) (n := d)
  have hd'_pos : 0 < d' := by
    rcases Nat.eq_zero_or_pos d' with rfl | hpos
    · simp at hd'; omega
    · exact hpos
  have hcop_d' : Nat.Coprime p d' := by
    rw [hp.coprime_iff_not_dvd]
    intro hpd'
    rcases hpd' with ⟨t, rfl⟩
    have h1 : p ^ (v + 1) ∣ d := ⟨t, by rw [hd', pow_succ]; ring⟩
    have h2 : v + 1 ≤ padicValNat p d := (padicValNat_dvd_iff_le (by omega)).mp h1
    omega
  refine ⟨(p : ℤ) ^ (E - v) * a, b * d', Nat.mul_pos hb hd'_pos, hcop.mul_right hcop_d', ?_⟩
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hd_cast : (d : ℚ) = (p : ℚ) ^ v * (d' : ℚ) := by exact_mod_cast hd'
  rw [hd_cast]
  have hexp : M = (M - E) + (E - v) + v := by omega
  push_cast
  calc (p : ℚ) ^ M * (a : ℚ) / (b : ℚ) / ((p : ℚ) ^ v * (d' : ℚ))
      = (p : ℚ) ^ ((M - E) + (E - v) + v) * (a : ℚ) / ((b : ℚ) * (d' : ℚ) * (p : ℚ) ^ v) := by
          rw [← hexp]; ring
    _ = ((p : ℚ) ^ (M - E) * ((p : ℚ) ^ (E - v) * (a : ℚ)) / ((b : ℚ) * (d' : ℚ))) *
        ((p : ℚ) ^ v / (p : ℚ) ^ v) := by rw [pow_add, pow_add]; ring
    _ = (p : ℚ) ^ (M - E) * ((p : ℚ) ^ (E - v) * (a : ℚ)) / ((b : ℚ) * (d' : ℚ)) := by
        rw [div_self (pow_ne_zero v hpq), mul_one]

/-- For `p ≥ 5` prime and `k ≥ 1`, `4 * padicValNat p k ≤ k - 1`. -/
lemma four_mul_padicValNat_le {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 1 ≤ k) :
    4 * padicValNat p k ≤ k - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  set v := padicValNat p k
  have hle : p ^ v ≤ k := Nat.le_of_dvd hk pow_padicValNat_dvd
  have h5v : 5 ^ v ≤ p ^ v := Nat.pow_le_pow_left hp5 v
  have hlin : 4 * v + 1 ≤ 5 ^ v := by
    induction v with
    | zero => norm_num
    | succ v ih =>
      rw [pow_succ]
      omega
  omega

/-- For `p ≥ 5` prime and `m : ℕ`, `4 * padicValNat p m.factorial ≤ m`. -/
lemma four_mul_padicValNat_factorial_le {p m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    4 * padicValNat p m.factorial ≤ m := by
  have : Fact p.Prime := ⟨hp⟩
  have h := sub_one_mul_padicValNat_factorial (p := p) m
  have h4 : 4 ≤ p - 1 := by omega
  calc 4 * padicValNat p m.factorial
      ≤ (p - 1) * padicValNat p m.factorial := Nat.mul_le_mul_right _ h4
    _ = m - (p.digits m).sum := h
    _ ≤ m := Nat.sub_le _ _

/-- Truncated logarithm `∑_{k=1}^M (-1)^{k-1} u^k / k`. -/
def truncLog (M : ℕ) (u : ℚ) : ℚ :=
  ∑ k ∈ Icc 1 M, (-1 : ℚ) ^ (k - 1) * u ^ k / (k : ℚ)

lemma poly_coeff_pDvdRat_mul {p : ℕ} {P Q : ℚ[X]}
    (hP : ∀ i, pDvdRat p (2 * i) (P.coeff i))
    (hQ : ∀ i, pDvdRat p (2 * i) (Q.coeff i)) :
    ∀ j, pDvdRat p (2 * j) ((P * Q).coeff j) := by
  intro j
  rw [Polynomial.coeff_mul]
  refine pDvdRat_sum (fun x hx => ?_)
  have hsum : x.1 + x.2 = j := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have hm := pDvdRat_mul (hP x.1) (hQ x.2)
  rwa [show 2 * x.1 + 2 * x.2 = 2 * j by omega] at hm

lemma poly_coeff_pDvdRat_pow {p : ℕ} {P : ℚ[X]}
    (hP : ∀ i, pDvdRat p (2 * i) (P.coeff i)) (k : ℕ) :
    ∀ j, pDvdRat p (2 * j) ((P ^ k).coeff j) := by
  induction k with
  | zero =>
    intro j
    rcases j with _ | j
    · simp; exact pDvdRat_of_int_zero p 1
    · rw [pow_zero, Polynomial.coeff_one]; simp [pDvdRat_zero]
  | succ k ih =>
    rw [pow_succ]
    exact poly_coeff_pDvdRat_mul ih hP

lemma coeff_zero_of_mul_unit_const {H P : ℚ[X]} (hH0 : H.coeff 0 = 1) (M : ℕ)
    (hHP : ∀ j < M, (H * P).coeff j = 0) : ∀ j < M, P.coeff j = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    have h0 := hHP j hj
    rw [Polynomial.coeff_mul] at h0
    have hsplit : ∑ x ∈ Finset.HasAntidiagonal.antidiagonal j, H.coeff x.1 * P.coeff x.2 =
        H.coeff 0 * P.coeff j := by
      rw [Finset.sum_eq_single (0, j)]
      · intro x hx hne
        have hsum : x.1 + x.2 = j := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
        have hlt : x.2 < j := by
          by_contra hge
          have h2 : x.2 = j := by omega
          have h1 : x.1 = 0 := by omega
          exact hne (Prod.ext h1 h2)
        rw [ih x.2 hlt (lt_trans hlt hj), mul_zero]
      · intro hnot
        exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega)) hnot
    rw [hsplit, hH0, one_mul] at h0
    exact h0

lemma natDegree_finset_sum_le {ι R : Type*} [Semiring R] (s : Finset ι) (f : ι → R[X]) (d : ℕ)
    (hf : ∀ i ∈ s, (f i).natDegree ≤ d) : (∑ i ∈ s, f i).natDegree ≤ d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (natDegree_add_le _ _).trans
      (max_le (hf a (Finset.mem_insert_self a s)) (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))))

lemma nat_coprime_prod_right {ι : Type*} {s : Finset ι} {p : ℕ} {f : ι → ℕ}
    (hf : ∀ i ∈ s, Nat.Coprime p (f i)) : Nat.Coprime p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul_right
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma truncLog_mul {p M : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {u v : ℚ}
    (hu : pDvdRat p 2 u) (hv : pDvdRat p 2 v) :
    pDvdRat p M (truncLog M (u + v + u * v) - truncLog M u - truncLog M v) := by
  let A : ℚ[X] := C (u + v) * X + C (u * v) * X ^ 2
  let Bu : ℚ[X] := C u * X
  let Bv : ℚ[X] := C v * X
  let G : ℚ[X] := ∑ k ∈ Icc 1 M,
    C ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * (A ^ k - Bu ^ k - Bv ^ k)
  have hGeval1 : G.eval 1 = truncLog M (u + v + u * v) - truncLog M u - truncLog M v := by
    simp only [G, truncLog, eval_finsetSum, eval_mul, eval_C, eval_sub, eval_pow, A, Bu, Bv,
      eval_add, eval_X, one_pow, mul_one]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have hG0 : G.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    dsimp only [G]
    rw [Polynomial.eval_finsetSum]
    refine Finset.sum_eq_zero (fun k hk => ?_)
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hne : k ≠ 0 := by omega
    simp [A, Bu, Bv, zero_pow hne]
  -- Derivative identity: (1 + Bu) * (1 + Bv) * G.derivative is divisible by X^M!
  have hderiv_pow : ∀ (P : ℚ[X]),
      (1 + P) * (∑ k ∈ Icc 1 M, C ((-1 : ℚ) ^ (k - 1)) * P ^ (k - 1) * P.derivative) =
        P.derivative * (1 - (-P) ^ M) := by
    intro P
    have hsum : (1 + P) * (∑ k ∈ Icc 1 M, (-P) ^ (k - 1)) = 1 - (-P) ^ M := by
      have hgeom := geom_sum_mul (-P) M
      have hre : ∑ k ∈ Icc 1 M, (-P) ^ (k - 1) = ∑ i ∈ range M, (-P) ^ i := by
        refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
        · intro k hk; simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢; omega
        · intro k1 hk1 k2 hk2 h; simp only [Finset.mem_Icc] at hk1 hk2; omega
        · intro i hi; exact ⟨i + 1, Finset.mem_Icc.mpr ⟨by omega, by rw [Finset.mem_range] at hi; omega⟩, by omega⟩
        · intro k _; rfl
      rw [hre]
      linear_combination -hgeom
    have hrew : ∑ k ∈ Icc 1 M, C ((-1 : ℚ) ^ (k - 1)) * P ^ (k - 1) * P.derivative =
        (∑ k ∈ Icc 1 M, (-P) ^ (k - 1)) * P.derivative := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have hc : C ((-1 : ℚ) ^ (k - 1)) * P ^ (k - 1) = (-P) ^ (k - 1) := by
        rw [map_pow, map_neg, map_one, ← mul_pow]; simp
      rw [hc]
    rw [hrew, ← mul_assoc, hsum]
    ring
  have hGderiv : G.derivative =
      (∑ k ∈ Icc 1 M, C ((-1 : ℚ) ^ (k - 1)) * A ^ (k - 1) * A.derivative) -
      (∑ k ∈ Icc 1 M, C ((-1 : ℚ) ^ (k - 1)) * Bu ^ (k - 1) * Bu.derivative) -
      (∑ k ∈ Icc 1 M, C ((-1 : ℚ) ^ (k - 1)) * Bv ^ (k - 1) * Bv.derivative) := by
    simp only [G, derivative_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkq : (k : ℚ) ≠ 0 := by positivity
    rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_sub, derivative_sub,
      derivative_pow, derivative_pow, derivative_pow]
    have hcancel : C ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * (k : ℚ[X]) = C ((-1 : ℚ) ^ (k - 1)) := by
      rw [← map_natCast C, ← map_mul, div_mul_cancel₀ _ hkq]
    calc C ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) *
          ((k : ℚ[X]) * A ^ (k - 1) * A.derivative -
           (k : ℚ[X]) * Bu ^ (k - 1) * Bu.derivative -
           (k : ℚ[X]) * Bv ^ (k - 1) * Bv.derivative)
        = (C ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * (k : ℚ[X])) * A ^ (k - 1) * A.derivative -
          (C ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * (k : ℚ[X])) * Bu ^ (k - 1) * Bu.derivative -
          (C ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * (k : ℚ[X])) * Bv ^ (k - 1) * Bv.derivative := by ring
      _ = C ((-1 : ℚ) ^ (k - 1)) * A ^ (k - 1) * A.derivative -
          C ((-1 : ℚ) ^ (k - 1)) * Bu ^ (k - 1) * Bu.derivative -
          C ((-1 : ℚ) ^ (k - 1)) * Bv ^ (k - 1) * Bv.derivative := by rw [hcancel]
  have h1A : 1 + A = (1 + Bu) * (1 + Bv) := by
    simp only [A, Bu, Bv, map_add, map_mul]; ring
  have hAderiv : A.derivative = Bu.derivative * (1 + Bv) + Bv.derivative * (1 + Bu) := by
    simp only [A, Bu, Bv, derivative_mul, derivative_C, derivative_X,
      derivative_pow, map_add, map_mul, map_natCast]
    ring
  have hH_mul : ((1 + Bu) * (1 + Bv)) * G.derivative =
      -(A.derivative * (-A) ^ M) + (1 + Bv) * (Bu.derivative * (-Bu) ^ M) +
      (1 + Bu) * (Bv.derivative * (-Bv) ^ M) := by
    rw [hGderiv, mul_sub, mul_sub]
    have t1 : (1 + Bu) * (1 + Bv) *
        (∑ k ∈ Icc 1 M, C ((-1 : ℚ) ^ (k - 1)) * A ^ (k - 1) * A.derivative) =
        A.derivative * (1 - (-A) ^ M) := by rw [← h1A, hderiv_pow A]
    have t2 : (1 + Bu) * (1 + Bv) *
        (∑ k ∈ Icc 1 M, C ((-1 : ℚ) ^ (k - 1)) * Bu ^ (k - 1) * Bu.derivative) =
        (1 + Bv) * (Bu.derivative * (1 - (-Bu) ^ M)) := by
      rw [mul_comm (1 + Bu) (1 + Bv), mul_assoc, hderiv_pow Bu]
    have t3 : (1 + Bu) * (1 + Bv) *
        (∑ k ∈ Icc 1 M, C ((-1 : ℚ) ^ (k - 1)) * Bv ^ (k - 1) * Bv.derivative) =
        (1 + Bu) * (Bv.derivative * (1 - (-Bv) ^ M)) := by
      rw [mul_assoc, hderiv_pow Bv]
    rw [t1, t2, t3, hAderiv]
    ring
  have hXdvd_A : X ∣ A := ⟨C (u + v) + C (u * v) * X, by simp only [A]; ring⟩
  have hXdvd_Bu : X ∣ Bu := ⟨C u, by simp only [Bu]; ring⟩
  have hXdvd_Bv : X ∣ Bv := ⟨C v, by simp only [Bv]; ring⟩
  have hXM_dvd : X ^ M ∣ ((1 + Bu) * (1 + Bv)) * G.derivative := by
    rw [hH_mul]
    have d1 : X ^ M ∣ (-A) ^ M := pow_dvd_pow_of_dvd (dvd_neg.mpr hXdvd_A) M
    have d2 : X ^ M ∣ (-Bu) ^ M := pow_dvd_pow_of_dvd (dvd_neg.mpr hXdvd_Bu) M
    have d3 : X ^ M ∣ (-Bv) ^ M := pow_dvd_pow_of_dvd (dvd_neg.mpr hXdvd_Bv) M
    exact dvd_add (dvd_add (dvd_neg.mpr (dvd_mul_of_dvd_right d1 _))
      (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right d2 _) _))
      (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right d3 _) _)
  have hH0 : ((1 + Bu) * (1 + Bv)).coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]; simp [Bu, Bv]
  have hGd_zero : ∀ j < M, G.derivative.coeff j = 0 := by
    refine coeff_zero_of_mul_unit_const hH0 M (fun j hj => ?_)
    rcases hXM_dvd with ⟨Q, hQ⟩
    rw [hQ, coeff_X_pow_mul']
    simp [Nat.not_le.mpr hj]
  have hG_coeff_zero : ∀ j ≤ M, G.coeff j = 0 := by
    intro j hj
    rcases j with _ | j
    · exact hG0
    · have h1 := hGd_zero j (by omega)
      rw [coeff_derivative] at h1
      have hne : ((j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      exact (mul_eq_zero.mp h1).resolve_right (by push_cast at hne ⊢; exact hne)
  have hGdeg : G.natDegree ≤ 2 * M := by
    have hdegA : A.natDegree ≤ 2 := by
      calc A.natDegree ≤ max (C (u + v) * X).natDegree (C (u * v) * X ^ 2).natDegree := natDegree_add_le _ _
        _ ≤ max (0 + 1) (0 + 2) := by
          gcongr
          · exact natDegree_C_mul_le _ _ |>.trans (by simp)
          · exact natDegree_C_mul_le _ _ |>.trans (by simp)
        _ = 2 := by norm_num
    have hdegBu : Bu.natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans (by simp)
    have hdegBv : Bv.natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans (by simp)
    refine natDegree_finset_sum_le (Icc 1 M) _ (2 * M) (fun k hk => ?_)
    have hkM : k ≤ M := (Finset.mem_Icc.mp hk).2
    refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le ?_ ?_)) ?_)
    · exact (natDegree_pow_le).trans (by nlinarith)
    · exact (natDegree_pow_le).trans (by nlinarith)
    · exact (natDegree_pow_le).trans (by nlinarith)
  rw [← hGeval1, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hGdeg)]
  simp only [one_pow, mul_one]
  refine pDvdRat_sum (fun j hj => ?_)
  by_cases hjM : j ≤ M
  · rw [hG_coeff_zero j hjM]; exact pDvdRat_zero p M
  · have hjgt : M < j := Nat.lt_of_not_ge hjM
    simp only [G, finsetSum_coeff, coeff_C_mul, coeff_sub]
    refine pDvdRat_sum (fun k hk => ?_)
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkM : k ≤ M := (Finset.mem_Icc.mp hk).2
    have hBu0 : (Bu ^ k).coeff j = 0 := by
      have hdeg : (Bu ^ k).natDegree ≤ k :=
        (natDegree_pow_le).trans (by have : Bu.natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans (by simp); nlinarith)
      exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (lt_of_le_of_lt hkM hjgt))
    have hBv0 : (Bv ^ k).coeff j = 0 := by
      have hdeg : (Bv ^ k).natDegree ≤ k :=
        (natDegree_pow_le).trans (by have : Bv.natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans (by simp); nlinarith)
      exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (lt_of_le_of_lt hkM hjgt))
    rw [hBu0, hBv0, sub_zero, sub_zero]
    have hAcoeff : ∀ i, pDvdRat p (2 * i) (A.coeff i) := by
      intro i
      rcases i with _ | _ | _ | i
      · have : A.coeff 0 = 0 := by simp [A]
        rw [this]; exact pDvdRat_zero p 0
      · have : A.coeff 1 = u + v := by
          simp only [A, coeff_add, coeff_C_mul, coeff_X_one, coeff_X_pow]
          norm_num
        rw [this]; exact pDvdRat_add hu hv
      · have : A.coeff 2 = u * v := by
          simp only [A, coeff_add, coeff_C_mul, coeff_X, coeff_X_pow]
          norm_num
        rw [this]; exact pDvdRat_mul hu hv
      · have hdeg : A.natDegree ≤ 2 := by
          calc A.natDegree ≤ max (C (u + v) * X).natDegree (C (u * v) * X ^ 2).natDegree := natDegree_add_le _ _
            _ ≤ max 1 2 := max_le_max ((natDegree_C_mul_le _ _).trans (by simp)) ((natDegree_C_mul_le _ _).trans (by simp))
            _ = 2 := by norm_num
        rw [coeff_eq_zero_of_natDegree_lt (by omega)]; exact pDvdRat_zero p _
    have hAkj : pDvdRat p (2 * j) ((A ^ k).coeff j) := poly_coeff_pDvdRat_pow hAcoeff k j
    have hvp : padicValNat p k ≤ j := by
      have h4 := four_mul_padicValNat_le hp hp5 hk1
      omega
    have hdiv := pDvdRat_div_nat hp (by omega : 0 < k) hvp (by omega : j ≤ 0 + 2 * j)
      (pDvdRat_mul (pDvdRat_of_int_zero p ((-1 : ℤ) ^ (k - 1))) hAkj)
    have hrew : ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * (A ^ k).coeff j =
        ((((-1 : ℤ) ^ (k - 1) : ℤ) : ℚ) * (A ^ k).coeff j) / (k : ℚ) := by push_cast; ring
    rw [hrew]
    exact pDvdRat_mono (by omega : M ≤ 0 + 2 * j - j) hdiv

lemma truncLog_prod {ι : Type*} (s : Finset ι) {p M : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (u : ι → ℚ) (hu : ∀ i ∈ s, pDvdRat p 2 (u i)) :
    pDvdRat p 2 ((∏ i ∈ s, (1 + u i)) - 1) ∧
    pDvdRat p M (truncLog M ((∏ i ∈ s, (1 + u i)) - 1) - ∑ i ∈ s, truncLog M (u i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using pDvdRat_zero p 2, ?_⟩
    simp only [Finset.prod_empty, sub_self, Finset.sum_empty, sub_zero]
    have h0 : truncLog M 0 = 0 := by
      refine Finset.sum_eq_zero (fun k hk => ?_)
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      rw [zero_pow (by omega : k ≠ 0), mul_zero, zero_div]
    rw [h0]; exact pDvdRat_zero p M
  | insert a s ha ih =>
    have hua : pDvdRat p 2 (u a) := hu a (Finset.mem_insert_self a s)
    obtain ⟨hP2, hPlog⟩ := ih (fun i hi => hu i (Finset.mem_insert_of_mem hi))
    set v := (∏ i ∈ s, (1 + u i)) - 1
    have hprod : (∏ i ∈ insert a s, (1 + u i)) - 1 = u a + v + u a * v := by
      rw [Finset.prod_insert ha]
      have : ∏ i ∈ s, (1 + u i) = 1 + v := by simp [v]
      rw [this]; ring
    rw [hprod, Finset.sum_insert ha]
    refine ⟨pDvdRat_add (pDvdRat_add hua hP2) (pDvdRat_mono (by omega : 2 ≤ 2 + 2) (pDvdRat_mul hua hP2)), ?_⟩
    have hstep := truncLog_mul (M := M) hp hp5 hua hP2
    have hcomb := pDvdRat_add hstep hPlog
    convert hcomb using 1
    ring

lemma truncLog_inj {p M : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {w : ℚ}
    (hw2 : pDvdRat p 2 w) (hlog : pDvdRat p M (truncLog M w)) : pDvdRat p M w := by
  by_cases hM2 : M ≤ 2
  · exact pDvdRat_mono hM2 hw2
  · have hstep : ∀ t : ℕ, 2 ≤ t → t ≤ M → pDvdRat p t w := by
      intro t ht2 htM
      induction t with
      | zero => omega
      | succ t ih =>
        by_cases h2 : t + 1 ≤ 2
        · exact pDvdRat_mono h2 hw2
        · have ht : pDvdRat p t w := ih (by omega) (by omega)
          have hlog' : pDvdRat p (t + 1) (truncLog M w) := pDvdRat_mono htM hlog
          have htail : pDvdRat p (t + 1) (∑ k ∈ Icc 2 M, (-1 : ℚ) ^ (k - 1) * w ^ k / (k : ℚ)) := by
            refine pDvdRat_sum (fun k hk => ?_)
            have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
            have hwk : pDvdRat p (k * t) (w ^ k) := pDvdRat_pow ht k
            have hvp : padicValNat p k ≤ k - 1 := by
              have h4 := four_mul_padicValNat_le hp hp5 (by omega : 1 ≤ k)
              omega
            have ht_ge2 : 2 ≤ t := by omega
            have hkt : k + t ≤ k * t := by nlinarith
            have hdiv := pDvdRat_div_nat hp (by omega : 0 < k) hvp (by omega : k - 1 ≤ 0 + k * t)
              (pDvdRat_mul (pDvdRat_of_int_zero p ((-1 : ℤ) ^ (k - 1))) hwk)
            have hrew : (-1 : ℚ) ^ (k - 1) * w ^ k / (k : ℚ) =
                ((((-1 : ℤ) ^ (k - 1) : ℤ) : ℚ) * w ^ k) / (k : ℚ) := by push_cast; ring
            rw [hrew]
            exact pDvdRat_mono (by omega : t + 1 ≤ 0 + k * t - (k - 1)) hdiv
          have hsplit : truncLog M w = w + ∑ k ∈ Icc 2 M, (-1 : ℚ) ^ (k - 1) * w ^ k / (k : ℚ) := by
            unfold truncLog
            have hIcc : Icc 1 M = insert 1 (Icc 2 M) := by
              ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
            rw [hIcc, Finset.sum_insert (by simp)]
            simp
          have hw_eq : w = truncLog M w - ∑ k ∈ Icc 2 M, (-1 : ℚ) ^ (k - 1) * w ^ k / (k : ℚ) := by
            linarith
          rw [hw_eq]
          exact pDvdRat_sub hlog' htail
    exact hstep M (by omega) le_rfl

/-- Integer-scaled Faulhaber polynomial: `(faulhaberInt d).eval (B : ℤ) = (d+1)! * ∑_{j<B} j^d`. -/
noncomputable def faulhaberInt : ℕ → ℤ[X]
  | 0 => X
  | d + 1 =>
    C ((d + 1).factorial : ℤ) * X ^ (d + 2) -
    ∑ m ∈ (range (d + 1)).attach,
      C (((d + 2).choose m.1 * ((d + 1).factorial / (m.1 + 1).factorial) : ℕ) : ℤ) *
        faulhaberInt m.1
termination_by d => d
decreasing_by
  exact Finset.mem_range.mp m.2

lemma faulhaberInt_eval (d B : ℕ) :
    (faulhaberInt d).eval (B : ℤ) = ((d + 1).factorial : ℤ) * ∑ j ∈ range B, (j : ℤ) ^ d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    rcases d with _ | d
    · simp [faulhaberInt]
    · rw [faulhaberInt]
      simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_finsetSum]
      have htel : (B : ℤ) ^ (d + 2) = ∑ j ∈ range B, ((j + 1 : ℤ) ^ (d + 2) - (j : ℤ) ^ (d + 2)) := by
        have hgen : ∀ B' : ℕ, (B' : ℤ) ^ (d + 2) =
            ∑ j ∈ range B', ((j + 1 : ℤ) ^ (d + 2) - (j : ℤ) ^ (d + 2)) := by
          intro B'
          induction B' with
          | zero => simp
          | succ B' ihB =>
            rw [Finset.sum_range_succ, ← ihB]
            push_cast; ring
        exact hgen B
      have hexp : ∀ j : ℕ, (j + 1 : ℤ) ^ (d + 2) - (j : ℤ) ^ (d + 2) =
          ((d + 2 : ℕ) : ℤ) * (j : ℤ) ^ (d + 1) +
          ∑ m ∈ range (d + 1), ((d + 2).choose m : ℤ) * (j : ℤ) ^ m := by
        intro j
        rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ]
        simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one]
        have hch : (d + 2).choose (d + 1) = d + 2 := by
          rw [← Nat.choose_symm (by omega : d + 1 ≤ d + 2)]
          simp
        rw [hch]; ring
      have hsum_tel : (B : ℤ) ^ (d + 2) =
          ((d + 2 : ℕ) : ℤ) * (∑ j ∈ range B, (j : ℤ) ^ (d + 1)) +
          ∑ m ∈ range (d + 1), ((d + 2).choose m : ℤ) * (∑ j ∈ range B, (j : ℤ) ^ m) := by
        rw [htel, Finset.sum_congr rfl (fun j _ => hexp j), Finset.sum_add_distrib,
          ← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [← Finset.mul_sum]
      have hmul_tel := congrArg (fun z : ℤ => ((d + 1).factorial : ℤ) * z) hsum_tel
      have hfac : ((d + 1).factorial : ℤ) * ((d + 2 : ℕ) : ℤ) = ((d + 2).factorial : ℤ) := by
        have hnat : (d + 2).factorial = (d + 2) * (d + 1).factorial := Nat.factorial_succ (d + 1)
        rw [hnat]
        push_cast; ring
      rw [mul_add, ← mul_assoc, hfac] at hmul_tel
      have hmul_rhs : ((d + 1).factorial : ℤ) *
          ∑ m ∈ range (d + 1), ((d + 2).choose m : ℤ) * ∑ j ∈ range B, (j : ℤ) ^ m =
          ∑ m ∈ range (d + 1), ((d + 1).factorial : ℤ) *
            (((d + 2).choose m : ℤ) * ∑ j ∈ range B, (j : ℤ) ^ m) :=
        Finset.mul_sum _ _ _
      rw [hmul_rhs] at hmul_tel
      have hih_sum : ∑ m ∈ (range (d + 1)).attach,
          (((d + 2).choose m.1 * ((d + 1).factorial / (m.1 + 1).factorial) : ℕ) : ℤ) *
            (faulhaberInt m.1).eval (B : ℤ) =
          ∑ m ∈ range (d + 1), ((d + 1).factorial : ℤ) *
            (((d + 2).choose m : ℤ) * ∑ j ∈ range B, (j : ℤ) ^ m) := by
        have hstep : ∑ m ∈ (range (d + 1)).attach,
            (((d + 2).choose m.1 * ((d + 1).factorial / (m.1 + 1).factorial) : ℕ) : ℤ) *
              (faulhaberInt m.1).eval (B : ℤ) =
            ∑ m ∈ (range (d + 1)).attach, ((d + 1).factorial : ℤ) *
              (((d + 2).choose m.1 : ℤ) * ∑ j ∈ range B, (j : ℤ) ^ m.1) := by
          refine Finset.sum_congr rfl (fun m _ => ?_)
          have hmd : m.1 < d + 1 := Finset.mem_range.mp m.2
          rw [ih m.1 hmd]
          have hdvd : (m.1 + 1).factorial ∣ (d + 1).factorial := Nat.factorial_dvd_factorial (by omega)
          have hdiv : ((d + 1).factorial / (m.1 + 1).factorial : ℕ) * (m.1 + 1).factorial = (d + 1).factorial :=
            Nat.div_mul_cancel hdvd
          have hdivZ : (((d + 1).factorial / (m.1 + 1).factorial : ℕ) : ℤ) * ((m.1 + 1).factorial : ℤ) =
              ((d + 1).factorial : ℤ) := by exact_mod_cast hdiv
          rw [Nat.cast_mul]
          linear_combination ((d + 2).choose m.1 : ℤ) * (∑ j ∈ range B, (j : ℤ) ^ m.1) * hdivZ
        rw [hstep, Finset.sum_attach (range (d + 1)) (fun m =>
          ((d + 1).factorial : ℤ) * (((d + 2).choose m : ℤ) * ∑ j ∈ range B, (j : ℤ) ^ m))]
      rw [hih_sum]
      linarith

lemma faulhaberInt_eval_zero (d : ℕ) : (faulhaberInt d).eval 0 = 0 := by
  have := faulhaberInt_eval d 0
  simpa using this

/-- Power-sum divisibility: `B * D * (B + D)` divides `(2k+1)! * S_k(B, D)` in `ℤ`. -/
lemma power_sum_dvd (k B D : ℕ) :
    ((B * D * (B + D) : ℕ) : ℤ) ∣
      ((2 * k + 1).factorial : ℤ) *
        ∑ j ∈ range B, ((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ k -
                        ((j : ℤ) * ((j : ℤ) + 1)) ^ k) := by
  -- Inner polynomial ring `ℤ[X]` represents variable `B`; outer `Polynomial (ℤ[X])` represents `D`.
  -- Auxiliary `Q : Polynomial (ℤ[X])` where inner `ℤ[X]` is `D` and outer `X` is `j`:
  let Q : Polynomial (ℤ[X]) :=
    ((C (X : ℤ[X]) + X) * (C (X : ℤ[X]) + X + 1)) ^ k - (X * (X + 1)) ^ k
  have hQdeg : Q.natDegree ≤ 2 * k := by
    have hd1 : ((C (X : ℤ[X]) + X) * (C (X : ℤ[X]) + X + 1)).natDegree ≤ 2 := by
      have h1 : (C (X : ℤ[X]) + X).natDegree ≤ 1 :=
        (natDegree_add_le _ _).trans (max_le (by simp) (by simp))
      have h2 : (C (X : ℤ[X]) + X + 1).natDegree ≤ 1 :=
        (natDegree_add_le _ _).trans (max_le h1 (by simp))
      exact natDegree_mul_le.trans (by omega)
    have hd2 : ((X : Polynomial (ℤ[X])) * (X + 1)).natDegree ≤ 2 := by
      have hX : (X : Polynomial (ℤ[X])).natDegree ≤ 1 := natDegree_X_le
      have h1 : ((X : Polynomial (ℤ[X])) + 1).natDegree ≤ 1 :=
        (natDegree_add_le _ _).trans (max_le hX (by simp))
      exact natDegree_mul_le.trans (by omega)
    exact (natDegree_sub_le _ _).trans (max_le (natDegree_pow_le.trans (by nlinarith))
      (natDegree_pow_le.trans (by nlinarith)))
  let Fsc : ℕ → ℤ[X] := fun m =>
    C (((2 * k + 1).factorial / (m + 1).factorial : ℕ) : ℤ) * faulhaberInt m
  let P_BD : Polynomial (ℤ[X]) :=
    ∑ m ∈ range (2 * k + 1), (Q.coeff m).map C * C (Fsc m)
  have hFsc_eval : ∀ m ∈ range (2 * k + 1), ∀ b : ℕ,
      (Fsc m).eval (b : ℤ) = ((2 * k + 1).factorial : ℤ) * ∑ j ∈ range b, (j : ℤ) ^ m := by
    intro m hm b
    have hmk : m ≤ 2 * k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    simp only [Fsc, eval_mul, eval_C, faulhaberInt_eval]
    have hdvd : (m + 1).factorial ∣ (2 * k + 1).factorial := Nat.factorial_dvd_factorial (by omega)
    have hdiv : ((2 * k + 1).factorial / (m + 1).factorial : ℕ) * (m + 1).factorial =
        (2 * k + 1).factorial := Nat.div_mul_cancel hdvd
    have hdivZ : (((2 * k + 1).factorial / (m + 1).factorial : ℕ) : ℤ) * ((m + 1).factorial : ℤ) =
        ((2 * k + 1).factorial : ℤ) := by exact_mod_cast hdiv
    rw [← mul_assoc, hdivZ]
  have hP_eval : ∀ (b : ℕ) (d : ℤ),
      (P_BD.eval (C d)).eval (b : ℤ) =
        ((2 * k + 1).factorial : ℤ) *
          ∑ j ∈ range b, (((d + (j : ℤ)) * (d + (j : ℤ) + 1)) ^ k - ((j : ℤ) * ((j : ℤ) + 1)) ^ k) := by
    intro b d
    have hmap_eval : ∀ (f : ℤ[X]), (f.map (C : ℤ →+* ℤ[X])).eval (C d) = C (f.eval d) := by
      intro f
      induction f using Polynomial.induction_on' with
      | add p q ihp ihq => rw [Polynomial.map_add, eval_add, ihp, ihq, eval_add, map_add]
      | monomial m c => simp
    have hlhs : (P_BD.eval (C d)).eval (b : ℤ) =
        ∑ m ∈ range (2 * k + 1), (Q.coeff m).eval d * (Fsc m).eval (b : ℤ) := by
      simp only [P_BD, eval_finsetSum, eval_mul, eval_C, hmap_eval]
    rw [hlhs]
    have h2 : ∑ m ∈ range (2 * k + 1), (Q.coeff m).eval d * (Fsc m).eval (b : ℤ) =
        ((2 * k + 1).factorial : ℤ) *
          ∑ j ∈ range b, ∑ m ∈ range (2 * k + 1), (Q.coeff m).eval d * (j : ℤ) ^ m := by
      rw [Finset.mul_sum]
      have hinner : ∑ j ∈ range b, ((2 * k + 1).factorial : ℤ) *
          ∑ m ∈ range (2 * k + 1), (Q.coeff m).eval d * (j : ℤ) ^ m =
          ∑ j ∈ range b, ∑ m ∈ range (2 * k + 1),
            ((2 * k + 1).factorial : ℤ) * ((Q.coeff m).eval d * (j : ℤ) ^ m) :=
        Finset.sum_congr rfl (fun j _ => Finset.mul_sum _ _ _)
      rw [hinner, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [hFsc_eval m hm b, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => by ring)
    rw [h2]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hdeg_map : (Q.map (evalRingHom d)).natDegree ≤ 2 * k :=
      natDegree_map_le.trans hQdeg
    have hq_sum : ∑ m ∈ range (2 * k + 1), (Q.coeff m).eval d * (j : ℤ) ^ m =
        (Q.map (evalRingHom d)).eval (j : ℤ) := by
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg_map)]
      refine Finset.sum_congr rfl (fun m _ => by
        rw [coeff_map]; rfl)
    rw [hq_sum]
    simp only [Q, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_add,
      Polynomial.map_C, Polynomial.map_X, Polynomial.map_one, eval_sub, eval_pow, eval_mul,
      eval_add, eval_C, eval_X, eval_one]
    change (((X : ℤ[X]).eval d + (j : ℤ)) * ((X : ℤ[X]).eval d + (j : ℤ) + 1)) ^ k -
        ((j : ℤ) * ((j : ℤ) + 1)) ^ k = _
    simp
  -- Factor 1: X ∣ P_BD (since P_BD.eval 0 = 0)
  have hzero_of_nat : ∀ f : ℤ[X], (∀ b : ℕ, 1 ≤ b → f.eval (b : ℤ) = 0) → f = 0 := by
    intro f hf
    by_contra hne
    have hsub : (range (f.natDegree + 1)).image (fun b : ℕ => ((b + 1 : ℕ) : ℤ)) ⊆ f.roots.toFinset := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨b, _, rfl⟩
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
      exact hf (b + 1) (by omega)
    have hinj : Function.Injective (fun b : ℕ => ((b + 1 : ℕ) : ℤ)) := fun a b h => by
      have := Int.ofNat.inj h; omega
    have hcard1 : ((range (f.natDegree + 1)).image (fun b : ℕ => ((b + 1 : ℕ) : ℤ))).card = f.natDegree + 1 := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
    have hcard2 : f.roots.toFinset.card ≤ f.natDegree :=
      (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' f)
    have := Finset.card_le_card hsub
    omega
  have hP_eval0 : P_BD.eval 0 = 0 := by
    apply hzero_of_nat
    intro b _
    simpa using hP_eval b 0
  obtain ⟨P1, hP1⟩ : X ∣ P_BD := by
    rw [show (X : Polynomial (ℤ[X])) = X - C 0 by simp, Polynomial.dvd_iff_isRoot]
    exact hP_eval0
  -- Factor 2: (X + C X) ∣ P1 (since P1.eval (-X) = 0; note `-X : ℤ[X]` is the element of the base ring!)
  have hP1_root : P1.eval (-X : ℤ[X]) = 0 := by
    apply hzero_of_nat
    intro b hb
    have h1 := hP_eval b (-(b : ℤ))
    have hsym : ∑ j ∈ range b, (((-(b : ℤ) + (j : ℤ)) * (-(b : ℤ) + (j : ℤ) + 1)) ^ k -
        ((j : ℤ) * ((j : ℤ) + 1)) ^ k) = 0 := by
      rw [Finset.sum_sub_distrib]
      have href := Finset.sum_range_reflect (fun j => ((j : ℤ) * ((j : ℤ) + 1)) ^ k) b
      have heq : ∑ j ∈ range b, ((-(b : ℤ) + (j : ℤ)) * (-(b : ℤ) + (j : ℤ) + 1)) ^ k =
          ∑ j ∈ range b, (((b - 1 - j : ℕ) : ℤ) * (((b - 1 - j : ℕ) : ℤ) + 1)) ^ k := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        have hjb : j ≤ b - 1 := by rw [Finset.mem_range] at hj; omega
        have hsub : ((b - 1 - j : ℕ) : ℤ) = (b : ℤ) - 1 - (j : ℤ) := by omega
        rw [hsub]; congr 1; ring
      rw [heq, href, sub_self]
    rw [hsym, mul_zero] at h1
    have hev_neg : ∀ R : Polynomial (ℤ[X]), (R.eval (-X : ℤ[X])).eval (b : ℤ) =
        (R.eval (C (-(b : ℤ)))).eval (b : ℤ) := by
      intro R
      induction R using Polynomial.induction_on' with
      | add p q ihp ihq => simp [ihp, ihq]
      | monomial m c =>
        simp only [eval_monomial, eval_mul, eval_pow, eval_neg, eval_C, eval_X]
    have h2 : (P_BD.eval (-X : ℤ[X])).eval (b : ℤ) = 0 := by rw [hev_neg, h1]
    rw [hP1, eval_mul, eval_X, eval_mul, eval_neg, eval_X] at h2
    have hbne : -(b : ℤ) ≠ 0 := by omega
    exact (mul_eq_zero.mp h2).resolve_left hbne
  obtain ⟨P2, hP2⟩ : (X - C (-X : ℤ[X]) : Polynomial (ℤ[X])) ∣ P1 := by
    rw [Polynomial.dvd_iff_isRoot]
    exact hP1_root
  -- Factor 3: C X ∣ P2 (since evaluating inner B = 0 gives P_BD.map (evalRingHom 0) = 0!)
  have hP_map0 : P_BD.map (evalRingHom (0 : ℤ)) = 0 := by
    simp only [P_BD, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]
    refine Finset.sum_eq_zero (fun m _ => ?_)
    have hF0 : (evalRingHom (0 : ℤ)) (Fsc m) = 0 := by
      change (Fsc m).eval 0 = 0
      simp [Fsc, faulhaberInt_eval_zero]
    rw [hF0, map_zero, mul_zero]
  have hP2_map0 : P2.map (evalRingHom (0 : ℤ)) = 0 := by
    have h1 := hP_map0
    rw [hP1, hP2, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C] at h1
    have h0neg : (evalRingHom (0 : ℤ)) (-X : ℤ[X]) = 0 := by
      change (-X : ℤ[X]).eval 0 = 0; simp
    rw [h0neg, map_zero, sub_zero] at h1
    have hX2 : (X : ℤ[X]) * (X : ℤ[X]) ≠ 0 := mul_ne_zero X_ne_zero X_ne_zero
    rw [← mul_assoc] at h1
    exact (mul_eq_zero.mp h1).resolve_left hX2
  have hP2_coeff0 : ∀ m, (X : ℤ[X]) ∣ P2.coeff m := by
    intro m
    rw [show (X : ℤ[X]) = X - C 0 by simp, Polynomial.dvd_iff_isRoot]
    have h := congrArg (fun f : ℤ[X] => f.coeff m) hP2_map0
    rw [coeff_map, coeff_zero] at h
    exact h
  -- Write P2 = C X * P3 by dividing each coefficient by X (via P2 = ∑ m, C (P2.coeff m) * X^m)
  have hCX_dvd_P2 : C (X : ℤ[X]) ∣ P2 := by
    rw [Polynomial.as_sum_range_C_mul_X_pow P2]
    refine Finset.dvd_sum (fun m _ => ?_)
    obtain ⟨q, hq⟩ := hP2_coeff0 m
    refine ⟨C q * X ^ m, ?_⟩
    rw [hq, map_mul, mul_assoc]
  obtain ⟨P3, hP3⟩ := hCX_dvd_P2
  -- Now evaluate P_BD = X * ((X - C (-X)) * (C X * P3)) at outer D and inner B!
  have hfinal := hP_eval B (D : ℤ)
  rw [hP1, hP2, hP3] at hfinal
  simp only [eval_mul, eval_sub, eval_X, eval_C, sub_neg_eq_add, eval_add] at hfinal
  refine ⟨(P3.eval (C (D : ℤ))).eval (B : ℤ), ?_⟩
  push_cast
  linarith

/-- For prime `p ≥ 5`, `p` divides the numerator of `∑_{i=1}^{(p-1)/2} (i*(p-i))⁻¹` in `ℤ_{(p)}`. -/
lemma half_sum_inv_p_dvd {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    pDvdRat p 1 (∑ i ∈ Icc 1 ((p - 1) / 2), (((i * (p - i) : ℕ) : ℚ)⁻¹)) := by
  have : Fact p.Prime := ⟨hp⟩
  set h := (p - 1) / 2
  have h2h : 2 * h + 1 = p := by
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
    omega
  -- Common denominator P = ∏ i ∈ Icc 1 h, (i * (p - i))
  set P : ℕ := ∏ i ∈ Icc 1 h, (i * (p - i))
  have hP_pos : 0 < P := Finset.prod_pos (fun i hi => by
    have := Finset.mem_Icc.mp hi; exact Nat.mul_pos (by omega) (by omega))
  have hP_cop : Nat.Coprime p P := by
    refine nat_coprime_prod_right (fun i hi => ?_)
    have hi' := Finset.mem_Icc.mp hi
    have hc1 : Nat.Coprime p i := (hp.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
    have hc2 : Nat.Coprime p (p - i) := (hp.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
    exact hc1.mul_right hc2
  -- Numerator N = ∑ i ∈ Icc 1 h, P / (i * (p - i))
  set N : ℕ := ∑ i ∈ Icc 1 h, P / (i * (p - i))
  have hsum_eq : ∑ i ∈ Icc 1 h, (((i * (p - i) : ℕ) : ℚ)⁻¹) = (N : ℚ) / (P : ℚ) := by
    have hPq : (P : ℚ) ≠ 0 := by positivity
    rw [eq_div_iff hPq, Finset.sum_mul]
    simp only [N, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hdvd : i * (p - i) ∣ P := Finset.dvd_prod_of_mem _ hi
    have hpos : 0 < i * (p - i) := by have := Finset.mem_Icc.mp hi; exact Nat.mul_pos (by omega) (by omega)
    have hmul : (P / (i * (p - i)) : ℕ) * (i * (p - i)) = P := Nat.div_mul_cancel hdvd
    have hmulq : ((P / (i * (p - i)) : ℕ) : ℚ) * ((i * (p - i) : ℕ) : ℚ) = (P : ℚ) := by exact_mod_cast hmul
    rw [← hmulq]
    have hne : ((i * (p - i) : ℕ) : ℚ) ≠ 0 := by positivity
    field_simp
  -- Show p ∣ N by working in ZMod p (which is a Field)!
  have hp_dvd_N : p ∣ N := by
    rw [← ZMod.natCast_eq_zero_iff]
    have hPz : (P : ZMod p) ≠ 0 := by
      intro h0
      have hd : p ∣ P := (ZMod.natCast_eq_zero_iff P p).mp h0
      have h1 : p ∣ Nat.gcd p P := Nat.dvd_gcd dvd_rfl hd
      rw [hP_cop.gcd_eq_one] at h1
      exact hp.not_dvd_one h1
    have hNz : (N : ZMod p) = (P : ZMod p) * ∑ i ∈ Icc 1 h, -((i : ZMod p) ^ 2)⁻¹ := by
      simp only [N, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hi' := Finset.mem_Icc.mp hi
      have hiz : (i : ZMod p) ≠ 0 := by
        intro h0
        have := (ZMod.natCast_eq_zero_iff i p).mp h0
        exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) this
      have hpiz : ((i * (p - i) : ℕ) : ZMod p) = -((i : ZMod p) ^ 2) := by
        have hsub : ((p - i : ℕ) : ZMod p) = -(i : ZMod p) := by
          have h1 : ((p - i : ℕ) : ZMod p) + (i : ZMod p) = (p : ZMod p) := by
            rw [← Nat.cast_add, Nat.sub_add_cancel (by omega)]
          rw [ZMod.natCast_self] at h1
          exact eq_neg_of_add_eq_zero_left h1
        rw [Nat.cast_mul, hsub]; ring
      have hdvd : i * (p - i) ∣ P := Finset.dvd_prod_of_mem _ hi
      have hmul : ((P / (i * (p - i)) : ℕ) : ZMod p) * ((i * (p - i) : ℕ) : ZMod p) = (P : ZMod p) := by
        rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
      rw [hpiz] at hmul
      have hsqne : -((i : ZMod p) ^ 2) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 2 hiz)
      calc ((P / (i * (p - i)) : ℕ) : ZMod p)
          = ((P / (i * (p - i)) : ℕ) : ZMod p) * (-((i : ZMod p) ^ 2) * (-((i : ZMod p) ^ 2))⁻¹) := by
              rw [mul_inv_cancel₀ hsqne, mul_one]
        _ = (((P / (i * (p - i)) : ℕ) : ZMod p) * -((i : ZMod p) ^ 2)) * (-((i : ZMod p) ^ 2))⁻¹ := by ring
        _ = (P : ZMod p) * -((i : ZMod p) ^ 2)⁻¹ := by rw [hmul, inv_neg]
    -- Show ∑ i ∈ Icc 1 h, ((i : ZMod p) ^ 2)⁻¹ = 0
    have hsum_zero : ∑ i ∈ Icc 1 h, ((i : ZMod p) ^ 2)⁻¹ = 0 := by
      have hpair : ∑ i ∈ Icc 1 h, ((i : ZMod p) ^ 2)⁻¹ =
          ∑ i ∈ Icc (h + 1) (p - 1), ((i : ZMod p) ^ 2)⁻¹ := by
        refine Finset.sum_bij (fun i _ => p - i) ?_ ?_ ?_ ?_
        · intro i hi; simp only [Finset.mem_Icc] at hi ⊢; omega
        · intro i1 hi1 i2 hi2 heq; simp only [Finset.mem_Icc] at hi1 hi2; omega
        · intro j hj; simp only [Finset.mem_Icc] at hj
          exact ⟨p - j, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro i hi
          have hi' := Finset.mem_Icc.mp hi
          have hsub : ((p - i : ℕ) : ZMod p) = -(i : ZMod p) := by
            have h1 : ((p - i : ℕ) : ZMod p) + (i : ZMod p) = (p : ZMod p) := by
              rw [← Nat.cast_add, Nat.sub_add_cancel (by omega)]
            rw [ZMod.natCast_self] at h1
            exact eq_neg_of_add_eq_zero_left h1
          rw [hsub, neg_sq]
      have hfull : (∑ i ∈ Icc 1 h, ((i : ZMod p) ^ 2)⁻¹) +
          (∑ i ∈ Icc (h + 1) (p - 1), ((i : ZMod p) ^ 2)⁻¹) =
          ∑ x : ZMod p, (x ^ 2)⁻¹ := by
        rw [← Finset.sum_union (by
          rw [Finset.disjoint_left]; intro x hx1 hx2; simp only [Finset.mem_Icc] at hx1 hx2; omega)]
        have hun : Icc 1 h ∪ Icc (h + 1) (p - 1) = Ico 1 p := by
          ext x; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ico]; omega
        rw [hun]
        have h0 : ∑ x : ZMod p, (x ^ 2)⁻¹ = ∑ x ∈ Finset.univ.erase (0 : ZMod p), (x ^ 2)⁻¹ := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p))]
          rw [zero_pow (by decide : 2 ≠ 0), inv_zero, zero_add]
        rw [h0]
        refine Finset.sum_bij (fun i _ => (i : ZMod p)) ?_ ?_ ?_ ?_
        · intro i hi
          have hi' := Finset.mem_Ico.mp hi
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
          intro hzero
          exact Nat.not_dvd_of_pos_of_lt hi'.1 hi'.2 ((ZMod.natCast_eq_zero_iff i p).mp hzero)
        · intro i1 hi1 i2 hi2 heq
          have h1 := Finset.mem_Ico.mp hi1
          have h2 := Finset.mem_Ico.mp hi2
          have hv := congrArg ZMod.val heq
          rwa [ZMod.val_natCast_of_lt h1.2, ZMod.val_natCast_of_lt h2.2] at hv
        · intro x hx
          have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
          have hlt : x.val < p := ZMod.val_lt x
          have hpos : 1 ≤ x.val := by
            rcases Nat.eq_zero_or_pos x.val with h0' | hp'
            · exact absurd ((ZMod.val_eq_zero x).mp h0') hx0
            · exact hp'
          exact ⟨x.val, Finset.mem_Ico.mpr ⟨hpos, hlt⟩, ZMod.natCast_zmod_val x⟩
        · intro _ _; rfl
      have hall0 : ∑ x : ZMod p, (x ^ 2)⁻¹ = 0 := by
        have h2ne : (2 : ZMod p) ≠ 0 := by
          intro h0; have := (ZMod.natCast_eq_zero_iff 2 p).mp h0
          have := Nat.le_of_dvd (by decide) this; omega
        have h3ne : (3 : ZMod p) ≠ 0 := by
          intro h0; have := (ZMod.natCast_eq_zero_iff 3 p).mp h0
          have := Nat.le_of_dvd (by decide) this; omega
        set T : ZMod p := ∑ x : ZMod p, (x ^ 2)⁻¹
        have hmul : (2 : ZMod p) ^ 2 * T = T := by
          rw [Finset.mul_sum]
          have h1 : ∀ x : ZMod p, (2 : ZMod p) ^ 2 * (x ^ 2)⁻¹ = (((2 : ZMod p)⁻¹ * x) ^ 2)⁻¹ := by
            intro x; rw [mul_pow, mul_inv, inv_pow, inv_inv]
          rw [Finset.sum_congr rfl (fun x _ => h1 x)]
          exact Fintype.sum_equiv (Equiv.mulLeft₀ (2 : ZMod p)⁻¹ (inv_ne_zero h2ne)) _ _ (fun _ => rfl)
        have h3T : (3 : ZMod p) * T = 0 := by
          have : (3 : ZMod p) = (2 : ZMod p) ^ 2 - 1 := by norm_num
          rw [this, sub_mul, one_mul, hmul, sub_self]
        exact (mul_eq_zero.mp h3T).resolve_left h3ne
      rw [hall0, ← hpair, ← two_mul] at hfull
      have h2ne : (2 : ZMod p) ≠ 0 := by
        intro h0; have := (ZMod.natCast_eq_zero_iff 2 p).mp h0
        have := Nat.le_of_dvd (by decide) this; omega
      exact (mul_eq_zero.mp hfull).resolve_left h2ne
    rw [hNz, Finset.sum_neg_distrib, hsum_zero, neg_zero, mul_zero]
  obtain ⟨q, hq⟩ := hp_dvd_N
  refine ⟨q, P, hP_pos, hP_cop, ?_⟩
  rw [hsum_eq, hq]; push_cast; ring

/-- Block product `F p m = ∏_{i=1}^{p-1} (m * p + i)`. -/
def Fblock (p m : ℕ) : ℕ := ∏ i ∈ Ico 1 p, (m * p + i)

lemma Fblock_coprime {p : ℕ} (hp : p.Prime) (m : ℕ) : Nat.Coprime p (Fblock p m) := by
  refine nat_coprime_prod_right (fun i hi => ?_)
  have hi' := Finset.mem_Ico.mp hi
  rw [hp.coprime_iff_not_dvd]
  intro hd
  have hd_i : p ∣ i := (Nat.dvd_add_right (dvd_mul_left p m)).mp hd
  exact Nat.not_dvd_of_pos_of_lt hi'.1 hi'.2 hd_i

lemma Fblock_pair {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (m : ℕ) :
    (Fblock p m : ℚ) = ∏ i ∈ Icc 1 ((p - 1) / 2),
      (((i * (p - i) : ℕ) : ℚ) + ((m * (m + 1) : ℕ) : ℚ) * (p : ℚ) ^ 2) := by
  set h := (p - 1) / 2
  have h2h : 2 * h + 1 = p := by
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
    omega
  unfold Fblock
  have hsplit : Ico 1 p = Icc 1 h ∪ Icc (h + 1) (p - 1) := by
    ext x; simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Icc 1 h) (Icc (h + 1) (p - 1)) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2; simp only [Finset.mem_Icc] at hx1 hx2; omega
  rw [hsplit, Finset.prod_union hdisj, Nat.cast_mul, Nat.cast_prod, Nat.cast_prod]
  have hbij : ∏ i ∈ Icc (h + 1) (p - 1), ((m * p + i : ℕ) : ℚ) =
      ∏ i ∈ Icc 1 h, ((m * p + (p - i) : ℕ) : ℚ) := by
    refine Finset.prod_bij (fun j _ => p - j) ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
    · intro j1 hj1 j2 hj2 heq; simp only [Finset.mem_Icc] at hj1 hj2; omega
    · intro i hi; simp only [Finset.mem_Icc] at hi
      exact ⟨p - i, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro j hj; simp only [Finset.mem_Icc] at hj; congr 1; omega
  rw [hbij, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  have hi' := Finset.mem_Icc.mp hi
  have hsub : ((p - i : ℕ) : ℚ) = (p : ℚ) - (i : ℚ) := Nat.cast_sub (by omega)
  push_cast
  rw [hsub]
  ring

lemma factorial_mul_eq {p : ℕ} (hp : 0 < p) (m : ℕ) :
    (m * p).factorial = p ^ m * m.factorial * ∏ j ∈ range m, Fblock p j := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : ((m + 1) * p).factorial = (m * p).factorial * ∏ i ∈ Icc 1 p, (m * p + i) := by
      have hgen : ∀ a k : ℕ, (a + k).factorial = a.factorial * ∏ i ∈ Icc 1 k, (a + i) := by
        intro a k
        induction k with
        | zero => simp
        | succ k ihk =>
          rw [show a + (k + 1) = (a + k) + 1 by omega, Nat.factorial_succ, ihk]
          have hIcc : Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hIcc, Finset.prod_insert (by simp)]
          ring
      simpa [Nat.add_mul] using hgen (m * p) p
    have hIcc : ∏ i ∈ Icc 1 p, (m * p + i) = ((m + 1) * p) * Fblock p m := by
      have hs : Icc 1 p = insert p (Ico 1 p) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
      rw [hs, Finset.prod_insert (by simp), Fblock]
      have : m * p + p = (m + 1) * p := by ring
      rw [this]
    rw [hsplit, hIcc, ih, Finset.prod_range_succ, pow_succ, Nat.factorial_succ]
    ring

lemma choose_mul_Fblock {p : ℕ} (hp : 0 < p) (B D : ℕ) :
    ((B + D) * p).choose (B * p) * (∏ j ∈ range B, Fblock p j) =
      (B + D).choose B * (∏ j ∈ range B, Fblock p (D + j)) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show B * p ≤ (B + D) * p by nlinarith)
  have h2 := Nat.choose_mul_factorial_mul_factorial (show B ≤ B + D by omega)
  have hs1 : (B + D) * p - B * p = D * p := by
    rw [Nat.add_mul, Nat.add_sub_cancel_left]
  have hs2 : B + D - B = D := Nat.add_sub_cancel_left B D
  rw [hs1] at h1; rw [hs2] at h2
  have hprod_split : ∏ j ∈ range (B + D), Fblock p j =
      (∏ j ∈ range D, Fblock p j) * (∏ j ∈ range B, Fblock p (D + j)) := by
    have hs : range (B + D) = range D ∪ Ico D (B + D) := by
      ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    have hd : Disjoint (range D) (Ico D (B + D)) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2; simp only [Finset.mem_range, Finset.mem_Ico] at hx1 hx2; omega
    rw [hs, Finset.prod_union hd]
    congr 1
    refine Finset.prod_bij (fun j _ => j - D) ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢; omega
    · intro j1 hj1 j2 hj2 heq; simp only [Finset.mem_Ico] at hj1 hj2; omega
    · intro j hj; simp only [Finset.mem_range] at hj
      exact ⟨D + j, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro j hj; simp only [Finset.mem_Ico] at hj; congr 1; omega
  have hpos : 0 < p ^ (B + D) * B.factorial * D.factorial * (∏ j ∈ range D, Fblock p j) := by
    have hFp : 0 < ∏ j ∈ range D, Fblock p j :=
      Finset.prod_pos (fun j _ => Finset.prod_pos (fun i hi => by
        have := (Finset.mem_Ico.mp hi).1; omega))
    positivity
  apply Nat.eq_of_mul_eq_mul_left hpos
  have hlhs : p ^ (B + D) * B.factorial * D.factorial * (∏ j ∈ range D, Fblock p j) *
      (((B + D) * p).choose (B * p) * ∏ j ∈ range B, Fblock p j) =
      ((B + D) * p).choose (B * p) * (B * p).factorial * (D * p).factorial := by
    rw [factorial_mul_eq hp B, factorial_mul_eq hp D, pow_add]; ring
  have hrhs : p ^ (B + D) * B.factorial * D.factorial * (∏ j ∈ range D, Fblock p j) *
      ((B + D).choose B * ∏ j ∈ range B, Fblock p (D + j)) =
      ((B + D) * p).factorial := by
    rw [factorial_mul_eq hp (B + D), hprod_split, ← h2]; ring
  rw [hlhs, hrhs, h1]

/-- Main Kazandzidis F-product congruence:
`p^(3 + v_p(B) + v_p(D) + v_p(B+D)) ∣ ∏_{j<B} F(D+j) - ∏_{j<B} F(j)`. -/
lemma Fblock_prod_congr {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (B D : ℕ) (hB : 0 < B) (hD : 0 < D) :
    ((p : ℤ) ^ (3 + padicValNat p B + padicValNat p D + padicValNat p (B + D))) ∣
      ((∏ j ∈ range B, Fblock p (D + j) : ℕ) : ℤ) - ((∏ j ∈ range B, Fblock p j : ℕ) : ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  set M := 3 + padicValNat p B + padicValNat p D + padicValNat p (B + D)
  set h := (p - 1) / 2
  have h2h : 2 * h + 1 = p := by
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
    omega
  set P0 : ℕ := ∏ j ∈ range B, Fblock p j
  set P1 : ℕ := ∏ j ∈ range B, Fblock p (D + j)
  set F0 : ℕ := Fblock p 0
  have hF0_pos : 0 < F0 := Finset.prod_pos (fun i hi => by have := (Finset.mem_Ico.mp hi).1; omega)
  have hF0_cop : Nat.Coprime p F0 := Fblock_coprime hp 0
  have hP0_pos : 0 < P0 := Finset.prod_pos (fun j _ =>
    Finset.prod_pos (fun i hi => by have := (Finset.mem_Ico.mp hi).1; omega))
  have hP0_cop : Nat.Coprime p P0 := nat_coprime_prod_right (fun j _ => Fblock_coprime hp j)
  -- Express P1 / F0^B and P0 / F0^B as products of (1 + u_{j,i}) where p^2 ∣ u_{j,i}!
  have hF0_pair : (F0 : ℚ) = ∏ i ∈ Icc 1 h, ((i * (p - i) : ℕ) : ℚ) := by
    simpa [F0, h] using Fblock_pair hp hp5 0
  have hratio : ∀ m : ℕ, (Fblock p m : ℚ) / (F0 : ℚ) =
      ∏ i ∈ Icc 1 h, (1 + ((m * (m + 1) : ℕ) : ℚ) * (p : ℚ) ^ 2 / ((i * (p - i) : ℕ) : ℚ)) := by
    intro m
    rw [Fblock_pair hp hp5 m, hF0_pair, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have hi' := Finset.mem_Icc.mp hi
    have hne : ((i * (p - i) : ℕ) : ℚ) ≠ 0 := by
      have : 0 < i * (p - i) := Nat.mul_pos (by omega) (by omega)
      positivity
    field_simp
  let u : ℕ → ℕ × ℕ → ℚ := fun shift ji =>
    (((shift + ji.1) * (shift + ji.1 + 1) : ℕ) : ℚ) * (p : ℚ) ^ 2 / ((ji.2 * (p - ji.2) : ℕ) : ℚ)
  let S_idx : Finset (ℕ × ℕ) := range B ×ˢ Icc 1 h
  have hu_p2 : ∀ shift, ∀ ji ∈ S_idx, pDvdRat p 2 (u shift ji) := by
    intro shift ji hji
    have hi' := Finset.mem_Icc.mp (Finset.mem_product.mp hji).2
    have hpos : 0 < ji.2 * (p - ji.2) := Nat.mul_pos (by omega) (by omega)
    have hcop : Nat.Coprime p (ji.2 * (p - ji.2)) :=
      ((hp.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).mul_right
        ((hp.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)))
    exact ⟨((shift + ji.1) * (shift + ji.1 + 1) : ℕ), ji.2 * (p - ji.2), hpos, hcop, by
      simp only [u]; push_cast; ring⟩
  have hP1_eq : (P1 : ℚ) / ((F0 : ℚ) ^ B) = ∏ ji ∈ S_idx, (1 + u D ji) := by
    simp only [P1, S_idx, Finset.prod_product, Nat.cast_prod]
    rw [show (F0 : ℚ) ^ B = ∏ _j ∈ range B, (F0 : ℚ) by simp, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl (fun j _ => hratio (D + j))
  have hP0_eq : (P0 : ℚ) / ((F0 : ℚ) ^ B) = ∏ ji ∈ S_idx, (1 + u 0 ji) := by
    simp only [P0, S_idx, Finset.prod_product, Nat.cast_prod]
    rw [show (F0 : ℚ) ^ B = ∏ _j ∈ range B, (F0 : ℚ) by simp, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl (fun j _ => by simpa [u] using hratio j)
  -- Apply truncLog_prod to both products!
  obtain ⟨hQ1_2, hQ1_log⟩ := truncLog_prod S_idx (M := M) hp hp5 (u D) (hu_p2 D)
  obtain ⟨hQ0_2, hQ0_log⟩ := truncLog_prod S_idx (M := M) hp hp5 (u 0) (hu_p2 0)
  -- Show ∑ truncLog M (u D ji) - ∑ truncLog M (u 0 ji) has pDvdRat p M!
  have hlog_diff : pDvdRat p M (∑ ji ∈ S_idx, truncLog M (u D ji) - ∑ ji ∈ S_idx, truncLog M (u 0 ji)) := by
    have hrew : (∑ ji ∈ S_idx, truncLog M (u D ji)) - (∑ ji ∈ S_idx, truncLog M (u 0 ji)) =
        ∑ k ∈ Icc 1 M, ((-1 : ℚ) ^ (k - 1) * (p : ℚ) ^ (2 * k) / (k : ℚ)) *
          (∑ i ∈ Icc 1 h, (((i * (p - i) : ℕ) : ℚ)⁻¹) ^ k) *
          (∑ j ∈ range B, (((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ k -
                            ((j : ℤ) * ((j : ℤ) + 1)) ^ k : ℤ) : ℚ)) := by
      simp only [truncLog, ← Finset.sum_sub_distrib]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      conv_lhs => simp only [S_idx, Finset.sum_product, u, mul_pow, div_pow, ← pow_mul]
      have hcomm : ∑ j ∈ range B, ∑ i ∈ Icc 1 h,
          ((-1 : ℚ) ^ (k - 1) * ((((D + j) * (D + j + 1) : ℕ) : ℚ) ^ k * (p : ℚ) ^ (2 * k) /
            ((i * (p - i) : ℕ) : ℚ) ^ k) / (k : ℚ) -
           (-1 : ℚ) ^ (k - 1) * ((((0 + j) * (0 + j + 1) : ℕ) : ℚ) ^ k * (p : ℚ) ^ (2 * k) /
            ((i * (p - i) : ℕ) : ℚ) ^ k) / (k : ℚ)) =
          ∑ j ∈ range B, ((-1 : ℚ) ^ (k - 1) * (p : ℚ) ^ (2 * k) / (k : ℚ)) *
            (∑ i ∈ Icc 1 h, (((i * (p - i) : ℕ) : ℚ)⁻¹) ^ k) *
            (((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ k -
              ((j : ℤ) * ((j : ℤ) + 1)) ^ k : ℤ) : ℚ) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        push_cast
        rw [inv_pow]
        ring
      rw [hcomm, ← Finset.mul_sum]
    rw [hrew]
    refine pDvdRat_sum (fun k hk => ?_)
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hV : (p : ℤ) ^ (padicValNat p B + padicValNat p D + padicValNat p (B + D)) ∣
        ((B * D * (B + D) : ℕ) : ℤ) := by
      have h1 : p ^ padicValNat p B ∣ B := pow_padicValNat_dvd
      have h2 : p ^ padicValNat p D ∣ D := pow_padicValNat_dvd
      have h3 : p ^ padicValNat p (B + D) ∣ B + D := pow_padicValNat_dvd
      have hmul : p ^ (padicValNat p B + padicValNat p D + padicValNat p (B + D)) ∣ B * D * (B + D) := by
        rw [pow_add, pow_add]; exact mul_dvd_mul (mul_dvd_mul h1 h2) h3
      exact_mod_cast hmul
    have hSk_dvd : (p : ℤ) ^ (padicValNat p B + padicValNat p D + padicValNat p (B + D)) ∣
        ((2 * k + 1).factorial : ℤ) *
          ∑ j ∈ range B, ((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ k -
                          ((j : ℤ) * ((j : ℤ) + 1)) ^ k) :=
      hV.trans (power_sum_dvd k B D)
    set V := padicValNat p B + padicValNat p D + padicValNat p (B + D)
    have hinv_sum_0 : pDvdRat p 0 (∑ i ∈ Icc 1 h, (((i * (p - i) : ℕ) : ℚ)⁻¹) ^ k) := by
      refine pDvdRat_sum (fun i hi => ?_)
      have hi' := Finset.mem_Icc.mp hi
      have hpos : 0 < i * (p - i) := Nat.mul_pos (by omega) (by omega)
      have hcop : Nat.Coprime p (i * (p - i)) :=
        ((hp.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).mul_right
          ((hp.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)))
      simpa using pDvdRat_pow (pDvdRat_inv_nat hpos hcop) k
    by_cases hk_eq1 : k = 1
    · subst hk_eq1
      have hinv1 := half_sum_inv_p_dvd hp hp5
      have hS1_eq : ∑ j ∈ range B, ((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ 1 -
          ((j : ℤ) * ((j : ℤ) + 1)) ^ 1) = ((B * D * (B + D) : ℕ) : ℤ) := by
        have h1 : ∀ B' : ℕ, ∑ j ∈ range B', ((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ 1 -
            ((j : ℤ) * ((j : ℤ) + 1)) ^ 1) = ((B' * D * (B' + D) : ℕ) : ℤ) := by
          intro B'
          induction B' with
          | zero => simp
          | succ B' ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
        exact h1 B
      have hS1_p : pDvdRat p V (∑ j ∈ range B, (((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ 1 -
          ((j : ℤ) * ((j : ℤ) + 1)) ^ 1 : ℤ) : ℚ)) := by
        rw [← Int.cast_sum, hS1_eq]
        exact pDvdRat_of_int _ hV
      have hp2 : pDvdRat p 2 ((-1 : ℚ) ^ (1 - 1) * (p : ℚ) ^ (2 * 1) / ((1 : ℕ) : ℚ)) := by
        refine ⟨1, 1, Nat.one_pos, Nat.coprime_one_right p, ?_⟩; norm_num
      have hinv1' : pDvdRat p 1 (∑ i ∈ Icc 1 h, (((i * (p - i) : ℕ) : ℚ)⁻¹) ^ 1) := by
        simpa only [pow_one] using hinv1
      have hprod := pDvdRat_mul (pDvdRat_mul hp2 hinv1') hS1_p
      exact pDvdRat_mono (by omega : M ≤ 2 + 1 + V) hprod
    · have hk2 : 2 ≤ k := by omega
      have hSk_q : pDvdRat p V ((((2 * k + 1).factorial : ℤ) *
          ∑ j ∈ range B, ((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ k -
                          ((j : ℤ) * ((j : ℤ) + 1)) ^ k) : ℤ) : ℚ) :=
        pDvdRat_of_int _ hSk_dvd
      have hp2k : pDvdRat p (2 * k) ((-1 : ℚ) ^ (k - 1) * (p : ℚ) ^ (2 * k)) := by
        refine ⟨(-1 : ℤ) ^ (k - 1), 1, Nat.one_pos, Nat.coprime_one_right p, ?_⟩
        push_cast; ring
      have hnum := pDvdRat_mul (pDvdRat_mul hp2k hinv_sum_0) hSk_q
      have hvp_k : 4 * padicValNat p k ≤ k - 1 := four_mul_padicValNat_le hp hp5 hk1
      have hvp_fac : 4 * padicValNat p (2 * k + 1).factorial ≤ 2 * k + 1 :=
        four_mul_padicValNat_factorial_le hp hp5
      have hvp_prod : padicValNat p (k * (2 * k + 1).factorial) =
          padicValNat p k + padicValNat p (2 * k + 1).factorial :=
        padicValNat.mul (by omega) (Nat.factorial_ne_zero _)
      have hbound : 3 + padicValNat p (k * (2 * k + 1).factorial) ≤ 2 * k := by omega
      have hdiv := pDvdRat_div_nat hp (Nat.mul_pos (by omega) (Nat.factorial_pos _))
        le_rfl (by omega : padicValNat p (k * (2 * k + 1).factorial) ≤ 2 * k + 0 + V) hnum
      have hrew_k : ((-1 : ℚ) ^ (k - 1) * (p : ℚ) ^ (2 * k) / (k : ℚ)) *
          (∑ i ∈ Icc 1 h, (((i * (p - i) : ℕ) : ℚ)⁻¹) ^ k) *
          (∑ j ∈ range B, (((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ k -
                            ((j : ℤ) * ((j : ℤ) + 1)) ^ k : ℤ) : ℚ)) =
          ((-1 : ℚ) ^ (k - 1) * (p : ℚ) ^ (2 * k) *
            (∑ i ∈ Icc 1 h, (((i * (p - i) : ℕ) : ℚ)⁻¹) ^ k) *
            ((((2 * k + 1).factorial : ℤ) *
              ∑ j ∈ range B, ((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ k -
                              ((j : ℤ) * ((j : ℤ) + 1)) ^ k) : ℤ) : ℚ)) /
            ((k * (2 * k + 1).factorial : ℕ) : ℚ) := by
        rw [← Int.cast_sum]
        have hfacne : ((2 * k + 1).factorial : ℚ) ≠ 0 := by positivity
        have hkne : (k : ℚ) ≠ 0 := by positivity
        push_cast
        field_simp
      rw [hrew_k]
      exact pDvdRat_mono (by omega : M ≤ 2 * k + 0 + V - padicValNat p (k * (2 * k + 1).factorial)) hdiv
  -- Combine: truncLog M (P1/F0^B - 1) - truncLog M (P0/F0^B - 1) has pDvdRat p M!
  set q1 : ℚ := (P1 : ℚ) / ((F0 : ℚ) ^ B) - 1
  set q0 : ℚ := (P0 : ℚ) / ((F0 : ℚ) ^ B) - 1
  rw [← hP1_eq] at hQ1_2 hQ1_log
  rw [← hP0_eq] at hQ0_2 hQ0_log
  have hlog_q : pDvdRat p M (truncLog M q1 - truncLog M q0) := by
    have h1 := pDvdRat_add (pDvdRat_sub hQ1_log hQ0_log) hlog_diff
    convert h1 using 1
    ring
  -- Define w = (P1 - P0) / P0 so 1 + q1 = (1 + q0) * (1 + w)
  set w : ℚ := ((P1 : ℚ) - (P0 : ℚ)) / (P0 : ℚ)
  have h1q1 : 1 + q1 = (1 + q0) * (1 + w) := by
    have hP0ne : (P0 : ℚ) ≠ 0 := by positivity
    have hF0ne : (F0 : ℚ) ^ B ≠ 0 := pow_ne_zero B (by positivity)
    simp only [q1, q0, w]; field_simp; ring
  have hq1_eq : q1 = q0 + w + q0 * w := by linarith
  have hw2 : pDvdRat p 2 w := by
    have hq10 : pDvdRat p 2 (q1 - q0) := pDvdRat_sub hQ1_2 hQ0_2
    have hF0B : pDvdRat p 0 (((F0 : ℚ) ^ B) / (P0 : ℚ)) := by
      refine ⟨(F0 : ℤ) ^ B, P0, hP0_pos, hP0_cop, ?_⟩; push_cast; ring
    have hw_eq : w = (q1 - q0) * (((F0 : ℚ) ^ B) / (P0 : ℚ)) := by
      have hP0ne : (P0 : ℚ) ≠ 0 := by positivity
      have hF0ne : (F0 : ℚ) ^ B ≠ 0 := pow_ne_zero B (by positivity)
      simp only [q1, q0, w]; field_simp; ring
    rw [hw_eq]
    simpa using pDvdRat_mul hq10 hF0B
  have hmul_log := truncLog_mul (M := M) hp hp5 hQ0_2 hw2
  rw [← hq1_eq] at hmul_log
  have hlog_w : pDvdRat p M (truncLog M w) := by
    have h := pDvdRat_sub hlog_q hmul_log
    convert h using 1
    ring
  have hwM : pDvdRat p M w := truncLog_inj hp hp5 hw2 hlog_w
  -- Multiply by P0 to get pDvdRat p M ((P1 - P0 : ℤ) : ℚ)!
  have hdiff_q : pDvdRat p M ((((P1 : ℤ) - (P0 : ℤ) : ℤ) : ℚ)) := by
    have hP0_0 : pDvdRat p 0 (P0 : ℚ) := pDvdRat_of_int_zero p (P0 : ℤ)
    have hmul := pDvdRat_mul hwM hP0_0
    have hP0ne : (P0 : ℚ) ≠ 0 := by positivity
    have heq : w * (P0 : ℚ) = (((P1 : ℤ) - (P0 : ℤ) : ℤ) : ℚ) := by
      simp only [w]; push_cast; field_simp
    rw [heq] at hmul
    simpa using hmul
  exact int_dvd_of_pDvdRat hdiff_q

/-- Kazandzidis congruence with extra `p`-adic factor from `C(B+D, B)`:
`p^(3 + v_p(B) + v_p(D) + v_p(B+D) + v_p(C(B+D, B))) ∣ C((B+D)p, Bp) - C(B+D, B)` (in `ℤ`). -/
lemma kazandzidis_pow {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (B D : ℕ) (hB : 0 < B) (hD : 0 < D) :
    ((p : ℤ) ^ (3 + padicValNat p B + padicValNat p D + padicValNat p (B + D) +
        padicValNat p ((B + D).choose B))) ∣
      (((B + D) * p).choose (B * p) : ℤ) - ((B + D).choose B : ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  set E := 3 + padicValNat p B + padicValNat p D + padicValNat p (B + D)
  set V := padicValNat p ((B + D).choose B)
  set P0 : ℕ := ∏ j ∈ range B, Fblock p j
  set P1 : ℕ := ∏ j ∈ range B, Fblock p (D + j)
  have hrel : (((B + D) * p).choose (B * p) : ℤ) * (P0 : ℤ) = ((B + D).choose B : ℤ) * (P1 : ℤ) := by
    exact_mod_cast choose_mul_Fblock hp.pos B D
  have hsub : ((((B + D) * p).choose (B * p) : ℤ) - ((B + D).choose B : ℤ)) * (P0 : ℤ) =
      ((B + D).choose B : ℤ) * ((P1 : ℤ) - (P0 : ℤ)) := by linarith
  have hP0_cop : Nat.Coprime p P0 := nat_coprime_prod_right (fun j _ => Fblock_coprime hp j)
  have hd1 : (p : ℤ) ^ E ∣ (P1 : ℤ) - (P0 : ℤ) := Fblock_prod_congr hp hp5 B D hB hD
  have hd2 : (p : ℤ) ^ V ∣ ((B + D).choose B : ℤ) := by
    exact_mod_cast pow_padicValNat_dvd (p := p) (n := (B + D).choose B)
  have hmul : (p : ℤ) ^ (E + V) ∣ (P0 : ℤ) * ((((B + D) * p).choose (B * p) : ℤ) - ((B + D).choose B : ℤ)) := by
    rw [mul_comm, hsub, pow_add, mul_comm ((p : ℤ) ^ E)]
    exact mul_dvd_mul hd2 hd1
  have hcopZ : IsCoprime ((p : ℤ) ^ (E + V)) (P0 : ℤ) :=
    (Nat.isCoprime_iff_coprime.mpr hP0_cop).pow_left
  exact hcopZ.dvd_of_dvd_mul_left hmul

/-- Part 3 helper: `p^(v_p(A) - v_p(B)) ∣ C(A, B)` whenever `0 < B ≤ A` and `v_p(B) ≤ v_p(A)`. -/
lemma padicValNat_choose_ge {p A B : ℕ} (hp : p.Prime) (hB : 0 < B) (hBA : B ≤ A) :
    padicValNat p A - padicValNat p B ≤ padicValNat p (A.choose B) := by
  have : Fact p.Prime := ⟨hp⟩
  have hA : 0 < A := lt_of_lt_of_le hB hBA
  have hch_pos : 0 < A.choose B := Nat.choose_pos hBA
  have hmul : B * A.choose B = A * (A - 1).choose (B - 1) := by
    have := Nat.add_one_mul_choose_eq (A - 1) (B - 1)
    rw [Nat.sub_add_cancel hA, Nat.sub_add_cancel hB] at this
    linarith
  have hv := congrArg (padicValNat p) hmul
  have hprev_pos : 0 < (A - 1).choose (B - 1) := Nat.choose_pos (by omega)
  rw [padicValNat.mul (by omega) (by omega), padicValNat.mul (by omega) (by omega)] at hv
  omega


end OeisA363986Part23

end

section

open Finset OeisA363986Part23
namespace A363990Valuation

/-- Positive representation of the negative-top coefficient (-1)^k binom(-A,k). -/
def negChoose (A k : ℕ) : ℕ := (A + k - 1).choose k

theorem negChoose_pos {A : ℕ} (hA : 0 < A) (k : ℕ) : 0 < negChoose A k :=
  Nat.choose_pos (by omega)

/-- The cleared ratio that converts negative-top scaling to ordinary Kazandzidis. -/
theorem mul_negChoose {A : ℕ} (hA : 0 < A) (k : ℕ) :
    (A + k) * negChoose A k = A * (A + k).choose k := by
  have h := Nat.choose_mul_succ_eq (A + k - 1) k
  rw [Nat.sub_add_cancel (by omega : 1 ≤ A + k), show A + k - k = A by omega] at h
  simpa only [negChoose, mul_comm] using h

/-- The corresponding identity for the difference of two scaled coefficients. -/
theorem negChoose_scale_identity {p A : ℕ} (hp : 0 < p) (hA : 0 < A) (k : ℕ) :
    ((A + k : ℕ) : ℤ) * ((negChoose (A * p) (k * p) : ℤ) - negChoose A k) =
      (A : ℤ) * ((((A + k) * p).choose (k * p) : ℤ) - (A + k).choose k) := by
  have hu := mul_negChoose (Nat.mul_pos hA hp) (k * p)
  have hs : ((A + k) * negChoose (A * p) (k * p)) * p =
      (A * ((A + k) * p).choose (k * p)) * p := by
    convert hu using 1 <;> ring
  have hsc := mul_right_cancel₀ hp.ne' hs
  have hl := mul_negChoose hA k
  have hz1 : ((A + k : ℕ) : ℤ) * (negChoose (A * p) (k * p) : ℤ) =
      (A : ℤ) * (((A + k) * p).choose (k * p) : ℤ) := by exact_mod_cast hsc
  have hz0 : ((A + k : ℕ) : ℤ) * (negChoose A k : ℤ) =
      (A : ℤ) * ((A + k).choose k : ℤ) := by exact_mod_cast hl
  linear_combination hz1 - hz0

/-- Certified negative-top Kazandzidis, including the full lower coefficient valuation. -/
theorem negChoose_kazandzidis {p A k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hA : 0 < A) (hk : 0 < k) :
    (p : ℤ) ^ (3 + padicValNat p A + padicValNat p k + padicValNat p (A + k) +
      padicValNat p (negChoose A k)) ∣
      (negChoose (A * p) (k * p) : ℤ) - negChoose A k := by
  letI : Fact p.Prime := ⟨hp⟩
  let Δ : ℤ := (negChoose (A * p) (k * p) : ℤ) - negChoose A k
  let C : ℤ := (((A + k) * p).choose (k * p) : ℤ) - (A + k).choose k
  by_cases hz : Δ = 0
  · change _ ∣ Δ
    rw [hz]
    exact dvd_zero _
  have hid : ((A + k : ℕ) : ℤ) * Δ = (A : ℤ) * C := negChoose_scale_identity hp.pos hA k
  have hC : C ≠ 0 := by
    intro he
    rw [he, mul_zero] at hid
    exact hz ((mul_eq_zero.mp hid).resolve_left (by positivity))
  have hd := kazandzidis_pow hp hp5 k A hk hA
  rw [Nat.add_comm k A] at hd
  change (p : ℤ) ^ (3 + padicValNat p k + padicValNat p A + padicValNat p (A + k) +
    padicValNat p ((A + k).choose k)) ∣ C at hd
  have hdv := ((padicValInt_dvd_iff _ C).mp hd).resolve_left hC
  have hv := congrArg (padicValInt p) hid
  rw [padicValInt.mul (by positivity) hz, padicValInt.mul (by positivity) hC,
    padicValInt.of_nat, padicValInt.of_nat] at hv
  have hlow := congrArg (padicValNat p) (mul_negChoose hA k)
  rw [padicValNat.mul (by omega) (negChoose_pos hA k).ne',
    padicValNat.mul hA.ne' (Nat.choose_pos (by omega)).ne'] at hlow
  apply (padicValInt_dvd_iff _ _).mpr
  right
  change _ ≤ padicValInt p Δ
  omega

/-- A unit lower index exposes every prime power in an ordinary binomial top. -/
theorem choose_unit_dvd {p e A k : ℕ} (hp : p.Prime) (hA : p ^ e ∣ A)
    (hk : ¬p ∣ k) : (p : ℤ) ^ e ∣ (A.choose k : ℤ) := by
  by_cases hka : k ≤ A
  · have hk0 : 0 < k := Nat.pos_of_ne_zero (fun h => hk (h ▸ dvd_zero p))
    have hA0 : 0 < A := lt_of_lt_of_le hk0 hka
    have hh := Nat.add_one_mul_choose_eq (A - 1) (k - 1)
    rw [Nat.sub_add_cancel hA0, Nat.sub_add_cancel hk0] at hh
    have hid : (k : ℤ) * (A.choose k : ℤ) =
        (A : ℤ) * ((A - 1).choose (k - 1) : ℤ) := by
      have hn : k * A.choose k = A * (A - 1).choose (k - 1) := by simpa only [mul_comm] using hh.symm
      exact_mod_cast hn
    have hd : (p : ℤ) ^ e ∣ (A : ℤ) := by exact_mod_cast hA
    have hm : (p : ℤ) ^ e ∣ (k : ℤ) * (A.choose k : ℤ) := by
      rw [hid]
      exact dvd_mul_of_dvd_left hd _
    have hc : IsCoprime ((p : ℤ) ^ e) (k : ℤ) :=
      (Nat.isCoprime_iff_coprime.mpr (hp.coprime_iff_not_dvd.mpr hk)).pow_left
    exact hc.dvd_of_dvd_mul_left hm
  · rw [Nat.choose_eq_zero_of_lt (by omega : A < k), Nat.cast_zero]
    exact dvd_zero _

/-- The same unit-index divisibility for the negative-top positive representation. -/
theorem negChoose_unit_dvd {p e A k : ℕ} (hp : p.Prime) (hA : p ^ e ∣ A)
    (hk : ¬p ∣ k) : (p : ℤ) ^ e ∣ (negChoose A k : ℤ) := by
  have hk0 : 0 < k := Nat.pos_of_ne_zero (fun h => hk (h ▸ dvd_zero p))
  have hh := Nat.choose_succ_right_eq (A + k - 1) (k - 1)
  rw [Nat.sub_add_cancel hk0, show A + k - 1 - (k - 1) = A by omega] at hh
  have hid : (k : ℤ) * (negChoose A k : ℤ) =
      (A : ℤ) * ((A + k - 1).choose (k - 1) : ℤ) := by
    exact_mod_cast (show k * negChoose A k = A * (A + k - 1).choose (k - 1) by
      simpa only [negChoose, mul_comm] using hh)
  have hd : (p : ℤ) ^ e ∣ (A : ℤ) := by exact_mod_cast hA
  have hm : (p : ℤ) ^ e ∣ (k : ℤ) * (negChoose A k : ℤ) := by
    rw [hid]
    exact dvd_mul_of_dvd_left hd _
  have hc : IsCoprime ((p : ℤ) ^ e) (k : ℤ) :=
    (Nat.isCoprime_iff_coprime.mpr (hp.coprime_iff_not_dvd.mpr hk)).pow_left
  exact hc.dvd_of_dvd_mul_left hm

/-- The m=4 signed convolution, after cancellation of its negative-top sign. -/
def term (N i j k : ℕ) : ℤ :=
  (4 * N).choose i * ((4 * N).choose j : ℤ) ^ 2 * negChoose (6 * N) k

/-- The complete j-unit part is pointwise divisible by p^(3r). -/
theorem unit_j_term {p r N i j k : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (hN : p ^ r ∣ N) (hsum : i + j + k = N) (hj : ¬p ∣ j) :
    (p : ℤ) ^ (3 * r) ∣ term N i j k := by
  have h4 : p ^ r ∣ 4 * N := dvd_mul_of_dvd_right hN _
  have h6 : p ^ r ∣ 6 * N := dvd_mul_of_dvd_right hN _
  have hdj := choose_unit_dvd hp h4 hj
  have hN1 : p ∣ N := by simpa only [pow_one] using (pow_dvd_pow p hr).trans hN
  have hu : ¬p ∣ i ∨ ¬p ∣ k := by
    by_contra h
    push Not at h
    obtain ⟨hi, hk⟩ := h
    have hNi : (p : ℤ) ∣ (N : ℤ) := by exact_mod_cast hN1
    have hii : (p : ℤ) ∣ (i : ℤ) := by exact_mod_cast hi
    have hki : (p : ℤ) ∣ (k : ℤ) := by exact_mod_cast hk
    have hji : (p : ℤ) ∣ (j : ℤ) := by
      have hh : (p : ℤ) ∣ (N : ℤ) - i - k := dvd_sub (dvd_sub hNi hii) hki
      have he : (N : ℤ) - i - k = j := by
        have he : (i : ℤ) + j + k = N := by exact_mod_cast hsum
        linear_combination -he
      rw [he] at hh
      exact hh
    exact hj (by exact_mod_cast hji)
  have hjsq : (p : ℤ) ^ (2 * r) ∣ ((4 * N).choose j : ℤ) ^ 2 := by
    have hh : ((p : ℤ) ^ r) ^ 2 ∣ ((4 * N).choose j : ℤ) ^ 2 := pow_dvd_pow_of_dvd hdj 2
    rw [← pow_mul] at hh
    simpa only [Nat.mul_comm r 2] using hh
  rcases hu with hi | hk
  · have hdi := choose_unit_dvd hp h4 hi
    have hd := dvd_mul_of_dvd_left (mul_dvd_mul hdi hjsq) (negChoose (6 * N) k : ℤ)
    simpa only [term, ← pow_add, show r + 2 * r = 3 * r by omega] using hd
  · have hdk := negChoose_unit_dvd hp h6 hk
    have hd := dvd_mul_of_dvd_left (mul_dvd_mul hjsq hdk) ((4 * N).choose i : ℤ)
    rw [← pow_add, show 2 * r + r = 3 * r by omega] at hd
    have he : ((4 * N).choose j : ℤ) ^ 2 * (negChoose (6 * N) k : ℤ) *
        ((4 * N).choose i : ℤ) = term N i j k := by unfold term; ring
    rw [he] at hd
    exact hd

/-- Uniform ordinary-binomial scaling when the top and index carry prescribed powers. -/
theorem choose_scale_bound {p A k R t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hA : p ^ R ∣ A) (hk : p ^ t ∣ k) (ht : t ≤ R) :
    (p : ℤ) ^ (3 + R + 2 * t + padicValNat p (A.choose k)) ∣
      ((A * p).choose (k * p) : ℤ) - A.choose k := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hk0 : k = 0
  · subst k
    simp only [Nat.zero_mul, Nat.choose_zero_right, Nat.cast_one, sub_self, dvd_zero]
  by_cases hka : k < A
  · have hD : 0 < A - k := Nat.sub_pos_of_lt hka
    have hA0 : 0 < A := lt_of_le_of_lt (Nat.zero_le k) hka
    have hAt : p ^ t ∣ A := (pow_dvd_pow p ht).trans hA
    have hDt : p ^ t ∣ A - k := Nat.dvd_sub hAt hk
    have hvA := (padicValNat_dvd_iff_le hA0.ne').mp hA
    have hvk := (padicValNat_dvd_iff_le hk0).mp hk
    have hvD := (padicValNat_dvd_iff_le hD.ne').mp hDt
    have hd := kazandzidis_pow hp hp5 k (A - k) (Nat.pos_of_ne_zero hk0) hD
    rw [show k + (A - k) = A by omega] at hd
    exact (pow_dvd_pow (p : ℤ) (by omega :
      3 + R + 2 * t + padicValNat p (A.choose k) ≤
      3 + padicValNat p k + padicValNat p (A - k) + padicValNat p A +
        padicValNat p (A.choose k))).trans hd
  · by_cases hEq : k = A
    · subst k
      simp only [Nat.choose_self, Nat.cast_one, sub_self, dvd_zero]
    · have hlt : A < k := by omega
      rw [Nat.choose_eq_zero_of_lt hlt,
        Nat.choose_eq_zero_of_lt (Nat.mul_lt_mul_of_pos_right hlt hp.pos)]
      simp

/-- Uniform negative-top scaling, with exactly the same gain as an ordinary factor. -/
theorem negChoose_scale_bound {p A k R t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hA0 : 0 < A) (hA : p ^ R ∣ A) (hk : p ^ t ∣ k) (ht : t ≤ R) :
    (p : ℤ) ^ (3 + R + 2 * t + padicValNat p (negChoose A k)) ∣
      (negChoose (A * p) (k * p) : ℤ) - negChoose A k := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hk0 : k = 0
  · subst k
    simp only [Nat.zero_mul, negChoose, Nat.add_zero, Nat.choose_zero_right, Nat.cast_one,
      sub_self, dvd_zero]
  have hAt : p ^ t ∣ A := (pow_dvd_pow p ht).trans hA
  have hsum : p ^ t ∣ A + k := dvd_add hAt hk
  have hvA := (padicValNat_dvd_iff_le hA0.ne').mp hA
  have hvk := (padicValNat_dvd_iff_le hk0).mp hk
  have hvsum := (padicValNat_dvd_iff_le (by omega : A + k ≠ 0)).mp hsum
  have hd := negChoose_kazandzidis hp hp5 hA0 (Nat.pos_of_ne_zero hk0)
  exact (pow_dvd_pow (p : ℤ) (by omega :
    3 + R + 2 * t + padicValNat p (negChoose A k) ≤
    3 + padicValNat p A + padicValNat p k + padicValNat p (A + k) +
      padicValNat p (negChoose A k))).trans hd

/-- Four relative p-adic errors preserve the sum of all lower-factor valuations. -/
theorem four_factor_congr (q : ℤ) (E va vb vc vd : ℕ) (a b c d A B C D : ℤ)
    (ha : q ^ va ∣ a) (hb : q ^ vb ∣ b) (hc : q ^ vc ∣ c) (hd : q ^ vd ∣ d)
    (hA : q ^ (E + va) ∣ A - a) (hB : q ^ (E + vb) ∣ B - b)
    (hC : q ^ (E + vc) ∣ C - c) (hD : q ^ (E + vd) ∣ D - d) :
    q ^ (E + va + vb + vc + vd) ∣ A * B * C * D - a * b * c * d := by
  have baseline (v : ℕ) (x X : ℤ) (hx : q ^ v ∣ x) (hX : q ^ (E + v) ∣ X - x) :
      q ^ v ∣ X := by
    have hh : q ^ v ∣ X - x := (pow_dvd_pow q (by omega : v ≤ E + v)).trans hX
    simpa only [sub_add_cancel] using dvd_add hh hx
  have hBh := baseline vb b B hb hB
  have hCh := baseline vc c C hc hC
  have hDh := baseline vd d D hd hD
  have h1 := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul hA hBh) hCh) hDh
  have h2 := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul ha hB) hCh) hDh
  have h3 := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul ha hb) hC) hDh
  have h4 := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul ha hb) hc) hD
  simp only [← pow_add] at h1 h2 h3 h4
  rw [show va + (E + vb) + vc + vd = E + va + vb + vc + vd by omega] at h2
  rw [show va + vb + (E + vc) + vd = E + va + vb + vc + vd by omega] at h3
  rw [show va + vb + vc + (E + vd) = E + va + vb + vc + vd by omega] at h4
  have ht : A * B * C * D - a * b * c * d =
      (A - a) * B * C * D + a * (B - b) * C * D +
      a * b * (C - c) * D + a * b * c * (D - d) := by ring
  rw [ht]
  exact dvd_add (dvd_add (dvd_add h1 h2) h3) h4

/-- Strong common-scale congruence for the complete m=4 convolution summand. -/
theorem term_scale_strong {p M R t i j k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hM0 : 0 < M) (hM : p ^ R ∣ M) (ht : t ≤ R)
    (hi : p ^ t ∣ i) (hj : p ^ t ∣ j) (hk : p ^ t ∣ k) :
    (p : ℤ) ^ (3 + R + 2 * t + padicValNat p ((4 * M).choose i) +
      padicValNat p ((4 * M).choose j) + padicValNat p ((4 * M).choose j) +
      padicValNat p (negChoose (6 * M) k)) ∣
      term (M * p) (i * p) (j * p) (k * p) - term M i j k := by
  have h4 : p ^ R ∣ 4 * M := dvd_mul_of_dvd_right hM _
  have h6 : p ^ R ∣ 6 * M := dvd_mul_of_dvd_right hM _
  have hiS := choose_scale_bound hp hp5 h4 hi ht
  have hjS := choose_scale_bound hp hp5 h4 hj ht
  have hkS := negChoose_scale_bound hp hp5 (by omega : 0 < 6 * M) h6 hk ht
  have divNat (n : ℕ) : (p : ℤ) ^ padicValNat p n ∣ (n : ℤ) := by
    exact_mod_cast pow_padicValNat_dvd (p := p) (n := n)
  have hh := four_factor_congr (p : ℤ) (3 + R + 2 * t)
    (padicValNat p ((4 * M).choose i)) (padicValNat p ((4 * M).choose j))
    (padicValNat p ((4 * M).choose j)) (padicValNat p (negChoose (6 * M) k))
    ((4 * M).choose i) ((4 * M).choose j) ((4 * M).choose j) (negChoose (6 * M) k)
    (((4 * M) * p).choose (i * p)) (((4 * M) * p).choose (j * p))
    (((4 * M) * p).choose (j * p)) (negChoose ((6 * M) * p) (k * p))
    (divNat _) (divNat _) (divNat _) (divNat _) hiS hjS hjS hkS
  simpa only [term, pow_two, Nat.mul_assoc, mul_assoc] using hh

/-- A known exact common exponent is recovered without a convention for v_p(0). -/
theorem valuation_eq_of_dvd_not_dvd {p k t : ℕ} (hp : p.Prime)
    (hk : p ^ t ∣ k) (hn : ¬p ^ (t + 1) ∣ k) : padicValNat p k = t := by
  letI : Fact p.Prime := ⟨hp⟩
  have hk0 : k ≠ 0 := fun h => hn (h ▸ dvd_zero _)
  have hlo := (padicValNat_dvd_iff_le hk0).mp hk
  have hhi : padicValNat p k < t + 1 := by
    by_contra h
    exact hn ((padicValNat_dvd_iff_le hk0).mpr (by omega))
  omega

/-- Index-clearing identity for the positive representation of a negative binomial. -/
theorem index_mul_negChoose {A k : ℕ} (hk : 0 < k) :
    k * negChoose A k = A * (A + k - 1).choose (k - 1) := by
  have hh := Nat.choose_succ_right_eq (A + k - 1) (k - 1)
  rw [Nat.sub_add_cancel hk, show A + k - 1 - (k - 1) = A by omega] at hh
  simpa only [negChoose, mul_comm] using hh

/-- A negative binomial carries at least the top valuation minus the index valuation. -/
theorem negChoose_valuation_ge {p A k R : ℕ} (hp : p.Prime) (hA : 0 < A)
    (hk : 0 < k) (hR : p ^ R ∣ A) :
    R - padicValNat p k ≤ padicValNat p (negChoose A k) := by
  letI : Fact p.Prime := ⟨hp⟩
  have h := congrArg (padicValNat p) (index_mul_negChoose (A := A) hk)
  rw [padicValNat.mul hk.ne' (negChoose_pos hA k).ne',
    padicValNat.mul hA.ne' (Nat.choose_pos (by omega)).ne'] at h
  have hvA := (padicValNat_dvd_iff_le hA.ne').mp hR
  omega

/-- The ordinary counterpart in a form convenient for the convolution. -/
theorem choose_valuation_ge {p A k R : ℕ} (hp : p.Prime)
    (hk : 0 < k) (hka : k ≤ A) (hR : p ^ R ∣ A) :
    R - padicValNat p k ≤ padicValNat p (A.choose k) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hvA := (padicValNat_dvd_iff_le (by omega : A ≠ 0)).mp hR
  have hh := padicValNat_choose_ge hp hk hka
  omega

/-- The minimum common index scale forces two lower-factor valuation contributions. -/
theorem term_valuation_mass {p M R t i j k : ℕ} (hp : p.Prime) (hM0 : 0 < M)
    (hM : p ^ R ∣ M) (ht : t < R) (hsum : i + j + k = M)
    (hi : p ^ t ∣ i) (hj : p ^ t ∣ j) (hk : p ^ t ∣ k)
    (hn : ¬(p ^ (t + 1) ∣ i ∧ p ^ (t + 1) ∣ j ∧ p ^ (t + 1) ∣ k)) :
    2 * (R - t) ≤ padicValNat p ((4 * M).choose i) +
      padicValNat p ((4 * M).choose j) + padicValNat p ((4 * M).choose j) +
      padicValNat p (negChoose (6 * M) k) := by
  have h4 : p ^ R ∣ 4 * M := dvd_mul_of_dvd_right hM _
  have h6 : p ^ R ∣ 6 * M := dvd_mul_of_dvd_right hM _
  by_cases hjn : p ^ (t + 1) ∣ j
  · have hMn : p ^ (t + 1) ∣ M := (pow_dvd_pow p (by omega : t + 1 ≤ R)).trans hM
    have hin : ¬p ^ (t + 1) ∣ i := by
      intro hin
      have hkn : p ^ (t + 1) ∣ k := by
        have hd := Nat.dvd_sub (Nat.dvd_sub hMn hin) hjn
        simpa only [show M - i - j = k by omega] using hd
      exact hn ⟨hin, hjn, hkn⟩
    have hkn : ¬p ^ (t + 1) ∣ k := by
      intro hkn
      have hin : p ^ (t + 1) ∣ i := by
        have hd := Nat.dvd_sub (Nat.dvd_sub hMn hjn) hkn
        simpa only [show M - j - k = i by omega] using hd
      exact hn ⟨hin, hjn, hkn⟩
    have hiv := valuation_eq_of_dvd_not_dvd hp hi hin
    have hkv := valuation_eq_of_dvd_not_dvd hp hk hkn
    have hip : 0 < i := Nat.pos_of_ne_zero (fun h => hin (h ▸ dvd_zero _))
    have hkp : 0 < k := Nat.pos_of_ne_zero (fun h => hkn (h ▸ dvd_zero _))
    have hci := choose_valuation_ge hp hip (by omega : i ≤ 4 * M) h4
    have hck := negChoose_valuation_ge hp (by omega : 0 < 6 * M) hkp h6
    rw [hiv] at hci
    rw [hkv] at hck
    omega
  · have hjv := valuation_eq_of_dvd_not_dvd hp hj hjn
    have hjp : 0 < j := Nat.pos_of_ne_zero (fun h => hjn (h ▸ dvd_zero _))
    have hcj := choose_valuation_ge hp hjp (by omega : j ≤ 4 * M) h4
    rw [hjv] at hcj
    omega

/-- Every all-p-divisible convolution index scales with the full cubic modulus. -/
theorem term_scale {p M R i j k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hM0 : 0 < M) (hM : p ^ R ∣ M) (hsum : i + j + k = M) :
    (p : ℤ) ^ (3 * (R + 1)) ∣
      term (M * p) (i * p) (j * p) (k * p) - term M i j k := by
  classical
  let P : ℕ → Prop := fun t => p ^ t ∣ i ∧ p ^ t ∣ j ∧ p ^ t ∣ k
  let t := Nat.findGreatest P R
  have ht : t ≤ R := Nat.findGreatest_le R
  have hP : P t := Nat.findGreatest_spec (P := P) (m := 0) (Nat.zero_le R) (by simp [P])
  have hstrong := term_scale_strong hp hp5 hM0 hM ht hP.1 hP.2.1 hP.2.2
  have he : 3 * (R + 1) ≤ 3 + R + 2 * t + padicValNat p ((4 * M).choose i) +
      padicValNat p ((4 * M).choose j) + padicValNat p ((4 * M).choose j) +
      padicValNat p (negChoose (6 * M) k) := by
    by_cases htR : t = R
    · omega
    · have hlt : t < R := by omega
      have hn : ¬P (t + 1) := Nat.findGreatest_is_greatest (by omega) (by omega : t + 1 ≤ R)
      have hm := term_valuation_mass hp hM0 hM hlt hsum hP.1 hP.2.1 hP.2.2 hn
      omega
  exact (pow_dvd_pow (p : ℤ) he).trans hstrong

/-- The exact n,p,r form needed to pair all-divisible summation blocks. -/
theorem divisible_term_dvd {p n r i j k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hsum : i + j + k = n * p ^ (r - 1)) :
    (p : ℤ) ^ (3 * r) ∣ term (n * p ^ r) (p * i) (p * j) (p * k) -
      term (n * p ^ (r - 1)) i j k := by
  have hM : p ^ (r - 1) ∣ n * p ^ (r - 1) := dvd_mul_left _ _
  have hM0 : 0 < n * p ^ (r - 1) := Nat.mul_pos hn (pow_pos hp.pos _)
  have h := term_scale hp hp5 hM0 hM hsum
  rw [Nat.sub_add_cancel hr] at h
  have hNM : n * p ^ (r - 1) * p = n * p ^ r := by
    rw [Nat.mul_assoc, ← pow_succ, Nat.sub_add_cancel hr]
  simpa only [hNM, Nat.mul_comm i p, Nat.mul_comm j p, Nat.mul_comm k p] using h

end A363990Valuation

end

section

namespace A363990LocalVariation

def posUnit (A i : ℕ) : ℤ := (-1 : ℤ)^(i-1) * ((A-1).choose (i-1) : ℤ)

def negUnit (D i : ℕ) : ℤ := ((D+i-1).choose (i-1) : ℤ)

def weight (A D h i : ℕ) : ℤ := posUnit A i * negUnit D (h-i)

theorem posUnit_step (A i : ℕ) (ha : 0 < A) (hi : 0 < i) :
    (i : ℤ) * (posUnit A (i+1) - posUnit A i) = -(A : ℤ) * posUnit A i := by
  have hindex : i - 1 + 1 = i := by omega
  by_cases hle : i ≤ A
  · have h := Nat.choose_succ_right_eq (A-1) (i-1)
    rw [hindex, show A-1-(i-1) = A-i by omega] at h
    have hc := congrArg (fun n : ℕ => (n : ℤ)) h
    push_cast [Nat.cast_sub hle] at hc
    have he : (-1 : ℤ)^i = (-1 : ℤ)^(i-1) * (-1) := by
      rw [← pow_succ, hindex]
    simp only [posUnit, Nat.add_sub_cancel, he]
    linear_combination -(-1 : ℤ)^(i-1) * hc
  · have h0 : (A-1).choose (i-1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h1 : (A-1).choose i = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [posUnit, h0, h1]

theorem negUnit_step (D i : ℕ) (hd : 0 < D) (hi : 0 < i) :
    (i : ℤ) * (negUnit D (i+1) - negUnit D i) = (D : ℤ) * negUnit D i := by
  have hk : i - 1 + 1 = i := by omega
  have hn : D + i - 1 + 1 = D + i := by omega
  have h := Nat.add_one_mul_choose_eq (D+i-1) (i-1)
  rw [hk, hn] at h
  have hc := congrArg (fun n : ℕ => (n : ℤ)) h
  push_cast at hc
  simp only [negUnit, Nat.add_sub_cancel,
    show D + (i+1) - 1 = D+i by omega]
  linear_combination -hc

/-- An index interior to a p^t-block can absorb at most t-1 powers of p. -/
theorem cancel_from_interior {p r t i : ℕ} {z : ℤ} (hp : p.Prime) (hi : i ≠ 0)
    (htr : t ≤ r) (hnot : ¬ p^t ∣ i) (h : (p : ℤ)^r ∣ (i : ℤ)*z) :
    (p : ℤ)^(r-t+1) ∣ z := by
  by_cases hz : z = 0
  · simp [hz]
  have hz' : z.natAbs ≠ 0 := by simpa using hz
  have hnat : p^r ∣ i * z.natAbs := by
    rw [← Int.natAbs_natCast i, ← Int.natAbs_mul, ← Int.natCast_dvd, Nat.cast_pow]
    exact h
  have hs := (hp.pow_dvd_iff_le_factorization (mul_ne_zero hi hz')).mp hnat
  rw [Nat.factorization_mul hi hz', Finsupp.add_apply] at hs
  have hit : i.factorization p < t :=
    lt_of_not_ge (fun he => hnot ((hp.pow_dvd_iff_le_factorization hi).mpr he))
  rw [← Nat.cast_pow, Int.natCast_dvd]
  exact (hp.pow_dvd_iff_le_factorization hz').mpr (by omega)

theorem interior_not_dvd {m L i : ℕ} (_hm : 0 < m)
    (hl : L*m < i) (hu : i < (L+1)*m) : ¬m ∣ i := by
  rintro ⟨k, rfl⟩
  rw [Nat.mul_comm m k] at hl hu
  have hkl := Nat.lt_of_mul_lt_mul_right hl
  have hku := Nat.lt_of_mul_lt_mul_right hu
  omega

theorem block_constant {m modulus L i j : ℕ} (f : ℕ → ℤ)
    (hi0 : L*m < i) (hi1 : i < (L+1)*m) (hj0 : L*m < j) (hj1 : j < (L+1)*m)
    (hstep : ∀ x, L*m < x → x < (L+1)*m → f x ≡ f (x+1) [ZMOD (modulus : ℤ)]) :
    f i ≡ f j [ZMOD (modulus : ℤ)] := by
  have forward (u v : ℕ) (hu : L*m < u) (hv : v < (L+1)*m) (huv : u ≤ v) :
      f u ≡ f v [ZMOD (modulus : ℤ)] := by
    induction v, huv using Nat.le_induction with
    | base => exact Int.ModEq.refl _
    | succ n hn ih =>
      exact (ih (by omega)).trans (hstep n (by omega) (by omega))
  by_cases h : i ≤ j
  · exact forward i j hi0 hj1 h
  · exact (forward j i hj0 hi1 (by omega)).symm

theorem block_constant_of_scaled_step {p r t L i j : ℕ} (hp : p.Prime) (htr : t ≤ r)
    (f : ℕ → ℤ) {a : ℤ} (ha : (p : ℤ)^r ∣ a)
    (hstep : ∀ x : ℕ, 0 < x → (x : ℤ)*(f (x+1)-f x) = a*f x)
    (hi0 : L*p^t < i) (hi1 : i < (L+1)*p^t)
    (hj0 : L*p^t < j) (hj1 : j < (L+1)*p^t) :
    f i ≡ f j [ZMOD (p : ℤ)^(r-t+1)] := by
  rw [← Nat.cast_pow]
  apply block_constant f hi0 hi1 hj0 hj1
  intro x hx0 hx1
  have hx : 0 < x := (Nat.zero_le _).trans_lt hx0
  have hnot := interior_not_dvd (pow_pos hp.pos t) hx0 hx1
  have h : (p : ℤ)^r ∣ (x : ℤ)*(f (x+1)-f x) := by
    rw [hstep x hx]
    exact dvd_mul_of_dvd_left ha (f x)
  rw [Int.modEq_iff_dvd, Nat.cast_pow]
  exact cancel_from_interior hp hx.ne' htr hnot h

/-- Reflection of an open interval whose endpoints are consecutive multiples of m. -/
theorem reflect_block {m L h i j : ℕ}
    (hdvd : m ∣ h) (hi : i < h) (hj : j < h)
    (hi0 : L*m < i) (hi1 : i < (L+1)*m)
    (hj0 : L*m < j) (hj1 : j < (L+1)*m) :
    ∃ L', L'*m < h-i ∧ h-i < (L'+1)*m ∧
      L'*m < h-j ∧ h-j < (L'+1)*m := by
  obtain ⟨Q, hQ⟩ := hdvd
  have hL : L < Q := Nat.lt_of_mul_lt_mul_right
    (by rw [← Nat.mul_comm m Q, ← hQ]; exact hi0.trans hi)
  let L' := Q-(L+1)
  have h1 : L'+(L+1)=Q := Nat.sub_add_cancel hL
  have h2 : (L'+1)+L=Q := by omega
  have he1 : L'*m+(L+1)*m=h := by
    rw [← Nat.add_mul,h1,Nat.mul_comm,← hQ]
  have he2 : (L'+1)*m+L*m=h := by
    rw [← Nat.add_mul,h2,Nat.mul_comm,← hQ]
  exact ⟨L', by omega, by omega, by omega, by omega⟩

/-- The product of shifted binomial factors is locally constant on every full block. -/
theorem weight_variation {p A D h r t L i j : ℕ}
    (hp : p.Prime) (hA : 0 < A) (hD : 0 < D)
    (ha : (p : ℤ)^r ∣ (A : ℤ)) (hd : (p : ℤ)^r ∣ (D : ℤ))
    (htr : t ≤ r) (hh : p^t ∣ h) (hi : i < h) (hj : j < h)
    (hi0 : L*p^t < i) (hi1 : i < (L+1)*p^t)
    (hj0 : L*p^t < j) (hj1 : j < (L+1)*p^t) :
    (p : ℤ)^(r-t+1) ∣ weight A D h i - weight A D h j := by
  have hpos := block_constant_of_scaled_step hp htr (posUnit A)
    (Int.dvd_neg.mpr ha) (fun x hx => posUnit_step A x hA hx) hi0 hi1 hj0 hj1
  obtain ⟨L',hi0',hi1',hj0',hj1'⟩ := reflect_block hh hi hj hi0 hi1 hj0 hj1
  have hneg := block_constant_of_scaled_step hp htr (negUnit D) hd
    (fun x hx => negUnit_step D x hD hx) hi0' hi1' hj0' hj1'
  exact Int.modEq_iff_dvd.mp (hpos.mul hneg).symm

theorem posChoose_scaled {A i : ℕ} (hA : 0 < A) (hi : 0 < i) :
    (i : ℤ) * (A.choose i : ℤ) = (A : ℤ) * ((A-1).choose (i-1) : ℤ) := by
  have h := Nat.add_one_mul_choose_eq (A-1) (i-1)
  rw [show A-1+1=A by omega, show i-1+1=i by omega] at h
  exact_mod_cast (Nat.mul_comm i _).trans h.symm

theorem negChoose_scaled {D i : ℕ} (hi : 0 < i) :
    (i : ℤ) * ((D+i-1).choose i : ℤ) = (D : ℤ) * negUnit D i := by
  have h := Nat.choose_succ_right_eq (D+i-1) (i-1)
  rw [show i-1+1=i by omega, show D+i-1-(i-1)=D by omega] at h
  unfold negUnit
  exact_mod_cast (Nat.mul_comm i _).trans (h.trans (Nat.mul_comm _ D))

/-- Clear the unit denominator in the factorization used by cancellation. -/
theorem weighted_pair_identity {A D h i : ℕ} (hA : 0 < A) (hi : 0 < i) (hh : i < h) :
    (i : ℤ) * ((h-i : ℕ) : ℤ) *
      ((A.choose i : ℤ)*((D+(h-i)-1).choose (h-i) : ℤ)) =
    (A : ℤ)*(D : ℤ)*(-1 : ℤ)^(i-1)*weight A D h i := by
  have hpos := posChoose_scaled hA hi
  have hneg := negChoose_scaled (D := D) (by omega : 0 < h-i)
  unfold weight posUnit
  have hsign : (-1 : ℤ)^(i-1) * (-1)^(i-1) = 1 := by
    rw [← mul_pow, show (-1 : ℤ) * (-1) = 1 by decide, one_pow]
  calc
    _ = ((i : ℤ)*(A.choose i : ℤ)) *
        (((h-i : ℕ) : ℤ)*((D+(h-i)-1).choose (h-i) : ℤ)) := by ring
    _ = (A : ℤ)*(D : ℤ)*((A-1).choose (i-1) : ℤ)*negUnit D (h-i) := by rw [hpos,hneg]; ring
    _ = _ := by
      symm
      calc
        _ = ((-1 : ℤ)^(i-1) * (-1)^(i-1)) *
            ((A : ℤ)*(D : ℤ)*((A-1).choose (i-1) : ℤ)*negUnit D (h-i)) := by ring
        _ = _ := by rw [hsign, one_mul]

end A363990LocalVariation

end

section

namespace A363990Cancellation
open Finset

theorem map_inverse_unit {m n : ℕ} (f : ZMod m →+* ZMod n) (x : ZMod m)
    (hx : IsUnit x) : f x⁻¹=(f x)⁻¹ := by
  have hunit : IsUnit (f x) := hx.map f
  calc
    f x⁻¹ = 1*f x⁻¹ := (one_mul _).symm
    _ = ((f x)⁻¹*f x)*f x⁻¹ := by rw [ZMod.inv_mul_of_unit _ hunit]
    _ = (f x)⁻¹*(f x*f x⁻¹) := by rw [mul_assoc]
    _ = (f x)⁻¹ := by rw [← map_mul,ZMod.mul_inv_of_unit _ hx,map_one,mul_one]

theorem pow_dvd_of_projection_zero {p s t : ℕ} (hp : p.Prime) (ht : t ≤ s)
    (x : ZMod (p^s))
    (hx : ZMod.castHom (pow_dvd_pow p ht) (ZMod (p^t)) x=0) :
    (p : ZMod (p^s))^t ∣ x := by
  let : NeZero (p^s) := ⟨pow_ne_zero s hp.ne_zero⟩
  have hv : ((x.val : ℕ) : ZMod (p^t))=0 := by
    rw [← ZMod.natCast_zmod_val x] at hx
    simpa only [map_natCast] using hx
  obtain ⟨a,ha⟩ := (ZMod.natCast_eq_zero_iff x.val (p^t)).mp hv
  refine ⟨(a : ZMod (p^s)),?_⟩
  calc
    x = (x.val : ZMod (p^s)) := (ZMod.natCast_zmod_val x).symm
    _ = (p : ZMod (p^s))^t*(a : ZMod (p^s)) := by rw [ha,Nat.cast_mul,Nat.cast_pow]

end A363990Cancellation

end

section

namespace A363990Cancellation
open Finset

/-- Decompose an arbitrary complete interval into adjacent equal blocks. -/
theorem sum_range_blocks {R : Type*} [AddCommMonoid R] (M q : ℕ) (f : ℕ → R) :
    ∑ i ∈ range (M*q), f i = ∑ L ∈ range M, ∑ i ∈ Ico (L*q) ((L+1)*q), f i := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ← ih, show (M+1)*q=M*q+q by ring]
    have hd : Disjoint (range (M*q)) (Ico (M*q) (M*q+q)) := by
      rw [Finset.disjoint_left]
      intro x hx hy
      simp only [Finset.mem_range, Finset.mem_Ico] at hx hy
      omega
    have hu : range (M*q+q) = range (M*q) ∪ Ico (M*q) (M*q+q) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
      omega
    rw [hu,Finset.sum_union hd]

/-- A blockwise constant weight of valuation s-t kills a kernel whose
complete p^t-block sums have valuation t. The multiplicity M is arbitrary. -/
theorem weighted_layer_zero {p s t M : ℕ} (hp : p.Prime) (ht : t ≤ s)
    (g b : ℕ → ZMod (p^s))
    (hkernel : ∀ L < M*p^(s-t), (p : ZMod (p^s))^t ∣
      ∑ i ∈ Ico (L*p^t) ((L+1)*p^t), b i)
    (hweight : ∀ L < M*p^(s-t), ∃ c : ZMod (p^s),
      (p : ZMod (p^s))^(s-t) ∣ c ∧
      ∀ i ∈ Ico (L*p^t) ((L+1)*p^t), g i*b i=c*b i) :
    ∑ i ∈ range (M*p^s), g i*b i=0 := by
  have hlen : M*p^s=(M*p^(s-t))*p^t := by
    rw [mul_assoc,← pow_add,Nat.sub_add_cancel ht]
  rw [hlen,sum_range_blocks]
  apply Finset.sum_eq_zero
  intro L hL
  have hL' := Finset.mem_range.mp hL
  obtain ⟨c,hc,hconst⟩ := hweight L hL'
  rw [Finset.sum_congr rfl (fun i hi => hconst i hi),← Finset.mul_sum]
  obtain ⟨a,ha⟩ := hc
  obtain ⟨d,hd⟩ := hkernel L hL'
  rw [ha,hd]
  calc
    _ = (p : ZMod (p^s))^((s-t)+t)*(a*d) := by rw [pow_add]; ring
    _ = 0 := by rw [Nat.sub_add_cancel ht,← Nat.cast_pow,ZMod.natCast_self,zero_mul]

/-- Multiscale cancellation in ZMod(p^s). W_t is any hierarchy of coarse
weights. It is sufficient that each layer difference is blockwise constant
(after multiplying by the kernel), and divisible by p^(s-t). -/
theorem multiscale_zero {p s M : ℕ} (hp : p.Prime)
    (W : ℕ → ℕ → ZMod (p^s)) (b : ℕ → ZMod (p^s))
    (hkernel : ∀ t ≤ s, ∀ L < M*p^(s-t), (p : ZMod (p^s))^t ∣
      ∑ i ∈ Ico (L*p^t) ((L+1)*p^t), b i)
    (hdiff : ∀ t < s, ∀ L < M*p^(s-t), ∃ c : ZMod (p^s),
      (p : ZMod (p^s))^(s-t) ∣ c ∧
      ∀ i ∈ Ico (L*p^t) ((L+1)*p^t),
        (W t i-W (t+1) i)*b i=c*b i)
    (htop : ∀ L < M, ∃ c : ZMod (p^s),
      ∀ i ∈ Ico (L*p^s) ((L+1)*p^s), W s i*b i=c*b i) :
    ∑ i ∈ range (M*p^s), W 0 i*b i=0 := by
  have htel (m i : ℕ) :
      (∑ t ∈ range m, (W t i-W (t+1) i))=W 0 i-W m i := by
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ,ih]; ring
  have hpoint (i : ℕ) : W 0 i*b i=W s i*b i+
      ∑ t ∈ range s, (W t i-W (t+1) i)*b i := by
    rw [← Finset.sum_mul,htel]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hpoint i),Finset.sum_add_distrib,Finset.sum_comm]
  have htop0 : ∑ i ∈ range (M*p^s), W s i*b i=0 := by
    apply weighted_layer_zero hp (le_refl s) (W s) b (hkernel s le_rfl)
    intro L hL
    simp only [Nat.sub_self,pow_zero,mul_one] at hL ⊢
    obtain ⟨c,hc⟩ := htop L hL
    exact ⟨c,one_dvd _,hc⟩
  have hmid : ∑ t ∈ range s, ∑ i ∈ range (M*p^s), (W t i-W (t+1) i)*b i=0 := by
    apply Finset.sum_eq_zero
    intro t ht
    exact weighted_layer_zero hp (Finset.mem_range.mp ht).le
      (fun i => W t i-W (t+1) i) b (hkernel t (Finset.mem_range.mp ht).le)
      (hdiff t (Finset.mem_range.mp ht))
  rw [htop0,hmid,add_zero]

end A363990Cancellation

end

section

namespace A363990Cancellation
open Finset

theorem block_quotient {q L i : ℕ} (hq : 0 < q) (hi : L*q ≤ i ∧ i < (L+1)*q) : i/q=L := by
  apply Nat.le_antisymm
  · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hq).mpr hi.2)
  · exact (Nat.le_div_iff_mul_le hq).mpr hi.1

theorem parent_quotient {p t L i : ℕ} (hp : 0 < p)
    (hi : L*p^t ≤ i ∧ i < (L+1)*p^t) : i/p^(t+1)=L/p := by
  rw [pow_succ,← Nat.div_div_eq_div_mul,block_quotient (pow_pos hp t) hi]

theorem cast_int_pow_dvd {p s e d : ℕ} {a : ℤ}
    (h : (p : ℤ)^e ∣ a) (hd : d ≤ e) :
    (p : ZMod (p^s))^d ∣ (a : ZMod (p^s)) := by
  have hcast : (p : ZMod (p^s))^e ∣ (a : ZMod (p^s)) := by
    obtain ⟨c,hc⟩ := h
    refine ⟨(c : ZMod (p^s)),?_⟩
    rw [hc,Int.cast_mul,Int.cast_pow,Int.cast_natCast]
  exact (pow_dvd_pow (p : ZMod (p^s)) hd).trans hcast

end A363990Cancellation

end

section

namespace A361712
open Finset

noncomputable def unitRange (p L : ℕ) : Finset ℕ := (Ico 1 L).filter (fun j => ¬p∣j)

/-- Permuting units by a single unit annihilates their power sum whenever
v^e-1 is itself a unit. -/
theorem sum_units_inv_pow_zero {R : Type*} [CommRing R] [Fintype Rˣ]
    (e : ℕ) (v : Rˣ) (hv : IsUnit ((v : R)^e-1)) :
    ∑ u : Rˣ, (((u⁻¹ : Rˣ) : R)^e)=0 := by
  classical
  have h := Equiv.sum_comp (Equiv.mulLeft v) (fun u : Rˣ => (u : R)^e)
  change (∑ u : Rˣ, ((v*u : Rˣ) : R)^e)=(∑ u : Rˣ, (u : R)^e) at h
  simp only [Units.val_mul,mul_pow,← Finset.mul_sum] at h
  have hz : (∑ u : Rˣ, (u : R)^e)=0 := by
    apply hv.mul_right_eq_zero.mp
    calc
      _ = (v : R)^e*(∑ u : Rˣ,(u : R)^e)-(∑ u : Rˣ,(u : R)^e) := by ring
      _ = 0 := sub_eq_zero.mpr h
  have hi := Equiv.sum_comp (Equiv.inv Rˣ) (fun u : Rˣ => (u : R)^e)
  change (∑ u : Rˣ, (((u⁻¹ : Rˣ) : R)^e))=(∑ u : Rˣ,(u : R)^e) at hi
  exact hi.trans hz

/-- Exact natural representatives for the units modulo a prime power. -/
theorem sum_unitRange_eq_units {p h : ℕ} [NeZero (p^h)] (hp : p.Prime) (hh : 1 ≤ h) (e : ℕ) :
    (∑ j ∈ unitRange p (p^h), ((j : ZMod (p^h))^e)⁻¹)=
      ∑ u : (ZMod (p^h))ˣ, (((u⁻¹ : (ZMod (p^h))ˣ) : ZMod (p^h))^e) := by
  classical
  let : NeZero (p^h) := ⟨pow_ne_zero h hp.ne_zero⟩
  have hbase : (∑ j ∈ unitRange p (p^h), ((j : ZMod (p^h))^e)⁻¹)=
      ∑ u : (ZMod (p^h))ˣ, ((u : ZMod (p^h))^e)⁻¹ := by
    apply Finset.sum_bij (fun j hj => ZMod.unitOfCoprime j
      (((hp.coprime_iff_not_dvd).mpr (Finset.mem_filter.mp hj).2).symm.pow_right h))
    · intro _ _; exact mem_univ _
    · intro a ha b hb hab
      have hc : (a : ZMod (p^h))=(b : ZMod (p^h)) := by
        simpa only [ZMod.coe_unitOfCoprime] using congrArg Units.val hab
      have hal : a < p^h := (mem_Ico.mp (mem_filter.mp ha).1).2
      have hbl : b < p^h := (mem_Ico.mp (mem_filter.mp hb).1).2
      have hv := congrArg ZMod.val hc
      simpa only [ZMod.val_natCast_of_lt hal,ZMod.val_natCast_of_lt hbl] using hv
    · intro u _
      have hcop : Nat.Coprime (u : ZMod (p^h)).val (p^h) := by
        rw [← ZMod.isUnit_iff_coprime]
        simpa only [ZMod.natCast_zmod_val] using u.isUnit
      have hnd : ¬p ∣ (u : ZMod (p^h)).val := by
        intro hd
        have he := Nat.dvd_gcd hd (dvd_pow_self p (by omega : h ≠ 0))
        rw [hcop.gcd_eq_one] at he
        exact hp.not_dvd_one he
      have hvpos : 1 ≤ (u : ZMod (p^h)).val := by
        have : (u : ZMod (p^h)).val ≠ 0 := by intro he; exact hnd (he ▸ dvd_zero p)
        omega
      refine ⟨(u : ZMod (p^h)).val,mem_filter.mpr
        ⟨mem_Ico.mpr ⟨hvpos,ZMod.val_lt _⟩,hnd⟩,?_⟩
      ext
      simp only [ZMod.coe_unitOfCoprime,ZMod.natCast_zmod_val]
    · intro j hj
      simp only [ZMod.coe_unitOfCoprime]
  rw [hbase]
  apply Finset.sum_congr rfl
  intro u hu
  rw [← Units.val_pow_eq_pow_val,ZMod.inv_coe_unit,← inv_pow,Units.val_pow_eq_pow_val]

end A361712

end

section

namespace A363983
open A363990Valuation

def term (N k : ℕ) : ℤ :=
 (-1:ℤ)^(N+k)*(N.choose k:ℤ)*((N+k-1).choose k:ℤ)*((2*k).choose N:ℤ)

lemma ordinary_mul (N k : ℕ) (hN:0<N) (hk:0<k) :
 (k:ℤ)*(N.choose k:ℤ)=(N:ℤ)*((N-1).choose (k-1):ℤ) := by
 have h:=Nat.add_one_mul_choose_eq (N-1) (k-1)
 rw [Nat.sub_add_cancel hN,Nat.sub_add_cancel hk] at h
 exact_mod_cast (by simpa only [mul_comm] using h.symm : k * N.choose k=N*(N-1).choose (k-1))

lemma shifted_mul (N k : ℕ) (hk:0<k) :
 (k:ℤ)*((N+k-1).choose k:ℤ)=(N:ℤ)*((N+k-1).choose (k-1):ℤ) := by
 have h:=Nat.choose_succ_right_eq (N+k-1) (k-1)
 rw [Nat.sub_add_cancel hk,show N+k-1-(k-1)=N by omega] at h
 exact_mod_cast (by simpa only [mul_comm] using h : k*(N+k-1).choose k=N*(N+k-1).choose (k-1))

lemma cleared_term (N k : ℕ) (hN:0<N) (hk:0<k) :
 (k:ℤ)^2*term N k=(N:ℤ)^2*((-1:ℤ)^(N+k)*
 ((N-1).choose (k-1):ℤ)*((N+k-1).choose (k-1):ℤ)*((2*k).choose N:ℤ)) := by
 have h1:=ordinary_mul N k hN hk
 have h2:=shifted_mul N k hk
 dsimp [term]
 calc
  _ = (-1:ℤ)^(N+k)*((k:ℤ)*(N.choose k:ℤ))*
    ((k:ℤ)*((N+k-1).choose k:ℤ))*((2*k).choose N:ℤ) := by ring
  _ = _ := by rw [h1,h2];ring

lemma term_unit_dvd (p r N k : ℕ) (hp:p.Prime) (hN:p^r∣N) (hk:¬p∣k) :
 (p:ℤ)^(2*r)∣term N k := by
 have h1 : (p:ℤ)^r∣(N.choose k:ℤ) := choose_unit_dvd hp hN hk
 have h2 : (p:ℤ)^r∣((N+k-1).choose k:ℤ) := negChoose_unit_dvd hp hN hk
 have h := mul_dvd_mul h1 h2
 rw [←pow_add,show r+r=2*r by omega] at h
 dsimp [term]
 have hh:=dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h ((-1:ℤ)^(N+k))) ((2*k).choose N:ℤ)
 simpa only [mul_assoc] using hh
end A363983

end

section

namespace A363983
open A363990LocalVariation

lemma half_to_block {q L i:ℕ} (hi0:L*q < 2*i) (hi1:2*i < (L+1)*q) :
 (L/2)*q < i ∧ i < (L/2+1)*q := by
 have h0:2*(L/2)≤L := by omega
 have h1:L+1≤2*(L/2+1) := by omega
 constructor
 · nlinarith [Nat.mul_le_mul_right q h0]
 · nlinarith [Nat.mul_le_mul_right q h1]

lemma choose_top_step (A x:ℕ):
 ((x+1:ℕ):ℤ)*(((x+1).choose A:ℤ)-(x.choose A:ℤ))=
 (A:ℤ)*((x+1).choose A:ℤ) := by
 by_cases h:A≤x+1
 · have hc:=Nat.choose_mul_succ_eq x A
   have hh:=congrArg (fun n:ℕ=>(n:ℤ)) hc
   push_cast [Nat.cast_sub h] at hh
   push_cast
   linear_combination -hh
 · have h1:=Nat.choose_eq_zero_of_lt (by omega:x+1 < A)
   have h0:=Nat.choose_eq_zero_of_lt (by omega:x < A)
   simp [h0,h1]

lemma choose_top_variation {p r t A L i j:ℕ} (hp:p.Prime) (htr:t≤r)
 (ha:(p:ℤ)^r∣(A:ℤ))
 (hi0:L*p^t < i) (hi1:i < (L+1)*p^t)
 (hj0:L*p^t < j) (hj1:j < (L+1)*p^t):
 (p:ℤ)^(r-t+1)∣(i.choose A:ℤ)-(j.choose A:ℤ) := by
 have forward (u v:ℕ) (hu:L*p^t < u) (hv:v < (L+1)*p^t) (huv:u≤v):
   (u.choose A:ℤ) ≡ (v.choose A:ℤ) [ZMOD (p:ℤ)^(r-t+1)] := by
  induction v,huv using Nat.le_induction with
  | base => exact Int.ModEq.refl _
  | succ n hn ih =>
   have hstep:(p:ℤ)^(r-t+1)∣((n+1).choose A:ℤ)-(n.choose A:ℤ) := by
    apply cancel_from_interior hp (by omega) htr
      (interior_not_dvd (pow_pos hp.pos t) (by omega) hv)
    rw [choose_top_step]
    exact dvd_mul_of_dvd_left ha _
   exact (ih (by omega)).trans (Int.modEq_iff_dvd.mpr hstep)
 apply Int.modEq_iff_dvd.mp
 by_cases h:i≤j
 · exact (forward i j hi0 hj1 h).symm
 · exact forward j i hj0 hi1 (by omega)

def weight (N k:ℕ):ℤ := posUnit N k*negUnit N k*((2*k).choose N:ℤ)

lemma weight_variation {p r t N L i j:ℕ} (hp:p.Prime) (hN:0 < N)
 (hNr:(p:ℤ)^r∣(N:ℤ)) (htr:t≤r)
 (hi0:L*p^t < 2*i) (hi1:2*i < (L+1)*p^t)
 (hj0:L*p^t < 2*j) (hj1:2*j < (L+1)*p^t):
 (p:ℤ)^(r-t+1)∣weight N i-weight N j := by
 obtain ⟨hi0',hi1'⟩:=half_to_block hi0 hi1
 obtain ⟨hj0',hj1'⟩:=half_to_block hj0 hj1
 have hpos:=block_constant_of_scaled_step hp htr (posUnit N)
   (Int.dvd_neg.mpr hNr) (fun x hx=>posUnit_step N x hN hx) hi0' hi1' hj0' hj1'
 have hneg:=block_constant_of_scaled_step hp htr (negUnit N)
   hNr (fun x hx=>negUnit_step N x hN hx) hi0' hi1' hj0' hj1'
 have htop:=choose_top_variation hp htr hNr hi0 hi1 hj0 hj1
 have htop':((2*i).choose N:ℤ)≡((2*j).choose N:ℤ) [ZMOD (p:ℤ)^(r-t+1)] :=
  (Int.modEq_iff_dvd.mpr htop).symm
 exact Int.modEq_iff_dvd.mp ((hpos.mul hneg).mul htop').symm
end A363983

end

section

namespace A363983
open Finset A363990Cancellation

noncomputable def halfCoarse (p : ℕ) (W : ℕ → ℤ) (t x : ℕ) : ℤ :=
 if t=0 then W (x/2) else W (((x/p^t)*p^t)/2+1)

lemma anchor_interior {q L : ℕ} (hq:3≤q):
 L*q  <  2*(L*q/2+1) ∧ 2*(L*q/2+1)  <  (L+1)*q := by
 have he:(L+1)*q=L*q+q := by ring
 constructor  <;> omega

lemma halfCoarse_on_block {p t L x:ℕ} (hp:0 < p) (ht:1≤t) (W:ℕ→ℤ)
 (hx:L*p^t≤x ∧ x < (L+1)*p^t):
 halfCoarse p W t x=halfCoarse p W t (L*p^t) := by
 simp only [halfCoarse,show ¬t=0 by omega,if_false,
   block_quotient (pow_pos hp t) hx,Nat.mul_div_cancel _ (pow_pos hp t)]

lemma halfCoarse_parent_on_block {p t L x:ℕ} (hp:0 < p) (W:ℕ→ℤ)
 (hx:L*p^t≤x ∧ x < (L+1)*p^t):
 halfCoarse p W (t+1) x=halfCoarse p W (t+1) (L*p^t) := by
 have hstart:L*p^t/p^(t+1)=L/p := by
  rw [pow_succ,←Nat.div_div_eq_div_mul,Nat.mul_div_cancel _ (pow_pos hp t)]
 simp only [halfCoarse,Nat.succ_ne_zero,if_false,parent_quotient hp hx,hstart]

theorem half_weighted_zero {p r M:ℕ} (hp:p.Prime) (hp3:3≤p) (hr:1≤r)
 (W:ℕ→ℤ) (K:ℕ→ZMod (p^r))
 (hodd:∀x,¬Even x→K x=0) (hdvd:∀x,p∣x→K x=0)
 (hvar:∀t,1≤t→t≤r→∀L i j,
   L*p^t  <  2*i→2*i  <  (L+1)*p^t→L*p^t  <  2*j→2*j  <  (L+1)*p^t→
   (p:ℤ)^(r-t+1)∣W i-W j)
 (hkernel:∀t≤r,∀L  <  M*p^(r-t),(p:ZMod (p^r))^t∣
   ∑x∈Ico (L*p^t) ((L+1)*p^t),K x):
 ∑x∈range (M*p^r),(W (x/2):ZMod (p^r))*K x=0 := by
 let C:ℕ→ℕ→ZMod (p^r):=fun t x=>(halfCoarse p W t x:ZMod (p^r))
 have hdiff:∀t  <  r,∀L  <  M*p^(r-t),∃c:ZMod (p^r),
   (p:ZMod (p^r))^(r-t)∣c ∧ ∀x∈Ico (L*p^t) ((L+1)*p^t),
   (C t x-C (t+1) x)*K x=c*K x := by
  intro t ht L hL
  by_cases ht0:t=0
  · subst t
    simp only [pow_zero,mul_one,Nat.sub_zero] at hL ⊢
    by_cases hLp:p∣L
    · refine ⟨0,dvd_zero _,?_⟩
      intro x hx
      have he:x=L := by have :=mem_Ico.mp hx;omega
      subst x
      simp [hdvd L hLp]
    · by_cases hLe:Even L
      · let a:=((L/p)*p)/2+1
        have ha:=anchor_interior (L:=L/p) hp3
        have hlo:(L/p)*p  <  L := by
          have hmod:=Nat.mod_add_div L p
          rw [Nat.mul_comm p (L/p)] at hmod
          have hne:L%p≠0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hLp
          have hh:=Nat.div_mul_le_self L p
          omega
        have hhi:L  <  (L/p+1)*p := (Nat.div_lt_iff_lt_mul hp.pos).mp (Nat.lt_succ_self _)
        have hEven:2*(L/2)=L := by obtain ⟨k,hk⟩:=hLe;omega
        have hv:=hvar 1 (by omega) hr (L/p) (L/2) a
          (by simpa only [pow_one,hEven] using hlo)
          (by simpa only [pow_one,hEven] using hhi)
          (by simpa only [pow_one,a] using ha.1)
          (by simpa only [pow_one,a] using ha.2)
        have hv':(p:ℤ)^r∣W (L/2)-W a := by simpa only [show r-1+1=r by omega] using hv
        refine ⟨((W (L/2)-W a:ℤ):ZMod (p^r)),cast_int_pow_dvd hv' le_rfl,?_⟩
        intro x hx
        have he:x=L := by have :=mem_Ico.mp hx;omega
        subst x
        dsimp [C,halfCoarse,a]
        simp only [pow_one,Int.cast_sub]
      · refine ⟨0,dvd_zero _,?_⟩
        intro x hx
        have he:x=L := by have :=mem_Ico.mp hx;omega
        subst x
        simp [hodd L hLe]
  · let a:=L*p^t/2+1
    let b:=(L/p)*p^(t+1)/2+1
    have ht1:1≤t := by omega
    have hq:3≤p^t := by
      calc 3≤p:=hp3
           _≤p^t:=le_self_pow₀ (by omega:1≤p) (by omega:t≠0)
    have hqp:3≤p^(t+1) := by
      calc 3≤p:=hp3
           _≤p^(t+1):=le_self_pow₀ (by omega:1≤p) (by omega:t+1≠0)
    have ha:=anchor_interior (L:=L) hq
    have hb:=anchor_interior (L:=L/p) hqp
    have hparent0:(L/p)*p^(t+1)≤L*p^t := by
      calc _=(L/p*p)*p^t:=by rw [pow_succ];ring
           _≤L*p^t:=Nat.mul_le_mul_right _ (Nat.div_mul_le_self L p)
    have hparent1:(L+1)*p^t≤(L/p+1)*p^(t+1) := by
      calc _≤((L/p+1)*p)*p^t:=Nat.mul_le_mul_right _ (by have hh : L < (L/p+1)*p := (Nat.div_lt_iff_lt_mul hp.pos).mp (Nat.lt_succ_self (L/p));omega)
           _=(L/p+1)*p^(t+1):=by rw [pow_succ];ring
    have hv:=hvar (t+1) (by omega) (by omega) (L/p) a b
      (by dsimp [a];omega) (by dsimp [a];omega)
      (by simpa only [b] using hb.1) (by simpa only [b] using hb.2)
    have hv':(p:ℤ)^(r-t)∣W a-W b := by
      simpa only [show r-(t+1)+1=r-t by omega] using hv
    have hcs:halfCoarse p W t (L*p^t)=W a := by
      simp only [halfCoarse,ht0,if_false,Nat.mul_div_cancel _ (pow_pos hp.pos t)];rfl
    have hcp:halfCoarse p W (t+1) (L*p^t)=W b := by
      have hh:L*p^t/p^(t+1)=L/p := by rw [pow_succ,←Nat.div_div_eq_div_mul,Nat.mul_div_cancel _ (pow_pos hp.pos t)]
      simp only [halfCoarse,Nat.succ_ne_zero,if_false,hh];rfl
    refine ⟨((W a-W b:ℤ):ZMod (p^r)),cast_int_pow_dvd hv' le_rfl,?_⟩
    intro x hx
    dsimp [C]
    rw [halfCoarse_on_block hp.pos ht1 W (mem_Ico.mp hx),halfCoarse_parent_on_block hp.pos W (mem_Ico.mp hx),hcs,hcp,Int.cast_sub]
 have htop:∀L  <  M,∃c:ZMod (p^r),∀x∈Ico (L*p^r) ((L+1)*p^r),C r x*K x=c*K x := by
  intro L hL
  refine ⟨C r (L*p^r),?_⟩
  intro x hx
  dsimp [C]
  rw [halfCoarse_on_block hp.pos hr W (mem_Ico.mp hx)]
 have h:=multiscale_zero hp C K hkernel hdiff htop
 simpa [C,halfCoarse] using h
end A363983

end

section

namespace A363983
open Finset A363990LocalVariation

lemma cleared_weight (N k:ℕ) (hN:0<N) (hk:0<k):
 (k:ℤ)^2*term N k=(N:ℤ)^2*(-1:ℤ)^(N+1)*weight N k := by
 have hs:(-1:ℤ)^(N+k)=(-1:ℤ)^(N+1)*(-1:ℤ)^(k-1) := by
  rw [←pow_add]
  congr 1
  omega
 rw [cleared_term N k hN hk,hs]
 dsimp [weight,posUnit,negUnit]
 ring

lemma unit_term_approx {p r N k:ℕ} (hp:p.Prime) (hN:0<N) (hNr:p^r∣N)
 (hk:¬p∣k) (v:ℤ) (hv:(p:ℤ)^r∣(k:ℤ)*v-1):
 (p:ℤ)^(3*r)∣term N k-(N:ℤ)^2*(-1:ℤ)^(N+1)*weight N k*v^2 := by
 have hk0:0<k := Nat.pos_of_ne_zero (fun h=>hk (h ▸ dvd_zero p))
 have hn:(p:ℤ)^r∣(N:ℤ) := by exact_mod_cast hNr
 have hn2:(p:ℤ)^(2*r)∣(N:ℤ)^2 := by
  simpa only [pow_mul,Nat.mul_comm] using pow_dvd_pow_of_dvd hn 2
 have hv2:(p:ℤ)^r∣(k:ℤ)^2*v^2-1 := by
  have h:=dvd_mul_of_dvd_left hv ((k:ℤ)*v+1)
  have he : ((k:ℤ)*v-1)*((k:ℤ)*v+1)=(k:ℤ)^2*v^2-1 := by ring
  rwa [he] at h
 have hprod:=mul_dvd_mul hn2 hv2
 rw [←pow_add,show 2*r+r=3*r by omega] at hprod
 have hh: (p:ℤ)^(3*r)∣(k:ℤ)^2*(term N k-(N:ℤ)^2*(-1:ℤ)^(N+1)*weight N k*v^2) := by
  have hd:=dvd_mul_of_dvd_left hprod (-((-1:ℤ)^(N+1)*weight N k))
  have he:(N:ℤ)^2*((k:ℤ)^2*v^2-1)*(-((-1:ℤ)^(N+1)*weight N k))=
    (k:ℤ)^2*(term N k-(N:ℤ)^2*(-1:ℤ)^(N+1)*weight N k*v^2) := by
   have hc:=cleared_weight N k hN hk0
   linear_combination -hc
  rwa [he] at hd
 have hcop:IsCoprime ((p:ℤ)^(3*r)) ((k:ℤ)^2) :=
  ((Nat.isCoprime_iff_coprime.mpr (hp.coprime_iff_not_dvd.mpr hk)).pow_left).pow_right
 exact hcop.dvd_of_dvd_mul_left hh

lemma unit_sum_dvd {p r N L:ℕ} (hp:p.Prime) (hN:0<N) (hNr:p^r∣N)
 (v:ℕ→ℤ) (hv:∀k,¬p∣k→(p:ℤ)^r∣(k:ℤ)*v k-1)
 (hweighted:(p:ℤ)^r∣∑k∈(range L).filter (fun k=>¬p∣k),weight N k*(v k)^2):
 (p:ℤ)^(3*r)∣∑k∈(range L).filter (fun k=>¬p∣k),term N k := by
 let S:Finset ℕ:=(range L).filter (fun k=>¬p∣k)
 have herr:(p:ℤ)^(3*r)∣∑k∈S,
   (term N k-(N:ℤ)^2*(-1:ℤ)^(N+1)*weight N k*(v k)^2) := by
  apply dvd_sum
  intro k hk
  have hkp:¬p∣k := (mem_filter.mp hk).2
  exact unit_term_approx hp hN hNr hkp (v k) (hv k hkp)
 have hn:(p:ℤ)^r∣(N:ℤ) := by exact_mod_cast hNr
 have hn2:(p:ℤ)^(2*r)∣(N:ℤ)^2 := by
  simpa only [pow_mul,Nat.mul_comm] using pow_dvd_pow_of_dvd hn 2
 have hmain:=mul_dvd_mul hn2 hweighted
 rw [←pow_add,show 2*r+r=3*r by omega] at hmain
 have hmain':(p:ℤ)^(3*r)∣(N:ℤ)^2*(-1:ℤ)^(N+1)*(∑k∈S,weight N k*(v k)^2) := by
  have hh:=dvd_mul_of_dvd_right hmain ((-1:ℤ)^(N+1))
  dsimp [S]
  have he : ((-1:ℤ)^(N+1))*((N:ℤ)^2*(∑k∈(range L).filter (fun k=>¬p∣k),weight N k*(v k)^2))=
    (N:ℤ)^2*(-1:ℤ)^(N+1)*(∑k∈(range L).filter (fun k=>¬p∣k),weight N k*(v k)^2) := by ring
  rwa [he] at hh
 have he:(∑k∈S,(term N k-(N:ℤ)^2*(-1:ℤ)^(N+1)*weight N k*(v k)^2))+
   (N:ℤ)^2*(-1:ℤ)^(N+1)*(∑k∈S,weight N k*(v k)^2)=∑k∈S,term N k := by
  have hs:(∑k∈S,(N:ℤ)^2*(-1:ℤ)^(N+1)*weight N k*(v k)^2)=
    (N:ℤ)^2*(-1:ℤ)^(N+1)*(∑k∈S,weight N k*(v k)^2) := by
   rw [mul_sum]
   apply sum_congr rfl
   intro k _
   ring
  rw [sum_sub_distrib,hs]
  ring
 have hh:=herr.add hmain'
 rwa [he] at hh
end A363983

end

section

namespace A363983Half
open Finset

def low (p q : ℕ) : Finset ℕ := (Ico 1 (q/2+1)).filter (fun j => ¬p∣j)
def high (p q : ℕ) : Finset ℕ := (Ico (q/2+1) q).filter (fun j => ¬p∣j)

def kernel (q j : ℕ) : ZMod q := ((j : ZMod q)^2)⁻¹

theorem two_coprime_pow {p t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : Nat.Coprime 2 (p^t) :=
  ((hp.coprime_iff_not_dvd.mpr (fun hd => by
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega)).symm).pow_right t

theorem complete_zero {p t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (ht : 0 < t) :
    ∑ j ∈ A361712.unitRange p (p^t), kernel (p^t) j = 0 := by
  let : NeZero (p^t) := ⟨pow_ne_zero t hp.ne_zero⟩
  let v := ZMod.unitOfCoprime 2 (two_coprime_pow (t:=t) hp hp5)
  have hc3 : Nat.Coprime 3 (p^t) :=
    ((hp.coprime_iff_not_dvd.mpr (fun hd => by
      have := Nat.le_of_dvd (by decide : 0 < 3) hd
      omega)).symm).pow_right t
  have hv : IsUnit ((v : ZMod (p^t))^2-1) := by
    have he : ((v : ZMod (p^t))^2-1)=(3 : ZMod (p^t)) := by
      simp only [v,ZMod.coe_unitOfCoprime]
      ring
    rw [he]
    exact (ZMod.isUnit_iff_coprime _ _).mpr hc3
  simp only [kernel]
  rw [A361712.sum_unitRange_eq_units hp ht]
  exact A361712.sum_units_inv_pow_zero 2 v hv

private theorem reflect_eq (q j : ℕ) (hj : j ≤ q) : kernel q (q-j) = kernel q j := by
  unfold kernel
  rw [Nat.cast_sub hj, ZMod.natCast_self, zero_sub, neg_sq]

theorem high_eq_low {p q : ℕ} (hq : q % 2 = 1) (hd : p ∣ q) :
    ∑ j ∈ high p q, kernel q j = ∑ j ∈ low p q, kernel q j := by
  classical
  symm
  apply sum_bij (fun j _ => q-j)
  · intro j hj
    rcases mem_filter.mp hj with ⟨hj,hnd⟩
    rcases mem_Ico.mp hj with ⟨hl,hr⟩
    refine mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,?_⟩
    intro h
    have hs : q-j+j=q := Nat.sub_add_cancel (by omega)
    exact hnd ((Nat.dvd_add_right h).mp (hs.symm ▸ hd))
  · intro i hi j hj h
    have hi' := (mem_Ico.mp (mem_filter.mp hi).1).2
    have hj' := (mem_Ico.mp (mem_filter.mp hj).1).2
    omega
  · intro j hj
    rcases mem_filter.mp hj with ⟨hj,hnd⟩
    rcases mem_Ico.mp hj with ⟨hl,hr⟩
    refine ⟨q-j,mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,?_⟩,by omega⟩
    intro h
    have hs : q-j+j=q := Nat.sub_add_cancel (by omega)
    exact hnd ((Nat.dvd_add_right h).mp (hs.symm ▸ hd))
  · intro j hj
    exact (reflect_eq q j (by have := (mem_Ico.mp (mem_filter.mp hj).1).2; omega)).symm

theorem low_zero {p t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (ht : 0 < t) :
    ∑ j ∈ low p (p^t), kernel (p^t) j = 0 := by
  let q := p^t
  have hqo : q % 2 = 1 := Nat.odd_iff.mp ((hp.odd_of_ne_two (by omega)).pow)
  have hpq : p ∣ q := dvd_pow_self p ht.ne'
  have he : low p q ∪ high p q = A361712.unitRange p q := by
    ext j
    simp only [low,high,A361712.unitRange,mem_union,mem_filter,mem_Ico]
    omega
  have hd : Disjoint (low p q) (high p q) := by
    rw [Finset.disjoint_left]
    intro j hj hk
    have h1 := (mem_Ico.mp (mem_filter.mp hj).1).2
    have h2 := (mem_Ico.mp (mem_filter.mp hk).1).1
    omega
  have hn := complete_zero hp hp5 ht
  change ∑j ∈ A361712.unitRange p q, kernel q j = 0 at hn
  rw [← he,sum_union hd,high_eq_low hqo hpq,← two_mul] at hn
  have hu : IsUnit (2 : ZMod q) := (ZMod.isUnit_iff_coprime _ _).mpr
    (two_coprime_pow (t:=t) hp hp5)
  exact hu.mul_right_eq_zero.mp hn

private theorem double_div_shift (q B j : ℕ) (hq : 0 < q) :
    2*(q*B+j)/q = 2*B+(2*j)/q := by
  rw [show 2*(q*B+j)=q*(2*B)+2*j by ring, Nat.mul_add_div hq]

private theorem mod_dvd_shift {p q B j : ℕ} (h : p ∣ q) :
    (p ∣ q*B+j) ↔ p ∣ j :=
  Nat.dvd_add_right (dvd_mul_of_dvd_left h B)

private theorem kernel_shift (q B j : ℕ) : kernel q (q*B+j) = kernel q j := by
  simp [kernel,Nat.cast_add,Nat.cast_mul]

/-- An entire half block of residue classes, selected by the doubled position. -/
def residueHalf (p q e : ℕ) : Finset ℕ := if e = 0 then low p q else high p q

private theorem mem_residueHalf {p q e j : ℕ} (hq : 0 < q) (hqo : q % 2 = 1)
    (he : e < 2) :
    j ∈ residueHalf p q e ↔ j < q ∧ ¬p∣j ∧ (2*j)/q=e := by
  by_cases hz : e = 0
  · subst e
    rw [residueHalf, if_pos rfl, low, mem_filter, mem_Ico]
    constructor
    · rintro ⟨⟨h1,h2⟩,hd⟩
      have hd0 := Nat.div_eq_of_lt (show 2*j < q by omega)
      exact ⟨by omega,hd,hd0⟩
    · rintro ⟨hqj,hd,he⟩
      have hlt := Nat.lt_mul_div_succ (2*j) hq
      rw [he] at hlt
      have hn : j ≠ 0 := fun h => hd (h ▸ dvd_zero p)
      exact ⟨⟨by omega,by omega⟩,hd⟩
  · have h1 : e=1 := by omega
    subst e
    simp only [residueHalf, if_neg Nat.one_ne_zero, high, mem_filter, mem_Ico]
    constructor
    · rintro ⟨⟨h1,h2⟩,hd⟩
      have he := Nat.div_eq_of_lt_le (k:=1) (n:=q) (m:=2*j)
        (by omega) (by omega)
      exact ⟨h2,hd,he⟩
    · rintro ⟨hqj,hd,he⟩
      have hl := Nat.div_mul_le_self (2*j) q
      rw [he, one_mul] at hl
      exact ⟨⟨by omega,hqj⟩,hd⟩

/-- Every complete doubled-index half block has inverse-square sum zero. -/
theorem half_kernel_zero {p t b L : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (ht : 0 < t)
    (hbound : (b+1)*p^t ≤ 2*L) :
    ∑ j ∈ (range L).filter (fun j => 2*j/p^t=b ∧ ¬p∣j), kernel (p^t) j = 0 := by
  classical
  let q := p^t
  have hq : 0 < q := pow_pos hp.pos _
  have hqo : q % 2 = 1 := Nat.odd_iff.mp ((hp.odd_of_ne_two (by omega)).pow)
  have hpq : p ∣ q := dvd_pow_self p ht.ne'
  let B := b/2
  let e := b%2
  have he : e < 2 := Nat.mod_lt _ (by decide)
  have hb : 2*B+e=b := Nat.div_add_mod b 2
  let S := (range L).filter (fun j => 2*j/q=b ∧ ¬p∣j)
  change ∑ j ∈ S, kernel q j = 0
  have hs : (∑ j ∈ residueHalf p q e, kernel q j) = ∑ j ∈ S, kernel q j := by
    apply sum_bij (fun j _ => q*B+j)
    · intro j hj
      obtain ⟨hjq,hnd,hd⟩ := (mem_residueHalf hq hqo he).mp hj
      have h := double_div_shift q B j hq
      rw [hd,hb] at h
      have hlt := Nat.lt_mul_div_succ (2*(q*B+j)) hq
      rw [h, Nat.mul_comm q (b+1)] at hlt
      exact mem_filter.mpr ⟨mem_range.mpr (by change (b+1)*q ≤ 2*L at hbound; omega),
        h, fun hh => hnd ((mod_dvd_shift (B:=B) hpq).mp hh)⟩
    · intro i hi j hj h
      omega
    · intro j hj
      obtain ⟨_,hd,hnd⟩ := mem_filter.mp hj
      let r := j%q
      have hrq : r < q := Nat.mod_lt _ hq
      have hsep : q*(j/q)+r=j := Nat.div_add_mod j q
      have h := double_div_shift q (j/q) r hq
      rw [hsep,hd] at h
      have hsmall : 2*r/q < 2 := (Nat.div_lt_iff_lt_mul hq).mpr (by omega)
      have hsame : 2*(j/q)+(2*r)/q = 2*B+e := h.symm.trans hb.symm
      have hB : j/q=B := by
        have hh := congrArg (fun a : ℕ => a/2) hsame
        simpa only [Nat.mul_add_div (by decide : 0 < 2),
          Nat.div_eq_of_lt hsmall, Nat.div_eq_of_lt he, add_zero] using hh
      have her : 2*r/q=e := by
        rw [hB] at hsame
        exact Nat.add_left_cancel hsame
      rw [hB] at hsep
      refine ⟨r,(mem_residueHalf hq hqo he).mpr ⟨hrq,?_,her⟩,hsep⟩
      exact fun hh => hnd (hsep ▸ (mod_dvd_shift (B:=B) hpq).mpr hh)
    · intro j hj
      exact (kernel_shift q B j).symm
  rw [← hs]
  by_cases he0 : e = 0
  · rw [residueHalf,if_pos he0]
    exact low_zero hp hp5 ht
  · rw [residueHalf,if_neg he0,high_eq_low hqo hpq]
    exact low_zero hp hp5 ht

end A363983Half

end

section

namespace A363983Half
open Finset

noncomputable def doubledKernel (p r x : ℕ) : ZMod (p^r) :=
  if x % 2 = 0 ∧ ¬ p ∣ x / 2 then kernel (p^r) (x/2) else 0

theorem doubledKernel_odd (p r x : ℕ) (hx : ¬ Even x) : doubledKernel p r x = 0 := by
  apply if_neg
  intro h
  apply hx
  refine ⟨x/2, ?_⟩
  have hh := Nat.div_add_mod x 2
  rw [h.1, add_zero] at hh
  omega

theorem doubledKernel_dvd (p r x : ℕ) (hx : p ∣ x) (hp : p.Prime)
    (hp5 : 5 ≤ p) : doubledKernel p r x = 0 := by
  apply if_neg
  intro h
  have hh := Nat.div_add_mod x 2
  rw [h.1, add_zero] at hh
  have h2 : ¬ p ∣ 2 := fun hz => by have := Nat.le_of_dvd (by decide : 0 < 2) hz; omega
  apply h.2
  exact ((hp.dvd_mul.mp (hh.symm ▸ hx)).resolve_left h2)

private theorem doubledKernel_map {p r t x : ℕ} (hp : p.Prime) (hr : 0 < r) (ht : t ≤ r) :
    ZMod.castHom (pow_dvd_pow p ht) (ZMod (p^t)) (doubledKernel p r x) =
      doubledKernel p t x := by
  by_cases hx : x%2=0 ∧ ¬p∣x/2
  · simp only [doubledKernel, if_pos hx, kernel]
    have hu := (ZMod.isUnit_natCast_iff_not_dvd_pow hp hr).mpr hx.2
    rw [A363990Cancellation.map_inverse_unit _ _ (hu.pow 2), map_pow, map_natCast]
  · simp [doubledKernel, hx]

private theorem doubledKernel_at_modulus {p t b L : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (ht : 0 < t) (hb : (b+1)*p^t ≤ 2*L) :
    ∑ x ∈ Ico (b*p^t) ((b+1)*p^t), doubledKernel p t x = 0 := by
  classical
  let S := (Ico (b*p^t) ((b+1)*p^t)).filter (fun x => x%2=0 ∧ ¬p∣x/2)
  have hs : (∑ x ∈ S, kernel (p^t) (x/2)) =
      ∑ j ∈ (range L).filter (fun j => 2*j/p^t=b ∧ ¬p∣j), kernel (p^t) j := by
    apply sum_bij (fun x _ => x/2)
    · intro x hx
      obtain ⟨hxI,hx2,hxp⟩ := mem_filter.mp hx
      obtain ⟨hxlo,hxhi⟩ := mem_Ico.mp hxI
      have he : 2*(x/2)=x := by
        simpa only [hx2, add_zero] using Nat.div_add_mod x 2
      refine mem_filter.mpr ⟨mem_range.mpr (by omega), ?_, hxp⟩
      rw [he]
      exact Nat.div_eq_of_lt_le hxlo hxhi
    · intro x hx y hy h
      have hxe := (mem_filter.mp hx).2.1
      have hye := (mem_filter.mp hy).2.1
      omega
    · intro j hj
      obtain ⟨_,hjdiv,hjp⟩ := mem_filter.mp hj
      have hq := pow_pos hp.pos t
      have hjlo := Nat.div_mul_le_self (2*j) (p^t)
      have hjhi := Nat.lt_mul_div_succ (2*j) hq
      rw [hjdiv] at hjlo hjhi
      rw [Nat.mul_comm (p^t) (b+1)] at hjhi
      have he : 2*j/2=j := by omega
      refine ⟨2*j, mem_filter.mpr ⟨mem_Ico.mpr ⟨hjlo,hjhi⟩, ?_, ?_⟩, he⟩
      · omega
      · simpa only [he] using hjp
    · intro x hx
      rfl
  rw [← half_kernel_zero hp hp5 ht hb, ← hs]
  change _ = ∑ x ∈ S, kernel (p^t) (x/2)
  rw [show S = _ from rfl, sum_filter]
  rfl

theorem doubledKernel_block_dvd {p r t b L : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (ht : t ≤ r) (hb : (b+1)*p^t ≤ 2*L) :
    (p : ZMod (p^r))^t ∣ ∑ x ∈ Ico (b*p^t) ((b+1)*p^t), doubledKernel p r x := by
  by_cases ht0 : t=0
  · simp [ht0]
  apply A363990Cancellation.pow_dvd_of_projection_zero hp ht
  rw [map_sum]
  rw [sum_congr rfl (fun x _ => doubledKernel_map hp (by omega) ht)]
  exact doubledKernel_at_modulus hp hp5 (by omega) hb

end A363983Half

end

section

namespace A363983
open Finset A363983Half

lemma sum_even_double {R:Type*} [AddCommMonoid R] (L:ℕ) (f:ℕ→R):
 (∑x∈range (2*L),if Even x then f (x/2) else 0)=∑k∈range L,f k := by
 rw [←sum_filter]
 symm
 apply sum_nbij' (fun k=>2*k) (fun x=>x/2)
 · intro k hk
   simp only [mem_filter,mem_range] at *
   exact ⟨by omega,⟨k,by omega⟩⟩
 · intro x hx
   simp only [mem_filter,mem_range] at hx ⊢
   obtain ⟨k,hk⟩:=hx.2
   omega
 · intro k hk
   omega
 · intro x hx
   obtain ⟨k,hk⟩:=(mem_filter.mp hx).2
   omega
 · intro k hk
   congr 1
   omega

noncomputable def inverseLift (p r k:ℕ):ℤ := ((k:ZMod (p^r))⁻¹).val

lemma inverseLift_cast {p r k:ℕ} (hp:p.Prime): (inverseLift p r k:ZMod (p^r))=(k:ZMod (p^r))⁻¹ := by
 haveI : NeZero (p^r) := ⟨pow_ne_zero _ hp.ne_zero⟩
 simp only [inverseLift,Int.cast_natCast,ZMod.natCast_zmod_val]

lemma index_unit {p r k:ℕ} (hp:p.Prime) (hk:¬p∣k):IsUnit (k:ZMod (p^r)) :=
 (ZMod.isUnit_iff_coprime _ _).mpr ((hp.coprime_iff_not_dvd.mpr hk).symm.pow_right r)

lemma inverseLift_spec {p r k:ℕ} (hp:p.Prime) (hk:¬p∣k):
 (p:ℤ)^r∣(k:ℤ)*inverseLift p r k-1 := by
 rw [←Nat.cast_pow,←ZMod.intCast_zmod_eq_zero_iff_dvd]
 push_cast
 rw [inverseLift_cast hp,ZMod.mul_inv_of_unit _ (index_unit hp hk),sub_self]

lemma kernel_eq_inverseLift {p r k:ℕ} (hp:p.Prime) (hk:¬p∣k):
 kernel (p^r) k=(inverseLift p r k:ZMod (p^r))^2 := by
 rw [inverseLift_cast hp]
 have hu:=index_unit (r:=r) hp hk
 apply (hu.pow 2).mul_left_cancel
 rw [kernel,ZMod.mul_inv_of_unit _ (hu.pow 2)]
 rw [show (k:ZMod (p^r))^2*((k:ZMod (p^r))⁻¹)^2=
   ((k:ZMod (p^r))*(k:ZMod (p^r))⁻¹)^2 by ring,
   ZMod.mul_inv_of_unit _ hu]
 norm_num

lemma doubled_sum_eq (p r N:ℕ):
 (∑x∈range (2*N),(weight N (x/2):ZMod (p^r))*doubledKernel p r x)=
 ∑k∈(range N).filter (fun k=>¬p∣k),(weight N k:ZMod (p^r))*kernel (p^r) k := by
 rw [sum_filter]
 have he:(∑x∈range (2*N),(weight N (x/2):ZMod (p^r))*doubledKernel p r x)=
   ∑x∈range (2*N),if Even x then
     (if ¬p∣x/2 then (weight N (x/2):ZMod (p^r))*kernel (p^r) (x/2) else 0) else 0 := by
  apply sum_congr rfl
  intro x hx
  by_cases hxe:Even x
  · have hxm:x%2=0 := by obtain ⟨k,hk⟩:=hxe;omega
    by_cases hxp:p∣x/2 <;> simp [doubledKernel,hxm,hxp,hxe]
  · simp [doubledKernel_odd p r x hxe,hxe]
 rw [he]
 exact sum_even_double N (fun k=>if ¬p∣k then (weight N k:ZMod (p^r))*kernel (p^r) k else 0)

lemma weighted_inverseSquare_dvd {p r N:ℕ} (hp:p.Prime) (hp5:5≤p) (hr:1≤r)
 (hN:0<N) (hNr:p^r∣N):
 (p:ℤ)^r∣∑k∈(range N).filter (fun k=>¬p∣k),weight N k*(inverseLift p r k)^2 := by
 obtain ⟨m,hm⟩:=hNr
 have hn:(p:ℤ)^r∣(N:ℤ) := by exact_mod_cast (show p^r∣N from ⟨m,hm⟩)
 have hs:=half_weighted_zero (M:=2*m) hp (by omega) hr (weight N) (doubledKernel p r)
   (doubledKernel_odd p r) (fun x hx=>doubledKernel_dvd p r x hx hp hp5)
   (fun t ht htr L i j hi0 hi1 hj0 hj1=>weight_variation hp hN hn htr hi0 hi1 hj0 hj1)
   (by
    intro t ht b hb
    apply doubledKernel_block_dvd (L:=N) hp hp5 ht
    have hbound: (b+1)*p^t≤((2*m)*p^(r-t))*p^t := Nat.mul_le_mul_right _ (by omega)
    have he:((2*m)*p^(r-t))*p^t=2*N := by
     rw [mul_assoc,←pow_add,Nat.sub_add_cancel ht,hm]
     ring
    rwa [he] at hbound)
 have hlen:(2*m)*p^r=2*N := by rw [hm];ring
 rw [hlen,doubled_sum_eq] at hs
 rw [←Nat.cast_pow,←ZMod.intCast_zmod_eq_zero_iff_dvd]
 push_cast
 rw [sum_congr rfl (fun k hk=>by
   rw [←kernel_eq_inverseLift hp (mem_filter.mp hk).2])]
 exact hs

lemma unit_terms_dvd {p r N:ℕ} (hp:p.Prime) (hp5:5≤p) (hr:1≤r)
 (hN:0<N) (hNr:p^r∣N):
 (p:ℤ)^(3*r)∣∑k∈(range N).filter (fun k=>¬p∣k),term N k := by
 exact unit_sum_dvd hp hN hNr (inverseLift p r) (fun k hk=>inverseLift_spec hp hk)
  (weighted_inverseSquare_dvd hp hp5 hr hN hNr)
end A363983

end

section

namespace A363983
open A363990Valuation OeisA363986Part23

/-- Ordinary binomial scaling with the larger power attached to the index. -/
private theorem choose_scale_bound_index {p A k R t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hA : p^t ∣ A) (hk : p^R ∣ k) (ht : t ≤ R) :
    (p : ℤ) ^ (3+R+2*t+padicValNat p (A.choose k)) ∣
      ((A*p).choose (k*p) : ℤ) - A.choose k := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hk0 : k=0
  · subst k
    simp
  by_cases hka : k<A
  · have hD : 0 < A-k := Nat.sub_pos_of_lt hka
    have hA0 : 0 < A := lt_of_le_of_lt (Nat.zero_le k) hka
    have hkt : p^t ∣ k := (pow_dvd_pow p ht).trans hk
    have hDt : p^t ∣ A-k := Nat.dvd_sub hA hkt
    have hvA := (padicValNat_dvd_iff_le hA0.ne').mp hA
    have hvk := (padicValNat_dvd_iff_le hk0).mp hk
    have hvD := (padicValNat_dvd_iff_le hD.ne').mp hDt
    have hd := kazandzidis_pow hp hp5 k (A-k) (Nat.pos_of_ne_zero hk0) hD
    rw [show k+(A-k)=A by omega] at hd
    exact (pow_dvd_pow (p : ℤ) (by omega :
      3+R+2*t+padicValNat p (A.choose k) ≤
        3+padicValNat p k+padicValNat p (A-k)+padicValNat p A+
          padicValNat p (A.choose k))).trans hd
  by_cases he : k=A
  · subst k
    simp
  have hlt : A < k := by omega
  rw [Nat.choose_eq_zero_of_lt hlt,
    Nat.choose_eq_zero_of_lt (Nat.mul_lt_mul_of_pos_right hlt hp.pos)]
  simp

theorem term_scale {p M R k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hM0 : 0 < M) (hM : p^R ∣ M) (hk : k ≤ M) :
    (p : ℤ)^(3*(R+1)) ∣ term (M*p) (k*p) - term M k := by
  by_cases hk0 : k=0
  · subst k
    have hpM := Nat.mul_pos hM0 hp.pos
    simp [term, Nat.choose_eq_zero_of_lt hM0, Nat.choose_eq_zero_of_lt hpM]
  letI : Fact p.Prime := ⟨hp⟩
  let t := min R (padicValNat p k)
  have ht : t ≤ R := min_le_left _ _
  have hkt : p^t ∣ k := (padicValNat_dvd_iff_le hk0).mpr (min_le_right _ _)
  have ha := choose_scale_bound hp hp5 hM hkt ht
  have hb := negChoose_scale_bound hp hp5 hM0 hM hkt ht
  have hc := choose_scale_bound_index hp hp5 (dvd_mul_of_dvd_right hkt 2) hM ht
  have divNat (n : ℕ) : (p : ℤ)^padicValNat p n ∣ (n : ℤ) := by
    exact_mod_cast pow_padicValNat_dvd (p:=p) (n:=n)
  have h4 := four_factor_congr (p : ℤ) (3+R+2*t)
    (padicValNat p (M.choose k)) (padicValNat p (negChoose M k))
    (padicValNat p ((2*k).choose M)) 0
    (M.choose k) (negChoose M k) ((2*k).choose M) 1
    ((M*p).choose (k*p)) (negChoose (M*p) (k*p)) (((2*k)*p).choose (M*p)) 1
    (divNat _) (divNat _) (divNat _) (by simp) ha hb hc (by simp)
  simp only [add_zero, mul_one] at h4
  have hmass : 3*(R+1) ≤ 3+R+2*t+
      padicValNat p (M.choose k)+padicValNat p (negChoose M k)+
        padicValNat p ((2*k).choose M) := by
    by_cases h : R ≤ padicValNat p k
    · dsimp [t]
      rw [min_eq_left h]
      omega
    · have ha' := choose_valuation_ge hp (Nat.pos_of_ne_zero hk0) hk hM
      have hb' := negChoose_valuation_ge hp hM0 (Nat.pos_of_ne_zero hk0) hM
      dsimp [t]
      rw [min_eq_right (by omega : padicValNat p k ≤ R)]
      omega
  have hd := (pow_dvd_pow (p : ℤ) hmass).trans h4
  have hodd := hp.odd_of_ne_two (by omega : p ≠ 2)
  have hs : (-1 : ℤ)^(M*p+k*p) = (-1)^(M+k) := by
    rw [← Nat.add_mul, Nat.mul_comm (M+k) p, pow_mul, hodd.neg_one_pow]
  have hprod := dvd_mul_of_dvd_right hd ((-1 : ℤ)^(M+k))
  have he : term (M*p) (k*p)-term M k =
      (-1 : ℤ)^(M+k)*(
        ((M*p).choose (k*p) : ℤ)*negChoose (M*p) (k*p)*(((2*k)*p).choose (M*p) : ℤ) -
        (M.choose k : ℤ)*negChoose M k*((2*k).choose M : ℤ)) := by
    rw [term, term, hs]
    simp only [negChoose, Nat.mul_assoc]
    ring
  exact he.symm ▸ hprod

end A363983

end

section

namespace A363983
open Finset

def seq (N:ℕ):ℤ:=∑k∈range (N+1),term N k

lemma a_eq_seq (N:ℕ) : OMA.S_oeis_a363983.a N=seq N := by
 unfold OMA.S_oeis_a363983.a seq
 calc
  _=∑k∈Icc ((N+1)/2) N,term N k := by
   apply sum_congr rfl
   intro k hk
   dsimp [term]
   push_cast
   ring
  _=_ := by
   apply sum_subset
   · intro k hk
     simp only [mem_Icc,mem_range] at hk ⊢
     omega
   · intro k hk hnot
     have hk':k<N+1:=mem_range.mp hk
     have hkl:k < (N+1)/2 := by simp only [mem_Icc,not_and_or,not_le] at hnot;omega
     have htop:2*k<N := by omega
     simp [term,Nat.choose_eq_zero_of_lt htop]

theorem sum_multiples_closed (p L : ℕ) (hp : 0 < p) (f : ℕ → ℤ) :
    ∑ j ∈ (range (L*p+1)).filter (fun j => p ∣ j), f j =
      ∑ j ∈ range (L+1), f (j*p) := by
  have hset : (range (L*p+1)).filter (fun j => p ∣ j) =
      (range (L+1)).image (fun j => j*p) := by
    ext j
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hj, ⟨k, rfl⟩⟩
      refine ⟨k, ?_, by ring⟩
      have hh : k*p ≤ L*p := by simpa [mul_comm] using (show p*k ≤ L*p by omega)
      nlinarith
    · rintro ⟨k,hk,rfl⟩
      constructor
      · have := Nat.mul_le_mul_right p (show k ≤ L by omega)
        omega
      · exact dvd_mul_left p k
  rw [hset, sum_image]
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_right hp hab


lemma seq_step {p R M:ℕ} (hp:p.Prime) (hp5:5≤p) (hM0:0<M) (hM:p^R∣M):
 (p:ℤ)^(3*(R+1))∣seq (M*p)-seq M := by
 have hon:(p:ℤ)^(3*(R+1))∣
   (∑k∈(range (M*p+1)).filter (fun k=>p∣k),term (M*p) k)-seq M := by
  rw [sum_multiples_closed p M hp.pos,seq,←sum_sub_distrib]
  apply dvd_sum
  intro k hk
  exact term_scale hp hp5 hM0 hM (by have :=mem_range.mp hk;omega)
 have hNr:p^(R+1)∣M*p := by
  rw [pow_succ]
  exact mul_dvd_mul hM (dvd_refl p)
 have hun:=unit_terms_dvd hp hp5 (by omega:1≤R+1) (Nat.mul_pos hM0 hp.pos) hNr
 have hfilter:(range (M*p+1)).filter (fun k=>¬p∣k)=
   (range (M*p)).filter (fun k=>¬p∣k) := by
  rw [range_add_one,filter_insert]
  simp [dvd_mul_left p M]
 have hsplit:seq (M*p)=
   (∑k∈(range (M*p+1)).filter (fun k=>p∣k),term (M*p) k)+
   ∑k∈(range (M*p+1)).filter (fun k=>¬p∣k),term (M*p) k :=
  (sum_filter_add_sum_filter_not (range (M*p+1)) (fun k=>p∣k) _).symm
 rw [hfilter] at hsplit
 have he:seq (M*p)-seq M=
   ((∑k∈(range (M*p+1)).filter (fun k=>p∣k),term (M*p) k)-seq M)+
   ∑k∈(range (M*p)).filter (fun k=>¬p∣k),term (M*p) k := by rw [hsplit];ring
 rw [he]
 exact hon.add hun

theorem solution : ∀p:ℕ,p.Prime→5≤p→∀n r:ℕ,1≤n→1≤r→
 (p:ℤ)^(3*r)∣OMA.S_oeis_a363983.a (n*p^r)-OMA.S_oeis_a363983.a (n*p^(r-1)) := by
 intro p hp hp5 n r hn hr
 let M:=n*p^(r-1)
 have hM0:0<M:=Nat.mul_pos (by omega) (pow_pos hp.pos _)
 have hM:p^(r-1)∣M:=dvd_mul_left _ _
 have hh:=seq_step hp hp5 hM0 hM
 have he:r-1+1=r:=by omega
 have hNp:M*p=n*p^r:=by dsimp [M];rw [mul_assoc,←pow_succ,he]
 rw [he,hNp] at hh
 rw [a_eq_seq,a_eq_seq]
 exact hh
end A363983

end

theorem OMA.solution : type_of% @OMA.S_oeis_a363983.main := A363983.solution
