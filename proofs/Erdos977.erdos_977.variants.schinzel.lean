import FormalConjectures.ErdosProblems.«977»

-- Problem: Erdős Problem 977 — schinzel
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/977.lean:65 (declaration Erdos977.erdos_977.variants.schinzel)
-- Credit: @sebastianbachmaier (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Polynomial

namespace OMA977

lemma two_pow_dvd_of_orderOf {q d : ℕ} [Fact q.Prime] (h : orderOf (2 : ZMod q) = d) :
    q ∣ 2 ^ d - 1 := by
  have h1 : (2 : ZMod q) ^ d = 1 := by rw [← h]; exact pow_orderOf_eq_one 2
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow]
  simp [h1]

lemma dvd_sub_one_of_orderOf {q d : ℕ} [Fact q.Prime] (h : orderOf (2 : ZMod q) = d)
    (hd : 0 < d) : d ∣ q - 1 := by
  have h1 : (2 : ZMod q) ^ d = 1 := by rw [← h]; exact pow_orderOf_eq_one 2
  rw [← h]
  apply ZMod.orderOf_dvd_card_sub_one
  intro h0
  rw [h0, zero_pow hd.ne'] at h1
  exact zero_ne_one h1

lemma P_lemma (a : ℤ) (ha : 2 ≤ |a|) (m q : ℕ) (hm : 0 < m) (hq : q.Prime) (hq2 : q ≠ 2)
    (hqm : q ∣ m) (hqd : (q : ℤ) ∣ eval a (cyclotomic m ℤ)) :
    (∀ t, t.Prime → t ∣ m → t ≤ q) ∧ ¬ ((q : ℤ) ^ 2 ∣ eval a (cyclotomic m ℤ)) := by
  haveI := Fact.mk hq
  obtain ⟨s, m', hm'q, hmeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' q hq.one_lt.ne'
  have hm'0 : m' ≠ 0 := by rintro rfl; simp at hmeq; omega
  haveI : NeZero (m' : ZMod q) := ⟨by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hm'q⟩
  have hroot : IsRoot (cyclotomic (q ^ s * m') (ZMod q)) (a : ZMod q) := by
    rw [IsRoot.def, ← hmeq]
    have := cyclotomic.eval_apply a m (Int.castRingHom (ZMod q))
    simp only [eq_intCast] at this
    rw [this, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hqd
  have hprim : IsPrimitiveRoot (a : ZMod q) m' :=
    (isRoot_cyclotomic_prime_pow_mul_iff_of_charP).1 hroot
  have ha0 : (a : ZMod q) ≠ 0 := hprim.ne_zero hm'0
  have hdvd : m' ∣ q - 1 := by
    rw [hprim.eq_orderOf]; exact ZMod.orderOf_dvd_card_sub_one ha0
  have hm'le : m' ≤ q - 1 := Nat.le_of_dvd (by have := hq.two_le; omega) hdvd
  refine ⟨fun t ht htm => ?_, ?_⟩
  · rw [hmeq] at htm
    rcases (Nat.Prime.dvd_mul ht).1 htm with h | h
    · exact le_of_eq ((Nat.prime_dvd_prime_iff_eq ht hq).1 (ht.dvd_of_dvd_pow h))
    · have := Nat.le_of_dvd (Nat.pos_of_ne_zero hm'0) h; omega
  · have hs : s ≠ 0 := by
      rintro rfl; simp at hmeq; exact hm'q (hmeq ▸ hqm)
    have hmd : m = (q ^ (s - 1) * m') * q := by
      rw [hmeq]
      obtain ⟨s', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs
      simp [pow_succ]; ring
    have hdpos : 0 < q ^ (s - 1) * m' := by
      have := hq.pos; positivity
    have hb1 : (q : ℤ) ∣ a ^ (q ^ (s - 1) * m') - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [mul_comm, pow_mul, hprim.pow_eq_one, one_pow, sub_self]
    obtain ⟨c, hc⟩ := hb1
    have hbne : a ^ (q ^ (s - 1) * m') - 1 ≠ 0 := by
      intro h0
      have h2 : |a ^ (q ^ (s - 1) * m')| = |a| ^ (q ^ (s - 1) * m') := abs_pow _ _
      have h3 : (2:ℤ) ≤ |a| ^ (q ^ (s - 1) * m') :=
        le_trans ha (le_self_pow₀ (by linarith) hdpos.ne')
      rw [show a ^ (q ^ (s - 1) * m') = 1 by linarith] at h2
      simp at h2; linarith
    have hdiv : (a ^ (q ^ (s - 1) * m') - 1) * eval a (cyclotomic m ℤ) ∣
        (a ^ (q ^ (s - 1) * m')) ^ q - 1 := by
      have hmem : q ^ (s - 1) * m' ∈ m.properDivisors := by
        rw [Nat.mem_properDivisors]; refine ⟨⟨q, hmd⟩, ?_⟩
        rw [hmd]; have := hq.two_le
        nlinarith
      have := eval_dvd (x := a) (X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ hmem)
      rw [← pow_mul, ← hmd]
      simpa [eval_mul, eval_sub, eval_pow, eval_X, eval_one] using this
    have hS : eval a (cyclotomic m ℤ) ∣ ∑ i ∈ Finset.range q, (a ^ (q ^ (s - 1) * m')) ^ i := by
      have hgeom : (a ^ (q ^ (s - 1) * m')) ^ q - 1 = (a ^ (q ^ (s - 1) * m') - 1) *
          ∑ i ∈ Finset.range q, (a ^ (q ^ (s - 1) * m')) ^ i := by
        rw [← geom_sum_mul]; ring
      rw [hgeom] at hdiv
      exact (mul_dvd_mul_iff_left hbne).1 hdiv
    have key := odd_sq_dvd_geom_sum₂_sub (R := ℤ) 1 c (hq.odd_of_ne_two hq2)
    simp only [one_pow, mul_one] at key
    rw [show (1:ℤ) + q * c = a ^ (q ^ (s - 1) * m') by linarith] at key
    intro hsq
    have h3 : (q:ℤ) ^ 2 ∣ (q : ℤ) := by
      have := (dvd_sub (hsq.trans hS) key)
      simpa using this
    have h4 : q ^ 2 ∣ q := by exact_mod_cast h3
    have := Nat.le_of_dvd hq.pos h4
    have := hq.two_le
    nlinarith

lemma le_of_prime_factors (N n e : ℕ) (hN : 1 < N) (hn : 0 < n)
    (h : ∀ q, q.Prime → q ∣ N → q ∣ n ∧ (∀ t, t.Prime → t ∣ n → t ≤ q) ∧ N.factorization q ≤ e) :
    N ≤ (Nat.maxPrimeFac n) ^ e := by
  obtain ⟨q, hq, hqN⟩ := Nat.exists_prime_and_dvd hN.ne'
  obtain ⟨hqn, hqmax, hqe⟩ := h q hq hqN
  have huniq : ∀ {d : ℕ}, d.Prime → d ∣ N → d = q := by
    intro d hd hdN
    obtain ⟨hdn, hdmax, _⟩ := h d hd hdN
    exact le_antisymm (hqmax _ hd hdn) (hdmax _ hq hqn)
  have hNe := Nat.eq_prime_pow_of_unique_prime_dvd (by omega) huniq
  have hf : N.factorization q = N.primeFactorsList.length := by
    conv_lhs => rw [hNe]
    simp [hq.factorization_pow]
  rw [hNe, ← hf]
  calc q ^ N.factorization q ≤ q ^ e := Nat.pow_le_pow_right hq.pos hqe
    _ ≤ _ := Nat.pow_le_pow_left (Nat.le_maxPrimeFac hn.ne' hq hqn) e

lemma norm_cyclotomic_le (m : ℕ) (hm : 0 < m) (Y : ℂ) :
    ‖eval Y (cyclotomic m ℂ)‖ ≤ (‖Y‖ + 1) ^ Nat.totient m := by
  have hζ := Complex.isPrimitiveRoot_exp m hm.ne'
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots hζ, eval_prod, norm_prod,
    ← Complex.card_primitiveRoots m, ← Finset.prod_const]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro μ hμ
  rw [mem_primitiveRoots hm] at hμ
  simp only [eval_sub, eval_X, eval_C]
  calc ‖Y - μ‖ ≤ ‖Y‖ + ‖μ‖ := norm_sub_le _ _
    _ = ‖Y‖ + 1 := by rw [hμ.norm'_eq_one hm.ne']

lemma norm_cyclotomic_ge (m : ℕ) (hm : 0 < m) (Y : ℂ) (hY : 1 ≤ ‖Y‖) :
    (‖Y‖ - 1) ^ Nat.totient m ≤ ‖eval Y (cyclotomic m ℂ)‖ := by
  have hζ := Complex.isPrimitiveRoot_exp m hm.ne'
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots hζ, eval_prod, norm_prod,
    ← Complex.card_primitiveRoots m, ← Finset.prod_const]
  apply Finset.prod_le_prod (fun _ _ => sub_nonneg.2 hY)
  intro μ hμ
  rw [mem_primitiveRoots hm] at hμ
  simp only [eval_sub, eval_X, eval_C]
  calc ‖Y‖ - 1 = ‖Y‖ - ‖μ‖ := by rw [hμ.norm'_eq_one hm.ne']
    _ ≤ ‖Y - μ‖ := norm_sub_norm_le _ _

lemma eval_cyclotomic_mul_pow (R : Type*) [CommRing R] (r : ℕ) (hr : r.Prime) (a : ℕ)
    (har : r ∣ a) : ∀ (t : ℕ) (z : R),
    eval z (cyclotomic (a * r ^ t) R) = eval (z ^ (r ^ t)) (cyclotomic a R)
  | 0, z => by simp
  | t + 1, z => by
    rw [pow_succ, ← mul_assoc, ← cyclotomic_expand_eq_cyclotomic hr (dvd_mul_of_dvd_left har _),
      expand_eval, eval_cyclotomic_mul_pow R r hr a har t, ← pow_mul]
    congr 2; ring

lemma lower_bound (r s m : ℕ) (hr : r.Prime) (hs : 1 ≤ s) (hm : 0 < m) (hrm : ¬ r ∣ m)
    (z : ℂ) (hz : 1 ≤ ‖z‖) :
    ((‖z‖ ^ (r ^ (s - 1))) ^ r - 1) ^ Nat.totient m ≤
      ‖eval z (cyclotomic (r ^ s * m) ℂ)‖ * (‖z‖ ^ (r ^ (s - 1)) + 1) ^ Nat.totient m := by
  have hk : r ^ s * m = (m * r) * r ^ (s - 1) := by
    obtain ⟨s', rfl⟩ := Nat.exists_eq_add_of_le' hs
    simp [pow_succ]; ring
  have h1 : eval z (cyclotomic (r ^ s * m) ℂ) =
      eval (z ^ (r ^ (s - 1))) (cyclotomic (m * r) ℂ) := by
    rw [hk, eval_cyclotomic_mul_pow ℂ r hr (m * r) (dvd_mul_left r m)]
  have h2 : eval (z ^ (r ^ (s - 1))) (cyclotomic (m * r) ℂ) *
      eval (z ^ (r ^ (s - 1))) (cyclotomic m ℂ) =
      eval ((z ^ (r ^ (s - 1))) ^ r) (cyclotomic m ℂ) := by
    rw [← eval_mul, ← cyclotomic_expand_eq_cyclotomic_mul hr hrm, expand_eval]
  have hy : ‖z ^ (r ^ (s - 1))‖ = ‖z‖ ^ (r ^ (s - 1)) := norm_pow _ _
  have hy1 : 1 ≤ ‖z ^ (r ^ (s - 1))‖ := hy ▸ one_le_pow₀ hz
  have h3 := norm_cyclotomic_ge m hm ((z ^ (r ^ (s - 1))) ^ r)
    (by rw [norm_pow]; exact one_le_pow₀ hy1)
  have h4 := norm_cyclotomic_le m hm (z ^ (r ^ (s - 1)))
  rw [norm_pow, hy] at h3
  rw [hy] at h4
  rw [h1]
  calc _ ≤ ‖eval ((z ^ (r ^ (s - 1))) ^ r) (cyclotomic m ℂ)‖ := h3
    _ = ‖eval (z ^ (r ^ (s - 1))) (cyclotomic (m * r) ℂ)‖ *
        ‖eval (z ^ (r ^ (s - 1))) (cyclotomic m ℂ)‖ := by rw [← h2, norm_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (norm_nonneg _)

lemma pow_ineq (u A c r : ℝ) (φ : ℕ) (hφ : φ ≠ 0) (hu : 0 < u + 1) (hc : 0 ≤ c)
    (hA : c * (u + 1) < A) (hr : r ≤ c ^ φ) : r * (u + 1) ^ φ < A ^ φ := by
  calc r * (u + 1) ^ φ ≤ c ^ φ * (u + 1) ^ φ := mul_le_mul_of_nonneg_right hr (pow_pos hu _).le
    _ = (c * (u + 1)) ^ φ := (mul_pow _ _ _).symm
    _ < A ^ φ := pow_lt_pow_left₀ hA (by positivity) hφ

lemma grow (u : ℝ) (hu : 14 / 5 ≤ u) : ∀ r : ℕ, 3 ≤ r → (r : ℝ) * (u + 1) < u ^ r - 1 := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
    have h2 : 14 / 5 * u ≤ u * u := mul_le_mul_of_nonneg_right hu (by linarith)
    have h3 : 14 / 5 * (u * u) ≤ u * (u * u) := mul_le_mul_of_nonneg_right hu (by positivity)
    push_cast
    nlinarith
  | succ r hr ih =>
    have hu0 : 0 < u := by linarith
    have h1 := mul_lt_mul_of_pos_left ih hu0
    push_cast
    rw [pow_succ]
    have : (3:ℝ) ≤ r := by exact_mod_cast hr
    have h2 : (0:ℝ) ≤ (u + 1) * (u * r - r - 1) := mul_nonneg (by linarith) (by nlinarith)
    nlinarith

lemma grow2 : ∀ r : ℕ, 11 ≤ r → (r : ℝ) * (Real.sqrt 2 + 1) < Real.sqrt 2 ^ r - 1 := by
  have ht2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ht : (1.4 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have ht' : Real.sqrt 2 < 1.5 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
    have : Real.sqrt 2 ^ 11 = 32 * Real.sqrt 2 := by
      rw [show 11 = 2 * 5 + 1 by rfl, pow_succ, pow_mul, ht2]; norm_num
    rw [this]; push_cast; nlinarith
  | succ r hr ih =>
    have h1 := mul_lt_mul_of_pos_left ih (by linarith : (0:ℝ) < Real.sqrt 2)
    push_cast
    rw [pow_succ]
    have : (11:ℝ) ≤ r := by exact_mod_cast hr
    nlinarith

lemma grow3 : ∀ r : ℕ, 4 ≤ r → 3 * r + 1 < 2 ^ r := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih => rw [pow_succ]; omega

lemma totient_ge_two (m : ℕ) (hm : 3 ≤ m) : 2 ≤ Nat.totient m := by
  have h1 := Nat.totient_even (by omega : 2 < m)
  have h2 : 0 < Nat.totient m := Nat.totient_pos.2 (by omega)
  obtain ⟨t, ht⟩ := h1
  omega


lemma conclude (X u A r : ℝ) (φ : ℕ) (hu : 0 < u + 1) (LB : A ^ φ ≤ X * (u + 1) ^ φ)
    (key : r * (u + 1) ^ φ < A ^ φ) : r < X :=
  lt_of_mul_lt_mul_right (lt_of_lt_of_le key LB) (pow_pos hu _).le

lemma cyc_two_complex (n : ℕ) :
    ‖eval (2:ℂ) (cyclotomic n ℂ)‖ = ((eval (2:ℤ) (cyclotomic n ℤ)).natAbs : ℝ) := by
  have := cyclotomic.eval_apply (2:ℤ) n (Int.castRingHom ℂ)
  simp only [eq_intCast, Int.cast_ofNat] at this
  rw [this, Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs]

lemma zsigmondy (n : ℕ) (hn : 7 ≤ n) : ∃ q, q.Prime ∧ orderOf (2 : ZMod q) = n := by
  have hN1 : 1 < (eval (2:ℤ) (cyclotomic n ℤ)).natAbs := by
    have := sub_one_lt_natAbs_cyclotomic_eval (n := n) (q := 2) (by omega) (by norm_num)
    simpa using this
  have hodd : ¬ (2:ℤ) ∣ eval (2:ℤ) (cyclotomic n ℤ) := by
    have h := sub_dvd_eval_sub (2:ℤ) 0 (cyclotomic n ℤ)
    rw [← coeff_zero_eq_eval_zero, cyclotomic_coeff_zero ℤ (by omega)] at h
    intro h2
    have := dvd_sub h2 h
    norm_num at this
  by_contra hcon
  push Not at hcon
  have hall : ∀ q, q.Prime → q ∣ (eval (2:ℤ) (cyclotomic n ℤ)).natAbs → q ∣ n := by
    intro q hq hqN
    by_contra hqn
    apply hcon q hq
    haveI := Fact.mk hq
    haveI : NeZero (n : ZMod q) := ⟨by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hqn⟩
    have hroot : IsRoot (cyclotomic n (ZMod q)) (2 : ZMod q) := by
      rw [IsRoot.def]
      have := cyclotomic.eval_apply (2:ℤ) n (Int.castRingHom (ZMod q))
      simp only [eq_intCast, Int.cast_ofNat] at this
      rw [this, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact Int.natCast_dvd.2 hqN
    exact ((isRoot_cyclotomic_iff).1 hroot).eq_orderOf.symm
  have hP : ∀ q, q.Prime → q ∣ (eval (2:ℤ) (cyclotomic n ℤ)).natAbs →
      q ∣ n ∧ (∀ t, t.Prime → t ∣ n → t ≤ q) ∧
        (eval (2:ℤ) (cyclotomic n ℤ)).natAbs.factorization q ≤ 1 := by
    intro q hq hqN
    have hqn := hall q hq hqN
    have hqΦ : (q:ℤ) ∣ eval (2:ℤ) (cyclotomic n ℤ) := Int.natCast_dvd.2 hqN
    have hq2 : q ≠ 2 := by rintro rfl; exact hodd (by exact_mod_cast hqΦ)
    obtain ⟨h1, h2⟩ := P_lemma 2 (by norm_num) n q (by omega) hq hq2 hqn hqΦ
    refine ⟨hqn, h1, ?_⟩
    by_contra hf
    push Not at hf
    apply h2
    have : q ^ 2 ∣ (eval (2:ℤ) (cyclotomic n ℤ)).natAbs :=
      (hq.pow_dvd_iff_le_factorization (by omega)).2 hf
    exact Int.natCast_dvd.2 (by exact_mod_cast this)
  have hle := le_of_prime_factors _ n 1 hN1 (by omega) hP
  rw [pow_one] at hle
  obtain ⟨q0, hq0, hq0N⟩ := Nat.exists_prime_and_dvd hN1.ne'
  obtain ⟨hq0n, -, -⟩ := hP q0 hq0 hq0N
  have hq02 : q0 ≠ 2 := by
    rintro rfl; exact hodd (by exact_mod_cast (Int.natCast_dvd.2 hq0N))
  have hrp : (Nat.maxPrimeFac n).Prime := Nat.prime_maxPrimeFac_of_one_lt n (by omega)
  have hr3 : 3 ≤ Nat.maxPrimeFac n := by
    have := Nat.le_maxPrimeFac (by omega) hq0 hq0n
    have := hq0.two_le
    omega
  set r := Nat.maxPrimeFac n with hr
  obtain ⟨s, m, hrm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) r (by omega)
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hnm; omega
    · exact h
  have hs : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · exfalso
      have hrn : r ∣ n := hr ▸ Nat.maxPrimeFac_dvd
      rw [h, pow_zero, one_mul] at hnm; rw [hnm] at hrn; exact hrm hrn
    · exact h
  have LB := lower_bound r s m hrp hs hm hrm (2:ℂ) (by norm_num)
  rw [← hnm, cyc_two_complex] at LB
  have h2n : ‖(2:ℂ)‖ = 2 := by norm_num
  rw [h2n] at LB
  have hφ : Nat.totient m ≠ 0 := (Nat.totient_pos.2 hm).ne'
  have hrR : (3:ℝ) ≤ r := by exact_mod_cast hr3
  have key : (r:ℝ) < ((eval (2:ℤ) (cyclotomic n ℤ)).natAbs : ℝ) := by
    apply conclude _ _ _ _ _ (by positivity) LB
    rcases (by omega : s = 1 ∨ 2 ≤ s) with hs1 | hs2
    · subst hs1
      simp only [Nat.sub_self, pow_zero, pow_one]
      rcases (by omega : r = 3 ∨ 4 ≤ r) with hr3' | hr4
      · have hm3 : 3 ≤ m := by rw [hr3', pow_one] at hnm; omega
        have hφ2 := totient_ge_two m hm3
        apply pow_ineq _ _ (23 / 10) _ _ hφ (by norm_num) (by norm_num)
        · rw [hr3']; norm_num
        · rw [hr3']
          calc ((3:ℕ):ℝ) ≤ (23/10) ^ 2 := by norm_num
            _ ≤ _ := pow_le_pow_right₀ (by norm_num) hφ2
      · apply pow_ineq _ _ r _ _ hφ (by norm_num) (by positivity)
        · have := grow3 r hr4
          have : ((3 * r + 1 : ℕ) : ℝ) < ((2 ^ r : ℕ) : ℝ) := by exact_mod_cast this
          push_cast at this
          linarith
        · exact le_self_pow₀ (by linarith) hφ
    · have hu : (14 / 5 : ℝ) ≤ 2 ^ (r ^ (s - 1)) := by
        have h1 : 3 ≤ r ^ (s - 1) :=
          le_trans hr3 (Nat.le_self_pow (by omega) r)
        calc (14 / 5 : ℝ) ≤ 2 ^ 3 := by norm_num
          _ ≤ _ := pow_le_pow_right₀ (by norm_num) h1
      apply pow_ineq _ _ r _ _ hφ (by positivity) (by positivity)
      · exact grow _ hu r hr3
      · exact le_self_pow₀ (by linarith) hφ
  have : ((eval (2:ℤ) (cyclotomic n ℤ)).natAbs : ℝ) ≤ r := by exact_mod_cast hle
  linarith


lemma w_sq : (⟨1, 1⟩ : GaussianInt) ^ 2 = ⟨0, 2⟩ := by
  ext <;> simp [pow_two]

lemma w'_sq : (⟨-1, -1⟩ : GaussianInt) ^ 2 = ⟨0, 2⟩ := by
  ext <;> simp [pow_two]

lemma i2_sq : (⟨0, 2⟩ : GaussianInt) ^ 2 = ((-4 : ℤ) : GaussianInt) := by
  ext <;> simp [pow_two]

lemma i2_pow_even (t : ℕ) :
    (⟨0, 2⟩ : GaussianInt) ^ (2 * t) = (((-4 : ℤ) ^ t : ℤ) : GaussianInt) := by
  rw [pow_mul, i2_sq, Int.cast_pow]

lemma norm_c_i2_sub_one (c : ℤ) :
    ((c : GaussianInt) * ⟨0, 2⟩ - 1).norm = 1 + 4 * c ^ 2 := by
  simp [Zsqrtd.norm_def]; ring

lemma re_c_w (c : ℤ) : ((c : GaussianInt) * ⟨1, 1⟩).re = c := by
  simp

lemma re_c_i2_w (c : ℤ) : ((c : GaussianInt) * ⟨0, 2⟩ * ⟨1, 1⟩).re = -2 * c := by
  simp; ring

lemma norm_i2_pow_sub_one (j : ℕ) :
    ((⟨0, 2⟩ : GaussianInt) ^ (2 * j + 1) - 1).norm = 4 ^ (2 * j + 1) + 1 := by
  rw [pow_succ, i2_pow_even, norm_c_i2_sub_one]
  have h1 : ((-4 : ℤ) ^ j) ^ 2 = 16 ^ j := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h2 : (4 : ℤ) ^ (2 * j + 1) = 16 ^ j * 4 := by
    rw [pow_succ, pow_mul]; norm_num
  rw [h2, h1]; ring

lemma re_w_pow (j : ℕ) : ∃ e, (((⟨1, 1⟩ : GaussianInt)) ^ (2 * j + 1)).re.natAbs = 2 ^ e := by
  rw [pow_succ, pow_mul, w_sq]
  rcases Nat.even_or_odd' j with ⟨t, rfl | rfl⟩
  · rw [i2_pow_even, re_c_w]
    refine ⟨2 * t, ?_⟩
    rw [Int.natAbs_pow, pow_mul]; norm_num
  · rw [pow_succ, i2_pow_even, re_c_i2_w]
    refine ⟨2 * t + 1, ?_⟩
    rw [Int.natAbs_mul, Int.natAbs_pow, pow_succ, pow_mul]; norm_num; ring

lemma coprime_norms (k : ℕ) (hk : Odd k) (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (h1 : (q:ℤ) ∣ ((⟨1, 1⟩ : GaussianInt) ^ k - 1).norm)
    (h2 : (q:ℤ) ∣ ((⟨1, 1⟩ : GaussianInt) ^ k + 1).norm) : False := by
  obtain ⟨j, rfl⟩ := hk
  obtain ⟨e, he⟩ := re_w_pow j
  have hd : (((⟨1, 1⟩ : GaussianInt) ^ (2 * j + 1)) + 1).norm -
      (((⟨1, 1⟩ : GaussianInt) ^ (2 * j + 1)) - 1).norm =
      4 * ((⟨1, 1⟩ : GaussianInt) ^ (2 * j + 1)).re := by
    simp only [Zsqrtd.norm_def, Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_sub, Zsqrtd.im_sub,
      Zsqrtd.re_one, Zsqrtd.im_one]
    ring
  have h3 : (q:ℤ) ∣ 4 * ((⟨1, 1⟩ : GaussianInt) ^ (2 * j + 1)).re := hd ▸ dvd_sub h2 h1
  have hqp : Prime (q:ℤ) := Nat.prime_iff_prime_int.1 hq
  rcases hqp.dvd_or_dvd h3 with h4 | h4
  · have h5 : q ∣ 4 := by exact_mod_cast h4
    have : q ∣ 2 := hq.dvd_of_dvd_pow (show q ∣ 2 ^ 2 by simpa using h5)
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 this)
  · have : q ∣ 2 ^ e := he ▸ Int.natCast_dvd.1 h4
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow this))

lemma norm_dvd_of_dvd {x y : GaussianInt} (h : x ∣ y) : x.norm ∣ y.norm := by
  obtain ⟨c, rfl⟩ := h
  rw [Zsqrtd.norm_mul]
  exact dvd_mul_right _ _

lemma ord_of_root (k q : ℕ) (hk : Odd k) (hq : q.Prime) (hq2 : q ≠ 2) (hqk : ¬ q ∣ k)
    (φ : GaussianInt →+* ZMod q) (hφi : φ ⟨0, 1⟩ * φ ⟨0, 1⟩ = -1) (v : GaussianInt)
    (hv : v ^ 2 = ⟨0, 2⟩) (h0 : φ (eval v (cyclotomic k GaussianInt)) = 0) :
    orderOf (2 : ZMod q) = 4 * k := by
  haveI := Fact.mk hq
  haveI : NeZero (k : ZMod q) := ⟨by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hqk⟩
  have hroot : IsRoot (cyclotomic k (ZMod q)) (φ v) := by
    rw [IsRoot.def, cyclotomic.eval_apply, h0]
  have hprim : IsPrimitiveRoot (φ v) k := (isRoot_cyclotomic_iff).1 hroot
  have hcop : Nat.Coprime 2 k := (Nat.coprime_two_left).2 hk
  have hprim2 : IsPrimitiveRoot ((φ v) ^ 2) k := hprim.pow_of_coprime 2 hcop
  have hv2 : (φ v) ^ 2 = 2 * φ ⟨0, 1⟩ := by
    rw [← map_pow, hv, show (⟨0, 2⟩ : GaussianInt) = 2 * ⟨0, 1⟩ by ext <;> simp, map_mul,
      map_ofNat]
  have hne : (-1 : ZMod q) ≠ 1 := by
    intro h
    have : ((2:ℕ) : ZMod q) = 0 := by push_cast; linear_combination -h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 this)
  have hord4 : orderOf (-φ ⟨0, 1⟩) = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := -φ ⟨0, 1⟩) ?_ ?_
    · simpa using this
    · rw [pow_one, neg_sq, sq, hφi]; exact hne
    · have hx2 : (φ ⟨0, 1⟩) ^ 2 = -1 := by rw [sq]; exact hφi
      rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, neg_sq, hx2]; norm_num
  have h2eq : (2 : ZMod q) = (φ v) ^ 2 * (-φ ⟨0, 1⟩) := by
    rw [hv2]; linear_combination 2 * hφi
  have hco : (orderOf ((φ v) ^ 2)).Coprime (orderOf (-φ ⟨0, 1⟩)) := by
    rw [← hprim2.eq_orderOf, hord4, show 4 = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_right 2 hcop.symm
  rw [h2eq, (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime hco, ← hprim2.eq_orderOf,
    hord4, mul_comm]

lemma exists_hom (q : ℕ) (hq : q.Prime) (ι : ZMod q) (hι : ι * ι = -1) (z : GaussianInt)
    (hz : (q:ℤ) ∣ z.norm) : ∃ φ : GaussianInt →+* ZMod q, φ ⟨0, 1⟩ * φ ⟨0, 1⟩ = -1 ∧ φ z = 0 := by
  haveI := Fact.mk hq
  have hι1 : ι * ι = (((-1 : ℤ)) : ZMod q) := by simpa using hι
  have hι2 : (-ι) * (-ι) = (((-1 : ℤ)) : ZMod q) := by simpa using hι
  have hprod : Zsqrtd.lift ⟨ι, hι1⟩ z * Zsqrtd.lift ⟨-ι, hι2⟩ z = 0 := by
    have : ((z.norm : ℤ) : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hz
    rw [← this, Zsqrtd.lift_apply_apply, Zsqrtd.lift_apply_apply, Zsqrtd.norm_def]
    push_cast
    linear_combination (-(z.im : ZMod q) ^ 2) * hι
  rcases mul_eq_zero.1 hprod with h | h
  · refine ⟨Zsqrtd.lift ⟨ι, hι1⟩, ?_, h⟩
    rw [Zsqrtd.lift_apply_apply]; simpa using hι
  · refine ⟨Zsqrtd.lift ⟨-ι, hι2⟩, ?_, h⟩
    rw [Zsqrtd.lift_apply_apply]; simpa using hι

lemma cyc_dvd_four (k : ℕ) (hk : Odd k) (v : GaussianInt) (hv : v ^ 2 = ⟨0, 2⟩) :
    eval v (cyclotomic k GaussianInt) ∣ ((eval (-4 : ℤ) (cyclotomic k ℤ) : ℤ) : GaussianInt) := by
  have h2 : ¬ 2 ∣ k := by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd]
  have hd1 : cyclotomic k GaussianInt ∣ expand GaussianInt 2 (cyclotomic k GaussianInt) := by
    rw [cyclotomic_expand_eq_cyclotomic_mul Nat.prime_two h2]; exact dvd_mul_left _ _
  have hd2 : cyclotomic k GaussianInt ∣
      expand GaussianInt 2 (expand GaussianInt 2 (cyclotomic k GaussianInt)) := by
    refine hd1.trans ?_
    obtain ⟨c, hc⟩ := hd1
    exact ⟨expand GaussianInt 2 c, by rw [hc, map_mul, hc]⟩
  have := eval_dvd (x := v) hd2
  rw [expand_eval, expand_eval, hv, i2_sq] at this
  have h4 : eval (((-4 : ℤ)) : GaussianInt) (cyclotomic k GaussianInt) =
      ((eval (-4 : ℤ) (cyclotomic k ℤ) : ℤ) : GaussianInt) :=
    cyclotomic.eval_apply (-4 : ℤ) k (Int.castRingHom GaussianInt)
  rw [← h4]
  exact this

lemma norm_toComplex_sq (z : GaussianInt) : ‖GaussianInt.toComplex z‖ ^ 2 = (z.norm : ℝ) := by
  rw [GaussianInt.intCast_real_norm, Complex.normSq_eq_norm_sq]


lemma gauss_lower (k r : ℕ) (hk : Odd k) (hk5 : 5 ≤ k) (h5 : k ≠ 5) (h7 : k ≠ 7) (h15 : k ≠ 15)
    (hrp : r.Prime) (hrk : r ∣ k) (hmax : ∀ t, t.Prime → t ∣ k → t ≤ r)
    (z : ℂ) (hz : ‖z‖ = Real.sqrt 2) :
    (r : ℝ) < ‖eval z (cyclotomic k ℂ)‖ := by
  have ht2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ht : (1.4 : ℝ) < Real.sqrt 2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hr2 : r ≠ 2 := by
    rintro h2; rw [h2] at hrk; exact (Nat.not_even_iff_odd.2 hk) (even_iff_two_dvd.2 hrk)
  have hr3 : 3 ≤ r := by have := hrp.two_le; omega
  obtain ⟨s, m, hrm, hkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : k ≠ 0) r (by omega)
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hkm; omega
    · exact h
  have hs : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · exfalso
      rw [h, pow_zero, one_mul] at hkm; rw [hkm] at hrk; exact hrm hrk
    · exact h
  have hmk : m ∣ k := ⟨r ^ s, by rw [hkm]; ring⟩
  have hmodd : ¬ 2 ∣ m := fun h => (Nat.not_even_iff_odd.2 hk) (even_iff_two_dvd.2 (h.trans hmk))
  have LB := lower_bound r s m hrp hs hm hrm z (by rw [hz]; linarith)
  rw [← hkm, hz] at LB
  have hφ : Nat.totient m ≠ 0 := (Nat.totient_pos.2 hm).ne'
  have hrR : (3:ℝ) ≤ r := by exact_mod_cast hr3
  apply conclude _ _ _ _ _ (by positivity) LB
  rcases (by omega : s = 1 ∨ 2 ≤ s) with hs1 | hs2
  · subst hs1
    simp only [Nat.sub_self, pow_zero, pow_one]
    rw [pow_one] at hkm
    have hmprimes : ∀ t, t.Prime → t ∣ m → t < r ∧ t ≠ 2 := by
      intro t ht htm
      refine ⟨lt_of_le_of_ne (hmax t ht (htm.trans hmk)) ?_, ?_⟩
      · rintro rfl; exact hrm htm
      · rintro rfl; exact hmodd htm
    by_cases h11 : 11 ≤ r
    · apply pow_ineq _ _ r _ _ hφ (by positivity) (by positivity)
      · exact grow2 r h11
      · exact le_self_pow₀ (by linarith) hφ
    · interval_cases r
      · exfalso
        have hm1 : m = 1 := by
          rw [Nat.eq_one_iff_not_exists_prime_dvd]
          intro t ht htm
          have := hmprimes t ht htm
          have := ht.two_le
          omega
        omega
      · norm_num at hrp
      · have h3 : ∀ {d : ℕ}, d.Prime → d ∣ m → d = 3 := by
          intro d hd hdm
          have := hmprimes d hd hdm
          have := hd.two_le
          rcases (by omega : d = 3 ∨ d = 4) with h | h
          · exact h
          · subst h; norm_num at hd
        have hm3 := Nat.eq_prime_pow_of_unique_prime_dvd hm.ne' h3
        have h9 : 9 ∣ m := by
          rcases (by omega : m.primeFactorsList.length = 0 ∨ m.primeFactorsList.length = 1 ∨
            2 ≤ m.primeFactorsList.length) with h | h | h
          · rw [h] at hm3; omega
          · rw [h] at hm3; omega
          · rw [hm3]; exact (Nat.pow_dvd_pow 3 h)
        have hφ6 : 6 ≤ Nat.totient m := by
          have := Nat.totient_dvd_of_dvd h9
          have h96 : Nat.totient 9 = 6 := by decide
          rw [h96] at this
          exact Nat.le_of_dvd (Nat.totient_pos.2 hm) this
        apply pow_ineq _ _ (7 / 4) _ _ hφ (by positivity) (by norm_num)
        · rw [show Real.sqrt 2 ^ 5 = (Real.sqrt 2 ^ 2) ^ 2 * Real.sqrt 2 by ring, ht2]
          linarith
        · calc ((5:ℕ):ℝ) ≤ (7 / 4) ^ 6 := by norm_num
            _ ≤ _ := pow_le_pow_right₀ (by norm_num) hφ6
      · norm_num at hrp
      · have hm3 : 3 ≤ m := by omega
        have hφ2 := totient_ge_two m hm3
        apply pow_ineq _ _ 3 _ _ hφ (by positivity) (by norm_num)
        · rw [show Real.sqrt 2 ^ 7 = (Real.sqrt 2 ^ 2) ^ 3 * Real.sqrt 2 by ring, ht2]
          linarith
        · calc ((7:ℕ):ℝ) ≤ 3 ^ 2 := by norm_num
            _ ≤ _ := pow_le_pow_right₀ (by norm_num) hφ2
      · norm_num at hrp
      · norm_num at hrp
      · norm_num at hrp
  · have hu : (14 / 5 : ℝ) ≤ Real.sqrt 2 ^ (r ^ (s - 1)) := by
      have h1 : 3 ≤ r ^ (s - 1) :=
        le_trans hr3 (Nat.le_self_pow (by omega) r)
      calc (14 / 5 : ℝ) ≤ Real.sqrt 2 ^ 3 := by
            rw [show Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 by ring, ht2]; linarith
        _ ≤ _ := pow_le_pow_right₀ (by linarith) h1
    apply pow_ineq _ _ r _ _ hφ (by positivity) (by positivity)
    · exact grow _ hu r hr3
    · exact le_self_pow₀ (by linarith) hφ

lemma gauss_main (k : ℕ) (hk : Odd k) (hk5 : 5 ≤ k) (h5 : k ≠ 5) (h7 : k ≠ 7) (h15 : k ≠ 15)
    (v : GaussianInt) (hv2 : v ^ 2 = ⟨0, 2⟩) (hvn : v.norm = 2) :
    ∃ q, q.Prime ∧ orderOf (2 : ZMod q) = 4 * k ∧ (q : ℤ) ∣ (v ^ k - 1).norm := by
  have hvc : ‖GaussianInt.toComplex v‖ = Real.sqrt 2 := by
    have h := norm_toComplex_sq v
    rw [hvn] at h; push_cast at h
    rw [← h, Real.sqrt_sq (norm_nonneg _)]
  obtain ⟨j, hj⟩ := hk
  have hE : (v ^ k - 1).norm * (v ^ k + 1).norm = 4 ^ k + 1 := by
    rw [← Zsqrtd.norm_mul]
    have : (v ^ k - 1) * (v ^ k + 1) = (⟨0, 2⟩ : GaussianInt) ^ k - 1 := by
      rw [← hv2, ← pow_mul, mul_comm 2 k, pow_mul]; ring
    rw [this, hj, norm_i2_pow_sub_one]
  have hEodd : ¬ (2:ℤ) ∣ (v ^ k - 1).norm := by
    intro h
    have h1 : (2:ℤ) ∣ 4 ^ k + 1 := hE ▸ dvd_mul_of_dvd_left h _
    have h4 : (2:ℤ) ∣ 4 ^ k := dvd_pow (by norm_num) (by omega)
    have := dvd_sub h1 h4
    norm_num at this
  have hΦE : (eval v (cyclotomic k GaussianInt)).norm ∣ (v ^ k - 1).norm := by
    apply norm_dvd_of_dvd
    simpa using eval_dvd (x := v) (cyclotomic.dvd_X_pow_sub_one k GaussianInt)
  have hΦF : (eval v (cyclotomic k GaussianInt)).norm ∣
      eval (-4 : ℤ) (cyclotomic k ℤ) * eval (-4 : ℤ) (cyclotomic k ℤ) := by
    have := norm_dvd_of_dvd (cyc_dvd_four k ⟨j, hj⟩ v hv2)
    rwa [Zsqrtd.norm_intCast] at this
  have hrp : (Nat.maxPrimeFac k).Prime := Nat.prime_maxPrimeFac_of_one_lt k (by omega)
  have LBc := gauss_lower k (Nat.maxPrimeFac k) ⟨j, hj⟩ hk5 h5 h7 h15 hrp Nat.maxPrimeFac_dvd
    (fun t ht htk => Nat.le_maxPrimeFac (by omega) ht htk) _ hvc
  rw [cyclotomic.eval_apply v k GaussianInt.toComplex] at LBc
  have hLr : ((Nat.maxPrimeFac k : ℕ) : ℝ) ^ 2 <
      ((eval v (cyclotomic k GaussianInt)).norm.natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast GaussianInt.norm_nonneg _),
      ← norm_toComplex_sq]
    exact pow_lt_pow_left₀ LBc (by positivity) (by norm_num)
  have hr3 : 3 ≤ Nat.maxPrimeFac k := by
    have := hrp.two_le
    have : Nat.maxPrimeFac k ≠ 2 := by
      intro h2
      have hd : 2 ∣ k := h2 ▸ Nat.maxPrimeFac_dvd
      exact (Nat.not_even_iff_odd.2 ⟨j, hj⟩) (even_iff_two_dvd.2 hd)
    omega
  have hL1 : 1 < (eval v (cyclotomic k GaussianInt)).norm.natAbs := by
    have : ((3:ℕ):ℝ) ^ 2 ≤ ((Nat.maxPrimeFac k : ℕ) : ℝ) ^ 2 := by
      have : ((3:ℕ):ℝ) ≤ ((Nat.maxPrimeFac k : ℕ) : ℝ) := by exact_mod_cast hr3
      exact pow_le_pow_left₀ (by norm_num) this 2
    have : ((1:ℕ):ℝ) < ((eval v (cyclotomic k GaussianInt)).norm.natAbs : ℝ) := by
      push_cast at *; linarith
    exact_mod_cast this
  by_cases hex : ∃ q, q.Prime ∧ q ∣ (eval v (cyclotomic k GaussianInt)).norm.natAbs ∧ ¬ q ∣ k
  · obtain ⟨q, hq, hqL, hqk⟩ := hex
    have hqZ : (q:ℤ) ∣ (eval v (cyclotomic k GaussianInt)).norm := Int.natCast_dvd.2 hqL
    have hqE : (q:ℤ) ∣ (v ^ k - 1).norm := hqZ.trans hΦE
    have hq2 : q ≠ 2 := by rintro rfl; exact hEodd (by exact_mod_cast hqE)
    haveI := Fact.mk hq
    have hι : (2 : ZMod q) ^ k * (2 : ZMod q) ^ k = -1 := by
      have h4 : (((4 ^ k + 1 : ℤ)) : ZMod q) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (hE ▸ dvd_mul_of_dvd_left hqE _)
      push_cast at h4
      rw [← mul_pow]; norm_num
      linear_combination h4
    obtain ⟨φ, hφi, hφ0⟩ := exists_hom q hq _ hι _ hqZ
    exact ⟨q, hq, ord_of_root k q ⟨j, hj⟩ hq hq2 hqk φ hφi v hv2 hφ0, hqE⟩
  · exfalso
    push Not at hex
    have hP : ∀ q, q.Prime → q ∣ (eval v (cyclotomic k GaussianInt)).norm.natAbs →
        q ∣ k ∧ (∀ t, t.Prime → t ∣ k → t ≤ q) ∧
          (eval v (cyclotomic k GaussianInt)).norm.natAbs.factorization q ≤ 2 := by
      intro q hq hqL
      have hqk := hex q hq hqL
      have hqZ : (q:ℤ) ∣ (eval v (cyclotomic k GaussianInt)).norm := Int.natCast_dvd.2 hqL
      have hqp : Prime (q:ℤ) := Nat.prime_iff_prime_int.1 hq
      have hqF : (q:ℤ) ∣ eval (-4 : ℤ) (cyclotomic k ℤ) :=
        hqp.dvd_of_dvd_pow (n := 2) (by rw [sq]; exact hqZ.trans hΦF)
      have hq2 : q ≠ 2 := by rintro rfl; exact hEodd (by exact_mod_cast hqZ.trans hΦE)
      obtain ⟨h1, h2⟩ := P_lemma (-4) (by norm_num) k q (by omega) hq hq2 hqk hqF
      refine ⟨hqk, h1, ?_⟩
      have hF0 : eval (-4 : ℤ) (cyclotomic k ℤ) ≠ 0 := by
        intro h0; apply h2; rw [h0]; exact dvd_zero _
      have hFf : (eval (-4 : ℤ) (cyclotomic k ℤ)).natAbs.factorization q ≤ 1 := by
        by_contra hf
        push Not at hf
        apply h2
        have : q ^ 2 ∣ (eval (-4 : ℤ) (cyclotomic k ℤ)).natAbs :=
          (hq.pow_dvd_iff_le_factorization (by simpa using hF0)).2 hf
        exact Int.natCast_dvd.2 (by exact_mod_cast this)
      have hdvd : (eval v (cyclotomic k GaussianInt)).norm.natAbs ∣
          (eval (-4 : ℤ) (cyclotomic k ℤ)).natAbs * (eval (-4 : ℤ) (cyclotomic k ℤ)).natAbs := by
        rw [← Int.natAbs_mul]; exact Int.natAbs_dvd_natAbs.2 hΦF
      have hFa : (eval (-4 : ℤ) (cyclotomic k ℤ)).natAbs ≠ 0 := by simpa using hF0
      have := (Nat.factorization_le_iff_dvd (by omega) (mul_ne_zero hFa hFa)).2 hdvd q
      rw [Nat.factorization_mul hFa hFa, Finsupp.add_apply] at this
      omega
    have hle := le_of_prime_factors _ k 2 hL1 (by omega) hP
    have : ((eval v (cyclotomic k GaussianInt)).norm.natAbs : ℝ) ≤
        ((Nat.maxPrimeFac k : ℕ) : ℝ) ^ 2 := by exact_mod_cast hle
    linarith

lemma two_pow_dvd_of_orderOf_dvd {q d n : ℕ} [Fact q.Prime] (h : orderOf (2 : ZMod q) = d)
    (hd : d ∣ n) : q ∣ 2 ^ n - 1 := by
  obtain ⟨c, rfl⟩ := hd
  refine (two_pow_dvd_of_orderOf h).trans ?_
  rw [pow_mul]
  simpa using Nat.sub_dvd_pow_sub_pow (2 ^ d) 1 c

lemma two_primes (n q1 q2 : ℕ) (_hn : 0 < n) (h1 : 2 ≤ q1) (h2 : 2 ≤ q2) (hne : q1 ≠ q2)
    (hd1 : n ∣ q1 - 1) (hd2 : n ∣ q2 - 1) : 2 * n < q1 ∨ 2 * n < q2 := by
  obtain ⟨t1, ht1⟩ := hd1
  obtain ⟨t2, ht2⟩ := hd2
  rcases Nat.lt_or_ge t1 2 with h | h
  · rcases Nat.lt_or_ge t2 2 with h' | h'
    · interval_cases t1 <;> interval_cases t2 <;> omega
    · right; have := Nat.mul_le_mul_left n h'; omega
  · left; have := Nat.mul_le_mul_left n h; omega

lemma main (n : ℕ) (hn : 12 < n) : ∃ q, q.Prime ∧ q ∣ 2 ^ n - 1 ∧ 2 * n < q := by
  rcases Nat.even_or_odd' n with ⟨d, rfl | rfl⟩
  · rcases Nat.even_or_odd' d with ⟨e, rfl | rfl⟩
    · rcases Nat.even_or_odd' e with ⟨f, rfl | rfl⟩
      · obtain ⟨q, hq, hord⟩ := zsigmondy (2 * (2 * (2 * f))) (by omega)
        haveI := Fact.mk hq
        have hdvd := dvd_sub_one_of_orderOf hord (by omega)
        refine ⟨q, hq, two_pow_dvd_of_orderOf hord, ?_⟩
        obtain ⟨t, ht⟩ := hdvd
        have hq2 := hq.two_le
        rcases (by omega : t = 0 ∨ t = 1 ∨ 2 ≤ t) with h | h | h
        · subst h; omega
        · subst h
          exfalso
          have hq8 : q % 8 = 1 := by omega
          have hsq : IsSquare (2 : ZMod q) :=
            (ZMod.exists_sq_eq_two_iff (by omega)).2 (Or.inl hq8)
          have h20 : (2 : ZMod q) ≠ 0 := by
            intro h0
            have := pow_orderOf_eq_one (2 : ZMod q)
            rw [hord, h0, zero_pow (by omega)] at this
            exact zero_ne_one this
          have hpow := (ZMod.euler_criterion q h20).1 hsq
          have := orderOf_dvd_of_pow_eq_one hpow
          rw [hord] at this
          have := Nat.le_of_dvd (by omega) this
          omega
        · have := Nat.mul_le_mul_left (2 * (2 * (2 * f))) h; omega
      · rw [show 2 * (2 * (2 * f + 1)) = 4 * (2 * f + 1) by ring]
        rcases (by omega : f = 2 ∨ f = 3 ∨ f = 7 ∨ (f ≠ 2 ∧ f ≠ 3 ∧ f ≠ 7)) with
          rfl | rfl | rfl | hf
        · exact ⟨41, by norm_num, by norm_num, by norm_num⟩
        · exact ⟨113, by norm_num, by norm_num, by norm_num⟩
        · exact ⟨1321, by norm_num, by norm_num, by norm_num⟩
        · have hk : Odd (2 * f + 1) := ⟨f, rfl⟩
          obtain ⟨q1, hq1, hord1, hd1⟩ := gauss_main (2 * f + 1) hk (by omega) (by omega)
            (by omega) (by omega) ⟨1, 1⟩ w_sq (by rfl)
          obtain ⟨q2, hq2, hord2, hd2⟩ := gauss_main (2 * f + 1) hk (by omega) (by omega)
            (by omega) (by omega) ⟨-1, -1⟩ w'_sq (by rfl)
          have hneg : (⟨-1, -1⟩ : GaussianInt) ^ (2 * f + 1) - 1 =
              -((⟨1, 1⟩ : GaussianInt) ^ (2 * f + 1) + 1) := by
            rw [show (⟨-1, -1⟩ : GaussianInt) = -⟨1, 1⟩ by ext <;> simp, Odd.neg_pow hk]; ring
          rw [hneg, Zsqrtd.norm_neg] at hd2
          haveI := Fact.mk hq1
          haveI := Fact.mk hq2
          have hdv1 := dvd_sub_one_of_orderOf hord1 (by omega)
          have hdv2 := dvd_sub_one_of_orderOf hord2 (by omega)
          have hq1_2 : q1 ≠ 2 := by
            rintro rfl; have := Nat.le_of_dvd (by norm_num) hdv1; omega
          have hne : q1 ≠ q2 := by
            rintro rfl; exact coprime_norms _ hk q1 hq1 hq1_2 hd1 hd2
          rcases two_primes (4 * (2 * f + 1)) q1 q2 (by omega) hq1.two_le hq2.two_le hne hdv1
            hdv2 with h | h
          · exact ⟨q1, hq1, two_pow_dvd_of_orderOf hord1, h⟩
          · exact ⟨q2, hq2, two_pow_dvd_of_orderOf hord2, h⟩
    · obtain ⟨q1, hq1, hord1⟩ := zsigmondy (2 * (2 * e + 1)) (by omega)
      obtain ⟨q2, hq2, hord2⟩ := zsigmondy (2 * e + 1) (by omega)
      haveI := Fact.mk hq1
      haveI := Fact.mk hq2
      have hdv1 := dvd_sub_one_of_orderOf hord1 (by omega)
      have hdv2 := dvd_sub_one_of_orderOf hord2 (by omega)
      have hq2odd : q2 % 2 = 1 := by
        rcases hq2.eq_two_or_odd with h | h
        · subst h; have := Nat.le_of_dvd (by norm_num) hdv2; omega
        · exact h
      have hdv2' : 2 * (2 * e + 1) ∣ q2 - 1 :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.coprime_two_left.2 ⟨e, rfl⟩)
          (Nat.dvd_of_mod_eq_zero (by omega)) hdv2
      have hne : q1 ≠ q2 := by
        rintro rfl; rw [hord1] at hord2; omega
      rcases two_primes (2 * (2 * e + 1)) q1 q2 (by omega) hq1.two_le hq2.two_le hne hdv1
        hdv2' with h | h
      · exact ⟨q1, hq1, two_pow_dvd_of_orderOf hord1, h⟩
      · exact ⟨q2, hq2, two_pow_dvd_of_orderOf_dvd hord2 (Dvd.intro_left 2 rfl), h⟩
  · obtain ⟨q, hq, hord⟩ := zsigmondy (2 * d + 1) (by omega)
    haveI := Fact.mk hq
    have hdv := dvd_sub_one_of_orderOf hord (by omega)
    have hqodd : q % 2 = 1 := by
      rcases hq.eq_two_or_odd with h | h
      · subst h; have := Nat.le_of_dvd (by norm_num) hdv; omega
      · exact h
    have hdv' : 2 * (2 * d + 1) ∣ q - 1 :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.coprime_two_left.2 ⟨d, rfl⟩)
        (Nat.dvd_of_mod_eq_zero (by omega)) hdv
    have := Nat.le_of_dvd (by have := hq.two_le; omega) hdv'
    exact ⟨q, hq, two_pow_dvd_of_orderOf hord, by omega⟩

end OMA977

theorem OMA.solution : type_of% @Erdos977.erdos_977.variants.schinzel := by
  intro n hn
  obtain ⟨q, hq, hdvd, hlt⟩ := OMA977.main n hn
  have h1 : 2 ^ n - 1 ≠ 0 := by
    have := Nat.one_lt_two_pow (n := n) (by omega)
    omega
  exact lt_of_lt_of_le hlt (Nat.le_maxPrimeFac h1 hq hdvd)
