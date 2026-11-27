import OMAReductions.R_Erdos458_erdos_458_R1

-- Step Erdos458.erdos_458.R1.H1
-- Credit: @caa1982

open Finset ArithmeticFunction

private lemma lcm_upto_pos (n : ℕ) : 0 < Erdos458.lcm_upto n := by
  unfold Erdos458.lcm_upto
  rw [Nat.pos_iff_ne_zero]
  intro h
  have := Finset.lcm_eq_zero_iff.mp h
  rcases this with ⟨k, hk, hk0⟩
  simp only [Finset.mem_Icc, id_eq] at hk hk0
  omega

private lemma lcm_upto_succ (n : ℕ) :
    Erdos458.lcm_upto (n + 1) = Nat.lcm (Erdos458.lcm_upto n) (n + 1) := by
  unfold Erdos458.lcm_upto
  have hset : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hset, Finset.lcm_insert, Nat.lcm_comm]
  rfl

private lemma factorization_lcm_upto_le (n p : ℕ) (hp : p.Prime) :
    ∀ r : ℕ, (Erdos458.lcm_upto n).factorization p ≤ r ↔ ∀ k ∈ Finset.Icc 1 n, k.factorization p ≤ r := by
  intro r
  induction n with
  | zero =>
    simp [Erdos458.lcm_upto]
  | succ n ih =>
    rw [lcm_upto_succ]
    have hL : Erdos458.lcm_upto n ≠ 0 := (lcm_upto_pos n).ne'
    have hfac : (Nat.lcm (Erdos458.lcm_upto n) (n + 1)).factorization p =
        max ((Erdos458.lcm_upto n).factorization p) ((n + 1).factorization p) := by
      have := Nat.factorization_lcm hL (Nat.succ_ne_zero n)
      exact congr_arg (fun f => f p) this
    rw [hfac, max_le_iff, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      simp only [Finset.mem_Icc] at hk
      rcases Nat.lt_or_eq_of_le hk.2 with hlt | rfl
      · exact h1 k (Finset.mem_Icc.mpr ⟨hk.1, Nat.lt_succ_iff.mp hlt⟩)
      · exact h2
    · intro h
      exact ⟨fun k hk => h k (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1, by
          have := (Finset.mem_Icc.mp hk).2; omega⟩),
        h (n + 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)⟩

private lemma lcm_upto_prime_pow (n p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r) (heq : n + 1 = p ^ r) :
    Erdos458.lcm_upto (n + 1) = p * Erdos458.lcm_upto n := by
  rw [lcm_upto_succ, heq]
  have hL : Erdos458.lcm_upto n ≠ 0 := (lcm_upto_pos n).ne'
  have hpr : p ^ r ≠ 0 := pow_ne_zero r hp.ne_zero
  apply Nat.eq_of_factorization_eq (Nat.lcm_ne_zero hL hpr) (mul_ne_zero hp.ne_zero hL)
  intro q
  have hlcm : (Nat.lcm (Erdos458.lcm_upto n) (p ^ r)).factorization q =
      max ((Erdos458.lcm_upto n).factorization q) ((p ^ r).factorization q) :=
    congr_arg (fun f => f q) (Nat.factorization_lcm hL hpr)
  rw [hlcm, Nat.factorization_mul hp.ne_zero hL, Finsupp.add_apply,
    Nat.Prime.factorization_pow hp, Finsupp.single_apply, hp.factorization, Finsupp.single_apply]
  by_cases hqp : p = q
  · subst hqp
    simp only [↓reduceIte]
    have hle : (Erdos458.lcm_upto n).factorization p ≤ r - 1 := by
      rw [factorization_lcm_upto_le n p hp]
      intro k hk
      simp only [Finset.mem_Icc] at hk
      by_contra hgt
      push Not at hgt
      have hge : r ≤ k.factorization p := by omega
      have hdvd : p ^ r ∣ k := (hp.pow_dvd_iff_le_factorization (by omega)).mpr hge
      have hkle : p ^ r ≤ k := Nat.le_of_dvd (by omega) hdvd
      omega
    have hge : r - 1 ≤ (Erdos458.lcm_upto n).factorization p := by
      have hmem : p ^ (r - 1) ∈ Finset.Icc 1 n := by
        rw [Finset.mem_Icc]
        have hlt : p ^ (r - 1) < p ^ r := Nat.pow_lt_pow_right hp.one_lt (by omega)
        exact ⟨Nat.one_le_pow _ _ hp.pos, by omega⟩
      have hdvd : p ^ (r - 1) ∣ Erdos458.lcm_upto n := by
        unfold Erdos458.lcm_upto
        exact Finset.dvd_lcm hmem
      exact (hp.pow_dvd_iff_le_factorization hL).mp hdvd
    have hval : (Erdos458.lcm_upto n).factorization p = r - 1 := by omega
    rw [hval]
    omega
  · simp [hqp]

private lemma lcm_upto_not_prime_pow (n : ℕ) (hnp : ¬ IsPrimePow (n + 1)) :
    Erdos458.lcm_upto (n + 1) = Erdos458.lcm_upto n := by
  rw [lcm_upto_succ]
  apply Nat.lcm_eq_left
  rw [← Nat.factorization_le_iff_dvd (Nat.succ_ne_zero n) (lcm_upto_pos n).ne']
  intro q
  by_cases hq : q.Prime
  · by_cases hzero : (n + 1).factorization q = 0
    · simp [hzero]
    · set e := (n + 1).factorization q
      have he : 1 ≤ e := Nat.pos_of_ne_zero hzero
      have hdvd : q ^ e ∣ n + 1 := Nat.ordProj_dvd (n + 1) q
      have hle : q ^ e ≤ n + 1 := Nat.le_of_dvd (Nat.succ_pos n) hdvd
      have hne : q ^ e ≠ n + 1 := by
        intro heq
        exact hnp (heq ▸ hq.isPrimePow.pow (by omega))
      have hmem : q ^ e ∈ Finset.Icc 1 n :=
        Finset.mem_Icc.mpr ⟨Nat.one_le_pow _ _ hq.pos, by omega⟩
      have hdvdL : q ^ e ∣ Erdos458.lcm_upto n := by
        unfold Erdos458.lcm_upto
        exact Finset.dvd_lcm hmem
      exact (hq.pow_dvd_iff_le_factorization (lcm_upto_pos n).ne').mp hdvdL
  · rw [Nat.factorization_eq_zero_of_not_prime (n + 1) hq]
    exact Nat.zero_le _

private lemma log_lcm_upto (n : ℕ) :
    Real.log (Erdos458.lcm_upto n : ℝ) = ∑ k ∈ Finset.Icc 1 n, vonMangoldt k := by
  induction n with
  | zero =>
    simp [Erdos458.lcm_upto]
  | succ n ih =>
    have hset : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnotmem : n + 1 ∉ Finset.Icc 1 n := by simp
    rw [hset, Finset.sum_insert hnotmem, ← ih]
    by_cases hpp : IsPrimePow (n + 1)
    · rw [isPrimePow_nat_iff] at hpp
      obtain ⟨p, r, hp, hr, heq⟩ := hpp
      rw [lcm_upto_prime_pow n p r hp hr heq.symm, Nat.cast_mul,
        Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast (lcm_upto_pos n).ne')]
      rw [← heq, vonMangoldt_apply_pow (by omega : r ≠ 0), vonMangoldt_apply_prime hp]
    · rw [lcm_upto_not_prime_pow n hpp, vonMangoldt_eq_zero_iff.mpr hpp, zero_add]

theorem OMA.solution : OMA.R_Erdos458_erdos_458_R1.H1 := by
  intro a b hab
  rw [log_lcm_upto b, log_lcm_upto a]
  have hunion : Finset.Icc 1 a ∪ Finset.Ioc a b = Finset.Icc 1 b := by
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 a) (Finset.Ioc a b) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hx1 hx2
    omega
  rw [← hunion, Finset.sum_union hdisj]
  ring
