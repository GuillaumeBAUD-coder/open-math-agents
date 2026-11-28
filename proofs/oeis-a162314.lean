import OMAStatements.S_oeis_a162314
import Mathlib

/-!
# Proof of OEIS A162314 Conjecture

Since `a(n) = 2^n * ∑_{j=0..n} (S(n, j) * j!) * (if j = 0 then 1 else 2)`, for `n >= k`
both `2^n` and the inner sum are periodic modulo `k` with period dividing `phi(k)`.
-/

namespace OeisA162314Proof

open Finset

private lemma pow_add_totient_modEq (r : ℕ) :
    ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, k ≤ n → r ^ (n + Nat.totient k) ≡ r ^ n [MOD k] := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk n hn
    by_cases hk1 : k = 1
    · subst hk1; exact Nat.modEq_one
    · set p := k.minFac
      have hp : p.Prime := Nat.minFac_prime (by omega)
      set e := k.factorization p
      have he_pos : 1 ≤ e := by
        have hdvd : p ∣ k := Nat.minFac_dvd k
        have := (Nat.Prime.dvd_iff_one_le_factorization hp (by omega)).mp hdvd
        exact this
      set q := p ^ e
      have hq_dvd : q ∣ k := Nat.ordProj_dvd k p
      set m := k / q
      have hqm : q * m = k := Nat.mul_div_cancel' hq_dvd
      have hcop : Nat.Coprime q m := by
        have hpm : ¬ p ∣ m := by
          intro hpm
          have hpow1 : p ^ (e + 1) ∣ k := by
            rcases hpm with ⟨t, ht⟩
            refine ⟨t, ?_⟩
            calc k = p ^ e * m := hqm.symm
              _ = p ^ e * (p * t) := by rw [ht]
              _ = p ^ (e + 1) * t := by rw [pow_succ]; ring
          have hle := (Nat.Prime.pow_dvd_iff_le_factorization hp (by omega)).mp hpow1
          omega
        exact (hp.coprime_iff_not_dvd.mpr hpm).pow_left e
      have hm_pos : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h0 | hpos
        · rw [h0, mul_zero] at hqm; omega
        · exact hpos
      have hm_lt : m < k := by
        have hq_gt1 : 1 < q := one_lt_pow₀ hp.one_lt (by omega)
        nlinarith
      suffices h : r ^ (n + Nat.totient k) ≡ r ^ n [MOD q * m] by rwa [hqm] at h
      rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop]
      constructor
      · by_cases hpr : p ∣ r
        · have he_le : e ≤ n := by
            have h1 : e < p ^ e := Nat.lt_pow_self hp.one_lt
            have h2 : q ≤ k := Nat.le_of_dvd (by omega) hq_dvd
            omega
          have hd1 : q ∣ r ^ n := by
            rcases hpr with ⟨t, rfl⟩
            rw [mul_pow]
            exact dvd_mul_of_dvd_left (pow_dvd_pow p he_le) _
          have hd2 : q ∣ r ^ (n + Nat.totient k) :=
            dvd_trans hd1 (pow_dvd_pow r (Nat.le_add_right n _))
          rw [Nat.ModEq, Nat.mod_eq_zero_of_dvd hd1, Nat.mod_eq_zero_of_dvd hd2]
        · have hcop_rq : Nat.Coprime r q := (hp.coprime_iff_not_dvd.mpr hpr).symm.pow_right e
          have heuler : r ^ Nat.totient q ≡ 1 [MOD q] := Nat.ModEq.pow_totient hcop_rq
          have htdvd : Nat.totient q ∣ Nat.totient k := Nat.totient_dvd_of_dvd hq_dvd
          rcases htdvd with ⟨t, ht⟩
          have hphi : r ^ Nat.totient k ≡ 1 [MOD q] := by
            rw [ht, pow_mul]
            simpa using heuler.pow t
          rw [pow_add]
          simpa using (Nat.ModEq.refl (r ^ n)).mul hphi
      · have hm_dvd : m ∣ k := ⟨q, by linarith⟩
        have htdvd : Nat.totient m ∣ Nat.totient k := Nat.totient_dvd_of_dvd hm_dvd
        rcases htdvd with ⟨t, ht⟩
        rw [ht]
        have hiter : ∀ s : ℕ, r ^ (n + Nat.totient m * s) ≡ r ^ n [MOD m] := by
          intro s
          induction s with
          | zero => simp [Nat.ModEq]
          | succ s ihs =>
            have hstep : r ^ (n + Nat.totient m * s + Nat.totient m) ≡
                r ^ (n + Nat.totient m * s) [MOD m] :=
              ih m hm_lt hm_pos (n + Nat.totient m * s) (by omega)
            rw [show n + Nat.totient m * (s + 1) = n + Nat.totient m * s + Nat.totient m by ring]
            exact hstep.trans ihs
        exact hiter t

private lemma alt_sum_choose (j : ℕ) :
    ∑ r ∈ Finset.range (j + 2), (-1 : ℤ) ^ (j + 1 - r) * (Nat.choose (j + 1) r : ℤ) = 0 := by
  have h := add_pow (1 : ℤ) (-1 : ℤ) (j + 1)
  simp only [add_neg_cancel, zero_pow (Nat.succ_ne_zero j), one_pow, one_mul] at h
  exact h.symm

private lemma stirling2_mul_fact_eq :
    ∀ n j : ℕ, (OMA.S_oeis_a162314.stirling2 n j * j.factorial : ℤ) =
      ∑ r ∈ Finset.range (j + 1), (-1 : ℤ) ^ (j - r) * (Nat.choose j r : ℤ) * (r : ℤ) ^ n := by
  intro n
  induction n with
  | zero =>
    intro j
    cases j with
    | zero => simp [OMA.S_oeis_a162314.stirling2]
    | succ j =>
      simp only [OMA.S_oeis_a162314.stirling2, zero_mul, Nat.cast_zero, pow_zero, mul_one]
      exact (alt_sum_choose j).symm
  | succ n ih =>
    intro j
    cases j with
    | zero =>
      simp [OMA.S_oeis_a162314.stirling2]
    | succ j =>
      have hrec : (OMA.S_oeis_a162314.stirling2 (n + 1) (j + 1) * (j + 1).factorial : ℤ) =
          (j + 1 : ℤ) * (OMA.S_oeis_a162314.stirling2 n (j + 1) * (j + 1).factorial : ℤ) +
          (j + 1 : ℤ) * (OMA.S_oeis_a162314.stirling2 n j * j.factorial : ℤ) := by
        simp only [OMA.S_oeis_a162314.stirling2, Nat.factorial_succ]
        push_cast
        ring
      rw [hrec, ih (j + 1), ih j]
      rw [Finset.sum_range_succ (fun r => (-1 : ℤ) ^ (j + 1 - r) * (Nat.choose (j + 1) r : ℤ) * (r : ℤ) ^ n)]
      rw [Finset.sum_range_succ (fun r => (-1 : ℤ) ^ (j + 1 - r) * (Nat.choose (j + 1) r : ℤ) * (r : ℤ) ^ (n + 1))]
      simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, one_mul]
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, add_assoc]
      have hlast : (j + 1 : ℤ) * ((j + 1 : ℕ) : ℤ) ^ n = ((j + 1 : ℕ) : ℤ) ^ (n + 1) := by
        push_cast; rw [pow_succ]; ring
      rw [add_comm ((j + 1 : ℤ) * ((j + 1 : ℕ) : ℤ) ^ n), ← add_assoc, hlast]
      congr 1
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      have hrj : r ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      have hsign : (-1 : ℤ) ^ (j + 1 - r) = -((-1 : ℤ) ^ (j - r)) := by
        have : j + 1 - r = (j - r) + 1 := by omega
        rw [this, pow_succ]; ring
      have hpascal : (j + 1 : ℤ) * (Nat.choose (j + 1) r : ℤ) - (j + 1 : ℤ) * (Nat.choose j r : ℤ) =
          (r : ℤ) * (Nat.choose (j + 1) r : ℤ) := by
        cases r with
        | zero => simp
        | succ r' =>
          have h1 : Nat.choose (j + 1) (r' + 1) = Nat.choose j r' + Nat.choose j (r' + 1) :=
            Nat.choose_succ_succ j r'
          have h2 : (r' + 1) * Nat.choose (j + 1) (r' + 1) = (j + 1) * Nat.choose j r' := by
            have := Nat.add_one_mul_choose_eq j r'
            linarith
          have h1Z : (Nat.choose (j + 1) (r' + 1) : ℤ) =
              (Nat.choose j r' : ℤ) + (Nat.choose j (r' + 1) : ℤ) := by exact_mod_cast h1
          have h2Z : ((r' + 1 : ℕ) : ℤ) * (Nat.choose (j + 1) (r' + 1) : ℤ) =
              (j + 1 : ℤ) * (Nat.choose j r' : ℤ) := by exact_mod_cast h2
          linear_combination (j + 1 : ℤ) * h1Z - h2Z
      rw [pow_succ]
      calc (j + 1 : ℤ) * ((-1 : ℤ) ^ (j + 1 - r) * (Nat.choose (j + 1) r : ℤ) * (r : ℤ) ^ n) +
            (j + 1 : ℤ) * ((-1 : ℤ) ^ (j - r) * (Nat.choose j r : ℤ) * (r : ℤ) ^ n)
          = (-1 : ℤ) ^ (j + 1 - r) *
              ((j + 1 : ℤ) * (Nat.choose (j + 1) r : ℤ) - (j + 1 : ℤ) * (Nat.choose j r : ℤ)) *
              (r : ℤ) ^ n := by rw [hsign]; ring
        _ = (-1 : ℤ) ^ (j + 1 - r) * ((r : ℤ) * (Nat.choose (j + 1) r : ℤ)) * (r : ℤ) ^ n := by
              rw [hpascal]
        _ = (-1 : ℤ) ^ (j + 1 - r) * (Nat.choose (j + 1) r : ℤ) * ((r : ℤ) ^ n * (r : ℤ)) := by ring

private lemma genSeq_periodic (g : ℕ → ℤ) (k : ℕ) (hk : 1 ≤ k) :
    ∀ n : ℕ, k ≤ n →
      (∑ j ∈ Finset.range (n + Nat.totient k + 1),
          (OMA.S_oeis_a162314.stirling2 (n + Nat.totient k) j * j.factorial : ℤ) * g j) ≡
      (∑ j ∈ Finset.range (n + 1),
          (OMA.S_oeis_a162314.stirling2 n j * j.factorial : ℤ) * g j) [ZMOD k] := by
  intro n hn
  rw [← ZMod.intCast_eq_intCast_iff]
  have htrunc : ∀ m : ℕ, k ≤ m →
      ((∑ j ∈ Finset.range (m + 1), (OMA.S_oeis_a162314.stirling2 m j * j.factorial : ℤ) * g j : ℤ) : ZMod k) =
      ∑ j ∈ Finset.range k,
        (((OMA.S_oeis_a162314.stirling2 m j * j.factorial : ℤ) * g j : ℤ) : ZMod k) := by
    intro m hm
    push_cast
    have hsplit : Finset.range (m + 1) = Finset.range k ∪ (Finset.range (m + 1) \ Finset.range k) := by
      ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_range]; omega
    rw [hsplit, Finset.sum_union disjoint_sdiff_self_right]
    have htail : ∑ j ∈ Finset.range (m + 1) \ Finset.range k,
        (((OMA.S_oeis_a162314.stirling2 m j : ℤ) * (j.factorial : ℤ) * g j : ℤ) : ZMod k) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Finset.mem_sdiff, Finset.mem_range] at hj
      have h0 : (j.factorial : ZMod k) = 0 :=
        (ZMod.natCast_eq_zero_iff _ k).mpr (Nat.dvd_factorial hk (by omega))
      push_cast
      rw [h0, mul_zero, zero_mul]
    push_cast at htail ⊢
    rw [htail, add_zero]
  rw [htrunc (n + Nat.totient k) (by omega), htrunc n hn]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  congr 1
  have h1 := congrArg (Int.cast (R := ZMod k)) (stirling2_mul_fact_eq (n + Nat.totient k) j)
  have h2 := congrArg (Int.cast (R := ZMod k)) (stirling2_mul_fact_eq n j)
  push_cast at h1 h2
  rw [h1, h2]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  have hr := pow_add_totient_modEq r k hk n hn
  have hrz := (ZMod.natCast_eq_natCast_iff _ _ k).mpr hr
  simpa using hrz


end OeisA162314Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a162314.main := by
  intro k hk
  refine ⟨k, fun n hn => ?_⟩
  unfold OMA.S_oeis_a162314.a
  have hpow := OeisA162314Proof.pow_add_totient_modEq 2 k hk n hn
  have hZ := OeisA162314Proof.genSeq_periodic (fun j => if j = 0 then (1 : ℤ) else 2) k hk n hn
  have hcast : ∀ m : ℕ,
      ((∑ j ∈ Finset.range (m + 1),
          OMA.S_oeis_a162314.stirling2 m j * j.factorial * (if j = 0 then 1 else 2) : ℕ) : ℤ) =
      ∑ j ∈ Finset.range (m + 1),
        (OMA.S_oeis_a162314.stirling2 m j * j.factorial : ℤ) * (if j = 0 then (1 : ℤ) else 2) := by
    intro m
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  rw [← hcast (n + Nat.totient k), ← hcast n] at hZ
  exact hpow.mul (Int.natCast_modEq_iff.mp hZ)
