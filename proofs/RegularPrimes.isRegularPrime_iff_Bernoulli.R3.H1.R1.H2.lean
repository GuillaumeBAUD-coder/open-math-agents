import OMAReductions.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H1_R1

/-!
# Kummer congruence for the power-sum representative of `B_k / k`

For a prime `p` and an even integer `2 ≤ k ≤ p - 3`, let `m = 1 + p * (k - 1)` and
`S n = ∑ a ∈ Ico 1 p, a ^ n`.
1. Pick a primitive root `c mod p`, so `c ^ k ≠ 1` in `ZMod p`; this forces `p ∣ S k` and `p ∣ S m`.
2. Writing `c * a = (c * a) % p + p * ((c * a) / p)` and raising to the `n`-th power modulo `p ^ 2`
   gives the Voronoi congruence `(c ^ n - 1) * (S n / p) ≡ n * ∑ r_a ^ (n - 1) * q_a (mod p)`.
   Comparing `n = m` (where `m ≡ 1 (mod p)` and `r_a ^ (m - 1) ≡ r_a ^ (k - 1) (mod p)`) with `n = k`
   and cancelling `c ^ k - 1 ≠ 0` yields `k * (S m / p) ≡ S k / p (mod p)`.
3. Faulhaber's formula (`sum_range_pow`) together with von Staudt–Clausen (`denominator_coprime`)
   gives `S k / p ≡ B_k (mod p)`, completing the proof.
-/

section KummerPowerSumH2

private lemma zmod_sq_pow_add_mul (p : ℕ) (r q : ZMod (p ^ 2)) : ∀ n : ℕ, 1 ≤ n →
    (r + (p : ZMod (p ^ 2)) * q) ^ n =
      r ^ n + (n : ZMod (p ^ 2)) * r ^ (n - 1) * ((p : ZMod (p ^ 2)) * q) := by
  have hp2 : ((p : ZMod (p ^ 2)) ^ 2) = 0 := by
    rw [← Nat.cast_pow]
    exact ZMod.natCast_self (p ^ 2)
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · simp
    · rw [pow_succ (r + (p : ZMod (p ^ 2)) * q) n, pow_succ r n, ih hn', Nat.add_sub_cancel]
      have hr : r ^ (n - 1) * r = r ^ n := by
        rw [← pow_succ r (n - 1), Nat.sub_add_cancel hn']
      push_cast
      linear_combination (n : ZMod (p ^ 2)) * r ^ (n - 1) * q ^ 2 * hp2 +
        (n : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) * q * hr

private lemma zmod_eq_of_mul_eq_zmod_sq {p A B : ℕ} (hp : 0 < p)
    (h : ((p * A : ℕ) : ZMod (p ^ 2)) = ((p * B : ℕ) : ZMod (p ^ 2))) :
    (A : ZMod p) = (B : ZMod p) := by
  have hz : (((p * B : ℕ) : ℤ) : ZMod (p ^ 2)) = (((p * A : ℕ) : ℤ) : ZMod (p ^ 2)) := by
    simpa using h.symm
  have hd : ((p ^ 2 : ℕ) : ℤ) ∣ ((p * A : ℕ) : ℤ) - ((p * B : ℕ) : ℤ) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hz
  have hd' : (p : ℤ) * (p : ℤ) ∣ (p : ℤ) * ((A : ℤ) - (B : ℤ)) := by
    convert hd using 1 <;> push_cast <;> ring
  have hdp : (p : ℤ) ∣ (A : ℤ) - (B : ℤ) :=
    (mul_dvd_mul_iff_left (by exact_mod_cast hp.ne' : (p : ℤ) ≠ 0)).mp hd'
  have hz' : ((B : ℤ) : ZMod p) = ((A : ℤ) : ZMod p) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (B : ℤ) (A : ℤ) p).mpr hdp
  simpa using hz'.symm

private lemma bernoulli_den_coprime_prime (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (j : ℕ) (hj : j ≤ p - 3) : p.Coprime (bernoulli j).den := by
  have hp : p.Prime := Fact.out
  rcases eq_or_ne j 0 with rfl | hj0
  · have hden : (bernoulli 0).den = 1 := by rw [bernoulli_zero]; simp
    rw [hden]
    exact Nat.coprime_one_right p
  rcases eq_or_ne j 1 with rfl | hj1
  · have hden : (bernoulli 1).den = 2 := by
      rw [bernoulli_one, show (-1 / 2 : ℚ) = -(1 / 2 : ℚ) by ring]
      norm_num [one_div, Rat.inv_ofNat_den]
    rw [hden]
    exact (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
  rcases Nat.even_or_odd j with he | ho
  · rw [bernoulli_eq_bernoulli'_of_ne_one hj1]
    have hndvd := OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3.denominator_coprime
      p j (Finset.mem_Icc.mpr ⟨by omega, hj⟩) he
    exact hp.coprime_iff_not_dvd.mpr hndvd
  · have hden : (bernoulli j).den = 1 := by
      rw [bernoulli_eq_zero_of_odd ho (by omega)]
      rfl
    rw [hden]
    exact Nat.coprime_one_right p

private lemma sum_Ico_pow_dvd_prime (p : ℕ) [Fact p.Prime] {c n : ℕ}
    (hc1 : 1 ≤ c) (hcp : c < p) (hn : 1 ≤ n) (hcn : (c : ZMod p) ^ n ≠ 1) :
    p ∣ ∑ a ∈ Finset.Ico 1 p, a ^ n := by
  have hp : p.Prime := Fact.out
  have hc0 : (c : ZMod p) ≠ 0 := by
    intro h
    exact Nat.not_dvd_of_pos_of_lt (by omega) hcp ((ZMod.natCast_eq_zero_iff c p).mp h)
  have hsum_eq : ((∑ a ∈ Finset.Ico 1 p, a ^ n : ℕ) : ZMod p) = ∑ x : ZMod p, x ^ n := by
    simp only [Nat.cast_sum, Nat.cast_pow]
    have hrange : ∑ a ∈ Finset.range p, (a : ZMod p) ^ n = ∑ a ∈ Finset.Ico 1 p, (a : ZMod p) ^ n := by
      rw [Finset.sum_range_eq_add_Ico _ hp.pos, Nat.cast_zero, zero_pow (by omega), zero_add]
    rw [← hrange]
    refine Finset.sum_bij (fun a _ => (a : ZMod p)) ?_ ?_ ?_ ?_
    · intro a _; exact Finset.mem_univ _
    · intro a ha b hb hab
      have hval := congrArg ZMod.val hab
      rwa [ZMod.val_natCast_of_lt (Finset.mem_range.mp ha),
        ZMod.val_natCast_of_lt (Finset.mem_range.mp hb)] at hval
    · intro x _
      exact ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
    · intro _ _; rfl
  have hmul : (c : ZMod p) ^ n * ∑ x : ZMod p, x ^ n = ∑ x : ZMod p, x ^ n := by
    rw [Finset.mul_sum]
    have hpow : ∀ x : ZMod p, (c : ZMod p) ^ n * x ^ n = ((c : ZMod p) * x) ^ n :=
      fun x => (mul_pow _ _ _).symm
    simp_rw [hpow]
    exact Equiv.sum_comp (Equiv.mulLeft₀ (c : ZMod p) hc0) (fun x : ZMod p => x ^ n)
  have hzero : ∑ x : ZMod p, x ^ n = 0 := by
    have hsub : ((c : ZMod p) ^ n - 1) * ∑ x : ZMod p, x ^ n = 0 := by
      linear_combination hmul
    exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hcn)
  exact (ZMod.natCast_eq_zero_iff _ p).mp (hsum_eq.trans hzero)

private lemma voronoi_congruence (p : ℕ) [Fact p.Prime] {c n : ℕ}
    (hc1 : 1 ≤ c) (hcp : c < p) (hn : 1 ≤ n)
    (hdiv : p ∣ ∑ a ∈ Finset.Ico 1 p, a ^ n) :
    ((c : ZMod p) ^ n - 1) * (((∑ a ∈ Finset.Ico 1 p, a ^ n) / p : ℕ) : ZMod p) =
      (n : ZMod p) * ∑ a ∈ Finset.Ico 1 p,
        (((c * a) % p : ℕ) : ZMod p) ^ (n - 1) * (((c * a) / p : ℕ) : ZMod p) := by
  have hp : p.Prime := Fact.out
  have hc0 : (c : ZMod p) ≠ 0 := by
    intro h
    exact Nat.not_dvd_of_pos_of_lt (by omega) hcp ((ZMod.natCast_eq_zero_iff c p).mp h)
  let S : ℕ := ∑ a ∈ Finset.Ico 1 p, a ^ n
  let r : ℕ → ℕ := fun a => (c * a) % p
  let q : ℕ → ℕ := fun a => (c * a) / p
  have hperm : ∑ a ∈ Finset.Ico 1 p, (r a) ^ n = S := by
    refine Finset.sum_bij (fun a _ => r a) ?_ ?_ ?_ ?_
    · intro a ha
      obtain ⟨ha1, hap⟩ := Finset.mem_Ico.mp ha
      refine Finset.mem_Ico.mpr ⟨?_, Nat.mod_lt _ hp.pos⟩
      by_contra h0
      dsimp only [r] at h0
      have hmod : (c * a) % p = 0 := by omega
      have hd : p ∣ c * a := Nat.dvd_of_mod_eq_zero hmod
      rcases hp.dvd_mul.mp hd with hdc | hda
      · exact Nat.not_dvd_of_pos_of_lt (by omega) hcp hdc
      · exact Nat.not_dvd_of_pos_of_lt (by omega) hap hda
    · intro a ha b hb hab
      obtain ⟨_, hap⟩ := Finset.mem_Ico.mp ha
      obtain ⟨_, hbp⟩ := Finset.mem_Ico.mp hb
      have hmod : ((c * a : ℕ) : ZMod p) = ((c * b : ℕ) : ZMod p) :=
        (ZMod.natCast_eq_natCast_iff (c * a) (c * b) p).mpr hab
      push_cast at hmod
      have heq : (a : ZMod p) = (b : ZMod p) := mul_left_cancel₀ hc0 hmod
      have hval := congrArg ZMod.val heq
      rwa [ZMod.val_natCast_of_lt hap, ZMod.val_natCast_of_lt hbp] at hval
    · intro y hy
      obtain ⟨hy1, hyp⟩ := Finset.mem_Ico.mp hy
      let a : ℕ := ((c : ZMod p)⁻¹ * (y : ZMod p)).val
      have ha_lt : a < p := ZMod.val_lt _
      have ha_cast : (a : ZMod p) = (c : ZMod p)⁻¹ * (y : ZMod p) := ZMod.natCast_zmod_val _
      have hy0 : (y : ZMod p) ≠ 0 := by
        intro h
        exact Nat.not_dvd_of_pos_of_lt (by omega) hyp ((ZMod.natCast_eq_zero_iff y p).mp h)
      have ha0 : (a : ZMod p) ≠ 0 := by
        rw [ha_cast]
        exact mul_ne_zero (inv_ne_zero hc0) hy0
      have ha1 : 1 ≤ a := by
        by_contra h
        have ha0' : a = 0 := by omega
        rw [ha0', Nat.cast_zero] at ha0
        exact ha0 rfl
      refine ⟨a, Finset.mem_Ico.mpr ⟨ha1, ha_lt⟩, ?_⟩
      have hca : ((c * a : ℕ) : ZMod p) = (y : ZMod p) := by
        push_cast
        rw [ha_cast, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
      have hmod : c * a ≡ y [MOD p] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hca
      change (c * a) % p = y
      rw [Nat.ModEq] at hmod
      rw [hmod, Nat.mod_eq_of_lt hyp]
    · intro _ _; rfl
  have hsq : ((c ^ n * S : ℕ) : ZMod (p ^ 2)) =
      ((S : ℕ) : ZMod (p ^ 2)) +
        ((p * (n * ∑ a ∈ Finset.Ico 1 p, (r a) ^ (n - 1) * q a) : ℕ) : ZMod (p ^ 2)) := by
    have hcs : c ^ n * S = ∑ a ∈ Finset.Ico 1 p, (c * a) ^ n := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => (mul_pow c a n).symm
    rw [hcs, Nat.cast_sum]
    have hterm : ∀ a ∈ Finset.Ico 1 p,
        (((c * a) ^ n : ℕ) : ZMod (p ^ 2)) =
          ((r a : ZMod (p ^ 2)) ^ n) +
            (p : ZMod (p ^ 2)) *
              ((n : ZMod (p ^ 2)) * (r a : ZMod (p ^ 2)) ^ (n - 1) * (q a : ZMod (p ^ 2))) := by
      intro a _
      have hdivmod : c * a = r a + p * q a := by
        dsimp only [r, q]
        rw [add_comm]
        exact (Nat.div_add_mod (c * a) p).symm
      rw [hdivmod, Nat.cast_pow, Nat.cast_add, Nat.cast_mul, zmod_sq_pow_add_mul p _ _ n hn]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    congr 1
    · rw [← hperm, Nat.cast_sum]
      exact Finset.sum_congr rfl fun a _ => by push_cast; rfl
    · simp only [Nat.cast_mul, Nat.cast_sum, Nat.cast_pow, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring
  have hc1_le : 1 ≤ c ^ n := Nat.one_le_pow n c (by omega)
  have hmul_eq : ((p * ((c ^ n - 1) * (S / p)) : ℕ) : ZMod (p ^ 2)) =
      ((p * (n * ∑ a ∈ Finset.Ico 1 p, (r a) ^ (n - 1) * q a) : ℕ) : ZMod (p ^ 2)) := by
    have hS : p * (S / p) = S := Nat.mul_div_cancel' hdiv
    have hsub : ((p * ((c ^ n - 1) * (S / p)) : ℕ) : ZMod (p ^ 2)) + ((S : ℕ) : ZMod (p ^ 2)) =
        ((c ^ n * S : ℕ) : ZMod (p ^ 2)) := by
      rw [← Nat.cast_add]
      congr 1
      calc
        p * ((c ^ n - 1) * (S / p)) + S = (c ^ n - 1) * (p * (S / p)) + S := by ring
        _ = (c ^ n - 1) * S + S := by rw [hS]
        _ = (c ^ n - 1 + 1) * S := by ring
        _ = c ^ n * S := by rw [Nat.sub_add_cancel hc1_le]
    linear_combination hsub + hsq
  have hmodp := zmod_eq_of_mul_eq_zmod_sq hp.pos hmul_eq
  rw [Nat.cast_mul, Nat.cast_sub hc1_le, Nat.cast_pow, Nat.cast_one] at hmodp
  rw [hmodp]
  push_cast
  rfl

private lemma faulhaber_mod_p (p : ℕ) [Fact p.Prime] (k : ℕ) (hk2 : 2 ≤ k) (hkp : k ≤ p - 3)
    (hdiv : p ∣ ∑ a ∈ Finset.Ico 1 p, a ^ k) :
    (((∑ a ∈ Finset.Ico 1 p, a ^ k) / p : ℕ) : ZMod p) * ((bernoulli k).den : ZMod p) =
      ((bernoulli k).num : ZMod p) := by
  have hp : p.Prime := Fact.out
  have hp5 : 5 ≤ p := by omega
  let S : ℕ := ∑ a ∈ Finset.Ico 1 p, a ^ k
  let Q : ℕ := S / p
  have hcastS : (S : ℚ) = ∑ a ∈ Finset.range p, (a : ℚ) ^ k := by
    rw [Finset.sum_range_eq_add_Ico _ hp.pos, Nat.cast_zero, zero_pow (by omega), zero_add]
    simp [S]
  let R : ℚ := ∑ j ∈ Finset.range k, bernoulli j * ((k + 1).choose j : ℚ) * (p : ℚ) ^ (k - 1 - j)
  have hfaul : ((k + 1 : ℕ) : ℚ) * (Q : ℚ) - ((k + 1 : ℕ) : ℚ) * bernoulli k =
      (p : ℚ) * R := by
    have hSp : (S : ℚ) = (p : ℚ) * (Q : ℚ) := by
      exact_mod_cast (Nat.mul_div_cancel' hdiv).symm
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hk1q : (k : ℚ) + 1 ≠ 0 := by positivity
    have h1 : (S : ℚ) * ((k + 1 : ℕ) : ℚ) =
        (∑ j ∈ Finset.range k, bernoulli j * ((k + 1).choose j : ℚ) * (p : ℚ) ^ (k + 1 - j)) +
          bernoulli k * ((k + 1).choose k : ℚ) * (p : ℚ) ^ (k + 1 - k) := by
      rw [hcastS, sum_range_pow, show ((k + 1 : ℕ) : ℚ) = (k : ℚ) + 1 by push_cast; rfl,
        Finset.sum_mul]
      rw [Finset.sum_congr rfl fun i _ => div_mul_cancel₀ _ hk1q, Finset.sum_range_succ]
    have h2 : ∑ j ∈ Finset.range k, bernoulli j * ((k + 1).choose j : ℚ) * (p : ℚ) ^ (k + 1 - j) =
        (p : ℚ) * (p : ℚ) * R := by
      dsimp only [R]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjk := Finset.mem_range.mp hj
      rw [show k + 1 - j = (k - 1 - j) + 1 + 1 by omega, pow_succ, pow_succ]
      ring
    have h3 : bernoulli k * ((k + 1).choose k : ℚ) * (p : ℚ) ^ (k + 1 - k) =
        ((k + 1 : ℕ) : ℚ) * bernoulli k * (p : ℚ) := by
      rw [Nat.choose_succ_self_right, show k + 1 - k = 1 by omega, pow_one]
      ring
    rw [hSp, h2, h3] at h1
    apply mul_left_cancel₀ hpq
    linear_combination h1
  have hR_cop : p.Coprime R.den := by
    apply Nat.Coprime.of_dvd_right (Finset.Rat.den_sum_dvd_prod_den _ _)
    refine Nat.Coprime.prod_right fun j hj => ?_
    have hjk := Finset.mem_range.mp hj
    have hbj : p.Coprime (bernoulli j).den := bernoulli_den_coprime_prime p hp5 j (by omega)
    have hmul1 : p.Coprime (bernoulli j * ((k + 1).choose j : ℚ)).den :=
      hbj.of_dvd_right (by simpa using Rat.mul_den_dvd (bernoulli j) ((k + 1).choose j : ℚ))
    have hmul2 : p.Coprime
        (bernoulli j * ((k + 1).choose j : ℚ) * ((p ^ (k - 1 - j) : ℕ) : ℚ)).den :=
      hmul1.of_dvd_right (by simpa using Rat.mul_den_dvd (bernoulli j * ((k + 1).choose j : ℚ)) ((p ^ (k - 1 - j) : ℕ) : ℚ))
    simpa [Nat.cast_pow] using hmul2
  have hBden : ((bernoulli k).den : ℚ) ≠ 0 := by exact_mod_cast (bernoulli k).den_nz
  have hRden : (R.den : ℚ) ≠ 0 := by exact_mod_cast R.den_nz
  have hintQ :
      ((((k + 1 : ℕ) : ℤ) * ((Q : ℤ) * ((bernoulli k).den : ℤ) - (bernoulli k).num) *
        (R.den : ℤ) : ℤ) : ℚ) =
      (((p : ℤ) * R.num * ((bernoulli k).den : ℤ) : ℤ) : ℚ) := by
    have h1 := congrArg (fun x : ℚ => x * ((bernoulli k).den : ℚ) * (R.den : ℚ)) hfaul
    have hBq : bernoulli k * ((bernoulli k).den : ℚ) = ((bernoulli k).num : ℚ) := by
      conv_lhs => arg 1; rw [← Rat.num_div_den (bernoulli k)]
      exact div_mul_cancel₀ _ hBden
    have hRq : R * (R.den : ℚ) = (R.num : ℚ) := by
      conv_lhs => arg 1; rw [← Rat.num_div_den R]
      exact div_mul_cancel₀ _ hRden
    push_cast at h1 ⊢
    linear_combination h1 + ((k + 1 : ℚ) * (R.den : ℚ)) * hBq +
      (p : ℚ) * ((bernoulli k).den : ℚ) * hRq
  have hint :
      ((k + 1 : ℕ) : ℤ) * ((Q : ℤ) * ((bernoulli k).den : ℤ) - (bernoulli k).num) *
        (R.den : ℤ) =
      (p : ℤ) * R.num * ((bernoulli k).den : ℤ) :=
    Int.cast_injective hintQ
  have hz := congrArg (fun z : ℤ => (z : ZMod p)) hint
  push_cast at hz
  rw [ZMod.natCast_self, zero_mul, zero_mul] at hz
  have hRden_ne : (R.den : ZMod p) ≠ 0 := by
    intro h
    exact (hp.coprime_iff_not_dvd.mp hR_cop) ((ZMod.natCast_eq_zero_iff R.den p).mp h)
  have hk1_ne : ((k + 1 : ℕ) : ZMod p) ≠ 0 := by
    intro h
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
      ((ZMod.natCast_eq_zero_iff (k + 1) p).mp h)
  have hk1_ne' : ((k : ZMod p) + 1) ≠ 0 := by simpa using hk1_ne
  have hzero1 : ((k : ZMod p) + 1) *
      ((Q : ZMod p) * ((bernoulli k).den : ZMod p) - ((bernoulli k).num : ZMod p)) = 0 :=
    (mul_eq_zero.mp hz).resolve_right hRden_ne
  have hzero2 : (Q : ZMod p) * ((bernoulli k).den : ZMod p) -
      ((bernoulli k).num : ZMod p) = 0 :=
    (mul_eq_zero.mp hzero1).resolve_left hk1_ne'
  exact sub_eq_zero.mp hzero2

end KummerPowerSumH2

theorem OMA.solution : OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H1_R1.H2 := by
  intro p hp k hk2 hkp hkeven
  have hp_prime : p.Prime := hp.out
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime hp_prime]
  let c : ℕ := ((g : ZMod p)).val
  have hc_lt : c < p := ZMod.val_lt _
  have hc_cast : (c : ZMod p) = (g : ZMod p) := ZMod.natCast_zmod_val _
  have hc0 : (c : ZMod p) ≠ 0 := by
    rw [hc_cast]
    exact g.ne_zero
  have hc1 : 1 ≤ c := by
    by_contra h
    have hc_eq : c = 0 := by omega
    rw [hc_eq, Nat.cast_zero] at hc0
    exact hc0 rfl
  have hck : (c : ZMod p) ^ k ≠ 1 := by
    intro h
    have hgk : g ^ k = 1 := by
      apply Units.ext
      simpa [hc_cast] using h
    have hdvd : p - 1 ∣ k := hord ▸ orderOf_dvd_of_pow_eq_one hgk
    have hle : p - 1 ≤ k := Nat.le_of_dvd (by omega) hdvd
    omega
  let m : ℕ := 1 + p * (k - 1)
  have hm_eq : m = k + (p - 1) * (k - 1) := by
    dsimp only [m]
    zify [show 1 ≤ k by omega, show 1 ≤ p by omega]
    ring
  have hcm : (c : ZMod p) ^ m = (c : ZMod p) ^ k := by
    rw [hm_eq, pow_add, pow_mul, ZMod.pow_card_sub_one_eq_one hc0, one_pow, mul_one]
  have hcm_ne : (c : ZMod p) ^ m ≠ 1 := hcm.symm ▸ hck
  have hdiv_k : p ∣ ∑ a ∈ Finset.Ico 1 p, a ^ k :=
    sum_Ico_pow_dvd_prime p hc1 hc_lt (by omega) hck
  have hdiv_m : p ∣ ∑ a ∈ Finset.Ico 1 p, a ^ m :=
    sum_Ico_pow_dvd_prime p hc1 hc_lt (by omega) hcm_ne
  have hvm := voronoi_congruence p hc1 hc_lt (by omega) hdiv_m
  have hvk := voronoi_congruence p hc1 hc_lt (by omega) hdiv_k
  have hm_cast : (m : ZMod p) = 1 := by
    dsimp only [m]
    push_cast
    rw [ZMod.natCast_self, zero_mul, add_zero]
  have hsum_eq :
      ∑ a ∈ Finset.Ico 1 p,
        (((c * a) % p : ℕ) : ZMod p) ^ (m - 1) * (((c * a) / p : ℕ) : ZMod p) =
      ∑ a ∈ Finset.Ico 1 p,
        (((c * a) % p : ℕ) : ZMod p) ^ (k - 1) * (((c * a) / p : ℕ) : ZMod p) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    have hm1 : m - 1 = p * (k - 1) := by dsimp only [m]; omega
    rw [hm1, pow_mul, ZMod.pow_card]
  rw [hcm, hm_cast, one_mul, hsum_eq] at hvm
  have hcomp :
      ((c : ZMod p) ^ k - 1) *
        ((((∑ a ∈ Finset.Ico 1 p, a ^ m) / p : ℕ) : ZMod p) * (k : ZMod p) -
          (((∑ a ∈ Finset.Ico 1 p, a ^ k) / p : ℕ) : ZMod p)) = 0 := by
    linear_combination (k : ZMod p) * hvm - hvk
  have hkm :
      ((((∑ a ∈ Finset.Ico 1 p, a ^ m) / p : ℕ) : ZMod p) * (k : ZMod p)) =
        (((∑ a ∈ Finset.Ico 1 p, a ^ k) / p : ℕ) : ZMod p) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hcomp).resolve_left (sub_ne_zero.mpr hck))
  have hfaul := faulhaber_mod_p p k hk2 hkp hdiv_k
  rw [bernoulli_eq_bernoulli'_of_ne_one (by omega)] at hfaul
  calc
    ((((∑ a ∈ Finset.Ico 1 p, a ^ (1 + p * (k - 1))) / p : ℕ) : ZMod p)) *
        (k * (bernoulli' k).den : ZMod p)
      = ((((∑ a ∈ Finset.Ico 1 p, a ^ m) / p : ℕ) : ZMod p) * (k : ZMod p)) *
          ((bernoulli' k).den : ZMod p) := by
          dsimp only [m]
          ring
    _ = (((∑ a ∈ Finset.Ico 1 p, a ^ k) / p : ℕ) : ZMod p) *
          ((bernoulli' k).den : ZMod p) := by rw [hkm]
    _ = ((bernoulli' k).num : ZMod p) := hfaul
