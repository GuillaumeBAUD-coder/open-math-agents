import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1_H2_R1

/-! Fermat factors in the 19423 branch of Erdős 1052. Write a for the exponent of 2 in n.
The first two cases force high powers of explicit odd primes. In the third case a
prime from the exact Fermat number occurs in the repeated part of n. The modular
sieves exclude whole odd-multiple classes of a in all three cases. -/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1_H2_R1_H1_R1


open OMA.R_Erdos1052_erdos_1052_R1 (sum_udiv_of_isUnitaryPerfect sum_udiv_eq_prod)

lemma odd_multiple_factor {b d m : ℕ} (hd : m % (2 * d) = d) :
    b ^ d + 1 ∣ b ^ m + 1 := by
  have he : m = d * (2 * (m / (2 * d)) + 1) := by
    have hr := Nat.div_add_mod m (2 * d)
    rw [hd] at hr
    linarith
  have hf := Odd.nat_add_dvd_pow_add_pow (b ^ d) 1 (show Odd (2 * (m / (2*d)) + 1) from ⟨_, rfl⟩)
  rwa [one_pow, ← pow_mul, ← he] at hf

/-- Every odd divisor of the unitary sum of one prime power divides the perfect number. -/
lemma component_divisor {n p d : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hp : p.Prime) (hpn : p ∣ n) (hd : d.Coprime 2)
    (h : d ∣ p ^ n.factorization p + 1) : d ∣ n := by
  obtain ⟨hpos, hs⟩ := sum_udiv_of_isUnitaryPerfect hn
  rw [sum_udiv_eq_prod hpos.ne'] at hs
  apply hd.dvd_of_dvd_mul_left
  rw [← hs]
  exact (show d ∣ 1 + p ^ n.factorization p by simpa [add_comm] using h).trans
    (Finset.dvd_prod_of_mem _ (Nat.mem_primeFactors.mpr ⟨hp, hpn, hpos.ne'⟩))

lemma required_divisor {n p d q : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hp : p.Prime) (hpn : p ∣ n) (hq : q.Coprime 2)
    (hqd : q ∣ p ^ d + 1) (he : n.factorization p % (2*d) = d) : q ∣ n :=
  component_divisor hn hp hpn hq (hqd.trans (odd_multiple_factor he))

lemma prime_gap {n q : ℕ} {S : Finset ℕ}
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (hsq : ∀ z ∈ S, 25000 ≤ z)
    (hgap : ∀ q : ℕ, q.Prime → q ∣ n → ¬ q ^ 2 ∣ n → q < 49468 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨
      q = 3967 ∨ q = 7933 ∨ q = 19423)
    (hq : q.Prime) (hlt : q < 25000)
    (hout : q ∉ ([2,3,5,7,19,31,223,607,3967,7933,19423] : List ℕ)) : ¬ q ∣ n := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hout
  intro hqn
  have h2 : q ≠ 2 := by tauto
  have hsingle : ¬ q ^ 2 ∣ n := fun h => (hsq q ((hS q).mpr ⟨hq,h2,h⟩)).not_gt hlt
  exact hout (hgap q hq hqn hsingle (by omega))

lemma excluded_residue {n p q d : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hp : p.Prime) (hpn : p ∣ n) (hq : q.Coprime 2)
    (hqd : q ∣ p ^ d + 1) (hqn : ¬ q ∣ n) : n.factorization p % (2*d) ≠ d :=
  fun he => hqn (required_divisor hn hp hpn hq hqd he)

lemma power_divides {n p k : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hp : p.Prime) (hpn : p ∣ n) (hk : k ∣ n.factorization p) : p ^ k ∣ n := by
  exact Nat.pow_dvd_of_le_of_pow_dvd
    (Nat.le_of_dvd (hp.factorization_pos_of_dvd (sum_udiv_of_isUnitaryPerfect hn).1.ne' hpn) hk)
    (Nat.ordProj_dvd n p)
lemma lift_power_of_two {e d : ℕ} (hd : 0 < d) (h : d ∣ e) (hhalf : e % (2*d) ≠ d) :
    2*d ∣ e := by
  obtain ⟨u, hu⟩ := h
  rcases Nat.even_or_odd u with ⟨v, hv⟩ | ⟨v, hv⟩
  · exact ⟨v, by rw [hu, hv]; ring⟩
  · exfalso
    apply hhalf
    have he : e = d + 2*d*v := by rw [hu, hv]; ring
    rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

lemma valuation_four {n : ℕ} (hn : Erdos1052.IsUnitaryPerfect n) (h2 : 2 ∣ n)
    (ha : padicValNat 2 n % 32 = 16)
    (hb : ∀ q ∈ ([11,8681,17,257,1409,641] : List ℕ), ¬ q ∣ n) :
    65537 ^ 16 ∣ n ∧
    (n.factorization 65537 % 32 = 16 ∨ 128 ∣ n.factorization 65537) := by
  have hF : 65537 ∣ n := required_divisor hn Nat.prime_two h2
    (by decide) (d := 16) (by decide) (by rwa [Nat.factorization_def _ Nat.prime_two])
  have block (d q : ℕ) (hmem : q ∈ ([11,8681,17,257,1409,641] : List ℕ))
      (hodd : q.Coprime 2) (hdiv : q ∣ 65537 ^ d + 1) :
      n.factorization 65537 % (2*d) ≠ d := fun h => hb q hmem (required_divisor hn (show Nat.Prime 65537 by norm_num) hF hodd hdiv h)
  have h1 := block 1 11 (by decide) (by decide) (by decide)
  have h2' := block 2 8681 (by decide) (by decide) (by decide)
  have h4 := block 4 17 (by decide) (by decide) (by decide)
  have h8 := block 8 257 (by decide) (by decide) (by decide)
  have h32 := block 32 1409 (by decide) (by decide) (by decide)
  have h64 := block 64 641 (by decide) (by decide) (by decide)
  have hx2 := lift_power_of_two (by decide) (one_dvd _) h1
  have hx4 := lift_power_of_two (by decide) hx2 h2'
  have hx8 := lift_power_of_two (by decide) hx4 h4
  have hx16 := lift_power_of_two (by decide) hx8 h8
  refine ⟨power_divides hn (by norm_num) hF hx16, ?_⟩
  by_cases hm : n.factorization 65537 % 32 = 16
  · exact Or.inl hm
  · have hx32 := lift_power_of_two (by decide) hx16 hm
    have hx64 := lift_power_of_two (by decide) hx32 h32
    exact Or.inr (lift_power_of_two (by decide) hx64 h64)

-- Lucas certificate adapted from @adammcarter, Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.
theorem prime_67280421310721 : Nat.Prime 67280421310721 := by
  refine lucas_primality 67280421310721 (3 : ZMod 67280421310721) ?_ (fun q hq hd => ?_)
  · rw [show 67280421310721 - 1 = 67280421310720 from by norm_num]
    reduce_mod_char
  · have e : 67280421310721 - 1 = [2 ^ 8, 5 ^ 1, 47 ^ 1, 373 ^ 1, 2998279 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67280421310721 - 1) / 2 = 33640210655360 from by norm_num]
      have h2 : (3 : ZMod 67280421310721) ^ 33640210655360 = ((67280421310720 : ℕ) : ZMod 67280421310721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      decide
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67280421310721 - 1) / 5 = 13456084262144 from by norm_num]
      have h2 : (3 : ZMod 67280421310721) ^ 13456084262144 = ((8348471219631 : ℕ) : ZMod 67280421310721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      decide
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67280421310721 - 1) / 47 = 1431498325760 from by norm_num]
      have h2 : (3 : ZMod 67280421310721) ^ 1431498325760 = ((29801263682154 : ℕ) : ZMod 67280421310721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      decide
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67280421310721 - 1) / 373 = 180376464640 from by norm_num]
      have h2 : (3 : ZMod 67280421310721) ^ 180376464640 = ((65541179653181 : ℕ) : ZMod 67280421310721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      decide
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67280421310721 - 1) / 2998279 = 22439680 from by norm_num]
      have h2 : (3 : ZMod 67280421310721) ^ 22439680 = ((61150258807256 : ℕ) : ZMod 67280421310721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      decide

lemma valuation_six {n : ℕ} (hn : Erdos1052.IsUnitaryPerfect n) (h2 : 2 ∣ n)
    (ha : padicValNat 2 n % 128 = 64)
    (hb : ∀ q ∈ ([109,13,17,9337,2617,13709,313] : List ℕ), ¬ q ∣ n) :
    67280421310721 ^ 8 ∣ n ∧ (274177 ^ 8 ∣ n ∨ 137089 ^ 8 ∣ n) := by
  have he : n.factorization 2 % (2 * 64) = 64 := by rwa [Nat.factorization_def _ Nat.prime_two]
  have hlarge : 67280421310721 ∣ n :=
    required_divisor hn Nat.prime_two h2 (by decide) (by decide) he
  have hsmall : 274177 ∣ n := required_divisor hn Nat.prime_two h2 (by decide) (by decide) he
  have hA : Nat.Prime 274177 := by norm_num
  have hB : Nat.Prime 137089 := by norm_num
  have block {p d q : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hodd : q.Coprime 2)
      (hqd : q ∣ p ^ d + 1) (hmem : q ∈ ([109,13,17,9337,2617,13709,313] : List ℕ)) :
      n.factorization p % (2*d) ≠ d := excluded_residue hn hp hpn hodd hqd (hb q hmem)
  constructor
  · apply power_divides hn prime_67280421310721 hlarge
    have h1 := block (d := 1) (q := 109) prime_67280421310721 hlarge (by decide) (by decide) (by decide)
    have h2' := block (d := 2) (q := 13) prime_67280421310721 hlarge (by decide) (by decide) (by decide)
    have h4 := block (d := 4) (q := 17) prime_67280421310721 hlarge (by decide) (by decide) (by decide)
    have hx2 := lift_power_of_two (by decide) (one_dvd _) h1
    have hx4 := lift_power_of_two (by decide) hx2 h2'
    exact lift_power_of_two (by decide) hx4 h4
  · by_cases hodd : n.factorization 274177 % 2 = 1
    · right
      have hmid : 137089 ∣ n := required_divisor hn hA hsmall (by decide) (d := 1) (by decide) hodd
      apply power_divides hn hB hmid
      have h1 := block (d := 1) (q := 13709) hB hmid (by decide) (by decide) (by decide)
      have h2' := block (d := 2) (q := 109) hB hmid (by decide) (by decide) (by decide)
      have h4 := block (d := 4) (q := 313) hB hmid (by decide) (by decide) (by decide)
      have hx2 := lift_power_of_two (by decide) (one_dvd _) h1
      have hx4 := lift_power_of_two (by decide) hx2 h2'
      exact lift_power_of_two (by decide) hx4 h4
    · left
      apply power_divides hn hA hsmall
      have h2' := block (d := 2) (q := 9337) hA hsmall (by decide) (by decide) (by decide)
      have h4 := block (d := 4) (q := 2617) hA hsmall (by decide) (by decide) (by decide)
      have hx2 := lift_power_of_two (by decide) (one_dvd _) hodd
      have hx4 := lift_power_of_two (by decide) hx2 h2'
      exact lift_power_of_two (by decide) hx4 h4

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 (facts exists_prime_mod3)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1.Erdos1052C7 (setup7)

/-- The exact power of two in the exponent selects a Fermat number before the odd cofactor enters.
A prime divisor congruent to 2 modulo 3 must occur among the repeated primes. -/
lemma high_fermat_factor {n : ℕ} {S : Finset ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (hge : ∀ z ∈ S, 25000 ≤ z) (h2 : 2 ∣ n) (h5 : 5 ∣ n)
    (ha : 128 ∣ padicValNat 2 n) (ha0 : padicValNat 2 n ≠ 0) :
    ∃ k t z : ℕ, 7 ≤ k ∧ Odd t ∧ padicValNat 2 n = 2 ^ k * t ∧ z ∈ S ∧
      z % 3 = 2 ∧ z ∣ Nat.fermatNumber k ∧ 2 ^ (k + 2) ∣ z - 1 := by
  obtain ⟨k,t,ht,he⟩ := Nat.exists_eq_two_pow_mul_odd ha0
  have hk : 7 ≤ k := by
    by_contra! hsmall
    obtain ⟨u,hu⟩ := ht
    rw [he, hu] at ha
    interval_cases k <;> norm_num at ha <;> omega
  have hF3 : Nat.fermatNumber k % 3 = 2 := by
    obtain ⟨i,hi⟩ : ∃ i, k = i + 1 := ⟨k-1, by omega⟩
    have hpow : (2 : ℕ) ^ 2 ^ k % 3 = 1 := by
      rw [hi, pow_succ', pow_mul, Nat.pow_mod]
      norm_num
    unfold Nat.fermatNumber
    omega
  obtain ⟨z,hzp,hzF,hz3⟩ := exists_prime_mod3 _ hF3
  obtain ⟨b,hb⟩ := Nat.fermat_primeFactors_one_lt k z (by omega) hzp hzF
  have hpow : 8 ≤ (2:ℕ) ^ (k+2) := le_trans (by decide : 8 ≤ (2:ℕ)^3)
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hzbig : 5 < z := by
    have hb0 : b ≠ 0 := by rintro rfl; simp at hb; exact hzp.ne_one hb
    have hbpos : 1 ≤ b := by omega
    have := Nat.mul_le_mul_right (2^(k+2)) hbpos
    simp only [one_mul] at this
    omega
  have hroot : z ∣ 2 ^ padicValNat 2 n + 1 := by
    have hmul := ht.nat_add_dvd_pow_add_pow ((2:ℕ) ^ 2 ^ k) 1
    rw [one_pow, ← pow_mul, ← he] at hmul
    exact hzF.trans hmul
  obtain ⟨K,K',P,hP,hK,-,-,E,hm⟩ := setup7 hn hS h2
  obtain ⟨-,hrootP,hsingle,-,-,-,-,-⟩ := facts hP hK E
  have hout (p : ℕ) (h : p < 25000) : p ∉ S := fun hs => absurd (hge p hs) (not_le.mpr h)
  have hfive : 5 ∈ P := (hm 5).mpr ⟨by norm_num,by decide,h5,hout 5 (by decide)⟩
  have hzS : z ∈ S := by
    by_contra hno
    have hzp' := hrootP z hzp (by omega) hno hroot
    have heq := hsingle 3 (by decide) (by decide) (hout 3 (by decide)) z hzp' 5 hfive
      (by omega : 3 ∣ z+1) (by decide)
    omega
  exact ⟨k,t,z,hk,ht,he,hzS,hz3,hzF,⟨b, by rw [hb, Nat.add_sub_cancel, mul_comm]⟩⟩

lemma divisor_from_residue {p b d : ℕ} (h : (b : ZMod p) ^ d = -1) :
    p ∣ b ^ d + 1 := by
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  push_cast
  rw [h, neg_add_cancel]

/-- For an odd multiple of b, a forbidden factor of 2^(b*r)+1 excludes every odd
cofactor divisible by r, including arbitrarily large ones. -/
lemma exclude_odd_cofactor {n b r q : ℕ} (hn : Erdos1052.IsUnitaryPerfect n) (h2 : 2 ∣ n)
    (hb : 0 < b) (ha : padicValNat 2 n % (2*b) = b) (hq : q.Coprime 2)
    (hdiv : q ∣ 2 ^ (b*r) + 1) (hqn : ¬ q ∣ n) : ¬ r ∣ padicValNat 2 n / b := by
  let a := padicValNat 2 n
  have he : a = b * (2 * (a / (2*b)) + 1) := by
    have hr := Nat.div_add_mod a (2*b)
    change a % (2*b) = b at ha
    rw [ha] at hr
    linarith
  have hquot : a / b = 2 * (a / (2*b)) + 1 := by
    conv_lhs => rw [he, Nat.mul_div_cancel_left _ hb]
  have hodd : Odd (a / b) := ⟨a / (2*b), hquot⟩
  intro hr
  change r ∣ a / b at hr
  obtain ⟨u,hu⟩ := hr
  have huodd : Odd u := (Nat.odd_mul.mp (hu ▸ hodd)).2
  have hfull : a = (b*r)*u := by calc
    a = b * (a / b) := he.trans (congrArg (b * ·) hquot.symm)
    _ = (b*r)*u := by rw [hu, Nat.mul_assoc]
  have hm := huodd.nat_add_dvd_pow_add_pow ((2:ℕ)^(b*r)) 1
  rw [one_pow, ← pow_mul, ← hfull] at hm
  exact hqn (component_divisor hn Nat.prime_two h2 hq (by
    rw [Nat.factorization_def _ Nat.prime_two]
    exact hdiv.trans hm))

lemma odd_part_16 {n : ℕ} (hn : Erdos1052.IsUnitaryPerfect n) (h2 : 2 ∣ n)
    (ha : padicValNat 2 n % 32 = 16)
    (hb : ∀ q ∈ ([193,449,5441,5953,7873,2753] : List ℕ), ¬ q ∣ n) :
    ∀ d ∈ ([3,7,17,31,41,43] : List ℕ), ¬ d ∣ padicValNat 2 n / 16 := by
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  · exact exclude_odd_cofactor hn h2 (by decide : 0 < 16) ha (q := 193)
      (by decide) (divisor_from_residue (by reduce_mod_char)) (hb 193 (by decide))
  · exact exclude_odd_cofactor hn h2 (by decide : 0 < 16) ha (q := 449)
      (by decide) (divisor_from_residue (by reduce_mod_char)) (hb 449 (by decide))
  · exact exclude_odd_cofactor hn h2 (by decide : 0 < 16) ha (q := 5441)
      (by decide) (divisor_from_residue (by reduce_mod_char)) (hb 5441 (by decide))
  · exact exclude_odd_cofactor hn h2 (by decide : 0 < 16) ha (q := 5953)
      (by decide) (divisor_from_residue (by reduce_mod_char)) (hb 5953 (by decide))
  · exact exclude_odd_cofactor hn h2 (by decide : 0 < 16) ha (q := 7873)
      (by decide) (divisor_from_residue (by reduce_mod_char)) (hb 7873 (by decide))
  · exact exclude_odd_cofactor hn h2 (by decide : 0 < 16) ha (q := 2753)
      (by decide) (divisor_from_residue (by reduce_mod_char)) (hb 2753 (by decide))

lemma odd_part_64 {n : ℕ} (hn : Erdos1052.IsUnitaryPerfect n) (h2 : 2 ∣ n)
    (ha : padicValNat 2 n % 128 = 64)
    (hb : ∀ q ∈ ([769,3329,11777,7937] : List ℕ), ¬ q ∣ n) :
    ∀ d ∈ ([3,13,23,31] : List ℕ), ¬ d ∣ padicValNat 2 n / 64 := by
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · exact exclude_odd_cofactor hn h2 (by decide : 0 < 64) ha (q := 769)
      (by decide) (divisor_from_residue (by reduce_mod_char)) (hb 769 (by decide))
  · exact exclude_odd_cofactor hn h2 (by decide : 0 < 64) ha (q := 3329)
      (by decide) (divisor_from_residue (by reduce_mod_char)) (hb 3329 (by decide))
  · exact exclude_odd_cofactor hn h2 (by decide : 0 < 64) ha (q := 11777)
      (by decide) (divisor_from_residue (by reduce_mod_char)) (hb 11777 (by decide))
  · exact exclude_odd_cofactor hn h2 (by decide : 0 < 64) ha (q := 7937)
      (by decide) (divisor_from_residue (by reduce_mod_char)) (hb 7937 (by decide))

lemma odd_part_128 {n : ℕ} (hn : Erdos1052.IsUnitaryPerfect n) (h2 : 2 ∣ n)
    (ha : padicValNat 2 n % 256 = 128)
    (hb : ∀ q ∈ ([10753,18433,7681,19457] : List ℕ), ¬ q ∣ n) :
    ∀ d ∈ ([7,9,15,19] : List ℕ), ¬ d ∣ padicValNat 2 n / 128 := by
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · exact exclude_odd_cofactor hn h2 (by decide : 0 < 128) ha (q := 10753)
      (by decide) (divisor_from_residue (by reduce_mod_char)) (hb 10753 (by decide))
  · exact exclude_odd_cofactor hn h2 (by decide : 0 < 128) ha (q := 18433)
      (by decide) (divisor_from_residue (by reduce_mod_char)) (hb 18433 (by decide))
  · exact exclude_odd_cofactor hn h2 (by decide : 0 < 128) ha (q := 7681)
      (by decide) (divisor_from_residue (by reduce_mod_char)) (hb 7681 (by decide))
  · exact exclude_odd_cofactor hn h2 (by decide : 0 < 128) ha (q := 19457)
      (by decide) (divisor_from_residue (by reduce_mod_char)) (hb 19457 (by decide))

lemma two_repeated {n : ℕ} {S : Finset ℕ}
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (hlarge : 67280421310721 ^ 8 ∣ n) (hsmall : 274177 ^ 8 ∣ n ∨ 137089 ^ 8 ∣ n) :
    2 ≤ S.card := by
  have mem {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpow : p ^ 8 ∣ n) : p ∈ S :=
    (hS p).mpr ⟨hp, hp2, Nat.pow_dvd_of_le_of_pow_dvd (by decide : 2 ≤ 8) hpow⟩
  have hL := mem prime_67280421310721 (by decide) hlarge
  rcases hsmall with h | h
  · exact Finset.one_lt_card.mpr ⟨274177, mem (by norm_num) (by decide) h, 67280421310721, hL, by decide⟩
  · exact Finset.one_lt_card.mpr ⟨137089, mem (by norm_num) (by decide) h, 67280421310721, hL, by decide⟩

lemma budget_without_fermat {S : Finset ℕ} (hmem : 65537 ∈ S)
    (hthin : ∏ z ∈ S, (1 + 5 / (z : ℚ)) ≤ 5001/5000) :
    ∏ z ∈ S.erase 65537, (1 + 5 / (z : ℚ)) ≤ 5001/5000 / (1 + 5/(65537:ℚ)) := by
  apply (le_div_iff₀ (by norm_num : (0:ℚ) < 1 + 5/65537)).mpr
  rw [mul_comm]
  have h := (Finset.mul_prod_erase S (fun z : ℕ => 1 + 5/(z:ℚ)) hmem).le.trans hthin
  norm_num only [Nat.cast_ofNat] at h ⊢
  exact h

def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n → 223 ∣ n → 607 ∣ n → 3967 ∣ n → 48 ≤ padicValNat 2 n →
    ∏ z ∈ S, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000 → (∀ z ∈ S, 25000 ≤ z) →
    ¬ 8191 ∣ n → 7933 ∣ n → 19423 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → ¬ q ^ 2 ∣ n → q < 49468 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨
        q = 7933 ∨ q = 19423) →
    padicValNat 2 n % 32 = 16 →
    65537 ^ 16 ∣ n → (n.factorization 65537 % 32 = 16 ∨ 128 ∣ n.factorization 65537) →
    (∀ d ∈ ([3,7,17,31,41,43] : List ℕ), ¬ d ∣ padicValNat 2 n / 16) →
    (∏ z ∈ S.erase 65537, (1 + 5 / (z : ℚ))) ≤ 5001/5000 / (1 + 5/(65537:ℚ)) →
    padicValNat 2 n ≤ A

def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n → 223 ∣ n → 607 ∣ n → 3967 ∣ n → 48 ≤ padicValNat 2 n →
    ∏ z ∈ S, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000 → (∀ z ∈ S, 25000 ≤ z) →
    ¬ 8191 ∣ n → 7933 ∣ n → 19423 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → ¬ q ^ 2 ∣ n → q < 49468 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨
        q = 7933 ∨ q = 19423) →
    padicValNat 2 n % 128 = 64 →
    67280421310721 ^ 8 ∣ n → (274177 ^ 8 ∣ n ∨ 137089 ^ 8 ∣ n) → 2 ≤ S.card →
    (∀ d ∈ ([3,13,23,31] : List ℕ), ¬ d ∣ padicValNat 2 n / 64) →
    padicValNat 2 n ≤ A

def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n → 223 ∣ n → 607 ∣ n → 3967 ∣ n → 48 ≤ padicValNat 2 n →
    ∏ z ∈ S, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000 → (∀ z ∈ S, 25000 ≤ z) →
    ¬ 8191 ∣ n → 7933 ∣ n → 19423 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → ¬ q ^ 2 ∣ n → q < 49468 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨
        q = 7933 ∨ q = 19423) →
    128 ∣ padicValNat 2 n →
    (∃ k t z : ℕ, 7 ≤ k ∧ Odd t ∧ padicValNat 2 n = 2 ^ k * t ∧ z ∈ S ∧
      z % 3 = 2 ∧ z ∣ Nat.fermatNumber k ∧ 2 ^ (k + 2) ∣ z - 1) →
    (padicValNat 2 n % 256 = 128 → ∀ d ∈ ([7,9,15,19] : List ℕ), ¬ d ∣ padicValNat 2 n / 128) →
    padicValNat 2 n ≤ A

theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1_H2_R1.H1 := by
  rintro ⟨A,hA⟩ ⟨B,hB⟩ ⟨C,hC⟩
  refine ⟨max A (max B C), ?_⟩
  intro n hn hns S hS hadm hweight h4 h3 h5 h7 h19 hres h16 hnot32 h31 h223 h607
    h3967 h48 hthin hge h8191 h7933 h19423 hgap
  specialize hA n hn hns S hS hadm hweight h4 h3 h5 h7 h19 hres h16 hnot32 h31 h223 h607
    h3967 h48 hthin hge h8191 h7933 h19423 hgap
  specialize hB n hn hns S hS hadm hweight h4 h3 h5 h7 h19 hres h16 hnot32 h31 h223 h607
    h3967 h48 hthin hge h8191 h7933 h19423 hgap
  specialize hC n hn hns S hS hadm hweight h4 h3 h5 h7 h19 hres h16 hnot32 h31 h223 h607
    h3967 h48 hthin hge h8191 h7933 h19423 hgap
  have h2 : 2 ∣ n := dvd_of_one_le_padicValNat (le_trans (by decide) h48)
  have forbidden : ∀ q ∈ ([11,8681,17,257,1409,641,109,13,9337,2617,13709,313,193,449,5441,5953,7873,2753,769,3329,11777,7937,10753,18433,7681,19457] : List ℕ), ¬ q ∣ n := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact prime_gap hS hge hgap (by norm_num) (by decide) (by decide)
  have sublist (l : List ℕ) (hl : l ⊆ ([11,8681,17,257,1409,641,109,13,9337,2617,13709,313,193,449,5441,5953,7873,2753,769,3329,11777,7937,10753,18433,7681,19457] : List ℕ)) :
      ∀ q ∈ l, ¬ q ∣ n := fun _ hq => forbidden _ (hl hq)
  by_cases hm4 : padicValNat 2 n % 32 = 16
  · obtain ⟨hpow, he⟩ := valuation_four hn h2 hm4 (sublist _ (by decide))
    have hs := (hS 65537).mpr ⟨by norm_num, by decide, Nat.pow_dvd_of_le_of_pow_dvd (by decide : 2 ≤ 16) hpow⟩
    exact (hA hm4 hpow he (odd_part_16 hn h2 hm4 (sublist _ (by decide)))
      (budget_without_fermat hs hthin)).trans (le_max_left _ _)
  by_cases hm6 : padicValNat 2 n % 128 = 64
  · obtain ⟨hbig, hmore⟩ := valuation_six hn h2 hm6 (sublist _ (by decide))
    exact (hB hm6 hbig hmore (two_repeated hS hbig hmore)
      (odd_part_64 hn h2 hm6 (sublist _ (by decide)))).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  have hm32 := lift_power_of_two (by decide) h16 hm4
  have hm64 := lift_power_of_two (by decide) hm32 hnot32
  have hm7 := lift_power_of_two (by decide) hm64 hm6
  exact (hC hm7 (high_fermat_factor hn hS hge h2 h5 hm7 (Nat.ne_zero_of_lt (Nat.lt_of_lt_of_le (by decide : 0 < 48) h48)))
    (fun h => odd_part_128 hn h2 h (sublist _ (by decide)))).trans
    ((le_max_right _ _).trans (le_max_right _ _))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1_H2_R1_H1_R1
