import OMAStatements.S_oeis_a250404

-- Credit: @rleshner

open OMA.S_oeis_a250404

namespace TotientDivisors

private theorem totient_proper {k : ℕ} (h : IsTerm k) {d : ℕ} (hd : d ∣ k) :
    d.totient ∈ (k+1).properDivisors := by
  rw [←h.2]
  exact Finset.mem_image.mpr ⟨d,Nat.mem_divisors.mpr ⟨hd,h.1.ne'⟩,rfl⟩

private theorem power_successor {k : ℕ} (h : IsTerm k) (hk : 2 < k) :
    ∃ a : ℕ, k+1 = 2^a := by
  rcases (k+1).eq_two_pow_or_exists_odd_prime_and_dvd with yes | ⟨p,hp,hd,ho⟩
  · exact yes
  exfalso
  have hle := Nat.le_of_dvd (by omega : 0 < k+1) hd
  rcases lt_or_eq_of_le hle with hlt|rfl
  · have mem := Nat.mem_properDivisors.mpr ⟨hd,hlt⟩
    rw [←h.2] at mem
    obtain ⟨d,_,heq⟩ := Finset.mem_image.mp mem
    have odd : Odd d.totient := heq ▸ ho
    have eqone := Nat.totient_eq_one_iff.mpr (Nat.odd_totient_iff.mp odd)
    exact hp.ne_one (heq ▸ eqone)
  · have mem := totient_proper h (dvd_refl k)
    rw [Nat.properDivisors_eq_singleton_one_iff_prime.mpr hp,Finset.mem_singleton] at mem
    have := Nat.totient_eq_one_iff.mp mem
    omega

private theorem power_exponent {k a : ℕ} (h : IsTerm k) (ha : k+1 = 2^a) :
    ∃ b : ℕ, a = 2^b := by
  rcases a.eq_two_pow_or_exists_odd_prime_and_dvd with yes | ⟨p,hp,hd,ho⟩
  · exact yes
  exfalso
  have hp2 := hp.two_le
  have big : 4 ≤ 2^p := Nat.pow_le_pow_right (n:=2) (i:=2) (by decide) hp2
  obtain ⟨q,hq,hqd⟩ := Nat.exists_prime_and_dvd (n:=2^p-1) (by omega)
  have dk : (2^p-1) ∣ k := by
    rw [show k=2^a-1 by omega]
    exact Nat.pow_sub_one_dvd_pow_sub_one _ hd
  have ht := (Nat.mem_properDivisors.mp (totient_proper h (hqd.trans dk))).1
  rw [ha, Nat.totient_prime hq] at ht
  obtain ⟨j,_,hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ht
  have oddq : Odd q := by
    apply hq.odd_of_ne_two
    rintro rfl
    have : 2 ∣ (2:ℕ)^p := dvd_pow_self _ (by omega)
    omega
  have flt := Nat.ModEq.pow_totient (Nat.coprime_two_left.mpr oddq)
  rw [Nat.totient_prime hq,hj] at flt
  have hpow : q ∣ 2^(2^j)-1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by decide) : 1 ≤ 2^(2^j))).mp flt.symm
  have hg := Nat.dvd_gcd hqd hpow
  rw [Nat.pow_sub_one_gcd_pow_sub_one, (Nat.coprime_two_right.mpr ho).pow_right j |>.gcd_eq_one] at hg
  exact hq.not_dvd_one (by simpa using hg)

theorem bound (k : ℕ) (h : IsTerm k) : k ≤ 4294967295 := by
  by_contra! large
  obtain ⟨a,ha⟩ := power_successor h (by omega)
  obtain ⟨b,hb⟩ := power_exponent h ha
  have hb6 : 6 ≤ b := by
    by_contra! small
    have h1 : 2^b ≤ 32 := Nat.pow_le_pow_right (n:=2) (j:=5) (by decide) (by omega)
    have h2 : 2^a ≤ 4294967296 := Nat.pow_le_pow_right (n:=2) (j:=32) (by decide) (by omega)
    omega
  have d64 : 64 ∣ a := by
    rw [hb]
    exact Nat.pow_dvd_pow 2 hb6
  have d641 : 641 ∣ k := by
    rw [show k = 2^a-1 by omega]
    exact dvd_trans (by decide : 641 ∣ (2:ℕ)^64-1) (Nat.pow_sub_one_dvd_pow_sub_one _ d64)
  have ht := (Nat.mem_properDivisors.mp (totient_proper h d641)).1
  rw [ha,Nat.totient_prime (by norm_num : Nat.Prime 641)] at ht
  have bad := (show 5 ∣ 641-1 by decide).trans ht
  have := (show Nat.Prime 5 by decide).dvd_of_dvd_pow bad
  norm_num at this

end TotientDivisors

open OMA.S_oeis_a250404

namespace TotientEndpoint

private def addFactor (p : ℕ) (s : Finset ℕ) : Finset ℕ :=
  s ∪ s.image (fun a => (p-1)*a)

private theorem divisor_totients_step (p m : ℕ) (hp : p.Prime) (hm : m ≠ 0) (cop : p.Coprime m) :
    (p*m).divisors.image Nat.totient = addFactor p (m.divisors.image Nat.totient) := by
  ext x
  simp only [addFactor,Finset.mem_union,Finset.mem_image,Nat.mem_divisors]
  constructor
  · rintro ⟨d,⟨hd,_⟩,rfl⟩
    by_cases h : p ∣ d
    · obtain ⟨z,rfl⟩ := h
      have hz := Nat.dvd_of_mul_dvd_mul_left hp.pos hd
      right
      exact ⟨z.totient,⟨z,⟨hz,hm⟩,rfl⟩,by rw [Nat.totient_mul (Nat.Coprime.of_dvd_right hz cop), Nat.totient_prime hp]⟩
    · left
      exact ⟨d,⟨((hp.coprime_iff_not_dvd.mpr h).symm.dvd_of_dvd_mul_left hd), hm⟩,rfl⟩
  · rintro (⟨d,⟨hd,_⟩,rfl⟩|⟨_,⟨d,⟨hd,_⟩,rfl⟩,rfl⟩)
    · exact ⟨d,⟨dvd_mul_of_dvd_right hd p,mul_ne_zero hp.ne_zero hm⟩,rfl⟩
    · exact ⟨p*d,⟨Nat.mul_dvd_mul_left p hd,mul_ne_zero hp.ne_zero hm⟩,by rw [Nat.totient_mul (Nat.Coprime.of_dvd_right hd cop), Nat.totient_prime hp]⟩

theorem endpoint : IsTerm 4294967295 := by
  refine ⟨by decide, ?_⟩
  rw [show (4294967295:ℕ)+1=2^32 by decide, Nat.properDivisors_prime_pow Nat.prime_two]
  rw [show (4294967295:ℕ)=65537*(257*(17*(5*(3*1)))) by decide]
  rw [divisor_totients_step 65537 _ (by norm_num1) (by decide) (by decide),
      divisor_totients_step 257 _ (by norm_num1) (by decide) (by decide),
      divisor_totients_step 17 _ (by norm_num1) (by decide) (by decide),
      divisor_totients_step 5 _ (by norm_num1) (by decide) (by decide),
      divisor_totients_step 3 _ (by norm_num1) (by decide) (by decide)]
  decide +kernel

end TotientEndpoint

theorem OMA.solution : type_of% @OMA.S_oeis_a250404.main := by
  exact ⟨TotientEndpoint.endpoint, fun k hk => TotientDivisors.bound k hk⟩
