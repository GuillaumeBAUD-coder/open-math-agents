import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1

/-!
# A simultaneous exponent and successor sieve for the one-repeated-prime case

The unitary balance identity and the quotient congruence are due to
@adammcarter (PR 1834). The sieve tests arbitrary odd cofactor decompositions
of the repeated-prime exponent, with arbitrary finite successor depth.
-/
-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R2 of step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2
-- Credit: @Mapika
namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R2
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 main
open scoped BigOperators

theorem sieve {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (hz : z.Prime) (hz5 : 5 ≤ z)
    (hr : ∀ p, p.Prime ∧ p ≠ 2 ∧ p^2 ∣ n ↔ p=z) :
    (∀ d w : ℕ, 0 < d → Odd w → n.factorization z = d*w →
    Nat.Coprime w (1+z^d) ∧ ∀ b : ℕ, b ∣ 2^(n.factorization 2)+1 → ∀ F : Finset ℕ,
    (∀ p ∈ F, (∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ≠ z ∧ r ∣ (b*(1+z^d)) ∧
      Relation.ReflTransGen (fun x y : ℕ => y.Prime ∧ y ≠ 2 ∧ y ≠ z ∧ y ∣ x+1) r p)) → ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ z →
    ¬ q*q ∣ b*(1+z^d)*∏ p ∈ F, (p+1)) := by
  classical
  have hn0 := h.2.ne'
  have hzsq := ((hr z).mpr rfl).2.2
  have hzmem := Nat.mem_primeFactors.mpr ⟨hz, (dvd_pow_self z (by decide : 2 ≠ 0)).trans hzsq, hn0⟩
  have hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ z → n.factorization r = 1 := by
    intro r hrm hr2 hrz
    have hp := Nat.prime_of_mem_primeFactors hrm
    have hpos := hp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hrm)
    have hsmall : ¬ 2 ≤ n.factorization r :=
      fun he => hrz ((hr r).mp ⟨hp, hr2, (hp.pow_dvd_iff_le_factorization hn0).mpr he⟩)
    omega
  let P := (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({z} : Finset ℕ))
  obtain ⟨hP,E⟩ := kernel_balance_one h hzmem (by omega) hs
  change ∀ p ∈ P, p.Prime ∧ p ≠ 2 at hP
  change (2 ^ n.factorization 2 + 1) * (1 + z ^ n.factorization z) *
    ∏ p ∈ P, (p + 1) = 2 ^ (n.factorization 2 + 1) * z ^ n.factorization z *
      ∏ p ∈ P, p at E
  have hK := prime_dvd_prime_pow (e := n.factorization z) hz
  obtain ⟨succMem, _, _, _, _, _, _, _⟩ := facts hP hK E
  intro d w hd hw he
  obtain ⟨Q, hQ, hQr⟩ := exists_quot_mod (z := z^d) hw
  rw [← pow_mul, ← he] at hQ
  have seed_dvd : 1+z^d ∣ 1+z^(n.factorization z) := by
    rw [hQ, add_comm 1]; exact dvd_mul_right _ _
  constructor
  · by_contra bad
    obtain ⟨q,hq,hqw,hqd⟩ := Nat.Prime.not_coprime_iff_dvd.mp bad
    have hq2 : q ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hw) (even_iff_two_dvd.mpr hqw)
    have hqz : q ≠ z := by
      rintro rfl
      have one := (Nat.dvd_add_left (dvd_pow_self q hd.ne')).mp hqd
      exact hq.one_lt.ne' (Nat.dvd_one.mp one)
    have hq' : q ∣ z^d+1 := by simpa [add_comm] using hqd
    have hqr : Q ≡ w [MOD q] := Nat.ModEq.of_dvd hq' hQr
    have hqQ : q ∣ Q := by
      apply Nat.dvd_of_mod_eq_zero
      exact Eq.trans hqr (Nat.mod_eq_zero_of_dvd hqw)
    have sq : q*q ∣ 1+z^(n.factorization z) := hQ ▸ mul_dvd_mul hq' hqQ
    exact S_sq hP hK E hq hq2 (by simpa using hqz) ((sq.mul_left _).mul_right _)
  · intro b hb F hF q hq hq2 hqz sq
    have seeds := mul_dvd_mul hb seed_dvd
    have mem : ∀ p ∈ F, p ∈ P := by
      intro p hp
      obtain ⟨r,hr,hr2,hrz,hrd,path⟩ := hF p hp
      have start := S_mem hP hK E hr hr2 (by simpa using hrz) ((hrd.trans seeds).mul_right _)
      clear hp
      induction path with
      | refl => exact start
      | tail _ step ih =>
        obtain ⟨hq',h2,hz',hdvd⟩ := step
        exact succMem _ hq' h2 (by simpa using hz') _ ih hdvd
    have sub : F ⊆ P := fun x hx => mem x hx
    have prodD := Finset.prod_dvd_prod_of_subset F P (fun p => p+1) sub
    exact S_sq hP hK E hq hq2 (by simpa using hqz) (sq.trans (mul_dvd_mul seeds prodD))


/-- Every odd prime in the base seed forbids an entire progression of exponents. -/
theorem exclude_class {z e d q : ℕ} (clean : ∀ (d w : ℕ), 0 < d → Odd w → e = d*w → Nat.Coprime w (1+z^d)) (hd : 0 < d)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqd : q ∣ 1+z^d) : e % (2*(d*q)) ≠ d*q := by
  intro hr
  let t := e / (2*(d*q))
  have dec : e = d * (q * (2*t+1)) := by
    have h := Nat.div_add_mod e (2*(d*q))
    rw [hr] at h
    dsimp [t]
    nlinarith [h]
  have oddQ := hq.odd_of_ne_two hq2
  have hc := clean d (q*(2*t+1)) hd (oddQ.mul (show Odd (2*t+1) from ⟨t,rfl⟩)) dec
  exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨q,hq,dvd_mul_right ..,hqd⟩) hc

/-- In every positive even divisor layer there is an odd prime producing the
preceding exclusion. In particular take d to be any positive power of two. -/
theorem exclusion_in_every_even_layer {z e d : ℕ} (clean : ∀ (d w : ℕ), 0 < d → Odd w → e = d*w → Nat.Coprime w (1+z^d))
    (zo : Odd z) (hz : 5 ≤ z) (hd : 0 < d) (ed : Even d) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ 1+z^d ∧ e % (2*(d*q)) ≠ d*q := by
  obtain ⟨k,rfl⟩ := ed
  have hk : k ≠ 0 := by omega
  have power := Nat.le_self_pow hk z
  obtain ⟨t, ht⟩ := zo.pow (n := k)
  let L := 2*t*(t+1)+1
  have repr : 1+z^(k+k) = 2*L := by rw [pow_add, ht]; dsimp [L]; ring
  have htpos : 0 < t := by omega
  have Lne : L ≠ 1 := by dsimp [L]; nlinarith
  have prime := Nat.minFac_prime Lne
  have dv := Nat.minFac_dvd L
  have notTwo : L.minFac ≠ 2 := by
    intro he
    rw [he] at dv
    have even : Even L := even_iff_two_dvd.mpr dv
    have odd : Odd L := ⟨t*(t+1), by dsimp [L]; ring⟩
    exact (Nat.not_even_iff_odd.mpr odd) even
  have dvdSeed : L.minFac ∣ 1+z^(k+k) := by rw [repr]; exact dv.mul_left _
  exact ⟨_,prime,notTwo,dvdSeed,exclude_class clean hd prime notTwo dvdSeed⟩


/-- Evaluate a binary addition chain modulo m, reducing after each digit. -/
theorem binary_power (m z : ℕ) (bits : List Bool) (e r : ℕ) (base : z^e ≡ r [MOD m]) :
    z^(bits.foldl (fun a b => 2*a+b.toNat) e) ≡
    bits.foldl (fun a b => a*a*(if b then z else 1)%m) r [MOD m] := by
  induction bits generalizing e r with
  | nil => exact base
  | cons bit rest ih =>
    simp only [List.foldl_cons]
    apply ih
    cases bit with
    | false =>
      simp only [Bool.toNat_false, add_zero, Bool.false_eq_true, ↓reduceIte, mul_one, two_mul, pow_add]
      exact (base.mul base).trans (Nat.mod_modEq ..).symm
    | true =>
      simp only [Bool.toNat_true, ↓reduceIte, two_mul, pow_succ, pow_add]
      exact ((base.mul base).mul (Nat.ModEq.refl z)).trans (Nat.mod_modEq ..).symm

theorem plus_one_test {z e q r : ℕ} (hm : z^e ≡ r [MOD q]) (ht : (1+r)%q=0) : q ∣ 1+z^e :=
  Nat.dvd_of_mod_eq_zero (Eq.trans ((Nat.ModEq.refl 1).add hm) ht)

theorem binary_certificate {z e q : ℕ} (bits : List Bool)
    (he : bits.foldl (fun a b => 2*a+b.toNat) 0 = e)
    (hr : (1+bits.foldl (fun a b => a*a*(if b then z else 1)%q) 1)%q=0) :
    q ∣ 1+z^e := by
  have hm := binary_power q z bits 0 1 (by simp [Nat.ModEq])
  rw [he] at hm
  exact plus_one_test hm hr

/- Explicit exponent residue exclusions. At z=5 the exponent 1252 survives
the earlier sieve up to 283 (its only divisors with odd cofactor are 4 and
1252, and 4 is exempt). The third sample is in the 2 modulo 4 layer at 11,
and the last sample is divisible by 32 at 257. -/
theorem examples {e : ℕ} :
    ((∀ d w : ℕ, 0 < d → Odd w → e=d*w → Nat.Coprime w (1+5^d)) → e % 2504 ≠ 1252) ∧
    ((∀ d w : ℕ, 0 < d → Odd w → e=d*w → Nat.Coprime w (1+5^d)) → e % 4295032832 ≠ 2147516416) ∧
    ((∀ d w : ℕ, 0 < d → Odd w → e=d*w → Nat.Coprime w (1+11^d)) → e % 1710380116 ≠ 855190058) ∧
    ((∀ d w : ℕ, 0 < d → Odd w → e=d*w → Nat.Coprime w (1+257^d)) → e % 103079346176 ≠ 51539673088) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact exclude_class (d:=4) (q:=313) h (by decide) (by norm_num) (by decide) (by decide)
  · exact exclude_class (d:=32768) (q:=65537) h (by decide) (by norm_num) (by decide)
      (binary_certificate (true :: List.replicate 15 false) (by decide) (by decide))
  · exact exclude_class (d:=2018) (q:=423781) h (by decide) (by norm_num) (by decide)
      (binary_certificate [true, true, true, true, true, true, false, false, false, true, false] (by decide) (by decide))
  · exact exclude_class (d:=65536) (q:=786433) h (by decide) (by norm_num) (by decide)
      (binary_certificate (true :: List.replicate 16 false) (by decide) (by decide))

/-- The surviving odd exponent case, including every lifted congruence and finite closure certificate. -/
def H1 : Prop := ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z : ℕ, z.Prime → 5 ≤ z → z < 2100 →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    (z % 3 = 2 → Odd (n.factorization z) → n.factorization z % 6 = 1) →
    (z = 5 → (n.factorization 5 = 2 ∨ n.factorization 5 = 4 ∨ 41 ≤ n.factorization 5) ∧
      ∀ d ∈ ({5, 6, 7, 8, 10, 12, 13, 14, 16, 19, 20, 22, 26, 28, 29, 31, 32, 34, 37, 38} : Finset ℕ),
        n.factorization 5 % (2 * d) ≠ d) →
    (z = 7 → 41 ≤ n.factorization 7 ∧
      ∀ d ∈ ({2, 3, 4, 5, 7, 8, 11, 13, 16, 17, 19, 23, 29, 31, 32, 37} : Finset ℕ),
        n.factorization 7 % (2 * d) ≠ d) →
    Odd (n.factorization z) → (∀ d w : ℕ, 0 < d → Odd w → n.factorization z = d*w →
    Nat.Coprime w (1+z^d) ∧ ∀ b : ℕ, b ∣ 2^(n.factorization 2)+1 → ∀ F : Finset ℕ,
    (∀ p ∈ F, (∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ≠ z ∧ r ∣ (b*(1+z^d)) ∧
      Relation.ReflTransGen (fun x y : ℕ => y.Prime ∧ y ≠ 2 ∧ y ≠ z ∧ y ∣ x+1) r p)) → ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ z →
    ¬ q*q ∣ b*(1+z^d)*∏ p ∈ F, (p+1)) →
    padicValNat 2 n ≤ A

/-- The surviving even exponent case, including every lifted congruence and finite closure certificate. -/
def H2 : Prop := ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z : ℕ, z.Prime → 5 ≤ z → z < 2100 →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    (z % 3 = 2 → Odd (n.factorization z) → n.factorization z % 6 = 1) →
    (z = 5 → (n.factorization 5 = 2 ∨ n.factorization 5 = 4 ∨ 41 ≤ n.factorization 5) ∧
      ∀ d ∈ ({5, 6, 7, 8, 10, 12, 13, 14, 16, 19, 20, 22, 26, 28, 29, 31, 32, 34, 37, 38} : Finset ℕ),
        n.factorization 5 % (2 * d) ≠ d) →
    (z = 7 → 41 ≤ n.factorization 7 ∧
      ∀ d ∈ ({2, 3, 4, 5, 7, 8, 11, 13, 16, 17, 19, 23, 29, 31, 32, 37} : Finset ℕ),
        n.factorization 7 % (2 * d) ≠ d) →
    Even (n.factorization z) → (∀ d w : ℕ, 0 < d → Odd w → n.factorization z = d*w →
    Nat.Coprime w (1+z^d) ∧ ∀ b : ℕ, b ∣ 2^(n.factorization 2)+1 → ∀ F : Finset ℕ,
    (∀ p ∈ F, (∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ≠ z ∧ r ∣ (b*(1+z^d)) ∧
      Relation.ReflTransGen (fun x y : ℕ => y.Prime ∧ y ≠ 2 ∧ y ≠ z ∧ y ∣ x+1) r p)) → ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ z →
    ¬ q*q ∣ b*(1+z^d)*∏ p ∈ F, (p+1)) →
    padicValNat 2 n ≤ A

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1.H2 := by
  rintro ⟨A,oddBound⟩ ⟨B,evenBound⟩
  refine ⟨max A B, ?_⟩
  intro n h z hz low high unique mod3 five seven
  have clean := sieve h hz low unique
  rcases Nat.even_or_odd (n.factorization z) with even | odd
  · exact (evenBound n h z hz low high unique mod3 five seven even clean).trans (le_max_right ..)
  · exact (oddBound n h z hz low high unique mod3 five seven odd clean).trans (le_max_left ..)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R2
