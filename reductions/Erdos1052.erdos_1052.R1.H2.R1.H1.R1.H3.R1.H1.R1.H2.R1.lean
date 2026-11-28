import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H1_R1
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Prime divisors forced by the exponent of 3

Let e be the exponent of 3 in a unitary perfect number in the residual case.
If e is odd, every prime power dividing e occurs as the order of -3 at a
prime divisor of n. Distinct orders give at least Ω(e) different divisors
other than 2 and 3. If e is even, write e = 2^t u with u odd. A divisor p
of (3^(2^t)+1)/2 is 2 modulo 3. Quadratic reciprocity and Euler's criterion
give the exact power of 2 in p-1. The exclusions in the parent leave t=1,
t=2 and t≥6. Uniform bounds on the exponent of 2 in these odd and even
cases suffice for the assigned bound.
-/

-- Credit: @Pixelstorm44
namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H1_R1_H2_R1
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (exists_quot_mod exists_prime_mod3)

private theorem odd_lift {a b e : ℕ} (ho : Odd e) (hd : a ∣ e) :
    b ^ a + 1 ∣ b ^ e + 1 := by
  obtain ⟨k, rfl⟩ := hd
  have hk := ho.of_dvd_nat (dvd_mul_left k a)
  simpa [pow_mul] using hk.nat_add_dvd_pow_add_pow (b ^ a) 1

private theorem cast_neg_three_pow {p a : ℕ} (ha : Odd a) :
    (-3 : ZMod p) ^ a = 1 ↔ p ∣ 3 ^ a + 1 := by
  rw [show (-3 : ZMod p) = -(3 : ZMod p) by rfl, ha.neg_pow]
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  constructor <;> intro h <;> linear_combination -h

-- The successive quotients for a prime power have distinct prime witnesses.
private theorem odd_layer {e l j : ℕ} (he : Odd e) (hl : l.Prime)
    (hd : l ^ (j + 1) ∣ e) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ 3 ^ e + 1 ∧
      orderOf (-3 : ZMod p) = l ^ (j + 1) ∧ 2 * l ^ (j + 1) ∣ p - 1 := by
  have : Fact l.Prime := ⟨hl⟩
  have hlo : Odd l := he.of_dvd_nat ((dvd_pow_self _ (Nat.succ_ne_zero j)).trans hd)
  let b := 3 ^ (l ^ j)
  obtain ⟨Q, hQ, hres⟩ := exists_quot_mod (z := b) hlo
  have hb : 1 < b := Nat.one_lt_pow (pow_ne_zero _ hl.ne_zero) (by decide)
  have hbQ : b < b ^ l := by
    simpa using Nat.pow_lt_pow_right hb hl.one_lt
  have hQ1 : Q ≠ 1 := by rintro rfl; simp at hQ; omega
  obtain ⟨p, hp, hpQ⟩ := Nat.exists_prime_and_dvd hQ1
  have : Fact p.Prime := ⟨hp⟩
  have hres' : Q ≡ l [MOD b + 1] := hres
  have h2b : 2 ∣ b + 1 := by
    have : Odd b := (by decide : Odd 3).pow
    have := Nat.odd_iff.mp this
    omega
  have h2 : p ≠ 2 := by
    rintro rfl
    have h := Nat.ModEq.of_dvd h2b hres'
    change Q % 2 = l % 2 at h
    have := Nat.odd_iff.mp hlo
    omega
  have hpbig : p ∣ 3 ^ (l ^ (j+1)) + 1 := by
    rw [pow_succ l, pow_mul, Nat.add_comm, hQ]
    exact hpQ.trans (dvd_mul_left _ _)
  have hfin := (cast_neg_three_pow (p := p) (show Odd (l ^ (j+1)) from hlo.pow)).mpr hpbig
  have hnot : ¬ (-3 : ZMod p) ^ l ^ j = 1 := by
    intro h
    have hpb : p ∣ b + 1 := (cast_neg_three_pow (show Odd (l ^ j) from hlo.pow)).mp h
    have hmod := Nat.ModEq.of_dvd hpb hres'
    have hpl : p ∣ l := (hmod.dvd_iff (dvd_refl p)).mp hpQ
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hl).mp hpl
    rw [ZMod.pow_card_pow] at hfin
    have hf : ((4 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination -hfin
    have h4 := (ZMod.natCast_eq_zero_iff _ _).mp hf
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from h4)))
  have hord := orderOf_eq_prime_pow hnot hfin
  have hx : (-3 : ZMod p) ≠ 0 := by
    intro h
    rw [h, zero_pow (pow_ne_zero _ hl.ne_zero)] at hfin
    exact zero_ne_one hfin
  have hdiv := ZMod.orderOf_dvd_card_sub_one hx
  rw [hord] at hdiv
  have htwo : 2 ∣ p - 1 := by have := hp.eq_two_or_odd; omega
  exact ⟨p, hp, h2, hpbig.trans (odd_lift he hd), hord,
    ((show Odd (l ^ (j+1)) from hlo.pow).coprime_two_left).mul_dvd_of_dvd_of_dvd htwo hdiv⟩

-- A prime in the class 2 modulo 3 detects the exact power of 2 in its predecessor.
private theorem even_layer {t : ℕ} (ht : 0 < t) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p % 3 = 2 ∧ p ∣ (3 ^ (2 ^ t) + 1) / 2 ∧
      orderOf (3 : ZMod p) = 2 ^ (t + 1) ∧
      2 ^ (t + 1) ∣ p - 1 ∧ ¬ 2 ^ (t + 2) ∣ p - 1 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  let F := 3 ^ (2 ^ (s+1)) + 1
  have h4 : F % 4 = 2 := by
    change 3 ^ (2 ^ (s+1)) + 1 ≡ 2 [MOD 4]
    rw [pow_succ', pow_mul]
    exact ((show 9 ≡ 1 [MOD 4] by decide).pow (2^s) |>.add_right 1 :
      9 ^ (2^s) + 1 ≡ 1 ^ (2^s) + 1 [MOD 4]) |>.trans (by simp only [one_pow]; rfl)
  have h3 : F % 3 = 1 := by
    have h := dvd_pow_self 3 (show 2 ^ (s+1) ≠ 0 by positivity)
    dsimp [F]; omega
  obtain ⟨p, hp, hpd, hp3⟩ := exists_prime_mod3 (F/2) (by omega)
  have ho : p ≠ 2 := by rintro rfl; omega
  have : Fact p.Prime := ⟨hp⟩
  have hpdF : p ∣ F := hpd.trans (Nat.div_dvd_of_dvd (by omega : 2 ∣ F))
  have hneg : (3 : ZMod p) ^ (2 ^ (s+1)) = -1 := by
    have h := (ZMod.natCast_eq_zero_iff F p).mpr hpdF
    dsimp [F] at h
    push_cast at h
    exact eq_neg_of_add_eq_zero_left h
  have hnot : (3 : ZMod p) ^ (2 ^ (s+1)) ≠ 1 := by
    intro h
    have hz : ((2 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination hneg - h
    exact ho ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff _ _).mp hz))
  have hfin : (3 : ZMod p) ^ (2 ^ (s+1+1)) = 1 := by
    rw [pow_succ 2 (s+1), pow_mul, hneg]; norm_num
  have hord := orderOf_eq_prime_pow hnot hfin
  have hx : (3 : ZMod p) ≠ 0 := by
    intro h
    have hpdiv := (ZMod.natCast_eq_zero_iff 3 p).mp (by exact_mod_cast h)
    have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp hpdiv
    omega
  have hd := ZMod.orderOf_dvd_card_sub_one hx
  rw [hord] at hd
  have h4p : 4 ∣ p - 1 := (pow_dvd_pow 2 (by omega : 2 ≤ s+1+1)).trans hd
  have hp1 := hp.one_lt
  have hrec := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := p) (q := 3)
    (by omega) (by decide)
  have hnon : ¬IsSquare (3 : ZMod p) := by
    intro h
    have hs := hrec.mp h
    have hc : (p : ZMod 3) = 2 :=
      (ZMod.natCast_eq_natCast_iff p 2 3).mpr (by exact hp3)
    rw [hc] at hs
    obtain ⟨x, hx⟩ := hs
    fin_cases x <;> revert hx <;> decide
  refine ⟨p, hp, ho, hp3, hpd, hord, hd, ?_⟩
  intro hmore
  apply hnon
  apply (ZMod.euler_criterion p hx).mpr
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [hord]
  obtain ⟨k, hk⟩ := hmore
  rw [pow_succ 2 (s+1+1)] at hk
  exact ⟨k, by rw [Nat.mul_right_comm] at hk; omega⟩

-- Different prime powers give different orders, so their witnesses are distinct.
private theorem count_layers {n e : ℕ} (hn : n ≠ 0)
    (h : ∀ l j : ℕ, l.Prime → l ^ (j+1) ∣ e →
      ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ∣ n ∧ orderOf (-3 : ZMod p) = l ^ (j+1)) :
    (∑ l ∈ e.primeFactors, e.factorization l) ≤ ((n.primeFactors.erase 2).erase 3).card := by
  classical
  let D := e.primeFactors.sigma (fun l => Finset.range (e.factorization l))
  let T := (n.primeFactors.erase 2).erase 3
  have layer (x : D) : ∃ p ∈ T, orderOf (-3 : ZMod p) = x.val.1 ^ (x.val.2 + 1) := by
    obtain ⟨hmem, hj⟩ := Finset.mem_sigma.mp x.property
    have hl := Nat.prime_of_mem_primeFactors hmem
    have he := (Nat.mem_primeFactors.mp hmem).2.2
    have hd := (hl.pow_dvd_iff_le_factorization he).mpr (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
    obtain ⟨p, hp, hp2, hp3, hpn, hord⟩ := h _ _ hl hd
    exact ⟨p, Finset.mem_erase.mpr ⟨hp3, Finset.mem_erase.mpr ⟨hp2,
      Nat.mem_primeFactors.mpr ⟨hp, hpn, hn⟩⟩⟩, hord⟩
  choose f hf horder using layer
  let g (x : D) : T := ⟨f x, hf x⟩
  have hinj : Function.Injective g := by
    intro x y heq
    have heq' : f x = f y := congrArg Subtype.val heq
    have hx := Nat.prime_of_mem_primeFactors (Finset.mem_sigma.mp x.property).1
    have hy := Nat.prime_of_mem_primeFactors (Finset.mem_sigma.mp y.property).1
    have hord := horder x
    rw [heq', horder y] at hord
    obtain ⟨ha, hb⟩ := hy.pow_inj hx hord
    apply Subtype.ext
    exact Sigma.ext ha.symm (heq_of_eq hb.symm)
  simpa [D, T, Finset.card_sigma] using Finset.card_le_card_of_injective hinj

-- Every prime-power component contributes its successor to the unitary divisor sum.
private theorem component {n b q : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hb : b.Prime) (hbn : b ∣ n) (hq : q.Prime) (hq2 : q ≠ 2)
    (hd : q ∣ b ^ n.factorization b + 1) : q ∣ n := by
  have hm : b ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hb, hbn, h.2.ne'⟩
  have ht : q ∣ 2 * n := by
    rw [← OMA.R_Erdos1052_erdos_1052_R1.prod_eq_two_mul h]
    exact (by simpa [Nat.add_comm] using hd : q ∣ 1 + b ^ n.factorization b).trans
      (Finset.dvd_prod_of_mem (fun p => 1 + p ^ n.factorization p) hm)
  exact (hq.dvd_mul.mp ht).resolve_left (fun hd2 => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hd2))

def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) → 2 ≤ S.card →
    3 ∈ S →
    (∀ d ∈ ({6, 8, 9, 10, 12, 14, 15, 16, 17, 20, 21, 22, 23, 25, 26, 28, 29, 31, 32, 33, 34, 35, 37, 38, 39} : Finset ℕ), n.factorization 3 % (2 * d) ≠ d) →
    (5 ∈ S → ∀ dL ∈ ([(6, [13, 601, 7]), (10, [13, 41, 7]), (14, [234750601, 5953, 13]),
      (20, [241, 11]), (26, [13]),
      (28, [59509429687890001, 29754714843945001, 83, 7679233, 769, 7]),
      (34, [13, 1973, 7])] : List (ℕ × List ℕ)),
      n.factorization 5 % (2 * dL.1) = dL.1 → ∃ c ∈ dL.2, c ∈ S) →
    (7 ∈ S → ∀ dL ∈ ([(2, [5]), (19, [351121, 419]), (32, [7699649, 5]), (37, [149, 5])] : List (ℕ × List ℕ)),
      n.factorization 7 % (2 * dL.1) = dL.1 → ∃ c ∈ dL.2, c ∈ S) →
    Odd (n.factorization 3) →
    (∀ l j : ℕ, l.Prime → l ^ (j+1) ∣ n.factorization 3 →
      ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ∣ n ∧ p ∣ 3 ^ n.factorization 3 + 1 ∧
        orderOf (-3 : ZMod p) = l ^ (j+1) ∧ 2 * l ^ (j+1) ∣ p - 1) →
    (∑ l ∈ (n.factorization 3).primeFactors, (n.factorization 3).factorization l) ≤
      ((n.primeFactors.erase 2).erase 3).card →
    padicValNat 2 n ≤ A

def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) → 2 ≤ S.card →
    3 ∈ S →
    (∀ d ∈ ({6, 8, 9, 10, 12, 14, 15, 16, 17, 20, 21, 22, 23, 25, 26, 28, 29, 31, 32, 33, 34, 35, 37, 38, 39} : Finset ℕ), n.factorization 3 % (2 * d) ≠ d) →
    (5 ∈ S → ∀ dL ∈ ([(6, [13, 601, 7]), (10, [13, 41, 7]), (14, [234750601, 5953, 13]),
      (20, [241, 11]), (26, [13]),
      (28, [59509429687890001, 29754714843945001, 83, 7679233, 769, 7]),
      (34, [13, 1973, 7])] : List (ℕ × List ℕ)),
      n.factorization 5 % (2 * dL.1) = dL.1 → ∃ c ∈ dL.2, c ∈ S) →
    (7 ∈ S → ∀ dL ∈ ([(2, [5]), (19, [351121, 419]), (32, [7699649, 5]), (37, [149, 5])] : List (ℕ × List ℕ)),
      n.factorization 7 % (2 * dL.1) = dL.1 → ∃ c ∈ dL.2, c ∈ S) →
    (∃ t u p : ℕ, (t = 1 ∨ t = 2 ∨ 6 ≤ t) ∧ Odd u ∧ n.factorization 3 = 2 ^ t * u ∧
      p.Prime ∧ p ∣ n ∧ p % 3 = 2 ∧ p ∣ (3 ^ (2 ^ t) + 1) / 2 ∧
      orderOf (3 : ZMod p) = 2 ^ (t+1) ∧ 2 ^ (t+1) ∣ p - 1 ∧ ¬ 2 ^ (t+2) ∣ p - 1 ∧
      (t = 1 → p = 5) ∧ (t = 2 → p = 41)) →
    padicValNat 2 n ≤ A

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H1_R1.H2 := by
  rintro ⟨A, hA⟩ ⟨B, hB⟩
  refine ⟨max A B, ?_⟩
  intro n hn S hS hcard _ h3 hex h5 h7
  let e := n.factorization 3
  have h9 := ((hS 3).mp h3).2.2
  have hp3 : Nat.Prime 3 := by decide
  have h3n : 3 ∣ n := (dvd_pow_self 3 (by decide : 2 ≠ 0)).trans h9
  have hge : 2 ≤ e := (hp3.pow_dvd_iff_le_factorization hn.2.ne').mp h9
  have lift {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hd : p ∣ 3 ^ e + 1) : p ∣ n :=
    component hn hp3 h3n hp h2 hd
  by_cases he : Odd e
  · apply le_trans _ (le_max_left A B)
    have layers (l j : ℕ) (hl : l.Prime) (hd : l ^ (j+1) ∣ e) :
        ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ∣ n ∧ p ∣ 3 ^ e + 1 ∧
          orderOf (-3 : ZMod p) = l ^ (j+1) ∧ 2 * l ^ (j+1) ∣ p - 1 := by
      obtain ⟨p, hp, h2, hpd, hord, hdiv⟩ := odd_layer he hl hd
      have hne : p ≠ 3 := by
        rintro rfl
        have := dvd_pow_self 3 (show e ≠ 0 by omega)
        omega
      exact ⟨p, hp, h2, hne, lift hp h2 hpd, hpd, hord, hdiv⟩
    apply hA n hn S hS hcard h3 hex h5 h7 he layers
    apply count_layers hn.2.ne'
    intro l j hl hd
    obtain ⟨p, hp, h2, hne, hpn, _, hord, _⟩ := layers l j hl hd
    exact ⟨p, hp, h2, hne, hpn, hord⟩
  · apply le_trans _ (le_max_right A B)
    apply hB n hn S hS hcard h3 hex h5 h7
    obtain ⟨t, u, hu, htu⟩ := Nat.exists_eq_two_pow_mul_odd (show e ≠ 0 by omega)
    have htpos : 0 < t := by
      by_contra! ht
      have : t = 0 := by omega
      simp [this] at htu
      exact he (htu ▸ hu)
    have hclass : t = 1 ∨ t = 2 ∨ 6 ≤ t := by
      have h8 := hex 8 (by decide)
      have h16 := hex 16 (by decide)
      have h32 := hex 32 (by decide)
      change e % 16 ≠ 8 at h8
      change e % 32 ≠ 16 at h16
      change e % 64 ≠ 32 at h32
      obtain ⟨v, hv⟩ := hu
      by_contra! h
      obtain ht | ht | ht : t = 3 ∨ t = 4 ∨ t = 5 := by omega
      all_goals rw [ht, hv] at htu; norm_num at htu; omega
    obtain ⟨p, hp, h2, hr, hpd, hord, hdiv, hexact⟩ := even_layer htpos
    have h2F : 2 ∣ 3 ^ (2 ^ t) + 1 := by
      have hodd : Odd (3 ^ (2 ^ t)) := (by decide : Odd 3).pow
      have := Nat.odd_iff.mp hodd
      omega
    have hpdF := hpd.trans (Nat.div_dvd_of_dvd h2F)
    have hde : 3 ^ (2^t) + 1 ∣ 3 ^ e + 1 := by
      rw [htu, pow_mul]
      simpa using hu.nat_add_dvd_pow_add_pow (3 ^ (2^t)) 1
    refine ⟨t, u, p, hclass, hu, htu, hp, lift hp h2 (hpdF.trans hde),
      hr, hpd, hord, hdiv, hexact, ?_, ?_⟩
    · rintro rfl
      exact (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp hpd
    · rintro rfl
      exact (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 41)).mp hpd

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H1_R1_H2_R1
