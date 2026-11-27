import OMAReductions.R_RiemannHypothesis_lagarias_criterion_R1_H1_R1
import Mathlib

/-! Exact certificates on 46 intervals. Each divisor sum is computed
from a certified prime factorization. The common harmonic lower bound on an interval comes from
rounding each reciprocal down to a multiple of one ten-millionth. -/
-- Credit: @marcusbuffett
namespace OMA.LagariasFinite
open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

def primes : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67]

lemma table : ∀ i : Fin 71, i.val.Prime ↔ i.val∈primes := by decide +kernel

lemma listed {p : ℕ} (h : p ∈ primes) : p.Prime := by
  have b : p<71 := by
    have e : ∀ k∈primes, k<71 := by decide +kernel
    exact e p h
  exact (table ⟨p,b⟩).mpr h

def factors : ℕ → ℕ → List ℕ
  | 0,n => if n=1 then [] else [n]
  | k+1,n =>
    if n=1 then [] else
      match primes.find? (fun p => n%p==0) with
      | some p => p :: factors k (n/p)
      | none => [n]

lemma factors_ok (k n : ℕ) (hn : 0<n) (bound : n<2^(k+1)) (small : n≤5040) :
    (factors k n).prod=n ∧ ∀ p∈factors k n, p.Prime := by
  induction k generalizing n with
  | zero =>
    norm_num at bound
    have : n=1 := by omega
    simp [factors,this]
  | succ k ih =>
    by_cases one : n=1
    · simp [factors,one]
    rw [factors,if_neg one]
    cases e : primes.find? (fun p => n%p==0) with
    | none =>
      simp only [List.prod_cons,List.prod_nil,mul_one,List.mem_singleton,forall_eq, true_and]
      by_contra composite
      have hp : n.minFac.Prime := Nat.minFac_prime one
      have hs := Nat.minFac_sq_le_self hn composite
      have hm : n.minFac < 71 := by nlinarith
      have miss := (List.find?_eq_none.mp e) n.minFac ((table ⟨_,hm⟩).mp hp)
      simp [Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd n)] at miss
    | some p =>
      have hp := listed (List.mem_of_find?_eq_some e)
      have eqmod := List.find?_some e
      have dvd : p ∣ n := Nat.dvd_of_mod_eq_zero ((beq_iff_eq).mp eqmod)
      have pos := Nat.div_pos (Nat.le_of_dvd hn dvd) hp.pos
      have hmore : n/p < 2^(k+1) := by
        apply (Nat.div_lt_iff_lt_mul hp.pos).mpr
        exact bound.trans_le (by rw [pow_succ]; exact Nat.mul_le_mul_left _ hp.two_le)
      obtain ⟨prod,allp⟩ := ih (n/p) pos hmore ((Nat.div_le_self _ _).trans small)
      constructor
      · simpa [prod,Nat.mul_div_cancel' dvd]
      · intro r hr
        rcases List.mem_cons.mp hr with rfl|mem
        · exact hp
        · exact allp r mem

def factorSigma (n : ℕ) : ℕ :=
  let l := factors 13 n
  ∏ p ∈ l.toFinset, ∑ i ∈ range (l.count p+1), p^i

lemma sigma_le (n : ℕ) (hn : 0<n) (small : n≤5040) : σ 1 n ≤ factorSigma n := by
  obtain ⟨prod,prime⟩ := factors_ok 13 n hn (by norm_num; omega) small
  have perm := Nat.primeFactorsList_unique prod prime
  have sets : (factors 13 n).toFinset=n.primeFactors := by
    ext p; simpa only [Nat.primeFactors,List.mem_toFinset] using (perm.mem_iff (a := p))
  rw [sigma_one_apply,Nat.sum_divisors hn.ne',factorSigma,sets]
  simp only [List.perm_iff_count.mp perm,Nat.primeFactorsList_count_eq,le_refl]

def checks (s bound : ℕ) : ℕ → Bool
  | 0 => true
  | k+1 => decide (factorSigma (s+k) ≤ bound) && checks s bound k

lemma in_checks {s n bound k : ℕ} (h : checks s bound k=true) (lo : s≤n) (hi : n<s+k) :
    factorSigma n≤bound := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [checks,Bool.and_eq_true,decide_eq_true_eq] at h
    by_cases e : n=s+k
    · simpa [e] using h.1
    · exact ih h.2 (by omega)

def floorH : ℕ → ℕ
  | 0 => 0
  | k+1 => floorH k + 10000000/(k+1)

lemma floorH_le (n : ℕ) : (floorH n : ℚ)/10000000 ≤ harmonic n := by
  induction n with
  | zero => norm_num [floorH]
  | succ n ih =>
    rw [floorH,harmonic_succ,Nat.cast_add,add_div]
    apply add_le_add ih
    have h := Nat.div_mul_le_self 10000000 (n+1)
    have hc : (↑(10000000/(n+1) : ℕ) : ℚ)*(n+1)≤10000000 := by exact_mod_cast h
    rw [div_le_iff₀ (by norm_num)]
    rw [←div_eq_inv_mul,le_div_iff₀ (by positivity)]
    simpa only [Nat.cast_add,Nat.cast_one] using hc

lemma harmonic_mono : Monotone harmonic := by
  apply monotone_nat_of_le_succ
  intro n
  rw [harmonic_succ]
  exact le_add_of_nonneg_right (by positivity)

def lowerValue (q : ℚ) := q + (∑ i ∈ range 24, q^i/(i.factorial : ℚ)) *
    (2*∑ i ∈ range 12, ((q-1)/(q+1))^(2*i+1)/((2*i+1 : ℕ) : ℚ))

lemma packet {s k b h n : ℕ} (lo : s≤n) (hi : n<s+k) (hn : 0<n) (hmax : n≤5040)
    (hs : checks s b k=true) (hv : floorH s=h)
    (one : (1:ℚ)≤h/10000000) (gap : (b:ℚ)<lowerValue (h/10000000)) :
    ∃ q : ℚ, 1≤q ∧ q≤harmonic n ∧ (σ 1 n : ℚ)<lowerValue q := by
  refine ⟨(h:ℚ)/10000000,one,?_,?_⟩
  · rw [←hv]; exact (floorH_le s).trans (harmonic_mono lo)
  · exact lt_of_le_of_lt (by exact_mod_cast (sigma_le n hn hmax).trans (in_checks hs lo hi)) gap

lemma checks_cat (s b a k : ℕ) (left : checks s b a=true) (right : checks (s+a) b k=true) :
    checks s b (a+k)=true := by
  induction k with
  | zero => simpa using left
  | succ k ih =>
    simp only [checks,Bool.and_eq_true] at right
    rw [Nat.add_succ,checks,Bool.and_eq_true]
    change decide (factorSigma (s+(a+k))≤b)=true ∧ checks s b (a+k)=true
    exact ⟨by simpa only [Nat.add_assoc] using right.1,ih right.2⟩

end OMA.LagariasFinite

open OMA.LagariasFinite in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : OMA.R_RiemannHypothesis_lagarias_criterion_R1_H1_R1.H2 := by
  intro n low high
  by_cases h0 : n<3
  · apply packet (s := 2) (k := 1) (b := 3) (h := 15000000) (by omega) (by omega) (by omega) high
    · exact (by decide +kernel)
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h1 : n<4
  · apply packet (s := 3) (k := 1) (b := 4) (h := 18333333) (by omega) (by omega) (by omega) high
    · exact (by decide +kernel)
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h2 : n<6
  · apply packet (s := 4) (k := 2) (b := 7) (h := 20833333) (by omega) (by omega) (by omega) high
    · exact (by decide +kernel)
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h3 : n<8
  · apply packet (s := 6) (k := 2) (b := 12) (h := 24499999) (by omega) (by omega) (by omega) high
    · exact (by decide +kernel)
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h4 : n<10
  · apply packet (s := 8) (k := 2) (b := 15) (h := 27178570) (by omega) (by omega) (by omega) high
    · exact (by decide +kernel)
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h5 : n<12
  · apply packet (s := 10) (k := 2) (b := 18) (h := 29289681) (by omega) (by omega) (by omega) high
    · exact (by decide +kernel)
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h6 : n<16
  · apply packet (s := 12) (k := 4) (b := 28) (h := 31032104) (by omega) (by omega) (by omega) high
    · exact (by decide +kernel)
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h7 : n<20
  · apply packet (s := 16) (k := 4) (b := 39) (h := 33807285) (by omega) (by omega) (by omega) high
    · exact (by decide +kernel)
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h8 : n<24
  · apply packet (s := 20) (k := 4) (b := 42) (h := 35977390) (by omega) (by omega) (by omega) high
    · exact (by decide +kernel)
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h9 : n<30
  · apply packet (s := 24) (k := 6) (b := 60) (h := 37759573) (by omega) (by omega) (by omega) high
    · exact (by decide +kernel)
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h10 : n<36
  · apply packet (s := 30) (k := 6) (b := 72) (h := 39949860) (by omega) (by omega) (by omega) high
    · exact (by decide +kernel)
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h11 : n<48
  · apply packet (s := 36) (k := 12) (b := 96) (h := 41745578) (by omega) (by omega) (by omega) high
    · exact (by decide +kernel)
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h12 : n<60
  · apply packet (s := 48) (k := 12) (b := 124) (h := 44587953) (by omega) (by omega) (by omega) high
    · exact (by decide +kernel)
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h13 : n<72
  · apply packet (s := 60) (k := 12) (b := 168) (h := 46798680) (by omega) (by omega) (by omega) high
    · exact (by decide +kernel)
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h14 : n<84
  · apply packet (s := 72) (k := 12) (b := 195) (h := 48608073) (by omega) (by omega) (by omega) high
    · exact (by decide +kernel)
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h15 : n<96
  · apply packet (s := 84) (k := 12) (b := 234) (h := 50139697) (by omega) (by omega) (by omega) high
    · exact (by decide +kernel)
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h16 : n<120
  · apply packet (s := 96) (k := 24) (b := 280) (h := 51467593) (by omega) (by omega) (by omega) high
    · exact (by decide +kernel)
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h17 : n<144
  · apply packet (s := 120) (k := 24) (b := 360) (h := 53688633) (by omega) (by omega) (by omega) high
    · exact (by decide +kernel)
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h18 : n<168
  · apply packet (s := 144) (k := 24) (b := 403) (h := 55504911) (by omega) (by omega) (by omega) high
    · exact (by decide +kernel)
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h19 : n<180
  · apply packet (s := 168) (k := 12) (b := 480) (h := 57041459) (by omega) (by omega) (by omega) high
    · exact (by decide +kernel)
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h20 : n<210
  · apply packet (s := 180) (k := 30) (b := 546) (h := 57729401) (by omega) (by omega) (by omega) high
    · exact (by decide +kernel)
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h21 : n<240
  · apply packet (s := 210) (k := 30) (b := 600) (h := 59266934) (by omega) (by omega) (by omega) high
    · exact (by decide +kernel)
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h22 : n<288
  · apply packet (s := 240) (k := 48) (b := 744) (h := 60599262) (by omega) (by omega) (by omega) high
    · exact (checks_cat 240 744 24 24 (by decide +kernel) (by decide +kernel))
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h23 : n<336
  · apply packet (s := 288) (k := 48) (b := 868) (h := 62418987) (by omega) (by omega) (by omega) high
    · exact (checks_cat 288 868 24 24 (by decide +kernel) (by decide +kernel))
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h24 : n<360
  · apply packet (s := 336) (k := 24) (b := 992) (h := 63957994) (by omega) (by omega) (by omega) high
    · exact (by decide +kernel)
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h25 : n<420
  · apply packet (s := 360) (k := 60) (b := 1170) (h := 64646919) (by omega) (by omega) (by omega) high
    · exact (checks_cat 360 1170 30 30 (by decide +kernel) (by decide +kernel))
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h26 : n<480
  · apply packet (s := 420) (k := 60) (b := 1344) (h := 66186413) (by omega) (by omega) (by omega) high
    · exact (checks_cat 420 1344 30 30 (by decide +kernel) (by decide +kernel))
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h27 : n<540
  · apply packet (s := 480) (k := 60) (b := 1560) (h := 67520211) (by omega) (by omega) (by omega) high
    · exact (checks_cat 480 1560 30 30 (by decide +kernel) (by decide +kernel))
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h28 : n<630
  · apply packet (s := 540) (k := 90) (b := 1860) (h := 68696853) (by omega) (by omega) (by omega) high
    · exact (checks_cat 540 1860 45 45 (checks_cat 540 1860 22 23 (by decide +kernel) (by decide +kernel)) (checks_cat 585 1860 22 23 (by decide +kernel) (by decide +kernel)))
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h29 : n<720
  · apply packet (s := 630) (k := 90) (b := 2016) (h := 70236998) (by omega) (by omega) (by omega) high
    · exact (checks_cat 630 2016 45 45 (checks_cat 630 2016 22 23 (by decide +kernel) (by decide +kernel)) (checks_cat 675 2016 22 23 (by decide +kernel) (by decide +kernel)))
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h30 : n<840
  · apply packet (s := 720) (k := 120) (b := 2418) (h := 71571273) (by omega) (by omega) (by omega) high
    · exact (checks_cat 720 2418 60 60 (checks_cat 720 2418 30 30 (by decide +kernel) (by decide +kernel)) (checks_cat 780 2418 30 30 (by decide +kernel) (by decide +kernel)))
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h31 : n<960
  · apply packet (s := 840) (k := 120) (b := 2880) (h := 73111729) (by omega) (by omega) (by omega) high
    · exact (checks_cat 840 2880 60 60 (checks_cat 840 2880 30 30 (by decide +kernel) (by decide +kernel)) (checks_cat 900 2880 30 30 (by decide +kernel) (by decide +kernel)))
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h32 : n<1080
  · apply packet (s := 960) (k := 120) (b := 3224) (h := 74446240) (by omega) (by omega) (by omega) high
    · exact (checks_cat 960 3224 60 60 (checks_cat 960 3224 30 30 (by decide +kernel) (by decide +kernel)) (checks_cat 1020 3224 30 30 (by decide +kernel) (by decide +kernel)))
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h33 : n<1260
  · apply packet (s := 1080) (k := 180) (b := 3844) (h := 75623432) (by omega) (by omega) (by omega) high
    · exact (checks_cat 1080 3844 90 90 (checks_cat 1080 3844 45 45 (checks_cat 1080 3844 22 23 (by decide +kernel) (by decide +kernel)) (checks_cat 1125 3844 22 23 (by decide +kernel) (by decide +kernel))) (checks_cat 1170 3844 45 45 (checks_cat 1170 3844 22 23 (by decide +kernel) (by decide +kernel)) (checks_cat 1215 3844 22 23 (by decide +kernel) (by decide +kernel))))
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h34 : n<1440
  · apply packet (s := 1260) (k := 180) (b := 4368) (h := 77164193) (by omega) (by omega) (by omega) high
    · exact (checks_cat 1260 4368 90 90 (checks_cat 1260 4368 45 45 (checks_cat 1260 4368 22 23 (by decide +kernel) (by decide +kernel)) (checks_cat 1305 4368 22 23 (by decide +kernel) (by decide +kernel))) (checks_cat 1350 4368 45 45 (checks_cat 1350 4368 22 23 (by decide +kernel) (by decide +kernel)) (checks_cat 1395 4368 22 23 (by decide +kernel) (by decide +kernel))))
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h35 : n<1680
  · apply packet (s := 1440) (k := 240) (b := 5082) (h := 78498926) (by omega) (by omega) (by omega) high
    · exact (checks_cat 1440 5082 120 120 (checks_cat 1440 5082 60 60 (checks_cat 1440 5082 30 30 (by decide +kernel) (by decide +kernel)) (checks_cat 1500 5082 30 30 (by decide +kernel) (by decide +kernel))) (checks_cat 1560 5082 60 60 (checks_cat 1560 5082 30 30 (by decide +kernel) (by decide +kernel)) (checks_cat 1620 5082 30 30 (by decide +kernel) (by decide +kernel))))
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h36 : n<1980
  · apply packet (s := 1680) (k := 300) (b := 6120) (h := 80039823) (by omega) (by omega) (by omega) high
    · exact (checks_cat 1680 6120 150 150 (checks_cat 1680 6120 75 75 (checks_cat 1680 6120 37 38 (checks_cat 1680 6120 18 19 (by decide +kernel) (by decide +kernel)) (checks_cat 1717 6120 19 19 (by decide +kernel) (by decide +kernel))) (checks_cat 1755 6120 37 38 (checks_cat 1755 6120 18 19 (by decide +kernel) (by decide +kernel)) (checks_cat 1792 6120 19 19 (by decide +kernel) (by decide +kernel)))) (checks_cat 1830 6120 75 75 (checks_cat 1830 6120 37 38 (checks_cat 1830 6120 18 19 (by decide +kernel) (by decide +kernel)) (checks_cat 1867 6120 19 19 (by decide +kernel) (by decide +kernel))) (checks_cat 1905 6120 37 38 (checks_cat 1905 6120 18 19 (by decide +kernel) (by decide +kernel)) (checks_cat 1942 6120 19 19 (by decide +kernel) (by decide +kernel)))))
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h37 : n<2160
  · apply packet (s := 1980) (k := 180) (b := 6944) (h := 81682252) (by omega) (by omega) (by omega) high
    · exact (checks_cat 1980 6944 90 90 (checks_cat 1980 6944 45 45 (checks_cat 1980 6944 22 23 (by decide +kernel) (by decide +kernel)) (checks_cat 2025 6944 22 23 (by decide +kernel) (by decide +kernel))) (checks_cat 2070 6944 45 45 (checks_cat 2070 6944 22 23 (by decide +kernel) (by decide +kernel)) (checks_cat 2115 6944 22 23 (by decide +kernel) (by decide +kernel))))
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h38 : n<2520
  · apply packet (s := 2160) (k := 360) (b := 7812) (h := 82552069) (by omega) (by omega) (by omega) high
    · exact (checks_cat 2160 7812 180 180 (checks_cat 2160 7812 90 90 (checks_cat 2160 7812 45 45 (checks_cat 2160 7812 22 23 (by decide +kernel) (by decide +kernel)) (checks_cat 2205 7812 22 23 (by decide +kernel) (by decide +kernel))) (checks_cat 2250 7812 45 45 (checks_cat 2250 7812 22 23 (by decide +kernel) (by decide +kernel)) (checks_cat 2295 7812 22 23 (by decide +kernel) (by decide +kernel)))) (checks_cat 2340 7812 90 90 (checks_cat 2340 7812 45 45 (checks_cat 2340 7812 22 23 (by decide +kernel) (by decide +kernel)) (checks_cat 2385 7812 22 23 (by decide +kernel) (by decide +kernel))) (checks_cat 2430 7812 45 45 (checks_cat 2430 7812 22 23 (by decide +kernel) (by decide +kernel)) (checks_cat 2475 7812 22 23 (by decide +kernel) (by decide +kernel)))))
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h39 : n<2880
  · apply packet (s := 2520) (k := 360) (b := 9360) (h := 84093071) (by omega) (by omega) (by omega) high
    · exact (checks_cat 2520 9360 180 180 (checks_cat 2520 9360 90 90 (checks_cat 2520 9360 45 45 (checks_cat 2520 9360 22 23 (by decide +kernel) (by decide +kernel)) (checks_cat 2565 9360 22 23 (by decide +kernel) (by decide +kernel))) (checks_cat 2610 9360 45 45 (checks_cat 2610 9360 22 23 (by decide +kernel) (by decide +kernel)) (checks_cat 2655 9360 22 23 (by decide +kernel) (by decide +kernel)))) (checks_cat 2700 9360 90 90 (checks_cat 2700 9360 45 45 (checks_cat 2700 9360 22 23 (by decide +kernel) (by decide +kernel)) (checks_cat 2745 9360 22 23 (by decide +kernel) (by decide +kernel))) (checks_cat 2790 9360 45 45 (checks_cat 2790 9360 22 23 (by decide +kernel) (by decide +kernel)) (checks_cat 2835 9360 22 23 (by decide +kernel) (by decide +kernel)))))
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h40 : n<3360
  · apply packet (s := 2880) (k := 480) (b := 10890) (h := 85427959) (by omega) (by omega) (by omega) high
    · exact (checks_cat 2880 10890 240 240 (checks_cat 2880 10890 120 120 (checks_cat 2880 10890 60 60 (checks_cat 2880 10890 30 30 (by decide +kernel) (by decide +kernel)) (checks_cat 2940 10890 30 30 (by decide +kernel) (by decide +kernel))) (checks_cat 3000 10890 60 60 (checks_cat 3000 10890 30 30 (by decide +kernel) (by decide +kernel)) (checks_cat 3060 10890 30 30 (by decide +kernel) (by decide +kernel)))) (checks_cat 3120 10890 120 120 (checks_cat 3120 10890 60 60 (checks_cat 3120 10890 30 30 (by decide +kernel) (by decide +kernel)) (checks_cat 3180 10890 30 30 (by decide +kernel) (by decide +kernel))) (checks_cat 3240 10890 60 60 (checks_cat 3240 10890 30 30 (by decide +kernel) (by decide +kernel)) (checks_cat 3300 10890 30 30 (by decide +kernel) (by decide +kernel)))))
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h41 : n<3780
  · apply packet (s := 3360) (k := 420) (b := 12493) (h := 86968970) (by omega) (by omega) (by omega) high
    · exact (checks_cat 3360 12493 210 210 (checks_cat 3360 12493 105 105 (checks_cat 3360 12493 52 53 (checks_cat 3360 12493 26 26 (by decide +kernel) (by decide +kernel)) (checks_cat 3412 12493 26 27 (by decide +kernel) (by decide +kernel))) (checks_cat 3465 12493 52 53 (checks_cat 3465 12493 26 26 (by decide +kernel) (by decide +kernel)) (checks_cat 3517 12493 26 27 (by decide +kernel) (by decide +kernel)))) (checks_cat 3570 12493 105 105 (checks_cat 3570 12493 52 53 (checks_cat 3570 12493 26 26 (by decide +kernel) (by decide +kernel)) (checks_cat 3622 12493 26 27 (by decide +kernel) (by decide +kernel))) (checks_cat 3675 12493 52 53 (checks_cat 3675 12493 26 26 (by decide +kernel) (by decide +kernel)) (checks_cat 3727 12493 26 27 (by decide +kernel) (by decide +kernel)))))
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h42 : n<4200
  · apply packet (s := 3780) (k := 420) (b := 14040) (h := 88146426) (by omega) (by omega) (by omega) high
    · exact (checks_cat 3780 14040 210 210 (checks_cat 3780 14040 105 105 (checks_cat 3780 14040 52 53 (checks_cat 3780 14040 26 26 (by decide +kernel) (by decide +kernel)) (checks_cat 3832 14040 26 27 (by decide +kernel) (by decide +kernel))) (checks_cat 3885 14040 52 53 (checks_cat 3885 14040 26 26 (by decide +kernel) (by decide +kernel)) (checks_cat 3937 14040 26 27 (by decide +kernel) (by decide +kernel)))) (checks_cat 3990 14040 105 105 (checks_cat 3990 14040 52 53 (checks_cat 3990 14040 26 26 (by decide +kernel) (by decide +kernel)) (checks_cat 4042 14040 26 27 (by decide +kernel) (by decide +kernel))) (checks_cat 4095 14040 52 53 (checks_cat 4095 14040 26 26 (by decide +kernel) (by decide +kernel)) (checks_cat 4147 14040 26 27 (by decide +kernel) (by decide +kernel)))))
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h43 : n<4680
  · apply packet (s := 4200) (k := 480) (b := 16128) (h := 89199693) (by omega) (by omega) (by omega) high
    · exact (checks_cat 4200 16128 240 240 (checks_cat 4200 16128 120 120 (checks_cat 4200 16128 60 60 (checks_cat 4200 16128 30 30 (by decide +kernel) (by decide +kernel)) (checks_cat 4260 16128 30 30 (by decide +kernel) (by decide +kernel))) (checks_cat 4320 16128 60 60 (checks_cat 4320 16128 30 30 (by decide +kernel) (by decide +kernel)) (checks_cat 4380 16128 30 30 (by decide +kernel) (by decide +kernel)))) (checks_cat 4440 16128 120 120 (checks_cat 4440 16128 60 60 (checks_cat 4440 16128 30 30 (by decide +kernel) (by decide +kernel)) (checks_cat 4500 16128 30 30 (by decide +kernel) (by decide +kernel))) (checks_cat 4560 16128 60 60 (checks_cat 4560 16128 30 30 (by decide +kernel) (by decide +kernel)) (checks_cat 4620 16128 30 30 (by decide +kernel) (by decide +kernel)))))
    · decide +kernel
    · decide +kernel
    · decide +kernel
  by_cases h44 : n<5040
  · apply packet (s := 4680) (k := 360) (b := 16380) (h := 90281471) (by omega) (by omega) (by omega) high
    · exact (checks_cat 4680 16380 180 180 (checks_cat 4680 16380 90 90 (checks_cat 4680 16380 45 45 (checks_cat 4680 16380 22 23 (by decide +kernel) (by decide +kernel)) (checks_cat 4725 16380 22 23 (by decide +kernel) (by decide +kernel))) (checks_cat 4770 16380 45 45 (checks_cat 4770 16380 22 23 (by decide +kernel) (by decide +kernel)) (checks_cat 4815 16380 22 23 (by decide +kernel) (by decide +kernel)))) (checks_cat 4860 16380 90 90 (checks_cat 4860 16380 45 45 (checks_cat 4860 16380 22 23 (by decide +kernel) (by decide +kernel)) (checks_cat 4905 16380 22 23 (by decide +kernel) (by decide +kernel))) (checks_cat 4950 16380 45 45 (checks_cat 4950 16380 22 23 (by decide +kernel) (by decide +kernel)) (checks_cat 4995 16380 22 23 (by decide +kernel) (by decide +kernel)))))
    · decide +kernel
    · decide +kernel
    · decide +kernel
  apply packet (s := 5040) (k := 1) (b := 19344) (h := 91022298) (by omega) (by omega) (by omega) high
  · exact (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
