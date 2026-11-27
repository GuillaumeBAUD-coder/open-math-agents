import FormalConjectures.ErdosProblems.«873»
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# The infinitely-often lower bound for consecutive triples of small LCM

The CRT progressions come from Erdős and Szemerédi (1980), p. 123.
We restrict the gaps to have large prime factors. This makes the gcd
sum over progression moduli small enough to bound the total overlaps.
A finite independent subfamily at each scale gives separated triples.
Combining scales and adjoining arbitrarily late blocks produces a
single increasing sequence with the required infinitely-often bound.
-/

/-
Arithmetic progressions of closely spaced triples from the construction of
Erdős and Szemerédi (https://www.renyi.hu/~p_erdos/1980-15.pdf, p. 123).
-/

open Finset

namespace LCMTripleConstruction

def period (p q : ℕ) : ℕ := p*(p+q)*q

def triple (a p q : ℕ) : ℕ → ℕ
  | 0 => a
  | 1 => a+p
  | _ => a+p+q

theorem progression_residue {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hco : p.Coprime q) :
    ∃ r < period p q, ∀ t : ℕ, p*(p+q) ∣ r+period p q*t ∧ q ∣ (r+period p q*t)+p := by
  have hC : (p*(p+q)).Coprime q :=
    Nat.coprime_mul_iff_left.2 ⟨hco,Nat.coprime_add_self_left.2 hco⟩
  let u := q-p%q
  let r := Nat.chineseRemainder hC 0 u
  have hR : (r : ℕ) < period p q :=
    Nat.chineseRemainder_lt_mul hC 0 u (by positivity) hq.ne'
  have hA : p*(p+q) ∣ (r : ℕ) := Nat.modEq_zero_iff_dvd.1 r.property.1
  have hU : q ∣ u+p := by
    have hmod := Nat.mod_lt p hq
    have hsum := Nat.mod_add_div p q
    refine ⟨p/q+1,?_⟩
    dsimp [u]
    rw [mul_add,mul_one]
    omega
  have hB : q ∣ (r : ℕ)+p :=
    Nat.modEq_zero_iff_dvd.1 ((r.property.2.add_right _).trans hU.modEq_zero_nat)
  refine ⟨r,hR,?_⟩
  intro t
  have hPD : p*(p+q) ∣ period p q*t := by unfold period; exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hQD : q ∣ period p q*t := by unfold period; exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  refine ⟨dvd_add hA hPD,?_⟩
  rw [add_right_comm]
  exact dvd_add hB hQD

theorem explicit_multiple {p q c d : ℕ} (h : p*c+1 = q*d) :
    let a := p*(p+q)*c
    let L := period p q*c*d*(c+d)
    (Finset.range 3).lcm (triple a p q) ∣ L ∧
      period p q*L = a*(a+p)*(a+p+q) := by
  let a := p*(p+q)*c
  let L := period p q*c*d*(c+d)
  change (Finset.range 3).lcm (triple a p q) ∣ L ∧ period p q*L = a*(a+p)*(a+p+q)
  have hb : a+p = p*q*(c+d) := by
    dsimp [a]
    calc
      _ = p*q*c + p*(p*c+1) := by ring
      _ = _ := by rw [h]; ring
  have hc : a+p+q = (p+q)*q*d := by
    dsimp [a]
    calc
      _ = (p+q)*(p*c+1) := by ring
      _ = _ := by rw [h]; ring
  constructor
  · rw [Finset.lcm_dvd_iff]
    intro i hi
    have hlt := Finset.mem_range.1 hi
    interval_cases i
    · change a ∣ L
      exact ⟨q*d*(c+d),by dsimp [a,L,period]; ring⟩
    · change a+p ∣ L
      rw [hb]
      exact ⟨(p+q)*c*d,by dsimp [L,period]; ring⟩
    · change a+p+q ∣ L
      rw [hc]
      exact ⟨p*c*(c+d),by dsimp [L,period]; ring⟩
  · rw [hc,hb]
    dsimp [a,L,period]
    ring

theorem lcm_bound_of_congruences {s V a p q : ℕ} (hs : 0 < s) (ha : 0 < a)
    (hp : s ≤ p) (hq : s ≤ q) (hEnd : a+p+q ≤ V*s) (hco : p.Coprime q)
    (hDiv : p*(p+q) ∣ a) (hMid : q ∣ a+p) :
    (Finset.range 3).lcm (triple a p q) ≤ V^3 := by
  obtain ⟨c,rfl⟩ := hDiv
  let a := p*(p+q)*c
  have hMid' : q ∣ p*c+1 := by
    have he : a+p = p*((p+q)*c+1) := by dsimp [a]; ring
    change q ∣ a+p at hMid
    rw [he] at hMid
    have hq' := hco.symm.dvd_of_dvd_mul_left hMid
    have he' : (p+q)*c+1 = q*c+(p*c+1) := by ring
    rw [he'] at hq'
    simpa only [Nat.add_sub_cancel_left] using Nat.dvd_sub hq' (dvd_mul_right q c)
  obtain ⟨d,hd⟩ := hMid'
  let L := period p q*c*d*(c+d)
  obtain ⟨hL,hprod⟩ := explicit_multiple hd
  have hC : 0 < c := by
    by_contra! hc
    have he : c = 0 := by omega
    simp [he] at ha
  have hD : 0 < d := by
    by_contra! h
    have he : d = 0 := by omega
    simp [he] at hd
  have hp₀ : 0 < p := hs.trans_le hp
  have hq₀ : 0 < q := hs.trans_le hq
  have hLpos : 0 < L := by dsimp [L,period]; positivity
  apply (Nat.le_of_dvd hLpos hL).trans
  have hPeriod : s^3 ≤ period p q := by
    unfold period
    have hh : s ≤ p+q := hp.trans (Nat.le_add_right _ _)
    rw [pow_succ,pow_two]
    exact Nat.mul_le_mul (Nat.mul_le_mul hp hh) hq
  change a+p+q ≤ V*s at hEnd
  have hA : a ≤ V*s := (Nat.le_add_right a (p+q)).trans (by simpa [add_assoc] using hEnd)
  have hB : a+p ≤ V*s := (Nat.le_add_right (a+p) q).trans hEnd
  apply Nat.le_of_mul_le_mul_left _ (by positivity : 0 < s^3)
  calc
    s^3 * L ≤ period p q * L := Nat.mul_le_mul_right L hPeriod
    _ = a*(a+p)*(a+p+q) := hprod
    _ ≤ ((V*s)*(V*s))*(V*s) := Nat.mul_le_mul (Nat.mul_le_mul hA hB) hEnd
    _ = (V*s)^3 := by ring
    _ = s^3 * V^3 := by ring

end LCMTripleConstruction

/-
# A prime window estimate for low-LCM triples

Chebyshev's bounds give enough primes in a fixed multiplicative window to construct a
positive-density family of integers with a large prime factor.
-/

open Filter
open scoped Topology

namespace LCMPrimeWindow

theorem window : ∀ᶠ t : ℝ in atTop,
    t / Real.log t ≤
      (Nat.primeCounting ⌊32*t⌋₊ : ℝ) - (Nat.primeCounting ⌊t⌋₊ : ℝ) := by
  filter_upwards [eventually_ge_atTop (32 : ℝ),
    Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num)] with t ht hUpper
  have htpos : 0 < t := by linarith
  have htlog : 0 < Real.log t := Real.log_pos (by linarith)
  have hlog2Upper : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hlog2Lower : (1/2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2⁻¹ by norm_num)
    rw [Real.log_inv] at h
    norm_num at h ⊢
    linarith
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2*2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith
  have hpiUpper : (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ 3*t / Real.log t := by
    exact hUpper.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) htpos.le) htlog.le)
  have hlog32 : Real.log (32*t) ≤ 2 * Real.log t := by
    rw [Real.log_mul (by norm_num) (ne_of_gt htpos)]
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 32) ht
    linarith
  have hlog32pos : 0 < Real.log (32*t) := Real.log_pos (by linarith)
  have hupperAux : Real.log (32*t + 2) ≤ 4*t + 7 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (32*t+2)/8 by linarith)
    rw [Real.log_div (by linarith : 32*t+2 ≠ 0) (by norm_num : (8 : ℝ) ≠ 0)] at h
    have h8 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num)
    linarith
  have hnum : 8*t ≤ (32*t-1)*Real.log 2 - Real.log (32*t+2) := by
    have h := mul_le_mul_of_nonneg_left hlog2Lower (show 0 ≤ 32*t-1 by linarith)
    linarith
  have hpiLower : 4*t / Real.log t ≤ (Nat.primeCounting ⌊32*t⌋₊ : ℝ) := calc
    4*t / Real.log t = 8*t / (2*Real.log t) := by
      field_simp
      ring
    _ ≤ 8*t / Real.log (32*t) :=
      div_le_div_of_nonneg_left (by positivity) hlog32pos hlog32
    _ ≤ ((32*t-1)*Real.log 2 - Real.log (32*t+2)) / Real.log (32*t) :=
      div_le_div_of_nonneg_right hnum hlog32pos.le
    _ ≤ _ := Chebyshev.pi_ge' (by linarith)
  linarith [show 4*t / Real.log t = 3*t / Real.log t + t / Real.log t by ring]


noncomputable def primeWindow (t : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊32*t⌋₊ \ Nat.primesLE ⌊t⌋₊

theorem mem_primeWindow {t : ℝ} (ht : 0 ≤ t) {p : ℕ} :
    p ∈ primeWindow t ↔ p.Prime ∧ t < (p : ℝ) ∧ (p : ℝ) ≤ 32*t := by
  simp only [primeWindow, Finset.mem_sdiff, Nat.mem_primesLE,
    Nat.le_floor_iff ht, Nat.le_floor_iff (show 0 ≤ 32*t by positivity)]
  constructor
  · rintro ⟨⟨hpt, hp⟩, hnot⟩
    exact ⟨hp, lt_of_not_ge (fun h => hnot ⟨h, hp⟩), hpt⟩
  · rintro ⟨hp, hlt, hle⟩
    exact ⟨⟨hle, hp⟩, fun h => hlt.not_ge h.1⟩

theorem card_primeWindow {t : ℝ} (ht : 0 ≤ t) :
    ((primeWindow t).card : ℝ) =
      (Nat.primeCounting ⌊32*t⌋₊ : ℝ) - (Nat.primeCounting ⌊t⌋₊ : ℝ) := by
  have h := Nat.primesLE_mono (Nat.floor_mono (show t ≤ 32*t by linarith))
  rw [primeWindow, Finset.card_sdiff_of_subset h, Nat.cast_sub (Finset.card_le_card h)]
  simp

noncomputable def bigFactors (s : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc s (32*s)).filter
    (fun n => ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (s : ℝ) ^ (99/100 : ℝ) < (p : ℝ))

theorem bigFactors_lower : ∀ᶠ s : ℕ in atTop,
    (s : ℝ)/100 ≤ ((bigFactors s).card : ℝ) := by
  classical
  obtain ⟨T, hT⟩ := eventually_atTop.1 window
  have hlim : Tendsto (fun s : ℕ => (s : ℝ) ^ (99/100 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 99/100)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2 : ℕ), hlim.eventually (eventually_ge_atTop T)]
    with s hs hsT
  have hs1 : 1 < (s : ℝ) := by exact_mod_cast (show 1 < s by omega)
  have hs0 : 0 < (s : ℝ) := by linarith
  have hslog : 0 < Real.log s := Real.log_pos hs1
  let R := ⌊(s : ℝ) ^ (1/100 : ℝ)⌋₊
  let Q (i : ℕ) := (s : ℝ)/(i+1:ℕ)
  let W (i : ℕ) := primeWindow (Q i)
  let D := (Finset.range R).sigma W
  have hdiv (i : ℕ) (hi : i ∈ Finset.range R) :
      (s : ℝ) ^ (99/100 : ℝ) ≤ Q i := by
    have hi' : (i+1 : ℕ) ≤ R := Finset.mem_range.1 hi
    have hc : ((i+1 : ℕ) : ℝ) ≤ (s : ℝ) ^ (1/100 : ℝ) :=
      (Nat.le_floor_iff (by positivity)).1 hi'
    calc
      (s : ℝ) ^ (99/100 : ℝ) = (s : ℝ) / (s : ℝ) ^ (1/100 : ℝ) := by
        calc
          _ = (s : ℝ) ^ (1 - 1/100 : ℝ) := by rw [show (1 - 1/100 : ℝ) = 99/100 by norm_num]
          _ = _ := by rw [Real.rpow_sub hs0, Real.rpow_one]
      _ ≤ _ := div_le_div_of_nonneg_left hs0.le (by positivity) hc
  have hsmall (i : ℕ) (hi : i ∈ Finset.range R) :
      ((i+1 : ℕ) : ℝ) < (s : ℝ) ^ (99/100 : ℝ) :=
    ((Nat.le_floor_iff (by positivity)).1 (Finset.mem_range.1 hi)).trans_lt
      (Real.rpow_lt_rpow_of_exponent_lt hs1 (by norm_num))
  have hprime (z : Sigma (fun _ : ℕ => ℕ)) (hz : z ∈ D) :
      z.2.Prime ∧ Q z.1 < (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ 32*(Q z.1) :=
    (mem_primeWindow (by dsimp [Q]; positivity)).1 (Finset.mem_sigma.1 hz).2
  have hiD : D.card ≤ (bigFactors s).card := by
    apply Finset.card_le_card_of_injOn (fun z => (z.1+1)*z.2)
    · intro z hz
      have hp := hprime z hz
      have hbig := (hdiv z.1 (Finset.mem_sigma.1 hz).1).trans_lt hp.2.1
      have hnLo := (div_lt_iff₀ (by positivity : 0 < ((z.1+1:ℕ):ℝ))).1 hp.2.1
      have hnHi := hp.2.2
      dsimp [Q] at hnHi
      rw [← mul_div_assoc] at hnHi
      have hnHi := (le_div_iff₀ (by positivity : 0 < ((z.1+1:ℕ):ℝ))).1 hnHi
      change (z.1+1)*z.2 ∈ bigFactors s
      unfold bigFactors
      refine Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨?_, ?_⟩,
        z.2, hp.1, dvd_mul_left _ _, hbig⟩
      · exact_mod_cast (show (s : ℝ) < (((z.1+1)*z.2:ℕ):ℝ) by
          push_cast
          simpa [mul_comm] using hnLo)
      · exact_mod_cast (show (((z.1+1)*z.2:ℕ):ℝ) ≤ ((32*s:ℕ):ℝ) by
          push_cast
          simpa [mul_comm] using hnHi)
    · intro z hz w hw heq
      have hz0 := (Finset.mem_sigma.1 hz).1
      have hw0 := (Finset.mem_sigma.1 hw).1
      have hpz := hprime z hz
      have hpw := hprime w hw
      have hlt := (hsmall w.1 hw0).trans
        ((hdiv z.1 hz0).trans_lt hpz.2.1)
      have hltNat : w.1+1 < z.2 := by exact_mod_cast hlt
      change (z.1+1)*z.2 = (w.1+1)*w.2 at heq
      have hdvd : z.2 ∣ (w.1+1)*w.2 := by
        rw [← heq]
        exact dvd_mul_left _ _
      have hprimeDvd : z.2 ∣ w.2 := (hpz.1.dvd_mul.1 hdvd).resolve_left
        (fun hd => hltNat.not_ge (Nat.le_of_dvd (by positivity) hd))
      have h2 : z.2 = w.2 := (Nat.prime_dvd_prime_iff_eq hpz.1 hpw.1).1 hprimeDvd
      have h1 := Nat.eq_of_mul_eq_mul_right (hpw.1.pos) (by simpa [h2] using heq)
      exact Sigma.ext (by omega) (heq_of_eq h2)
  have hsum : (s : ℝ) / Real.log s * (harmonic R : ℝ) ≤ (D.card : ℝ) := by
    simp only [D, Finset.card_sigma, Nat.cast_sum, harmonic, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hT' := hT (Q i) (hsT.trans (hdiv i hi))
    rw [← card_primeWindow (by dsimp [Q]; positivity)] at hT'
    refine le_trans ?_ hT'
    have hQ1 : 1 < Q i := by
      exact (Real.one_lt_rpow hs1 (by norm_num : (0:ℝ)<99/100)).trans_le (hdiv i hi)
    have hlogQ := Real.log_le_log (by linarith : 0 < Q i)
      (div_le_self hs0.le (by exact_mod_cast (show 1 ≤ i+1 by omega)) : Q i ≤ s)
    have hdivLog : Q i / Real.log s ≤ Q i / Real.log (Q i) :=
      div_le_div_of_nonneg_left (by linarith) (Real.log_pos hQ1) hlogQ
    calc
      _ = Q i / Real.log s := by unfold Q; ring
      _ ≤ _ := hdivLog
  have hharm : (Real.log s)/100 ≤ (harmonic R : ℝ) := by
    rw [← show Real.log ((s : ℝ) ^ (1/100 : ℝ)) = Real.log s / 100 by
      rw [Real.log_rpow hs0]
      ring]
    exact log_le_harmonic_floor _ (by positivity)
  calc
    (s : ℝ)/100 = (s : ℝ) / Real.log s * (Real.log s/100) := by
      field_simp
    _ ≤ (s : ℝ) / Real.log s * (harmonic R : ℝ) :=
      mul_le_mul_of_nonneg_left hharm (by positivity)
    _ ≤ (D.card : ℝ) := hsum
    _ ≤ ((bigFactors s).card : ℝ) := by exact_mod_cast hiD

end LCMPrimeWindow

/-
# Many coprime branches at each large scale

Discard pairs whose gcd exceeds a fixed constant. Dividing the other pairs by their gcd leaves
coprime branches, with bounded multiplicity and the same designated large prime factors.
-/

open Filter
open scoped BigOperators

namespace LCMBranchDensity

theorem card_multiples {A : Finset ℕ} {N d : ℕ} (hd : 0 < d)
    (hA : ∀ a ∈ A, 0 < a ∧ a ≤ N) :
    (A.filter fun a => d ∣ a).card ≤ N/d := by
  have hcard : (A.filter fun a => d ∣ a).card ≤ (Finset.Icc 1 (N/d)).card := by
    apply Finset.card_le_card_of_injOn (fun a => a/d)
    · intro a ha
      obtain ⟨ha, hda⟩ := Finset.mem_filter.1 ha
      obtain ⟨hapos, haN⟩ := hA a ha
      change a/d ∈ Finset.Icc 1 (N/d)
      exact Finset.mem_Icc.2 ⟨Nat.div_pos (Nat.le_of_dvd hapos hda) hd,
        Nat.div_le_div_right haN⟩
    · intro a ha b hb heq
      have hda := (Finset.mem_filter.1 ha).2
      have hdb := (Finset.mem_filter.1 hb).2
      change a/d = b/d at heq
      rw [← Nat.mul_div_cancel' hda, ← Nat.mul_div_cancel' hdb, heq]
  simpa [Nat.card_Icc] using hcard

theorem card_large_gcd {A : Finset ℕ} {N D : ℕ} (hD : 0 < D)
    (hA : ∀ a ∈ A, 0 < a ∧ a ≤ N) :
    ((((A ×ˢ A).filter (fun a => D < a.1.gcd a.2)).card : ℕ) : ℝ) ≤
      (N : ℝ)^2/D := by
  classical
  let M (d : ℕ) := A.filter (fun a => d ∣ a)
  let T := (A ×ˢ A).filter (fun a => D < a.1.gcd a.2)
  have hsub : T ⊆ (Finset.Ioc D N).biUnion (fun d => M d ×ˢ M d) := by
    intro a ha
    obtain ⟨hab, hd⟩ := Finset.mem_filter.1 ha
    obtain ⟨ha, hb⟩ := Finset.mem_product.1 hab
    have hle := (Nat.gcd_le_left a.2 (hA _ ha).1).trans (hA _ ha).2
    exact Finset.mem_biUnion.2 ⟨a.1.gcd a.2, Finset.mem_Ioc.2 ⟨hd,hle⟩,
      Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨ha,Nat.gcd_dvd_left _ _⟩,
        Finset.mem_filter.2 ⟨hb,Nat.gcd_dvd_right _ _⟩⟩⟩
  have hcount : (T.card : ℝ) ≤ ∑ d ∈ Finset.Ioc D N, ((M d).card : ℝ)^2 := by
    have h := (Finset.card_le_card hsub).trans
      (Finset.card_biUnion_le (s := Finset.Ioc D N) (t := fun d => M d ×ˢ M d))
    exact_mod_cast (show T.card ≤ ∑ d ∈ Finset.Ioc D N, (M d).card^2 by
      simpa only [Finset.card_product, pow_two] using h)
  have hsec (d : ℕ) (hd : d ∈ Finset.Ioc D N) :
      ((M d).card : ℝ) ≤ (N : ℝ)/d := by
    have h := card_multiples (hD.trans (Finset.mem_Ioc.1 hd).1) hA
    exact (show ((M d).card : ℝ) ≤ ((N/d : ℕ) : ℝ) by exact_mod_cast h).trans Nat.cast_div_le
  have hsum : (∑ d ∈ Finset.Ioc D N, ((d : ℝ)^2)⁻¹) ≤ (D : ℝ)⁻¹ := by
    by_cases hDN : D ≤ N
    · exact (sum_Ioc_inv_sq_le_sub (α := ℝ) hD.ne' hDN).trans (sub_le_self _ (by positivity))
    · have he : Finset.Ioc D N = ∅ := Finset.Ioc_eq_empty (by omega)
      rw [he, Finset.sum_empty]
      positivity
  change (T.card : ℝ) ≤ _
  calc
    _ ≤ ∑ d ∈ Finset.Ioc D N, ((M d).card : ℝ)^2 := hcount
    _ ≤ ∑ d ∈ Finset.Ioc D N, ((N : ℝ)/d)^2 :=
      Finset.sum_le_sum (fun d hd => pow_le_pow_left₀ (by positivity) (hsec d hd) 2)
    _ = (N : ℝ)^2 * (∑ d ∈ Finset.Ioc D N, ((d : ℝ)^2)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [div_pow, div_eq_mul_inv]
    _ ≤ (N : ℝ)^2/D := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hsum (by positivity)

def reduce (b : ℕ × ℕ) : ℕ × ℕ :=
  (b.1/b.1.gcd b.2,b.2/b.1.gcd b.2)

theorem card_reduce {S : Finset (ℕ × ℕ)} {D : ℕ}
    (hS : ∀ b ∈ S, 0 < b.1 ∧ b.1.gcd b.2 ≤ D) :
    S.card ≤ (S.image reduce).card*D := by
  have hcount : S.card ≤ (S.image reduce ×ˢ Finset.Icc 1 D).card := by
    apply Finset.card_le_card_of_injOn (fun b => (reduce b,b.1.gcd b.2))
    · intro b hb
      change (reduce b,b.1.gcd b.2) ∈ S.image reduce ×ˢ Finset.Icc 1 D
      exact Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hb,
        Finset.mem_Icc.2 ⟨Nat.gcd_pos_of_pos_left _ (hS b hb).1, (hS b hb).2⟩⟩
    · intro a _ b _ heq
      have hg := congrArg Prod.snd heq
      have hp := congrArg (fun z : (ℕ × ℕ) × ℕ => z.1.1) heq
      have hq := congrArg (fun z : (ℕ × ℕ) × ℕ => z.1.2) heq
      change a.1.gcd a.2 = b.1.gcd b.2 at hg
      change a.1/a.1.gcd a.2 = b.1/b.1.gcd b.2 at hp
      change a.2/a.1.gcd a.2 = b.2/b.1.gcd b.2 at hq
      apply Prod.ext
      · have h := congrArg₂ (· * ·) hg hp
        simpa only [Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)] using h
      · have h := congrArg₂ (· * ·) hg hq
        simpa only [Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)] using h
  simpa [Finset.card_product, Nat.card_Icc] using hcount

def cutoff : ℕ := 2^25

def branchConstant : ℕ := 32*cutoff

theorem branch_density : ∀ᶠ s : ℕ in atTop, ∃ S : Finset (ℕ × ℕ),
    (s : ℝ)^2/20000 ≤ (S.card : ℝ) ∧
    ∀ b ∈ S, s ≤ b.1 ∧ s ≤ b.2 ∧ b.1 ≤ branchConstant*s ∧ b.2 ≤ branchConstant*s ∧
      b.1.Coprime b.2 ∧ ∃ P Q : ℕ, P.Prime ∧ Q.Prime ∧ P ∣ b.1 ∧ Q ∣ b.2 ∧
        (s : ℝ)^(99/100 : ℝ) ≤ P ∧ (s : ℝ)^(99/100 : ℝ) ≤ Q := by
  classical
  have hc0 : 0 < cutoff := by norm_num [cutoff]
  have hc1 : 1 ≤ cutoff := hc0
  have hcl : 1024/(cutoff : ℝ) ≤ 1/20000 := by norm_num [cutoff]
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.1 LCMPrimeWindow.bigFactors_lower
  have hpow : Tendsto (fun s : ℕ => (s : ℝ)^(99/100 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 99/100)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (max 1 N₀),
    hpow.eventually (eventually_gt_atTop (cutoff : ℝ))] with s hs hpow'
  let N := cutoff*s
  have hn : s ≤ N := by unfold N; exact Nat.le_mul_of_pos_left _ hc0
  have hn' : N₀ ≤ N := (le_max_right 1 N₀).trans (hs.trans hn)
  have hAcard := hN₀ N hn'
  let A := LCMPrimeWindow.bigFactors N
  let T := (A ×ˢ A).filter (fun a => cutoff < a.1.gcd a.2)
  let G := (A ×ˢ A).filter (fun a => a.1.gcd a.2 ≤ cutoff)
  let S := G.image reduce
  have hA (a : ℕ) (ha : a ∈ A) :
      N < a ∧ a ≤ 32*N ∧ ∃ p : ℕ, p.Prime ∧ p ∣ a ∧ (N : ℝ)^(99/100 : ℝ) < p := by
    have h := Finset.mem_filter.1 ha
    exact ⟨(Finset.mem_Ioc.1 h.1).1,(Finset.mem_Ioc.1 h.1).2,h.2⟩
  have hT : (T.card : ℝ) ≤ (N : ℝ)^2/20000 := by
    have h := card_large_gcd hc0 (fun a ha => ⟨Nat.zero_lt_of_lt (hA a ha).1, (hA a ha).2.1⟩)
    change (T.card : ℝ) ≤ _ at h
    push_cast at h
    refine h.trans ?_
    calc
      _ = 1024/(cutoff : ℝ)*(N : ℝ)^2 := by ring
      _ ≤ (1/20000 : ℝ)*(N : ℝ)^2 := mul_le_mul_of_nonneg_right hcl (by positivity)
      _ = _ := by ring
  have hGT : (G.card : ℝ)+(T.card : ℝ) = (A.card : ℝ)^2 := by
    have h := Finset.card_filter_add_card_filter_not (s := A ×ˢ A)
      (fun a => a.1.gcd a.2 ≤ cutoff)
    exact_mod_cast (show G.card+T.card=A.card^2 by
      simpa only [not_le, Finset.card_product, pow_two] using h)
  have hG (a : ℕ × ℕ) (ha : a ∈ G) : a.1 ∈ A ∧ a.2 ∈ A ∧ a.1.gcd a.2 ≤ cutoff := by
    have h := Finset.mem_filter.1 ha
    exact ⟨(Finset.mem_product.1 h.1).1,(Finset.mem_product.1 h.1).2,h.2⟩
  have hGS := card_reduce (fun a ha =>
    ⟨Nat.zero_lt_of_lt (hA _ (hG a ha).1).1,(hG a ha).2.2⟩)
  have hGS' : (G.card : ℝ) ≤ (S.card : ℝ)*(cutoff : ℝ) := by exact_mod_cast hGS
  have hGcard : (N : ℝ)^2/20000 ≤ (G.card : ℝ) := by
    have h := pow_le_pow_left₀ (by positivity) hAcard 2
    change ((N : ℝ)/100)^2 ≤ (A.card : ℝ)^2 at h
    linarith
  have hGe : (s : ℝ)^2/20000 ≤ (S.card : ℝ) := by
    have hcR : 0 < (cutoff : ℝ) := by exact_mod_cast hc0
    have hcR1 : 1 ≤ (cutoff : ℝ) := by exact_mod_cast hc1
    have h := hGcard.trans hGS'
    apply le_of_mul_le_mul_right _ hcR
    calc
      ((s : ℝ)^2/20000)*(cutoff : ℝ) ≤ ((s : ℝ)^2/20000)*(cutoff : ℝ)^2 :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg ((cutoff : ℝ)-1)]) (by positivity)
      _ = (N : ℝ)^2/20000 := by
        dsimp [N]
        push_cast
        ring
      _ ≤ (S.card : ℝ)*(cutoff : ℝ) := h
  refine ⟨S,hGe,?_⟩
  intro b hb
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.1 hb
  obtain ⟨ha₁,ha₂,had⟩ := hG a ha
  obtain ⟨ha₁N,ha₁U,P,hP,hPa,hPL⟩ := hA _ ha₁
  obtain ⟨ha₂N,ha₂U,Q,hQ,hQa,hQL⟩ := hA _ ha₂
  let d := a.1.gcd a.2
  have hd : 0 < d := Nat.gcd_pos_of_pos_left _ (Nat.zero_lt_of_lt ha₁N)
  have hl₁ : s ≤ a.1/d := (Nat.le_div_iff_mul_le hd).2 (by
    have h := Nat.mul_le_mul_left s had
    unfold N at ha₁N
    nlinarith)
  have hl₂ : s ≤ a.2/d := (Nat.le_div_iff_mul_le hd).2 (by
    have h := Nat.mul_le_mul_left s had
    unfold N at ha₂N
    nlinarith)
  have hu₁ : a.1/d ≤ branchConstant*s := by
    unfold branchConstant
    rw [mul_assoc]
    exact (Nat.div_le_self _ _).trans ha₁U
  have hu₂ : a.2/d ≤ branchConstant*s := by
    unfold branchConstant
    rw [mul_assoc]
    exact (Nat.div_le_self _ _).trans ha₂U
  have hnc : (s : ℝ)^(99/100 : ℝ) ≤ (N : ℝ)^(99/100 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn) (by norm_num)
  have hpD : d < P := by
    have h := (hpow'.trans_le hnc).trans hPL
    have hdR : (d : ℝ) ≤ (cutoff : ℝ) := by exact_mod_cast had
    exact_mod_cast (hdR.trans_lt h)
  have hqD : d < Q := by
    have h := (hpow'.trans_le hnc).trans hQL
    have hdR : (d : ℝ) ≤ (cutoff : ℝ) := by exact_mod_cast had
    exact_mod_cast (hdR.trans_lt h)
  have hp' : P ∣ a.1/d := by
    have he : d*(a.1/d) = a.1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    rw [← he] at hPa
    exact (hP.dvd_mul.1 hPa).resolve_left (fun h => hpD.not_ge (Nat.le_of_dvd hd h))
  have hq' : Q ∣ a.2/d := by
    have he : d*(a.2/d) = a.2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    rw [← he] at hQa
    exact (hQ.dvd_mul.1 hQa).resolve_left (fun h => hqD.not_ge (Nat.le_of_dvd hd h))
  exact ⟨hl₁,hl₂,hu₁,hu₂,Nat.coprime_div_gcd_div_gcd hd,
    P,Q,hP,hQ,hp',hq',(hnc.trans_lt hPL).le,(hnc.trans_lt hQL).le⟩

end LCMBranchDensity

/-
# A small-power bound on the number of divisors

Large prime factors absorb their contribution to the divisor count directly. The remaining
finitely many primes each cost at most a fixed constant.
-/

open scoped BigOperators

namespace LCMDivisorBound

theorem divisor_bound : ∃ K : ℝ, 1 ≤ K ∧ ∀ n : ℕ, 0 < n →
    (n.divisors.card : ℝ) ≤ K * (n : ℝ) ^ (1/100 : ℝ) := by
  let δ : ℝ := 1/100
  let L : ℕ := 2^100
  let b : ℝ := 2^δ
  let K : ℝ := max 1 (b-1)⁻¹
  have hδ : 0 < δ := by norm_num [δ]
  have hb : 1 < b := Real.one_lt_rpow (by norm_num) hδ
  have hK : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := by linarith
  have hKmul : 1 ≤ K*(b-1) := by
    have h := mul_le_mul_of_nonneg_right (le_max_right 1 ((b-1)⁻¹))
      (show 0 ≤ b-1 by linarith)
    change (b-1)⁻¹*(b-1) ≤ K*(b-1) at h
    rwa [inv_mul_cancel₀ (by linarith)] at h
  have hgeneral (p e : ℕ) (hp : 2 ≤ p) : (e : ℝ)+1 ≤ K*((p : ℝ)^δ)^e := by
    have hBernoulli := one_add_mul_le_pow (show (-2 : ℝ) ≤ b-1 by linarith) e
    rw [show 1 + (b-1) = b by ring] at hBernoulli
    have hb_le : b ≤ (p : ℝ)^δ :=
      Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp) hδ.le
    calc
      (e : ℝ)+1 ≤ K * (1+(e : ℝ)*(b-1)) := by
        have h := mul_le_mul_of_nonneg_left hKmul (show 0 ≤ (e : ℝ) by positivity)
        nlinarith
      _ ≤ K*b^e := mul_le_mul_of_nonneg_left hBernoulli hKpos.le
      _ ≤ K*((p : ℝ)^δ)^e := by gcongr
  have hlarge (p e : ℕ) (hp : L ≤ p) : (e : ℝ)+1 ≤ ((p : ℝ)^δ)^e := by
    have hL : (L : ℝ)^δ = 2 := by
      simp only [L, Nat.cast_pow, Nat.cast_ofNat]
      have h := Real.pow_rpow_inv_natCast (n := 100) (x := (2 : ℝ)) (by norm_num)
        (by norm_num)
      convert h using 2
      norm_num [δ]
    have hp' : (2 : ℝ) ≤ (p : ℝ)^δ := hL ▸
      Real.rpow_le_rpow (by positivity : 0 ≤ (L : ℝ)) (by exact_mod_cast hp) hδ.le
    have hBernoulli := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 by norm_num) e
    calc
      (e : ℝ)+1 ≤ (2 : ℝ)^e := by norm_num at hBernoulli; simpa [add_comm] using hBernoulli
      _ ≤ ((p : ℝ)^δ)^e := by gcongr
  refine ⟨K^L, one_le_pow₀ hK, fun n hn => ?_⟩
  let C (p : ℕ) := if p < L then K else 1
  have hfactor (p : ℕ) (hp : p ∈ n.primeFactors) :
      (n.factorization p : ℝ)+1 ≤ C p*((p : ℝ)^δ)^(n.factorization p) := by
    by_cases h : p < L
    · simpa [C, h] using hgeneral p (n.factorization p) (Nat.prime_of_mem_primeFactors hp).two_le
    · simpa [C, h] using hlarge p (n.factorization p) (le_of_not_gt h)
  have hprod : (∏ p ∈ n.primeFactors, ((p : ℝ)^δ)^(n.factorization p)) =
      (n : ℝ)^δ := by
    calc
      (∏ p ∈ n.primeFactors, ((p : ℝ)^δ)^(n.factorization p)) =
          ∏ p ∈ n.primeFactors, (((p : ℝ)^(n.factorization p))^δ) := by
        apply Finset.prod_congr rfl
        intro p _
        rw [← Real.rpow_mul_natCast (by positivity), mul_comm δ,
          Real.rpow_natCast_mul (by positivity)]
      _ = (n : ℝ)^δ := by
        rw [Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
        simp_rw [← Nat.cast_pow]
        rw [← Nat.cast_prod]
        exact congrArg (fun m : ℕ => (m : ℝ)^δ) (Nat.prod_factorization_pow_eq_self hn.ne')
  have hCprod : (∏ p ∈ n.primeFactors, C p) ≤ K^L := by
    rw [show (∏ p ∈ n.primeFactors, C p) =
        ∏ _p ∈ n.primeFactors.filter (· < L), K by
      rw [Finset.prod_filter], Finset.prod_const]
    apply pow_le_pow_right₀ hK
    calc
      (n.primeFactors.filter (· < L)).card ≤ (Finset.range L).card :=
        Finset.card_le_card (fun _ hp => Finset.mem_range.2 (Finset.mem_filter.1 hp).2)
      _ = L := Finset.card_range L
  calc
    (n.divisors.card : ℝ) =
        ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ)+1) := by
      rw [Nat.card_divisors hn.ne', Nat.cast_prod]
      simp
    _ ≤ ∏ p ∈ n.primeFactors, C p*((p : ℝ)^δ)^(n.factorization p) :=
      Finset.prod_le_prod (fun _ _ => by positivity) hfactor
    _ = (∏ p ∈ n.primeFactors, C p)*(n : ℝ)^δ := by
      rw [Finset.prod_mul_distrib, hprod]
    _ ≤ K^L*(n : ℝ)^δ := mul_le_mul_of_nonneg_right hCprod (by positivity)

end LCMDivisorBound

/-
# Controlling overlap between low-LCM triple progressions

The gcd of two CRT periods factors into a matrix of pairwise gcds. A nonzero determinant
bounds the matched cells. Two large prime factors bound the other cells.
-/

open scoped BigOperators

namespace LCMGCDMatrix

def signed (p q : ℕ) : Fin 3 → ℤ := ![(p : ℤ), (q : ℤ), -((p : ℤ)+(q : ℤ))]

def factors (p q : ℕ) (i : Fin 3) : ℕ := (signed p q i).natAbs

@[simp] theorem factors_zero (p q : ℕ) : factors p q 0 = p := rfl

@[simp] theorem factors_one (p q : ℕ) : factors p q 1 = q := rfl

@[simp] theorem factors_two (p q : ℕ) : factors p q 2 = p+q := by
  change (-((p : ℤ)+(q : ℤ))).natAbs = _
  rw [← Int.natCast_add, Int.natAbs_neg, Int.natAbs_natCast]

theorem factors_pos {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (i : Fin 3) :
    0 < factors p q i := by
  fin_cases i <;> simp_all

theorem factors_prod (p q : ℕ) : (∏ i, factors p q i) = p*q*(p+q) := by
  simp [Fin.prod_univ_three, mul_assoc]

theorem signed_sum (p q : ℕ) : ∑ i, signed p q i = 0 := by
  simp [Fin.sum_univ_three, signed]

theorem factors_coprime {p q : ℕ} (h : p.Coprime q) :
    Pairwise (fun i j => (factors p q i).Coprime (factors p q j)) := by
  intro i j hij
  have hp := Nat.coprime_self_add_right.2 h
  have hq := Nat.coprime_add_self_right.2 h.symm
  fin_cases i <;> fin_cases j <;> simp_all [Nat.coprime_comm] <;> assumption

theorem gcd_mul {a b c : ℕ} (h : b.Coprime c) :
    a.gcd (b*c) = a.gcd b * a.gcd c := by
  have hx : a.gcd (b*c) ∣ b*c := Nat.gcd_dvd_right _ _
  have hz := (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).2 hx
  have hb : (b*c).gcd b = b := Nat.gcd_eq_right (dvd_mul_right b c)
  have hc : (b*c).gcd c = c := Nat.gcd_eq_right (dvd_mul_left c b)
  rw [Nat.gcd_assoc, hb, Nat.gcd_assoc, hc] at hz
  exact hz.symm

theorem gcd_prod (a : ℕ) {f : Fin 3 → ℕ}
    (h : Pairwise (fun i j => (f i).Coprime (f j))) :
    a.gcd (∏ i, f i) = ∏ i, a.gcd (f i) := by
  have h₀₁ := h (show (0 : Fin 3) ≠ 1 by decide)
  have h₀₂ := h (show (0 : Fin 3) ≠ 2 by decide)
  have h₁₂ := h (show (1 : Fin 3) ≠ 2 by decide)
  simp only [Fin.prod_univ_three]
  rw [gcd_mul (h₀₂.mul_left h₁₂), gcd_mul h₀₁]

theorem gcd_matrix {a b : Fin 3 → ℕ}
    (ha : Pairwise (fun i j => (a i).Coprime (a j)))
    (hb : Pairwise (fun i j => (b i).Coprime (b j))) :
    (∏ i, a i).gcd (∏ j, b j) = ∏ i, ∏ j, (a i).gcd (b j) := by
  rw [Nat.gcd_comm, gcd_prod _ ha]
  apply Finset.prod_congr rfl
  intro i _
  rw [Nat.gcd_comm, gcd_prod _ hb]

theorem mul_dvd_natAbs_of_pairwise {a b c : ℕ} {z : ℤ}
    (hab : a.Coprime b) (hac : a.Coprime c) (hbc : b.Coprime c)
    (ha : (a : ℤ) ∣ z) (hb : (b : ℤ) ∣ z) (hc : (c : ℤ) ∣ z) :
    a*b*c ∣ z.natAbs := by
  exact (hac.mul_left hbc).mul_dvd_of_dvd_of_dvd
    (hab.mul_dvd_of_dvd_of_dvd (Int.natCast_dvd.1 ha) (Int.natCast_dvd.1 hb))
    (Int.natCast_dvd.1 hc)

theorem div_bound {a d p : ℕ} (ha : 0 < a) (hp : 0 < p) (h : p*d ∣ a) : d ≤ a/p := by
  exact (Nat.le_div_iff_mul_le hp).2 (by simpa [mul_comm] using Nat.le_of_dvd ha h)


theorem aligned_bound {p q P Q : ℕ} (hp : 0 < p) (hq : 0 < q) (hco : p.Coprime q)
    (hP : 0 < P) (hQ : 0 < Q) (hPp : P ∣ p) (hQq : Q ∣ q)
    (b : Fin 3 → ℤ) (hb : ∀ i, b i ≠ 0) (hbsum : b 0+b 1+b 2 = 0)
    (hbco : Pairwise (fun i j => (b i).natAbs.Coprime (b j).natAbs))
    (hPb : P ∣ (b 0).natAbs) (hQb : Q ∣ (b 1).natAbs)
    (hne : (p : ℤ)*b 1-(q : ℤ)*b 0 ≠ 0) :
    (p*q*(p+q)).gcd (∏ j, (b j).natAbs) ≤
      ((p : ℤ)*b 1-(q : ℤ)*b 0).natAbs *
        (((p/P)*(q/Q))*(((b 0).natAbs/P)*((b 1).natAbs/Q))) := by
  let a := signed p q
  let d (i j : Fin 3) := (factors p q i).gcd (b j).natAbs
  have hdleft (i j : Fin 3) : d i j ∣ factors p q i := Nat.gcd_dvd_left _ _
  have hdright (i j : Fin 3) : d i j ∣ (b j).natAbs := Nat.gcd_dvd_right _ _
  have hrow (i : Fin 3) : d i 0 * d i 1 * d i 2 ∣ factors p q i := by
    have h := Nat.gcd_dvd_left (factors p q i) (∏ j, (b j).natAbs)
    rw [gcd_prod _ hbco, Fin.prod_univ_three] at h
    exact h
  have hdP : P ∣ d 0 0 := Nat.dvd_gcd (by simpa using hPp) hPb
  have hdQ : Q ∣ d 1 1 := Nat.dvd_gcd (by simpa using hQq) hQb
  have hrow₀ : d 0 1*d 0 2 ≤ p/P := by
    apply div_bound hp hP
    have h := Nat.mul_dvd_mul hdP (dvd_refl (d 0 1*d 0 2))
    exact h.trans (by simpa [mul_assoc] using hrow 0)
  have hrow₁ : d 1 0*d 1 2 ≤ q/Q := by
    apply div_bound hq hQ
    have h := Nat.mul_dvd_mul hdQ (dvd_refl (d 1 0*d 1 2))
    exact h.trans (by simpa [mul_left_comm, mul_assoc, mul_comm] using hrow 1)
  have hcol₀ : d 2 0 ≤ (b 0).natAbs/P := by
    apply div_bound (Int.natAbs_pos.2 (hb 0)) hP
    have h := factors_coprime hco (show (0 : Fin 3) ≠ 2 by decide)
    have h' := (h.of_dvd_left (show P ∣ factors p q 0 by simpa using hPp)).of_dvd_right
      (hdleft 2 0)
    exact h'.mul_dvd_of_dvd_of_dvd hPb (hdright 2 0)
  have hcol₁ : d 2 1 ≤ (b 1).natAbs/Q := by
    apply div_bound (Int.natAbs_pos.2 (hb 1)) hQ
    have h := factors_coprime hco (show (1 : Fin 3) ≠ 2 by decide)
    have h' := (h.of_dvd_left (show Q ∣ factors p q 1 by simpa using hQq)).of_dvd_right
      (hdleft 2 1)
    exact h'.mul_dvd_of_dvd_of_dvd hQb (hdright 2 1)
  have hda (i : Fin 3) : (d i i : ℤ) ∣ a i := Int.natCast_dvd.2 (hdleft i i)
  have hdb (i : Fin 3) : (d i i : ℤ) ∣ b i := Int.natCast_dvd.2 (hdright i i)
  have habs (i j : Fin 3) (hij : i ≠ j) : (d i i).Coprime (d j j) :=
    ((factors_coprime hco hij).of_dvd_left (hdleft i i)).of_dvd_right (hdleft j j)
  let det := a 0*b 1-a 1*b 0
  have hdet₀ : (d 0 0 : ℤ) ∣ det :=
    dvd_sub (dvd_mul_of_dvd_left (hda 0) _) (dvd_mul_of_dvd_right (hdb 0) _)
  have hdet₁ : (d 1 1 : ℤ) ∣ det :=
    dvd_sub (dvd_mul_of_dvd_right (hdb 1) _) (dvd_mul_of_dvd_left (hda 1) _)
  have hdet₂ : (d 2 2 : ℤ) ∣ det := by
    have ha₂ : a 2 = -(a 0+a 1) := by
      have ha := signed_sum p q
      rw [Fin.sum_univ_three] at ha
      change a 0+a 1+a 2 = 0 at ha
      omega
    have hb₂ : b 2 = -(b 0+b 1) := by omega
    have h : (d 2 2 : ℤ) ∣ a 1*b 2-a 2*b 1 :=
      dvd_sub (dvd_mul_of_dvd_right (hdb 2) _) (dvd_mul_of_dvd_left (hda 2) _)
    convert h using 1
    unfold det
    rw [ha₂, hb₂]
    ring
  have hdiag : d 0 0*d 1 1*d 2 2 ≤ det.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.2 hne)
      (mul_dvd_natAbs_of_pairwise (habs 0 1 (by decide)) (habs 0 2 (by decide))
        (habs 1 2 (by decide)) hdet₀ hdet₁ hdet₂)
  calc
    (p*q*(p+q)).gcd (∏ j, (b j).natAbs) =
        (d 0 0*d 1 1*d 2 2) * ((d 0 1*d 0 2)*(d 1 0*d 1 2)*(d 2 0*d 2 1)) := by
      rw [← factors_prod, gcd_matrix (factors_coprime hco) hbco]
      change (∏ i, ∏ j, d i j) = _
      simp only [Fin.prod_univ_three]
      ring
    _ ≤ _ := by
      change _ ≤ det.natAbs * _
      gcongr


theorem determinant_zero {p q : ℕ} (hp : 0 < p) (hco : p.Coprime q)
    (b : Fin 3 → ℤ) (hbsum : b 0+b 1+b 2 = 0)
    (hbco : (b 0).natAbs.Coprime (b 1).natAbs)
    (hdet : (p : ℤ)*b 1-(q : ℤ)*b 0 = 0) :
    (b 0).natAbs = p ∧ (b 1).natAbs = q ∧ (b 2).natAbs = p+q := by
  have heq : (p : ℤ)*b 1 = (q : ℤ)*b 0 := sub_eq_zero.1 hdet
  have heqNat : p*(b 1).natAbs = q*(b 0).natAbs := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using congrArg Int.natAbs heq
  have hdvd : p ∣ (b 0).natAbs := hco.dvd_of_dvd_mul_left
    (heqNat ▸ dvd_mul_right p _)
  obtain ⟨k, hk⟩ := hdvd
  have hk' : (b 1).natAbs = q*k := by
    apply Nat.eq_of_mul_eq_mul_left hp
    rw [heqNat, hk]
    ring
  have hk1 : k = 1 := Nat.eq_one_of_dvd_coprimes hbco
    (hk ▸ dvd_mul_left k p) (hk' ▸ dvd_mul_left k q)
  rw [hk1, mul_one] at hk hk'
  have hb₂eq : (p : ℤ)*b 2 = -(p+q : ℕ)*b 0 := by
    have hb₂ : b 2 = -(b 0+b 1) := by omega
    rw [hb₂]
    push_cast
    linear_combination -heq
  have hb₂nat : p*(b 2).natAbs = (p+q)*(b 0).natAbs := by
    simpa only [Int.natAbs_mul, Int.natAbs_neg, Int.natAbs_natCast] using
      congrArg Int.natAbs hb₂eq
  refine ⟨hk, hk', Nat.eq_of_mul_eq_mul_left hp ?_⟩
  rw [hb₂nat, hk, mul_comm]

theorem factors_le_sum (p q : ℕ) (i : Fin 3) : factors p q i ≤ p+q := by
  fin_cases i <;> simp

theorem same_or_swapped_of_determinant_zero {p q r t : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hco : p.Coprime q)
    (hrt : r.Coprime t) (σ : Equiv.Perm (Fin 3))
    (heq : (p : ℤ)*signed r t (σ 1) - (q : ℤ)*signed r t (σ 0) = 0) :
    (p = r ∧ q = t) ∨ (p = t ∧ q = r) := by
  have hsum : signed r t (σ 0) + signed r t (σ 1) + signed r t (σ 2) = 0 := by
    rw [← Fin.sum_univ_three (f := fun i => signed r t (σ i)), Equiv.sum_comp σ]
    exact signed_sum r t
  have hc := factors_coprime hrt (σ.injective.ne (show (0 : Fin 3) ≠ 1 by decide))
  obtain ⟨h₀, h₁, h₂⟩ := determinant_zero hp hco (fun i => signed r t (σ i))
    hsum hc heq
  change factors r t (σ 0) = p at h₀
  change factors r t (σ 1) = q at h₁
  change factors r t (σ 2) = p+q at h₂
  have htop : σ 2 = 2 := by
    let j : Fin 3 := σ.symm 2
    have hj : σ j = 2 := σ.apply_symm_apply 2
    have hbound := factors_le_sum r t (σ 2)
    rw [h₂] at hbound
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj' with hj₀ | hj₁ | hj₂
    · rw [hj₀] at hj
      rw [hj, factors_two] at h₀
      omega
    · rw [hj₁] at hj
      rw [hj, factors_two] at h₁
      omega
    · rwa [hj₂] at hj
  rw [htop, factors_two] at h₂
  have h0ne : σ 0 ≠ 2 := by
    rw [← htop]
    exact σ.injective.ne (by decide)
  have hσ₀ : σ 0 = 0 ∨ σ 0 = 1 := by omega
  rcases hσ₀ with hσ₀ | hσ₀
  · rw [hσ₀, factors_zero] at h₀
    exact Or.inl ⟨h₀.symm, by omega⟩
  · rw [hσ₀, factors_one] at h₀
    exact Or.inr ⟨h₀.symm, by omega⟩

theorem perm_of_distinct (i j : Fin 3) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 3), σ 0 = i ∧ σ 1 = j := by
  let f := Equiv.swap (0 : Fin 3) i
  have hf : f 0 = i := Equiv.swap_apply_left _ _
  have hne : (0 : Fin 3) ≠ f.symm j := by
    intro heq
    apply hij
    have h := congrArg f heq
    rwa [hf, f.apply_symm_apply] at h
  refine ⟨f.setValue 1 j, ?_, Equiv.setValue_eq _ _ _⟩
  change f (Equiv.swap 1 (f.symm j) 0) = i
  rw [Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 3) ≠ 1) hne]
  exact hf

theorem missing_prime_bound {M N P : ℕ} (hM : 0 < M) (hP : P.Prime)
    (hPM : P ∣ M) (hPN : ¬P ∣ N) : M.gcd N ≤ M/P := by
  have hc := (hP.coprime_iff_not_dvd.2
    (fun hd => hPN (hd.trans (Nat.gcd_dvd_right M N)))).symm
  have hd : M.gcd N ∣ P*(M/P) := by
    rw [Nat.mul_div_cancel' hPM]
    exact Nat.gcd_dvd_left M N
  have hd' : M.gcd N ∣ M/P := hc.dvd_of_dvd_mul_left hd
  exact Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd hM hPM) hP.pos) hd'


theorem gcd_bound {p q r t P Q R : ℕ} {L : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (ht : 0 < t)
    (hpR : p ≤ R) (hqR : q ≤ R) (hrR : r ≤ R) (htR : t ≤ R)
    (hpq : p.Coprime q) (hrt : r.Coprime t)
    (hP : P.Prime) (hQ : Q.Prime) (hPp : P ∣ p) (hQq : Q ∣ q)
    (hL : 0 < L) (hLP : L ≤ (P : ℝ)) (hLQ : L ≤ (Q : ℝ))
    (hLR : 2*(R : ℝ) < L^2)
    (hne : ¬ ((p = r ∧ q = t) ∨ (p = t ∧ q = r))) :
    (((p*q*(p+q)).gcd (r*t*(r+t))) : ℝ) ≤
      max (2*(R : ℝ)^3/L) (4*(R : ℝ)^2*((2*(R : ℝ)/L)^4)) := by
  let M := p*q*(p+q)
  let N := r*t*(r+t)
  have hM : 0 < M := by dsimp [M]; positivity
  have hpB : (p : ℝ) ≤ (R : ℝ) := by exact_mod_cast hpR
  have hqB : (q : ℝ) ≤ (R : ℝ) := by exact_mod_cast hqR
  have hMbound : (M : ℝ) ≤ 2*(R : ℝ)^3 := by
    unfold M
    push_cast
    calc
      (p : ℝ)*q*(p+q) ≤ (R : ℝ)*R*(R+R) := by gcongr
      _ = _ := by ring
  have hdB {d : ℕ} (hd : d.Prime) (hLd : L ≤ (d : ℝ)) (hdM : d ∣ M) (hdN : ¬d ∣ N) :
      (M.gcd N : ℝ) ≤ 2*(R : ℝ)^3/L := by
    have hd' := missing_prime_bound hM hd hdM hdN
    calc
      (M.gcd N : ℝ) ≤ ((M/d : ℕ) : ℝ) := by exact_mod_cast hd'
      _ ≤ (M : ℝ)/d := Nat.cast_div_le
      _ ≤ _ := by gcongr
  change (M.gcd N : ℝ) ≤ _
  by_cases hPN : P ∣ N
  · by_cases hQN : Q ∣ N
    · apply le_max_of_le_right
      have hchoose (v : ℕ) (hv : v.Prime) (hd : v ∣ N) :
          ∃ j : Fin 3, v ∣ factors r t j := by
        rcases hv.dvd_mul.1 hd with hd' | hadd
        · rcases hv.dvd_mul.1 hd' with hdr | hdt
          · exact ⟨0, by simpa using hdr⟩
          · exact ⟨1, by simpa using hdt⟩
        · exact ⟨2, by simpa using hadd⟩
      obtain ⟨i, hPi⟩ := hchoose P hP hPN
      obtain ⟨j, hQj⟩ := hchoose Q hQ hQN
      have hcol (i : Fin 3) : factors r t i ≤ 2*R := by
        have h := factors_le_sum r t i
        omega
      have hij : i ≠ j := by
        intro hij
        subst j
        have hPQ := (hpq.of_dvd_left hPp).of_dvd_right hQq
        have hdiv := hPQ.mul_dvd_of_dvd_of_dvd hPi hQj
        have hle := (Nat.le_of_dvd (factors_pos hr ht i) hdiv).trans (hcol i)
        have hle' : (P : ℝ)*(Q : ℝ) ≤ 2*(R : ℝ) := by exact_mod_cast hle
        have hge : L*L ≤ (P : ℝ)*(Q : ℝ) := by gcongr
        nlinarith
      obtain ⟨σ, hσ₀, hσ₁⟩ := perm_of_distinct i j hij
      let b (l : Fin 3) := signed r t (σ l)
      have hb (i : Fin 3) : b i ≠ 0 := Int.natAbs_pos.1 (factors_pos hr ht (σ i))
      have hbsum : b 0+b 1+b 2 = 0 := by
        change signed r t (σ 0)+signed r t (σ 1)+signed r t (σ 2) = 0
        rw [← Fin.sum_univ_three (fun i => signed r t (σ i)), Equiv.sum_comp σ]
        exact signed_sum r t
      have hbco : Pairwise (fun i j => (b i).natAbs.Coprime (b j).natAbs) :=
        fun _ _ h => factors_coprime hrt (σ.injective.ne h)
      have hbP : P ∣ (b 0).natAbs := by
        change P ∣ factors r t (σ 0)
        rwa [hσ₀]
      have hbQ : Q ∣ (b 1).natAbs := by
        change Q ∣ factors r t (σ 1)
        rwa [hσ₁]
      have hdet : (p : ℤ)*b 1-(q : ℤ)*b 0 ≠ 0 := by
        intro h
        exact hne (same_or_swapped_of_determinant_zero hp hq hpq hrt σ h)
      have hbound := aligned_bound hp hq hpq hP.pos hQ.pos hPp hQq b hb hbsum hbco hbP hbQ hdet
      have hprod : (∏ j, (b j).natAbs) = N := by
        change (∏ j, factors r t (σ j)) = N
        rw [Equiv.prod_comp σ, factors_prod]
      rw [hprod] at hbound
      have hbB (i : Fin 3) : ((b i).natAbs : ℝ) ≤ 2*(R : ℝ) := by
        exact_mod_cast hcol (σ i)
      have hnat : (((p : ℤ)*b 1-(q : ℤ)*b 0).natAbs : ℝ) ≤ 4*(R : ℝ)^2 := by
        have h := Int.natAbs_sub_le ((p : ℤ)*b 1) ((q : ℤ)*b 0)
        rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast] at h
        calc
          _ ≤ (p : ℝ)*((b 1).natAbs : ℝ)+(q : ℝ)*((b 0).natAbs : ℝ) := by exact_mod_cast h
          _ ≤ (R : ℝ)*(2*R)+(R : ℝ)*(2*R) := by gcongr; exacts [hbB 1, hbB 0]
          _ = _ := by ring
      have hquot {n d : ℕ} (hn : (n : ℝ) ≤ 2*(R : ℝ)) (hd : L ≤ (d : ℝ)) :
          ((n/d : ℕ) : ℝ) ≤ 2*(R : ℝ)/L :=
        Nat.cast_div_le.trans (by gcongr)
      have hpQ := hquot (show (p : ℝ) ≤ 2*(R : ℝ) by linarith) hLP
      have hqQ := hquot (show (q : ℝ) ≤ 2*(R : ℝ) by linarith) hLQ
      have hb₀Q := hquot (hbB 0) hLP
      have hb₁Q := hquot (hbB 1) hLQ
      let B := 2*(R : ℝ)/L
      calc
        (M.gcd N : ℝ) ≤
            (((p : ℤ)*b 1-(q : ℤ)*b 0).natAbs : ℝ) *
              ((((p/P : ℕ) : ℝ)*((q/Q : ℕ) : ℝ)) *
                ((((b 0).natAbs/P : ℕ) : ℝ)*(((b 1).natAbs/Q : ℕ) : ℝ))) := by
          exact_mod_cast hbound
        _ ≤ 4*(R : ℝ)^2*((B*B)*(B*B)) := by gcongr
        _ = _ := by unfold B; ring
    · exact le_max_of_le_left (hdB hQ hLQ (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hQq p) _) hQN)
  · exact le_max_of_le_left (hdB hP hLP (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hPp q) _) hPN)


theorem scale_large (D : ℕ) : ∀ᶠ s : ℕ in Filter.atTop,
    2*(D : ℝ)*s < ((s : ℝ)^(99/100 : ℝ))^2 := by
  open Filter in
  have hpow : Tendsto (fun s : ℕ => (s : ℝ)^(98/100 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 98/100)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hpow.eventually (Filter.eventually_gt_atTop (2*(D : ℝ))),
    Filter.eventually_ge_atTop (1 : ℕ)] with s hs hs₁
  have hspos : 0 < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  have h' : (s : ℝ)^(98/100 : ℝ)*(s : ℝ) =
      ((s : ℝ)^(99/100 : ℝ))^2 := by
    conv_lhs => arg 2; rw [← Real.rpow_one (s : ℝ)]
    rw [← Real.rpow_add hspos, ← Real.rpow_mul_natCast hspos.le]
    norm_num
  exact h'.symm ▸ (mul_lt_mul_of_pos_right hs hspos)

theorem gcd_bound_at_scale {p q r t P Q D s : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (ht : 0 < t) (hs : 1 ≤ s)
    (hpR : p ≤ D*s) (hqR : q ≤ D*s) (hrR : r ≤ D*s) (htR : t ≤ D*s)
    (hpq : p.Coprime q) (hrt : r.Coprime t)
    (hP : P.Prime) (hQ : Q.Prime) (hPp : P ∣ p) (hQq : Q ∣ q)
    (hLP : (s : ℝ)^(99/100 : ℝ) ≤ (P : ℝ)) (hLQ : (s : ℝ)^(99/100 : ℝ) ≤ (Q : ℝ))
    (hlarge : 2*(D : ℝ)*s < ((s : ℝ)^(99/100 : ℝ))^2)
    (hne : ¬ ((p = r ∧ q = t) ∨ (p = t ∧ q = r))) :
    (((p*q*(p+q)).gcd (r*t*(r+t))) : ℝ) ≤
      (64*(D : ℝ)^6+2*(D : ℝ)^3)*(s : ℝ)^(51/25 : ℝ) := by
  have hs₁ : 1 ≤ (s : ℝ) := by exact_mod_cast hs
  have hs₀ : 0 < (s : ℝ) := by linarith
  have hR : 2*((D*s : ℕ) : ℝ) < ((s : ℝ)^(99/100 : ℝ))^2 := by
    push_cast
    linarith
  apply (gcd_bound hp hq hr ht hpR hqR hrR htR hpq hrt hP hQ hPp hQq
    (Real.rpow_pos_of_pos hs₀ _) hLP hLQ hR hne).trans
  apply max_le
  · push_cast
    calc
      2*((D : ℝ)*s)^3/(s : ℝ)^(99/100 : ℝ) =
          2*(D : ℝ)^3*((s : ℝ)^3/(s : ℝ)^(99/100 : ℝ)) := by ring
      _ = 2*(D : ℝ)^3*(s : ℝ)^(201/100 : ℝ) := by
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_sub hs₀]
        norm_num
      _ ≤ _ := mul_le_mul (le_add_of_nonneg_left (by positivity))
        (Real.rpow_le_rpow_of_exponent_le hs₁ (by norm_num)) (by positivity) (by positivity)
  · push_cast
    have hquot : (s : ℝ)/(s : ℝ)^(99/100 : ℝ) = (s : ℝ)^(1/100 : ℝ) := by
      conv_lhs => arg 1; rw [← Real.rpow_one (s : ℝ)]
      rw [← Real.rpow_sub hs₀]
      norm_num
    calc
      4*((D : ℝ)*s)^2*((2*((D : ℝ)*s)/(s : ℝ)^(99/100 : ℝ))^4) =
          64*(D : ℝ)^6*((s : ℝ)^2*((s : ℝ)/(s : ℝ)^(99/100 : ℝ))^4) := by ring
      _ = 64*(D : ℝ)^6*(s : ℝ)^(51/25 : ℝ) := by
        congr 1
        rw [hquot, ← Real.rpow_mul_natCast hs₀.le, ← Real.rpow_natCast, ← Real.rpow_add hs₀]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity)

end LCMGCDMatrix

/-
# Counting overlaps between two residue classes

Possible differences lie in one residue class modulo the gcd of the periods. At each
fixed difference, the first coordinates lie in one residue class modulo their lcm.
-/

open scoped BigOperators

namespace LCMProgressionCount

theorem card_residue {S : Finset ℕ} {lo hi d : ℕ}
    (hlo : ∀ x ∈ S, lo ≤ x) (hhi : ∀ x ∈ S, x ≤ hi)
    (_hd : 0 < d) (hmod : ∀ x ∈ S, ∀ y ∈ S, x ≡ y [MOD d]) :
    (S.card : ℝ) ≤ ((hi-lo : ℕ) : ℝ)/d+1 := by
  have hcard : S.card ≤ ((hi-lo)/d)+1 := by
    rw [← Finset.card_range ((hi-lo)/d+1)]
    apply Finset.card_le_card_of_injOn (fun x => (x-lo)/d)
    · intro x hx
      change (x-lo)/d ∈ Finset.range ((hi-lo)/d+1)
      apply Finset.mem_range.2
      exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.sub_le_sub_right (hhi x hx) lo))
    · intro x hx y hy hq
      change (x-lo)/d = (y-lo)/d at hq
      have hr := (hmod x hx y hy).sub (hlo x hx) (hlo y hy) Nat.ModEq.rfl
      change (x-lo)%d = (y-lo)%d at hr
      have h₀ := Nat.mod_add_div (x-lo) d
      have h₁ := Nat.mod_add_div (y-lo) d
      rw [hq, hr] at h₀
      have hx' := hlo x hx
      have hy' := hlo y hy
      omega
  calc
    (S.card : ℝ) ≤ (((hi-lo)/d : ℕ) : ℝ)+1 := by exact_mod_cast hcard
    _ ≤ _ := add_le_add_left (Nat.cast_div_le (m := hi-lo) (n := d) (α := ℝ)) 1

def closePairs (S T : Finset ℕ) (w : ℕ) : Finset (ℕ × ℕ) :=
  (S ×ˢ T).filter (fun z => z.1 ≤ z.2+w ∧ z.2 ≤ z.1+w)

def offset (w : ℕ) (z : ℕ × ℕ) : ℕ := z.2+w-z.1

theorem offset_spec {S T : Finset ℕ} {w : ℕ} {z : ℕ × ℕ} (hz : z ∈ closePairs S T w) :
    z.1 + offset w z = z.2+w ∧ offset w z ≤ 2*w := by
  obtain ⟨h₀, h₁⟩ := (Finset.mem_filter.1 hz).2
  unfold offset
  omega

theorem card_closePairs {S T : Finset ℕ} {lo hi m n w : ℕ}
    (hlo : ∀ x ∈ S, lo ≤ x) (hhi : ∀ x ∈ S, x ≤ hi)
    (hm : 0 < m) (hn : 0 < n)
    (hS : ∀ x ∈ S, ∀ y ∈ S, x ≡ y [MOD m])
    (hT : ∀ x ∈ T, ∀ y ∈ T, x ≡ y [MOD n]) :
    ((closePairs S T w).card : ℝ) ≤
      (((2*w : ℕ) : ℝ)/(m.gcd n)+1) * (((hi-lo : ℕ) : ℝ)/(m.lcm n)+1) := by
  let C := closePairs S T w
  let g := m.gcd n
  let d := m.lcm n
  let D := C.image (offset w)
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hm
  have hd : 0 < d := Nat.lcm_pos hm hn
  have hmembers {z : ℕ × ℕ} (hz : z ∈ C) : z.1 ∈ S ∧ z.2 ∈ T :=
    Finset.mem_product.1 (Finset.mem_filter.1 hz).1
  have hD : (D.card : ℝ) ≤ ((2*w : ℕ) : ℝ)/g+1 := by
    refine card_residue (lo := 0) (fun _ _ => Nat.zero_le _) ?_ hg ?_
    · intro t ht
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 ht
      exact (offset_spec hz).2
    · intro x hx y hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
      have h₁ := (hS a.1 (hmembers ha).1 b.1 (hmembers hb).1).of_dvd (Nat.gcd_dvd_left m n)
      have h₂ := (hT a.2 (hmembers ha).2 b.2 (hmembers hb).2).of_dvd (Nat.gcd_dvd_right m n)
      apply h₁.add_left_cancel
      rw [(offset_spec ha).1, (offset_spec hb).1]
      exact h₂.add_right w
  let fiber (t : ℕ) := C.filter (fun z => offset w z = t)
  have hF (t : ℕ) : ((fiber t).card : ℝ) ≤ ((hi-lo : ℕ) : ℝ)/d+1 := by
    let F := (fiber t).image Prod.fst
    have hFcard : (fiber t).card = F.card := by
      apply (Finset.card_image_of_injOn ?_).symm
      intro x hx y hy h
      change x.1 = y.1 at h
      obtain ⟨hx, hxt⟩ := Finset.mem_filter.1 hx
      obtain ⟨hy, hyt⟩ := Finset.mem_filter.1 hy
      have h₀ := (offset_spec hx).1
      have h₁ := (offset_spec hy).1
      exact Prod.ext h (by omega)
    rw [hFcard]
    refine card_residue ?_ ?_ hd ?_
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hx
      exact hlo _ (hmembers (Finset.mem_filter.1 hz).1).1
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hx
      exact hhi _ (hmembers (Finset.mem_filter.1 hz).1).1
    · intro x hx y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨hz, hzt⟩ := Finset.mem_filter.1 hz
      obtain ⟨hv, hvt⟩ := Finset.mem_filter.1 hv
      have hz' : z.1+t = z.2+w := hzt ▸ (offset_spec hz).1
      have hv' : v.1+t = v.2+w := hvt ▸ (offset_spec hv).1
      have h₁ := hS z.1 (hmembers hz).1 v.1 (hmembers hv).1
      have h₂ := hT z.2 (hmembers hz).2 v.2 (hmembers hv).2
      have h₃ : z.1 ≡ v.1 [MOD n] := by
        apply Nat.ModEq.add_right_cancel' t
        rw [hz', hv']
        exact h₂.add_right _
      exact Nat.mod_lcm h₁ h₃
  have hcard : C.card = ∑ t ∈ D, (fiber t).card :=
    Finset.card_eq_sum_card_fiberwise (fun z hz => Finset.mem_image_of_mem _ hz)
  change (C.card : ℝ) ≤ _
  rw [hcard, Nat.cast_sum]
  calc
    _ ≤ ∑ t ∈ D, (((hi-lo : ℕ) : ℝ)/d+1) := Finset.sum_le_sum (fun t _ => hF t)
    _ = (D.card : ℝ)*(((hi-lo : ℕ) : ℝ)/d+1) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hD (by positivity)

end LCMProgressionCount

/-
# Sums of overlaps between CRT periods

A gcd class is determined by three divisors of a fixed period. In each class choose the
largest divisor, count its coordinate first, and then use two congruences for the second coordinate.
-/

open scoped BigOperators

namespace LCMGCDSum

open LCMGCDMatrix LCMProgressionCount

abbrev Branch := ℕ × ℕ

def value (a : Branch) (i : Fin 3) : ℕ := factors a.1 a.2 i

theorem pair_injective {a b : Branch} {i j : Fin 3} (hij : i ≠ j)
    (hi : value a i = value b i) (hj : value a j = value b j) : a = b := by
  apply Prod.ext <;> fin_cases i <;> fin_cases j <;> simp_all [value]

theorem modEq_of_fixed {a b : Branch} {i j k : Fin 3} {d : ℕ}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : value a i = value b i)
    (hk : value a k ≡ value b k [MOD d]) : value a j ≡ value b j [MOD d] := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [value]
  · exact Nat.ModEq.add_left_cancel' _ hk
  · exact Nat.ModEq.rfl
  · exact Nat.ModEq.add_right_cancel' _ hk
  · exact Nat.ModEq.rfl
  · exact hk.add_right_cancel (hi ▸ Nat.ModEq.rfl)
  · exact hk.add_left_cancel (hi ▸ Nat.ModEq.rfl)

theorem card_two_coordinates {S : Finset Branch} {i j : Fin 3}
    (hij : i ≠ j) {A B : ℝ}
    (hfirst : ((S.image (fun z => value z i)).card : ℝ) ≤ A)
    (hsecond : ∀ x, (((S.filter (fun z => value z i = x)).image
      (fun z => value z j)).card : ℝ) ≤ B)
    (hB : 0 ≤ B) : (S.card : ℝ) ≤ A*B := by
  let D := S.image (fun z => value z i)
  let F (x : ℕ) := S.filter (fun z => value z i = x)
  have hcard : S.card = ∑ x ∈ D, (F x).card :=
    Finset.card_eq_sum_card_fiberwise (fun z hz => Finset.mem_image_of_mem _ hz)
  have hF (x : ℕ) : ((F x).card : ℝ) ≤ B := by
    have h := Finset.card_image_of_injOn (s := F x) (f := fun z => value z j) (by
      intro a ha b hb he
      have ha' := (Finset.mem_filter.1 ha).2
      have hb' := (Finset.mem_filter.1 hb).2
      exact pair_injective hij (ha'.trans hb'.symm) he)
    rw [← h]
    exact hsecond x
  rw [hcard, Nat.cast_sum]
  calc
    _ ≤ ∑ x ∈ D, B := Finset.sum_le_sum (fun x _ => hF x)
    _ = (D.card : ℝ)*B := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ A*B := mul_le_mul_of_nonneg_right hfirst hB

theorem card_of_divisibility {S : Finset Branch} {R : ℕ} {d : Fin 3 → ℕ}
    (hd : ∀ i, 0 < d i) (hdiv : ∀ z ∈ S, ∀ i, d i ∣ value z i)
    (hbounded : ∀ z ∈ S, ∀ i, value z i ≤ R)
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hcop : (d j).Coprime (d k)) :
    (S.card : ℝ) ≤ ((R : ℝ)/d i+1)*((R : ℝ)/(d j*d k : ℕ)+1) := by
  refine card_two_coordinates hij ?_ (fun x => ?_) (by positivity)
  · refine card_residue (lo := 0) (fun _ _ => Nat.zero_le _) ?_ (hd i) ?_
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hx
      exact hbounded z hz i
    · intro x hx y hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
      exact (Nat.modEq_zero_iff_dvd.2 (hdiv a ha i)).trans
        (Nat.modEq_zero_iff_dvd.2 (hdiv b hb i)).symm
  · refine card_residue (lo := 0) (fun _ _ => Nat.zero_le _) ?_ (Nat.mul_pos (hd j) (hd k)) ?_
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
      exact hbounded z (Finset.mem_filter.1 hz).1 j
    · intro y hy z hz
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hz
      obtain ⟨ha, hax⟩ := Finset.mem_filter.1 ha
      obtain ⟨hb, hbx⟩ := Finset.mem_filter.1 hb
      have hmod (l : Fin 3) : value a l ≡ value b l [MOD d l] :=
        (Nat.modEq_zero_iff_dvd.2 (hdiv a ha l)).trans
          (Nat.modEq_zero_iff_dvd.2 (hdiv b hb l)).symm
      have hk := modEq_of_fixed hij hik hjk (hax.trans hbx.symm) (hmod k)
      simpa [hcop.lcm_eq_mul] using Nat.mod_lcm (hmod j) hk

theorem exists_order (d : Fin 3 → ℕ) :
    ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ d j ≤ d i ∧ d k ≤ d i ∧
      d 0*d 1*d 2 = d i*d j*d k := by
  by_cases h₀₁ : d 1 ≤ d 0
  · by_cases h₀₂ : d 2 ≤ d 0
    · exact ⟨0, 1, 2, by decide, by decide, by decide, h₀₁, h₀₂, rfl⟩
    · exact ⟨2, 0, 1, by decide, by decide, by decide, by omega, by omega, by ring⟩
  · by_cases h₁₂ : d 2 ≤ d 1
    · exact ⟨1, 0, 2, by decide, by decide, by decide, by omega, h₁₂, by ring⟩
    · exact ⟨2, 0, 1, by decide, by decide, by decide, by omega, by omega, by ring⟩

theorem weighted_card_of_divisibility {S : Finset Branch} {R : ℕ} {d : Fin 3 → ℕ}
    (hd : ∀ i, 0 < d i) (hdR : ∀ i, d i ≤ R)
    (hdiv : ∀ z ∈ S, ∀ i, d i ∣ value z i)
    (hbounded : ∀ z ∈ S, ∀ i, value z i ≤ R)
    (hcop : Pairwise (fun i j => (d i).Coprime (d j))) :
    (((d 0*d 1*d 2 : ℕ) : ℝ) * S.card) ≤
      2*(R : ℝ)^2 + 2*(R : ℝ)*(((d 0*d 1*d 2 : ℕ) : ℝ)^(2/3 : ℝ)) := by
  obtain ⟨i,j,k,hij,hik,hjk,hji,hki,he⟩ := exists_order d
  rw [he]
  have hdᵢ : 0 < (d i : ℝ) := by exact_mod_cast hd i
  have hdᵤ : 0 < (d j : ℝ)*(d k : ℝ) := by
    exact mul_pos (by exact_mod_cast hd j) (by exact_mod_cast hd k)
  have hle : (d j : ℝ)*(d k : ℝ) ≤ (d i : ℝ)^2 := by
    rw [pow_two]
    exact mul_le_mul (by exact_mod_cast hji) (by exact_mod_cast hki)
      (by positivity) hdᵢ.le
  have hpow : (d j : ℝ)*(d k : ℝ) ≤
      ((d i : ℝ)*(d j : ℝ)*(d k : ℝ))^(2/3 : ℝ) := by
    have h₀ : ((d j : ℝ)*(d k : ℝ))^3 ≤ ((d i : ℝ)*(d j : ℝ)*(d k : ℝ))^2 := by
      calc
        _ = ((d j : ℝ)*(d k : ℝ))*((d j : ℝ)*(d k : ℝ))^2 := by ring
        _ ≤ (d i : ℝ)^2*((d j : ℝ)*(d k : ℝ))^2 :=
          mul_le_mul_of_nonneg_right hle (by positivity)
        _ = _ := by ring
    have h := Real.rpow_le_rpow (by positivity) h₀ (by norm_num : (0 : ℝ) ≤ 1/3)
    have hleft : (((d j : ℝ)*(d k : ℝ))^3)^(1/3 : ℝ) = (d j : ℝ)*(d k : ℝ) := by
      rw [← Real.rpow_natCast_mul hdᵤ.le]
      norm_num
    have hright :
        (((d i : ℝ)*(d j : ℝ)*(d k : ℝ))^2)^(1/3 : ℝ) =
          ((d i : ℝ)*(d j : ℝ)*(d k : ℝ))^(2/3 : ℝ) := by
      rw [← Real.rpow_natCast_mul (by positivity)]
      norm_num
    rwa [hleft, hright] at h
  have hcard := card_of_divisibility hd hdiv hbounded hij hik hjk (hcop hjk)
  have hdiR : (d i : ℝ) ≤ R := by exact_mod_cast hdR i
  push_cast at hcard ⊢
  calc
    _ ≤ ((d i : ℝ)*(d j : ℝ)*(d k : ℝ)) *
        (((R : ℝ)/d i+1)*((R : ℝ)/((d j : ℝ)*(d k : ℝ))+1)) :=
      mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = (R : ℝ)^2+(R : ℝ)*d i+(R : ℝ)*((d j : ℝ)*(d k : ℝ))+
        (d i : ℝ)*((d j : ℝ)*(d k : ℝ)) := by
      have hj₀ : (d j : ℝ) ≠ 0 := by exact_mod_cast (hd j).ne'
      have hk₀ : (d k : ℝ) ≠ 0 := by exact_mod_cast (hd k).ne'
      field_simp [hdᵢ.ne', hj₀, hk₀]
      ring
    _ ≤ (R : ℝ)^2+(R : ℝ)*R+(R : ℝ)*((d j : ℝ)*(d k : ℝ))+
        (R : ℝ)*((d j : ℝ)*(d k : ℝ)) := by gcongr
    _ = 2*(R : ℝ)^2+2*(R : ℝ)*((d j : ℝ)*(d k : ℝ)) := by ring
    _ ≤ _ := by gcongr


def modulus (b : Branch) : ℕ := b.1*b.2*(b.1+b.2)

def gcdData (M : ℕ) (b : Branch) : ℕ × ℕ × ℕ :=
  (M.gcd (value b 0), M.gcd (value b 1), M.gcd (value b 2))

def weight (d : ℕ × ℕ × ℕ) : ℕ := d.1*d.2.1*d.2.2

theorem gcdData_weight (M : ℕ) {b : Branch} (h : b.1.Coprime b.2) :
    weight (gcdData M b) = M.gcd (modulus b) := by
  unfold modulus
  rw [← factors_prod, gcd_prod _ (factors_coprime h), Fin.prod_univ_three]
  rfl

theorem gcd_sum_of_bound {S : Finset Branch} {M R : ℕ} {H : ℝ}
    (hM : 0 < M) (hH : 0 ≤ H)
    (hpos : ∀ b ∈ S, 0 < b.1 ∧ 0 < b.2)
    (hco : ∀ b ∈ S, b.1.Coprime b.2)
    (hR : ∀ b ∈ S, ∀ i, value b i ≤ R)
    (hG : ∀ b ∈ S, (M.gcd (modulus b) : ℝ) ≤ H) :
    ∑ b ∈ S, (M.gcd (modulus b) : ℝ) ≤
      (M.divisors.card : ℝ)^3 * (2*(R : ℝ)^2+2*(R : ℝ)*H^(2/3 : ℝ)) := by
  let D := S.image (gcdData M)
  let F (z : ℕ × ℕ × ℕ) := S.filter (fun b => gcdData M b = z)
  let C : ℝ := 2*(R : ℝ)^2+2*(R : ℝ)*H^(2/3 : ℝ)
  have hC : 0 ≤ C := by unfold C; positivity
  have hD : D.card ≤ M.divisors.card^3 := by
    calc
      D.card ≤ (M.divisors ×ˢ (M.divisors ×ˢ M.divisors)).card := by
        apply Finset.card_le_card
        intro z hz
        obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hz
        simp only [gcdData, Finset.mem_product, Nat.mem_divisors]
        exact ⟨⟨Nat.gcd_dvd_left _ _, hM.ne'⟩,
          ⟨Nat.gcd_dvd_left _ _, hM.ne'⟩, ⟨Nat.gcd_dvd_left _ _, hM.ne'⟩⟩
      _ = _ := by simp [Finset.card_product, pow_succ, mul_assoc]
  have hF (z : ℕ × ℕ × ℕ) (hz : z ∈ D) :
      (weight z : ℝ)*((F z).card : ℝ) ≤ C := by
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hz
    let d (i : Fin 3) := M.gcd (value b i)
    have hd (i : Fin 3) : 0 < d i := Nat.gcd_pos_of_pos_left _ hM
    have hdR (i : Fin 3) : d i ≤ R := (Nat.le_of_dvd
      (factors_pos (hpos b hb).1 (hpos b hb).2 i) (Nat.gcd_dvd_right _ _)).trans (hR b hb i)
    have hdiv (a : Branch) (ha : a ∈ F (gcdData M b)) (i : Fin 3) : d i ∣ value a i := by
      have he := (Finset.mem_filter.1 ha).2
      have he' : M.gcd (value b i) = M.gcd (value a i) := by
        fin_cases i
        · exact (congrArg Prod.fst he).symm
        · exact (congrArg (fun z => z.2.1) he).symm
        · exact (congrArg (fun z => z.2.2) he).symm
      change M.gcd (value b i) ∣ value a i
      rw [he']
      exact Nat.gcd_dvd_right _ _
    have hcop : Pairwise (fun i j => (d i).Coprime (d j)) := by
      intro i j hij
      exact ((factors_coprime (hco b hb) hij).of_dvd_left
        (Nat.gcd_dvd_right _ _)).of_dvd_right (Nat.gcd_dvd_right _ _)
    have h := weighted_card_of_divisibility hd hdR hdiv
      (fun a ha i => hR a (Finset.mem_filter.1 ha).1 i) hcop
    change (weight (gcdData M b) : ℝ)*((F (gcdData M b)).card : ℝ) ≤
      2*(R : ℝ)^2+2*(R : ℝ)*(weight (gcdData M b) : ℝ)^(2/3 : ℝ) at h
    apply h.trans
    unfold C
    rw [gcdData_weight M (hco b hb)]
    exact add_le_add_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hG b hb) (by norm_num : (0 : ℝ) ≤ 2/3))
      (by positivity : 0 ≤ 2*(R : ℝ))) _
  have hsum : ∑ b ∈ S, (M.gcd (modulus b) : ℝ) =
      ∑ z ∈ D, (weight z : ℝ)*((F z).card : ℝ) := by
    calc
      _ = ∑ b ∈ S, (weight (gcdData M b) : ℝ) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [gcdData_weight M (hco b hb)]
      _ = ∑ z ∈ D, ∑ b ∈ F z, (weight z : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to' (g := gcdData M) (s := S) (t := D)
          (fun b hb => Finset.mem_image_of_mem _ hb) (fun z => (weight z : ℝ))).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro z hz
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  rw [hsum]
  calc
    _ ≤ ∑ z ∈ D, C := Finset.sum_le_sum hF
    _ = (D.card : ℝ)*C := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (M.divisors.card : ℝ)^3*C := mul_le_mul_of_nonneg_right (by exact_mod_cast hD) hC


theorem gcd_sum_at_scale (D : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
    ∀ {S : Finset Branch} {s : ℕ}, 1 ≤ s →
      2*(D : ℝ)*s < ((s : ℝ)^(99/100 : ℝ))^2 →
      (∀ b ∈ S, 0 < b.1 ∧ 0 < b.2 ∧ b.1 ≤ D*s ∧ b.2 ≤ D*s ∧ b.1.Coprime b.2) →
      ∀ b ∈ S,
        (∃ P Q : ℕ, P.Prime ∧ Q.Prime ∧ P ∣ b.1 ∧ Q ∣ b.2 ∧
          (s : ℝ)^(99/100 : ℝ) ≤ P ∧ (s : ℝ)^(99/100 : ℝ) ≤ Q) →
        ∑ a ∈ S, ((modulus b).gcd (modulus a) : ℝ) ≤ K*(s : ℝ)^3 := by
  obtain ⟨J, hJ₁, hJ⟩ := LCMDivisorBound.divisor_bound
  let G : ℝ := 64*(D : ℝ)^6+2*(D : ℝ)^3
  let A : ℝ := 2*(D : ℝ)^3
  let B : ℝ := J^3*A^(3/100 : ℝ)
  let C : ℝ := 8*(D : ℝ)^2+4*(D : ℝ)*G^(2/3 : ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨B*C+2*A, by positivity, ?_⟩
  intro S s hs hLarge hS b hb hbP
  obtain ⟨hp, hq, hpR, hqR, hpq⟩ := hS b hb
  obtain ⟨P, Q, hP, hQ, hPp, hQq, hLP, hLQ⟩ := hbP
  let M := modulus b
  let T := S.filter (fun a => ¬(a = b ∨ a = (b.2,b.1)))
  let E := S.filter (fun a => a = b ∨ a = (b.2,b.1))
  let H := G*(s : ℝ)^(51/25 : ℝ)
  have hs₁ : 1 ≤ (s : ℝ) := by exact_mod_cast hs
  have hs₀ : 0 < (s : ℝ) := by linarith
  have hM : 0 < M := by unfold M modulus; positivity
  have hMbound : (M : ℝ) ≤ A*(s : ℝ)^3 := by
    have hpR' : (b.1 : ℝ) ≤ (D : ℝ)*s := by exact_mod_cast hpR
    have hqR' : (b.2 : ℝ) ≤ (D : ℝ)*s := by exact_mod_cast hqR
    unfold M modulus A
    push_cast
    calc
      (b.1 : ℝ)*b.2*(b.1+b.2) ≤ ((D : ℝ)*s)*((D : ℝ)*s)*((D : ℝ)*s+(D : ℝ)*s) := by
        gcongr
      _ = _ := by ring
  have hTBound := gcd_sum_of_bound (S := T) (R := 2*D*s) (M := M) (H := H)
    hM (by unfold H; positivity)
    (fun a ha => ⟨(hS a (Finset.mem_filter.1 ha).1).1, (hS a (Finset.mem_filter.1 ha).1).2.1⟩)
    (fun a ha => (hS a (Finset.mem_filter.1 ha).1).2.2.2.2)
    (fun a ha i => by
      have h := factors_le_sum a.1 a.2 i
      have h₁ := (hS a (Finset.mem_filter.1 ha).1).2.2.1
      have h₂ := (hS a (Finset.mem_filter.1 ha).1).2.2.2.1
      change factors a.1 a.2 i ≤ 2*D*s
      rw [mul_assoc]
      omega)
    (fun a ha => by
      obtain ⟨ha₀, ha₁, ha₂, ha₃, hac⟩ := hS a (Finset.mem_filter.1 ha).1
      apply gcd_bound_at_scale hp hq ha₀ ha₁ hs hpR hqR ha₂ ha₃ hpq hac
        hP hQ hPp hQq hLP hLQ hLarge
      intro he
      apply (Finset.mem_filter.1 ha).2
      rcases he with he | he
      · exact Or.inl (Prod.ext he.1.symm he.2.symm)
      · exact Or.inr (Prod.ext he.2.symm he.1.symm))
  have hcount : (M.divisors.card : ℝ)^3 ≤ B*(s : ℝ)^(1/10 : ℝ) := by
    have h₀ := hJ M hM
    have h₁ := Real.rpow_le_rpow (show 0 ≤ (M : ℝ) by positivity) hMbound
      (by norm_num : (0 : ℝ) ≤ 3/100)
    calc
      (M.divisors.card : ℝ)^3 ≤ (J*(M : ℝ)^(1/100 : ℝ))^3 := by gcongr
      _ = J^3*(M : ℝ)^(3/100 : ℝ) := by
        rw [mul_pow, ← Real.rpow_mul_natCast (by positivity)]
        norm_num
      _ ≤ J^3*(A*(s : ℝ)^3)^(3/100 : ℝ) := mul_le_mul_of_nonneg_left h₁ (by positivity)
      _ = B*(s : ℝ)^(9/100 : ℝ) := by
        rw [Real.mul_rpow hA (by positivity), ← Real.rpow_natCast_mul hs₀.le]
        norm_num [B, mul_assoc]
      _ ≤ B*(s : ℝ)^(1/10 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hs₁ (by norm_num)) hB
  have hH : H^(2/3 : ℝ) ≤ G^(2/3 : ℝ)*(s : ℝ)^(7/5 : ℝ) := by
    unfold H
    rw [Real.mul_rpow hG (by positivity), ← Real.rpow_mul hs₀.le]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hs₁ (by norm_num)) (by positivity)
  have hterm : 2*((2*D*s : ℕ) : ℝ)^2+2*((2*D*s : ℕ) : ℝ)*H^(2/3 : ℝ) ≤
      C*(s : ℝ)^(12/5 : ℝ) := by
    push_cast
    have hsq : (s : ℝ)^2 ≤ (s : ℝ)^(12/5 : ℝ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hs₁ (by norm_num)
    calc
      _ ≤ 2*(2*(D : ℝ)*s)^2+2*(2*(D : ℝ)*s)*(G^(2/3 : ℝ)*(s : ℝ)^(7/5 : ℝ)) := by
        gcongr
      _ = 8*(D : ℝ)^2*(s : ℝ)^2+4*(D : ℝ)*G^(2/3 : ℝ)*((s : ℝ)*(s : ℝ)^(7/5 : ℝ)) := by ring
      _ = 8*(D : ℝ)^2*(s : ℝ)^2+4*(D : ℝ)*G^(2/3 : ℝ)*(s : ℝ)^(12/5 : ℝ) := by
        have he : (s : ℝ)*(s : ℝ)^(7/5 : ℝ) = (s : ℝ)^(12/5 : ℝ) := by
          conv_lhs => arg 1; rw [← Real.rpow_one (s : ℝ)]
          rw [← Real.rpow_add hs₀]
          norm_num
        rw [he]
      _ ≤ C*(s : ℝ)^(12/5 : ℝ) := by
        rw [show C = 8*(D : ℝ)^2+4*(D : ℝ)*G^(2/3 : ℝ) by rfl, add_mul]
        gcongr
  have hT : ∑ a ∈ T, (M.gcd (modulus a) : ℝ) ≤ B*C*(s : ℝ)^3 := by
    refine hTBound.trans ?_
    calc
      _ ≤ (B*(s : ℝ)^(1/10 : ℝ))*(C*(s : ℝ)^(12/5 : ℝ)) := by gcongr
      _ = B*C*(s : ℝ)^(5/2 : ℝ) := by
        rw [show (5/2 : ℝ) = 1/10+12/5 by norm_num, Real.rpow_add hs₀]
        ring
      _ ≤ _ := by
        rw [← Real.rpow_natCast]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hs₁ (by norm_num)) (by positivity)
  have hEcard : E.card ≤ 2 := by
    calc
      E.card ≤ ({b,(b.2,b.1)} : Finset Branch).card := by
        apply Finset.card_le_card
        intro a ha
        simpa using (Finset.mem_filter.1 ha).2
      _ ≤ _ := Finset.card_insert_le _ _
  have hE : ∑ a ∈ E, (M.gcd (modulus a) : ℝ) ≤ 2*A*(s : ℝ)^3 := by
    calc
      _ ≤ ∑ a ∈ E, (M : ℝ) := Finset.sum_le_sum (fun _ _ => by
        exact_mod_cast Nat.gcd_le_left _ hM)
      _ = (E.card : ℝ)*(M : ℝ) := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2*(A*(s : ℝ)^3) := by gcongr; exact_mod_cast hEcard
      _ = _ := by ring
  change ∑ a ∈ S, (M.gcd (modulus a) : ℝ) ≤ _
  have hsplit : ∑ a ∈ T, (M.gcd (modulus a) : ℝ) +
      ∑ a ∈ E, (M.gcd (modulus a) : ℝ) = ∑ a ∈ S, (M.gcd (modulus a) : ℝ) := by
    unfold T E
    rw [add_comm, Finset.sum_filter_add_sum_filter_not]
  rw [← hsplit, add_mul]
  exact add_le_add hT hE

end LCMGCDSum

/-
# Finite CRT progressions of low-LCM triples

Each coprime pair determines a residue class of starts. A long interval contains many starts
from every branch, and the first pair of coordinates identifies the branch of a triple.
-/

open scoped BigOperators

namespace LCMCandidates

open LCMGCDSum

abbrev Candidate := Sigma (fun _ : Branch => ℕ)

def starts (s U : ℕ) (b : Branch) : Finset ℕ :=
  (Finset.Icc (U*s) (2*U*s)).filter
    (fun x => b.1*(b.1+b.2) ∣ x ∧ b.2 ∣ x+b.1)

theorem mem_starts {s U : ℕ} {b : Branch} {x : ℕ} :
    x ∈ starts s U b ↔ (U*s ≤ x ∧ x ≤ 2*U*s) ∧
      (b.1*(b.1+b.2) ∣ x ∧ b.2 ∣ x+b.1) := by
  simp only [starts, Finset.mem_filter, Finset.mem_Icc]

theorem starts_modEq {s U : ℕ} {b : Branch} (hco : b.1.Coprime b.2)
    {x y : ℕ} (hx : x ∈ starts s U b) (hy : y ∈ starts s U b) :
    x ≡ y [MOD modulus b] := by
  have hx' := (mem_starts.1 hx).2
  have hy' := (mem_starts.1 hy).2
  have hp := (Nat.modEq_zero_iff_dvd.2 hx'.1).trans (Nat.modEq_zero_iff_dvd.2 hy'.1).symm
  have hq := (Nat.modEq_zero_iff_dvd.2 hx'.2).trans (Nat.modEq_zero_iff_dvd.2 hy'.2).symm
  have hcp : (b.1*(b.1+b.2)).Coprime b.2 :=
    hco.mul_left (Nat.coprime_add_self_left.2 hco)
  have h := Nat.mod_lcm hp (Nat.ModEq.add_right_cancel' b.1 hq)
  rw [hcp.lcm_eq_mul] at h
  simpa [modulus, mul_assoc, mul_left_comm, mul_comm] using h

theorem modulus_bounds {s D : ℕ} {b : Branch}
    (hlo₀ : s ≤ b.1) (hlo₁ : s ≤ b.2) (hhi₀ : b.1 ≤ D*s) (hhi₁ : b.2 ≤ D*s) :
    s^3 ≤ modulus b ∧ modulus b ≤ 2*D^3*s^3 := by
  unfold modulus
  constructor
  · calc
      s^3 = s*s*s := by ring
      _ ≤ _ := by gcongr; omega
  · calc
      _ ≤ (D*s)*(D*s)*(D*s+D*s) := by gcongr
      _ = _ := by ring

theorem starts_card_period {p q U s : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hco : p.Coprime q) :
    (U*s / LCMTripleConstruction.period p q - 1) ≤ (starts s U (p,q)).card := by
  let M := LCMTripleConstruction.period p q
  have hm : 0 < M := by unfold M LCMTripleConstruction.period; positivity
  obtain ⟨r, hr, hCRT⟩ := LCMTripleConstruction.progression_residue hp hq hco
  change r < M at hr
  let k := (U*s)/M
  let A := Finset.range (k-1)
  let f (i : ℕ) := r+(k+1+i)*M
  have hmod := Nat.mod_lt (U*s) hm
  have hEq := Nat.mod_add_div (U*s) M
  change (U*s)%M + M*k = U*s at hEq
  rw [← show A.card = U*s / LCMTripleConstruction.period p q - 1 by simp [A,k,M]]
  apply Finset.card_le_card_of_injOn f
  · intro i hi
    have hi' : i < k-1 := Finset.mem_range.1 hi
    apply mem_starts.2
    refine ⟨⟨?_,?_⟩,?_⟩
    · have ht : (k+1)*M ≤ (k+1+i)*M := Nat.mul_le_mul_right _ (by omega)
      unfold f
      rw [add_mul, one_mul] at ht
      nlinarith
    · have ht : (k+1+i+1)*M ≤ (2*k)*M := Nat.mul_le_mul_right _ (by omega)
      have hkM : k*M ≤ U*s := by
        rw [mul_comm]
        omega
      calc
        f i ≤ (k+1+i+1)*M := by
          unfold f
          rw [show (k+1+i+1)*M = (k+1+i)*M+M by ring]
          omega
        _ ≤ (2*k)*M := ht
        _ ≤ 2*U*s := by
          rw [mul_assoc, mul_assoc]
          exact Nat.mul_le_mul_left 2 hkM
    · simpa [f,M,mul_comm] using hCRT (k+1+i)
  · intro i _ j _ h
    have he : (k+1+i)*M = (k+1+j)*M := Nat.add_left_cancel h
    have he' := Nat.eq_of_mul_eq_mul_right hm he
    omega

theorem starts_card_lower {s U D : ℕ} {b : Branch}
    (hs : 1 ≤ s) (hD : 1 ≤ D)
    (hlo₀ : s ≤ b.1) (hlo₁ : s ≤ b.2) (hhi₀ : b.1 ≤ D*s) (hhi₁ : b.2 ≤ D*s)
    (hco : b.1.Coprime b.2) (hU : 8*D^3*s^2 ≤ U) :
    (U : ℝ)/(4*(D : ℝ)^3*(s : ℝ)^2) ≤ ((starts s U b).card : ℝ) := by
  have hp : 0 < b.1 := hs.trans hlo₀
  have hq : 0 < b.2 := hs.trans hlo₁
  have hs' : 0 < (s : ℝ) := by exact_mod_cast hs
  have hD' : 0 < (D : ℝ) := by exact_mod_cast hD
  let M := LCMTripleConstruction.period b.1 b.2
  let k := U*s/M
  have hm : 0 < M := by unfold M LCMTripleConstruction.period; positivity
  have hmr : 0 < (M : ℝ) := by exact_mod_cast hm
  have hM : M = modulus b := by unfold M LCMTripleConstruction.period modulus; ring
  have hMupper : (M : ℝ) ≤ 2*(D : ℝ)^3*(s : ℝ)^3 := by
    rw [hM]
    exact_mod_cast (modulus_bounds hlo₀ hlo₁ hhi₀ hhi₁).2
  have hU' : 8*(D : ℝ)^3*(s : ℝ)^2 ≤ (U : ℝ) := by exact_mod_cast hU
  have hfour : 4 ≤ (U : ℝ)*s/(M : ℝ) := by
    apply (le_div_iff₀ hmr).2
    have hmul := mul_le_mul_of_nonneg_right hU' hs'.le
    nlinarith
  have hk : (U : ℝ)*s/(M : ℝ) ≤ (k : ℝ)+1 := by
    apply (div_le_iff₀ hmr).2
    have hmod := Nat.mod_lt (U*s) hm
    have hEq := Nat.mod_add_div (U*s) M
    have he : U*s ≤ (k+1)*M := by
      unfold k
      rw [add_mul, one_mul]
      nlinarith
    exact_mod_cast he
  have hk1 : 1 ≤ k := by
    have hkr : (1 : ℝ) ≤ (k : ℝ) := by linarith
    exact_mod_cast hkr
  have hcard := starts_card_period (U := U) (s := s) hp hq hco
  have hcardR : ((k-1 : ℕ) : ℝ) ≤ ((starts s U b).card : ℝ) := by exact_mod_cast hcard
  rw [Nat.cast_sub hk1, Nat.cast_one] at hcardR
  calc
    _ = ((U : ℝ)*s)/(2*(2*(D : ℝ)^3*(s : ℝ)^3)) := by field_simp; ring
    _ ≤ ((U : ℝ)*s)/(2*(M : ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hMupper (by norm_num))
    _ = ((U : ℝ)*s/(M : ℝ))/2 := by ring
    _ ≤ (k : ℝ)-1 := by linarith
    _ ≤ _ := hcardR

def candidates (S : Finset Branch) (s U : ℕ) : Finset Candidate :=
  S.sigma (starts s U)

theorem candidates_card_lower {S : Finset Branch} {s U D : ℕ}
    (hs : 1 ≤ s) (hD : 1 ≤ D) (hU : 8*D^3*s^2 ≤ U)
    (hS : ∀ b ∈ S, s ≤ b.1 ∧ s ≤ b.2 ∧ b.1 ≤ D*s ∧ b.2 ≤ D*s ∧ b.1.Coprime b.2)
    (hcard : (s : ℝ)^2/20000 ≤ (S.card : ℝ)) :
    (U : ℝ)/(80000*(D : ℝ)^3) ≤ ((candidates S s U).card : ℝ) := by
  have hs' : 0 < (s : ℝ) := by exact_mod_cast hs
  have hD' : 0 < (D : ℝ) := by exact_mod_cast hD
  rw [candidates, Finset.card_sigma, Nat.cast_sum]
  calc
    _ = ((s : ℝ)^2/20000)*((U : ℝ)/(4*(D : ℝ)^3*(s : ℝ)^2)) := by field_simp; ring
    _ ≤ (S.card : ℝ)*((U : ℝ)/(4*(D : ℝ)^3*(s : ℝ)^2)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = ∑ b ∈ S, ((U : ℝ)/(4*(D : ℝ)^3*(s : ℝ)^2)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro b hb
      obtain ⟨h₀,h₁,h₂,h₃,hc⟩ := hS b hb
      exact starts_card_lower hs hD h₀ h₁ h₂ h₃ hc hU


def conflict (s D : ℕ) (a b : Candidate) : Prop :=
  a.2 ≤ b.2+2*D*s ∧ b.2 ≤ a.2+2*D*s

instance conflictDecidable (s D : ℕ) : DecidableRel (conflict s D) :=
  fun a b => inferInstanceAs (Decidable (a.2 ≤ b.2+2*D*s ∧ b.2 ≤ a.2+2*D*s))

theorem conflict_symm {s D : ℕ} {a b : Candidate} (h : conflict s D a b) :
    conflict s D b a := ⟨h.2,h.1⟩

theorem closePairs_bound {s U D : ℕ} {a b : Branch}
    (hs : 1 ≤ s)
    (ha : s ≤ a.1 ∧ s ≤ a.2 ∧ a.1 ≤ D*s ∧ a.2 ≤ D*s ∧ a.1.Coprime a.2)
    (hb : s ≤ b.1 ∧ s ≤ b.2 ∧ b.1 ≤ D*s ∧ b.2 ≤ D*s ∧ b.1.Coprime b.2) :
    ((LCMProgressionCount.closePairs (starts s U a) (starts s U b) (2*D*s)).card : ℝ) ≤
      (4*(D : ℝ)+1)*s+4*(D : ℝ)*U/(s : ℝ)^4+
        (U : ℝ)/(s : ℝ)^5*((modulus a).gcd (modulus b) : ℝ) := by
  let m := modulus a
  let n := modulus b
  let g := m.gcd n
  let d := m.lcm n
  have hma := (modulus_bounds ha.1 ha.2.1 ha.2.2.1 ha.2.2.2.1).1
  have hnb := (modulus_bounds hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1).1
  have hs' : 0 < (s : ℝ) := by exact_mod_cast hs
  have hm : 0 < m := (pow_pos (show 0 < s by omega) 3).trans_le hma
  have hn : 0 < n := (pow_pos (show 0 < s by omega) 3).trans_le hnb
  have hmr : 0 < (m : ℝ) := by exact_mod_cast hm
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hm
  have hdr : 0 < (d : ℝ) := by exact_mod_cast Nat.lcm_pos hm hn
  have hgr : 0 < (g : ℝ) := by exact_mod_cast hg
  have hEq : (g : ℝ)*(d : ℝ) = (m : ℝ)*(n : ℝ) := by exact_mod_cast Nat.gcd_mul_lcm m n
  have hden : (s : ℝ)^6 ≤ (m : ℝ)*(n : ℝ) := by
    have ha₀ : (s : ℝ)^3 ≤ (m : ℝ) := by exact_mod_cast hma
    have hb₀ : (s : ℝ)^3 ≤ (n : ℝ) := by exact_mod_cast hnb
    calc
      _ = (s : ℝ)^3*(s : ℝ)^3 := by ring
      _ ≤ _ := by gcongr
  have hB := LCMProgressionCount.card_closePairs
    (S := starts s U a) (T := starts s U b) (w := 2*D*s)
    (fun x hx => (mem_starts.1 hx).1.1) (fun x hx => (mem_starts.1 hx).1.2)
    hm hn (fun _ hx _ hy => starts_modEq ha.2.2.2.2 hx hy)
    (fun _ hx _ hy => starts_modEq hb.2.2.2.2 hx hy)
  have hc : 2*U*s-U*s = U*s := by
    rw [two_mul, add_mul, Nat.add_sub_cancel_left]
  rw [hc] at hB
  push_cast at hB
  have hg1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  apply hB.trans
  calc
    _ = 1+(4*(D : ℝ)*s)/(g : ℝ)+(4*(D : ℝ)*U*(s : ℝ)^2)/((m : ℝ)*(n : ℝ))+
        ((U : ℝ)*s*(g : ℝ))/((m : ℝ)*(n : ℝ)) := by
      rw [← hEq]
      field_simp [hgr.ne', hdr.ne']
      ring
    _ ≤ (s : ℝ)+(4*(D : ℝ)*s)+(4*(D : ℝ)*U*(s : ℝ)^2)/(s : ℝ)^6+
        ((U : ℝ)*s*(g : ℝ))/(s : ℝ)^6 := by
      apply add_le_add (add_le_add (add_le_add hs1 ?_) ?_) ?_
      · exact div_le_self (by positivity) hg1
      · exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      · exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by
      change _ = _+_+(U : ℝ)/(s : ℝ)^5*(g : ℝ)
      field_simp [hs'.ne']
      ring

theorem ordered_conflicts_le_sum {S : Finset Branch} {s U D : ℕ} :
    ((((candidates S s U) ×ˢ (candidates S s U)).filter
      (fun z => conflict s D z.1 z.2)).card : ℝ) ≤
      ∑ a ∈ S, ∑ b ∈ S,
        ((LCMProgressionCount.closePairs (starts s U a) (starts s U b) (2*D*s)).card : ℝ) := by
  let C := candidates S s U
  let E := (C ×ˢ C).filter (fun z => conflict s D z.1 z.2)
  let F := (S ×ˢ S).sigma (fun z =>
    LCMProgressionCount.closePairs (starts s U z.1) (starts s U z.2) (2*D*s))
  have h : E.card ≤ F.card := by
    let f : Candidate × Candidate → Sigma (fun _ : Branch × Branch => ℕ × ℕ) :=
      fun z => ⟨(z.1.1,z.2.1),(z.1.2,z.2.2)⟩
    apply Finset.card_le_card_of_injOn f
    · intro z hz
      obtain ⟨hz,hcon⟩ := Finset.mem_filter.1 hz
      obtain ⟨ha,hb⟩ := Finset.mem_product.1 hz
      obtain ⟨ha₀,ha₁⟩ := Finset.mem_sigma.1 ha
      obtain ⟨hb₀,hb₁⟩ := Finset.mem_sigma.1 hb
      exact Finset.mem_sigma.2 ⟨Finset.mem_product.2 ⟨ha₀,hb₀⟩,
        Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨ha₁,hb₁⟩,hcon⟩⟩
    · intro x _ y _ hxy
      let inv (z : Sigma (fun _ : Branch × Branch => ℕ × ℕ)) : Candidate × Candidate :=
        (⟨z.1.1,z.2.1⟩,⟨z.1.2,z.2.2⟩)
      exact congrArg inv hxy
  change (E.card : ℝ) ≤ _
  have hr : (E.card : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast h
  refine hr.trans_eq ?_
  dsimp only [F]
  rw [Finset.card_sigma, Nat.cast_sum, Finset.sum_product]

theorem candidates_conflicts_bound (D : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧
    ∀ {S : Finset Branch} {s U : ℕ}, 1 ≤ s → s^5 ≤ U →
      2*(D : ℝ)*s < ((s : ℝ)^(99/100 : ℝ))^2 →
      (∀ b ∈ S, s ≤ b.1 ∧ s ≤ b.2 ∧ b.1 ≤ D*s ∧ b.2 ≤ D*s ∧ b.1.Coprime b.2 ∧
        ∃ P Q : ℕ, P.Prime ∧ Q.Prime ∧ P ∣ b.1 ∧ Q ∣ b.2 ∧
          (s : ℝ)^(99/100 : ℝ) ≤ P ∧ (s : ℝ)^(99/100 : ℝ) ≤ Q) →
      (((((candidates S s U) ×ˢ (candidates S s U)).filter
        (fun z => conflict s D z.1 z.2)).card : ℕ) : ℝ) ≤ L*(U : ℝ) := by
  obtain ⟨K,hK,hSum⟩ := gcd_sum_at_scale D
  let L := (D : ℝ)^4*(8*(D : ℝ)+1)+(D : ℝ)^2*K
  refine ⟨L, by unfold L; positivity, ?_⟩
  intro S s U hs hU hLarge hS
  have hs' : 0 < (s : ℝ) := by exact_mod_cast hs
  have hU' : (s : ℝ)^5 ≤ (U : ℝ) := by exact_mod_cast hU
  let A := (4*(D : ℝ)+1)*s+4*(D : ℝ)*U/(s : ℝ)^4
  let B := (U : ℝ)/(s : ℝ)^5
  have hS₀ (b : Branch) (hb : b ∈ S) :
      0 < b.1 ∧ 0 < b.2 ∧ b.1 ≤ D*s ∧ b.2 ≤ D*s ∧ b.1.Coprime b.2 := by
    obtain ⟨h₀,h₁,h₂,h₃,hc,_⟩ := hS b hb
    exact ⟨hs.trans h₀,hs.trans h₁,h₂,h₃,hc⟩
  have hS₁ (b : Branch) (hb : b ∈ S) :
      s ≤ b.1 ∧ s ≤ b.2 ∧ b.1 ≤ D*s ∧ b.2 ≤ D*s ∧ b.1.Coprime b.2 := by
    obtain ⟨h₀,h₁,h₂,h₃,hc,_⟩ := hS b hb
    exact ⟨h₀,h₁,h₂,h₃,hc⟩
  have hcard : (S.card : ℝ) ≤ (D : ℝ)^2*(s : ℝ)^2 := by
    let R := Finset.Icc 1 (D*s)
    have h : S ⊆ R ×ˢ R := by
      intro b hb
      obtain ⟨h₀,h₁,h₂,h₃,_⟩ := hS₀ b hb
      exact Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨h₀,h₂⟩,Finset.mem_Icc.2 ⟨h₁,h₃⟩⟩
    have hcard := Finset.card_le_card h
    have hr : R.card = D*s := by simp [R,Nat.card_Icc]
    rw [Finset.card_product, hr] at hcard
    have hreal : (S.card : ℝ) ≤ ((D : ℝ)*s)*((D : ℝ)*s) := by exact_mod_cast hcard
    convert hreal using 1
    ring
  have hbound (a : Branch) (ha : a ∈ S) :
      ∑ b ∈ S, ((modulus a).gcd (modulus b) : ℝ) ≤ K*(s : ℝ)^3 :=
    hSum hs hLarge hS₀ a ha (hS a ha).2.2.2.2.2
  refine ordered_conflicts_le_sum.trans ?_
  calc
    _ ≤ ∑ a ∈ S, ∑ b ∈ S, (A+B*((modulus a).gcd (modulus b) : ℝ)) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact closePairs_bound hs (hS₁ a ha) (hS₁ b hb)
    _ ≤ ∑ _a ∈ S, ((S.card : ℝ)*A+B*(K*(s : ℝ)^3)) := by
      apply Finset.sum_le_sum
      intro a ha
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
      exact add_le_add_right (mul_le_mul_of_nonneg_left (hbound a ha) (by unfold B; positivity)) _
    _ = (S.card : ℝ)*((S.card : ℝ)*A+B*(K*(s : ℝ)^3)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((D : ℝ)^2*(s : ℝ)^2)*(((D : ℝ)^2*(s : ℝ)^2)*A+B*(K*(s : ℝ)^3)) := by
      have hA : 0 ≤ A := by unfold A; positivity
      have hB : 0 ≤ B := by unfold B; positivity
      gcongr
    _ = (D : ℝ)^4*(4*(D : ℝ)+1)*(s : ℝ)^5+
        ((D : ℝ)^4*(4*(D : ℝ))+(D : ℝ)^2*K)*U := by
      unfold A B
      field_simp [hs'.ne']
      ring
    _ ≤ (D : ℝ)^4*(4*(D : ℝ)+1)*(U : ℝ)+
        ((D : ℝ)^4*(4*(D : ℝ))+(D : ℝ)^2*K)*U :=
      add_le_add_left (mul_le_mul_of_nonneg_left hU' (by positivity)) _
    _ = L*(U : ℝ) := by unfold L; ring

end LCMCandidates

/- A positive-density packing from a linear bound on ordered conflicts. -/

namespace ConflictPacking

open scoped BigOperators

private lemma ordered_count {V : Type*} (A : Finset V) (R : V → V → Prop) [DecidableRel R] :
    ((A ×ˢ A).filter (fun p => R p.1 p.2)).card =
      ∑ x ∈ A, (A.filter (R x)).card := by
  classical
  let P := (A ×ˢ A).filter (fun p => R p.1 p.2)
  have hMap : (P : Set (V × V)).MapsTo Prod.fst (A : Set V) := by
    intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  change P.card = _
  rw [Finset.card_eq_sum_card_fiberwise hMap]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.card_bij (fun p _ => p.2)
  · intro p hp
    obtain ⟨hP,hpx⟩ := Finset.mem_filter.mp hp
    obtain ⟨hA,hR⟩ := Finset.mem_filter.mp hP
    exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hA).2, hpx ▸ hR⟩
  · intro p hp q hq h
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    exact Prod.ext (hp'.trans hq'.symm) h
  · intro y hy
    obtain ⟨hyA,hyR⟩ := Finset.mem_filter.mp hy
    exact ⟨(x,y), Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hyA⟩,hyR⟩,rfl⟩, rfl⟩

private lemma choose_packing {V : Type*} (A L : Finset V) (R : V → V → Prop)
    [DecidableRel R] (hSym : (∀ ⦃x y⦄, R x y → R y x)) (d : ℝ)
    (hLA : L ⊆ A) (hDegree : ∀ x ∈ L, ((A.filter (R x)).card : ℝ) ≤ d) :
    ∃ I ⊆ L, (I : Set V).Pairwise (fun x y => ¬ R x y) ∧
      (L.card : ℝ) ≤ (I.card : ℝ) * (d + 1) := by
  classical
  let packs := L.powerset.filter (fun I : Finset V => (I : Set V).Pairwise (fun x y => ¬ R x y))
  have hPacks (I : Finset V) :
      I ∈ packs ↔ I ⊆ L ∧ (I : Set V).Pairwise (fun x y => ¬ R x y) := by
    simp only [packs, Finset.mem_filter, Finset.mem_powerset]
  have hNon : packs.Nonempty := ⟨∅,(hPacks _).mpr ⟨Finset.empty_subset _,by simp⟩⟩
  obtain ⟨I,hI,hMax⟩ := Finset.exists_max_image packs Finset.card hNon
  obtain ⟨hIL,hInd⟩ := (hPacks I).mp hI
  let row (x : V) := insert x (A.filter (R x))
  have hCover : L ⊆ I.biUnion row := by
    intro x hx
    by_contra hNot
    have hxI : x ∉ I := fun hi => hNot (Finset.mem_biUnion.mpr ⟨x,hi,Finset.mem_insert_self _ _⟩)
    have hFree (v : V) (hv : v ∈ I) : ¬ R v x := by
      intro h
      have hxA : x ∈ A := hLA hx
      exact hNot (Finset.mem_biUnion.mpr ⟨v,hv,Finset.mem_insert_of_mem
        (Finset.mem_filter.mpr ⟨hxA,h⟩)⟩)
    have hNew : ((insert x I : Finset V) : Set V).Pairwise (fun u v => ¬ R u v) := by
      intro u hu v hv huv
      change u ∈ insert x I at hu
      change v ∈ insert x I at hv
      rcases Finset.mem_insert.mp hu with rfl | huI <;> rcases Finset.mem_insert.mp hv with rfl | hvI
      · exact (huv rfl).elim
      · exact fun h => hFree v hvI (hSym h)
      · exact hFree u huI
      · exact hInd huI hvI huv
    have hSub : insert x I ⊆ L := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hyI
      · exact hx
      · exact hIL hyI
    have hMem : insert x I ∈ packs := (hPacks _).mpr ⟨hSub,hNew⟩
    have hBad := hMax _ hMem
    rw [Finset.card_insert_of_notMem hxI] at hBad
    omega
  refine ⟨I,hIL,hInd,?_⟩
  calc
    (L.card : ℝ) ≤ ((I.biUnion row).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hCover
    _ ≤ ∑ x ∈ I, ((row x).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := I) (t := row))
    _ ≤ ∑ _x ∈ I, (d + 1) := by
      apply Finset.sum_le_sum
      intro x hx
      have hRow : ((row x).card : ℝ) ≤ ((A.filter (R x)).card : ℝ) + 1 := by
        exact_mod_cast (Finset.card_insert_le x (A.filter (R x)))
      exact hRow.trans (by linarith [hDegree x (hIL hx)])
    _ = (I.card : ℝ) * (d + 1) := by rw [Finset.sum_const, nsmul_eq_mul]

/-- If the available family has size at least εU and at most CU ordered conflicting
pairs, it has an independent subfamily of size at least δU for a fixed δ > 0. -/
theorem exists_independent {V : Type*} (ε C : ℝ) (hε : 0 < ε) (hC : 0 ≤ C) :
    ∃ δ > 0, ∀ (A : Finset V) (R : V → V → Prop) [DecidableRel R], (∀ ⦃x y⦄, R x y → R y x) →
      ∀ {U : ℝ}, 0 ≤ U → ε * U ≤ (A.card : ℝ) →
      (((A ×ˢ A).filter (fun p => R p.1 p.2)).card : ℝ) ≤ C * U →
      ∃ I ⊆ A, (I : Set V).Pairwise (fun x y => ¬ R x y) ∧ δ * U ≤ (I.card : ℝ) := by
  let d : ℝ := 2 * C / ε + 1
  have hd : 0 < d := by dsimp [d]; positivity
  have hd' : 0 < d + 1 := by positivity
  refine ⟨(ε / 2) / (d + 1),div_pos (half_pos hε) hd',?_⟩
  intro A R _ hSym U hU hA hEdges
  classical
  let degree (x : V) : ℝ := (A.filter (R x)).card
  let low := A.filter (fun x => degree x ≤ d)
  let high := A.filter (fun x => ¬ degree x ≤ d)
  have hMass : (∑ x ∈ A, degree x) ≤ C * U := by
    simpa only [ordered_count A R, Nat.cast_sum, degree] using hEdges
  have hHighTotal : (high.card : ℝ) * d ≤ C * U := by
    calc
      _ = ∑ _x ∈ high, d := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ high, degree x :=
        Finset.sum_le_sum (fun _ hx => (lt_of_not_ge (Finset.mem_filter.mp hx).2).le)
      _ ≤ ∑ x ∈ A, degree x :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by
          dsimp [degree]
          positivity)
      _ ≤ _ := hMass
  have hCD : C ≤ (ε / 2) * d := by
    have hEq : (ε / 2) * d = C + ε / 2 := by
      dsimp [d]
      field_simp [hε.ne']
    linarith
  have hHigh : (high.card : ℝ) ≤ ε * U / 2 := by
    apply (mul_le_mul_iff_of_pos_right hd).mp
    calc
      _ ≤ C * U := hHighTotal
      _ ≤ ((ε / 2) * d) * U := mul_le_mul_of_nonneg_right hCD hU
      _ = (ε * U / 2) * d := by ring
  have hPart : (low.card : ℝ) + (high.card : ℝ) = (A.card : ℝ) := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := A) (fun x => degree x ≤ d)
  have hLow : ε * U / 2 ≤ (low.card : ℝ) := by linarith
  obtain ⟨I,hIL,hInd,hSize⟩ := choose_packing A low R hSym d (Finset.filter_subset _ _)
    (fun x hx => (Finset.mem_filter.mp hx).2)
  refine ⟨I,hIL.trans (Finset.filter_subset _ _),hInd,?_⟩
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  exact (div_le_iff₀ hd').mpr (hLow.trans hSize)

end ConflictPacking

/-
# Gluing finite blocks of low-LCM triples

Finite families of separated triples in arbitrarily late intervals produce a single infinite
increasing sequence with the same infinitely-often lower bounds.
-/

namespace LCMTripleGluing

abbrev Triple := ℕ × ℕ × ℕ

def coord (t : Triple) : ℕ → ℕ
  | 0 => t.1
  | 1 => t.2.1
  | _ => t.2.2

structure Block (c : ℝ) (N : ℕ) where
  X : ℝ
  large : (N : ℝ) < X
  triples : Finset Triple
  nonempty : triples.Nonempty
  ordered : ∀ t ∈ triples, N < t.1 ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2
  separated : ∀ t ∈ triples, ∀ u ∈ triples, t ≠ u →
    t.2.2 < u.1 ∨ u.2.2 < t.1
  small_lcm : ∀ t ∈ triples, ↑((Finset.range 3).lcm (coord t)) < X
  lower : c * X ^ (1 / 3 : ℝ) * Real.log X ≤ (triples.card : ℝ)

def points {c : ℝ} {N : ℕ} (B : Block c N) : Finset ℕ :=
  B.triples.biUnion (fun t => {t.1, t.2.1, t.2.2})

theorem mem_points {c : ℝ} {N : ℕ} (B : Block c N) (u : ℕ) :
    u ∈ points B ↔ ∃ t ∈ B.triples, u = t.1 ∨ u = t.2.1 ∨ u = t.2.2 := by
  simp [points]

theorem above {c : ℝ} {N : ℕ} (B : Block c N) {u : ℕ} (hu : u ∈ points B) :
    N < u := by
  obtain ⟨t, ht, h⟩ := (mem_points B u).1 hu
  obtain ⟨h₀, h₁, h₂⟩ := B.ordered t ht
  rcases h with h | h | h <;> omega

theorem next_index {a : ℕ → ℕ} (ha : StrictMono a) {i j : ℕ}
    (h : a i < a j) (hgap : ∀ k, ¬(a i < a k ∧ a k < a j)) : j = i + 1 := by
  have hij : i < j := (ha.lt_iff_lt).mp h
  by_contra hn
  exact hgap (i+1) ⟨ha (by omega), ha (by omega)⟩

def threshold {c : ℝ} (stage : ∀ N : ℕ, Block c N) : ℕ → ℕ
  | 0 => 0
  | n+1 => max (n+1) (max (threshold stage n) ((points (stage (threshold stage n))).sup id))

theorem assemble {c : ℝ} (hc : 0 < c) (stage : ∀ N : ℕ, Block c N) :
    ∃ (a : ℕ → ℕ) (c' : ℝ), 0 < a 0 ∧ StrictMono a ∧ 0 < c' ∧
      ∀ X₀ : ℝ, ∃ X > X₀,
        (c' * X ^ (1 / 3 : ℝ) * Real.log X).toEReal ≤ (Erdos873.F a X 3 : EReal) := by
  classical
  let limit := threshold stage
  have hlimit : Monotone limit := monotone_nat_of_le_succ (fun n => by
    simp only [limit, threshold]
    omega)
  have h_n_limit : ∀ n, n ≤ limit n := by
    intro n
    cases n with
    | zero => exact Nat.zero_le _
    | succ n =>
      simp only [limit, threshold]
      omega
  let S : Set ℕ := {u | ∃ n, u ∈ points (stage (limit n))}
  have hSpos : ∀ u ∈ S, 0 < u := by
    rintro u ⟨n, hu⟩
    have h := above _ hu
    omega
  have hSinfinite : S.Infinite := by
    apply Set.infinite_of_not_bddAbove
    rintro ⟨N, hN⟩
    obtain ⟨t, ht⟩ := (stage (limit N)).nonempty
    have hm : t.1 ∈ S := ⟨N, (mem_points _ _).2 ⟨t, ht, Or.inl rfl⟩⟩
    have hb : t.1 ≤ N := hN hm
    have ho := ((stage (limit N)).ordered t ht).1
    have hl := h_n_limit N
    omega
  let : Infinite S := hSinfinite.to_subtype
  let e : ℕ ≃o S := Nat.Subtype.orderIsoOfNat S
  let a : ℕ → ℕ := fun i => (e i).1
  have ha : StrictMono a := e.strictMono
  have mem_a (i : ℕ) : a i ∈ S := (e i).2
  have hmem (n : ℕ) (t : Triple) (ht : t ∈ (stage (limit n)).triples) :
      t.1 ∈ S ∧ t.2.1 ∈ S ∧ t.2.2 ∈ S :=
    ⟨⟨n, (mem_points _ _).2 ⟨t, ht, Or.inl rfl⟩⟩,
      ⟨n, (mem_points _ _).2 ⟨t, ht, Or.inr (Or.inl rfl)⟩⟩,
      ⟨n, (mem_points _ _).2 ⟨t, ht, Or.inr (Or.inr rfl)⟩⟩⟩
  have hless {i j u v : ℕ} (hij : i < j) (hu : u ∈ points (stage (limit i)))
      (hv : v ∈ points (stage (limit j))) : u < v := by
    have hsup := Finset.le_sup (f := id) hu
    have hl : u ≤ limit (i+1) := by
      simp only [limit, threshold]
      change u ≤ ((points (stage (threshold stage i))).sup id) at hsup
      omega
    exact (hl.trans (hlimit (a := i+1) (b := j) (by omega))).trans_lt (above _ hv)
  have hwithin {n : ℕ} {t : Triple} (ht : t ∈ (stage (limit n)).triples)
      {u : ℕ} (hu : u ∈ S) (h₀ : t.1 ≤ u) (h₂ : u ≤ t.2.2) :
      u = t.1 ∨ u = t.2.1 ∨ u = t.2.2 := by
    obtain ⟨m, hm⟩ := hu
    rcases lt_trichotomy m n with h | rfl | h
    · have ht₀ := (mem_points _ t.1).2 ⟨t, ht, Or.inl rfl⟩
      exact (not_lt_of_ge h₀ (hless h hm ht₀)).elim
    · obtain ⟨v, hv, hu⟩ := (mem_points _ _).1 hm
      by_cases he : t = v
      · simpa [he] using hu
      obtain ⟨_, hv₀, hv₁⟩ := (stage (limit m)).ordered v hv
      rcases (stage (limit m)).separated t ht v hv he with hs | hs <;>
        rcases hu with h | h | h <;> omega
    · have ht₂ := (mem_points _ t.2.2).2 ⟨t, ht, Or.inr (Or.inr rfl)⟩
      exact (not_lt_of_ge h₂ (hless h ht₂ hm)).elim
  have hrealize (n : ℕ) (t : Triple) (ht : t ∈ (stage (limit n)).triples) :
      ∃ i, a i = t.1 ∧ a (i+1) = t.2.1 ∧ a (i+2) = t.2.2 := by
    obtain ⟨ht₀, ht₁, ht₂⟩ := hmem n t ht
    let i := e.symm ⟨t.1, ht₀⟩
    let j := e.symm ⟨t.2.1, ht₁⟩
    let k := e.symm ⟨t.2.2, ht₂⟩
    have hi : a i = t.1 := congrArg Subtype.val (e.apply_symm_apply ⟨t.1, ht₀⟩)
    have hj : a j = t.2.1 := congrArg Subtype.val (e.apply_symm_apply ⟨t.2.1, ht₁⟩)
    have hk : a k = t.2.2 := congrArg Subtype.val (e.apply_symm_apply ⟨t.2.2, ht₂⟩)
    obtain ⟨_, ht₀₁, ht₁₂⟩ := (stage (limit n)).ordered t ht
    have hij : j = i+1 := next_index ha (by omega) (fun l h => by
      have hloc := hwithin ht (mem_a l) (by omega) (by omega)
      rcases hloc with hloc | hloc | hloc <;> omega)
    have hjk : k = j+1 := next_index ha (by omega) (fun l h => by
      have hloc := hwithin ht (mem_a l) (by omega) (by omega)
      rcases hloc with hloc | hloc | hloc <;> omega)
    exact ⟨i, hi, by rwa [← hij], by rwa [show i+2 = k by omega]⟩
  refine ⟨a, c, hSpos _ (mem_a 0), ha, hc, fun X₀ => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_gt X₀
  let B := stage (limit n)
  have hnB : (n : ℝ) ≤ (limit n : ℝ) := by exact_mod_cast h_n_limit n
  refine ⟨B.X, hn.trans_le (hnB.trans B.large.le), ?_⟩
  have hf : ∀ t ∈ B.triples, ∃ i, a i = t.1 ∧ a (i+1) = t.2.1 ∧ a (i+2) = t.2.2 :=
    hrealize n
  let f (t : Triple) : ℕ := if ht : t ∈ B.triples then (hf t ht).choose else 0
  have hfa (t : Triple) (ht : t ∈ B.triples) :
      a (f t) = t.1 ∧ a (f t+1) = t.2.1 ∧ a (f t+2) = t.2.2 := by
    simpa only [f, dif_pos ht] using (hf t ht).choose_spec
  have hinj : Set.InjOn f (B.triples : Set Triple) := by
    intro t ht u hu h
    obtain ⟨h₀, h₁, h₂⟩ := hfa t ht
    obtain ⟨k₀, k₁, k₂⟩ := hfa u hu
    rw [h] at h₀ h₁ h₂
    exact Prod.ext (h₀.symm.trans k₀) (Prod.ext (h₁.symm.trans k₁) (h₂.symm.trans k₂))
  have hmap : Set.MapsTo f (B.triples : Set Triple)
      {i : ℕ | (Finset.range 3).lcm (fun m => a (i+m)) < B.X} := by
    intro t ht
    have hvalues := hfa t ht
    have heq : (Finset.range 3).lcm (fun m => a (f t+m)) =
        (Finset.range 3).lcm (coord t) := by
      apply Finset.lcm_congr rfl
      intro m hm
      have hm := Finset.mem_range.mp hm
      interval_cases m
      · simpa [coord] using hvalues.1
      · exact hvalues.2.1
      · exact hvalues.2.2
    change ↑((Finset.range 3).lcm (fun m => a (f t+m))) < B.X
    rw [heq]
    exact B.small_lcm t ht
  have hcard := Set.encard_le_encard_of_injOn hmap hinj
  rw [Set.encard_coe_eq_coe_finsetCard] at hcard
  have hcast : ((B.triples.card : ℝ) : EReal) =
      (((B.triples.card : ℕ∞) : ENNReal) : EReal) := by
    rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast, EReal.coe_ennreal_ofReal,
      max_eq_left (by positivity)]
  exact (EReal.coe_le_coe_iff.2 B.lower).trans
    (hcast ▸ EReal.coe_ennreal_strictMono.monotone (ENat.toENNReal_mono hcard))

end LCMTripleGluing

namespace LCMMultiScale

open LCMTripleGluing

/-- The finite interval packing at one scale, with a common cubic LCM budget. -/
structure ScaleFamily (δ K : ℝ) (U s : ℕ) where
  triples : Finset Triple
  ordered : ∀ t ∈ triples, U * s ≤ t.1 ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧
    t.2.2 ≤ 3 * (U * s)
  separated : ∀ t ∈ triples, ∀ v ∈ triples, t ≠ v → t.2.2 < v.1 ∨ v.2.2 < t.1
  small_lcm : ∀ t ∈ triples, ↑((Finset.range 3).lcm (coord t)) ≤ K * (U : ℝ)^3
  lower : δ * (U : ℝ) ≤ (triples.card : ℝ)

private theorem ordered_scales {U J i j : ℕ} (hU : 0 < U) (hij : i < j) :
    3 * (U * 4^(J+i)) < U * 4^(J+j) := by
  have hle : 4^(J+i+1) ≤ (4 : ℕ)^(J+j) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hpos : 0 < U * 4^(J+i) := Nat.mul_pos hU (by positivity)
  calc
    _ < 4 * (U * 4^(J+i)) := by omega
    _ = U * 4^(J+i+1) := by rw [pow_succ]; ring
    _ ≤ _ := Nat.mul_le_mul_left U hle

theorem assemble_scales {δ K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K) {s₀ : ℕ}
    (hscale : ∀ s ≥ s₀, ∀ U : ℕ, s^5 ≤ U → Nonempty (ScaleFamily δ K U s)) :
    ∃ c > 0, ∀ N : ℕ, Nonempty (Block c N) := by
  classical
  let W : ℝ := K + 1
  let L : ℝ := Real.log W + 30 * Real.log 4
  let c : ℝ := δ / (W ^ (1 / 3 : ℝ) * L)
  have hW : 1 ≤ W := by dsimp [W]; linarith
  have hWpos : 0 < W := zero_lt_one.trans_le hW
  have hLogW : 0 ≤ Real.log W := Real.log_nonneg hW
  have hLog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hL : 0 < L := by dsimp [L]; linarith
  refine ⟨c, by dsimp [c]; positivity, fun N => ?_⟩
  let J := max s₀ 1
  let M := max J (N + 1)
  let U : ℕ := 4^(5 * (J+M))
  let X : ℝ := W * (U : ℝ)^3
  have hJM : J ≤ M := le_max_left _ _
  have hM : 1 ≤ M := (Nat.succ_le_succ (Nat.zero_le N)).trans (le_max_right _ _)
  have hNUₙ : N < U :=
    (show N ≤ 5 * (J+M) by have := le_max_right J (N+1); omega).trans_lt
      (Nat.lt_pow_self (by decide : 1 < 4))
  have hU : 0 < U := Nat.zero_lt_of_lt hNUₙ
  have hUr : 0 < (U : ℝ) := by exact_mod_cast hU
  have hUr1 : 1 ≤ (U : ℝ) := by exact_mod_cast hU
  have hUX : (U : ℝ) ≤ X := by
    calc
      _ ≤ (U : ℝ)^3 := le_self_pow₀ hUr1 (by norm_num)
      _ = 1 * (U : ℝ)^3 := by rw [one_mul]
      _ ≤ X := mul_le_mul_of_nonneg_right hW (by positivity)
  have hLarge : (N : ℝ) < X :=
    (by exact_mod_cast hNUₙ : (N : ℝ) < (U : ℝ)).trans_le hUX
  have hScale (i : Fin M) : s₀ ≤ 4^(J + (i : ℕ)) :=
    (le_max_left s₀ 1).trans ((Nat.le_add_right _ _).trans
      (Nat.lt_pow_self (by decide : 1 < 4)).le)
  have hBudget (i : Fin M) : (4^(J + (i : ℕ)))^5 ≤ U := by
    rw [← pow_mul]
    have hI := i.isLt
    apply Nat.pow_le_pow_right (by decide)
    omega
  obtain ⟨A⟩ : Nonempty (∀ i : Fin M, ScaleFamily δ K U (4^(J + (i : ℕ)))) :=
    ⟨fun i => (hscale _ (hScale i) U (hBudget i)).some⟩
  let T := Finset.univ.biUnion (fun i : Fin M => (A i).triples)
  have hCross {i j : Fin M} (hij : i < j)
      {u v : Triple} (hu : u ∈ (A i).triples) (hv : v ∈ (A j).triples) :
      u.2.2 < v.1 :=
    (((A i).ordered u hu).2.2.2.trans_lt (ordered_scales hU hij)).trans_le
      ((A j).ordered v hv).1
  have hCard : T.card = ∑ i : Fin M, (A i).triples.card := by
    dsimp only [T]
    apply Finset.card_biUnion
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro u hu hv
    have hOrd := (A i).ordered u hu
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have h := hCross hlt hu hv
      omega
    · have h := hCross hgt hv hu
      omega
  have hLower : δ * (U : ℝ) * (M : ℝ) ≤ (T.card : ℝ) := by
    rw [hCard, Nat.cast_sum]
    calc
      _ = ∑ _ : Fin M, δ * (U : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum (fun i _ => (A i).lower)
  have hNonempty : T.Nonempty := Finset.card_pos.mp (by
    have hmR : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M from hM)
    exact_mod_cast ((by positivity : 0 < δ * (U : ℝ) * (M : ℝ)).trans_le hLower))
  have hLogU : Real.log (U : ℝ) = (5 * ((J : ℝ) + (M : ℝ))) * Real.log 4 := by
    dsimp only [U]
    rw [Nat.cast_pow, Real.log_pow]
    push_cast
    ring
  have hLog : Real.log X ≤ L * (M : ℝ) := by
    have hJMr : (J : ℝ) ≤ (M : ℝ) := by exact_mod_cast hJM
    have hMr : 1 ≤ (M : ℝ) := by exact_mod_cast hM
    rw [show X = W * (U : ℝ)^3 by rfl, Real.log_mul hWpos.ne' (by positivity),
      Real.log_pow, hLogU]
    dsimp [L]
    nlinarith only [mul_le_mul_of_nonneg_right hJMr hLog4.le,
      mul_le_mul_of_nonneg_left hMr hLogW]
  have hRoot : X ^ (1 / 3 : ℝ) = W ^ (1/3 : ℝ) * (U : ℝ) := by
    dsimp [X]
    rw [Real.mul_rpow hWpos.le (by positivity)]
    congr 1
    simpa only [one_div, Nat.cast_ofNat] using
      (Real.pow_rpow_inv_natCast (x := (U : ℝ)) hUr.le (by decide : (3 : ℕ) ≠ 0))
  refine ⟨⟨X, hLarge, T, hNonempty, ?_, ?_, ?_, ?_⟩⟩
  · intro t ht
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ht
    have ho := (A i).ordered t hi
    have hsc : 1 ≤ (4 : ℕ)^(J+(i : ℕ)) := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
    have hUt : U ≤ t.1 := (Nat.le_mul_of_pos_right _ hsc).trans ho.1
    exact ⟨hNUₙ.trans_le hUt, ho.2.1, ho.2.2.1⟩
  · intro t ht v hv hne
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hv
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exact Or.inl (hCross hlt hi hj)
    · exact (A i).separated t hi v hj hne
    · exact Or.inr (hCross hgt hj hi)
  · intro t ht
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ht
    apply ((A i).small_lcm t hi).trans_lt
    apply mul_lt_mul_of_pos_right (by dsimp [W]; linarith) (by positivity)
  · rw [hRoot]
    apply le_trans (mul_le_mul_of_nonneg_left hLog (by positivity))
    calc
      c * (W ^ (1 / 3 : ℝ) * (U : ℝ)) * (L * (M : ℝ)) =
        δ * (U : ℝ) * (M : ℝ) := by
          dsimp [c]
          field_simp [(show (W ^ (1 / 3 : ℝ)) ≠ 0 by positivity), hL.ne']
      _ ≤ _ := hLower

end LCMMultiScale

namespace LCMScaleFamily

open LCMCandidates LCMGCDSum LCMTripleGluing LCMMultiScale

private def candidateTriple (x : Candidate) : Triple :=
  (x.2, x.2 + x.1.1, x.2 + x.1.1 + x.1.2)

private theorem candidateTriple_injective : Function.Injective candidateTriple := by
  rintro ⟨⟨p, q⟩, a⟩ ⟨⟨p', q'⟩, a'⟩ h
  simp only [candidateTriple, Prod.mk.injEq] at h
  obtain ⟨ha, hp, hq⟩ := h
  have hp' : p = p' := by omega
  have hq' : q = q' := by omega
  subst a'
  subst p'
  subst q'
  rfl

def of_packing {s U D : ℕ} {δ : ℝ} (hs : 1 ≤ s) (hU : 0 < U)
    (hGap : 2 * D ≤ U) {S : Finset Branch} {I : Finset Candidate}
    (hS : ∀ b ∈ S, s ≤ b.1 ∧ s ≤ b.2 ∧
      b.1 ≤ D*s ∧ b.2 ≤ D*s ∧ b.1.Coprime b.2)
    (hI : I ⊆ candidates S s U) (hCard : δ * (U : ℝ) ≤ (I.card : ℝ))
    (hSep : (I : Set Candidate).Pairwise
      (fun x y => ¬ (x.2 ≤ y.2 + 2*D*s ∧ y.2 ≤ x.2 + 2*D*s))) :
    ScaleFamily δ 27 U s := by
  let e : Candidate ↪ Triple := ⟨candidateTriple, candidateTriple_injective⟩
  have hStart (x : Candidate) (hx : x ∈ I) :
      (U*s ≤ x.2 ∧ x.2 ≤ 2*U*s) ∧
      (x.1.1*(x.1.1+x.1.2) ∣ x.2 ∧ x.1.2 ∣ x.2+x.1.1) ∧
      s ≤ x.1.1 ∧ s ≤ x.1.2 ∧ x.1.1 ≤ D*s ∧ x.1.2 ≤ D*s ∧ x.1.1.Coprime x.1.2 := by
    have hm := Finset.mem_sigma.mp (hI hx)
    exact ⟨(mem_starts.mp hm.2).1, (mem_starts.mp hm.2).2, hS _ hm.1⟩
  have hEnd (x : Candidate) (hx : x ∈ I) :
      x.2+x.1.1+x.1.2 ≤ 3*(U*s) := by
    obtain ⟨ha, _, _, _, hp, hq, _⟩ := hStart x hx
    have hmul := Nat.mul_le_mul_right s hGap
    calc
      _ ≤ 2*U*s + D*s + D*s := by omega
      _ = 2*(U*s) + (2*D)*s := by ring
      _ ≤ 3*(U*s) := by omega
  refine ⟨I.map e, ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ht
    obtain ⟨ha, _, hp, hq, _, _, _⟩ := hStart x hx
    exact ⟨ha.1, by change x.2 < x.2+x.1.1; omega,
      by change x.2+x.1.1 < x.2+x.1.1+x.1.2; omega, hEnd x hx⟩
  · intro t ht v hv hne
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ht
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hv
    have hxy : x ≠ y := fun h => hne (congrArg e h)
    have hx' := hStart x hx
    have hy' := hStart y hy
    have hdist := hSep hx hy hxy
    push Not at hdist
    change x.2+x.1.1+x.1.2 < y.2 ∨ y.2+y.1.1+y.1.2 < x.2
    have hw : (2*D)*s = D*s+D*s := by ring
    omega
  · intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ht
    obtain ⟨ha, hdiv, hp, hq, _, _, hco⟩ := hStart x hx
    have hpos : 0 < x.2 := (Nat.mul_pos hU hs).trans_le ha.1
    have hle := LCMTripleConstruction.lcm_bound_of_congruences hs hpos hp hq
      (show x.2+x.1.1+x.1.2 ≤ (3*U)*s by rw [Nat.mul_assoc]; exact hEnd x hx)
      hco hdiv.1 hdiv.2
    change (↑((Finset.range 3).lcm (LCMTripleConstruction.triple x.2 x.1.1 x.1.2)) : ℝ) ≤
      27*(U : ℝ)^3
    calc
      _ ≤ (((3*U)^3 : ℕ) : ℝ) := by exact_mod_cast hle
      _ = _ := by push_cast; ring
  · rw [Finset.card_map]
    exact hCard

open Filter LCMBranchDensity

theorem eventually_scaleFamily : ∃ δ > (0 : ℝ), ∀ᶠ s : ℕ in atTop,
    ∀ U : ℕ, s^5 ≤ U → Nonempty (ScaleFamily δ 27 U s) := by
  classical
  let D := branchConstant
  have hD : 1 ≤ D := by norm_num [D, branchConstant, cutoff]
  let ε : ℝ := 1 / (80000 * (D : ℝ)^3)
  have hDr : 0 < (D : ℝ) := by exact_mod_cast (show 0 < D from hD)
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨C, hC, hConf⟩ := candidates_conflicts_bound D
  obtain ⟨δ, hδ, pack⟩ := ConflictPacking.exists_independent (V := Candidate) ε C hε hC
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [branch_density, LCMGCDMatrix.scale_large D,
    eventually_ge_atTop (max (max 1 (2*D)) (8*D^3))] with s hDen hLarge hs
  intro U hU
  have hs₁ : 1 ≤ s := (le_max_left 1 (2*D)).trans ((le_max_left _ _).trans hs)
  have hgap₀ : 2*D ≤ s := (le_max_right 1 (2*D)).trans ((le_max_left _ _).trans hs)
  have hscale₀ : 8*D^3 ≤ s := (le_max_right _ _).trans hs
  have hscale : 8*D^3*s^2 ≤ U := by
    calc
      _ ≤ s^3*s^2 :=
        Nat.mul_le_mul_right _ (hscale₀.trans (le_self_pow₀ hs₁ (by norm_num)))
      _ = s^5 := by rw [← pow_add]
      _ ≤ U := hU
  have hsU : s ≤ U := (le_self_pow₀ hs₁ (by norm_num)).trans hU
  have hUpos : 0 < U := hs₁.trans hsU
  obtain ⟨S, hCard, hS⟩ := hDen
  have hadm (b : Branch) (hb : b ∈ S) :
      s ≤ b.1 ∧ s ≤ b.2 ∧ b.1 ≤ D*s ∧ b.2 ≤ D*s ∧ b.1.Coprime b.2 := by
    obtain ⟨h₁, h₂, h₃, h₄, h₅, _⟩ := hS b hb
    exact ⟨h₁, h₂, h₃, h₄, h₅⟩
  have hLower : ε * (U : ℝ) ≤ ((candidates S s U).card : ℝ) := by
    have h := candidates_card_lower hs₁ hD hscale hadm hCard
    simpa only [ε, div_eq_mul_inv, one_mul, mul_comm _ (U : ℝ)] using h
  have hUpper := hConf (S := S) hs₁ hU hLarge hS
  obtain ⟨I, hI, hISep, hISize⟩ := pack (candidates S s U)
    (conflict s D) (fun _ _ h => conflict_symm h) (by positivity) hLower hUpper
  exact ⟨of_packing hs₁ hUpos (hgap₀.trans hsU) hadm hI hISize hISep⟩

end LCMScaleFamily

theorem OMA.solution : type_of% @Erdos873.erdos_873.variants.triple_lower_bound_infinitely_often := by
  obtain ⟨δ, hδ, hScale⟩ := LCMScaleFamily.eventually_scaleFamily
  obtain ⟨s₀, hsc⟩ := Filter.eventually_atTop.mp hScale
  obtain ⟨c, hc, hBlock⟩ := LCMMultiScale.assemble_scales hδ (by norm_num : 0 ≤ (27 : ℝ)) hsc
  exact LCMTripleGluing.assemble hc (fun N => (hBlock N).some)