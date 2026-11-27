import OMAReductions.R_Erdos700_erdos_700_parts_ii_R1
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Combinatorics.Pigeonhole

namespace PrimeTriple
open Finset

lemma local_bin (k lo : ℕ) (hk : 0 < k) (S : Finset ℕ)
    (hS : ∀ x ∈ S, lo ≤ x ∧ x < lo+k^2) (hc : 2*k+1 < S.card) :
    ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S, p < q ∧ q < r ∧ q-p < r-q ∧ r-p < k^2 := by
  let r := S.max' (Finset.card_pos.mp (by omega))
  have hr : r ∈ S := Finset.max'_mem _ _
  let T := S \ Icc (r-k) r
  have hcard := card_le_card_sdiff_add_card (s := S) (t := Icc (r-k) r)
  rw [Nat.card_Icc] at hcard
  have ht : (range k).card < T.card := by dsimp [T]; simp only [card_range]; omega
  let f (n : ℕ) := (n-lo)/k
  have hf : Set.MapsTo f T (range k) := by
    intro x hx
    apply mem_range.mpr
    have h := hS x (mem_sdiff.mp hx).1
    apply (Nat.div_lt_iff_lt_mul hk).2
    rw [←sq]
    omega
  obtain ⟨x,hx,y,hy,hne,heq⟩ := exists_ne_map_eq_of_card_lt_of_maps_to ht hf
  have finish (p q : ℕ) (hp : p ∈ T) (hq : q ∈ T) (hpq : p < q) (he : f p = f q) :
      ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S, p < q ∧ q < r ∧ q-p < r-q ∧ r-p < k^2 := by
    obtain ⟨hps,-⟩ := mem_sdiff.mp hp
    obtain ⟨hqs,hnot⟩ := mem_sdiff.mp hq
    have hqr : q ≤ r := le_max' _ _ hqs
    have hqlo : q+k < r := by simpa [mem_Icc,hqr] using hnot
    have h1 := hS p hps
    have h2 := hS q hqs
    have h3 := hS r hr
    have hrem := Nat.mod_lt (q-lo) hk
    have hpdiv := Nat.div_add_mod (p-lo) k
    have hqdiv := Nat.div_add_mod (q-lo) k
    change (p-lo)/k=(q-lo)/k at he
    rw [he] at hpdiv
    refine ⟨p,hps,q,hqs,r,hr,hpq,by omega,by omega,by omega⟩
  rcases lt_or_gt_of_ne hne with h | h
  · exact finish x y hx hy h heq
  · exact finish y x hy hx h heq.symm

-- Chebyshev estimate from the checked proof of Erdos888.erdos_888.variants.primes.
/-- Chebyshev's lower bound in the form `n / log n ≤ 4 * π n` for `n ≥ 100`. -/
lemma chebyshev (n : ℕ) (hn : 100 ≤ n) :
    (n : ℝ) / Real.log n ≤ 4 * (Nat.primeCounting n : ℝ) := by
  have hn' : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogpos : 0 < Real.log n := Real.log_pos (by linarith)
  have hpi := Chebyshev.pi_ge n
  have hlog1 : Real.log ((n : ℝ) + 1) ≤ n / 4 := by
    have hs : Real.log (Real.sqrt ((n : ℝ) + 1)) ≤ Real.sqrt ((n : ℝ) + 1) - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (by positivity))
    have h2 : Real.log ((n : ℝ) + 1) = 2 * Real.log (Real.sqrt ((n : ℝ) + 1)) := by
      rw [Real.log_sqrt (by positivity)]
      ring
    have h3 : Real.sqrt ((n : ℝ) + 1) ≤ n / 8 := by
      rw [show (n : ℝ) / 8 = Real.sqrt (((n : ℝ) / 8) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      apply Real.sqrt_le_sqrt
      nlinarith
    linarith
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h4 : (n : ℝ) / 4 ≤ n * Real.log 2 - Real.log (n + 1) := by
    have := mul_le_mul_of_nonneg_left hlog2.le (show (0 : ℝ) ≤ n by positivity)
    linarith
  have h5 : (n : ℝ) / 4 / Real.log n ≤ (n * Real.log 2 - Real.log (n + 1)) / Real.log n :=
    div_le_div_of_nonneg_right h4 hlogpos.le
  have h6 : (n : ℝ) / Real.log n = 4 * ((n : ℝ) / 4 / Real.log n) := by
    field_simp
  linarith

lemma many (N : ℕ) : ∃ k, N < k ∧ 2 ≤ k ∧ 10*k^7 < (k^8).primeCounting := by
  let s := N+1000
  let k := s^2
  have hs : 1000 ≤ s := by dsimp [s]; omega
  have hk : 100 ≤ k := by dsimp [k]; nlinarith
  have hN : N < k := by dsimp [k,s]; nlinarith
  have hk8 : 100 ≤ k^8 := hk.trans (Nat.le_self_pow (by decide) _)
  have hb := chebyshev (k^8) hk8
  push_cast at hb
  have hsR : (1000 : ℝ) ≤ s := by exact_mod_cast hs
  have hkR : (100 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog : 0 < Real.log ((k : ℝ)^8) := Real.log_pos (one_lt_pow₀ (by linarith only [hkR]) (by decide))
  have he : (k : ℝ) = (s : ℝ)^2 := by simp [k]
  have hsmall : 40 * Real.log ((k : ℝ)^8) < k := by
    rw [he,Real.log_pow,Real.log_pow]
    have hl := Real.log_le_sub_one_of_pos (by linarith only [hsR] : 0 < (s:ℝ))
    norm_num
    nlinarith only [hl,hsR,mul_nonneg (by linarith only [hsR] : (0:ℝ) ≤ s - 1000) (by positivity : (0:ℝ) ≤ s)]
  refine ⟨k,hN,by omega,?_⟩
  have hh : 10*(k:ℝ)^7 < ((k^8).primeCounting : ℝ) := by
    have hb' := (div_le_iff₀ hlog).1 hb
    by_contra! hc
    have hupper := mul_le_mul_of_nonneg_right hc hlog.le
    have hlow := mul_lt_mul_of_pos_right hsmall (by positivity : 0 < (k:ℝ)^7)
    nlinarith only [hb',hupper,hlow]
  exact_mod_cast hh

lemma triples (N : ℕ) : ∃ p q r : ℕ, N < p ∧ p.Prime ∧ q.Prime ∧ r.Prime ∧ p < q ∧ q < r ∧
    q-p < r-q ∧ 2*(r-p)^2 < p := by
  obtain ⟨k,hN,hk,hpi⟩ := many N
  let P := (range (k^8+1)).filter Nat.Prime
  have hcard : P.card = (k^8).primeCounting := by
    rw [Nat.primeCounting,Nat.primeCounting',Nat.count_eq_card_filter_range]
  let U := P \ range (3*k^4+1)
  have hs := card_le_card_sdiff_add_card (s := P) (t := range (3*k^4+1))
  rw [card_range,hcard] at hs
  have hu : (range (k^6+1)).card*(2*k+1) < U.card := by
    rw [card_range]
    change (k^6+1)*(2*k+1) < (P \ range (3*k^4+1)).card
    have h46 : k^4 ≤ k^6 := Nat.pow_le_pow_right (by omega) (by decide)
    have h67 : k^6 ≤ k^7 := Nat.pow_le_pow_right (by omega) (by decide)
    have h17 : k ≤ k^7 := Nat.le_self_pow (by decide) _
    nlinarith
  have hmem {x : ℕ} (hx : x ∈ U) : x.Prime ∧ 3*k^4 < x ∧ x ≤ k^8 := by
    obtain ⟨h1,h2⟩ := mem_sdiff.mp hx
    obtain ⟨h3,h4⟩ := mem_filter.mp h1
    simp only [mem_range] at h2 h3
    exact ⟨h4,by omega,by omega⟩
  have hmaps (x : ℕ) (hx : x ∈ U) : x/k^2 ∈ range (k^6+1) := by
    apply mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul (by positivity)).2
    have := (hmem hx).2.2
    nlinarith [show 0 < k^2 by positivity]
  obtain ⟨b,-,hb⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hu
  let S := U.filter (fun x => x/k^2 = b)
  have bin (x : ℕ) (hx : x ∈ S) : b*k^2 ≤ x ∧ x < b*k^2+k^2 := by
    have he : x/k^2=b := (mem_filter.mp hx).2
    constructor
    · rw [←he]; exact Nat.div_mul_le_self _ _
    · rw [←Nat.add_one_mul]
      apply (Nat.div_lt_iff_lt_mul (by positivity)).mp
      omega
  obtain ⟨p,hp,q,hq,r,hr,hpq,hqr,hgap,hsep⟩ := local_bin k _ (by omega) S bin hb
  have ap := hmem (mem_filter.mp hp).1
  have aq := hmem (mem_filter.mp hq).1
  have ar := hmem (mem_filter.mp hr).1
  have hpow := Nat.pow_le_pow_left hsep.le 2
  have hkle : k ≤ k^4 := Nat.le_self_pow (by decide) _
  exact ⟨p,q,r,by omega,ap.1,aq.1,ar.1,hpq,hqr,hgap,by nlinarith [ap.2.1]⟩
end PrimeTriple

theorem OMA.solution : OMA.R_Erdos700_erdos_700_parts_ii_R1.H2 := PrimeTriple.triples
