import FormalConjectures.ErdosProblems.«269»
import Mathlib.Analysis.PSeries

/-!
# Irrationality for infinite sets of primes

Normalize the tail by the least common multiple just before a new prime
enters. If the prime reciprocals are summable, the supported integers
have density zero. Otherwise arbitrarily close new primes cause two
consecutive large increases in the denominator. Either way, the
normalized tails become arbitrarily small along suitable cuts.
-/

-- Credit: @ysanatomic

open Filter
open scoped Topology Classical BigOperators

private theorem prime_power_smooth {P : Set ℕ} {p : ℕ} (hp : p.Prime) (hpP : p ∈ P) (k : ℕ) :
    Erdos269.HasPrimeFactorsIn P (p^k) := by
  refine ⟨pow_pos hp.pos _, fun q hq hd ↦ ?_⟩
  have he : q = p := (Nat.dvd_prime hp).mp (hq.dvd_of_dvd_pow hd) |>.resolve_left hq.ne_one
  rwa [he]

private theorem prime_smooth {P : Set ℕ} {p : ℕ} (hp : p.Prime) (hpP : p ∈ P) :
    Erdos269.HasPrimeFactorsIn P p := by simpa using prime_power_smooth hp hpP 1

private theorem smooth_range {P : Set ℕ} {p : ℕ} (hp : p.Prime) (hpP : p ∈ P) :
    StrictMono (Erdos269.a P) ∧ ∀ n, Erdos269.HasPrimeFactorsIn P (Erdos269.a P n) := by
  have hinf : (Set.ofPred (Erdos269.HasPrimeFactorsIn P)).Infinite := by
    refine (Set.infinite_range_of_injective ?_ : (Set.range (fun k : ℕ ↦ p^k)).Infinite).mono ?_
    · exact (pow_right_strictMono₀ hp.one_lt).injective
    · rintro _ ⟨k, rfl⟩
      exact prime_power_smooth hp hpP k
  exact ⟨Nat.nth_strictMono hinf, Nat.nth_mem_of_infinite hinf⟩

private theorem close_primes_of_not_summable {P : Set ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (hinf : P.Infinite)
    (hns : ¬ Summable (fun p : ℕ ↦ if p ∈ P then 1/(p:ℝ) else 0))
    (δ : ℝ) (hδ : 0 < δ) (M : ℕ) :
    ∃ p ∈ P, ∃ q ∈ P, M ≤ p ∧ p < q ∧ (q:ℝ) < (1+δ)*(p:ℝ) := by
  by_contra! H
  let : Infinite P := hinf.to_subtype
  let e : ℕ ≃o P := Nat.Subtype.orderIsoOfNat P
  let f (n : ℕ) : ℕ := (e n).val
  have hf : StrictMono f := (Subtype.strictMono_coe _).comp e.strictMono
  have hmem (n : ℕ) : f n ∈ P := (e n).property
  have hstart : M ≤ f M := by
    have h := hf.add_le_nat M 0
    simpa only [add_zero] using (Nat.le_add_right M (f 0)).trans h
  have hpow (k : ℕ) : (f M : ℝ) * (1+δ)^k ≤ (f (k+M) : ℝ) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hstep := H (f (k+M)) (hmem _) (f (k+1+M)) (hmem _)
        (hstart.trans (hf.monotone (by omega))) (hf (by omega))
      calc
        _ = (1+δ)*((f M : ℝ)*(1+δ)^k) := by rw [pow_succ]; ring
        _ ≤ (1+δ)*(f (k+M):ℝ) := mul_le_mul_of_nonneg_left ih (by positivity)
        _ ≤ _ := hstep
  have hbase : 0 < (f M : ℝ) := by exact_mod_cast (hP _ (hmem M)).pos
  have ha : 0 < 1+δ := by positivity
  have hr : (1+δ)⁻¹ < 1 := by
    rw [inv_lt_one₀ ha]
    linarith
  have hmajor : Summable (fun k : ℕ ↦ (1/(f M:ℝ)) * ((1+δ)⁻¹)^k) :=
    (summable_geometric_of_lt_one (by positivity) hr).mul_left _
  have hs : Summable (fun k : ℕ ↦ 1/(f (k+M):ℝ)) := by
    refine hmajor.of_nonneg_of_le (fun _ ↦ by positivity) (fun k ↦ ?_)
    rw [inv_pow, ← one_div, one_div_mul_one_div]
    exact one_div_le_one_div_of_le (by positivity : 0 < (f M:ℝ)*(1+δ)^k) (hpow k)
  have hs' : Summable (fun k : ℕ ↦ 1/(f k:ℝ)) := (summable_nat_add_iff M).mp hs
  have hsub : Summable (fun p : P ↦ 1/(p.val:ℝ)) := e.toEquiv.summable_iff.mp hs'
  apply hns
  refine ((summable_subtype_iff_indicator (s := P) (f := fun p : ℕ ↦ 1/(p:ℝ))).mp hsub).congr ?_
  intro n
  by_cases hn : n ∈ P <;> simp [Set.indicator, hn]

private theorem inverse_square_tail {a : ℕ → ℕ} (ha : StrictMono a) (m : ℕ)
    (hm : 2 ≤ a m) :
    Summable (fun k : ℕ ↦ 1/((a (m+k):ℝ)^2)) ∧
      (∑' k : ℕ, 1/((a (m+k):ℝ)^2)) ≤ 1/((a m:ℝ)-1) := by
  let x : ℝ := a m
  have hx : (2:ℝ) ≤ x := by
    change (2 : ℝ) ≤ (a m : ℝ)
    exact_mod_cast hm
  have hp (i : ℕ) : 0 < x + i - 1 := by linarith [Nat.cast_nonneg (α := ℝ) i]
  have hsum (K : ℕ) : (∑ k ∈ Finset.range K, 1/((a (m+k):ℝ)^2)) ≤
      1/(x-1) - 1/(x+K-1) := by
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ]
      have hle : x + (K:ℝ) ≤ (a (m+K) : ℝ) := by
        change (a m : ℝ) + (K : ℝ) ≤ (a (m + K) : ℝ)
        exact_mod_cast (show a m + K ≤ a (m + K) by simpa only [add_comm] using ha.add_le_nat K m)
      have hxK : 0 < x + (K:ℝ) := by positivity
      have hterm : 1/((a (m+K):ℝ)^2) ≤ 1/(x+(K:ℝ)-1) - 1/(x+(K:ℝ)) := by
        calc
          _ ≤ 1/(x+(K:ℝ))^2 :=
            one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hxK.le hle 2)
          _ ≤ 1/((x+(K:ℝ)-1)*(x+(K:ℝ))) :=
            one_div_le_one_div_of_le (mul_pos (hp K) hxK) (by nlinarith)
          _ = _ := by field_simp [ne_of_gt (hp K), ne_of_gt hxK]; ring
      calc
        _ ≤ (1/(x-1) - 1/(x+K-1)) + (1/(x+K-1) - 1/(x+K)) := add_le_add ih hterm
        _ = _ := by
          rw [Nat.cast_succ, show x + ((K : ℝ) + 1) - 1 = x + K by ring]
          ring
  have hbound (K : ℕ) : (∑ k ∈ Finset.range K, 1/((a (m+k):ℝ)^2)) ≤ 1/(x-1) :=
    (hsum K).trans (sub_le_self _ (one_div_nonneg.mpr (hp K).le))
  exact ⟨summable_of_sum_range_le (fun _ ↦ by positivity) hbound,
    Real.tsum_le_of_sum_range_le (fun _ ↦ by positivity) hbound⟩

private theorem series_summable_of_cut {D a : ℕ → ℕ}
    (hD : ∀ i, 0 < D i) (ha : StrictMono a) (m : ℕ) (hm : 2 ≤ a m) (C : ℝ)
    (hbound : ∀ j ≥ m, (D m : ℝ) / (D (j+1):ℝ) ≤ C * (1/((a j:ℝ)^2))) :
    Summable (fun i : ℕ ↦ 1/(D i:ℝ)) := by
  have hmajor := (inverse_square_tail ha m hm).1.mul_left C
  have hs : Summable (fun k : ℕ ↦ (D m:ℝ) / (D (m+k+1):ℝ)) :=
    hmajor.of_nonneg_of_le (fun _ ↦ by positivity) (fun k ↦ hbound (m+k) (Nat.le_add_right _ _))
  apply (summable_nat_add_iff (m+1)).mp
  refine (hs.div_const (D m:ℝ)).congr (fun k ↦ ?_)
  rw [show m+k+1 = k+(m+1) by omega]
  have hp : 0 < (D m : ℝ) := by exact_mod_cast hD m
  field_simp [hp.ne']

private theorem normalized_tail_bound {D a : ℕ → ℕ}
    (hs : Summable (fun i : ℕ ↦ 1/(D i:ℝ))) (ha : StrictMono a)
    {m l : ℕ} (hlm : m ≤ l) (hl : 2 ≤ a l) (A C : ℝ) (hC : 0 ≤ C)
    (hbefore : ∀ j, m ≤ j → j < l → (D m:ℝ) / (D (j+1):ℝ) ≤ A)
    (hafter : ∀ j ≥ l, (D m:ℝ) / (D (j+1):ℝ) ≤ C * (1/((a j:ℝ)^2))) :
    (∑' k : ℕ, (D m:ℝ) / (D (m+k+1):ℝ)) ≤ (l-m : ℕ) * A + C * (1/((a l:ℝ)-1)) := by
  let g (k : ℕ) : ℝ := (D m : ℝ) / (D (m+k+1):ℝ)
  have hg : Summable g := by
    refine (((summable_nat_add_iff (m+1)).mpr hs).mul_left (D m:ℝ)).congr (fun k ↦ ?_)
    rw [show k+(m+1) = m+k+1 by omega]
    simp only [g, mul_one_div]
  rw [← hg.sum_add_tsum_nat_add (l-m)]
  apply add_le_add
  · calc
      _ ≤ ∑ _k ∈ Finset.range (l-m), A := by
        refine Finset.sum_le_sum (fun k hk ↦ ?_)
        have hkl := Finset.mem_range.mp hk
        exact hbefore (m+k) (by omega) (by omega)
      _ = _ := by simp
  · obtain ⟨hmjr, hmjrb⟩ := inverse_square_tail ha l hl
    calc
      _ ≤ ∑' k : ℕ, C * (1/((a (l+k):ℝ)^2)) := by
        apply ((summable_nat_add_iff (l-m)).mpr hg).tsum_le_tsum _ (hmjr.mul_left C)
        intro k
        dsimp only [g]
        rw [show m+(k+(l-m)) = l+k by omega]
        exact hafter (l+k) (by omega)
      _ = C * (∑' k : ℕ, 1/((a (l+k):ℝ)^2)) := tsum_mul_left
      _ ≤ _ := mul_le_mul_of_nonneg_left hmjrb hC

private theorem large_prime_in_set {P : Set ℕ} (hP : P.Infinite) (M : ℕ) :
    ∃ p ∈ P, M < p := by
  by_contra! h
  exact hP ((Set.finite_Iic M).subset h)

private theorem partial_lcm_pos {P : Set ℕ} (ha : ∀ n, 0 < Erdos269.a P n) (n : ℕ) :
    0 < Erdos269.partialLcm P n := by
  exact Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.2 (fun i _ ↦ (ha i).ne'))

private theorem partial_lcm_dvd (P : Set ℕ) (i j : ℕ) (hij : i ≤ j) :
    Erdos269.partialLcm P i ∣ Erdos269.partialLcm P j := by
  exact Finset.lcm_dvd (fun k hk ↦ Finset.dvd_lcm (Finset.range_mono hij hk))

namespace OMA

private lemma erdos269_factorization_lcm_le {f : ℕ → ℕ} {u e : ℕ} (S : Finset ℕ)
    (hpos : ∀ i ∈ S, f i ≠ 0) (h : ∀ i ∈ S, (f i).factorization u ≤ e) :
    (S.lcm f).factorization u ≤ e := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hs := Finset.lcm_ne_zero_iff.mpr (fun j hj ↦ hpos j (Finset.mem_insert_of_mem hj))
    rw [Finset.lcm_insert]
    change (Nat.lcm (f i) (S.lcm f)).factorization u ≤ e
    rw [Nat.factorization_lcm (hpos i (Finset.mem_insert_self i S)) hs]
    exact max_le (h i (Finset.mem_insert_self i S))
      (ih (fun j hj ↦ hpos j (Finset.mem_insert_of_mem hj))
        (fun j hj ↦ h j (Finset.mem_insert_of_mem hj)))

/-- The least common multiple beyond the cut includes extra powers of two fixed primes,
the prime at the cut, and every larger prime already reached. -/
lemma erdos269_cut_ratios {P : Set ℕ} (ha : StrictMono (Erdos269.a P))
    (hpos : ∀ n, 0 < Erdos269.a P n)
    (hcover : ∀ n, Erdos269.HasPrimeFactorsIn P n → ∃ i, Erdos269.a P i = n)
    {r s p m j : ℕ} (hr : r.Prime) (hs : s.Prime) (hp : p.Prime)
    (hrP : r ∈ P) (hsP : s ∈ P) (hrs : r ≠ s) (hrp : r < p) (hsp : s < p)
    (hm : Erdos269.a P m = p) (hmj : m ≤ j) :
    (Erdos269.partialLcm P m : ℝ) / (Erdos269.partialLcm P (j + 1) : ℝ) ≤
        (r * s * p : ℝ) / (Erdos269.a P j : ℝ)^2 ∧
    (Erdos269.partialLcm P m : ℝ) / (Erdos269.partialLcm P (j + 1) : ℝ) ≤
        1 / (p : ℝ) ∧
    ∀ q : ℕ, q.Prime → q ∈ P → p < q → q ≤ Erdos269.a P j →
      (Erdos269.partialLcm P m : ℝ) / (Erdos269.partialLcm P (j + 1) : ℝ) ≤
        (r * s * p : ℝ) / ((q : ℝ) * (Erdos269.a P j : ℝ)^2) := by
  let D := Erdos269.partialLcm P m
  let T := Erdos269.partialLcm P (j + 1)
  let x := Erdos269.a P j
  have hD : 0 < D := Nat.pos_of_ne_zero
    (Finset.lcm_ne_zero_iff.mpr fun i _ ↦ (hpos i).ne')
  have hT : 0 < T := Nat.pos_of_ne_zero
    (Finset.lcm_ne_zero_iff.mpr fun i _ ↦ (hpos i).ne')
  have hx : 0 < x := hpos j
  have hDT : D ∣ T :=
    Finset.lcm_dvd fun i hi ↦ Finset.dvd_lcm (Finset.mem_range.mpr (by
      have := Finset.mem_range.mp hi
      omega) : i ∈ Finset.range (j + 1))
  obtain ⟨U, hU⟩ := hDT
  have hu : 0 < U := by
    have hmul : 0 < D * U := hU ▸ hT
    exact Nat.pos_of_ne_zero fun hu ↦ by simp [hu] at hmul
  have hbase (v : ℕ) (hv : v.Prime) : v ^ D.factorization v ≤ p - 1 := by
    have hall (i : ℕ) (hi : i ∈ Finset.range m) : (Erdos269.a P i).factorization v ≤
        Nat.log v (p - 1) := by
      apply Nat.le_log_of_pow_le hv.one_lt
      have hai : Erdos269.a P i < p := hm ▸ ha (Finset.mem_range.mp hi)
      exact (Nat.le_of_dvd (hpos i) (Nat.ordProj_dvd _ _)).trans (by omega)
    have hvD : D.factorization v ≤ Nat.log v (p - 1) :=
      erdos269_factorization_lcm_le (Finset.range m) (fun i _ ↦ (hpos i).ne') hall
    exact (Nat.pow_le_pow_right hv.pos hvD).trans (Nat.pow_log_le_self v (by
      have := hp.two_le
      omega))
  have hlarge_not_dvd (v : ℕ) (hv : v.Prime) (hpv : p ≤ v) : ¬ v ∣ D := by
    intro hvD
    have hval := (hv.dvd_iff_one_le_factorization hD.ne').mp hvD
    have hle := (Nat.pow_le_pow_right hv.pos hval).trans (hbase v hv)
    rw [pow_one] at hle
    have := hp.two_le
    omega
  have hsmall_dvd (i : ℕ) (hi : i ≤ j) : Erdos269.a P i ∣ T :=
    Finset.dvd_lcm (Finset.mem_range.mpr (by omega) : i ∈ Finset.range (j + 1))
  have hpow_dvd (v : ℕ) (hv : v.Prime) (hvP : v ∈ P) (e : ℕ) (hle : v ^ e ≤ x) :
      v ^ e ∣ T := by
    have hsm : Erdos269.HasPrimeFactorsIn P (v ^ e) := by
      refine ⟨pow_pos hv.pos _, ?_⟩
      intro w hw hdvd
      have h := (Nat.prime_dvd_prime_iff_eq hw hv).mp (hw.dvd_of_dvd_pow hdvd)
      simpa [h] using hvP
    obtain ⟨i, hi⟩ := hcover _ hsm
    rw [← hi] at hle ⊢
    exact hsmall_dvd i (ha.le_iff_le.mp hle)
  have hpU : p ∣ U := by
    have hpT : p ∣ T := hm ▸ hsmall_dvd m hmj
    rw [hU] at hpT
    exact (hp.dvd_mul.mp hpT).resolve_left (hlarge_not_dvd p hp le_rfl)
  have hqU (q : ℕ) (hq : q.Prime) (hqP : q ∈ P) (hpq : p < q) (hqx : q ≤ x) :
      q ∣ U := by
    have hqT : q ∣ T := by simpa only [pow_one] using hpow_dvd q hq hqP 1 (by simpa using hqx)
    rw [hU] at hqT
    exact (hq.dvd_mul.mp hqT).resolve_left (hlarge_not_dvd q hq hpq.le)
  have hgrowth (v : ℕ) (hv : v.Prime) (hvP : v ∈ P) : x ≤ v * p * v ^ U.factorization v := by
    have hlog := (hv.pow_dvd_iff_le_factorization hT.ne').mp
      (hpow_dvd v hv hvP (Nat.log v x) (Nat.pow_log_le_self v hx.ne'))
    rw [hU, Nat.factorization_mul hD.ne' hu.ne', Finsupp.add_apply] at hlog
    have hlt := Nat.lt_pow_succ_log_self hv.one_lt x
    rw [pow_succ'] at hlt
    calc
      x ≤ v * v ^ Nat.log v x := hlt.le
      _ ≤ v * v ^ (D.factorization v + U.factorization v) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hv.pos hlog)
      _ = v * v ^ D.factorization v * v ^ U.factorization v := by rw [pow_add, mul_assoc]
      _ ≤ v * p * v ^ U.factorization v :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ((hbase v hv).trans (Nat.sub_le _ _)))
  let R := r ^ U.factorization r
  let S := s ^ U.factorization s
  have hRSU : R * S ∣ U :=
    (Nat.coprime_pow_primes _ _ hr hs hrs).mul_dvd_of_dvd_of_dvd
      (Nat.ordProj_dvd _ _) (Nat.ordProj_dvd _ _)
  have hfresh (v : ℕ) (hv : v.Prime) (hrv : r ≠ v) (hsv : s ≠ v) :
      Nat.Coprime (R * S) v := by
    apply Nat.coprime_mul_iff_left.mpr
    exact ⟨((Nat.coprime_primes hr hv).mpr hrv).pow_left _,
      ((Nat.coprime_primes hs hv).mpr hsv).pow_left _⟩
  have hRSp : R * S * p ∣ U :=
    (hfresh p hp hrp.ne hsp.ne).mul_dvd_of_dvd_of_dvd hRSU hpU
  have heq : (D : ℝ) / (T : ℝ) = 1 / (U : ℝ) := by
    have hcast : (T : ℝ) = (D : ℝ) * (U : ℝ) := by exact_mod_cast hU
    rw [hcast, div_mul_eq_div_div, div_self (by exact_mod_cast hD.ne')]
  have hratio (K : ℕ) (hK : 0 < K) (hdiv : R * S * K ∣ U) :
      (D : ℝ) / (T : ℝ) ≤ ((r : ℝ) * s * (p : ℝ)^2) / ((K : ℝ) * (x : ℝ)^2) := by
    have h₁ : (x : ℝ) ≤ (r : ℝ) * p * R := by exact_mod_cast hgrowth r hr hrP
    have h₂ : (x : ℝ) ≤ (s : ℝ) * p * S := by exact_mod_cast hgrowth s hs hsP
    have h₃ : (R : ℝ) * S * K ≤ (U : ℝ) := by exact_mod_cast Nat.le_of_dvd hu hdiv
    have huR : (0 : ℝ) < U := by exact_mod_cast hu
    have hxR : (0 : ℝ) < x := by exact_mod_cast hx
    have hKR : (0 : ℝ) < K := by exact_mod_cast hK
    rw [heq, div_le_div_iff₀ huR (by positivity)]
    calc
      1 * ((K : ℝ) * (x : ℝ)^2) = (K : ℝ) * ((x : ℝ) * x) := by ring
      _ ≤ (K : ℝ) * (((r : ℝ) * p * R) * ((s : ℝ) * p * S)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h₁ h₂ hxR.le (by positivity)) hKR.le
      _ = ((r : ℝ) * s * (p : ℝ)^2) * ((R : ℝ) * S * K) := by ring
      _ ≤ ((r : ℝ) * s * (p : ℝ)^2) * U := mul_le_mul_of_nonneg_left h₃ (by positivity)
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hxR : (x : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
  refine ⟨?_, ?_, ?_⟩
  · calc
      (D : ℝ) / (T : ℝ) ≤ _ := hratio p hp.pos hRSp
      _ = (r * s * p : ℝ) / (x : ℝ)^2 := by field_simp
  · rw [heq]
    exact one_div_le_one_div_of_le (by exact_mod_cast hp.pos) (by
      exact_mod_cast Nat.le_of_dvd hu hpU)
  · intro q hq hqP hpq hqx
    have hcop : Nat.Coprime (R * S * p) q := Nat.coprime_mul_iff_left.mpr
      ⟨hfresh q hq (hrp.trans hpq).ne (hsp.trans hpq).ne,
        (Nat.coprime_primes hp hq).mpr hpq.ne⟩
    have hdiv : R * S * (p * q) ∣ U := by
      rw [← mul_assoc]
      exact hcop.mul_dvd_of_dvd_of_dvd hRSp (hqU q hq hqP hpq hqx)
    calc
      (D : ℝ) / (T : ℝ) ≤ _ := hratio (p * q) (Nat.mul_pos hp.pos hq.pos) hdiv
      _ = (r * s * p : ℝ) / ((q : ℝ) * (x : ℝ)^2) := by
        push_cast
        field_simp

end OMA

namespace OMA.Erdos269

open Filter Set
open scoped Topology BigOperators Classical

lemma smooth_count_of_summable (P : Set ℕ) (_hP : ∀ p ∈ P, p.Prime)
    (hs : Summable (fun n : ℕ => if n ∈ P then 1 / (n : ℝ) else 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (((Finset.Icc 1 N).filter (_root_.Erdos269.HasPrimeFactorsIn P)).card : ℝ)
        ≤ ε * (N : ℝ) := by
  classical
  intro ε hε
  obtain ⟨K, hK⟩ := hs.nat_tsum_vanishing
    (Iio_mem_nhds (half_pos hε) : Iio (ε / 2) ∈ 𝓝 (0 : ℝ))
  let tail (N : ℕ) := (Finset.Icc K N).filter (· ∈ P)
  let multiples (N p : ℕ) := (Finset.Icc 1 N).filter (p ∣ ·)
  have hTail (N : ℕ) : ∑ p ∈ tail N, 1 / (p : ℝ) ≤ ε / 2 := by
    have ht := hK (↑(tail N) : Set ℕ) (fun p hp => (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1)
    rw [mem_Iio, tsum_fintype] at ht
    rw [Finset.sum_finset_coe (fun p : ℕ => if p ∈ P then 1 / (p : ℝ) else 0) (tail N)] at ht
    refine le_of_lt (lt_of_le_of_lt (le_of_eq ?_) ht)
    apply Finset.sum_congr rfl
    intro p hp
    exact (if_pos (Finset.mem_filter.mp hp).2).symm
  have hCover (N : ℕ) : (Finset.Icc 1 N).filter (_root_.Erdos269.HasPrimeFactorsIn P) ⊆
      Nat.smoothNumbersUpTo N K ∪ (tail N).biUnion (multiples N) := by
    intro n hn
    obtain ⟨hnIcc, hnP⟩ := Finset.mem_filter.mp hn
    by_cases hSmooth : n ∈ Nat.smoothNumbers K
    · exact Finset.mem_union.mpr (Or.inl (Nat.mem_smoothNumbersUpTo.mpr
        ⟨(Finset.mem_Icc.mp hnIcc).2, hSmooth⟩))
    · have hBad : ∃ p, K ≤ p ∧ p.Prime ∧ p ∣ n := by
        by_contra! h
        apply hSmooth
        exact Nat.mem_smoothNumbers_iff_forall_le.mpr ⟨ne_of_gt hnP.1,
          fun p _ hp hpn => lt_of_not_ge (fun hkp => h p hkp hp hpn)⟩
      obtain ⟨p, hpK, hp, hpn⟩ := hBad
      have hpN : p ≤ N := (Nat.le_of_dvd hnP.1 hpn).trans (Finset.mem_Icc.mp hnIcc).2
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
        ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpK, hpN⟩, hnP.2 p hp hpn⟩,
          Finset.mem_filter.mpr ⟨hnIcc, hpn⟩⟩))
  have hMultiples (N p : ℕ) : ((multiples N p).card : ℝ) ≤ (N : ℝ) * (1 / (p : ℝ)) := by
    have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    simp only [multiples, hIcc, Nat.Ioc_filter_dvd_card_eq_div, mul_one_div]
    exact Nat.cast_div_le
  let C : ℝ := (2 : ℝ) ^ K.primesBelow.card
  have hSmooth (N : ℕ) : ((Nat.smoothNumbersUpTo N K).card : ℝ) ≤ C * Real.sqrt (N : ℝ) := by
    calc
      _ ≤ C * (N.sqrt : ℝ) := by
        dsimp [C]
        exact_mod_cast Nat.smoothNumbersUpTo_card_le N K
      _ ≤ _ := mul_le_mul_of_nonneg_left Real.nat_sqrt_le_real_sqrt (by positivity)
  have hSqrt : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hSqrt.eventually_ge_atTop (C / (ε / 2))] with N hN
  have hBound : C * Real.sqrt (N : ℝ) ≤ (ε / 2) * (N : ℝ) := by
    have hProd := mul_le_mul_of_nonneg_right ((div_le_iff₀ (half_pos hε)).mp hN)
      (Real.sqrt_nonneg (N : ℝ))
    rw [mul_comm (Real.sqrt (N : ℝ)) (ε / 2), mul_assoc, ← sq,
      Real.sq_sqrt (Nat.cast_nonneg _)] at hProd
    exact hProd
  have hTailCount : (((tail N).biUnion (multiples N)).card : ℝ) ≤ (N : ℝ) * (ε / 2) := by
    calc
      _ ≤ ∑ p ∈ tail N, ((multiples N p).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ p ∈ tail N, (N : ℝ) * (1 / (p : ℝ)) :=
        Finset.sum_le_sum fun p _ => hMultiples N p
      _ = (N : ℝ) * ∑ p ∈ tail N, (1 / (p : ℝ)) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hTail N) (Nat.cast_nonneg _)
  calc
    _ ≤ ((Nat.smoothNumbersUpTo N K).card : ℝ) + ((tail N).biUnion (multiples N)).card := by
      exact_mod_cast (Finset.card_le_card (hCover N)).trans (Finset.card_union_le _ _)
    _ ≤ (ε / 2) * (N : ℝ) + (N : ℝ) * (ε / 2) :=
      add_le_add ((hSmooth N).trans hBound) hTailCount
    _ = _ := by ring

end OMA.Erdos269

namespace OMA.ER269

open scoped BigOperators

/-- A divisibility chain with arbitrarily small scaled tails has an irrational reciprocal sum. -/
theorem irrational_reciprocal_series (D : ℕ → ℕ) (hD : ∀ i, 0 < D i)
    (hdiv : ∀ i j, i ≤ j → D i ∣ D j)
    (hsum : Summable (fun i ↦ (1 : ℝ) / (D i : ℝ)))
    (hsmall : ∀ eps : ℝ, 0 < eps →
      ∃ m : ℕ, (∑' k : ℕ, (D m : ℝ) / (D (m + k + 1) : ℝ)) < eps) :
    Irrational (∑' i : ℕ, (1 : ℝ) / (D i : ℝ)) := by
  rintro ⟨q, hq⟩
  have hden : (0 : ℝ) < q.den := Nat.cast_pos.mpr q.pos
  obtain ⟨m, hm⟩ := hsmall (1 / (q.den : ℝ)) (one_div_pos.mpr hden)
  let f (i : ℕ) : ℝ := 1 / (D i : ℝ)
  let A : ℕ := ∑ i ∈ Finset.range (m + 1), D m / D i
  let tail : ℝ := ∑' k : ℕ, (D m : ℝ) / (D (m + k + 1) : ℝ)
  have hf : Summable f := hsum
  have hftail : Summable (fun k : ℕ ↦ f (k + (m + 1))) :=
    (summable_nat_add_iff (k := m + 1)).2 hf
  have hscale_tail : (D m : ℝ) * (∑' k : ℕ, f (k + (m + 1))) = tail := by
    rw [← hftail.tsum_mul_left]
    apply tsum_congr
    intro k
    rw [show k + (m + 1) = m + k + 1 by omega]
    exact mul_one_div _ _
  have htail_pos : 0 < tail := by
    rw [← hscale_tail]
    refine mul_pos (Nat.cast_pos.mpr (hD m)) (hftail.tsum_pos (fun i ↦ ?_) 0 ?_)
    · exact (one_div_pos.mpr (Nat.cast_pos.mpr (hD _))).le
    · exact one_div_pos.mpr (Nat.cast_pos.mpr (hD _))
  have hprefix : (D m : ℝ) * (∑ i ∈ Finset.range (m + 1), f i) = (A : ℝ) := by
    rw [Finset.mul_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    rw [Nat.cast_div (hdiv i m him) (Nat.cast_ne_zero.mpr (hD i).ne')]
    exact mul_one_div _ _
  have hsplit : (D m : ℝ) * (∑' i : ℕ, f i) = A + tail := by
    rw [← hf.sum_add_tsum_nat_add (m + 1), mul_add, hprefix, hscale_tail]
  have hrat : (q.den : ℝ) * (∑' i : ℕ, f i) = q.num := by
    change (q.den : ℝ) * (∑' i : ℕ, (1 : ℝ) / (D i : ℝ)) = q.num
    rw [← hq, Rat.cast_def, mul_comm, div_mul_cancel₀ _ hden.ne']
  let z : ℤ := (D m : ℤ) * q.num - (A : ℤ) * (q.den : ℤ)
  have hz : (z : ℝ) = (q.den : ℝ) * tail := by
    dsimp only [z]
    push_cast
    linear_combination (q.den : ℝ) * hsplit - (D m : ℝ) * hrat
  have hz_pos : 0 < (z : ℝ) := hz ▸ mul_pos hden htail_pos
  have hz_lt : (z : ℝ) < 1 := by
    rw [hz]
    have h := mul_lt_mul_of_pos_left hm hden
    rwa [mul_one_div, div_self hden.ne'] at h
  have hz_int_pos : 0 < z := by exact_mod_cast hz_pos
  have hz_int_lt : z < 1 := by exact_mod_cast hz_lt
  omega

end OMA.ER269

theorem OMA.solution : type_of% @Erdos269.erdos_269.variants.infinite := by
  intro P hP hinf
  obtain ⟨r, hrP⟩ := hinf.nonempty
  obtain ⟨s, hsP, hrs⟩ := large_prime_in_set hinf r
  have hr := hP r hrP
  have hs := hP s hsP
  obtain ⟨ha, hamem⟩ := smooth_range hr hrP
  have hap (j : ℕ) : 0 < Erdos269.a P j := (hamem j).1
  have hac (n : ℕ) (hn : Erdos269.HasPrimeFactorsIn P n) : ∃ j, Erdos269.a P j = n :=
    Nat.subset_range_nth hn
  let D := Erdos269.partialLcm P
  let C : ℝ := (r:ℝ) * (s:ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have cut {p m j : ℕ} (hpP : p ∈ P) (hsp : s < p) (hm : Erdos269.a P m = p) (hmj : m ≤ j) :=
    OMA.erdos269_cut_ratios ha hap hac hr hs (hP p hpP) hrP hsP hrs.ne (hrs.trans hsp) hsp hm hmj
  obtain ⟨p₀, hp₀P, hsp₀⟩ := large_prime_in_set hinf s
  obtain ⟨m₀, hm₀⟩ := hac _ (prime_smooth (hP p₀ hp₀P) hp₀P)
  have hsum : Summable (fun j : ℕ ↦ 1/(D j:ℝ)) := by
    apply series_summable_of_cut (partial_lcm_pos hap) ha m₀
      (hm₀ ▸ (hP p₀ hp₀P).two_le : 2 ≤ Erdos269.a P m₀) (C*(p₀:ℝ))
    intro j hj
    simpa only [D, C, mul_one_div] using (cut hp₀P hsp₀ hm₀ hj).1
  apply OMA.ER269.irrational_reciprocal_series D (partial_lcm_pos hap) (partial_lcm_dvd P) hsum
  intro ε hε
  have hhalf : 0 < ε/2 := half_pos hε
  by_cases hconv : Summable (fun p : ℕ ↦ if p ∈ P then 1/(p:ℝ) else 0)
  · obtain ⟨T, hT⟩ := exists_nat_gt (2*C/(ε/2)+2)
    have hTr : 0 < (T : ℝ) := by linarith [div_nonneg (mul_nonneg (by norm_num : 0 ≤ (2:ℝ)) hC) hhalf.le]
    have hTpos : 0 < T := by exact_mod_cast hTr
    have hfinal : 2*C/(T:ℝ) < ε/2 := by
      apply (div_lt_iff₀ hTr).2
      have ht : 2*C/(ε/2) < (T:ℝ) := by linarith
      linarith [(div_lt_iff₀ hhalf).mp ht]
    have hη : 0 < ε/(2*(T:ℝ)) := by positivity
    obtain ⟨B, hB⟩ := eventually_atTop.mp
      (OMA.Erdos269.smooth_count_of_summable P hP hconv _ hη)
    obtain ⟨p, hpP, hpB⟩ := large_prime_in_set hinf (max B s)
    have hsp : s < p := (le_max_right _ _).trans_lt hpB
    have hp2 := (hP p hpP).two_le
    have hpr : 0 < (p:ℝ) := by exact_mod_cast (hP p hpP).pos
    obtain ⟨m, hm⟩ := hac _ (prime_smooth (hP p hpP) hpP)
    refine ⟨m, ?_⟩
    have hpT : p ≤ T*p := by
      simpa using Nat.mul_le_mul_right p (show 1 ≤ T by omega)
    have hBT : B ≤ T*p := (le_max_left _ _).trans (hpB.le.trans hpT)
    have hEx : ∃ j, T*p ≤ Erdos269.a P j := by
      refine ⟨T*p, ?_⟩
      exact (Nat.le_add_right _ _).trans (by simpa only [add_zero] using ha.add_le_nat (T*p) 0)
    let l := Nat.find hEx
    have hl : T*p ≤ Erdos269.a P l := Nat.find_spec hEx
    have hml : m ≤ l := ha.le_iff_le.mp (hm.symm ▸ hpT.trans hl)
    have hl2 : 2 ≤ Erdos269.a P l := hp2.trans (hpT.trans hl)
    have hcount : l-m ≤ ((Finset.Icc 1 (T*p)).filter (Erdos269.HasPrimeFactorsIn P)).card := by
      rw [← Nat.card_Ico]
      apply Finset.card_le_card_of_injOn (Erdos269.a P) ?_ ha.injective.injOn
      intro j hj
      have hjl : j < l := (Finset.mem_Ico.mp hj).2
      have hjT : Erdos269.a P j ≤ T*p := (lt_of_not_ge (Nat.find_min hEx hjl)).le
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hap j, hjT⟩, hamem j⟩
    have hcountR : ((l-m : ℕ):ℝ) ≤ ε/(2*(T:ℝ)) * ((T:ℝ)*(p:ℝ)) := by
      have hh := hB (T*p) hBT
      rw [Nat.cast_mul] at hh
      exact (Nat.cast_le.mpr hcount).trans hh
    have hhead : ((l-m : ℕ):ℝ) * (1/(p:ℝ)) ≤ ε/2 := by
      calc
        _ ≤ (ε/(2*(T:ℝ)) * ((T:ℝ)*(p:ℝ))) * (1/(p:ℝ)) :=
          mul_le_mul_of_nonneg_right hcountR (by positivity)
        _ = _ := by field_simp
    have hlR : (T:ℝ)*(p:ℝ) ≤ (Erdos269.a P l:ℝ) := by exact_mod_cast hl
    have hl2R : (2:ℝ) ≤ (Erdos269.a P l:ℝ) := by exact_mod_cast hl2
    have hlpos : 0 < (Erdos269.a P l:ℝ)-1 := by linarith
    have htail : (C*(p:ℝ)) * (1/((Erdos269.a P l:ℝ)-1)) ≤ 2*C/(T:ℝ) := by
      calc
        _ = C * ((p:ℝ)/((Erdos269.a P l:ℝ)-1)) := by ring
        _ ≤ C * (2/(T:ℝ)) :=
          mul_le_mul_of_nonneg_left ((div_le_div_iff₀ hlpos hTr).2 (by linarith [mul_comm (p:ℝ) (T:ℝ)])) hC
        _ = _ := by ring
    have hbound := normalized_tail_bound hsum ha hml hl2 (1/(p:ℝ)) (C*(p:ℝ)) (by positivity)
      (fun j hj _ ↦ (cut hpP hsp hm hj).2.1)
      (fun j hj ↦ by simpa only [C, D, mul_one_div] using (cut hpP hsp hm (hml.trans hj)).1)
    exact hbound.trans_lt (by linarith)
  · obtain ⟨B, hB⟩ := exists_nat_gt (C/(ε/2)+1)
    obtain ⟨p, hpP, q, hqP, hpB, hpq, hclose⟩ :=
      close_primes_of_not_summable hP hinf hconv (ε/2) hhalf (max B (s+1))
    have hsp : s < p := (le_max_right _ _).trans hpB
    have hpr : 0 < (p:ℝ) := by exact_mod_cast (hP p hpP).pos
    have hqr : 0 < (q:ℝ) := by exact_mod_cast (hP q hqP).pos
    have hBq : (B:ℝ) < (q:ℝ) := by exact_mod_cast ((le_max_left _ _).trans hpB).trans_lt hpq
    obtain ⟨m, hm⟩ := hac _ (prime_smooth (hP p hpP) hpP)
    obtain ⟨l, hl⟩ := hac _ (prime_smooth (hP q hqP) hqP)
    refine ⟨m, ?_⟩
    have hml : m ≤ l := ha.le_iff_le.mp (by rw [hm, hl]; exact hpq.le)
    have hl2 : 2 ≤ Erdos269.a P l := by rw [hl]; exact (hP q hqP).two_le
    have hcard : (l-m : ℕ) + p ≤ q := by
      have h := ha.add_le_nat (l-m) m
      rwa [Nat.sub_add_cancel hml, hm, hl] at h
    have hcardR : ((l-m : ℕ):ℝ) + (p:ℝ) ≤ (q:ℝ) := by exact_mod_cast hcard
    have hhead : ((l-m : ℕ):ℝ) * (1/(p:ℝ)) < ε/2 := by
      rw [mul_one_div, div_lt_iff₀ hpr]
      nlinarith [hclose, hcardR]
    have hqr1 : 0 < (q:ℝ)-1 := by
      have hq2 : (2 : ℝ) ≤ (q:ℝ) := by exact_mod_cast (hP q hqP).two_le
      linarith
    have hfinal : C/((q:ℝ)-1) < ε/2 := by
      apply (div_lt_iff₀ hqr1).2
      have ht : C/(ε/2) < (q:ℝ)-1 := by linarith
      linarith [(div_lt_iff₀ hhalf).mp ht]
    have hCt : C*(p:ℝ)/(q:ℝ) ≤ C := by
      apply (div_le_iff₀ hqr).mpr
      exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hpq.le) hC
    have htail : (C*(p:ℝ)/(q:ℝ)) * (1/((Erdos269.a P l:ℝ)-1)) ≤ C/((q:ℝ)-1) := by
      rw [hl]
      simpa only [mul_one_div] using
        (mul_le_mul_of_nonneg_right hCt (one_div_nonneg.mpr hqr1.le))
    have hbound := normalized_tail_bound hsum ha hml hl2 (1/(p:ℝ)) (C*(p:ℝ)/(q:ℝ)) (by positivity)
      (fun j hj _ ↦ (cut hpP hsp hm hj).2.1)
      (fun j hj ↦ by
        have hqj : q ≤ Erdos269.a P j := hl ▸ ha.monotone hj
        simpa only [C, D, mul_one_div, div_div] using
          (cut hpP hsp hm (hml.trans hj)).2.2 q (hP q hqP) hqP hpq hqj)
    exact hbound.trans_lt (by linarith)
