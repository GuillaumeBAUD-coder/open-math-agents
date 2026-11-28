import FormalConjectures.GreensOpenProblems.«59»

/-!
# Reduction of Balog's theorem

Credit: @yuka30240. The dyadic triples follow S. Jain, *Sums of Integers with
Small Prime Factors*, §4, equations (4.2)–(4.4), with θ = 5/9.
https://arxiv.org/abs/2611.21136

The first step concerns only primes in a real-power interval. The second
counts triples before enforcing smoothness on both of their long factors.
The proof below combines the two estimates and removes the roughness
restriction on the integer to be represented.
-/

namespace OMA.R_Green59_green_59_variants_balog_R1

open Filter Green59
open scoped Classical

/-- Mertens' second theorem, with an unspecified Meissel–Mertens constant. -/
def H1 : Prop :=
  ∃ C : ℝ, Tendsto (fun x : ℝ =>
    (∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime, (p : ℝ)⁻¹) -
      Real.log (Real.log x)) atTop (nhds C)

/-- Distribution input on rough targets. In Jain's count, s is determined
by s + ℓmn = N. Mark just the m coordinate if it has a prime factor above Y.
The unmarked total and the marked upper bound are estimated in (4.3) and
(4.4). The sum of prime reciprocals keeps the Mertens step separate. -/
def H2 : Prop :=
  ∀ a : ℝ, 4 / (9 * Real.sqrt (Real.exp 1)) < a → a < 4 / 9 → ∀ η : ℝ, 0 < η →
    ∃ K : ℕ, ∀ᶠ N : ℕ in atTop,
      let Y := (N : ℝ) ^ a
      let M := (N : ℝ) ^ (4 / 9 : ℝ)
      let L := (N : ℝ) ^ (1 / 9 : ℝ) / Real.log (Real.log N)
      let I : Finset ℕ := Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊
      let J : Finset ℕ := (Finset.Ioc ⌊L⌋₊ ⌊2 * L⌋₊).filter fun ℓ => (ℓ : ℝ) ≤ Y
      let T := (J ×ˢ (I ×ˢ I)).filter fun (ℓ, m, n) =>
        let v : ℕ := ℓ * (m * n)
        v < N ∧ IsSmooth (min Y ((Real.log N) ^ K)) (N - v)
      let primes := (Finset.Ioc ⌊Y⌋₊ ⌊2 * M⌋₊).filter Nat.Prime
      Y < (N.minFac : ℝ) → T.Nonempty ∧
        ((T.filter fun t => ¬ IsSmooth Y t.2.1).card : ℝ) ≤
          ((∑ p ∈ primes, (p : ℝ)⁻¹) + η) * T.card

/-- Absorb the factor 2 in the dyadic endpoint by increasing b slightly.
Mertens' constant cancels when the two partial sums are subtracted. -/
lemma prime_interval (hmertens : H1) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hcrit : b < a * Real.sqrt (Real.exp 1)) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ N : ℕ in atTop,
      let primes := (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊2 * (N : ℝ) ^ b⌋₊).filter Nat.Prime
      (∑ p ∈ primes, (p : ℝ)⁻¹) + η < 1 / 2 := by
  obtain ⟨C, hC⟩ := hmertens
  obtain ⟨d, hbd, hd⟩ := exists_between hcrit
  have hdpos := ha.trans (hab.trans hbd)
  have hlog : Real.log d - Real.log a < 1 / 2 := by
    rw [← Real.log_div hdpos.ne' ha.ne', Real.log_lt_iff_lt_exp (div_pos hdpos ha),
      div_lt_iff₀ ha]
    simpa only [Real.sqrt_eq_rpow, Real.exp_one_rpow, mul_comm a] using hd
  let η := (1 / 2 - (Real.log d - Real.log a)) / 3
  have hη : 0 < η := by dsimp [η]; linarith
  refine ⟨η, hη, ?_⟩
  have grows (t : ℝ) (ht : 0 < t) :=
    (tendsto_rpow_atTop ht).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hdiff := (hC.comp (grows d hdpos)).sub (hC.comp (grows a ha))
  have herr := hdiff.eventually_lt_const (show C - C < η by linarith)
  filter_upwards [herr, (grows (d - b) (sub_pos.mpr hbd)).eventually_ge_atTop 2,
    eventually_ge_atTop 2] with N herror hscale hN
  have hbase : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hpositive := zero_lt_one.trans hbase
  have hupper : 2 * (N : ℝ) ^ b ≤ (N : ℝ) ^ d := by
    calc
      _ ≤ (N : ℝ) ^ (d - b) * (N : ℝ) ^ b :=
        mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hpositive.le _)
      _ = _ := by rw [← Real.rpow_add hpositive, sub_add_cancel]
  have hord : ⌊(N : ℝ) ^ a⌋₊ ≤ ⌊(N : ℝ) ^ d⌋₊ :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hbase.le (hab.trans hbd).le)
  have hcut := Finset.sum_Ioc_consecutive
    (fun p : ℕ => if p.Prime then (p : ℝ)⁻¹ else 0) (Nat.zero_le _) hord
  simp only [← Finset.sum_filter] at hcut
  have hsubset : (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊2 * (N : ℝ) ^ b⌋₊).filter Nat.Prime ⊆
      (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ d⌋₊).filter Nat.Prime := by
    apply Finset.filter_subset_filter
    exact Finset.Ioc_subset_Ioc le_rfl (Nat.floor_mono hupper)
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => (p : ℝ)⁻¹)
    hsubset (fun _ _ _ => by positivity)
  dsimp [Function.comp_def] at herror
  rw [Real.log_rpow hpositive, Real.log_rpow hpositive,
    Real.log_mul hdpos.ne' (Real.log_pos hbase).ne',
    Real.log_mul ha.ne' (Real.log_pos hbase).ne'] at herror
  dsimp only
  dsimp [η] at herror ⊢
  linarith

lemma smooth_of_le {y : ℝ} {m : ℕ} (hm : (m : ℝ) ≤ y) : IsSmooth y m :=
  fun _ hp => le_trans (mod_cast Nat.le_of_mem_primeFactors hp) hm

lemma smooth_mul {y : ℝ} {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : IsSmooth y m) (h' : IsSmooth y n) : IsSmooth y (m * n) := by
  intro p hp
  rw [Nat.primeFactors_mul hm.ne' hn.ne', Finset.mem_union] at hp
  exact hp.elim (h p) (h' p)

/-- Strip a small prime at a time, keeping the cutoff fixed. If the quotient
reaches the cutoff, the split 1 + (m - 1) starts the lift back up. -/
lemma split_from_rough (N : ℕ) (y : ℝ)
    (rough : ∀ m ≤ N, y < (m : ℝ) → y < (m.minFac : ℝ) →
      ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = m ∧ IsSmooth y a ∧ IsSmooth y b)
    (hN : 2 ≤ N) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = N ∧ IsSmooth y a ∧ IsSmooth y b := by
  suffices all : ∀ m ≤ N, 2 ≤ m →
      ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = m ∧ IsSmooth y a ∧ IsSmooth y b from
    all N le_rfl hN
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm htwo
    by_cases hy : (m : ℝ) ≤ y
    · exact ⟨1, m - 1, by decide, by omega, by omega, by simp [IsSmooth],
        smooth_of_le (le_trans (by exact_mod_cast Nat.sub_le m 1) hy)⟩
    by_cases hp : y < (m.minFac : ℝ)
    · exact rough m hm (lt_of_not_ge hy) hp
    have hpm : m.minFac < m := by
      exact_mod_cast lt_of_le_of_lt (le_of_not_gt hp) (lt_of_not_ge hy)
    have hprime := Nat.minFac_prime (show m ≠ 1 by omega)
    obtain ⟨q, hq⟩ := Nat.minFac_dvd m
    have hqpos : 0 < q := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at hq; omega
    have hq2 : 2 ≤ q := by
      by_contra! hsmall
      have : q = 1 := by omega
      simp [this] at hq
      omega
    have hqlt : q < m := by
      calc
        q = 1 * q := (one_mul _).symm
        _ < m.minFac * q := Nat.mul_lt_mul_of_pos_right hprime.one_lt hqpos
        _ = m := hq.symm
    obtain ⟨a, b, ha, hb, hab, hsa, hsb⟩ := ih q hqlt (hqlt.le.trans hm) hq2
    have hs := smooth_of_le (le_of_not_gt hp)
    exact ⟨m.minFac * a, m.minFac * b, Nat.mul_pos hprime.pos ha, Nat.mul_pos hprime.pos hb,
      by rw [← Nat.mul_add, hab, ← hq],
      smooth_mul hprime.pos ha hs hsa, smooth_mul hprime.pos hb hs hsb⟩

/-- In a symmetric family, fewer than half the triples failing in their first
long coordinate leaves a triple passing in both long coordinates. -/
lemma exists_good_pair (T : Finset (ℕ × ℕ × ℕ)) (P : ℕ → Prop)
    (swap : ∀ ℓ m n, (ℓ, m, n) ∈ T → (ℓ, n, m) ∈ T)
    (hfew : 2 * (T.filter fun t => ¬ P t.2.1).card < T.card) :
    ∃ ℓ m n, (ℓ, m, n) ∈ T ∧ P m ∧ P n := by
  classical
  by_contra! hnone
  have hinj : (T.filter fun t => P t.2.1).card ≤ (T.filter fun t => ¬ P t.2.1).card := by
    apply Finset.card_le_card_of_injOn (fun (ℓ, m, n) => (ℓ, n, m))
    · rintro ⟨ℓ, m, n⟩ ht
      obtain ⟨ht, hgood⟩ := Finset.mem_filter.mp ht
      exact Finset.mem_filter.mpr ⟨swap ℓ m n ht, hnone ℓ m n ht hgood⟩
    · rintro ⟨ℓ, m, n⟩ _ ⟨ℓ', m', n'⟩ _ he
      simpa [Prod.mk.injEq, and_comm, and_left_comm] using he
  have htotal := Finset.card_filter_add_card_filter_not (s := T) (fun t => P t.2.1)
  omega

theorem main : H1 → H2 → type_of% @Green59.green_59.variants.balog := by
  classical
  intro hmertens hcount ε hε
  let c := 4 / (9 * Real.sqrt (Real.exp 1))
  have hsqrt : 0 < Real.sqrt (Real.exp 1) := by positivity
  have hsqrt_one : 1 < Real.sqrt (Real.exp 1) := by
    rw [Real.sqrt_eq_rpow, Real.exp_one_rpow, Real.one_lt_exp_iff]
    norm_num
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hc : c < 4 / 9 := by
    dsimp [c]
    rw [div_mul_eq_div_div, div_lt_iff₀ hsqrt]
    linarith
  let a := min (c + ε) ((c + 4 / 9) / 2)
  have hca : c < a := lt_min (by linarith) (by linarith)
  have ha := hcpos.trans hca
  have hab : a < 4 / 9 := (min_le_right _ _).trans_lt (by linarith)
  have hcrit : (4 / 9 : ℝ) < a * Real.sqrt (Real.exp 1) := by
    have h := mul_lt_mul_of_pos_right hca hsqrt
    dsimp [c] at h
    rwa [div_mul_eq_div_div, div_mul_cancel₀ _ hsqrt.ne'] at h
  obtain ⟨η, hη, hmass⟩ := prime_interval hmertens ha hab hcrit
  obtain ⟨K, htuples⟩ := hcount a hca hab η hη
  obtain ⟨B, hB⟩ := eventually_atTop.mp (hmass.and htuples)
  have hgrowth := (tendsto_rpow_atTop ha).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop 2, hgrowth.eventually_ge_atTop (B : ℝ)] with N hN hlarge
  have hfinal : (N : ℝ) ^ a ≤ (N : ℝ) ^ (c + ε) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (min_le_left _ _)
  suffices h : ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ u + v = N ∧
      IsSmooth ((N : ℝ) ^ a) u ∧ IsSmooth ((N : ℝ) ^ a) v by
    obtain ⟨u, v, hu, hv, huv, hsu, hsv⟩ := h
    exact ⟨u, v, hu, hv, huv, fun p hp => (hsu p hp).trans hfinal,
      fun p hp => (hsv p hp).trans hfinal⟩
  apply split_from_rough N ((N : ℝ) ^ a) _ hN
  intro k hk hky hrough
  have hBk : B ≤ k := by exact_mod_cast hlarge.trans hky.le
  have hmono : (k : ℝ) ^ a ≤ (N : ℝ) ^ a := by
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hk) ha.le
  obtain ⟨hmass', htuples'⟩ := hB k hBk
  let Y := (k : ℝ) ^ a
  let M := (k : ℝ) ^ (4 / 9 : ℝ)
  let L := (k : ℝ) ^ (1 / 9 : ℝ) / Real.log (Real.log k)
  let I : Finset ℕ := Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊
  let J : Finset ℕ := (Finset.Ioc ⌊L⌋₊ ⌊2 * L⌋₊).filter fun ℓ => (ℓ : ℝ) ≤ Y
  let T := (J ×ˢ (I ×ˢ I)).filter fun (ℓ, m, n) =>
    let v : ℕ := ℓ * (m * n)
    v < k ∧ IsSmooth (min Y ((Real.log k) ^ K)) (k - v)
  let primes := (Finset.Ioc ⌊Y⌋₊ ⌊2 * M⌋₊).filter Nat.Prime
  obtain ⟨hne, hbad⟩ := htuples' (hmono.trans_lt hrough)
  change T.Nonempty at hne
  change ((T.filter fun t => ¬ IsSmooth Y t.2.1).card : ℝ) ≤
    ((∑ p ∈ primes, (p : ℝ)⁻¹) + η) * T.card at hbad
  change (∑ p ∈ primes, (p : ℝ)⁻¹) + η < 1 / 2 at hmass'
  have hpos : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hfew := hbad.trans_lt (mul_lt_mul_of_pos_right hmass' hpos)
  have hfew' : 2 * (T.filter fun t => ¬ IsSmooth Y t.2.1).card < T.card := by
    exact_mod_cast (show 2 * ((T.filter fun t => ¬ IsSmooth Y t.2.1).card : ℝ) < T.card by
      linarith)
  have hswap : ∀ ℓ m n, (ℓ, m, n) ∈ T → (ℓ, n, m) ∈ T := by
    intro ℓ m n ht
    obtain ⟨hbox, hpred⟩ := Finset.mem_filter.mp ht
    obtain ⟨hℓ, hmn⟩ := Finset.mem_product.mp hbox
    obtain ⟨hm, hn⟩ := Finset.mem_product.mp hmn
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hℓ, Finset.mem_product.mpr ⟨hn, hm⟩⟩, ?_⟩
    simpa only [Nat.mul_comm n m] using hpred
  obtain ⟨ℓ, m, n, ht, hm, hn⟩ := exists_good_pair T (IsSmooth Y) hswap hfew'
  obtain ⟨hbox, hv, hrest⟩ := Finset.mem_filter.mp ht
  obtain ⟨hℓ, hmn⟩ := Finset.mem_product.mp hbox
  obtain ⟨hmI, hnI⟩ := Finset.mem_product.mp hmn
  obtain ⟨hℓJ, hℓY⟩ := Finset.mem_filter.mp hℓ
  have hℓpos := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hℓJ).1
  have hmpos := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hmI).1
  have hnpos := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hnI).1
  have hprod := smooth_mul hℓpos (Nat.mul_pos hmpos hnpos) (smooth_of_le hℓY)
    (smooth_mul hmpos hnpos hm hn)
  exact ⟨ℓ * (m * n), k - ℓ * (m * n), Nat.mul_pos hℓpos (Nat.mul_pos hmpos hnpos),
    Nat.sub_pos_of_lt hv, Nat.add_sub_of_le hv.le,
    fun p hp => (hprod p hp).trans hmono,
    fun p hp => (hrest p hp).trans ((min_le_left _ _).trans hmono)⟩

end OMA.R_Green59_green_59_variants_balog_R1
