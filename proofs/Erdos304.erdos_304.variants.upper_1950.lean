import FormalConjectures.ErdosProblems.«304»

/-! # Erdős 1950: `N(b) ≪ log b / log log b`

Every `x ≤ n!` is a sum of at most `n` distinct divisors of `n!` (divide by `n` and induct).
Given `a < b ≤ n!` with `M = n!`, write `a M = q b + r`; then
`a / b = q / M + r / (b M)`, and expanding `q` and `r` in divisors of `M` gives at most `2n`
distinct unit fractions (those from `q` have denominators at most `M`, those from `r` above `M`).
Finally `n = ⌈3 log b / log log b⌉` already has `n! ≥ b`, by `n! ≥ nⁿ / eⁿ`. -/

open Filter

namespace OMA.Egyptian304
open Erdos304

/-- Every `x ≤ (n+1)!` is a sum of at most `n+1` distinct positive divisors of `(n+1)!`. -/
lemma repr (n : ℕ) : ∀ x ≤ (n + 1).factorial, ∃ S : Finset ℕ, S.card ≤ n + 1 ∧
    (∀ d ∈ S, 0 < d ∧ d ∣ (n + 1).factorial) ∧ ∑ d ∈ S, d = x := by
  induction n with
  | zero =>
    intro x hx
    simp only [zero_add, Nat.factorial_one] at hx
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with rfl | rfl
    · exact ⟨∅, by simp, by simp, by simp⟩
    · exact ⟨{1}, by simp, by simp, by simp⟩
  | succ n ih =>
    intro x hx
    have hfac : (n + 2).factorial = (n + 2) * (n + 1).factorial := Nat.factorial_succ (n + 1)
    have hq : x / (n + 2) ≤ (n + 1).factorial := by
      apply Nat.div_le_of_le_mul
      rw [← hfac]; exact hx
    obtain ⟨S, hcard, hS, hsum⟩ := ih (x / (n + 2)) hq
    have hinj : Function.Injective (fun d : ℕ => d * (n + 2)) := by
      intro u v h
      simpa using h
    set T := S.image (fun d : ℕ => d * (n + 2)) with hT
    have hTcard : T.card = S.card := Finset.card_image_of_injective _ hinj
    have hTmem : ∀ e ∈ T, 0 < e ∧ e ∣ (n + 1 + 1).factorial ∧ n + 2 ≤ e := by
      intro e he
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hd0, hdd⟩ := hS d hd
      refine ⟨by positivity, ?_, by nlinarith⟩
      rw [show n + 1 + 1 = n + 2 from rfl, hfac, mul_comm d]
      exact Nat.mul_dvd_mul_left _ hdd
    have hTsum : ∑ e ∈ T, e = (x / (n + 2)) * (n + 2) := by
      rw [hT, Finset.sum_image (fun u _ v _ h => hinj h), ← Finset.sum_mul, hsum]
    have hdm := Nat.div_add_mod x (n + 2)
    have hr : x % (n + 2) < n + 2 := Nat.mod_lt _ (by omega)
    by_cases h0 : x % (n + 2) = 0
    · refine ⟨T, by omega, fun e he => ⟨(hTmem e he).1, (hTmem e he).2.1⟩, ?_⟩
      rw [hTsum]; rw [h0] at hdm; linarith
    · have hnot : x % (n + 2) ∉ T := fun h => by have := (hTmem _ h).2.2; omega
      refine ⟨insert (x % (n + 2)) T, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hnot]; omega
      · intro e he
        rcases Finset.mem_insert.mp he with rfl | he
        · refine ⟨Nat.pos_of_ne_zero h0, Nat.dvd_factorial (Nat.pos_of_ne_zero h0) (by omega)⟩
        · exact ⟨(hTmem e he).1, (hTmem e he).2.1⟩
      · rw [Finset.sum_insert hnot, hTsum]; linarith

lemma key (a b m : ℕ) (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ (m + 1).factorial) :
    smallestCollection a b ≤ 2 * (m + 1) := by
  set M := (m + 1).factorial with hM
  have hMpos : 0 < M := Nat.factorial_pos _
  have hbpos : 0 < b := by omega
  set q := a * M / b with hqdef
  set r := a * M % b with hrdef
  have hdm : b * q + r = a * M := Nat.div_add_mod (a * M) b
  have hr : r < b := Nat.mod_lt _ hbpos
  have hqM : q < M := by
    rw [hqdef, Nat.div_lt_iff_lt_mul hbpos]
    rw [mul_comm M b]; exact Nat.mul_lt_mul_of_pos_right hab hMpos
  obtain ⟨S1, hc1, hS1, hs1⟩ := repr m q hqM.le
  obtain ⟨S2, hc2, hS2, hs2⟩ := repr m r (by omega)
  replace hS1 : ∀ d ∈ S1, 0 < d ∧ d ∣ M := hS1
  replace hS2 : ∀ d ∈ S2, 0 < d ∧ d ∣ M := hS2
  have hle1 : ∀ d ∈ S1, d ≤ q := fun d hd => by rw [← hs1]; exact Finset.single_le_sum (f := fun x => x) (fun _ _ => Nat.zero_le _) hd
  have hle2 : ∀ e ∈ S2, e ≤ r := fun e he => by rw [← hs2]; exact Finset.single_le_sum (f := fun x => x) (fun _ _ => Nat.zero_le _) he
  set T1 := S1.image (fun d => M / d) with hT1
  set T2 := S2.image (fun e => b * M / e) with hT2
  have hinj1 : Set.InjOn (fun d => M / d) S1 := by
    intro u hu v hv h
    simp only at h
    rw [← Nat.div_div_self (hS1 u hu).2 hMpos.ne', h, Nat.div_div_self (hS1 v hv).2 hMpos.ne']
  have hinj2 : Set.InjOn (fun e => b * M / e) S2 := by
    intro u hu v hv h
    simp only at h
    have hu' : u ∣ b * M := Dvd.dvd.mul_left (hS2 u hu).2 b
    have hv' : v ∣ b * M := Dvd.dvd.mul_left (hS2 v hv).2 b
    have hbM : b * M ≠ 0 := by positivity
    rw [← Nat.div_div_self hu' hbM, h, Nat.div_div_self hv' hbM]
  have hT1mem : ∀ y ∈ T1, 1 < y ∧ y ≤ M := by
    intro y hy
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hd0, k, hk⟩ := hS1 d hd
    have hdq := hle1 d hd
    refine ⟨?_, Nat.div_le_self _ _⟩
    rw [hk, Nat.mul_div_cancel_left _ hd0]
    rcases Nat.lt_or_ge 1 k with h | h
    · exact h
    · exfalso
      interval_cases k
      · simp at hk; omega
      · simp at hk; omega
  have hT2mem : ∀ y ∈ T2, M < y := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨he0, k, hk⟩ := hS2 e he
    have her := hle2 e he
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h] at hk; omega
      · exact h
    rw [hk, show b * (e * k) = e * (b * k) by ring, Nat.mul_div_cancel_left _ he0]
    nlinarith
  have hdisj : Disjoint T1 T2 := by
    rw [Finset.disjoint_left]
    intro y h1 h2
    have := (hT1mem y h1).2
    have := hT2mem y h2
    omega
  have hmem : (T1 ∪ T2).card ∈ unitFractionExpressible a b := by
    refine ⟨T1 ∪ T2, rfl, ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_union.mp hy with h | h
      · exact (hT1mem y h).1
      · have := hT2mem y h; omega
    · rw [Finset.sum_union hdisj, hT1, hT2, Finset.sum_image hinj1, Finset.sum_image hinj2]
      have e1 : ∑ d ∈ S1, (((M / d : ℕ) : ℚ))⁻¹ = (q : ℚ) / M := by
        rw [← hs1]
        push_cast
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun d hd => ?_
        rw [Nat.cast_div (hS1 d hd).2 (by exact_mod_cast (hS1 d hd).1.ne'), inv_div]
      have e2 : ∑ e ∈ S2, (((b * M / e : ℕ) : ℚ))⁻¹ = (r : ℚ) / (b * M) := by
        rw [← hs2]
        push_cast
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun e he => ?_
        rw [Nat.cast_div (Dvd.dvd.mul_left (hS2 e he).2 b)
          (by exact_mod_cast (hS2 e he).1.ne'), inv_div]
        push_cast
        rfl
      rw [e1, e2]
      have hdmQ : (b : ℚ) * q + r = a * M := by exact_mod_cast hdm
      have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hbpos.ne'
      have hMQ : (M : ℚ) ≠ 0 := by exact_mod_cast hMpos.ne'
      field_simp
      linear_combination (-1 : ℚ) * hdmQ
  have hcard : (T1 ∪ T2).card ≤ 2 * (m + 1) := by
    have := Finset.card_union_le T1 T2
    have h1 : T1.card ≤ S1.card := Finset.card_image_le
    have h2 : T2.card ≤ S2.card := Finset.card_image_le
    omega
  exact le_trans (Nat.sInf_le hmem) hcard

lemma to_le (b m : ℕ) (hb : b ≤ (m + 1).factorial) : smallestCollectionTo b ≤ 2 * (m + 1) := by
  apply csSup_le'
  rintro _ ⟨a, ha, rfl⟩
  rw [Finset.mem_Ico] at ha
  exact key a b m ha.1 ha.2 hb

/-- `n log n - n ≤ log n!`. -/
lemma log_factorial_ge (n : ℕ) : (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h := Real.pow_div_factorial_le_exp (n : ℝ) (by positivity) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ hf] at h
  have hl := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_mul (Real.exp_pos _).ne' hf.ne', Real.log_exp] at hl
  linarith

theorem main :
    (fun b => (smallestCollectionTo b : ℝ)) =O[atTop]
      (fun b => Real.log b / Real.log (Real.log b)) := by
  have hlim : Tendsto (fun b : ℕ => Real.log (Real.log b)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine Asymptotics.IsBigO.of_bound 8 ?_
  filter_upwards [hlim.eventually_ge_atTop 6] with b hL
  set ℓ := Real.log b with hℓ
  set L := Real.log ℓ with hLdef
  have hℓ0 : 0 ≤ ℓ := Real.log_natCast_nonneg b
  have hℓ1 : 1 < ℓ := by
    by_contra h
    push Not at h
    have : L ≤ 0 := Real.log_nonpos hℓ0 h
    linarith
  have hLpos : 0 < L := by linarith
  have hℓL : L ≤ ℓ := by have := Real.log_le_sub_one_of_pos (by linarith : 0 < ℓ); linarith
  have hlogL : Real.log L ≤ L / 2 := by
    have h1 := Real.log_le_sub_one_of_pos (by linarith : 0 < L / 2)
    rw [Real.log_div hLpos.ne' (by norm_num)] at h1
    have := Real.log_two_lt_d9
    linarith
  set x := 3 * ℓ / L with hxdef
  have hx3 : 3 ≤ x := by
    rw [hxdef, le_div_iff₀ hLpos]; linarith
  have hlogx : Real.log x = Real.log 3 + L - Real.log L := by
    rw [hxdef, Real.log_div (by positivity) hLpos.ne', Real.log_mul (by norm_num) (by linarith)]
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hx1 : L / 3 ≤ Real.log x - 1 := by rw [hlogx]; linarith
  set n := ⌈x⌉₊ with hndef
  have hxn : x ≤ n := Nat.le_ceil x
  have hnx : (n : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  have hn1 : 1 ≤ n := by
    have : (1 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hlogn : Real.log x ≤ Real.log n := Real.log_le_log (by linarith) hxn
  have hℓn : ℓ ≤ Real.log (n.factorial) := by
    have h1 := log_factorial_ge n
    have h2 : x * (Real.log x - 1) ≤ n * (Real.log n - 1) := by
      apply mul_le_mul hxn (by linarith) (by linarith) (by linarith)
    have h3 : x * (L / 3) ≤ x * (Real.log x - 1) := mul_le_mul_of_nonneg_left hx1 (by linarith)
    have h4 : x * (L / 3) = ℓ := by rw [hxdef]; field_simp
    nlinarith
  have hbpos : (0 : ℝ) < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · have : ℓ = 0 := by rw [hℓ, h]; simp
      linarith
    · exact_mod_cast h
  have hbn : b ≤ n.factorial := by
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have := (Real.log_le_log_iff hbpos hf).mp hℓn
    exact_mod_cast this
  have hto := to_le b (n - 1) (by rw [Nat.sub_add_cancel hn1]; exact hbn)
  rw [Nat.sub_add_cancel hn1] at hto
  have hto' : (smallestCollectionTo b : ℝ) ≤ 2 * n := by exact_mod_cast hto
  rw [Real.norm_natCast, Real.norm_of_nonneg (div_nonneg hℓ0 hLpos.le)]
  have hq : ℓ / L = x / 3 := by rw [hxdef]; ring
  rw [hq]
  linarith

end OMA.Egyptian304

theorem OMA.solution : type_of% @Erdos304.erdos_304.variants.upper_1950 := OMA.Egyptian304.main
