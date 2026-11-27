import FormalConjectures.ErdosProblems.«975»

/-! A reduction by complementary factor pairs and periodic counting on short moduli. -/

open Finset Polynomial Real Filter Function
open scoped ArithmeticFunction.sigma Topology

namespace OMA.R_Erdos975_erdos_975_R1


-- Counting ties with weight one avoids a separate square-value error.
theorem pair_identity (m N : ℕ) :
    σ 0 m =
      (∑ d ∈ m.divisors, if d ≤ N ∧ d * d ≤ m then 1 else 0) +
      (∑ d ∈ m.divisors, if d ≤ N ∧ d * d < m then 1 else 0) +
      (m.divisorsAntidiagonal.filter (fun p ↦ N < p.1 ∧ N < p.2)).card := by
  let s := m.divisorsAntidiagonal
  have first : (∑ p ∈ s, if p.1 ≤ N ∧ p.1 ≤ p.2 then 1 else 0) =
      ∑ d ∈ m.divisors, if d ≤ N ∧ d*d ≤ m then 1 else 0 := by
    rw [show s = _ from rfl, Nat.sum_divisorsAntidiagonal
      (fun a b ↦ if a ≤ N ∧ a ≤ b then 1 else 0)]
    apply sum_congr rfl
    intro d hd
    have h := Nat.mem_divisors.mp hd
    have hp := Nat.pos_of_mem_divisors hd
    have he := Nat.mul_div_cancel' h.1
    have hh : d ≤ m / d ↔ d*d ≤ m := by
      calc d ≤ m / d ↔ d*d ≤ d*(m/d) := (Nat.mul_le_mul_left_iff hp).symm
           _ ↔ _ := by rw [he]
    simp only [hh]
  have second : (∑ p ∈ s, if p.2 ≤ N ∧ p.2 < p.1 then 1 else 0) =
      ∑ d ∈ m.divisors, if d ≤ N ∧ d*d < m then 1 else 0 := by
    rw [show s = _ from rfl, Nat.sum_divisorsAntidiagonal'
      (fun a b ↦ if b ≤ N ∧ b < a then 1 else 0)]
    apply sum_congr rfl
    intro d hd
    have h := Nat.mem_divisors.mp hd
    have hp := Nat.pos_of_mem_divisors hd
    have he := Nat.mul_div_cancel' h.1
    have hh : d < m / d ↔ d*d < m := by
      calc d < m / d ↔ d*d < d*(m/d) := (Nat.mul_lt_mul_left hp).symm
           _ ↔ _ := by rw [he]
    simp only [hh]
  rw [← first, ← second, ArithmeticFunction.sigma_zero_apply]
  have cardeq : m.divisors.card = ∑ _p ∈ s, 1 := by
    rw [show s = _ from rfl, Nat.sum_divisorsAntidiagonal (fun _ _ ↦ 1)]
    simp
  rw [cardeq, Finset.card_filter, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  split_ifs <;> omega

theorem weighted_short (m N : ℕ) (strict : Bool) :
    (∑ d ∈ m.divisors, if d ≤ N ∧ (if strict then d*d < m else d*d ≤ m) then 1 else 0) =
    ∑ d ∈ Icc 1 N, if d ∣ m ∧ (if strict then d*d < m else d*d ≤ m) then 1 else 0 := by
  classical
  rw [← Finset.card_filter, ← Finset.card_filter]
  congr 1
  ext d
  simp only [mem_filter, Nat.mem_divisors, mem_Icc]
  have hpos : d ∣ m → m ≠ 0 → 1 ≤ d := fun h hm ↦ Nat.pos_of_dvd_of_pos h (Nat.pos_of_ne_zero hm)
  have hsq : 1 ≤ d → 0 < d*d := fun hd ↦ Nat.mul_pos hd hd
  cases strict <;> simp <;> constructor <;> rintro h <;> obtain ⟨_,_⟩ := h <;> grind

-- Relate integer evaluations to the natural floor in the target, even at a root.
theorem floor_test (z : ℤ) {d : ℕ} (hd : 0 < d) (strict : Bool) :
    (d ∣ ⌊z⌋₊ ∧ (if strict then d*d < ⌊z⌋₊ else d*d ≤ ⌊z⌋₊)) ↔
    ((d : ℤ) ∣ z ∧ (if strict then (d : ℤ)*d < z else (d : ℤ)*d ≤ z)) := by
  rcases le_or_gt 0 z with h | h
  · lift z to ℕ using h with m
    simp only [Nat.floor_natCast]
    cases strict <;> simp <;> exact_mod_cast Iff.rfl
  · have hz : ⌊z⌋₊ = 0 := Nat.floor_of_nonpos h.le
    have hp : 0 < d*d := Nat.mul_pos hd hd
    have hpi : (0 : ℤ) < ↑d * ↑d := by exact_mod_cast hp
    cases strict <;> simp [hz] <;> omega


theorem periodic_roots (f : ℤ[X]) (d : ℕ) :
    Periodic (fun n : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ)) d := by
  intro n
  apply propext
  have h : (d : ℤ) ∣ f.eval ((n+d : ℕ) : ℤ) - f.eval (n : ℤ) := by
    simpa using Polynomial.sub_dvd_eval_sub ((n+d : ℕ) : ℤ) (n : ℤ) f
  exact ⟨fun h1 ↦ by simpa using dvd_sub h1 h, fun h2 ↦ by simpa using dvd_add h h2⟩

theorem count_period_block (P : ℕ → Prop) [DecidablePred P] {d : ℕ}
    (hp : Periodic P d) (A q : ℕ) :
    Nat.count (fun n ↦ P (A+n)) (q*d) = q * Nat.count P d := by
  have shift (B : ℕ) : Nat.count (fun n ↦ P (B+n)) d = Nat.count P d := by
    rw [Nat.count_eq_card_filter_range, ← Nat.filter_Ico_card_eq_of_periodic B d P hp,
      Finset.card_filter, Finset.card_filter]
    simpa only [Nat.add_sub_cancel_left, Nat.add_sub_cancel, Nat.add_comm B] using
      (Finset.sum_Ico_eq_sum_range (f := fun n ↦ if P n then 1 else 0) (m := B) (n := B+d)).symm
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, Nat.count_add, ih, Nat.succ_mul]
    simpa [Nat.add_assoc] using congrArg (q * Nat.count P d + ·) (shift (A+q*d))

theorem interval_error (P : ℕ → Prop) [DecidablePred P] {d : ℕ}
    (hd : 0 < d) (hp : Periodic P d) (A L : ℕ) :
    |(Nat.count (fun n ↦ P (A+n)) L : ℝ) - (L : ℝ) / d * Nat.count P d| ≤ Nat.count P d := by
  let q := L / d
  have lo : q*d ≤ L := Nat.div_mul_le_self L d
  have hi : L ≤ (q+1)*d := by simpa [q, Nat.mul_comm] using (Nat.lt_mul_div_succ L hd).le
  have c1 := Nat.count_monotone (fun n ↦ P (A+n)) lo
  have c2 := Nat.count_monotone (fun n ↦ P (A+n)) hi
  rw [count_period_block P hp] at c1 c2
  have hlo : (q : ℝ) ≤ (L : ℝ)/d := (le_div_iff₀ (by positivity)).2 (by exact_mod_cast lo)
  have hhi : (L : ℝ)/d ≤ q+1 := (div_le_iff₀ (by positivity)).2 (by exact_mod_cast hi)
  have u := mul_le_mul_of_nonneg_right hlo (Nat.cast_nonneg (α := ℝ) (Nat.count P d))
  have v := mul_le_mul_of_nonneg_right hhi (Nat.cast_nonneg (α := ℝ) (Nat.count P d))
  have cl : (q : ℝ)*Nat.count P d ≤ Nat.count (fun n ↦ P (A+n)) L := by exact_mod_cast c1
  have cu : (Nat.count (fun n ↦ P (A+n)) L : ℝ) ≤ (q+1)*Nat.count P d := by exact_mod_cast c2
  rw [abs_le]
  constructor <;> linarith

theorem ico_root_error (P : ℕ → Prop) [DecidablePred P] {d : ℕ}
    (hd : 0 < d) (hp : Function.Periodic P d) (A T : ℕ) :
    |(((Ico A T).filter P).card : ℝ) - ((Ico A T).card : ℝ) / d * Nat.count P d| ≤ Nat.count P d := by
  have he : ((Ico A T).filter P).card = Nat.count (fun n ↦ P (A+n)) (T-A) := by
    simp only [Nat.count_eq_card_filter_range, card_filter]
    simpa only [add_comm A] using (Finset.sum_Ico_eq_sum_range (f := fun n ↦ if P n then 1 else 0) (m := A) (n := T))
  simpa only [he, Nat.card_Ico] using interval_error P hd hp A (T-A)

theorem threshold_error (f : ℤ[X]) {K : ℕ}
    (hK : Monotone (fun n : ℕ ↦ f.eval ((K+n : ℕ) : ℤ)))
    (T : ℕ) (u : ℤ) {d : ℕ} (hd : 0 < d) :
    let S := (range T).filter (fun n : ℕ ↦ u ≤ f.eval (n : ℤ))
    let P := fun n : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ)
    |((S.filter P).card : ℝ) - (S.card : ℝ)/d * Nat.count P d| ≤ K + Nat.count P d := by
  dsimp only
  let S := (range T).filter (fun n : ℕ ↦ u ≤ f.eval (n : ℤ))
  let B := S.filter (· < K)
  let U := S.filter (K ≤ ·)
  let P := fun n : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ)
  have hmono {n k : ℕ} (hn : K ≤ n) (hnk : n ≤ k) : f.eval (n : ℤ) ≤ f.eval (k : ℤ) := by
    simpa [Nat.add_sub_of_le hn, Nat.add_sub_of_le (hn.trans hnk)] using
      hK (show n-K ≤ k-K by omega)
  have suffix : ∃ A, U = Ico A T := by
    by_cases h : U.Nonempty
    · let a := U.min' h
      have ha : a ∈ U := U.min'_mem h
      simp only [U,S, mem_filter, mem_range] at ha
      refine ⟨a, Finset.ext (fun n ↦ ?_)⟩
      constructor
      · intro hn
        have hmin := U.min'_le n hn
        simp only [U,S,mem_filter,mem_range] at hn
        exact mem_Ico.mpr ⟨hmin, hn.1.1⟩
      · intro hn
        obtain ⟨han, hnT⟩ := mem_Ico.mp hn
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr hnT, ha.1.2.trans (hmono ha.2 han)⟩, ha.2.trans han⟩
    · exact ⟨T, by simp [Finset.not_nonempty_iff_eq_empty.mp h]⟩
  obtain ⟨A, hA⟩ := suffix
  have hpart : B ∪ U = S := by
    ext n
    simp only [B,U,mem_union,mem_filter]
    by_cases hn : n < K <;> simp [hn, show K ≤ n ↔ ¬n < K from not_lt.symm]
  have hdis : Disjoint B U := by
    apply Finset.disjoint_left.mpr
    intro n hb hu
    exact (mem_filter.mp hb).2.not_ge (mem_filter.mp hu).2
  have hboth : (B.filter P).card + (U.filter P).card = (S.filter P).card := by
    rw [← card_union_of_disjoint (hdis.mono (filter_subset ..) (filter_subset ..)), ← filter_union, hpart]
  have hall : B.card + U.card = S.card := by rw [← card_union_of_disjoint hdis, hpart]
  have hB : B.card ≤ K := by
    calc B.card ≤ (range K).card := card_le_card (fun n hn ↦ mem_range.mpr (mem_filter.mp hn).2)
         _ = K := card_range _
  have hBP : (B.filter P).card ≤ K := (card_le_card (filter_subset ..)).trans hB
  have hR : Nat.count P d ≤ d := Nat.count_le _
  have hBmodel : (B.card : ℝ)/d * Nat.count P d ≤ K := by
    calc _ ≤ (B.card : ℝ)/d * d := mul_le_mul_of_nonneg_left (by exact_mod_cast hR) (by positivity)
         _ = B.card := div_mul_cancel₀ _ (by positivity)
         _ ≤ K := by exact_mod_cast hB
  have hE : |((B.filter P).card : ℝ) - (B.card : ℝ)/d * Nat.count P d| ≤ K := by
    rw [abs_le]
    have v : 0 ≤ (B.card : ℝ)/d * Nat.count P d := by positivity
    have hb' : ((B.filter P).card : ℝ) ≤ K := by exact_mod_cast hBP
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (B.filter P).card]
  have hU : |((U.filter P).card : ℝ) - (U.card : ℝ)/d * Nat.count P d| ≤ Nat.count P d := by
    rw [hA]
    exact ico_root_error P hd (periodic_roots f d) A T
  change |((S.filter P).card : ℝ) - (S.card : ℝ)/d * Nat.count P d| ≤ _
  rw [← hboth, ← hall, Nat.cast_add, Nat.cast_add, add_div, add_mul]
  calc _ = |(((B.filter P).card : ℝ) - (B.card : ℝ)/d * Nat.count P d) +
            (((U.filter P).card : ℝ) - (U.card : ℝ)/d * Nat.count P d)| := by congr 1; ring
       _ ≤ _ := (abs_add_le ..).trans (add_le_add hE hU)


theorem eventual_sign (g : ℤ[X]) :
    (∀ᶠ n : ℕ in atTop, 0 ≤ g.eval (n : ℤ)) ∨ (∀ᶠ n : ℕ in atTop, g.eval (n : ℤ) < 0) := by
  let p := g.map (Int.castRingHom ℝ)
  have he (n : ℕ) : p.eval (n : ℝ) = (↑(g.eval (n : ℤ)) : ℝ) := by
    simp [p, Polynomial.eval_map]
  by_cases h : 0 < p.degree
  · rcases le_or_gt 0 p.leadingCoeff with hl | hl
    · left
      have hh := ((p.tendsto_atTop_of_leadingCoeff_nonneg h hl).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 0
      filter_upwards [hh] with n hn
      change 0 ≤ p.eval (n : ℝ) at hn
      rw [he] at hn
      exact_mod_cast hn
    · right
      have hh := ((p.tendsto_atBot_of_leadingCoeff_nonpos h hl.le).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_lt_atBot 0
      filter_upwards [hh] with n hn
      change p.eval (n : ℝ) < 0 at hn
      rw [he] at hn
      exact_mod_cast hn
  · have hc := Polynomial.eq_C_of_degree_le_zero (le_of_not_gt h)
    have hh (n : ℕ) : (↑(g.eval (n : ℤ)) : ℝ) = p.coeff 0 := by
      rw [← he, hc, Polynomial.eval_C]
      simp
    rcases le_or_gt 0 (p.coeff 0) with h0 | h0
    · left
      exact Eventually.of_forall fun n ↦ by exact_mod_cast (hh n ▸ h0 : 0 ≤ (↑(g.eval (n : ℤ)) : ℝ))
    · right
      exact Eventually.of_forall fun n ↦ by exact_mod_cast (hh n ▸ h0 : (↑(g.eval (n : ℤ)) : ℝ) < 0)

theorem monotone_tail (f : ℤ[X]) (hpos : ∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) :
    ∃ K : ℕ, Monotone (fun n : ℕ ↦ f.eval ((K+n : ℕ) : ℤ)) := by
  let g := f.comp (X + 1) - f
  have he (n : ℕ) : g.eval (n : ℤ) = f.eval ((n+1 : ℕ) : ℤ) - f.eval (n : ℤ) := by simp [g]
  rcases eventual_sign g with h | h
  · obtain ⟨K, hK⟩ := eventually_atTop.1 h
    refine ⟨K, monotone_nat_of_le_succ (fun n ↦ ?_)⟩
    have hn := hK (K+n) (by omega)
    rw [he] at hn
    simpa [Nat.add_assoc] using sub_nonneg.mp hn
  · have hp := tendsto_natCast_atTop_atTop (R := ℤ) |>.eventually hpos
    obtain ⟨K, hK⟩ := eventually_atTop.1 (h.and hp)
    have bound (n : ℕ) : f.eval ((K+n : ℕ) : ℤ) ≤ f.eval (K : ℤ) - n := by
      induction n with
      | zero => simp
      | succ n ih =>
        have hn := (hK (K+n) (by omega)).1
        rw [he] at hn
        push_cast at ih hn ⊢
        rw [← add_assoc]
        omega
    obtain ⟨i, hi⟩ := exists_nat_gt (f.eval (K : ℤ))
    have hb := bound i
    have hc := (hK (K+i) (by omega)).2
    omega


theorem row_middle_bound (z : ℤ) (N U : ℕ) (hz : ⌊z⌋₊ ≤ U*U) :
    ((⌊z⌋₊.divisorsAntidiagonal).filter (fun p ↦ N < p.1 ∧ N < p.2)).card ≤
    2 * ∑ d ∈ Ioc N U, if (d : ℤ) ∣ z then 1 else 0 := by
  let m := ⌊z⌋₊
  let w (d : ℕ) := if N < d ∧ d ≤ U then 1 else 0
  have hcard : ((m.divisorsAntidiagonal).filter (fun p ↦ N < p.1 ∧ N < p.2)).card ≤
      (∑ d ∈ m.divisors, w d) + ∑ d ∈ m.divisors, w d := by
    rw [Finset.card_filter]
    nth_rw 1 [← Nat.sum_divisorsAntidiagonal (n := m) (fun a _ ↦ w a)]
    rw [← Nat.sum_divisorsAntidiagonal' (n := m) (fun _ b ↦ w b), ← sum_add_distrib]
    apply sum_le_sum
    intro p hp
    have he := (Nat.mem_divisorsAntidiagonal.mp hp).1
    have hsmall : p.1 ≤ U ∨ p.2 ≤ U := by
      by_contra! h
      have hc : (U+1)*(U+1) ≤ p.1*p.2 := Nat.mul_le_mul h.1 h.2
      change m ≤ U*U at hz
      rw [he] at hc
      nlinarith
    dsimp [w]
    split_ifs <;> omega
  have hdiv : (∑ d ∈ m.divisors, w d) ≤ ∑ d ∈ Ioc N U, if (d : ℤ) ∣ z then 1 else 0 := by
    change (∑ d ∈ m.divisors, if N < d ∧ d ≤ U then 1 else 0) ≤ _
    rw [← card_filter, ← card_filter]
    apply card_le_card
    intro d hd
    obtain ⟨hm,hdu⟩ := mem_filter.mp hd
    have hm' := Nat.mem_divisors.mp hm
    refine mem_filter.mpr ⟨mem_Ioc.mpr hdu, ?_⟩
    have hpos : 0 ≤ z := by
      by_contra! hz'
      have : m = 0 := Nat.floor_of_nonpos hz'.le
      exact hm'.2 this
    have hh : (d : ℤ) ∣ (↑m : ℤ) := by exact_mod_cast hm'.1
    simpa [m, Nat.floor_int, Int.toNat_of_nonneg hpos] using hh
  exact hcard.trans (by omega)

/-- Above the input cutoff, each residue class is visited at most once. -/
theorem total_middle_bound (f : ℤ[X]) (N U : ℕ)
    (hsize : ∀ n ≤ N, ⌊f.eval (n : ℤ)⌋₊ ≤ U*U) :
    (∑ n ∈ range (N+1), ((⌊f.eval (n : ℤ)⌋₊.divisorsAntidiagonal).filter
      (fun p ↦ N < p.1 ∧ N < p.2)).card) ≤
    2 * ∑ d ∈ Icc 1 U, Nat.count (fun n : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ)) d := by
  let P (d n : ℕ) := (d : ℤ) ∣ f.eval (n : ℤ)
  calc
    _ ≤ ∑ n ∈ range (N+1), 2 * ∑ d ∈ Ioc N U, if P d n then 1 else 0 := by
      exact sum_le_sum fun n hn ↦ row_middle_bound _ N U (hsize n (by simpa using hn))
    _ = 2 * ∑ d ∈ Ioc N U, ∑ n ∈ range (N+1), if P d n then 1 else 0 := by
      rw [← mul_sum, sum_comm]
    _ ≤ 2 * ∑ d ∈ Ioc N U, Nat.count (P d) d := by
      gcongr with d hd
      rw [← card_filter, ← Nat.count_eq_card_filter_range]
      exact Nat.count_monotone _ (mem_Ioc.mp hd).1
    _ ≤ _ := Nat.mul_le_mul_left _ (sum_le_sum_of_subset_of_nonneg (fun d hd ↦
      mem_Icc.mpr ⟨Nat.zero_lt_of_lt (mem_Ioc.mp hd).1, (mem_Ioc.mp hd).2⟩) (by simp))

/-- A fixed multiple of the input cutoff bounds the smaller factor in degree at most two. -/
theorem quadratic_height (f : ℤ[X]) (hdeg : f.natDegree ≤ 2) :
    ∃ L : ℕ, ∀ N : ℕ, 1 ≤ N → ∀ n ≤ N, ⌊f.eval (n : ℤ)⌋₊ ≤ (L*N)*(L*N) := by
  let A := (f.coeff 0).natAbs + (f.coeff 1).natAbs + (f.coeff 2).natAbs + 1
  refine ⟨A, fun N hN n hn ↦ ?_⟩
  have he := f.eval_eq_sum_range' (n := 3) (by omega) (n : ℤ)
  simp only [sum_range_succ, sum_range_zero, zero_add, pow_zero, pow_one, mul_one] at he
  have hc (j : ℕ) : f.coeff j ≤ (↑(f.coeff j).natAbs : ℤ) := by simpa using le_abs_self (f.coeff j)
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  have hn' : (n : ℤ) ≤ N := by exact_mod_cast hn
  have h1 : (1 : ℤ) ≤ (N : ℤ)^2 := by nlinarith
  have h2 : (n : ℤ) ≤ (N : ℤ)^2 := by nlinarith
  have h3 : (n : ℤ)^2 ≤ (N : ℤ)^2 := by gcongr
  have hb : f.eval (n : ℤ) ≤ (A : ℤ) * (N : ℤ)^2 := by
    rw [he]
    calc _ ≤ (↑(f.coeff 0).natAbs : ℤ)*(N : ℤ)^2 +
             (↑(f.coeff 1).natAbs : ℤ)*(N : ℤ)^2 +
             (↑(f.coeff 2).natAbs : ℤ)*(N : ℤ)^2 := by
           gcongr
           · exact (hc 0).trans (le_mul_of_one_le_right (by positivity) h1)
           · exact hc 1
           · exact hc 2
         _ ≤ _ := by simp only [A, Nat.cast_add, Nat.cast_one]; nlinarith [sq_nonneg (N : ℤ)]
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hh : f.eval (n : ℤ) ≤ ((A*N)*(A*N) : ℕ) := by
    apply hb.trans
    push_cast
    have hAA : (A : ℤ) ≤ (A : ℤ)*(A : ℤ) := le_mul_of_one_le_right (by positivity) (by exact_mod_cast hA)
    nlinarith [mul_le_mul_of_nonneg_right hAA (sq_nonneg (N : ℤ))]
  exact (Nat.floor_mono hh).trans_eq (Nat.floor_natCast _)

/-- Assign the smaller factor to the short sum, with different endpoints for the two orientations. -/
theorem integer_row (z : ℤ) (N : ℕ) :
    σ 0 ⌊z⌋₊ =
      (∑ i ∈ range 2, ∑ d ∈ Icc 1 N,
        if (d : ℤ) ∣ z ∧ (d : ℤ)*d+i ≤ z then 1 else 0) +
      (⌊z⌋₊.divisorsAntidiagonal.filter (fun p ↦ N < p.1 ∧ N < p.2)).card := by
  have hw (b : Bool) :
      (∑ d ∈ ⌊z⌋₊.divisors, if d ≤ N ∧ (if b then d*d < ⌊z⌋₊ else d*d ≤ ⌊z⌋₊) then 1 else 0) =
      ∑ d ∈ Icc 1 N, if (d : ℤ) ∣ z ∧ (if b then (d : ℤ)*d < z else (d : ℤ)*d ≤ z) then 1 else 0 := by
    rw [weighted_short]
    exact sum_congr rfl fun d hd ↦ if_congr (floor_test z (mem_Icc.mp hd).1 b) rfl rfl
  have h0 := hw false
  have h1 := hw true
  simp only [Bool.false_eq_true, if_false, if_true] at h0 h1
  rw [pair_identity, h0, h1]
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.cast_zero, add_zero, Nat.cast_one,
    Int.add_one_le_iff]

/-- Total error when each short-modulus count is replaced by interval length times root density. -/
theorem finite_estimate (f : ℤ[X]) {K : ℕ}
    (hK : Monotone (fun n : ℕ ↦ f.eval ((K+n : ℕ) : ℤ))) (x : ℝ) :
    let N := ⌊x⌋₊
    let P := fun (d n : ℕ) ↦ (d : ℤ) ∣ f.eval (n : ℤ)
    let S := fun (i d : ℕ) ↦ (range (N+1)).filter (fun n : ℕ ↦ (d : ℤ)*d+i ≤ f.eval (n : ℤ))
    let M := ∑ i ∈ range 2, ∑ d ∈ Icc 1 N, ((S i d).card : ℝ)/d * Nat.count (P d) d
    let B := ∑ n ∈ range (N+1), (((⌊f.eval (n : ℤ)⌋₊).divisorsAntidiagonal.filter
      (fun p ↦ N < p.1 ∧ N < p.2)).card : ℝ)
    |Erdos975.Erdos975Sum f x - (M+B)| ≤
      2 * ((N : ℝ)*K + ∑ d ∈ Icc 1 N, (Nat.count (P d) d : ℝ)) := by
  intro N P S M B
  let A (i d : ℕ) := (((S i d).filter (P d)).card : ℝ)
  have hcount (i d : ℕ) : A i d =
      ∑ n ∈ range (N+1), if P d n ∧ (d : ℤ)*d+i ≤ f.eval (n : ℤ) then (1 : ℝ) else 0 := by
    simp only [A,S,filter_filter,card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact sum_congr rfl fun n _ ↦ if_congr and_comm rfl rfl
  have hsum : Erdos975.Erdos975Sum f x = (∑ i ∈ range 2, ∑ d ∈ Icc 1 N, A i d) + B := by
    simp_rw [hcount]
    simp_rw [sum_comm (s := Icc 1 N) (t := range (N+1))]
    rw [sum_comm (s := range 2) (t := range (N+1))]
    unfold B
    rw [← sum_add_distrib]
    change (∑ n ∈ Iic N, (σ 0 ⌊f.eval (n : ℤ)⌋₊ : ℝ)) = _
    rw [← Nat.range_succ_eq_Iic]
    apply sum_congr rfl
    intro n _
    have h := congrArg (Nat.cast : ℕ → ℝ) (integer_row (f.eval (n : ℤ)) N)
    push_cast at h
    simpa [P] using h
  rw [hsum, add_sub_add_right_eq_sub, show M = _ from rfl, ← sum_sub_distrib]
  calc _ ≤ ∑ i ∈ range 2, |(∑ d ∈ Icc 1 N, A i d) -
         ∑ d ∈ Icc 1 N, ((S i d).card : ℝ)/d * Nat.count (P d) d| := Finset.abs_sum_le_sum_abs ..
       _ ≤ ∑ _i ∈ range 2, ∑ d ∈ Icc 1 N, ((K : ℝ) + Nat.count (P d) d) := by
         apply sum_le_sum
         intro i _
         rw [← sum_sub_distrib]
         exact (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum fun d hd ↦
           threshold_error f hK (N+1) ((d : ℤ)*d+i) (mem_Icc.mp hd).1)
       _ = _ := by simp [sum_add_distrib, nsmul_eq_mul]; ring

/-- A linear upper bound for the number of residue roots, summed over the moduli. -/
def H1 : Prop :=
  ∀ f : ℤ[X], f.natDegree ≠ 0 → Irreducible f →
    ∃ C ≥ (0 : ℝ), ∀ N : ℕ,
      (∑ d ∈ Icc 1 N, (Nat.count (fun n : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ)) d : ℝ)) ≤ C*N

/-- Short-divisor density model. Only superlevel-set lengths and roots in a *full*
period occur. The two thresholds give diagonal factorizations weight one. -/
def H2 : Prop :=
  ∀ f : ℤ[X], f.natDegree ≠ 0 → Irreducible f → (∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) →
    let rho := fun d : ℕ ↦ Nat.count (fun n : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ)) d
    let length := fun (N i d : ℕ) ↦ ((range (N+1)).filter
      (fun n : ℕ ↦ (d : ℤ)*d+i ≤ f.eval (n : ℤ))).card
    ∃ a > (0 : ℝ), Tendsto (fun N : ℕ ↦
      (∑ i ∈ range 2, ∑ d ∈ Icc 1 N, (length N i d : ℝ)/d * rho d) / ((N : ℝ)*log N))
      atTop (𝓝 a)

/-- For degree at least three, only ordered pairs with both factors strictly larger than the input cutoff. -/
def H3 : Prop :=
  ∀ f : ℤ[X], 2 < f.natDegree → Irreducible f → (∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) →
    ∃ b : ℝ, Tendsto (fun N : ℕ ↦
      (∑ n ∈ range (N+1), (((⌊f.eval (n : ℤ)⌋₊).divisorsAntidiagonal.filter
        (fun p ↦ N < p.1 ∧ N < p.2)).card : ℝ)) / ((N : ℝ)*log N)) atTop (𝓝 b)

/-- Transfer a count at integer endpoints to the real normalization in the original statement. -/
theorem floor_transfer {F : ℕ → ℝ} {c : ℝ}
    (hc : Tendsto (fun N : ℕ ↦ F N / ((N : ℝ)*log N)) atTop (𝓝 c)) :
    Tendsto (fun x : ℝ ↦ F ⌊x⌋₊ / (x*log x)) atTop (𝓝 c) := by
  have hratio : Tendsto (fun x : ℝ ↦ (⌊x⌋₊ : ℝ)/x) atTop (𝓝 1) := tendsto_nat_floor_div_atTop
  have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
  have hdiff := hlog.div_atTop Real.tendsto_log_atTop
  have hlogRatio : Tendsto (fun x : ℝ ↦ log ⌊x⌋₊ / log x) atTop (𝓝 1) := by
    have ht := hdiff.add (tendsto_const_nhds (x := (1 : ℝ)))
    rw [zero_add] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
    have hfloor : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
    change log ((⌊x⌋₊ : ℝ) / x) / log x + 1 = _
    rw [Real.log_div (by positivity) (by linarith)]
    field_simp [(Real.log_pos (by linarith : 1 < x)).ne']
    ring
  have ht := (hc.comp tendsto_nat_floor_atTop).mul (hratio.mul hlogRatio)
  rw [one_mul, mul_one] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (3 : ℝ)] with x hx
  have hf : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hfn : 1 < (⌊x⌋₊ : ℝ) := by exact_mod_cast (show 1 < ⌊x⌋₊ by omega)
  change F ⌊x⌋₊ / ((⌊x⌋₊ : ℝ)*log ⌊x⌋₊) *
    (((⌊x⌋₊ : ℝ)/x)*(log ⌊x⌋₊ / log x)) = _
  field_simp [(Real.log_pos hfn).ne', (by linarith : (⌊x⌋₊ : ℝ) ≠ 0)]

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @Erdos975.erdos_975 := by
  intro hr hm hb f hdeg hirr hp
  obtain ⟨C, hC, hroot⟩ := hr f hdeg hirr
  obtain ⟨a, ha, hmodel⟩ := hm f hdeg hirr hp
  obtain ⟨K, hK⟩ := monotone_tail f hp
  let rho (d : ℕ) := Nat.count (fun n : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ)) d
  let M (N : ℕ) := ∑ i ∈ range 2, ∑ d ∈ Icc 1 N,
    (((range (N+1)).filter (fun n : ℕ ↦ (d : ℤ)*d+i ≤ f.eval (n : ℤ))).card : ℝ)/d * rho d
  let B (N : ℕ) := ∑ n ∈ range (N+1), (((⌊f.eval (n : ℤ)⌋₊).divisorsAntidiagonal.filter
      (fun p ↦ N < p.1 ∧ N < p.2)).card : ℝ)
  let D (x : ℝ) := x * log x
  change Tendsto (fun N : ℕ ↦ M N / D N) atTop (𝓝 a) at hmodel
  have midlimit : ∃ b : ℝ, Tendsto (fun N : ℕ ↦ B N / D N) atTop (𝓝 b) := by
    by_cases h : 2 < f.natDegree
    · exact hb f h hirr hp
    obtain ⟨L, hL⟩ := quadratic_height f (by omega)
    refine ⟨0, ?_⟩
    apply squeeze_zero_norm' (a := fun N : ℕ ↦ 2*C*L/log N)
    · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
      have hN' : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
      have hl : 0 < log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
      have hB0 : 0 ≤ B N := Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)
      have hden : 0 < D N := mul_pos hN' hl
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hB0 hden.le)]
      have hn := total_middle_bound f N (L*N) (hL N (by omega))
      have hr' := hroot (L*N)
      have hbc : B N ≤ 2*(∑ d ∈ Icc 1 (L*N), (rho d : ℝ)) := by
        unfold B rho
        exact_mod_cast hn
      have hbN : B N ≤ (2*C*L)*N := by
        calc B N ≤ _ := hbc
             _ ≤ 2*(C*(L*N : ℕ)) := by gcongr
             _ = _ := by push_cast; ring
      calc B N / D N ≤ (2*C*L*N)/D N := div_le_div_of_nonneg_right hbN hden.le
           _ = _ := by dsimp [D]; field_simp
    · exact (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop _
  obtain ⟨b, hmiddle⟩ := midlimit
  have hbn : 0 ≤ b := ge_of_tendsto hmiddle (by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    have hl : 0 ≤ log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    change 0 ≤ B N / D N
    exact div_nonneg (Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)) (mul_nonneg (by positivity) hl))
  refine ⟨a+b, add_pos_of_pos_of_nonneg ha hbn, ?_⟩
  have bound (x : ℝ) (hx : 1 < x) :
      |(Erdos975.Erdos975Sum f x - (M ⌊x⌋₊ + B ⌊x⌋₊)) / D x| ≤ 2*(K+C)/log x := by
    have hfin := finite_estimate f hK x
    change |Erdos975.Erdos975Sum f x - (M ⌊x⌋₊ + B ⌊x⌋₊)| ≤ _ at hfin
    have hf := Nat.floor_le (show 0 ≤ x by linarith)
    have hC' := hroot ⌊x⌋₊
    have hbound : |Erdos975.Erdos975Sum f x - (M ⌊x⌋₊ + B ⌊x⌋₊)| ≤ 2*(K+C)*x := by
      calc _ ≤ _ := hfin
           _ ≤ 2*((⌊x⌋₊ : ℝ)*K+C*⌊x⌋₊) := by gcongr
           _ = 2*(K+C)*(⌊x⌋₊ : ℝ) := by ring
           _ ≤ _ := mul_le_mul_of_nonneg_left hf (by positivity)
    have hD : 0 < D x := mul_pos (by linarith) (Real.log_pos hx)
    rw [abs_div, abs_of_pos hD]
    calc _ ≤ (2*(K+C)*x)/D x := div_le_div_of_nonneg_right hbound hD.le
         _ = _ := by dsimp [D]; field_simp
  have herr : Tendsto (fun x : ℝ ↦ (Erdos975.Erdos975Sum f x - (M ⌊x⌋₊ + B ⌊x⌋₊))/D x)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm'
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact bound x hx
    · exact Real.tendsto_log_atTop.const_div_atTop _
  have ht := ((floor_transfer hmodel).add (floor_transfer hmiddle)).add herr
  rw [add_zero] at ht
  apply ht.congr
  intro x
  dsimp [D]
  ring


end OMA.R_Erdos975_erdos_975_R1
