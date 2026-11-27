import FormalConjectures.ErdosProblems.«604»

/-! # Reducing the pinned grid bound to two estimates for sums of two squares

The grid argument is finite. The remaining estimates concern reciprocal sums
and logarithmically weighted sums of integers with even valuations at inert primes.
Credit: @JaviSoto. -/

namespace OMA.R_Erdos604_erdos_604_variants_grid_upper_bound_R1

open Filter
open scoped BigOperators

/-- The reciprocal sum over numbers whose inert prime exponents are even. The term at zero
is zero by the convention for the reciprocal in ℝ. -/
def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
    (∑ m ∈ ((Finset.range (N + 1)).filter fun m =>
      ∀ q ∈ m.primeFactors, q % 4 = 3 → Even (padicValNat q m)), (m : ℝ)⁻¹) ≤
      C * Real.sqrt (Real.log N)

/-- Chebyshev's weighted counting estimate on the same multiplicative set. -/
def H2 : Prop :=
  ∃ D : ℝ, 0 < D ∧ ∀ᶠ N : ℕ in atTop,
    let S := ((Finset.range (N + 1)).filter fun m =>
      ∀ q ∈ m.primeFactors, q % 4 = 3 → Even (padicValNat q m))
    (∑ m ∈ S, Real.log m) ≤ D * N * ∑ m ∈ S, (m : ℝ)⁻¹

open Asymptotics

/-- Separate the integers at √N. Above the cutoff each term contributes at least log(N)/2. -/
private lemma count_from_log_sum (S : Finset ℕ) {N : ℕ} (hN : 2 ≤ N) :
    (S.card : ℝ) ≤ (Nat.sqrt N + 1 : ℕ) +
      2 * (∑ m ∈ S, Real.log m) / Real.log N := by
  let small := S.filter fun m => m ≤ Nat.sqrt N
  let large := S.filter fun m => ¬ m ≤ Nat.sqrt N
  have hsplit : small.card + large.card = S.card :=
    Finset.card_filter_add_card_filter_not _
  have hs : small.card ≤ Nat.sqrt N + 1 := by
    rw [← Finset.card_range (Nat.sqrt N + 1)]
    apply Finset.card_le_card
    intro m hm
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hm).2)
  have hl : (large.card : ℝ) * Real.log N ≤ 2 * ∑ m ∈ S, Real.log m := calc
    _ = ∑ _m ∈ large, Real.log N := by simp
    _ ≤ ∑ m ∈ large, 2 * Real.log m := by
      apply Finset.sum_le_sum
      intro m hm
      have hsq := Nat.sqrt_lt.mp (lt_of_not_ge (Finset.mem_filter.mp hm).2)
      have hreal : (N : ℝ) ≤ (m : ℝ) ^ 2 := by
        exact_mod_cast (show N ≤ m ^ 2 by simpa [sq] using hsq.le)
      have hnpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
      simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hnpos hreal
    _ = 2 * ∑ m ∈ large, Real.log m := (Finset.mul_sum ..).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ =>
        Real.log_natCast_nonneg i
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hl' := (le_div_iff₀ hlog).mpr hl
  rw [← hsplit, Nat.cast_add]
  exact add_le_add (by exact_mod_cast hs) hl'

/-- The two estimates for the multiplicative set imply the required counting bound. -/
private lemma count_asymptotic (harmonic : H1) (weighted : H2) :
    (fun N : ℕ => (((Finset.range (N + 1)).filter fun m =>
      ∀ q ∈ m.primeFactors, q % 4 = 3 → Even (padicValNat q m)).card : ℝ)) =O[atTop]
      (fun N : ℕ => (N : ℝ) / (Real.log N).sqrt) := by
  obtain ⟨C, hC, hh⟩ := harmonic
  obtain ⟨D, hD, hw⟩ := weighted
  refine Asymptotics.isBigO_iff.mpr ⟨2 + 2 * D * C, ?_⟩
  filter_upwards [hh, hw, eventually_ge_atTop 2] with N hH hW hN
  let S := ((Finset.range (N + 1)).filter fun m =>
      ∀ q ∈ m.primeFactors, q % 4 = 3 → Even (padicValNat q m))
  change (∑ m ∈ S, Real.log m) ≤ D * N * ∑ m ∈ S, (m : ℝ)⁻¹ at hW
  change (∑ m ∈ S, (m : ℝ)⁻¹) ≤ C * (Real.log N).sqrt at hH
  have hn : 1 < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hn' : (0 : ℝ) ≤ N := by positivity
  have hlog := Real.log_pos hn
  have hroot := Real.sqrt_pos.2 hlog
  have hroot2 := Real.sq_sqrt hlog.le
  have hW' : (∑ m ∈ S, Real.log m) ≤ (D * N) * (C * (Real.log N).sqrt) :=
    hW.trans (mul_le_mul_of_nonneg_left hH (by positivity))
  have hsmall : ((Nat.sqrt N + 1 : ℕ) : ℝ) * (Real.log N).sqrt ≤ 2 * N := by
    have hlogN : (Real.log N).sqrt ≤ Real.sqrt N :=
      Real.sqrt_le_sqrt (Real.log_le_self hn')
    have hOne : 1 ≤ Real.sqrt N := by simpa using Real.sqrt_le_sqrt hn.le
    calc
      _ ≤ (Real.sqrt N + Real.sqrt N) * Real.sqrt N := by
        push_cast
        exact mul_le_mul (add_le_add Real.nat_sqrt_le_real_sqrt hOne) hlogN
          hroot.le (by positivity)
      _ = _ := by nlinarith [Real.sq_sqrt hn']
  have hlarge : (2 * (∑ m ∈ S, Real.log m) / Real.log N) * (Real.log N).sqrt
        ≤ 2 * D * C * N := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hlog]
    calc
      _ ≤ (2 * ((D * N) * (C * (Real.log N).sqrt))) * (Real.log N).sqrt := by gcongr
      _ = _ := by linear_combination 2 * D * C * (N : ℝ) * hroot2
  simp only [Real.norm_eq_abs, Nat.abs_cast, abs_of_nonneg (div_nonneg hn' hroot.le)]
  rw [← mul_div_assoc, le_div_iff₀ hroot]
  calc
    (S.card : ℝ) * _ ≤ _ :=
      mul_le_mul_of_nonneg_right (count_from_log_sum S hN) hroot.le
    _ ≤ _ := by rw [add_mul]; linarith

/-- Passing from the number of points to the range of squared distances changes only the constant. -/
private lemma grid604AsymptoticTransfer (P count : ℕ → ℕ)
    (hgrid : ∀ n : ℕ, P n ≤ count (2 * (n.sqrt + 1)^2))
    (hcount : (fun x : ℕ => (count x : ℝ)) =O[atTop]
      (fun x : ℕ => (x : ℝ) / (x : ℝ).log.sqrt)) :
    (fun n : ℕ => (P n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) / (n : ℝ).log.sqrt) := by
  obtain ⟨C, hC, h⟩ := hcount.exists_nonneg
  obtain ⟨N, hN⟩ := eventually_atTop.1 h.bound
  apply IsBigO.of_bound (C * 8)
  filter_upwards [eventually_ge_atTop (max 2 N)] with n hn
  let m := 2 * (n.sqrt + 1)^2
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hnm : n ≤ m := by
    have hside : n < (n.sqrt + 1)^2 := Nat.lt_succ_sqrt' n
    dsimp [m]
    omega
  have hs : 1 ≤ n.sqrt := Nat.le_sqrt.mpr (by omega)
  have hm8 : m ≤ 8 * n := by
    dsimp [m]
    calc
      2 * (n.sqrt + 1)^2 ≤ 2 * (2 * n.sqrt)^2 := by gcongr; omega
      _ = 8 * n.sqrt^2 := by ring
      _ ≤ 8 * n := by gcongr; exact Nat.sqrt_le' n
  have hmcount := hN m (((le_max_right _ _).trans hn).trans hnm)
  have hnpos : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hlogpos : 0 < (n : ℝ).log.sqrt := Real.sqrt_pos.2 (Real.log_pos hnpos)
  have hlogle : (n : ℝ).log.sqrt ≤ (m : ℝ).log.sqrt :=
    Real.sqrt_le_sqrt (Real.log_le_log (by positivity) (by exact_mod_cast hnm))
  simp only [Real.norm_eq_abs, Nat.abs_cast,
    abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))] at hmcount ⊢
  calc
    (P n : ℝ) ≤ count m := by exact_mod_cast hgrid n
    _ ≤ C * ((m : ℝ) / (m : ℝ).log.sqrt) := hmcount
    _ ≤ C * ((8 * (n : ℝ)) / (n : ℝ).log.sqrt) := by
      apply mul_le_mul_of_nonneg_left _ hC
      calc
        (m : ℝ) / (m : ℝ).log.sqrt ≤ (m : ℝ) / (n : ℝ).log.sqrt :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg _) hlogpos hlogle
        _ ≤ (8 * (n : ℝ)) / (n : ℝ).log.sqrt := by gcongr; exact_mod_cast hm8
    _ = (C * 8) * ((n : ℝ) / (n : ℝ).log.sqrt) := by ring

open scoped EuclideanGeometry Classical

private lemma nat_dist_cast_abs (a b : ℕ) : (Nat.dist a b : ℝ) = |(a : ℝ) - b| := by
  rcases le_total a b with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    ring
  · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]

/-- Choose any n points of an m by m grid. Each squared distance is a sum of two squares. -/
private lemma pinned_le_square_count (n m : ℕ) (hn : n ≤ m * m) :
    Erdos604.pinnedDistinctDistances n ≤
      ((Finset.range (2 * m ^ 2 + 1)).filter (fun t => ∃ a b : ℕ, t = a ^ 2 + b ^ 2)).card := by
  classical
  let pt (i : Fin m × Fin m) : ℝ² := !₂[(i.1.val : ℝ), (i.2.val : ℝ)]
  have hinj : Function.Injective pt := by
    intro i j h
    have h0 := congrArg (fun v : ℝ² => v 0) h
    have h1 := congrArg (fun v : ℝ² => v 1) h
    apply Prod.ext <;> apply Fin.ext
    · exact_mod_cast (show (i.1.val : ℝ) = j.1.val by simpa [pt] using h0)
    · exact_mod_cast (show (i.2.val : ℝ) = j.2.val by simpa [pt] using h1)
  let grid := Finset.univ.image pt
  have hcard : grid.card = m * m := by simp [grid, Finset.card_image_of_injective _ hinj]
  obtain ⟨A, hA, hAn⟩ := Finset.exists_subset_card_eq (s := grid) (n := n) (hcard ▸ hn)
  let T := (Finset.range (2 * m ^ 2 + 1)).filter (fun t => ∃ a b : ℕ, t = a ^ 2 + b ^ 2)
  have hdist (i j : Fin m × Fin m) :
      dist (pt i) (pt j) = Real.sqrt ((Nat.dist i.1.val j.1.val ^ 2 + Nat.dist i.2.val j.2.val ^ 2 : ℕ) : ℝ) := by
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
    simp [pt, Real.dist_eq, nat_dist_cast_abs]
  unfold Erdos604.pinnedDistinctDistances
  apply le_trans (Nat.sInf_le (show A.sup (distinctDistancesFrom A) ∈
    {v : ℕ | ∃ a : Finset ℝ², a.card = n ∧ a.sup (distinctDistancesFrom a) = v} from
    ⟨A, hAn, rfl⟩))
  apply Finset.sup_le
  intro q hq
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (hA hq)
  unfold distinctDistancesFrom
  refine le_trans (Finset.card_le_card (t := T.image (fun t : ℕ => Real.sqrt (t : ℝ))) ?_) Finset.card_image_le
  rintro d hd
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
  have hpA : p ∈ A := @Finset.mem_of_mem_erase _ (fun _ _ => Classical.propDecidable _) _ _ _ hp
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hA hpA)
  let a := Nat.dist i.1.val j.1.val
  let b := Nat.dist i.2.val j.2.val
  have ha : a ≤ m := by
    have := i.1.isLt
    have := j.1.isLt
    dsimp [a, Nat.dist]
    omega
  have hb : b ≤ m := by
    have := i.2.isLt
    have := j.2.isLt
    dsimp [b, Nat.dist]
    omega
  have hbound : a ^ 2 + b ^ 2 < 2 * m ^ 2 + 1 := by
    nlinarith [Nat.pow_le_pow_left ha 2, Nat.pow_le_pow_left hb 2]
  refine Finset.mem_image.mpr ⟨a ^ 2 + b ^ 2, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr hbound, a, b, rfl⟩, ?_⟩
  rw [← hi, ← hj]
  exact (hdist i j).symm

theorem main : H1 → H2 → type_of% @Erdos604.erdos_604.variants.grid_upper_bound := by
  intro harmonic weighted
  apply grid604AsymptoticTransfer _ _ _ (count_asymptotic harmonic weighted)
  intro n
  have hside : n ≤ (n.sqrt + 1) * (n.sqrt + 1) := (Nat.lt_succ_sqrt n).le
  apply (pinned_le_square_count n (n.sqrt + 1) hside).trans
  apply Finset.card_le_card
  intro t ht
  obtain ⟨hr, hsq⟩ := Finset.mem_filter.mp ht
  exact Finset.mem_filter.mpr ⟨hr, Nat.eq_sq_add_sq_iff.mp hsq⟩

end OMA.R_Erdos604_erdos_604_variants_grid_upper_bound_R1
