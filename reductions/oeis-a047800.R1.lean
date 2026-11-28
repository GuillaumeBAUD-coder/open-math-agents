import OMAStatements.S_oeis_a047800

/-!
# A047800 reduced to a disk count and fixed-sector coverage

H1 is Landau's counting asymptotic, with zero included.
H2 is the relative density zero of norms missed by each fixed diagonal sector.
For fixed 0 < t < 2, a norm m ≤ t n² represented in that sector has both
coordinates at most n. The lower bound from these norms approaches the disk
upper bound at cutoff 2 n² as t tends to 2.
-/

namespace OMA.R_oeis_a047800_R1

open Filter Topology

/-- Landau's counting asymptotic for distinct sums of two squares up to x. -/
def H1 : Prop := by
  classical
  exact
    let diskAt : ℝ → Finset ℕ := fun x =>
      (Finset.range (⌊x⌋₊ + 1)).filter fun m => ∃ i j : ℕ, i ^ 2 + j ^ 2 = m
    ∃ K : ℝ, 0 < K ∧
      Tendsto (fun x : ℝ => ((diskAt x).card : ℝ) * Real.sqrt (Real.log x) / x)
        atTop (𝓝 K)

/-- For each fixed diagonal sector, the fraction of norms it misses tends to zero. -/
def H2 : Prop := by
  classical
  exact
    let diskAt : ℝ → Finset ℕ := fun x =>
      (Finset.range (⌊x⌋₊ + 1)).filter fun m => ∃ i j : ℕ, i ^ 2 + j ^ 2 = m
    ∀ t : ℝ, 0 < t → t < 2 →
      Tendsto (fun x : ℝ =>
        (((diskAt x).filter fun m =>
          ¬ ∃ i j : ℕ, i ^ 2 + j ^ 2 = m ∧
            t * (i : ℝ) ^ 2 ≤ m ∧ t * (j : ℝ) ^ 2 ≤ m).card : ℝ) / (diskAt x).card)
        atTop (𝓝 0)

section

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a047800.main := by
  classical
  intro hCount hsector
  let sums (n : ℕ) : Finset ℕ :=
    ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).image fun p => p.1 ^ 2 + p.2 ^ 2)
  let diskAt (x : ℝ) : Finset ℕ :=
    (Finset.range (⌊x⌋₊ + 1)).filter fun m => ∃ i j : ℕ, i ^ 2 + j ^ 2 = m
  let nearDiagonal (t : ℝ) (m : ℕ) : Prop :=
    ∃ i j : ℕ, i ^ 2 + j ^ 2 = m ∧
      t * (i : ℝ) ^ 2 ≤ m ∧ t * (j : ℝ) ^ 2 ≤ m
  let sector (t x : ℝ) : Finset ℕ := (diskAt x).filter (nearDiagonal t)
  let exceptions (t x : ℝ) : Finset ℕ := (diskAt x).filter fun m => ¬ nearDiagonal t m
  let weight (n : ℕ) : ℝ := Real.sqrt (Real.log n) / (n : ℝ) ^ 2
  let cutoff (t : ℝ) (n : ℕ) : ℝ := t * (n : ℝ) ^ 2
  have mem_sums {n m : ℕ} :
      m ∈ sums n ↔ ∃ i ≤ n, ∃ j ≤ n, i ^ 2 + j ^ 2 = m := by
    simp only [sums, Finset.mem_image, Finset.mem_product, Finset.mem_range]
    constructor
    · rintro ⟨⟨i, j⟩, ⟨hi, hj⟩, h⟩
      exact ⟨i, by omega, j, by omega, h⟩
    · rintro ⟨i, hi, j, hj, h⟩
      exact ⟨(i, j), ⟨by omega, by omega⟩, h⟩
  have cutoff_tendsto {t : ℝ} (ht : 0 < t) : Tendsto (cutoff t) atTop atTop :=
    ((tendsto_pow_atTop (n := 2) (by decide)).comp tendsto_natCast_atTop_atTop).const_mul_atTop ht
  have sector_subset_sums {t : ℝ} (ht : 0 < t) (n : ℕ) :
      sector t (cutoff t n) ⊆ sums n := by
    classical
    intro m hm
    have h := Finset.mem_filter.mp hm
    rcases h.2 with ⟨i, j, hij, hi, hj⟩
    have hcut : 0 ≤ cutoff t n := mul_nonneg ht.le (sq_nonneg _)
    have hm' := (Nat.le_floor_iff hcut).mp (Finset.mem_range.mp (Finset.mem_filter.mp h.1).1 |> Nat.le_of_lt_succ)
    have hi' : (i : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := le_of_mul_le_mul_left (hi.trans hm') ht
    have hj' : (j : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := le_of_mul_le_mul_left (hj.trans hm') ht
    apply mem_sums.mpr
    refine ⟨i, ?_, j, ?_, hij⟩
    · exact_mod_cast le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) (Nat.cast_nonneg n) hi'
    · exact_mod_cast le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) (Nat.cast_nonneg n) hj'

  have sums_subset_diskAt (n : ℕ) : sums n ⊆ diskAt (cutoff 2 n) := by
    intro m hm
    rcases mem_sums.mp hm with ⟨i, hi, j, hj, hij⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor ?_)), i, j, hij⟩
    dsimp only [cutoff]
    have hi2 := Nat.mul_le_mul hi hi
    have hj2 := Nat.mul_le_mul hj hj
    have hm₂ : m ≤ 2 * n ^ 2 := by nlinarith
    exact_mod_cast hm₂

  have disk_limit {K t : ℝ} (h : Tendsto (fun x : ℝ => ((diskAt x).card : ℝ) * Real.sqrt (Real.log x) / x)
      atTop (𝓝 K)) (ht : 0 < t) :
      Tendsto (fun n : ℕ => ((diskAt (cutoff t n)).card : ℝ) * weight n)
        atTop (𝓝 (K * (t / Real.sqrt 2))) := by
    have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hratio : Tendsto (fun n : ℕ => Real.log (cutoff t n) / Real.log n)
        atTop (𝓝 2) := by
      have hc' : Tendsto (fun n : ℕ => Real.log t / Real.log n) atTop (𝓝 0) :=
        by simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hlog).const_mul (Real.log t)
      have hadd := hc'.add_const (2 : ℝ)
      rw [zero_add] at hadd
      apply hadd.congr'
      filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
      have hn' : 1 < (n : ℝ) := by exact_mod_cast hn
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      have hl0 : Real.log (n : ℝ) ≠ 0 := (Real.log_pos hn').ne'
      dsimp only [cutoff]
      rw [Real.log_mul ht.ne' (pow_ne_zero _ hn0), Real.log_pow]
      field_simp
      norm_num
    have hfactor : Tendsto (fun n : ℕ => t / Real.sqrt (Real.log (cutoff t n) / Real.log n))
        atTop (𝓝 (t / Real.sqrt 2)) :=
      tendsto_const_nhds.div (Real.continuous_sqrt.continuousAt.tendsto.comp hratio)
        (by positivity)
    have hcomp := (show Tendsto _ atTop (𝓝 K) from h).comp (cutoff_tendsto ht)
    apply (hcomp.mul hfactor).congr'
    filter_upwards [hlog.eventually (eventually_gt_atTop (0 : ℝ)),
      (Real.tendsto_log_atTop.comp (cutoff_tendsto ht)).eventually
        (eventually_gt_atTop (0 : ℝ))] with n hn hx
    have hn0 : (n : ℝ) ≠ 0 := by
      intro hz
      simp [hz] at hn
    have hs : Real.sqrt (Real.log (cutoff t n)) ≠ 0 := (Real.sqrt_pos.2 hx).ne'
    have hsn : Real.sqrt (Real.log (n : ℝ)) ≠ 0 := (Real.sqrt_pos.2 hn).ne'
    change 0 < Real.log (cutoff t n) at hx
    change _ * Real.sqrt (Real.log (cutoff t n)) / cutoff t n * _ = _
    rw [Real.sqrt_div hx.le]
    dsimp only [weight, cutoff]
    dsimp only [cutoff] at hs
    field_simp

  have sector_limit {K t : ℝ} (h : Tendsto (fun x : ℝ => ((diskAt x).card : ℝ) * Real.sqrt (Real.log x) / x)
      atTop (𝓝 K))
      (hsector : H2) (ht : 0 < t) (ht₂ : t < 2) :
      Tendsto (fun n : ℕ => ((sector t (cutoff t n)).card : ℝ) * weight n)
        atTop (𝓝 (K * (t / Real.sqrt 2))) := by
    have hd := disk_limit h ht
    have he : Tendsto (fun n : ℕ => ((exceptions t (cutoff t n)).card : ℝ) /
        (diskAt (cutoff t n)).card) atTop (𝓝 0) :=
      (hsector t ht ht₂).comp (cutoff_tendsto ht)
    have H := (tendsto_const_nhds.sub he : Tendsto _ _ (𝓝 ((1 : ℝ) - 0))).mul hd
    rw [sub_zero, one_mul] at H
    apply H.congr'
    exact Eventually.of_forall fun n => by
      have hdpos : 0 < (diskAt (cutoff t n)).card :=
        Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.zero_lt_succ _),
          0, 0, by decide⟩⟩
      have hdne : ((diskAt (cutoff t n)).card : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
      have hc : (sector t (cutoff t n)).card + (exceptions t (cutoff t n)).card =
          (diskAt (cutoff t n)).card :=
        Finset.card_filter_add_card_filter_not (s := diskAt (cutoff t n)) (nearDiagonal t)
      rw [Nat.add_comm] at hc
      have hcast : ((exceptions t (cutoff t n)).card : ℝ) + (sector t (cutoff t n)).card =
          (diskAt (cutoff t n)).card := by exact_mod_cast hc
      change (1 - ((exceptions t (cutoff t n)).card : ℝ) / (diskAt (cutoff t n)).card) *
          (((diskAt (cutoff t n)).card : ℝ) * weight n) = _
      field_simp
      linear_combination weight n * hcast.symm
  obtain ⟨K, hK, h⟩ := hCount
  refine ⟨Real.sqrt 2 * K, by positivity, ?_⟩
  let L : ℝ := K * (2 / Real.sqrt 2)
  have hL : 0 < L := by dsimp [L]; positivity
  have hw (n : ℕ) : 0 ≤ weight n := by dsimp [weight]; positivity
  have hb : Tendsto (fun n : ℕ => (OMA.S_oeis_a047800.a n : ℝ) * weight n) atTop (𝓝 L) := by
    apply tendsto_order.mpr
    constructor
    · intro y hy
      let t : ℝ := 2 * ((max y 0 + L) / 2) / L
      have hmax : max y 0 < L := max_lt hy hL
      have ht : 0 < t := by dsimp [t]; positivity
      have ht₂ : t < 2 := by
        dsimp [t]
        apply (div_lt_iff₀ hL).mpr
        linarith
      have htval : K * (t / Real.sqrt 2) = (max y 0 + L) / 2 := by
        calc
          K * (t / Real.sqrt 2) = L * t / 2 := by dsimp [L]; ring
          _ = (max y 0 + L) / 2 := by dsimp [t]; field_simp
      have hy' : y < K * (t / Real.sqrt 2) := by
        rw [htval]
        linarith [le_max_left y 0]
      filter_upwards [(tendsto_order.mp (sector_limit h hsector ht ht₂)).1 y hy'] with n hn
      have hcard : ((sector t (cutoff t n)).card : ℝ) ≤ OMA.S_oeis_a047800.a n := by
        change ((sector t (cutoff t n)).card : ℝ) ≤ (sums n).card
        exact_mod_cast Finset.card_le_card (sector_subset_sums ht n)
      exact hn.trans_le (mul_le_mul_of_nonneg_right hcard (hw n))
    · intro y hy
      filter_upwards [(tendsto_order.mp (disk_limit h (by norm_num : 0 < (2 : ℝ)))).2 y hy]
        with n hn
      have hcard : (OMA.S_oeis_a047800.a n : ℝ) ≤ (diskAt (cutoff 2 n)).card := by
        change ((sums n).card : ℝ) ≤ (diskAt (cutoff 2 n)).card
        exact_mod_cast Finset.card_le_card (sums_subset_diskAt n)
      exact (mul_le_mul_of_nonneg_right hcard (hw n)).trans_lt hn
  have hconstant : L = Real.sqrt 2 * K := by
    have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
    have htwo : (2 : ℝ) / Real.sqrt 2 = Real.sqrt 2 := by
      apply (div_eq_iff hs).mpr
      rw [← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    change K * (2 / Real.sqrt 2) = Real.sqrt 2 * K
    rw [htwo, mul_comm]
  rw [← hconstant]
  convert hb using 1
  ext n
  dsimp only [weight]
  rw [div_div_eq_mul_div, mul_div_assoc]

end

end OMA.R_oeis_a047800_R1
