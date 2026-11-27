import OMAReductions.R_FlintCooksonHills_flint_hills_series_converges_R1

-- Step FlintCooksonHills.flint_hills_series_converges.R1.H2: hypothesis H2 of reduction FlintCooksonHills.flint_hills_series_converges.R1
-- Credit: @carterleffen
-- H2 := ∀ α c ν : ℝ, 0 < c → 1 < ν → ν < 5 / 2 →     (∀ q : ℕ, 0 < q →       c * (q : ℝ) ^ (1 - ν) ≤ |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)|) →     Summable (fun q : ℕ =>       1 / ((q : ℝ) ^ 3 * |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)| ^ 2))

/-!
# Summability from an irrationality exponent below 5/2

This is the dyadic counting argument behind the criterion of M. A. Alekseyev,
*On convergence of the Flint Hills series* (arXiv:1104.5100): an irrationality measure
below `5/2` makes `∑ 1 / (q ^ 3 ‖q α‖ ^ 2)` converge. The reduction is by @senamakel.

On the block `[2^k, 2^(k+1))` the signed distances `e q = q α - round (q α)` are
`η = c (2^(k+1))^(1-ν)`-separated, because `e q₂ - e q₁` is `(q₂ - q₁) α` minus an integer.
Every `|e q|` is at least `η`. Sorting by the bin `⌊|e q| / η⌋` and the sign of `e q`
is injective, so the block contributes at most `4 / (2^(3k) η^2)`, a geometric term of
ratio `2^(2ν-5) < 1`.
-/

namespace OMA.FlintHillsH2

open Finset

/-- Signed distance from `q α` to the nearest integer. -/
noncomputable def e (α : ℝ) (q : ℕ) : ℝ := (q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)

lemma dist_sub_le (α : ℝ) {q₁ q₂ : ℕ} (h : q₁ < q₂) :
    |e α (q₂ - q₁)| ≤ |e α q₂ - e α q₁| := by
  have key := round_le (((q₂ - q₁ : ℕ) : ℝ) * α)
    (round ((q₂ : ℝ) * α) - round ((q₁ : ℝ) * α))
  have hcast : ((q₂ - q₁ : ℕ) : ℝ) = (q₂ : ℝ) - q₁ := by rw [Nat.cast_sub h.le]
  unfold e
  refine key.trans (le_of_eq ?_)
  congr 1
  rw [hcast]
  push_cast
  ring

lemma rpow_anti {ν : ℝ} (hν : 1 < ν) {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    (b : ℝ) ^ (1 - ν) ≤ (a : ℝ) ^ (1 - ν) :=
  Real.rpow_le_rpow_of_nonpos (by exact_mod_cast ha) (by exact_mod_cast hab) (by linarith)

lemma sep {α c ν : ℝ} (hν : 1 < ν) (hc : 0 < c)
    (hyp : ∀ q : ℕ, 0 < q → c * (q : ℝ) ^ (1 - ν) ≤ |e α q|)
    {q₁ q₂ M : ℕ} (h12 : q₁ < q₂) (h2M : q₂ ≤ M) :
    c * (M : ℝ) ^ (1 - ν) ≤ |e α q₂ - e α q₁| := by
  have hd : 0 < q₂ - q₁ := Nat.sub_pos_of_lt h12
  calc c * (M : ℝ) ^ (1 - ν) ≤ c * ((q₂ - q₁ : ℕ) : ℝ) ^ (1 - ν) :=
        mul_le_mul_of_nonneg_left (rpow_anti hν hd (by omega)) hc.le
    _ ≤ |e α (q₂ - q₁)| := hyp _ hd
    _ ≤ _ := dist_sub_le α h12

lemma count_bound {ι : Type*} (B : Finset ι) (key : ι → ℕ × Bool)
    (hinj : Set.InjOn key B) (h1 : ∀ q ∈ B, 1 ≤ (key q).1) :
    ∑ q ∈ B, (((key q).1 : ℝ) ^ 2)⁻¹ ≤ 4 := by
  classical
  rw [show ∑ q ∈ B, (((key q).1 : ℝ) ^ 2)⁻¹ = ∑ x ∈ B.image key, ((x.1 : ℝ) ^ 2)⁻¹ from
    (sum_image (f := fun x : ℕ × Bool => ((x.1 : ℝ) ^ 2)⁻¹) hinj).symm]
  set J := (B.image key).sup Prod.fst
  have hsub : B.image key ⊆ (Ioo 0 (J + 1)) ×ˢ (univ : Finset Bool) := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hx
    simp only [mem_product, mem_Ioo, mem_univ, and_true]
    exact ⟨h1 q hq, Nat.lt_succ_of_le (le_sup (f := Prod.fst) hx)⟩
  calc ∑ x ∈ B.image key, ((x.1 : ℝ) ^ 2)⁻¹
      ≤ ∑ x ∈ (Ioo 0 (J + 1)) ×ˢ (univ : Finset Bool), ((x.1 : ℝ) ^ 2)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = 2 * ∑ i ∈ Ioo 0 (J + 1), ((i : ℝ) ^ 2)⁻¹ := by
        rw [sum_product, mul_sum]
        refine sum_congr rfl (fun i _ => ?_)
        simp only [sum_const, card_univ, Fintype.card_bool, nsmul_eq_mul]
        norm_num
    _ ≤ 2 * 2 := by
        gcongr
        have := sum_Ioo_inv_sq_le (α := ℝ) 0 (J + 1)
        simpa using this
    _ = 4 := by norm_num

lemma block {α c ν : ℝ} (hν : 1 < ν) (hc : 0 < c)
    (hyp : ∀ q : ℕ, 0 < q → c * (q : ℝ) ^ (1 - ν) ≤ |e α q|) (k : ℕ) :
    ∑ q ∈ Ico (2 ^ k : ℕ) (2 ^ (k + 1)), 1 / ((q : ℝ) ^ 3 * |e α q| ^ 2) ≤
      4 / (((2 : ℝ) ^ k) ^ 3 * (c * ((2 ^ (k + 1) : ℕ) : ℝ) ^ (1 - ν)) ^ 2) := by
  set M : ℕ := 2 ^ (k + 1) with hM
  set η : ℝ := c * (M : ℝ) ^ (1 - ν) with hη
  have hMpos : 0 < M := by positivity
  have hηpos : 0 < η := mul_pos hc (Real.rpow_pos_of_pos (by exact_mod_cast hMpos) _)
  set B := Ico (2 ^ k) M with hB
  have hmemB : ∀ q ∈ B, 2 ^ k ≤ q ∧ q < M := fun q hq => mem_Ico.mp hq
  have hlow : ∀ q ∈ B, η ≤ |e α q| := by
    intro q hq
    obtain ⟨h1, h2⟩ := hmemB q hq
    have hq0 : 0 < q := lt_of_lt_of_le (by positivity) h1
    exact (mul_le_mul_of_nonneg_left (rpow_anti hν hq0 h2.le) hc.le).trans (hyp q hq0)
  let key : ℕ → ℕ × Bool := fun q => (⌊|e α q| / η⌋₊, decide (0 ≤ e α q))
  have hkey1 : ∀ q ∈ B, 1 ≤ (key q).1 := by
    intro q hq
    apply Nat.le_floor
    rw [Nat.cast_one, le_div_iff₀ hηpos, one_mul]
    exact hlow q hq
  have hkey_le : ∀ q, ((key q).1 : ℝ) * η ≤ |e α q| := by
    intro q
    have := Nat.floor_le (div_nonneg (abs_nonneg (e α q)) hηpos.le)
    exact (le_div_iff₀ hηpos).mp this
  have hkey_lt : ∀ q, |e α q| < ((key q).1 : ℝ) * η + η := by
    intro q
    have := Nat.lt_floor_add_one (|e α q| / η)
    have h2 := (div_lt_iff₀ hηpos).mp this
    linarith [show (((key q).1 : ℝ) + 1) * η = ((key q).1 : ℝ) * η + η by ring]
  have hinj : Set.InjOn key B := by
    intro q₁ hq₁ q₂ hq₂ heq
    by_contra hne
    have hfl : (key q₁).1 = (key q₂).1 := congrArg Prod.fst heq
    have hsg : decide (0 ≤ e α q₁) = decide (0 ≤ e α q₂) := congrArg Prod.snd heq
    have hiff : 0 ≤ e α q₁ ↔ 0 ≤ e α q₂ := decide_eq_decide.mp hsg
    have hclose : |e α q₂ - e α q₁| < η := by
      have a1 := hkey_le q₁
      have a2 := hkey_lt q₁
      have b1 := hkey_le q₂
      have b2 := hkey_lt q₂
      rw [hfl] at a1 a2
      have habs : |e α q₂ - e α q₁| = abs (|e α q₂| - |e α q₁|) := by
        by_cases h0 : 0 ≤ e α q₁
        · have h0' : 0 ≤ e α q₂ := hiff.mp h0
          rw [abs_of_nonneg h0, abs_of_nonneg h0']
        · have h0' : ¬ 0 ≤ e α q₂ := fun h => h0 (hiff.mpr h)
          rw [not_le] at h0 h0'
          rw [abs_of_neg h0, abs_of_neg h0', ← abs_neg]
          congr 1
          ring
      rw [habs, abs_lt]
      constructor <;> linarith
    rcases lt_or_gt_of_ne hne with h | h
    · have hs : η ≤ |e α q₂ - e α q₁| := sep hν hc hyp h (hmemB q₂ hq₂).2.le
      linarith
    · have hs : η ≤ |e α q₁ - e α q₂| := sep hν hc hyp h (hmemB q₁ hq₁).2.le
      rw [abs_sub_comm] at hs
      linarith
  have hterm : ∀ q ∈ B, 1 / ((q : ℝ) ^ 3 * |e α q| ^ 2) ≤
      (1 / (((2 : ℝ) ^ k) ^ 3 * η ^ 2)) * (((key q).1 : ℝ) ^ 2)⁻¹ := by
    intro q hq
    have h1 : ((2 : ℝ) ^ k) ≤ q := by exact_mod_cast (hmemB q hq).1
    have hj : (1 : ℝ) ≤ (key q).1 := by exact_mod_cast hkey1 q hq
    have h2 := hkey_le q
    rw [← one_div, div_mul_div_comm, one_mul]
    apply one_div_le_one_div_of_le
    · positivity
    · calc ((2 : ℝ) ^ k) ^ 3 * η ^ 2 * ((key q).1 : ℝ) ^ 2
          = ((2 : ℝ) ^ k) ^ 3 * (((key q).1 : ℝ) * η) ^ 2 := by ring
        _ ≤ (q : ℝ) ^ 3 * |e α q| ^ 2 := by
          have h0 : 0 ≤ ((key q).1 : ℝ) * η := by positivity
          gcongr
  calc ∑ q ∈ B, 1 / ((q : ℝ) ^ 3 * |e α q| ^ 2)
      ≤ ∑ q ∈ B, (1 / (((2 : ℝ) ^ k) ^ 3 * η ^ 2)) * (((key q).1 : ℝ) ^ 2)⁻¹ :=
        sum_le_sum hterm
    _ = (1 / (((2 : ℝ) ^ k) ^ 3 * η ^ 2)) * ∑ q ∈ B, (((key q).1 : ℝ) ^ 2)⁻¹ := by
        rw [mul_sum]
    _ ≤ (1 / (((2 : ℝ) ^ k) ^ 3 * η ^ 2)) * 4 := by
        gcongr
        exact count_bound B key hinj hkey1
    _ = 4 / (((2 : ℝ) ^ k) ^ 3 * η ^ 2) := by ring

end OMA.FlintHillsH2

open Finset OMA.FlintHillsH2

theorem OMA.solution : OMA.R_FlintCooksonHills_flint_hills_series_converges_R1.H2 := by
  intro α c ν hc hν1 hν2 hyp
  have hyp' : ∀ q : ℕ, 0 < q → c * (q : ℝ) ^ (1 - ν) ≤ |e α q| := hyp
  show Summable (fun q : ℕ => 1 / ((q : ℝ) ^ 3 * |e α q| ^ 2))
  set s : ℝ := (2 : ℝ) ^ (1 - ν) with hsdef
  have hs : 0 < s := Real.rpow_pos_of_pos two_pos _
  have h8 : 1 < 8 * s ^ 2 := by
    have h : 8 * s ^ 2 = (2 : ℝ) ^ (5 - 2 * ν) := by
      rw [hsdef, ← Real.rpow_natCast ((2 : ℝ) ^ (1 - ν)) 2, ← Real.rpow_mul (by norm_num),
        show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_add two_pos]
      congr 1
      push_cast
      ring
    rw [h]
    exact Real.one_lt_rpow (by norm_num) (by linarith)
  set r : ℝ := (8 * s ^ 2)⁻¹ with hrdef
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ h8
  set A : ℝ := 4 / (c ^ 2 * s ^ 2) with hAdef
  have hA : 0 ≤ A := by positivity
  have hblock : ∀ k : ℕ, ∑ q ∈ Ico (2 ^ k : ℕ) (2 ^ (k + 1)), 1 / ((q : ℝ) ^ 3 * |e α q| ^ 2) ≤
      A * r ^ k := by
    intro k
    refine (block hν1 hc hyp' k).trans (le_of_eq ?_)
    have hM : ((2 ^ (k + 1) : ℕ) : ℝ) ^ (1 - ν) = s ^ (k + 1) := by
      push_cast
      rw [hsdef, Real.rpow_pow_comm (by norm_num)]
    have h83 : ((2 : ℝ) ^ k) ^ 3 = 8 ^ k := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [hM, h83, hAdef, hrdef, inv_pow, mul_pow, pow_succ]
    field_simp
    ring
  have hpow : ∀ N : ℕ, ∑ q ∈ range (2 ^ N), 1 / ((q : ℝ) ^ 3 * |e α q| ^ 2) ≤
      ∑ k ∈ range N, A * r ^ k := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [← sum_range_add_sum_Ico _ (Nat.pow_le_pow_right two_pos (Nat.le_succ N)),
        sum_range_succ]
      exact add_le_add ih (hblock N)
  refine summable_of_sum_range_le (c := A * (1 - r)⁻¹) (fun q => by positivity) ?_
  intro N
  calc ∑ q ∈ range N, 1 / ((q : ℝ) ^ 3 * |e α q| ^ 2)
      ≤ ∑ q ∈ range (2 ^ N), 1 / ((q : ℝ) ^ 3 * |e α q| ^ 2) :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (Nat.lt_two_pow_self (n := N)).le)
          (fun _ _ _ => by positivity)
    _ ≤ ∑ k ∈ range N, A * r ^ k := hpow N
    _ = A * ∑ k ∈ range N, r ^ k := (mul_sum _ _ _).symm
    _ ≤ A * (1 - r)⁻¹ := by
        gcongr
        rw [← tsum_geometric_of_lt_one hr0 hr1]
        exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum (range N)
          (fun _ _ => pow_nonneg hr0 _)
