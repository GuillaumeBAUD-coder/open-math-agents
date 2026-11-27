import FormalConjectures.ErdosProblems.«806»
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
Use the small-universal-set strategy of Alon, Bukh, and Sudakov (2009).
A translation chosen digit by digit places each element of a small chunk
in a different zero-digit class. Grouping the sorted set by interval and
rank gives one offset per chunk. The final estimates use explicit choices
of the digit base, interval length, and chunk size.
-/

-- Credit: @dk8827

open Finset Filter Real
open scoped BigOperators Pointwise Topology

namespace OMA.AdditiveBasis

private theorem shifts (q : ℕ) (hq : 1 < q) (f : ℕ → ℕ) (k : ℕ) :
    ∃ t < q ^ k, ∀ i < k, ((f i + t) / q ^ i) % q = 0 := by
  have hq0 : 0 < q := by omega
  induction k with
  | zero => exact ⟨0, by simp, fun _ hi => (Nat.not_lt_zero _ hi).elim⟩
  | succ k ih =>
    obtain ⟨t, ht, hi⟩ := ih
    let a := (f k + t) / q ^ k
    let r := a % q
    let c := if r = 0 then 0 else q - r
    have hr : r < q := Nat.mod_lt _ hq0
    have hc : c < q := by
      dsimp only [c]
      split <;> omega
    refine ⟨t + q ^ k * c, ?_, ?_⟩
    · have hmul := Nat.mul_le_mul_left (q ^ k) (show c + 1 ≤ q by omega)
      rw [Nat.mul_add, Nat.mul_one] at hmul
      rw [pow_succ]
      omega
    · intro i hik
      by_cases h : i = k
      · subst i
        rw [← add_assoc, Nat.add_mul_div_left _ _ (by positivity)]
        change (a + c) % q = 0
        rw [Nat.add_mod, Nat.mod_eq_of_lt hc]
        change (r + c) % q = 0
        by_cases hr0 : r = 0
        · simp [c, hr0]
        · have hrs : r + c = q := by simp only [c, if_neg hr0]; omega
          rw [hrs, Nat.mod_self]
      · have hik' : i < k := by omega
        have he : k = i + 1 + (k - (i + 1)) := by omega
        have hfactor : q ^ k * c = q ^ i * (q * (q ^ (k - (i + 1)) * c)) := by
          conv_lhs => rw [he, pow_add, pow_succ]
          ring
        rw [hfactor, ← add_assoc, Nat.add_mul_div_left _ _ (by positivity),
          Nat.add_mul_mod_self_left]
        exact hi i hik'

private theorem small_digit_filter (m q k i : ℕ) (hq : 1 < q)
    (hpow : q ^ k ≤ m) (hi : i < k) :
    ((range (2 * m)).filter (fun x => (x / q ^ i) % q = 0)).card * q ≤ 4 * m := by
  let p := q ^ i
  have hp : 0 < p := by dsimp only [p]; positivity
  have hq0 : 0 < q := by omega
  have hpq : p * q ≤ m := by
    rw [show p * q = q ^ (i + 1) from (pow_succ q i).symm]
    exact (Nat.pow_le_pow_right hq0 (by omega)).trans hpow
  let F := (range (2 * m)).filter (fun x => (x / p) % q = 0)
  let enc (x : ℕ) := (x / (p * q)) * p + x % p
  have split_at_digit {x : ℕ} (hx : x ∈ F) : x = (x / (p * q)) * (p * q) + x % p := by
    have hx0 := (mem_filter.1 hx).2
    have hfirst := Nat.mod_add_div x p
    have hsecond := Nat.mod_add_div (x / p) q
    rw [hx0, zero_add, Nat.div_div_eq_div_mul] at hsecond
    calc
      x = x % p + p * (x / p) := hfirst.symm
      _ = _ := by rw [← hsecond]; ring
  have hcard : F.card ≤ (range (3 * m / q + 1)).card := by
    apply card_le_card_of_injOn enc
    · intro x hx
      change x ∈ F at hx
      have hxm := mem_range.1 (mem_filter.1 hx).1
      have hr := Nat.mod_lt x hp
      have hrem : (x % p) * q ≤ m := (Nat.mul_le_mul_right q hr.le).trans hpq
      have hmain : x / (p * q) * (p * q) ≤ x := Nat.div_mul_le_self _ _
      have hmul : enc x * q ≤ 3 * m := by
        dsimp only [enc]
        rw [Nat.add_mul, Nat.mul_assoc]
        omega
      exact mem_range.2 (Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hq0).2 hmul))
    · intro x hx y hy h
      change x ∈ F at hx
      change y ∈ F at hy
      have hxrem := Nat.mod_lt x hp
      have hyrem := Nat.mod_lt y hp
      have hx_rem : enc x % p = x % p := by
        simp [enc, Nat.add_mod]
      have hy_rem : enc y % p = y % p := by
        simp [enc, Nat.add_mod]
      have hrem : x % p = y % p := by rw [← hx_rem, ← hy_rem, h]
      have hx_quot : enc x / p = x / (p * q) := by
        dsimp only [enc]
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hxrem, zero_add]
      have hy_quot : enc y / p = y / (p * q) := by
        dsimp only [enc]
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hyrem, zero_add]
      have hquot : x / (p * q) = y / (p * q) := by rw [← hx_quot, ← hy_quot, h]
      calc
        x = _ := split_at_digit hx
        _ = _ := by rw [hrem, hquot]
        _ = y := (split_at_digit hy).symm
  have hqm : q ≤ m := by
    exact (Nat.le_mul_of_pos_left _ hp).trans hpq
  simp only [card_range] at hcard
  calc
    F.card * q ≤ (3 * m / q + 1) * q := Nat.mul_le_mul_right _ hcard
    _ = (3 * m / q) * q + q := by ring
    _ ≤ 4 * m := by
      have := Nat.div_mul_le_self (3 * m) q
      omega

/-- Integers with at least one zero digit contain translates of every small subset. -/
theorem universal (m q k : ℕ) (hq : 1 < q) (hpow : q ^ k ≤ m) :
    ∃ U : Finset ℤ, U.card * q ≤ 4 * k * m ∧
      ∀ T : Finset ℕ, T ⊆ range m → T.card ≤ k →
        ∃ t : ℕ, ∀ x ∈ T, ((x + t : ℕ) : ℤ) ∈ U := by
  classical
  let D (i : ℕ) := (range (2 * m)).filter (fun x => (x / q ^ i) % q = 0)
  let W := (range k).biUnion D
  let U : Finset ℤ := W.map Nat.castEmbedding
  refine ⟨U, ?_, ?_⟩
  · change (W.map (Nat.castEmbedding : ℕ ↪ ℤ)).card * q ≤ _
    rw [card_map]
    calc
      W.card * q ≤ (∑ i ∈ range k, (D i).card) * q :=
        Nat.mul_le_mul_right _ card_biUnion_le
      _ = ∑ i ∈ range k, (D i).card * q := sum_mul ..
      _ ≤ ∑ _i ∈ range k, 4 * m := sum_le_sum (fun i hi =>
        small_digit_filter m q k i hq hpow (mem_range.1 hi))
      _ = 4 * k * m := by simp; ring
  · intro T hT hsize
    let f (i : ℕ) : ℕ := if hi : i < T.card then
      (T.equivFin.symm ⟨i, hi⟩ : ℕ) else 0
    obtain ⟨t, ht, hhit⟩ := shifts q hq f T.card
    have htm : t < m :=
      ht.trans_le ((Nat.pow_le_pow_right (by omega : 0 < q) hsize).trans hpow)
    refine ⟨t, fun x hx => ?_⟩
    apply Finset.mem_map.2
    refine ⟨x + t, mem_biUnion.2 ?_, rfl⟩
    let i := T.equivFin ⟨x, hx⟩
    have hi : (i : ℕ) < k := i.isLt.trans_le hsize
    have hfx : f i = x := by simp [f, i]
    refine ⟨i, mem_range.2 hi, mem_filter.2 ⟨mem_range.2 ?_, ?_⟩⟩
    · have := mem_range.1 (hT hx)
      omega
    · simpa only [hfx] using hhit i i.isLt

/-- Form one offset for each group of points in a common interval and rank block. -/
theorem basis_of_universal (n m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (A : Finset ℕ) (hA : A ⊆ Icc 1 n) (U : Finset ℤ)
    (hu : ∀ T : Finset ℕ, T ⊆ range m → T.card ≤ k →
      ∃ t : ℕ, ∀ x ∈ T, ((x + t : ℕ) : ℤ) ∈ U) :
    ∃ B : Finset ℤ, A.map Nat.castEmbedding ⊆ B + B ∧
      B.card ≤ U.card + n / m + A.card / k + 1 := by
  classical
  let d := A.orderEmbOfFin rfl
  let idx (i : Fin A.card) : ℕ := d i / m + (i : ℕ) / k
  let T (j : ℕ) : Finset (Fin A.card) := univ.filter (fun i => idx i = j)
  have idx_eq (i i' : Fin A.card) (h : idx i = idx i') :
      d i / m = d i' / m ∧ (i : ℕ) / k = (i' : ℕ) / k := by
    have key (a b : Fin A.card) (hab : a ≤ b) (he : idx a = idx b) :
        d a / m = d b / m ∧ (a : ℕ) / k = (b : ℕ) / k := by
      have hleft := Nat.div_le_div_right (c := m) (d.monotone hab)
      have hright := Nat.div_le_div_right (c := k) (show (a : ℕ) ≤ (b : ℕ) from hab)
      change d a / m + (a : ℕ) / k = d b / m + (b : ℕ) / k at he
      omega
    rcases le_total i i' with hi | hi
    · exact key i i' hi h
    · obtain ⟨hl, hr⟩ := key i' i hi h.symm
      exact ⟨hl.symm, hr.symm⟩
  have T_card (j : ℕ) : (T j).card ≤ k := by
    rw [← card_range k]
    apply card_le_card_of_injOn (fun i : Fin A.card => (i : ℕ) % k)
    · intro i _
      exact mem_range.2 (Nat.mod_lt _ hk)
    · intro i hi i' hi' he
      change i ∈ T j at hi
      change i' ∈ T j at hi'
      have hidx : idx i = idx i' := (mem_filter.1 hi).2.trans (mem_filter.1 hi').2.symm
      have hquot := (idx_eq i i' hidx).2
      apply Fin.ext
      have h1 := Nat.mod_add_div (i : ℕ) k
      have h2 := Nat.mod_add_div (i' : ℕ) k
      rw [hquot] at h1
      change (i : ℕ) % k = (i' : ℕ) % k at he
      omega
  let R (j : ℕ) := (T j).image (fun i => d i % m)
  have shift (j : ℕ) : ∃ t : ℕ, ∀ a ∈ R j, ((a + t : ℕ) : ℤ) ∈ U := by
    refine hu (R j) ?_ (card_image_le.trans (T_card j))
    intro a ha
    obtain ⟨i, _, rfl⟩ := mem_image.1 ha
    exact mem_range.2 (Nat.mod_lt _ hm)
  choose t ht using shift
  let c (j : ℕ) : ℕ := if h : (T j).Nonempty then d (Classical.choose h) / m else 0
  have c_eq (i : Fin A.card) : c (idx i) = d i / m := by
    have hi : i ∈ T (idx i) := mem_filter.2 ⟨mem_univ _, rfl⟩
    have h : (T (idx i)).Nonempty := ⟨i, hi⟩
    dsimp only [c]
    rw [dif_pos h]
    exact (idx_eq (Classical.choose h) i (mem_filter.1 (Classical.choose_spec h)).2).1
  let J := range (n / m + A.card / k + 1)
  let off (j : ℕ) : ℤ := (c j : ℤ) * (m : ℤ) - (t j : ℤ)
  let B := U ∪ J.image off
  refine ⟨B, ?_, ?_⟩
  · intro aInt ha
    obtain ⟨a, haA, rfl⟩ := Finset.mem_map.1 ha
    let i := (A.orderIsoOfFin rfl).symm ⟨a, haA⟩
    have hdi : d i = a := congrArg Subtype.val
      ((A.orderIsoOfFin rfl).apply_symm_apply ⟨a, haA⟩)
    let j := idx i
    have hj : j ∈ J := by
      have hleft : d i / m ≤ n / m := Nat.div_le_div_right (by rw [hdi]; exact (mem_Icc.1 (hA haA)).2)
      have hright : (i : ℕ) / k ≤ A.card / k := Nat.div_le_div_right i.isLt.le
      apply mem_range.2
      change d i / m + (i : ℕ) / k < n / m + A.card / k + 1
      omega
    have hiR : d i % m ∈ R j := mem_image.2
      ⟨i, mem_filter.2 ⟨mem_univ _, rfl⟩, rfl⟩
    apply Finset.mem_add.2
    refine ⟨_, mem_union_left _ (ht j _ hiR), _, mem_union_right _ (mem_image_of_mem off hj), ?_⟩
    change (((d i % m + t j : ℕ) : ℤ)) + ((c j : ℤ) * m - t j) = (a : ℤ)
    rw [c_eq i, ← hdi, Nat.cast_add]
    calc
      _ = ((d i % m : ℕ) : ℤ) + (m : ℤ) * ((d i / m : ℕ) : ℤ) := by ring
      _ = _ := by exact_mod_cast Nat.mod_add_div (d i) m
  · have hcard := (card_union_le U (J.image off)).trans
        (Nat.add_le_add_left (card_image_le (f := off) (s := J)) U.card)
    simpa [B, J, add_assoc] using hcard

private theorem log_le_sqrt_of_pos {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ √x := by
  have h : 0 < √x / 2 := by positivity
  have heq : Real.log (√x / 2) = Real.log x / 2 - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt hx.le]
  linarith only [Real.log_le_sub_one_of_pos h, heq, Real.log_two_lt_d9]

private theorem cast_div_le (a b : ℕ) (hb : 0 < b) : ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / b := by
  apply (le_div_iff₀ (show (0 : ℝ) < b by exact_mod_cast hb)).2
  exact_mod_cast Nat.div_mul_le_self a b

set_option maxHeartbeats 860000 in
theorem small_basis : type_of% @Erdos806.erdos_806.variants.alon_bukh_sudakov := by
  refine ⟨40, ?_⟩
  have hL_atTop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hL_atTop.eventually_ge_atTop 400, eventually_ge_atTop (1 : ℕ)] with n hL hn
  intro A hA hAcard
  let L := Real.log (n : ℝ)
  let D := Real.log L
  let z := √(n : ℝ)
  let m : ℕ := ⌈z * L⌉₊
  let q : ℕ := ⌈L ^ 4⌉₊
  let k : ℕ := Nat.log q m
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hz0 : 0 < z := Real.sqrt_pos.2 hn0
  have hzsq : z ^ 2 = n := Real.sq_sqrt hn0.le
  have hzL : L ≤ z := log_le_sqrt_of_pos hn0
  have hz1 : 1 ≤ z := hL1.trans hzL
  have hD1 : 1 ≤ D := by
    have he : Real.exp 1 ≤ L := by
      have hexp := Real.exp_one_lt_three
      linarith
    exact (Real.le_log_iff_exp_le hL0).2 he
  have hD0 : 0 < D := by linarith
  have hD : 20 * D ≤ L := by
    have hDle : D ≤ √L := log_le_sqrt_of_pos hL0
    have hroot : 20 ≤ √L := by
      have hs := Real.sq_sqrt hL0.le
      have hnon := Real.sqrt_nonneg L
      nlinarith only [hL, hs, hnon]
    have h1 := mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg L)
    have h2 := Real.sq_sqrt hL0.le
    nlinarith only [hDle, h1, h2]
  have hmlo : z * L ≤ (m : ℝ) := Nat.le_ceil _
  have hzL1 : 1 ≤ z * L := one_le_mul_of_one_le_of_one_le hz1 hL1
  have hmhi : (m : ℝ) ≤ 2 * z * L := by
    have h := Nat.ceil_lt_add_one (mul_nonneg hz0.le hL0.le)
    change (m : ℝ) < z * L + 1 at h
    linarith only [h, hzL1]
  have hm0r : 0 < (m : ℝ) := (mul_pos hz0 hL0).trans_le hmlo
  have hm0 : 0 < m := by exact_mod_cast hm0r
  have hqlo : L ^ 4 ≤ (q : ℝ) := Nat.le_ceil _
  have hL4 : L ≤ L ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hL1 (by decide : 1 ≤ 4)
  have hqhi : (q : ℝ) ≤ 2 * L ^ 4 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ L ^ 4 by positivity)
    change (q : ℝ) < L ^ 4 + 1 at h
    linarith only [h, hL4, hL1]
  have hq : 1 < q := by
    exact_mod_cast (show (1 : ℝ) < q by linarith only [hL, hL4, hqlo])
  have hq0 : (0 : ℝ) < q := by positivity
  have hqlow : 1 ≤ Real.log (q : ℝ) :=
    hD1.trans (Real.log_le_log hL0 (hL4.trans hqlo))
  have hqlog : Real.log (q : ℝ) ≤ 5 * D := by
    have h := Real.log_le_log hq0 hqhi
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h
    change Real.log (q : ℝ) ≤ Real.log 2 + (4 : ℝ) * D at h
    linarith only [h, hD1, Real.log_two_lt_d9]
  have hm_lowlog : L / 2 ≤ Real.log (m : ℝ) := by
    have hzle : z ≤ m := by calc
      _ = z * 1 := (mul_one z).symm
      _ ≤ z * L := mul_le_mul_of_nonneg_left hL1 hz0.le
      _ ≤ _ := hmlo
    have h := Real.log_le_log hz0 hzle
    rw [show Real.log z = L / 2 from Real.log_sqrt hn0.le] at h
    exact h
  have hm_log : Real.log (m : ℝ) ≤ 2 * L := by
    have h := Real.log_le_log hm0r hmhi
    rw [Real.log_mul (by positivity : (2 : ℝ) * z ≠ 0) hL0.ne',
      Real.log_mul (by norm_num) hz0.ne', show Real.log z = L / 2 from Real.log_sqrt hn0.le] at h
    change Real.log (m : ℝ) ≤ Real.log 2 + L / 2 + D at h
    linarith only [h, Real.log_two_lt_d9, hL, hD]
  have hpow : q ^ k ≤ m := Nat.pow_log_le_self _ hm0.ne'
  have hpowgt : m < q ^ (k + 1) := Nat.lt_pow_succ_log_self hq m
  have hk_hi : (k : ℝ) ≤ 2 * L := by
    have h := Real.log_le_log (pow_pos hq0 k) (show (q : ℝ) ^ k ≤ (m : ℝ) by exact_mod_cast hpow)
    rw [Real.log_pow] at h
    have hmul := mul_le_mul_of_nonneg_left hqlow (show (0 : ℝ) ≤ k by positivity)
    linarith only [h, hmul, hm_log]
  have hk_lo : L ≤ 20 * (k : ℝ) * D := by
    have h := Real.log_lt_log hm0r (show (m : ℝ) < (q : ℝ) ^ (k + 1) by exact_mod_cast hpowgt)
    rw [Real.log_pow, Nat.cast_add, Nat.cast_one] at h
    have hmul := mul_le_mul_of_nonneg_left hqlog (show (0 : ℝ) ≤ (k : ℝ) + 1 by positivity)
    nlinarith only [h, hmul, hm_lowlog, hD]
  have hk0 : 0 < k := by
    by_contra h
    have hk : k = 0 := by omega
    norm_num [hk] at hk_lo
    exact hL0.not_ge hk_lo
  have hk0r : (0 : ℝ) < k := by exact_mod_cast hk0
  obtain ⟨U, hUcard, hU⟩ := universal m q k hq hpow
  obtain ⟨B, hBB, hBcard⟩ := basis_of_universal n m k hm0 hk0 A hA U hU
  refine ⟨B, hBB, ?_⟩
  let W := D / L * z
  have hW0 : 0 ≤ W := by positivity
  have hW1 : 1 ≤ W := by
    have h := mul_le_mul_of_nonneg_left hzL (show 0 ≤ D / L by positivity)
    rw [div_mul_cancel₀ _ hL0.ne'] at h
    exact hD1.trans h
  have hshift1 : (A.card : ℝ) / k ≤ 20 * W := by
    apply (div_le_iff₀ hk0r).2
    have h1 := mul_le_mul_of_nonneg_left hk_lo (show 0 ≤ z / L by positivity)
    have hs : (z / L) * L = z := div_mul_cancel₀ _ hL0.ne'
    calc
      (A.card : ℝ) ≤ z := hAcard
      _ = (z / L) * L := hs.symm
      _ ≤ (z / L) * (20 * (k : ℝ) * D) := h1
      _ = _ := by dsimp only [W]; ring
  have hshift2 : (n : ℝ) / m ≤ W := by
    apply (div_le_iff₀ hm0r).2
    calc
      (n : ℝ) = 1 * z ^ 2 := by rw [hzsq, one_mul]
      _ ≤ D * z ^ 2 := mul_le_mul_of_nonneg_right hD1 (sq_nonneg _)
      _ = W * (z * L) := by dsimp only [W]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hmlo hW0
  have hUle : (U.card : ℝ) ≤ 16 * W := by
    apply (le_of_mul_le_mul_right · hq0)
    calc
      (U.card : ℝ) * q ≤ 4 * (k : ℝ) * m := by exact_mod_cast hUcard
      _ ≤ 4 * (2 * L) * (2 * z * L) := by gcongr
      _ = 16 * (z * L ^ 2) := by ring
      _ ≤ 16 * (D * z * L ^ 3) := by
        have hDL : 1 ≤ D * L := one_le_mul_of_one_le_of_one_le hD1 hL1
        have h := mul_le_mul_of_nonneg_right hDL (show 0 ≤ z * L ^ 2 by positivity)
        nlinarith only [h]
      _ = (16 * W) * L ^ 4 := by dsimp only [W]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hqlo (by positivity)
  have hcast : (B.card : ℝ) ≤ (U.card : ℝ) + ((n / m : ℕ) : ℝ) +
      ((A.card / k : ℕ) : ℝ) + 1 := by exact_mod_cast hBcard
  change (B.card : ℝ) ≤ 40 * D / L * z
  have hscale : 40 * D / L * z = 40 * W := by dsimp only [W]; ring
  rw [hscale]
  linarith only [hcast, hUle, (cast_div_le _ _ hm0).trans hshift2,
    (cast_div_le _ _ hk0).trans hshift1, hW1]

end OMA.AdditiveBasis

theorem OMA.solution : type_of% @Erdos806.erdos_806.variants.alon_bukh_sudakov :=
  OMA.AdditiveBasis.small_basis
