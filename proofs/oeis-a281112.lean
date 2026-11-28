import OMAStatements.S_oeis_a281112
import Mathlib

open OMA.S_oeis_a281112 Filter Topology PowerSeries

private lemma phi_bounds : (1 : ℝ) < (1 + Real.sqrt 5) / 2 ∧ (1 + Real.sqrt 5) / 2 < 2 := by
  have h1 : (1 : ℝ) < Real.sqrt 5 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h2 : Real.sqrt 5 < 3 := by
    rw [show (3 : ℝ) = Real.sqrt 9 by norm_num]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  constructor <;> linarith

private lemma weight_zero : weight 0 = 1 := by
  have h := phi_bounds
  have hfl : ⌊((0 : ℝ) + 1) * ((1 + Real.sqrt 5) / 2)⌋ = 1 := by
    rw [Int.floor_eq_iff]
    constructor <;> push_cast <;> linarith
  unfold weight
  simp only [Nat.cast_zero]
  rw [hfl]
  norm_num

private lemma weight_succ_sub (n : ℕ) :
    (1 : ℝ) ≤ weight (n + 1) - weight n ∧ weight (n + 1) - weight n ≤ 2 := by
  have hphi := phi_bounds
  set x : ℝ := ((n : ℝ) + 1) * ((1 + Real.sqrt 5) / 2)
  have hx1 : (((n + 1 : ℕ) : ℝ) + 1) * ((1 + Real.sqrt 5) / 2) = x + (1 + Real.sqrt 5) / 2 := by
    push_cast
    ring
  have hfl1 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have hfl2 : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
  have hge : ⌊x⌋ + 1 ≤ ⌊x + (1 + Real.sqrt 5) / 2⌋ := by
    rw [Int.le_floor]
    push_cast
    linarith
  have hlt : ⌊x + (1 + Real.sqrt 5) / 2⌋ < ⌊x⌋ + 3 := by
    rw [Int.floor_lt]
    push_cast
    linarith
  have hle : ⌊x + (1 + Real.sqrt 5) / 2⌋ ≤ ⌊x⌋ + 2 := by omega
  have hgeR : (⌊x⌋ : ℝ) + 1 ≤ (⌊x + (1 + Real.sqrt 5) / 2⌋ : ℝ) := by exact_mod_cast hge
  have hleR : (⌊x + (1 + Real.sqrt 5) / 2⌋ : ℝ) ≤ (⌊x⌋ : ℝ) + 2 := by exact_mod_cast hle
  unfold weight
  rw [hx1]
  constructor <;> linarith

private noncomputable def g : PowerSeries ℝ := (1 + PowerSeries.X) * denominator

private lemma coeff_zero_g : coeff 0 g = 1 := by
  rw [g, add_mul, one_mul, map_add, PowerSeries.coeff_zero_X_mul, add_zero,
    denominator, PowerSeries.coeff_mk, weight_zero]
  norm_num

private lemma coeff_succ_g (n : ℕ) :
    coeff (n + 1) g = (-1 : ℝ) ^ (n + 1) * (weight (n + 1) - weight n) := by
  rw [g, add_mul, one_mul, map_add, PowerSeries.coeff_succ_X_mul,
    denominator, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  rw [pow_succ]
  ring

private lemma abs_coeff_g_le_two (n : ℕ) : |coeff n g| ≤ 2 := by
  cases n with
  | zero =>
    rw [coeff_zero_g]
    norm_num
  | succ n =>
    rw [coeff_succ_g, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have h := weight_succ_sub n
    rw [abs_of_nonneg (by linarith)]
    exact h.2

private noncomputable def gEval (x : ℝ) : ℝ := ∑' n : ℕ, coeff n g * x ^ n

private lemma summable_g_abs (x : ℝ) (hx : |x| < 1) :
    Summable (fun n : ℕ => ‖coeff n g * x ^ n‖) := by
  have hdom : Summable (fun n : ℕ => (2 : ℝ) * |x| ^ n) :=
    (summable_geometric_of_lt_one (abs_nonneg x) hx).mul_left 2
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hdom
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_right (abs_coeff_g_le_two n) (pow_nonneg (abs_nonneg x) n)

private lemma summable_g (x : ℝ) (hx : |x| < 1) :
    Summable (fun n : ℕ => coeff n g * x ^ n) :=
  (summable_g_abs x hx).of_norm

private lemma continuousOn_gEval (a b : ℝ) (ha : 0 ≤ a) (hb : b < 1) :
    ContinuousOn gEval (Set.Icc a b) := by
  have hdom : Summable (fun n : ℕ => (2 : ℝ) * max 0 b ^ n) := by
    have hb' : max 0 b < 1 := max_lt (by norm_num) hb
    exact (summable_geometric_of_lt_one (le_max_left 0 b) hb').mul_left 2
  refine continuousOn_tsum (fun n => ?_) hdom (fun n x hx => ?_)
  · exact (continuous_const.mul (continuous_pow n)).continuousOn
  · rw [Real.norm_eq_abs, abs_mul, abs_pow]
    have hx0 : 0 ≤ x := le_trans ha hx.1
    have hxb : |x| ≤ max 0 b := by
      rw [abs_of_nonneg hx0]
      exact le_trans hx.2 (le_max_right 0 b)
    exact mul_le_mul (abs_coeff_g_le_two n)
      (pow_le_pow_left₀ (abs_nonneg x) hxb n)
      (pow_nonneg (abs_nonneg x) n) (by norm_num)

private lemma weight_eq_of_check (k w : ℕ)
    (h1 : k + 1 ≤ 2 * w)
    (h2 : (2 * w - (k + 1)) ^ 2 < 5 * (k + 1) ^ 2)
    (h3 : 5 * (k + 1) ^ 2 < (2 * w + 2 - (k + 1)) ^ 2) :
    weight k = (w : ℝ) := by
  have hm : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  have h2w : (k : ℝ) + 1 ≤ 2 * (w : ℝ) := by exact_mod_cast h1
  have h2R : (2 * (w : ℝ) - ((k : ℝ) + 1)) ^ 2 < 5 * ((k : ℝ) + 1) ^ 2 := by
    have hnat : (((2 * w - (k + 1)) ^ 2 : ℕ) : ℝ) < ((5 * (k + 1) ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast h2
    rw [Nat.cast_pow, Nat.cast_sub h1] at hnat
    push_cast at hnat
    exact hnat
  have h3R : 5 * ((k : ℝ) + 1) ^ 2 < (2 * (w : ℝ) + 2 - ((k : ℝ) + 1)) ^ 2 := by
    have h1' : k + 1 ≤ 2 * w + 2 := by omega
    have hnat : ((5 * (k + 1) ^ 2 : ℕ) : ℝ) < (((2 * w + 2 - (k + 1)) ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast h3
    rw [Nat.cast_pow, Nat.cast_sub h1'] at hnat
    push_cast at hnat
    exact hnat
  have hsq : (((k : ℝ) + 1) * Real.sqrt 5) ^ 2 = 5 * ((k : ℝ) + 1) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    ring
  have hsqrt_nn : 0 ≤ ((k : ℝ) + 1) * Real.sqrt 5 := mul_nonneg hm (Real.sqrt_nonneg 5)
  have hlo : 2 * (w : ℝ) - ((k : ℝ) + 1) < ((k : ℝ) + 1) * Real.sqrt 5 := by
    nlinarith
  have hhi : ((k : ℝ) + 1) * Real.sqrt 5 < 2 * (w : ℝ) + 2 - ((k : ℝ) + 1) := by
    nlinarith
  have hfl : ⌊((k : ℝ) + 1) * ((1 + Real.sqrt 5) / 2)⌋ = (w : ℤ) := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> linarith
  simp [weight, hfl]

private def checkChunk : List ℕ → ℕ → Bool
  | [], _ => true
  | w :: rest, k =>
    let m := k + 1
    decide (m ≤ 2 * w) &&
    decide ((2 * w - m) ^ 2 < 5 * m ^ 2) &&
    decide (5 * m ^ 2 < (2 * w + 2 - m) ^ 2) &&
    checkChunk rest (k + 1)

private lemma checkChunk_sound : ∀ (l : List ℕ) (k0 : ℕ),
    checkChunk l k0 = true →
    ∀ i : ℕ, (hi : i < l.length) → weight (k0 + i) = (l[i] : ℝ) := by
  intro l
  induction l with
  | nil =>
    intro k0 _ i hi
    simp at hi
  | cons w rest ih =>
    intro k0 hchk i hi
    simp only [checkChunk, Bool.and_eq_true, decide_eq_true_eq] at hchk
    rcases hchk with ⟨⟨⟨h1, h2⟩, h3⟩, hrest⟩
    cases i with
    | zero =>
      simp only [Nat.add_zero, List.getElem_cons_zero]
      exact weight_eq_of_check k0 w h1 h2 h3
    | succ i =>
      have hi' : i < rest.length := by
        simp only [List.length_cons] at hi
        omega
      have hidx : k0 + (i + 1) = (k0 + 1) + i := by omega
      rw [hidx, List.getElem_cons_succ]
      exact ih (k0 + 1) hrest i hi'

private def revDiffsAux (prev : ℕ) (sgn : ℤ) (acc : List ℤ) : List ℕ → List ℤ
  | [] => acc
  | w :: rest => revDiffsAux w (-sgn) ((sgn * ((w : ℤ) - (prev : ℤ))) :: acc) rest

private def hornerLo (num den S : ℤ) (acc : ℤ) : List ℤ → ℤ
  | [] => acc
  | c :: rest => hornerLo num den S ((acc * num) / den + c * S) rest

private def hornerReal (r : ℝ) (x : ℝ) : List ℤ → ℝ
  | [] => x
  | c :: rest => hornerReal r (x * r + (c : ℝ)) rest

private lemma revDiffsAux_append (prev : ℕ) (sgn : ℤ) :
    ∀ (l : List ℕ) (acc : List ℤ),
      revDiffsAux prev sgn acc l = revDiffsAux prev sgn [] l ++ acc := by
  intro l
  induction l generalizing prev sgn with
  | nil =>
    intro acc
    rfl
  | cons w rest ih =>
    intro acc
    simp only [revDiffsAux]
    rw [ih w (-sgn) ((sgn * ((w : ℤ) - (prev : ℤ))) :: acc),
      ih w (-sgn) [sgn * ((w : ℤ) - (prev : ℤ))], List.append_assoc, List.singleton_append]

private lemma hornerReal_append (r : ℝ) :
    ∀ (l1 l2 : List ℤ) (x : ℝ),
      hornerReal r x (l1 ++ l2) = hornerReal r (hornerReal r x l1) l2 := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 x
    rfl
  | cons c rest ih =>
    intro l2 x
    exact ih l2 (x * r + (c : ℝ))

private lemma hornerLo_sound (num den S : ℤ) (hnum : 0 ≤ num) (hden : 0 < den) (hS : 0 < S) :
    ∀ (cs : List ℤ) (acc : ℤ) (x : ℝ),
      (acc : ℝ) / (S : ℝ) ≤ x →
      (hornerLo num den S acc cs : ℝ) / (S : ℝ) ≤ hornerReal ((num : ℝ) / (den : ℝ)) x cs := by
  intro cs
  induction cs with
  | nil =>
    intro acc x hle
    exact hle
  | cons c rest ih =>
    intro acc x hle
    simp only [hornerLo, hornerReal]
    apply ih
    have hdenR : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
    have hSR : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
    have hnumR : (0 : ℝ) ≤ (num : ℝ) := by exact_mod_cast hnum
    have hr_nonneg : (0 : ℝ) ≤ (num : ℝ) / (den : ℝ) := div_nonneg hnumR (le_of_lt hdenR)
    have hdiv : ((acc * num) / den : ℤ) * den ≤ acc * num :=
      Int.ediv_mul_le (acc * num) (ne_of_gt hden)
    have hdivR : ((((acc * num) / den : ℤ) : ℝ)) * (den : ℝ) ≤ (acc : ℝ) * (num : ℝ) := by
      exact_mod_cast hdiv
    have hq : ((((acc * num) / den : ℤ) : ℝ)) ≤ (acc : ℝ) * ((num : ℝ) / (den : ℝ)) := by
      rw [← mul_div_assoc, le_div_iff₀ hdenR]
      exact hdivR
    have hstep : ((((acc * num) / den : ℤ) : ℝ) + (c : ℝ) * (S : ℝ)) / (S : ℝ) ≤
        ((acc : ℝ) / (S : ℝ)) * ((num : ℝ) / (den : ℝ)) + (c : ℝ) := by
      rw [add_div, mul_div_cancel_right₀ _ (ne_of_gt hSR)]
      have hq' : ((((acc * num) / den : ℤ) : ℝ)) / (S : ℝ) ≤
          ((acc : ℝ) / (S : ℝ)) * ((num : ℝ) / (den : ℝ)) := by
        rw [div_le_iff₀ hSR]
        calc
          ((((acc * num) / den : ℤ) : ℝ))
            ≤ (acc : ℝ) * ((num : ℝ) / (den : ℝ)) := hq
          _ = ((acc : ℝ) / (S : ℝ)) * ((num : ℝ) / (den : ℝ)) * (S : ℝ) := by
            rw [mul_right_comm, div_mul_cancel₀ _ (ne_of_gt hSR)]
      linarith
    push_cast
    exact le_trans hstep (by nlinarith)

private lemma hornerReal_revDiffsAux (r : ℝ) :
    ∀ (l : List ℕ) (k0 prev : ℕ) (sgn : ℤ) (x : ℝ),
      ((k0 = 0 ∧ prev = 0) ∨ (0 < k0 ∧ weight (k0 - 1) = (prev : ℝ))) →
      checkChunk l k0 = true →
      hornerReal r x (revDiffsAux prev sgn [] l) =
        x * r ^ l.length +
          ∑ i ∈ Finset.range l.length,
            ((sgn : ℝ) * (-1 : ℝ) ^ k0) * coeff (k0 + i) g * r ^ i := by
  intro l
  induction l with
  | nil =>
    intro k0 prev sgn x _ _
    simp [revDiffsAux, hornerReal]
  | cons w rest ih =>
    intro k0 prev sgn x hprev hchk
    simp only [checkChunk, Bool.and_eq_true, decide_eq_true_eq] at hchk
    rcases hchk with ⟨⟨⟨h1, h2⟩, h3⟩, hrest⟩
    have hw : weight k0 = (w : ℝ) := weight_eq_of_check k0 w h1 h2 h3
    simp only [revDiffsAux]
    rw [revDiffsAux_append, hornerReal_append]
    have hih := ih (k0 + 1) w (-sgn) x (Or.inr ⟨by omega, by simpa using hw⟩) hrest
    rw [hih]
    simp only [hornerReal, List.length_cons]
    have hsgn_inv : ((-sgn : ℤ) : ℝ) * (-1 : ℝ) ^ (k0 + 1) = (sgn : ℝ) * (-1 : ℝ) ^ k0 := by
      push_cast
      rw [pow_succ]
      ring
    have hc0 : ((sgn * ((w : ℤ) - (prev : ℤ)) : ℤ) : ℝ) =
        ((sgn : ℝ) * (-1 : ℝ) ^ k0) * coeff k0 g := by
      push_cast
      rcases hprev with ⟨rfl, rfl⟩ | ⟨hkpos, hwp⟩
      · have hw1 : (w : ℝ) = 1 := by rw [← hw, weight_zero]
        rw [hw1, coeff_zero_g]
        norm_num
      · obtain ⟨m, rfl⟩ : ∃ m, k0 = m + 1 := ⟨k0 - 1, by omega⟩
        simp only [Nat.add_sub_cancel] at hwp
        rw [coeff_succ_g, hw, hwp]
        have hsq : (-1 : ℝ) ^ (m + 1) * (-1 : ℝ) ^ (m + 1) = 1 := by
          rw [← pow_add, ← two_mul, pow_mul]
          norm_num
        calc
          (sgn : ℝ) * ((w : ℝ) - (prev : ℝ))
            = (sgn : ℝ) * ((-1 : ℝ) ^ (m + 1) * (-1 : ℝ) ^ (m + 1)) * ((w : ℝ) - (prev : ℝ)) := by
              rw [hsq, mul_one]
          _ = (sgn : ℝ) * (-1 : ℝ) ^ (m + 1) * ((-1 : ℝ) ^ (m + 1) * ((w : ℝ) - (prev : ℝ))) := by
              ring
    rw [Finset.sum_range_succ' (fun i => ((sgn : ℝ) * (-1 : ℝ) ^ k0) * coeff (k0 + i) g * r ^ i)]
    simp only [Nat.add_zero, pow_zero, mul_one]
    rw [← hc0, add_mul, Finset.sum_mul]
    have hsum_eq :
        ∑ i ∈ Finset.range rest.length,
          ((-sgn : ℤ) : ℝ) * (-1 : ℝ) ^ (k0 + 1) * coeff (k0 + 1 + i) g * r ^ i * r =
        ∑ i ∈ Finset.range rest.length,
          ((sgn : ℝ) * (-1 : ℝ) ^ k0) * coeff (k0 + (i + 1)) g * r ^ (i + 1) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hsgn_inv, show k0 + 1 + i = k0 + (i + 1) by omega, pow_succ]
      ring
    rw [hsum_eq, pow_succ r rest.length]
    ring

private noncomputable def tailSum (r : ℝ) (sgn : ℤ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (400 - k), (sgn : ℝ) * coeff (k + i) g * r ^ i

private lemma chunk_step (num den S : ℤ) (hnum : 0 ≤ num) (hden : 0 < den) (hS : 0 < S)
    (l : List ℕ) (k0 prev : ℕ) (sgn acc acc' : ℤ)
    (hlen : l.length = 10) (heven : Even k0)
    (hprev : (k0 = 0 ∧ prev = 0) ∨ (0 < k0 ∧ weight (k0 - 1) = (prev : ℝ)))
    (hchk : checkChunk l k0 = true) (hk : k0 + 10 ≤ 400)
    (hdec : hornerLo num den S acc (revDiffsAux prev sgn [] l) = acc')
    (hacc : (acc : ℝ) / (S : ℝ) ≤ tailSum ((num : ℝ) / (den : ℝ)) sgn (k0 + 10)) :
    (acc' : ℝ) / (S : ℝ) ≤ tailSum ((num : ℝ) / (den : ℝ)) sgn k0 := by
  set r : ℝ := (num : ℝ) / (den : ℝ)
  have h1 := hornerLo_sound num den S hnum hden hS (revDiffsAux prev sgn [] l) acc
    (tailSum r sgn (k0 + 10)) hacc
  rw [hdec, hornerReal_revDiffsAux r l k0 prev sgn _ hprev hchk, hlen] at h1
  have hpow1 : (-1 : ℝ) ^ k0 = 1 := by
    rcases heven with ⟨t, rfl⟩
    rw [← two_mul, pow_mul]
    norm_num
  have htail : tailSum r sgn (k0 + 10) * r ^ 10 +
      ∑ i ∈ Finset.range 10, ((sgn : ℝ) * (-1 : ℝ) ^ k0) * coeff (k0 + i) g * r ^ i =
      tailSum r sgn k0 := by
    simp only [hpow1, mul_one, tailSum]
    have hsplit : 400 - k0 = 10 + (400 - (k0 + 10)) := by omega
    rw [hsplit, Finset.sum_range_add, Finset.sum_mul, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show k0 + 10 + i = k0 + (10 + i) by omega, pow_add]
    ring
  rw [htail] at h1
  exact h1

private def P85 : ℤ := 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000
private def S92 : ℤ := 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

private def wC0 : List ℕ := [1, 3, 4, 6, 8, 9, 11, 12, 14, 16]
private def wC1 : List ℕ := [17, 19, 21, 22, 24, 25, 27, 29, 30, 32]
private def wC2 : List ℕ := [33, 35, 37, 38, 40, 42, 43, 45, 46, 48]
private def wC3 : List ℕ := [50, 51, 53, 55, 56, 58, 59, 61, 63, 64]
private def wC4 : List ℕ := [66, 67, 69, 71, 72, 74, 76, 77, 79, 80]
private def wC5 : List ℕ := [82, 84, 85, 87, 88, 90, 92, 93, 95, 97]
private def wC6 : List ℕ := [98, 100, 101, 103, 105, 106, 108, 110, 111, 113]
private def wC7 : List ℕ := [114, 116, 118, 119, 121, 122, 124, 126, 127, 129]
private def wC8 : List ℕ := [131, 132, 134, 135, 137, 139, 140, 142, 144, 145]
private def wC9 : List ℕ := [147, 148, 150, 152, 153, 155, 156, 158, 160, 161]
private def wC10 : List ℕ := [163, 165, 166, 168, 169, 171, 173, 174, 176, 177]
private def wC11 : List ℕ := [179, 181, 182, 184, 186, 187, 189, 190, 192, 194]
private def wC12 : List ℕ := [195, 197, 199, 200, 202, 203, 205, 207, 208, 210]
private def wC13 : List ℕ := [211, 213, 215, 216, 218, 220, 221, 223, 224, 226]
private def wC14 : List ℕ := [228, 229, 231, 232, 234, 236, 237, 239, 241, 242]
private def wC15 : List ℕ := [244, 245, 247, 249, 250, 252, 254, 255, 257, 258]
private def wC16 : List ℕ := [260, 262, 263, 265, 266, 268, 270, 271, 273, 275]
private def wC17 : List ℕ := [276, 278, 279, 281, 283, 284, 286, 288, 289, 291]
private def wC18 : List ℕ := [292, 294, 296, 297, 299, 300, 302, 304, 305, 307]
private def wC19 : List ℕ := [309, 310, 312, 313, 315, 317, 318, 320, 321, 323]
private def wC20 : List ℕ := [325, 326, 328, 330, 331, 333, 334, 336, 338, 339]
private def wC21 : List ℕ := [341, 343, 344, 346, 347, 349, 351, 352, 354, 355]
private def wC22 : List ℕ := [357, 359, 360, 362, 364, 365, 367, 368, 370, 372]
private def wC23 : List ℕ := [373, 375, 377, 378, 380, 381, 383, 385, 386, 388]
private def wC24 : List ℕ := [389, 391, 393, 394, 396, 398, 399, 401, 402, 404]
private def wC25 : List ℕ := [406, 407, 409, 410, 412, 414, 415, 417, 419, 420]
private def wC26 : List ℕ := [422, 423, 425, 427, 428, 430, 432, 433, 435, 436]
private def wC27 : List ℕ := [438, 440, 441, 443, 444, 446, 448, 449, 451, 453]
private def wC28 : List ℕ := [454, 456, 457, 459, 461, 462, 464, 465, 467, 469]
private def wC29 : List ℕ := [470, 472, 474, 475, 477, 478, 480, 482, 483, 485]
private def wC30 : List ℕ := [487, 488, 490, 491, 493, 495, 496, 498, 499, 501]
private def wC31 : List ℕ := [503, 504, 506, 508, 509, 511, 512, 514, 516, 517]
private def wC32 : List ℕ := [519, 521, 522, 524, 525, 527, 529, 530, 532, 533]
private def wC33 : List ℕ := [535, 537, 538, 540, 542, 543, 545, 546, 548, 550]
private def wC34 : List ℕ := [551, 553, 554, 556, 558, 559, 561, 563, 564, 566]
private def wC35 : List ℕ := [567, 569, 571, 572, 574, 576, 577, 579, 580, 582]
private def wC36 : List ℕ := [584, 585, 587, 588, 590, 592, 593, 595, 597, 598]
private def wC37 : List ℕ := [600, 601, 603, 605, 606, 608, 609, 611, 613, 614]
private def wC38 : List ℕ := [616, 618, 619, 621, 622, 624, 626, 627, 629, 631]
private def wC39 : List ℕ := [632, 634, 635, 637, 639, 640, 642, 643, 645, 647]

private lemma tw0 : checkChunk wC0 0 = true := by decide
private lemma tw1 : checkChunk wC1 10 = true := by decide
private lemma tw2 : checkChunk wC2 20 = true := by decide
private lemma tw3 : checkChunk wC3 30 = true := by decide
private lemma tw4 : checkChunk wC4 40 = true := by decide
private lemma tw5 : checkChunk wC5 50 = true := by decide
private lemma tw6 : checkChunk wC6 60 = true := by decide
private lemma tw7 : checkChunk wC7 70 = true := by decide
private lemma tw8 : checkChunk wC8 80 = true := by decide
private lemma tw9 : checkChunk wC9 90 = true := by decide
private lemma tw10 : checkChunk wC10 100 = true := by decide
private lemma tw11 : checkChunk wC11 110 = true := by decide
private lemma tw12 : checkChunk wC12 120 = true := by decide
private lemma tw13 : checkChunk wC13 130 = true := by decide
private lemma tw14 : checkChunk wC14 140 = true := by decide
private lemma tw15 : checkChunk wC15 150 = true := by decide
private lemma tw16 : checkChunk wC16 160 = true := by decide
private lemma tw17 : checkChunk wC17 170 = true := by decide
private lemma tw18 : checkChunk wC18 180 = true := by decide
private lemma tw19 : checkChunk wC19 190 = true := by decide
private lemma tw20 : checkChunk wC20 200 = true := by decide
private lemma tw21 : checkChunk wC21 210 = true := by decide
private lemma tw22 : checkChunk wC22 220 = true := by decide
private lemma tw23 : checkChunk wC23 230 = true := by decide
private lemma tw24 : checkChunk wC24 240 = true := by decide
private lemma tw25 : checkChunk wC25 250 = true := by decide
private lemma tw26 : checkChunk wC26 260 = true := by decide
private lemma tw27 : checkChunk wC27 270 = true := by decide
private lemma tw28 : checkChunk wC28 280 = true := by decide
private lemma tw29 : checkChunk wC29 290 = true := by decide
private lemma tw30 : checkChunk wC30 300 = true := by decide
private lemma tw31 : checkChunk wC31 310 = true := by decide
private lemma tw32 : checkChunk wC32 320 = true := by decide
private lemma tw33 : checkChunk wC33 330 = true := by decide
private lemma tw34 : checkChunk wC34 340 = true := by decide
private lemma tw35 : checkChunk wC35 350 = true := by decide
private lemma tw36 : checkChunk wC36 360 = true := by decide
private lemma tw37 : checkChunk wC37 370 = true := by decide
private lemma tw38 : checkChunk wC38 380 = true := by decide
private lemma tw39 : checkChunk wC39 390 = true := by decide

private lemma tlo39 : hornerLo P85 ((digits : ℤ) + 1) S92 (0) (revDiffsAux 631 1 [] wC39) = -273747181057203662650321702133824726160858538766983956819826067774409884468507959939107861 := by decide
private lemma tlo38 : hornerLo P85 ((digits : ℤ) + 1) S92 (-273747181057203662650321702133824726160858538766983956819826067774409884468507959939107861) (revDiffsAux 614 1 [] wC38) = 80157640025505662608432369599414613016368369964709525428315312733678926503497035703596611998 := by decide
private lemma tlo37 : hornerLo P85 ((digits : ℤ) + 1) S92 (80157640025505662608432369599414613016368369964709525428315312733678926503497035703596611998) (revDiffsAux 598 1 [] wC37) = 168884863322674461798709324439104603288586590684478411060751847970026062933858723719312873366 := by decide
private lemma tlo36 : hornerLo P85 ((digits : ℤ) + 1) S92 (168884863322674461798709324439104603288586590684478411060751847970026062933858723719312873366) (revDiffsAux 582 1 [] wC36) = 202402163018973983822801625558733712615252611949745047519788020637991120833499977490556392154 := by decide
private lemma tlo35 : hornerLo P85 ((digits : ℤ) + 1) S92 (202402163018973983822801625558733712615252611949745047519788020637991120833499977490556392154) (revDiffsAux 566 1 [] wC35) = 40965512674303768955820297102420279232839093513053628658116954150436904125639283703830814991 := by decide
private lemma tlo34 : hornerLo P85 ((digits : ℤ) + 1) S92 (40965512674303768955820297102420279232839093513053628658116954150436904125639283703830814991) (revDiffsAux 550 1 [] wC34) = -4118421365907905084337386134536251251226748892857797865144518359108648486593870698910475033 := by decide
private lemma tlo33 : hornerLo P85 ((digits : ℤ) + 1) S92 (-4118421365907905084337386134536251251226748892857797865144518359108648486593870698910475033) (revDiffsAux 533 1 [] wC33) = 99704444136848623799865854030878123249805159313790754275557803565383219016546229403710534137 := by decide
private lemma tlo32 : hornerLo P85 ((digits : ℤ) + 1) S92 (99704444136848623799865854030878123249805159313790754275557803565383219016546229403710534137) (revDiffsAux 517 1 [] wC32) = 81581416995156433534224222951217041143011142581627204727874103852448045405024981317072622584 := by decide
private lemma tlo31 : hornerLo P85 ((digits : ℤ) + 1) S92 (81581416995156433534224222951217041143011142581627204727874103852448045405024981317072622584) (revDiffsAux 501 1 [] wC31) = 168892402789024640099220827725746638920204301321336831666182352513777976586608403915464434484 := by decide
private lemma tlo30 : hornerLo P85 ((digits : ℤ) + 1) S92 (168892402789024640099220827725746638920204301321336831666182352513777976586608403915464434484) (revDiffsAux 485 1 [] wC30) = 199997356644533613442072488562139716746185504431970773097164261367286680037967282933762246767 := by decide
private lemma tlo29 : hornerLo P85 ((digits : ℤ) + 1) S92 (199997356644533613442072488562139716746185504431970773097164261367286680037967282933762246767) (revDiffsAux 469 1 [] wC29) = 52538356960091498844723932280638781061836133070332604466320794203199696444854337412933518322 := by decide
private lemma tlo28 : hornerLo P85 ((digits : ℤ) + 1) S92 (52538356960091498844723932280638781061836133070332604466320794203199696444854337412933518322) (revDiffsAux 453 1 [] wC28) = 4464352657536308690564472719552725598478632731423108104479453248591439424709579378871744 := by decide
private lemma tlo27 : hornerLo P85 ((digits : ℤ) + 1) S92 (4464352657536308690564472719552725598478632731423108104479453248591439424709579378871744) (revDiffsAux 436 1 [] wC27) = 80159113266428493574250883886465897807786295312701824730052356037873547905812044893967798752 := by decide
private lemma tlo26 : hornerLo P85 ((digits : ℤ) + 1) S92 (80159113266428493574250883886465897807786295312701824730052356037873547905812044893967798752) (revDiffsAux 420 1 [] wC26) = 175744610185080413118512747736365339201371508221098335553773477689301551816275683498390014841 := by decide
private lemma tlo25 : hornerLo P85 ((digits : ℤ) + 1) S92 (175744610185080413118512747736365339201371508221098335553773477689301551816275683498390014841) (revDiffsAux 404 1 [] wC25) = 202438488111837746484267545206304944595441790113142876037164218958805132507568055743822913770 := by decide
private lemma tlo24 : hornerLo P85 ((digits : ℤ) + 1) S92 (202438488111837746484267545206304944595441790113142876037164218958805132507568055743822913770) (revDiffsAux 388 1 [] wC24) = 40965705030144010294149538913986628405479170249074329357883935546589949984806032087502928621 := by decide
private lemma tlo23 : hornerLo P85 ((digits : ℤ) + 1) S92 (40965705030144010294149538913986628405479170249074329357883935546589949984806032087502928621) (revDiffsAux 372 1 [] wC23) = 51696220999531561303793337944074982634209036189908564749904895983963401146174253780152705253 := by decide
private lemma tlo22 : hornerLo P85 ((digits : ℤ) + 1) S92 (51696220999531561303793337944074982634209036189908564749904895983963401146174253780152705253) (revDiffsAux 355 1 [] wC22) = 100000004907202062971789794268185797919135716247023567125434221889903973349083733456948020564 := by decide
private lemma tlo21 : hornerLo P85 ((digits : ℤ) + 1) S92 (100000004907202062971789794268185797919135716247023567125434221889903973349083733456948020564) (revDiffsAux 339 1 [] wC21) = 81582982107199971584646560903262899013087753411982782411992069994873297441052282077834175461 := by decide
private lemma tlo20 : hornerLo P85 ((digits : ℤ) + 1) S92 (81582982107199971584646560903262899013087753411982782411992069994873297441052282077834175461) (revDiffsAux 323 1 [] wC20) = 168892411076916520671147195050269209284104523750480946394656138626942247262103993570376023849 := by decide
private lemma tlo19 : hornerLo P85 ((digits : ℤ) + 1) S92 (168892411076916520671147195050269209284104523750480946394656138626942247262103993570376023849) (revDiffsAux 307 1 [] wC19) = 199997356688421303213325671727941299185263989413041647982615440194717977133621138712500179963 := by decide
private lemma tlo18 : hornerLo P85 ((digits : ℤ) + 1) S92 (199997356688421303213325671727941299185263989413041647982615440194717977133621138712500179963) (revDiffsAux 291 1 [] wC18) = 52538356960323901648864379632780742709596552886798614310917734074737473117254347599139369471 := by decide
private lemma tlo17 : hornerLo P85 ((digits : ℤ) + 1) S92 (52538356960323901648864379632780742709596552886798614310917734074737473117254347599139369471) (revDiffsAux 275 1 [] wC17) = -4057138544279104786366718066513918802753706161392142208880127766155077398481514909054963884 := by decide
private lemma tlo16 : hornerLo P85 ((digits : ℤ) + 1) S92 (-4057138544279104786366718066513918802753706161392142208880127766155077398481514909054963884) (revDiffsAux 258 1 [] wC16) = 80137605460766521347974574709891026491111034839073206228665236224396700092114745327200984623 := by decide
private lemma tlo15 : hornerLo P85 ((digits : ℤ) + 1) S92 (80137605460766521347974574709891026491111034839073206228665236224396700092114745327200984623) (revDiffsAux 242 1 [] wC15) = 175744496292679769506146246419910064721615798311875346410930356770644452099345301615838177135 := by decide
private lemma tlo14 : hornerLo P85 ((digits : ℤ) + 1) S92 (175744496292679769506146246419910064721615798311875346410930356770644452099345301615838177135) (revDiffsAux 226 1 [] wC14) = 202438487508732105293735521293657897810550416459900753830749754136538034523345121670268466116 := by decide
private lemma tlo13 : hornerLo P85 ((digits : ℤ) + 1) S92 (202438487508732105293735521293657897810550416459900753830749754136538034523345121670268466116) (revDiffsAux 210 1 [] wC13) = 40965705026950325620015463182123809294252873474929876933389575014238358304144551497932299614 := by decide
private lemma tlo12 : hornerLo P85 ((digits : ℤ) + 1) S92 (40965705026950325620015463182123809294252873474929876933389575014238358304144551497932299614) (revDiffsAux 194 1 [] wC12) = 51696220999514649470938210277056412434162574546028515307962419105044817015184599234511732672 := by decide
private lemma tlo11 : hornerLo P85 ((digits : ℤ) + 1) S92 (51696220999514649470938210277056412434162574546028515307962419105044817015184599234511732672) (revDiffsAux 177 1 [] wC11) = 100000004907201973416896402257475441265895148509708589839549049365969338416434465894230401663 := by decide
private lemma tlo10 : hornerLo P85 ((digits : ℤ) + 1) S92 (100000004907201973416896402257475441265895148509708589839549049365969338416434465894230401663) (revDiffsAux 161 1 [] wC10) = 81582982107199971110417717752018295913832004602888820123132906098714128694200799996017668469 := by decide
private lemma tlo9 : hornerLo P85 ((digits : ℤ) + 1) S92 (81582982107199971110417717752018295913832004602888820123132906098714128694200799996017668469) (revDiffsAux 145 1 [] wC9) = 168892411076916520668635964371984121798885528747181509452754177770449535588256001369032117953 := by decide
private lemma tlo8 : hornerLo P85 ((digits : ℤ) + 1) S92 (168892411076916520668635964371984121798885528747181509452754177770449535588256001369032117953) (revDiffsAux 129 1 [] wC8) = 202402202987340055495170686150703471021857177529507458091614818066381226294821162506986896206 := by decide
private lemma tlo7 : hornerLo P85 ((digits : ℤ) + 1) S92 (202402202987340055495170686150703471021857177529507458091614818066381226294821162506986896206) (revDiffsAux 113 1 [] wC7) = 52551091579674077019986020332153508904469983667242933796973058742604829969899826937730671624 := by decide
private lemma tlo6 : hornerLo P85 ((digits : ℤ) + 1) S92 (52551091579674077019986020332153508904469983667242933796973058742604829969899826937730671624) (revDiffsAux 97 1 [] wC6) = -4057071109395608583384696928101326695033206740150537502022570134488036014216029540547843874 := by decide
private lemma tlo5 : hornerLo P85 ((digits : ℤ) + 1) S92 (-4057071109395608583384696928101326695033206740150537502022570134488036014216029540547843874) (revDiffsAux 80 1 [] wC5) = 80137605817861098508134861980837648767348936146578722827394556075232295321360189970112048483 := by decide
private lemma tlo4 : hornerLo P85 ((digits : ℤ) + 1) S92 (80137605817861098508134861980837648767348936146578722827394556075232295321360189970112048483) (revDiffsAux 64 1 [] wC4) = 175744496294570727574523033500427312060591388255136154234474249734733009937114430331813806683 := by decide
private lemma tlo3 : hornerLo P85 ((digits : ℤ) + 1) S92 (175744496294570727574523033500427312060591388255136154234474249734733009937114430331813806683) (revDiffsAux 48 1 [] wC3) = 169391033812661187205742504622598284585054938873851396843001719443336949253140711218028125511 := by decide
private lemma tlo2 : hornerLo P85 ((digits : ℤ) + 1) S92 (169391033812661187205742504622598284585054938873851396843001719443336949253140711218028125511) (revDiffsAux 32 1 [] wC2) = 40790705592058695730349476341403783073819829308317904200041687300532397204901172606276522359 := by decide
private lemma tlo1 : hornerLo P85 ((digits : ℤ) + 1) S92 (40790705592058695730349476341403783073819829308317904200041687300532397204901172606276522359) (revDiffsAux 16 1 [] wC1) = 51695294307779363649005485032357761934871907848375470057696040645446377914972614826580387608 := by decide
private lemma tlo0 : hornerLo P85 ((digits : ℤ) + 1) S92 (51695294307779363649005485032357761934871907848375470057696040645446377914972614826580387608) (revDiffsAux 0 1 [] wC0) = 2444474 := by decide

private lemma thi39 : hornerLo P85 (digits : ℤ) S92 (0) (revDiffsAux 631 (-1) [] wC39) = 273747181057203662650321702133824726160858538766983956819826067774409884468507959943192998 := by decide
private lemma thi38 : hornerLo P85 (digits : ℤ) S92 (273747181057203662650321702133824726160858538766983956819826067774409884468507959943192998) (revDiffsAux 614 (-1) [] wC38) = -80157640025505662608432369599414613016368369964709525428315312733678926503497035703587439276 := by decide
private lemma thi37 : hornerLo P85 (digits : ℤ) S92 (-80157640025505662608432369599414613016368369964709525428315312733678926503497035703587439276) (revDiffsAux 598 (-1) [] wC37) = -168884863322674461798709324439104603288586590684478411060751847970026062933858723719309471649 := by decide
private lemma thi36 : hornerLo P85 (digits : ℤ) S92 (-168884863322674461798709324439104603288586590684478411060751847970026062933858723719309471649) (revDiffsAux 582 (-1) [] wC36) = -202402163018973983822801625558733712615252611949745047519788020637991120833499977490559897032 := by decide
private lemma thi35 : hornerLo P85 (digits : ℤ) S92 (-202402163018973983822801625558733712615252611949745047519788020637991120833499977490559897032) (revDiffsAux 566 (-1) [] wC35) = -40965512674303768955820297102420279232839093513053628658116954150436904125639283703829763723 := by decide
private lemma thi34 : hornerLo P85 (digits : ℤ) S92 (-40965512674303768955820297102420279232839093513053628658116954150436904125639283703829763723) (revDiffsAux 550 (-1) [] wC34) = 4118421365907905084337386134536251251226748892857797865144518359108648486593870698916210122 := by decide
private lemma thi33 : hornerLo P85 (digits : ℤ) S92 (4118421365907905084337386134536251251226748892857797865144518359108648486593870698916210122) (revDiffsAux 533 (-1) [] wC33) = -99704444136848623799865854030878123249805159313790754275557803565383219016546229403706405719 := by decide
private lemma thi32 : hornerLo P85 (digits : ℤ) S92 (-99704444136848623799865854030878123249805159313790754275557803565383219016546229403706405719) (revDiffsAux 517 (-1) [] wC32) = -81581416995156433534224222951217041143011142581627204727874103852448045405024981317064239687 := by decide
private lemma thi31 : hornerLo P85 (digits : ℤ) S92 (-81581416995156433534224222951217041143011142581627204727874103852448045405024981317064239687) (revDiffsAux 501 (-1) [] wC31) = -168892402789024640099220827725746638920204301321336831666182352513777976586608403915461041413 := by decide
private lemma thi30 : hornerLo P85 (digits : ℤ) S92 (-168892402789024640099220827725746638920204301321336831666182352513777976586608403915461041413) (revDiffsAux 485 (-1) [] wC30) = -199997356644533613442072488562139716746185504431970773097164261367286680037967282933764559647 := by decide
private lemma thi29 : hornerLo P85 (digits : ℤ) S92 (-199997356644533613442072488562139716746185504431970773097164261367286680037967282933764559647) (revDiffsAux 469 (-1) [] wC29) = -52538356960091498844723932280638781061836133070332604466320794203199696444854337412936138183 := by decide
private lemma thi28 : hornerLo P85 (digits : ℤ) S92 (-52538356960091498844723932280638781061836133070332604466320794203199696444854337412936138183) (revDiffsAux 453 (-1) [] wC28) = -4464352657536308690564472719552725598478632731423108104479453248591439424709579374965208 := by decide
private lemma thi27 : hornerLo P85 (digits : ℤ) S92 (-4464352657536308690564472719552725598478632731423108104479453248591439424709579374965208) (revDiffsAux 436 (-1) [] wC27) = -80159113266428493574250883886465897807786295312701824730052356037873547905812044893958627849 := by decide
private lemma thi26 : hornerLo P85 (digits : ℤ) S92 (-80159113266428493574250883886465897807786295312701824730052356037873547905812044893958627849) (revDiffsAux 420 (-1) [] wC26) = -175744610185080413118512747736365339201371508221098335553773477689301551816275683498389201148 := by decide
private lemma thi25 : hornerLo P85 (digits : ℤ) S92 (-175744610185080413118512747736365339201371508221098335553773477689301551816275683498389201148) (revDiffsAux 404 (-1) [] wC25) = -202438488111837746484267545206304944595441790113142876037164218958805132507568055743826453861 := by decide
private lemma thi24 : hornerLo P85 (digits : ℤ) S92 (-202438488111837746484267545206304944595441790113142876037164218958805132507568055743826453861) (revDiffsAux 388 (-1) [] wC24) = -40965705030144010294149538913986628405479170249074329357883935546589949984806032087501877654 := by decide
private lemma thi23 : hornerLo P85 (digits : ℤ) S92 (-40965705030144010294149538913986628405479170249074329357883935546589949984806032087501877654) (revDiffsAux 372 (-1) [] wC23) = -51696220999531561303793337944074982634209036189908564749904895983963401146174253780154808678 := by decide
private lemma thi22 : hornerLo P85 (digits : ℤ) S92 (-51696220999531561303793337944074982634209036189908564749904895983963401146174253780154808678) (revDiffsAux 355 (-1) [] wC22) = -100000004907202062971789794268185797919135716247023567125434221889903973349083733456944108653 := by decide
private lemma thi21 : hornerLo P85 (digits : ℤ) S92 (-100000004907202062971789794268185797919135716247023567125434221889903973349083733456944108653) (revDiffsAux 339 (-1) [] wC21) = -81582982107199971584646560903262899013087753411982782411992069994873297441052282077825794638 := by decide
private lemma thi20 : hornerLo P85 (digits : ℤ) S92 (-81582982107199971584646560903262899013087753411982782411992069994873297441052282077825794638) (revDiffsAux 323 (-1) [] wC20) = -168892411076916520671147195050269209284104523750480946394656138626942247262103993570372630793 := by decide
private lemma thi19 : hornerLo P85 (digits : ℤ) S92 (-168892411076916520671147195050269209284104523750480946394656138626942247262103993570372630793) (revDiffsAux 307 (-1) [] wC19) = -199997356688421303213325671727941299185263989413041647982615440194717977133621138712502492843 := by decide
private lemma thi18 : hornerLo P85 (digits : ℤ) S92 (-199997356688421303213325671727941299185263989413041647982615440194717977133621138712502492843) (revDiffsAux 291 (-1) [] wC18) = -52538356960323901648864379632780742709596552886798614310917734074737473117254347599141989332 := by decide
private lemma thi17 : hornerLo P85 (digits : ℤ) S92 (-52538356960323901648864379632780742709596552886798614310917734074737473117254347599141989332) (revDiffsAux 275 (-1) [] wC17) = 4057138544279104786366718066513918802753706161392142208880127766155077398481514909060643248 := by decide
private lemma thi16 : hornerLo P85 (digits : ℤ) S92 (4057138544279104786366718066513918802753706161392142208880127766155077398481514909060643248) (revDiffsAux 258 (-1) [] wC16) = -80137605460766521347974574709891026491111034839073206228665236224396700092114745327191791596 := by decide
private lemma thi15 : hornerLo P85 (digits : ℤ) S92 (-80137605460766521347974574709891026491111034839073206228665236224396700092114745327191791596) (revDiffsAux 242 (-1) [] wC15) = -175744496292679769506146246419910064721615798311875346410930356770644452099345301615837363259 := by decide
private lemma thi14 : hornerLo P85 (digits : ℤ) S92 (-175744496292679769506146246419910064721615798311875346410930356770644452099345301615837363259) (revDiffsAux 226 (-1) [] wC14) = -202438487508732105293735521293657897810550416459900753830749754136538034523345121670272006205 := by decide
private lemma thi13 : hornerLo P85 (digits : ℤ) S92 (-202438487508732105293735521293657897810550416459900753830749754136538034523345121670272006205) (revDiffsAux 210 (-1) [] wC13) = -40965705026950325620015463182123809294252873474929876933389575014238358304144551497931248647 := by decide
private lemma thi12 : hornerLo P85 (digits : ℤ) S92 (-40965705026950325620015463182123809294252873474929876933389575014238358304144551497931248647) (revDiffsAux 194 (-1) [] wC12) = -51696220999514649470938210277056412434162574546028515307962419105044817015184599234513836096 := by decide
private lemma thi11 : hornerLo P85 (digits : ℤ) S92 (-51696220999514649470938210277056412434162574546028515307962419105044817015184599234513836096) (revDiffsAux 177 (-1) [] wC11) = -100000004907201973416896402257475441265895148509708589839549049365969338416434465894226489752 := by decide
private lemma thi10 : hornerLo P85 (digits : ℤ) S92 (-100000004907201973416896402257475441265895148509708589839549049365969338416434465894226489752) (revDiffsAux 161 (-1) [] wC10) = -81582982107199971110417717752018295913832004602888820123132906098714128694200799996009287646 := by decide
private lemma thi9 : hornerLo P85 (digits : ℤ) S92 (-81582982107199971110417717752018295913832004602888820123132906098714128694200799996009287646) (revDiffsAux 145 (-1) [] wC9) = -168892411076916520668635964371984121798885528747181509452754177770449535588256001369028724897 := by decide
private lemma thi8 : hornerLo P85 (digits : ℤ) S92 (-168892411076916520668635964371984121798885528747181509452754177770449535588256001369028724897) (revDiffsAux 129 (-1) [] wC8) = -202402202987340055495170686150703471021857177529507458091614818066381226294821162506990401154 := by decide
private lemma thi7 : hornerLo P85 (digits : ℤ) S92 (-202402202987340055495170686150703471021857177529507458091614818066381226294821162506990401154) (revDiffsAux 113 (-1) [] wC7) = -52551091579674077019986020332153508904469983667242933796973058742604829969899826937733305337 := by decide
private lemma thi6 : hornerLo P85 (digits : ℤ) S92 (-52551091579674077019986020332153508904469983667242933796973058742604829969899826937733305337) (revDiffsAux 97 (-1) [] wC6) = 4057071109395608583384696928101326695033206740150537502022570134488036014216029540553523125 := by decide
private lemma thi5 : hornerLo P85 (digits : ℤ) S92 (4057071109395608583384696928101326695033206740150537502022570134488036014216029540553523125) (revDiffsAux 80 (-1) [] wC5) = -80137605817861098508134861980837648767348936146578722827394556075232295321360189970102855457 := by decide
private lemma thi4 : hornerLo P85 (digits : ℤ) S92 (-80137605817861098508134861980837648767348936146578722827394556075232295321360189970102855457) (revDiffsAux 64 (-1) [] wC4) = -175744496294570727574523033500427312060591388255136154234474249734733009937114430331812992806 := by decide
private lemma thi3 : hornerLo P85 (digits : ℤ) S92 (-175744496294570727574523033500427312060591388255136154234474249734733009937114430331812992806) (revDiffsAux 48 (-1) [] wC3) = -169391033812661187205742504622598284585054938873851396843001719443336949253140711218025067757 := by decide
private lemma thi2 : hornerLo P85 (digits : ℤ) S92 (-169391033812661187205742504622598284585054938873851396843001719443336949253140711218025067757) (revDiffsAux 32 (-1) [] wC2) = -40790705592058695730349476341403783073819829308317904200041687300532397204901172606275332837 := by decide
private lemma thi1 : hornerLo P85 (digits : ℤ) S92 (-40790705592058695730349476341403783073819829308317904200041687300532397204901172606275332837) (revDiffsAux 16 (-1) [] wC1) = -51695294307779363649005485032357761934871907848375470057696040645446377914972614826582489750 := by decide
private lemma thi0 : hornerLo P85 (digits : ℤ) S92 (-51695294307779363649005485032357761934871907848375470057696040645446377914972614826582489750) (revDiffsAux 0 (-1) [] wC0) = 1467447 := by decide

private lemma hwp1 : weight 9 = (16 : ℝ) := by
  simpa [wC0] using checkChunk_sound wC0 0 tw0 9 (by decide)
private lemma hwp2 : weight 19 = (32 : ℝ) := by
  simpa [wC1] using checkChunk_sound wC1 10 tw1 9 (by decide)
private lemma hwp3 : weight 29 = (48 : ℝ) := by
  simpa [wC2] using checkChunk_sound wC2 20 tw2 9 (by decide)
private lemma hwp4 : weight 39 = (64 : ℝ) := by
  simpa [wC3] using checkChunk_sound wC3 30 tw3 9 (by decide)
private lemma hwp5 : weight 49 = (80 : ℝ) := by
  simpa [wC4] using checkChunk_sound wC4 40 tw4 9 (by decide)
private lemma hwp6 : weight 59 = (97 : ℝ) := by
  simpa [wC5] using checkChunk_sound wC5 50 tw5 9 (by decide)
private lemma hwp7 : weight 69 = (113 : ℝ) := by
  simpa [wC6] using checkChunk_sound wC6 60 tw6 9 (by decide)
private lemma hwp8 : weight 79 = (129 : ℝ) := by
  simpa [wC7] using checkChunk_sound wC7 70 tw7 9 (by decide)
private lemma hwp9 : weight 89 = (145 : ℝ) := by
  simpa [wC8] using checkChunk_sound wC8 80 tw8 9 (by decide)
private lemma hwp10 : weight 99 = (161 : ℝ) := by
  simpa [wC9] using checkChunk_sound wC9 90 tw9 9 (by decide)
private lemma hwp11 : weight 109 = (177 : ℝ) := by
  simpa [wC10] using checkChunk_sound wC10 100 tw10 9 (by decide)
private lemma hwp12 : weight 119 = (194 : ℝ) := by
  simpa [wC11] using checkChunk_sound wC11 110 tw11 9 (by decide)
private lemma hwp13 : weight 129 = (210 : ℝ) := by
  simpa [wC12] using checkChunk_sound wC12 120 tw12 9 (by decide)
private lemma hwp14 : weight 139 = (226 : ℝ) := by
  simpa [wC13] using checkChunk_sound wC13 130 tw13 9 (by decide)
private lemma hwp15 : weight 149 = (242 : ℝ) := by
  simpa [wC14] using checkChunk_sound wC14 140 tw14 9 (by decide)
private lemma hwp16 : weight 159 = (258 : ℝ) := by
  simpa [wC15] using checkChunk_sound wC15 150 tw15 9 (by decide)
private lemma hwp17 : weight 169 = (275 : ℝ) := by
  simpa [wC16] using checkChunk_sound wC16 160 tw16 9 (by decide)
private lemma hwp18 : weight 179 = (291 : ℝ) := by
  simpa [wC17] using checkChunk_sound wC17 170 tw17 9 (by decide)
private lemma hwp19 : weight 189 = (307 : ℝ) := by
  simpa [wC18] using checkChunk_sound wC18 180 tw18 9 (by decide)
private lemma hwp20 : weight 199 = (323 : ℝ) := by
  simpa [wC19] using checkChunk_sound wC19 190 tw19 9 (by decide)
private lemma hwp21 : weight 209 = (339 : ℝ) := by
  simpa [wC20] using checkChunk_sound wC20 200 tw20 9 (by decide)
private lemma hwp22 : weight 219 = (355 : ℝ) := by
  simpa [wC21] using checkChunk_sound wC21 210 tw21 9 (by decide)
private lemma hwp23 : weight 229 = (372 : ℝ) := by
  simpa [wC22] using checkChunk_sound wC22 220 tw22 9 (by decide)
private lemma hwp24 : weight 239 = (388 : ℝ) := by
  simpa [wC23] using checkChunk_sound wC23 230 tw23 9 (by decide)
private lemma hwp25 : weight 249 = (404 : ℝ) := by
  simpa [wC24] using checkChunk_sound wC24 240 tw24 9 (by decide)
private lemma hwp26 : weight 259 = (420 : ℝ) := by
  simpa [wC25] using checkChunk_sound wC25 250 tw25 9 (by decide)
private lemma hwp27 : weight 269 = (436 : ℝ) := by
  simpa [wC26] using checkChunk_sound wC26 260 tw26 9 (by decide)
private lemma hwp28 : weight 279 = (453 : ℝ) := by
  simpa [wC27] using checkChunk_sound wC27 270 tw27 9 (by decide)
private lemma hwp29 : weight 289 = (469 : ℝ) := by
  simpa [wC28] using checkChunk_sound wC28 280 tw28 9 (by decide)
private lemma hwp30 : weight 299 = (485 : ℝ) := by
  simpa [wC29] using checkChunk_sound wC29 290 tw29 9 (by decide)
private lemma hwp31 : weight 309 = (501 : ℝ) := by
  simpa [wC30] using checkChunk_sound wC30 300 tw30 9 (by decide)
private lemma hwp32 : weight 319 = (517 : ℝ) := by
  simpa [wC31] using checkChunk_sound wC31 310 tw31 9 (by decide)
private lemma hwp33 : weight 329 = (533 : ℝ) := by
  simpa [wC32] using checkChunk_sound wC32 320 tw32 9 (by decide)
private lemma hwp34 : weight 339 = (550 : ℝ) := by
  simpa [wC33] using checkChunk_sound wC33 330 tw33 9 (by decide)
private lemma hwp35 : weight 349 = (566 : ℝ) := by
  simpa [wC34] using checkChunk_sound wC34 340 tw34 9 (by decide)
private lemma hwp36 : weight 359 = (582 : ℝ) := by
  simpa [wC35] using checkChunk_sound wC35 350 tw35 9 (by decide)
private lemma hwp37 : weight 369 = (598 : ℝ) := by
  simpa [wC36] using checkChunk_sound wC36 360 tw36 9 (by decide)
private lemma hwp38 : weight 379 = (614 : ℝ) := by
  simpa [wC37] using checkChunk_sound wC37 370 tw37 9 (by decide)
private lemma hwp39 : weight 389 = (631 : ℝ) := by
  simpa [wC38] using checkChunk_sound wC38 380 tw38 9 (by decide)

private lemma rLo_band3
    (hinit : ((0 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 400) :
    ((199997356644533613442072488562139716746185504431970773097164261367286680037967282933762246767 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 300 := by
  have hP85_nn : (0 : ℤ) ≤ P85 := by decide
  have hd1_pos : (0 : ℤ) < (digits : ℤ) + 1 := by decide
  have hS92_pos : (0 : ℤ) < S92 := by decide
  have hlo39 : ((-273747181057203662650321702133824726160858538766983956819826067774409884468507959939107861 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 390 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC39 390 631 1 (0) (-273747181057203662650321702133824726160858538766983956819826067774409884468507959939107861) (by decide) ⟨195, by omega⟩ (Or.inr ⟨by omega, hwp39⟩) tw39 (by omega) tlo39 hinit
  have hlo38 : ((80157640025505662608432369599414613016368369964709525428315312733678926503497035703596611998 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 380 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC38 380 614 1 (-273747181057203662650321702133824726160858538766983956819826067774409884468507959939107861) (80157640025505662608432369599414613016368369964709525428315312733678926503497035703596611998) (by decide) ⟨190, by omega⟩ (Or.inr ⟨by omega, hwp38⟩) tw38 (by omega) tlo38 hlo39
  have hlo37 : ((168884863322674461798709324439104603288586590684478411060751847970026062933858723719312873366 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 370 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC37 370 598 1 (80157640025505662608432369599414613016368369964709525428315312733678926503497035703596611998) (168884863322674461798709324439104603288586590684478411060751847970026062933858723719312873366) (by decide) ⟨185, by omega⟩ (Or.inr ⟨by omega, hwp37⟩) tw37 (by omega) tlo37 hlo38
  have hlo36 : ((202402163018973983822801625558733712615252611949745047519788020637991120833499977490556392154 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 360 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC36 360 582 1 (168884863322674461798709324439104603288586590684478411060751847970026062933858723719312873366) (202402163018973983822801625558733712615252611949745047519788020637991120833499977490556392154) (by decide) ⟨180, by omega⟩ (Or.inr ⟨by omega, hwp36⟩) tw36 (by omega) tlo36 hlo37
  have hlo35 : ((40965512674303768955820297102420279232839093513053628658116954150436904125639283703830814991 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 350 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC35 350 566 1 (202402163018973983822801625558733712615252611949745047519788020637991120833499977490556392154) (40965512674303768955820297102420279232839093513053628658116954150436904125639283703830814991) (by decide) ⟨175, by omega⟩ (Or.inr ⟨by omega, hwp35⟩) tw35 (by omega) tlo35 hlo36
  have hlo34 : ((-4118421365907905084337386134536251251226748892857797865144518359108648486593870698910475033 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 340 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC34 340 550 1 (40965512674303768955820297102420279232839093513053628658116954150436904125639283703830814991) (-4118421365907905084337386134536251251226748892857797865144518359108648486593870698910475033) (by decide) ⟨170, by omega⟩ (Or.inr ⟨by omega, hwp34⟩) tw34 (by omega) tlo34 hlo35
  have hlo33 : ((99704444136848623799865854030878123249805159313790754275557803565383219016546229403710534137 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 330 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC33 330 533 1 (-4118421365907905084337386134536251251226748892857797865144518359108648486593870698910475033) (99704444136848623799865854030878123249805159313790754275557803565383219016546229403710534137) (by decide) ⟨165, by omega⟩ (Or.inr ⟨by omega, hwp33⟩) tw33 (by omega) tlo33 hlo34
  have hlo32 : ((81581416995156433534224222951217041143011142581627204727874103852448045405024981317072622584 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 320 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC32 320 517 1 (99704444136848623799865854030878123249805159313790754275557803565383219016546229403710534137) (81581416995156433534224222951217041143011142581627204727874103852448045405024981317072622584) (by decide) ⟨160, by omega⟩ (Or.inr ⟨by omega, hwp32⟩) tw32 (by omega) tlo32 hlo33
  have hlo31 : ((168892402789024640099220827725746638920204301321336831666182352513777976586608403915464434484 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 310 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC31 310 501 1 (81581416995156433534224222951217041143011142581627204727874103852448045405024981317072622584) (168892402789024640099220827725746638920204301321336831666182352513777976586608403915464434484) (by decide) ⟨155, by omega⟩ (Or.inr ⟨by omega, hwp31⟩) tw31 (by omega) tlo31 hlo32
  have hlo30 : ((199997356644533613442072488562139716746185504431970773097164261367286680037967282933762246767 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 300 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC30 300 485 1 (168892402789024640099220827725746638920204301321336831666182352513777976586608403915464434484) (199997356644533613442072488562139716746185504431970773097164261367286680037967282933762246767) (by decide) ⟨150, by omega⟩ (Or.inr ⟨by omega, hwp30⟩) tw30 (by omega) tlo30 hlo31
  exact hlo30
private lemma rHi_band3
    (hinit : ((0 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 400) :
    ((-199997356644533613442072488562139716746185504431970773097164261367286680037967282933764559647 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 300 := by
  have hP85_nn : (0 : ℤ) ≤ P85 := by decide
  have hd_pos : (0 : ℤ) < (digits : ℤ) := by decide
  have hS92_pos : (0 : ℤ) < S92 := by decide
  have hhi39 : ((273747181057203662650321702133824726160858538766983956819826067774409884468507959943192998 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 390 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC39 390 631 (-1) (0) (273747181057203662650321702133824726160858538766983956819826067774409884468507959943192998) (by decide) ⟨195, by omega⟩ (Or.inr ⟨by omega, hwp39⟩) tw39 (by omega) thi39 hinit
  have hhi38 : ((-80157640025505662608432369599414613016368369964709525428315312733678926503497035703587439276 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 380 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC38 380 614 (-1) (273747181057203662650321702133824726160858538766983956819826067774409884468507959943192998) (-80157640025505662608432369599414613016368369964709525428315312733678926503497035703587439276) (by decide) ⟨190, by omega⟩ (Or.inr ⟨by omega, hwp38⟩) tw38 (by omega) thi38 hhi39
  have hhi37 : ((-168884863322674461798709324439104603288586590684478411060751847970026062933858723719309471649 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 370 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC37 370 598 (-1) (-80157640025505662608432369599414613016368369964709525428315312733678926503497035703587439276) (-168884863322674461798709324439104603288586590684478411060751847970026062933858723719309471649) (by decide) ⟨185, by omega⟩ (Or.inr ⟨by omega, hwp37⟩) tw37 (by omega) thi37 hhi38
  have hhi36 : ((-202402163018973983822801625558733712615252611949745047519788020637991120833499977490559897032 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 360 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC36 360 582 (-1) (-168884863322674461798709324439104603288586590684478411060751847970026062933858723719309471649) (-202402163018973983822801625558733712615252611949745047519788020637991120833499977490559897032) (by decide) ⟨180, by omega⟩ (Or.inr ⟨by omega, hwp36⟩) tw36 (by omega) thi36 hhi37
  have hhi35 : ((-40965512674303768955820297102420279232839093513053628658116954150436904125639283703829763723 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 350 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC35 350 566 (-1) (-202402163018973983822801625558733712615252611949745047519788020637991120833499977490559897032) (-40965512674303768955820297102420279232839093513053628658116954150436904125639283703829763723) (by decide) ⟨175, by omega⟩ (Or.inr ⟨by omega, hwp35⟩) tw35 (by omega) thi35 hhi36
  have hhi34 : ((4118421365907905084337386134536251251226748892857797865144518359108648486593870698916210122 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 340 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC34 340 550 (-1) (-40965512674303768955820297102420279232839093513053628658116954150436904125639283703829763723) (4118421365907905084337386134536251251226748892857797865144518359108648486593870698916210122) (by decide) ⟨170, by omega⟩ (Or.inr ⟨by omega, hwp34⟩) tw34 (by omega) thi34 hhi35
  have hhi33 : ((-99704444136848623799865854030878123249805159313790754275557803565383219016546229403706405719 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 330 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC33 330 533 (-1) (4118421365907905084337386134536251251226748892857797865144518359108648486593870698916210122) (-99704444136848623799865854030878123249805159313790754275557803565383219016546229403706405719) (by decide) ⟨165, by omega⟩ (Or.inr ⟨by omega, hwp33⟩) tw33 (by omega) thi33 hhi34
  have hhi32 : ((-81581416995156433534224222951217041143011142581627204727874103852448045405024981317064239687 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 320 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC32 320 517 (-1) (-99704444136848623799865854030878123249805159313790754275557803565383219016546229403706405719) (-81581416995156433534224222951217041143011142581627204727874103852448045405024981317064239687) (by decide) ⟨160, by omega⟩ (Or.inr ⟨by omega, hwp32⟩) tw32 (by omega) thi32 hhi33
  have hhi31 : ((-168892402789024640099220827725746638920204301321336831666182352513777976586608403915461041413 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 310 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC31 310 501 (-1) (-81581416995156433534224222951217041143011142581627204727874103852448045405024981317064239687) (-168892402789024640099220827725746638920204301321336831666182352513777976586608403915461041413) (by decide) ⟨155, by omega⟩ (Or.inr ⟨by omega, hwp31⟩) tw31 (by omega) thi31 hhi32
  have hhi30 : ((-199997356644533613442072488562139716746185504431970773097164261367286680037967282933764559647 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 300 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC30 300 485 (-1) (-168892402789024640099220827725746638920204301321336831666182352513777976586608403915461041413) (-199997356644533613442072488562139716746185504431970773097164261367286680037967282933764559647) (by decide) ⟨150, by omega⟩ (Or.inr ⟨by omega, hwp30⟩) tw30 (by omega) thi30 hhi31
  exact hhi30
private lemma rLo_band2
    (hinit : ((199997356644533613442072488562139716746185504431970773097164261367286680037967282933762246767 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 300) :
    ((168892411076916520671147195050269209284104523750480946394656138626942247262103993570376023849 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 200 := by
  have hP85_nn : (0 : ℤ) ≤ P85 := by decide
  have hd1_pos : (0 : ℤ) < (digits : ℤ) + 1 := by decide
  have hS92_pos : (0 : ℤ) < S92 := by decide
  have hlo29 : ((52538356960091498844723932280638781061836133070332604466320794203199696444854337412933518322 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 290 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC29 290 469 1 (199997356644533613442072488562139716746185504431970773097164261367286680037967282933762246767) (52538356960091498844723932280638781061836133070332604466320794203199696444854337412933518322) (by decide) ⟨145, by omega⟩ (Or.inr ⟨by omega, hwp29⟩) tw29 (by omega) tlo29 hinit
  have hlo28 : ((4464352657536308690564472719552725598478632731423108104479453248591439424709579378871744 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 280 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC28 280 453 1 (52538356960091498844723932280638781061836133070332604466320794203199696444854337412933518322) (4464352657536308690564472719552725598478632731423108104479453248591439424709579378871744) (by decide) ⟨140, by omega⟩ (Or.inr ⟨by omega, hwp28⟩) tw28 (by omega) tlo28 hlo29
  have hlo27 : ((80159113266428493574250883886465897807786295312701824730052356037873547905812044893967798752 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 270 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC27 270 436 1 (4464352657536308690564472719552725598478632731423108104479453248591439424709579378871744) (80159113266428493574250883886465897807786295312701824730052356037873547905812044893967798752) (by decide) ⟨135, by omega⟩ (Or.inr ⟨by omega, hwp27⟩) tw27 (by omega) tlo27 hlo28
  have hlo26 : ((175744610185080413118512747736365339201371508221098335553773477689301551816275683498390014841 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 260 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC26 260 420 1 (80159113266428493574250883886465897807786295312701824730052356037873547905812044893967798752) (175744610185080413118512747736365339201371508221098335553773477689301551816275683498390014841) (by decide) ⟨130, by omega⟩ (Or.inr ⟨by omega, hwp26⟩) tw26 (by omega) tlo26 hlo27
  have hlo25 : ((202438488111837746484267545206304944595441790113142876037164218958805132507568055743822913770 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 250 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC25 250 404 1 (175744610185080413118512747736365339201371508221098335553773477689301551816275683498390014841) (202438488111837746484267545206304944595441790113142876037164218958805132507568055743822913770) (by decide) ⟨125, by omega⟩ (Or.inr ⟨by omega, hwp25⟩) tw25 (by omega) tlo25 hlo26
  have hlo24 : ((40965705030144010294149538913986628405479170249074329357883935546589949984806032087502928621 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 240 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC24 240 388 1 (202438488111837746484267545206304944595441790113142876037164218958805132507568055743822913770) (40965705030144010294149538913986628405479170249074329357883935546589949984806032087502928621) (by decide) ⟨120, by omega⟩ (Or.inr ⟨by omega, hwp24⟩) tw24 (by omega) tlo24 hlo25
  have hlo23 : ((51696220999531561303793337944074982634209036189908564749904895983963401146174253780152705253 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 230 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC23 230 372 1 (40965705030144010294149538913986628405479170249074329357883935546589949984806032087502928621) (51696220999531561303793337944074982634209036189908564749904895983963401146174253780152705253) (by decide) ⟨115, by omega⟩ (Or.inr ⟨by omega, hwp23⟩) tw23 (by omega) tlo23 hlo24
  have hlo22 : ((100000004907202062971789794268185797919135716247023567125434221889903973349083733456948020564 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 220 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC22 220 355 1 (51696220999531561303793337944074982634209036189908564749904895983963401146174253780152705253) (100000004907202062971789794268185797919135716247023567125434221889903973349083733456948020564) (by decide) ⟨110, by omega⟩ (Or.inr ⟨by omega, hwp22⟩) tw22 (by omega) tlo22 hlo23
  have hlo21 : ((81582982107199971584646560903262899013087753411982782411992069994873297441052282077834175461 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 210 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC21 210 339 1 (100000004907202062971789794268185797919135716247023567125434221889903973349083733456948020564) (81582982107199971584646560903262899013087753411982782411992069994873297441052282077834175461) (by decide) ⟨105, by omega⟩ (Or.inr ⟨by omega, hwp21⟩) tw21 (by omega) tlo21 hlo22
  have hlo20 : ((168892411076916520671147195050269209284104523750480946394656138626942247262103993570376023849 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 200 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC20 200 323 1 (81582982107199971584646560903262899013087753411982782411992069994873297441052282077834175461) (168892411076916520671147195050269209284104523750480946394656138626942247262103993570376023849) (by decide) ⟨100, by omega⟩ (Or.inr ⟨by omega, hwp20⟩) tw20 (by omega) tlo20 hlo21
  exact hlo20
private lemma rHi_band2
    (hinit : ((-199997356644533613442072488562139716746185504431970773097164261367286680037967282933764559647 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 300) :
    ((-168892411076916520671147195050269209284104523750480946394656138626942247262103993570372630793 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 200 := by
  have hP85_nn : (0 : ℤ) ≤ P85 := by decide
  have hd_pos : (0 : ℤ) < (digits : ℤ) := by decide
  have hS92_pos : (0 : ℤ) < S92 := by decide
  have hhi29 : ((-52538356960091498844723932280638781061836133070332604466320794203199696444854337412936138183 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 290 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC29 290 469 (-1) (-199997356644533613442072488562139716746185504431970773097164261367286680037967282933764559647) (-52538356960091498844723932280638781061836133070332604466320794203199696444854337412936138183) (by decide) ⟨145, by omega⟩ (Or.inr ⟨by omega, hwp29⟩) tw29 (by omega) thi29 hinit
  have hhi28 : ((-4464352657536308690564472719552725598478632731423108104479453248591439424709579374965208 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 280 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC28 280 453 (-1) (-52538356960091498844723932280638781061836133070332604466320794203199696444854337412936138183) (-4464352657536308690564472719552725598478632731423108104479453248591439424709579374965208) (by decide) ⟨140, by omega⟩ (Or.inr ⟨by omega, hwp28⟩) tw28 (by omega) thi28 hhi29
  have hhi27 : ((-80159113266428493574250883886465897807786295312701824730052356037873547905812044893958627849 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 270 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC27 270 436 (-1) (-4464352657536308690564472719552725598478632731423108104479453248591439424709579374965208) (-80159113266428493574250883886465897807786295312701824730052356037873547905812044893958627849) (by decide) ⟨135, by omega⟩ (Or.inr ⟨by omega, hwp27⟩) tw27 (by omega) thi27 hhi28
  have hhi26 : ((-175744610185080413118512747736365339201371508221098335553773477689301551816275683498389201148 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 260 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC26 260 420 (-1) (-80159113266428493574250883886465897807786295312701824730052356037873547905812044893958627849) (-175744610185080413118512747736365339201371508221098335553773477689301551816275683498389201148) (by decide) ⟨130, by omega⟩ (Or.inr ⟨by omega, hwp26⟩) tw26 (by omega) thi26 hhi27
  have hhi25 : ((-202438488111837746484267545206304944595441790113142876037164218958805132507568055743826453861 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 250 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC25 250 404 (-1) (-175744610185080413118512747736365339201371508221098335553773477689301551816275683498389201148) (-202438488111837746484267545206304944595441790113142876037164218958805132507568055743826453861) (by decide) ⟨125, by omega⟩ (Or.inr ⟨by omega, hwp25⟩) tw25 (by omega) thi25 hhi26
  have hhi24 : ((-40965705030144010294149538913986628405479170249074329357883935546589949984806032087501877654 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 240 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC24 240 388 (-1) (-202438488111837746484267545206304944595441790113142876037164218958805132507568055743826453861) (-40965705030144010294149538913986628405479170249074329357883935546589949984806032087501877654) (by decide) ⟨120, by omega⟩ (Or.inr ⟨by omega, hwp24⟩) tw24 (by omega) thi24 hhi25
  have hhi23 : ((-51696220999531561303793337944074982634209036189908564749904895983963401146174253780154808678 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 230 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC23 230 372 (-1) (-40965705030144010294149538913986628405479170249074329357883935546589949984806032087501877654) (-51696220999531561303793337944074982634209036189908564749904895983963401146174253780154808678) (by decide) ⟨115, by omega⟩ (Or.inr ⟨by omega, hwp23⟩) tw23 (by omega) thi23 hhi24
  have hhi22 : ((-100000004907202062971789794268185797919135716247023567125434221889903973349083733456944108653 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 220 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC22 220 355 (-1) (-51696220999531561303793337944074982634209036189908564749904895983963401146174253780154808678) (-100000004907202062971789794268185797919135716247023567125434221889903973349083733456944108653) (by decide) ⟨110, by omega⟩ (Or.inr ⟨by omega, hwp22⟩) tw22 (by omega) thi22 hhi23
  have hhi21 : ((-81582982107199971584646560903262899013087753411982782411992069994873297441052282077825794638 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 210 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC21 210 339 (-1) (-100000004907202062971789794268185797919135716247023567125434221889903973349083733456944108653) (-81582982107199971584646560903262899013087753411982782411992069994873297441052282077825794638) (by decide) ⟨105, by omega⟩ (Or.inr ⟨by omega, hwp21⟩) tw21 (by omega) thi21 hhi22
  have hhi20 : ((-168892411076916520671147195050269209284104523750480946394656138626942247262103993570372630793 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 200 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC20 200 323 (-1) (-81582982107199971584646560903262899013087753411982782411992069994873297441052282077825794638) (-168892411076916520671147195050269209284104523750480946394656138626942247262103993570372630793) (by decide) ⟨100, by omega⟩ (Or.inr ⟨by omega, hwp20⟩) tw20 (by omega) thi20 hhi21
  exact hhi20
private lemma rLo_band1
    (hinit : ((168892411076916520671147195050269209284104523750480946394656138626942247262103993570376023849 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 200) :
    ((81582982107199971110417717752018295913832004602888820123132906098714128694200799996017668469 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 100 := by
  have hP85_nn : (0 : ℤ) ≤ P85 := by decide
  have hd1_pos : (0 : ℤ) < (digits : ℤ) + 1 := by decide
  have hS92_pos : (0 : ℤ) < S92 := by decide
  have hlo19 : ((199997356688421303213325671727941299185263989413041647982615440194717977133621138712500179963 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 190 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC19 190 307 1 (168892411076916520671147195050269209284104523750480946394656138626942247262103993570376023849) (199997356688421303213325671727941299185263989413041647982615440194717977133621138712500179963) (by decide) ⟨95, by omega⟩ (Or.inr ⟨by omega, hwp19⟩) tw19 (by omega) tlo19 hinit
  have hlo18 : ((52538356960323901648864379632780742709596552886798614310917734074737473117254347599139369471 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 180 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC18 180 291 1 (199997356688421303213325671727941299185263989413041647982615440194717977133621138712500179963) (52538356960323901648864379632780742709596552886798614310917734074737473117254347599139369471) (by decide) ⟨90, by omega⟩ (Or.inr ⟨by omega, hwp18⟩) tw18 (by omega) tlo18 hlo19
  have hlo17 : ((-4057138544279104786366718066513918802753706161392142208880127766155077398481514909054963884 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 170 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC17 170 275 1 (52538356960323901648864379632780742709596552886798614310917734074737473117254347599139369471) (-4057138544279104786366718066513918802753706161392142208880127766155077398481514909054963884) (by decide) ⟨85, by omega⟩ (Or.inr ⟨by omega, hwp17⟩) tw17 (by omega) tlo17 hlo18
  have hlo16 : ((80137605460766521347974574709891026491111034839073206228665236224396700092114745327200984623 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 160 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC16 160 258 1 (-4057138544279104786366718066513918802753706161392142208880127766155077398481514909054963884) (80137605460766521347974574709891026491111034839073206228665236224396700092114745327200984623) (by decide) ⟨80, by omega⟩ (Or.inr ⟨by omega, hwp16⟩) tw16 (by omega) tlo16 hlo17
  have hlo15 : ((175744496292679769506146246419910064721615798311875346410930356770644452099345301615838177135 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 150 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC15 150 242 1 (80137605460766521347974574709891026491111034839073206228665236224396700092114745327200984623) (175744496292679769506146246419910064721615798311875346410930356770644452099345301615838177135) (by decide) ⟨75, by omega⟩ (Or.inr ⟨by omega, hwp15⟩) tw15 (by omega) tlo15 hlo16
  have hlo14 : ((202438487508732105293735521293657897810550416459900753830749754136538034523345121670268466116 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 140 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC14 140 226 1 (175744496292679769506146246419910064721615798311875346410930356770644452099345301615838177135) (202438487508732105293735521293657897810550416459900753830749754136538034523345121670268466116) (by decide) ⟨70, by omega⟩ (Or.inr ⟨by omega, hwp14⟩) tw14 (by omega) tlo14 hlo15
  have hlo13 : ((40965705026950325620015463182123809294252873474929876933389575014238358304144551497932299614 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 130 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC13 130 210 1 (202438487508732105293735521293657897810550416459900753830749754136538034523345121670268466116) (40965705026950325620015463182123809294252873474929876933389575014238358304144551497932299614) (by decide) ⟨65, by omega⟩ (Or.inr ⟨by omega, hwp13⟩) tw13 (by omega) tlo13 hlo14
  have hlo12 : ((51696220999514649470938210277056412434162574546028515307962419105044817015184599234511732672 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 120 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC12 120 194 1 (40965705026950325620015463182123809294252873474929876933389575014238358304144551497932299614) (51696220999514649470938210277056412434162574546028515307962419105044817015184599234511732672) (by decide) ⟨60, by omega⟩ (Or.inr ⟨by omega, hwp12⟩) tw12 (by omega) tlo12 hlo13
  have hlo11 : ((100000004907201973416896402257475441265895148509708589839549049365969338416434465894230401663 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 110 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC11 110 177 1 (51696220999514649470938210277056412434162574546028515307962419105044817015184599234511732672) (100000004907201973416896402257475441265895148509708589839549049365969338416434465894230401663) (by decide) ⟨55, by omega⟩ (Or.inr ⟨by omega, hwp11⟩) tw11 (by omega) tlo11 hlo12
  have hlo10 : ((81582982107199971110417717752018295913832004602888820123132906098714128694200799996017668469 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 100 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC10 100 161 1 (100000004907201973416896402257475441265895148509708589839549049365969338416434465894230401663) (81582982107199971110417717752018295913832004602888820123132906098714128694200799996017668469) (by decide) ⟨50, by omega⟩ (Or.inr ⟨by omega, hwp10⟩) tw10 (by omega) tlo10 hlo11
  exact hlo10
private lemma rHi_band1
    (hinit : ((-168892411076916520671147195050269209284104523750480946394656138626942247262103993570372630793 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 200) :
    ((-81582982107199971110417717752018295913832004602888820123132906098714128694200799996009287646 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 100 := by
  have hP85_nn : (0 : ℤ) ≤ P85 := by decide
  have hd_pos : (0 : ℤ) < (digits : ℤ) := by decide
  have hS92_pos : (0 : ℤ) < S92 := by decide
  have hhi19 : ((-199997356688421303213325671727941299185263989413041647982615440194717977133621138712502492843 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 190 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC19 190 307 (-1) (-168892411076916520671147195050269209284104523750480946394656138626942247262103993570372630793) (-199997356688421303213325671727941299185263989413041647982615440194717977133621138712502492843) (by decide) ⟨95, by omega⟩ (Or.inr ⟨by omega, hwp19⟩) tw19 (by omega) thi19 hinit
  have hhi18 : ((-52538356960323901648864379632780742709596552886798614310917734074737473117254347599141989332 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 180 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC18 180 291 (-1) (-199997356688421303213325671727941299185263989413041647982615440194717977133621138712502492843) (-52538356960323901648864379632780742709596552886798614310917734074737473117254347599141989332) (by decide) ⟨90, by omega⟩ (Or.inr ⟨by omega, hwp18⟩) tw18 (by omega) thi18 hhi19
  have hhi17 : ((4057138544279104786366718066513918802753706161392142208880127766155077398481514909060643248 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 170 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC17 170 275 (-1) (-52538356960323901648864379632780742709596552886798614310917734074737473117254347599141989332) (4057138544279104786366718066513918802753706161392142208880127766155077398481514909060643248) (by decide) ⟨85, by omega⟩ (Or.inr ⟨by omega, hwp17⟩) tw17 (by omega) thi17 hhi18
  have hhi16 : ((-80137605460766521347974574709891026491111034839073206228665236224396700092114745327191791596 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 160 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC16 160 258 (-1) (4057138544279104786366718066513918802753706161392142208880127766155077398481514909060643248) (-80137605460766521347974574709891026491111034839073206228665236224396700092114745327191791596) (by decide) ⟨80, by omega⟩ (Or.inr ⟨by omega, hwp16⟩) tw16 (by omega) thi16 hhi17
  have hhi15 : ((-175744496292679769506146246419910064721615798311875346410930356770644452099345301615837363259 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 150 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC15 150 242 (-1) (-80137605460766521347974574709891026491111034839073206228665236224396700092114745327191791596) (-175744496292679769506146246419910064721615798311875346410930356770644452099345301615837363259) (by decide) ⟨75, by omega⟩ (Or.inr ⟨by omega, hwp15⟩) tw15 (by omega) thi15 hhi16
  have hhi14 : ((-202438487508732105293735521293657897810550416459900753830749754136538034523345121670272006205 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 140 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC14 140 226 (-1) (-175744496292679769506146246419910064721615798311875346410930356770644452099345301615837363259) (-202438487508732105293735521293657897810550416459900753830749754136538034523345121670272006205) (by decide) ⟨70, by omega⟩ (Or.inr ⟨by omega, hwp14⟩) tw14 (by omega) thi14 hhi15
  have hhi13 : ((-40965705026950325620015463182123809294252873474929876933389575014238358304144551497931248647 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 130 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC13 130 210 (-1) (-202438487508732105293735521293657897810550416459900753830749754136538034523345121670272006205) (-40965705026950325620015463182123809294252873474929876933389575014238358304144551497931248647) (by decide) ⟨65, by omega⟩ (Or.inr ⟨by omega, hwp13⟩) tw13 (by omega) thi13 hhi14
  have hhi12 : ((-51696220999514649470938210277056412434162574546028515307962419105044817015184599234513836096 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 120 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC12 120 194 (-1) (-40965705026950325620015463182123809294252873474929876933389575014238358304144551497931248647) (-51696220999514649470938210277056412434162574546028515307962419105044817015184599234513836096) (by decide) ⟨60, by omega⟩ (Or.inr ⟨by omega, hwp12⟩) tw12 (by omega) thi12 hhi13
  have hhi11 : ((-100000004907201973416896402257475441265895148509708589839549049365969338416434465894226489752 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 110 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC11 110 177 (-1) (-51696220999514649470938210277056412434162574546028515307962419105044817015184599234513836096) (-100000004907201973416896402257475441265895148509708589839549049365969338416434465894226489752) (by decide) ⟨55, by omega⟩ (Or.inr ⟨by omega, hwp11⟩) tw11 (by omega) thi11 hhi12
  have hhi10 : ((-81582982107199971110417717752018295913832004602888820123132906098714128694200799996009287646 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 100 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC10 100 161 (-1) (-100000004907201973416896402257475441265895148509708589839549049365969338416434465894226489752) (-81582982107199971110417717752018295913832004602888820123132906098714128694200799996009287646) (by decide) ⟨50, by omega⟩ (Or.inr ⟨by omega, hwp10⟩) tw10 (by omega) thi10 hhi11
  exact hhi10
private lemma rLo_band0
    (hinit : ((81582982107199971110417717752018295913832004602888820123132906098714128694200799996017668469 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 100) :
    ((2444474 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 0 := by
  have hP85_nn : (0 : ℤ) ≤ P85 := by decide
  have hd1_pos : (0 : ℤ) < (digits : ℤ) + 1 := by decide
  have hS92_pos : (0 : ℤ) < S92 := by decide
  have hlo9 : ((168892411076916520668635964371984121798885528747181509452754177770449535588256001369032117953 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 90 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC9 90 145 1 (81582982107199971110417717752018295913832004602888820123132906098714128694200799996017668469) (168892411076916520668635964371984121798885528747181509452754177770449535588256001369032117953) (by decide) ⟨45, by omega⟩ (Or.inr ⟨by omega, hwp9⟩) tw9 (by omega) tlo9 hinit
  have hlo8 : ((202402202987340055495170686150703471021857177529507458091614818066381226294821162506986896206 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 80 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC8 80 129 1 (168892411076916520668635964371984121798885528747181509452754177770449535588256001369032117953) (202402202987340055495170686150703471021857177529507458091614818066381226294821162506986896206) (by decide) ⟨40, by omega⟩ (Or.inr ⟨by omega, hwp8⟩) tw8 (by omega) tlo8 hlo9
  have hlo7 : ((52551091579674077019986020332153508904469983667242933796973058742604829969899826937730671624 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 70 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC7 70 113 1 (202402202987340055495170686150703471021857177529507458091614818066381226294821162506986896206) (52551091579674077019986020332153508904469983667242933796973058742604829969899826937730671624) (by decide) ⟨35, by omega⟩ (Or.inr ⟨by omega, hwp7⟩) tw7 (by omega) tlo7 hlo8
  have hlo6 : ((-4057071109395608583384696928101326695033206740150537502022570134488036014216029540547843874 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 60 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC6 60 97 1 (52551091579674077019986020332153508904469983667242933796973058742604829969899826937730671624) (-4057071109395608583384696928101326695033206740150537502022570134488036014216029540547843874) (by decide) ⟨30, by omega⟩ (Or.inr ⟨by omega, hwp6⟩) tw6 (by omega) tlo6 hlo7
  have hlo5 : ((80137605817861098508134861980837648767348936146578722827394556075232295321360189970112048483 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 50 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC5 50 80 1 (-4057071109395608583384696928101326695033206740150537502022570134488036014216029540547843874) (80137605817861098508134861980837648767348936146578722827394556075232295321360189970112048483) (by decide) ⟨25, by omega⟩ (Or.inr ⟨by omega, hwp5⟩) tw5 (by omega) tlo5 hlo6
  have hlo4 : ((175744496294570727574523033500427312060591388255136154234474249734733009937114430331813806683 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 40 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC4 40 64 1 (80137605817861098508134861980837648767348936146578722827394556075232295321360189970112048483) (175744496294570727574523033500427312060591388255136154234474249734733009937114430331813806683) (by decide) ⟨20, by omega⟩ (Or.inr ⟨by omega, hwp4⟩) tw4 (by omega) tlo4 hlo5
  have hlo3 : ((169391033812661187205742504622598284585054938873851396843001719443336949253140711218028125511 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 30 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC3 30 48 1 (175744496294570727574523033500427312060591388255136154234474249734733009937114430331813806683) (169391033812661187205742504622598284585054938873851396843001719443336949253140711218028125511) (by decide) ⟨15, by omega⟩ (Or.inr ⟨by omega, hwp3⟩) tw3 (by omega) tlo3 hlo4
  have hlo2 : ((40790705592058695730349476341403783073819829308317904200041687300532397204901172606276522359 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 20 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC2 20 32 1 (169391033812661187205742504622598284585054938873851396843001719443336949253140711218028125511) (40790705592058695730349476341403783073819829308317904200041687300532397204901172606276522359) (by decide) ⟨10, by omega⟩ (Or.inr ⟨by omega, hwp2⟩) tw2 (by omega) tlo2 hlo3
  have hlo1 : ((51695294307779363649005485032357761934871907848375470057696040645446377914972614826580387608 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 10 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC1 10 16 1 (40790705592058695730349476341403783073819829308317904200041687300532397204901172606276522359) (51695294307779363649005485032357761934871907848375470057696040645446377914972614826580387608) (by decide) ⟨5, by omega⟩ (Or.inr ⟨by omega, hwp1⟩) tw1 (by omega) tlo1 hlo2
  have hlo0 : ((2444474 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)) 1 0 :=
    chunk_step P85 ((digits : ℤ) + 1) S92 hP85_nn hd1_pos hS92_pos wC0 0 0 1 (51695294307779363649005485032357761934871907848375470057696040645446377914972614826580387608) (2444474) (by decide) ⟨0, by omega⟩ (Or.inl ⟨rfl, rfl⟩) tw0 (by omega) tlo0 hlo1
  exact hlo0
private lemma rHi_band0
    (hinit : ((-81582982107199971110417717752018295913832004602888820123132906098714128694200799996009287646 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 100) :
    ((1467447 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 0 := by
  have hP85_nn : (0 : ℤ) ≤ P85 := by decide
  have hd_pos : (0 : ℤ) < (digits : ℤ) := by decide
  have hS92_pos : (0 : ℤ) < S92 := by decide
  have hhi9 : ((-168892411076916520668635964371984121798885528747181509452754177770449535588256001369028724897 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 90 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC9 90 145 (-1) (-81582982107199971110417717752018295913832004602888820123132906098714128694200799996009287646) (-168892411076916520668635964371984121798885528747181509452754177770449535588256001369028724897) (by decide) ⟨45, by omega⟩ (Or.inr ⟨by omega, hwp9⟩) tw9 (by omega) thi9 hinit
  have hhi8 : ((-202402202987340055495170686150703471021857177529507458091614818066381226294821162506990401154 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 80 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC8 80 129 (-1) (-168892411076916520668635964371984121798885528747181509452754177770449535588256001369028724897) (-202402202987340055495170686150703471021857177529507458091614818066381226294821162506990401154) (by decide) ⟨40, by omega⟩ (Or.inr ⟨by omega, hwp8⟩) tw8 (by omega) thi8 hhi9
  have hhi7 : ((-52551091579674077019986020332153508904469983667242933796973058742604829969899826937733305337 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 70 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC7 70 113 (-1) (-202402202987340055495170686150703471021857177529507458091614818066381226294821162506990401154) (-52551091579674077019986020332153508904469983667242933796973058742604829969899826937733305337) (by decide) ⟨35, by omega⟩ (Or.inr ⟨by omega, hwp7⟩) tw7 (by omega) thi7 hhi8
  have hhi6 : ((4057071109395608583384696928101326695033206740150537502022570134488036014216029540553523125 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 60 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC6 60 97 (-1) (-52551091579674077019986020332153508904469983667242933796973058742604829969899826937733305337) (4057071109395608583384696928101326695033206740150537502022570134488036014216029540553523125) (by decide) ⟨30, by omega⟩ (Or.inr ⟨by omega, hwp6⟩) tw6 (by omega) thi6 hhi7
  have hhi5 : ((-80137605817861098508134861980837648767348936146578722827394556075232295321360189970102855457 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 50 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC5 50 80 (-1) (4057071109395608583384696928101326695033206740150537502022570134488036014216029540553523125) (-80137605817861098508134861980837648767348936146578722827394556075232295321360189970102855457) (by decide) ⟨25, by omega⟩ (Or.inr ⟨by omega, hwp5⟩) tw5 (by omega) thi5 hhi6
  have hhi4 : ((-175744496294570727574523033500427312060591388255136154234474249734733009937114430331812992806 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 40 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC4 40 64 (-1) (-80137605817861098508134861980837648767348936146578722827394556075232295321360189970102855457) (-175744496294570727574523033500427312060591388255136154234474249734733009937114430331812992806) (by decide) ⟨20, by omega⟩ (Or.inr ⟨by omega, hwp4⟩) tw4 (by omega) thi4 hhi5
  have hhi3 : ((-169391033812661187205742504622598284585054938873851396843001719443336949253140711218025067757 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 30 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC3 30 48 (-1) (-175744496294570727574523033500427312060591388255136154234474249734733009937114430331812992806) (-169391033812661187205742504622598284585054938873851396843001719443336949253140711218025067757) (by decide) ⟨15, by omega⟩ (Or.inr ⟨by omega, hwp3⟩) tw3 (by omega) thi3 hhi4
  have hhi2 : ((-40790705592058695730349476341403783073819829308317904200041687300532397204901172606275332837 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 20 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC2 20 32 (-1) (-169391033812661187205742504622598284585054938873851396843001719443336949253140711218025067757) (-40790705592058695730349476341403783073819829308317904200041687300532397204901172606275332837) (by decide) ⟨10, by omega⟩ (Or.inr ⟨by omega, hwp2⟩) tw2 (by omega) thi2 hhi3
  have hhi1 : ((-51695294307779363649005485032357761934871907848375470057696040645446377914972614826582489750 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 10 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC1 10 16 (-1) (-40790705592058695730349476341403783073819829308317904200041687300532397204901172606275332837) (-51695294307779363649005485032357761934871907848375470057696040645446377914972614826582489750) (by decide) ⟨5, by omega⟩ (Or.inr ⟨by omega, hwp1⟩) tw1 (by omega) thi1 hhi2
  have hhi0 : ((1467447 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum (((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)) (-1) 0 :=
    chunk_step P85 (digits : ℤ) S92 hP85_nn hd_pos hS92_pos wC0 0 0 (-1) (-51695294307779363649005485032357761934871907848375470057696040645446377914972614826582489750) (1467447) (by decide) ⟨0, by omega⟩ (Or.inl ⟨rfl, rfl⟩) tw0 (by omega) thi0 hhi1
  exact hhi0

private lemma tail_bound_400 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 5921 / 10000) :
    |∑' k : ℕ, coeff (k + 400) g * x ^ (k + 400)| < (1000 : ℝ) / (S92 : ℝ) := by
  have hxlt : |x| < 1 := by
    rw [abs_of_nonneg hx0]
    linarith
  have hsum_abs : Summable (fun k : ℕ => ‖coeff (k + 400) g * x ^ (k + 400)‖) :=
    (summable_g_abs x hxlt).comp_injective (add_left_injective 400)
  have hdom : Summable (fun k : ℕ => (2 : ℝ) * x ^ 400 * x ^ k) :=
    (summable_geometric_of_lt_one hx0 (by linarith)).mul_left (2 * x ^ 400)
  have hstep1 : |∑' k : ℕ, coeff (k + 400) g * x ^ (k + 400)| ≤
      ∑' k : ℕ, (2 : ℝ) * x ^ 400 * x ^ k := by
    calc
      |∑' k : ℕ, coeff (k + 400) g * x ^ (k + 400)|
        = ‖∑' k : ℕ, coeff (k + 400) g * x ^ (k + 400)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' k : ℕ, ‖coeff (k + 400) g * x ^ (k + 400)‖ := norm_tsum_le_tsum_norm hsum_abs
      _ ≤ ∑' k : ℕ, (2 : ℝ) * x ^ 400 * x ^ k := by
          refine Summable.tsum_le_tsum (fun k => ?_) hsum_abs hdom
          rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hx0, pow_add]
          have hc := abs_coeff_g_le_two (k + 400)
          have hp : 0 ≤ x ^ k * x ^ 400 := mul_nonneg (pow_nonneg hx0 k) (pow_nonneg hx0 400)
          nlinarith
  have hgeom : ∑' k : ℕ, (2 : ℝ) * x ^ 400 * x ^ k = 2 * x ^ 400 / (1 - x) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hx0 (by linarith), div_eq_mul_inv]
  have hp5 : (5921 / 10000 : ℝ) ^ 5 ≤ 73 / 1000 := by norm_num
  have hp20 : (5921 / 10000 : ℝ) ^ 20 ≤ 29 / 10 ^ 6 := by
    calc
      (5921 / 10000 : ℝ) ^ 20 = ((5921 / 10000 : ℝ) ^ 5) ^ 4 := by rw [← pow_mul]
      _ ≤ (73 / 1000 : ℝ) ^ 4 := pow_le_pow_left₀ (by positivity) hp5 4
      _ ≤ 29 / 10 ^ 6 := by norm_num
  have hp80 : (5921 / 10000 : ℝ) ^ 80 ≤ 8 / 10 ^ 19 := by
    calc
      (5921 / 10000 : ℝ) ^ 80 = ((5921 / 10000 : ℝ) ^ 20) ^ 4 := by rw [← pow_mul]
      _ ≤ (29 / 10 ^ 6 : ℝ) ^ 4 := pow_le_pow_left₀ (by positivity) hp20 4
      _ ≤ 8 / 10 ^ 19 := by norm_num
  have hp400 : (5921 / 10000 : ℝ) ^ 400 ≤ 4 / 10 ^ 91 := by
    calc
      (5921 / 10000 : ℝ) ^ 400 = ((5921 / 10000 : ℝ) ^ 80) ^ 5 := by rw [← pow_mul]
      _ ≤ (8 / 10 ^ 19 : ℝ) ^ 5 := pow_le_pow_left₀ (by positivity) hp80 5
      _ ≤ 4 / 10 ^ 91 := by norm_num
  have hxp : x ^ 400 ≤ 4 / 10 ^ 91 := le_trans (pow_le_pow_left₀ hx0 hx1 400) hp400
  have hden : (4079 / 10000 : ℝ) ≤ 1 - x := by linarith
  have hfrac : 2 * x ^ 400 / (1 - x) ≤ 2 * (4 / 10 ^ 91) / (4079 / 10000) := by
    exact div_le_div₀ (by positivity) (by linarith) (by norm_num) hden
  have hlt : (2 : ℝ) * (4 / 10 ^ 91) / (4079 / 10000) < (1000 : ℝ) / (S92 : ℝ) := by
    unfold S92
    norm_num
  linarith

private lemma exists_root_r0 :
    ∃ r₀ : ℝ,
      ((P85 : ℝ) / ((digits : ℝ) + 1)) < r₀ ∧
      r₀ < ((P85 : ℝ) / (digits : ℝ)) ∧
      gEval r₀ = 0 := by
  set rLo : ℝ := ((P85 : ℤ) : ℝ) / (((digits : ℤ) + 1 : ℤ) : ℝ)
  set rHi : ℝ := ((P85 : ℤ) : ℝ) / ((digits : ℤ) : ℝ)
  have hrLo_eq : rLo = (P85 : ℝ) / ((digits : ℝ) + 1) := by
    simp [rLo]
  have hrHi_eq : rHi = (P85 : ℝ) / (digits : ℝ) := by
    simp [rHi]
  have hlo0 : ((2444474 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum rLo 1 0 :=
    rLo_band0 (rLo_band1 (rLo_band2 (rLo_band3 (by simp [tailSum]))))
  have hhi0 : ((1467447 : ℤ) : ℝ) / (S92 : ℝ) ≤ tailSum rHi (-1) 0 :=
    rHi_band0 (rHi_band1 (rHi_band2 (rHi_band3 (by simp [tailSum]))))
  have hrLo_pos : 0 ≤ rLo := by unfold rLo P85 digits; positivity
  have hrHi_pos : 0 ≤ rHi := by unfold rHi P85 digits; positivity
  have hrLo_le_rHi : rLo ≤ rHi := by
    rw [hrLo_eq, hrHi_eq]
    have hd : (0 : ℝ) < (digits : ℝ) := by unfold digits; positivity
    exact div_le_div_of_nonneg_left (by unfold P85; positivity) hd (by linarith)
  have hrHi_le : rHi ≤ 5921 / 10000 := by
    rw [hrHi_eq]
    unfold P85 digits
    norm_num
  have hrLo_le : rLo ≤ 5921 / 10000 := le_trans hrLo_le_rHi hrHi_le
  have hgLo_pos : 0 < gEval rLo := by
    have hsum := (summable_g rLo (by rw [abs_of_nonneg hrLo_pos]; linarith)).sum_add_tsum_nat_add 400
    have htail := tail_bound_400 rLo hrLo_pos hrLo_le
    have htail_ge : -((1000 : ℝ) / (S92 : ℝ)) < ∑' k : ℕ, coeff (k + 400) g * rLo ^ (k + 400) :=
      (abs_lt.mp htail).1
    have hpart : (2444474 : ℝ) / (S92 : ℝ) ≤ ∑ i ∈ Finset.range 400, coeff i g * rLo ^ i := by
      simpa [tailSum] using hlo0
    have hSpos : (0 : ℝ) < (S92 : ℝ) := by unfold S92; positivity
    have hgap : (1000 : ℝ) / (S92 : ℝ) < (2444474 : ℝ) / (S92 : ℝ) := by
      exact div_lt_div_of_pos_right (by norm_num) hSpos
    unfold gEval
    linarith
  have hgHi_neg : gEval rHi < 0 := by
    have hsum := (summable_g rHi (by rw [abs_of_nonneg hrHi_pos]; linarith)).sum_add_tsum_nat_add 400
    have htail := tail_bound_400 rHi hrHi_pos hrHi_le
    have htail_le : ∑' k : ℕ, coeff (k + 400) g * rHi ^ (k + 400) < (1000 : ℝ) / (S92 : ℝ) :=
      (abs_lt.mp htail).2
    have hpart : (1467447 : ℝ) / (S92 : ℝ) ≤ - ∑ i ∈ Finset.range 400, coeff i g * rHi ^ i := by
      have h0 : (1467447 : ℝ) / (S92 : ℝ) ≤
          ∑ i ∈ Finset.range 400, (-1 : ℝ) * coeff i g * rHi ^ i := by
        simpa [tailSum] using hhi0
      have hneg : ∑ i ∈ Finset.range 400, (-1 : ℝ) * coeff i g * rHi ^ i =
          - ∑ i ∈ Finset.range 400, coeff i g * rHi ^ i := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      linarith
    have hSpos : (0 : ℝ) < (S92 : ℝ) := by unfold S92; positivity
    have hgap : (1000 : ℝ) / (S92 : ℝ) < (1467447 : ℝ) / (S92 : ℝ) := by
      exact div_lt_div_of_pos_right (by norm_num) hSpos
    unfold gEval
    linarith
  have hcont : ContinuousOn (fun x => -gEval x) (Set.Icc rLo rHi) :=
    (continuousOn_gEval rLo rHi hrLo_pos (by linarith)).neg
  have hmem : (0 : ℝ) ∈ Set.Ioo (-gEval rLo) (-gEval rHi) := ⟨by linarith, by linarith⟩
  rcases intermediate_value_Ioo hrLo_le_rHi hcont hmem with ⟨r₀, hr₀_mem, hr₀_eq⟩
  refine ⟨r₀, ?_, ?_, ?_⟩
  · rw [← hrLo_eq]; exact hr₀_mem.1
  · rw [← hrHi_eq]; exact hr₀_mem.2
  · linarith

private lemma coeff_mul_eq_sum_range (φ ψ : PowerSeries ℝ) (n : ℕ) :
    coeff n (φ * ψ) = ∑ k ∈ Finset.range (n + 1), coeff k φ * coeff (n - k) ψ := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i φ * coeff j ψ) n]

private lemma tsum_eval_mul (φ ψ : PowerSeries ℝ) (r : ℝ)
    (hφ : Summable (fun n : ℕ => ‖coeff n φ * r ^ n‖))
    (hψ : Summable (fun n : ℕ => ‖coeff n ψ * r ^ n‖)) :
    (∑' n : ℕ, coeff n φ * r ^ n) * (∑' n : ℕ, coeff n ψ * r ^ n) =
    ∑' n : ℕ, coeff n (φ * ψ) * r ^ n := by
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hφ hψ]
  congr 1
  ext n
  rw [PowerSeries.coeff_mul, Finset.sum_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (coeff i φ * r ^ i) * (coeff j ψ * r ^ j)) n,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i φ * coeff j ψ * r ^ n) n]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hpow : r ^ n = r ^ k * r ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_of_le hkn]
  rw [hpow]
  ring

private lemma geom_inv_eq (L : ℝ) :
    (1 - PowerSeries.C L * PowerSeries.X)⁻¹ = PowerSeries.mk (fun n => L ^ n) := by
  have hc : PowerSeries.constantCoeff (1 - PowerSeries.C L * PowerSeries.X) ≠ 0 := by
    simp [map_sub, map_one, map_mul, PowerSeries.constantCoeff_X]
  have hmul : (1 - PowerSeries.C L * PowerSeries.X) * PowerSeries.mk (fun n => L ^ n) = 1 := by
    ext n
    rw [sub_mul, one_mul, mul_assoc, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_one]
    cases n with
    | zero =>
      rw [PowerSeries.coeff_zero_X_mul, mul_zero, sub_zero, PowerSeries.coeff_mk]
      simp
    | succ n =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mk, pow_succ]
      have hne : (if n + 1 = 0 then (1 : ℝ) else 0) = 0 := by simp
      rw [hne]
      ring
  calc
    (1 - PowerSeries.C L * PowerSeries.X)⁻¹
      = (1 - PowerSeries.C L * PowerSeries.X)⁻¹ * 1 := (mul_one _).symm
    _ = (1 - PowerSeries.C L * PowerSeries.X)⁻¹ *
          ((1 - PowerSeries.C L * PowerSeries.X) * PowerSeries.mk (fun n => L ^ n)) := by
          rw [hmul]
    _ = ((1 - PowerSeries.C L * PowerSeries.X)⁻¹ * (1 - PowerSeries.C L * PowerSeries.X)) *
          PowerSeries.mk (fun n => L ^ n) := (mul_assoc _ _ _).symm
    _ = PowerSeries.mk (fun n => L ^ n) := by
          rw [PowerSeries.inv_mul_cancel _ hc, one_mul]

private lemma tsum_le_of_sum_range_le {f : ℕ → ℝ} {c : ℝ}
    (hf : Summable f) (hle : ∀ N : ℕ, ∑ n ∈ Finset.range N, f n ≤ c) :
    ∑' n : ℕ, f n ≤ c :=
  le_of_tendsto hf.hasSum.tendsto_sum_nat (Eventually.of_forall hle)

private lemma ht_properties (r₀ L : ℝ)
    (hr0_pos : 0 < r₀) (hr0_lt : r₀ < 5921 / 10000) (hL_r0 : L * r₀ = 1)
    (hL_box : (168892 : ℝ) / 100000 ≤ L ∧ L ≤ (168893 : ℝ) / 100000)
    (hg0 : gEval r₀ = 0) :
    ∃ ht : PowerSeries ℝ,
      coeff 0 ht = 1 ∧
      (1 - PowerSeries.C L * PowerSeries.X) * ht = g ∧
      (∀ n : ℕ, |coeff n ht| ≤ 3) ∧
      Summable (fun n : ℕ => |coeff n (ht - 1)| * (62 / 100 : ℝ) ^ n) ∧
      ∑' n : ℕ, |coeff n (ht - 1)| * (62 / 100 : ℝ) ^ n ≤ 9 / 10 := by
  let ht : PowerSeries ℝ := PowerSeries.mk fun n => - ∑' k : ℕ, coeff (n + k + 1) g * r₀ ^ (k + 1)
  have hsum_ht_tail : ∀ n : ℕ, Summable (fun k : ℕ => coeff (n + k + 1) g * r₀ ^ (k + 1)) := by
    intro n
    have hdom : Summable (fun k : ℕ => (2 : ℝ) * r₀ * r₀ ^ k) :=
      (summable_geometric_of_lt_one (le_of_lt hr0_pos) (by linarith)).mul_left (2 * r₀)
    refine Summable.of_norm_bounded hdom fun k => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (le_of_lt hr0_pos), pow_succ]
    have hc := abs_coeff_g_le_two (n + k + 1)
    have hp : 0 ≤ r₀ ^ k * r₀ := mul_nonneg (pow_nonneg (le_of_lt hr0_pos) k) (le_of_lt hr0_pos)
    nlinarith only [hc, hp]
  have hht0 : coeff 0 ht = 1 := by
    have hs := (summable_g r₀ (by rw [abs_of_nonneg (le_of_lt hr0_pos)]; linarith)).tsum_eq_zero_add
    have hg0' : gEval r₀ = coeff 0 g * r₀ ^ 0 + ∑' k : ℕ, coeff (k + 1) g * r₀ ^ (k + 1) := hs
    rw [hg0, coeff_zero_g, pow_zero, mul_one] at hg0'
    simp only [ht, PowerSeries.coeff_mk, zero_add]
    linarith only [hg0']
  have ht_recur : ∀ n : ℕ, coeff (n + 1) ht = coeff (n + 1) g + L * coeff n ht := by
    intro n
    have hs := (hsum_ht_tail n).tsum_eq_zero_add
    have hshift : coeff n ht = -r₀ * coeff (n + 1) g + r₀ * coeff (n + 1) ht := by
      simp only [ht, PowerSeries.coeff_mk]
      rw [hs, add_zero, pow_one]
      have hfactor : ∑' k : ℕ, coeff (n + (k + 1) + 1) g * r₀ ^ (k + 1 + 1) =
          r₀ * ∑' k : ℕ, coeff (n + 1 + k + 1) g * r₀ ^ (k + 1) := by
        rw [← tsum_mul_left]
        congr 1
        ext k
        rw [show n + (k + 1) + 1 = n + 1 + k + 1 by omega, pow_succ]
        ring
      rw [hfactor]
      ring
    calc
      coeff (n + 1) ht
        = coeff (n + 1) g + (L * r₀) * (coeff (n + 1) ht - coeff (n + 1) g) := by
          rw [hL_r0]
          ring
      _ = coeff (n + 1) g + L * (-r₀ * coeff (n + 1) g + r₀ * coeff (n + 1) ht) := by ring
      _ = coeff (n + 1) g + L * coeff n ht := by rw [← hshift]
  have hht_eq_g : (1 - PowerSeries.C L * PowerSeries.X) * ht = g := by
    ext n
    rw [sub_mul, one_mul, mul_assoc, map_sub, PowerSeries.coeff_C_mul]
    cases n with
    | zero =>
      rw [PowerSeries.coeff_zero_X_mul, mul_zero, sub_zero, hht0, coeff_zero_g]
    | succ n =>
      rw [PowerSeries.coeff_succ_X_mul, ht_recur n]
      ring
  have hht_bound : ∀ n : ℕ, |coeff n ht| ≤ 3 := by
    intro n
    simp only [ht, PowerSeries.coeff_mk, abs_neg]
    have hdom : Summable (fun k : ℕ => (2 : ℝ) * r₀ * r₀ ^ k) :=
      (summable_geometric_of_lt_one (le_of_lt hr0_pos) (by linarith)).mul_left (2 * r₀)
    have hsum_abs : Summable (fun k : ℕ => ‖coeff (n + k + 1) g * r₀ ^ (k + 1)‖) := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) hdom
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (le_of_lt hr0_pos), pow_succ]
      have hc := abs_coeff_g_le_two (n + k + 1)
      have hp : 0 ≤ r₀ ^ k * r₀ := mul_nonneg (pow_nonneg (le_of_lt hr0_pos) k) (le_of_lt hr0_pos)
      nlinarith only [hc, hp]
    have hle : |∑' k : ℕ, coeff (n + k + 1) g * r₀ ^ (k + 1)| ≤ 2 * r₀ / (1 - r₀) := by
      calc
        |∑' k : ℕ, coeff (n + k + 1) g * r₀ ^ (k + 1)|
          = ‖∑' k : ℕ, coeff (n + k + 1) g * r₀ ^ (k + 1)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∑' k : ℕ, ‖coeff (n + k + 1) g * r₀ ^ (k + 1)‖ := norm_tsum_le_tsum_norm hsum_abs
        _ ≤ ∑' k : ℕ, (2 : ℝ) * r₀ * r₀ ^ k := by
            refine Summable.tsum_le_tsum (fun k => ?_) hsum_abs hdom
            rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (le_of_lt hr0_pos), pow_succ]
            have hc := abs_coeff_g_le_two (n + k + 1)
            have hp : 0 ≤ r₀ ^ k * r₀ :=
              mul_nonneg (pow_nonneg (le_of_lt hr0_pos) k) (le_of_lt hr0_pos)
            nlinarith only [hc, hp]
        _ = 2 * r₀ / (1 - r₀) := by
            rw [tsum_mul_left, tsum_geometric_of_lt_one (le_of_lt hr0_pos) (by linarith),
              div_eq_mul_inv]
    have h2 : 2 * r₀ / (1 - r₀) ≤ 3 := by
      rw [div_le_iff₀ (by linarith only [hr0_lt])]
      linarith only [hr0_lt]
    linarith only [hle, h2]
  have hw0 : weight 0 = (1 : ℝ) := by simpa [wC0] using checkChunk_sound wC0 0 tw0 0 (by decide)
  have hw1 : weight 1 = (3 : ℝ) := by simpa [wC0] using checkChunk_sound wC0 0 tw0 1 (by decide)
  have hw2 : weight 2 = (4 : ℝ) := by simpa [wC0] using checkChunk_sound wC0 0 tw0 2 (by decide)
  have hw3 : weight 3 = (6 : ℝ) := by simpa [wC0] using checkChunk_sound wC0 0 tw0 3 (by decide)
  have hw4 : weight 4 = (8 : ℝ) := by simpa [wC0] using checkChunk_sound wC0 0 tw0 4 (by decide)
  have hw5 : weight 5 = (9 : ℝ) := by simpa [wC0] using checkChunk_sound wC0 0 tw0 5 (by decide)
  have hw6 : weight 6 = (11 : ℝ) := by simpa [wC0] using checkChunk_sound wC0 0 tw0 6 (by decide)
  have hw7 : weight 7 = (12 : ℝ) := by simpa [wC0] using checkChunk_sound wC0 0 tw0 7 (by decide)
  have hw8 : weight 8 = (14 : ℝ) := by simpa [wC0] using checkChunk_sound wC0 0 tw0 8 (by decide)
  have hw9 : weight 9 = (16 : ℝ) := by simpa [wC0] using checkChunk_sound wC0 0 tw0 9 (by decide)
  have hg1 : coeff 1 g = (-2 : ℝ) := by rw [coeff_succ_g 0, hw1, hw0]; norm_num
  have hg2 : coeff 2 g = (1 : ℝ) := by rw [coeff_succ_g 1, hw2, hw1]; norm_num
  have hg3 : coeff 3 g = (-2 : ℝ) := by rw [coeff_succ_g 2, hw3, hw2]; norm_num
  have hg4 : coeff 4 g = (2 : ℝ) := by rw [coeff_succ_g 3, hw4, hw3]; norm_num
  have hg5 : coeff 5 g = (-1 : ℝ) := by rw [coeff_succ_g 4, hw5, hw4]; norm_num
  have hg6 : coeff 6 g = (2 : ℝ) := by rw [coeff_succ_g 5, hw6, hw5]; norm_num
  have hg7 : coeff 7 g = (-1 : ℝ) := by rw [coeff_succ_g 6, hw7, hw6]; norm_num
  have hg8 : coeff 8 g = (2 : ℝ) := by rw [coeff_succ_g 7, hw8, hw7]; norm_num
  have hg9 : coeff 9 g = (-2 : ℝ) := by rw [coeff_succ_g 8, hw9, hw8]; norm_num
  have hht1_eq : coeff 1 ht = (-2 : ℝ) + L * coeff 0 ht := by
    rw [ht_recur 0, hg1]
  have hht1 : (-3111 : ℝ) / 10000 ≤ coeff 1 ht ∧ coeff 1 ht ≤ (-311 : ℝ) / 1000 := by
    constructor <;> nlinarith only [hht1_eq, hL_box, hht0]
  have habs1 : |coeff 1 ht| ≤ (3111 : ℝ) / 10000 := abs_le.mpr ⟨by linarith only [hht1], by linarith only [hht1]⟩
  have hht2_eq : coeff 2 ht = (1 : ℝ) + L * coeff 1 ht := by
    rw [ht_recur 1, hg2]
  have hht2 : (949 : ℝ) / 2000 ≤ coeff 2 ht ∧ coeff 2 ht ≤ (1187 : ℝ) / 2500 := by
    constructor <;> nlinarith only [hht2_eq, hL_box, hht1]
  have habs2 : |coeff 2 ht| ≤ (1187 : ℝ) / 2500 := abs_le.mpr ⟨by linarith only [hht2], by linarith only [hht2]⟩
  have hht3_eq : coeff 3 ht = (-2 : ℝ) + L * coeff 2 ht := by
    rw [ht_recur 2, hg3]
  have hht3 : (-11987 : ℝ) / 10000 ≤ coeff 3 ht ∧ coeff 3 ht ≤ (-599 : ℝ) / 500 := by
    constructor <;> nlinarith only [hht3_eq, hL_box, hht2]
  have habs3 : |coeff 3 ht| ≤ (11987 : ℝ) / 10000 := abs_le.mpr ⟨by linarith only [hht3], by linarith only [hht3]⟩
  have hht4_eq : coeff 4 ht = (2 : ℝ) + L * coeff 3 ht := by
    rw [ht_recur 3, hg4]
  have hht4 : (-123 : ℝ) / 5000 ≤ coeff 4 ht ∧ coeff 4 ht ≤ (-233 : ℝ) / 10000 := by
    constructor <;> nlinarith only [hht4_eq, hL_box, hht3]
  have habs4 : |coeff 4 ht| ≤ (123 : ℝ) / 5000 := abs_le.mpr ⟨by linarith only [hht4], by linarith only [hht4]⟩
  have hht5_eq : coeff 5 ht = (-1 : ℝ) + L * coeff 4 ht := by
    rw [ht_recur 4, hg5]
  have hht5 : (-651 : ℝ) / 625 ≤ coeff 5 ht ∧ coeff 5 ht ≤ (-10393 : ℝ) / 10000 := by
    constructor <;> nlinarith only [hht5_eq, hL_box, hht4]
  have habs5 : |coeff 5 ht| ≤ (651 : ℝ) / 625 := abs_le.mpr ⟨by linarith only [hht5], by linarith only [hht5]⟩
  have hht6_eq : coeff 6 ht = (2 : ℝ) + L * coeff 5 ht := by
    rw [ht_recur 5, hg6]
  have hht6 : (301 : ℝ) / 1250 ≤ coeff 6 ht ∧ coeff 6 ht ≤ (153 : ℝ) / 625 := by
    constructor <;> nlinarith only [hht6_eq, hL_box, hht5]
  have habs6 : |coeff 6 ht| ≤ (153 : ℝ) / 625 := abs_le.mpr ⟨by linarith only [hht6], by linarith only [hht6]⟩
  have hht7_eq : coeff 7 ht = (-1 : ℝ) + L * coeff 6 ht := by
    rw [ht_recur 6, hg7]
  have hht7 : (-2967 : ℝ) / 5000 ≤ coeff 7 ht ∧ coeff 7 ht ≤ (-1173 : ℝ) / 2000 := by
    constructor <;> nlinarith only [hht7_eq, hL_box, hht6]
  have habs7 : |coeff 7 ht| ≤ (2967 : ℝ) / 5000 := abs_le.mpr ⟨by linarith only [hht7], by linarith only [hht7]⟩
  have hht8_eq : coeff 8 ht = (2 : ℝ) + L * coeff 7 ht := by
    rw [ht_recur 7, hg8]
  have hht8 : (9977 : ℝ) / 10000 ≤ coeff 8 ht ∧ coeff 8 ht ≤ (2019 : ℝ) / 2000 := by
    constructor <;> nlinarith only [hht8_eq, hL_box, hht7]
  have habs8 : |coeff 8 ht| ≤ (2019 : ℝ) / 2000 := abs_le.mpr ⟨by linarith only [hht8], by linarith only [hht8]⟩
  have hht9_eq : coeff 9 ht = (-2 : ℝ) + L * coeff 8 ht := by
    rw [ht_recur 8, hg9]
  have hht9 : (-63 : ℝ) / 200 ≤ coeff 9 ht ∧ coeff 9 ht ≤ (-59 : ℝ) / 200 := by
    constructor <;> nlinarith only [hht9_eq, hL_box, hht8]
  have habs9 : |coeff 9 ht| ≤ (63 : ℝ) / 200 := abs_le.mpr ⟨by linarith only [hht9], by linarith only [hht9]⟩
  set R : ℝ := 62 / 100
  have hR_pos : 0 < R := by norm_num [R]
  have hR_lt1 : R < 1 := by norm_num [R]
  have hu0 : coeff 0 (ht - 1) = 0 := by
    simp [map_sub, hht0]
  have hu_succ : ∀ n : ℕ, coeff (n + 1) (ht - 1) = coeff (n + 1) ht := by
    intro n
    simp [map_sub, PowerSeries.coeff_one]
  have hu_summable : Summable (fun n : ℕ => |coeff n (ht - 1)| * R ^ n) := by
    have hdom : Summable (fun n : ℕ => (3 : ℝ) * R ^ n) :=
      (summable_geometric_of_lt_one (le_of_lt hR_pos) hR_lt1).mul_left 3
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hdom
    cases n with
    | zero =>
      rw [hu0, abs_zero, zero_mul]
      positivity
    | succ n =>
      rw [hu_succ]
      exact mul_le_mul_of_nonneg_right (hht_bound (n + 1)) (pow_nonneg (le_of_lt hR_pos) _)
  have hu_norm_le : ∑' n : ℕ, |coeff n (ht - 1)| * R ^ n ≤ 9 / 10 := by
    rw [← hu_summable.sum_add_tsum_nat_add 10]
    have htail_dom : Summable (fun k : ℕ => (3 : ℝ) * R ^ 10 * R ^ k) :=
      (summable_geometric_of_lt_one (le_of_lt hR_pos) hR_lt1).mul_left (3 * R ^ 10)
    have htail_sum : Summable (fun k : ℕ => |coeff (k + 10) (ht - 1)| * R ^ (k + 10)) :=
      hu_summable.comp_injective (add_left_injective 10)
    have htail_le : ∑' k : ℕ, |coeff (k + 10) (ht - 1)| * R ^ (k + 10) ≤ 3 * R ^ 10 / (1 - R) := by
      calc
        ∑' k : ℕ, |coeff (k + 10) (ht - 1)| * R ^ (k + 10)
          ≤ ∑' k : ℕ, (3 : ℝ) * R ^ 10 * R ^ k := by
            refine Summable.tsum_le_tsum (fun k => ?_) htail_sum htail_dom
            have hidx : k + 10 = (k + 9) + 1 := by omega
            rw [hidx, hu_succ, ← hidx, pow_add]
            have hb := hht_bound (k + 10)
            have hp : 0 ≤ R ^ k * R ^ 10 :=
              mul_nonneg (pow_nonneg (le_of_lt hR_pos) k) (pow_nonneg (le_of_lt hR_pos) 10)
            nlinarith only [hb, hp]
        _ = 3 * R ^ 10 / (1 - R) := by
            rw [tsum_mul_left, tsum_geometric_of_lt_one (le_of_lt hR_pos) hR_lt1, div_eq_mul_inv]
    have hhead : ∑ n ∈ Finset.range 10, |coeff n (ht - 1)| * R ^ n =
        |coeff 1 ht| * R ^ 1 + |coeff 2 ht| * R ^ 2 + |coeff 3 ht| * R ^ 3 +
        |coeff 4 ht| * R ^ 4 + |coeff 5 ht| * R ^ 5 + |coeff 6 ht| * R ^ 6 +
        |coeff 7 ht| * R ^ 7 + |coeff 8 ht| * R ^ 8 + |coeff 9 ht| * R ^ 9 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
        hu0, abs_zero, zero_mul, hu_succ]
    rw [hhead]
    have hm1 : |coeff 1 ht| * R ^ 1 ≤ (3111 : ℝ) / 10000 * R ^ 1 :=
      mul_le_mul_of_nonneg_right habs1 (by positivity)
    have hm2 : |coeff 2 ht| * R ^ 2 ≤ (1187 : ℝ) / 2500 * R ^ 2 :=
      mul_le_mul_of_nonneg_right habs2 (by positivity)
    have hm3 : |coeff 3 ht| * R ^ 3 ≤ (11987 : ℝ) / 10000 * R ^ 3 :=
      mul_le_mul_of_nonneg_right habs3 (by positivity)
    have hm4 : |coeff 4 ht| * R ^ 4 ≤ (123 : ℝ) / 5000 * R ^ 4 :=
      mul_le_mul_of_nonneg_right habs4 (by positivity)
    have hm5 : |coeff 5 ht| * R ^ 5 ≤ (651 : ℝ) / 625 * R ^ 5 :=
      mul_le_mul_of_nonneg_right habs5 (by positivity)
    have hm6 : |coeff 6 ht| * R ^ 6 ≤ (153 : ℝ) / 625 * R ^ 6 :=
      mul_le_mul_of_nonneg_right habs6 (by positivity)
    have hm7 : |coeff 7 ht| * R ^ 7 ≤ (2967 : ℝ) / 5000 * R ^ 7 :=
      mul_le_mul_of_nonneg_right habs7 (by positivity)
    have hm8 : |coeff 8 ht| * R ^ 8 ≤ (2019 : ℝ) / 2000 * R ^ 8 :=
      mul_le_mul_of_nonneg_right habs8 (by positivity)
    have hm9 : |coeff 9 ht| * R ^ 9 ≤ (63 : ℝ) / 200 * R ^ 9 :=
      mul_le_mul_of_nonneg_right habs9 (by positivity)
    have hnum : (3111 : ℝ) / 10000 * R ^ 1 + (1187 : ℝ) / 2500 * R ^ 2 + (11987 : ℝ) / 10000 * R ^ 3 + (123 : ℝ) / 5000 * R ^ 4 + (651 : ℝ) / 625 * R ^ 5 + (153 : ℝ) / 625 * R ^ 6 + (2967 : ℝ) / 5000 * R ^ 7 + (2019 : ℝ) / 2000 * R ^ 8 + (63 : ℝ) / 200 * R ^ 9 + 3 * R ^ 10 / (1 - R) ≤ 9 / 10 := by
      norm_num [R]
    linarith only [hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, htail_le, hnum]
  exact ⟨ht, hht0, hht_eq_g, hht_bound, hu_summable, hu_norm_le⟩

private lemma q_properties (ht : PowerSeries ℝ) (r₀ : ℝ)
    (hr0_pos : 0 < r₀) (hr0_lt_R : r₀ < 62 / 100)
    (hht0 : coeff 0 ht = 1) (hht_bound : ∀ n : ℕ, |coeff n ht| ≤ 3)
    (hu_summable : Summable (fun n : ℕ => |coeff n (ht - 1)| * (62 / 100 : ℝ) ^ n))
    (hu_norm_le : ∑' n : ℕ, |coeff n (ht - 1)| * (62 / 100 : ℝ) ^ n ≤ 9 / 10) :
    ∃ q : PowerSeries ℝ,
      ht * q = 1 ∧
      coeff 0 q = 1 ∧
      Summable (fun n : ℕ => |coeff n q| * (62 / 100 : ℝ) ^ n) ∧
      ∑' n : ℕ, |coeff n q| * (62 / 100 : ℝ) ^ n ≤ 10 ∧
      0 < ∑' n : ℕ, coeff n q * r₀ ^ n := by
  set R : ℝ := 62 / 100
  have hR_pos : 0 < R := by norm_num [R]
  let u : PowerSeries ℝ := ht - 1
  have hu0 : coeff 0 u = 0 := by simp [u, map_sub, hht0]
  have hu_succ : ∀ n : ℕ, coeff (n + 1) u = coeff (n + 1) ht := by
    intro n
    simp [u, map_sub, PowerSeries.coeff_one]
  have hht_const : PowerSeries.constantCoeff ht ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, hht0]
    norm_num
  let q : PowerSeries ℝ := ht⁻¹
  have hht_q : ht * q = 1 := PowerSeries.mul_inv_cancel ht hht_const
  have hq0 : coeff 0 q = 1 := by
    have h0 := congrArg (PowerSeries.coeff 0) hht_q
    rw [coeff_mul_eq_sum_range, Finset.sum_range_one, Nat.sub_self, hht0, one_mul,
      PowerSeries.coeff_one] at h0
    simpa using h0
  have hq_eq : q = 1 - u * q := by
    have hu_def : ht = 1 + u := by simp [u]
    rw [hu_def, add_mul, one_mul] at hht_q
    exact eq_sub_of_add_eq hht_q
  have hq_partial : ∀ N : ℕ, ∑ n ∈ Finset.range N, |coeff n q| * R ^ n ≤ 10 := by
    intro N
    cases N with
    | zero => simp
    | succ N =>
      set SN : ℝ := ∑ n ∈ Finset.range (N + 1), |coeff n q| * R ^ n
      have hSN_le : SN ≤ 1 + (9 / 10) * SN := by
        have hsplit : SN = 1 + ∑ n ∈ Finset.Ico 1 (N + 1), |coeff n q| * R ^ n := by
          have h1 : Finset.range (N + 1) = insert 0 (Finset.Ico 1 (N + 1)) := by
            ext n
            simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
            omega
          rw [show SN = ∑ n ∈ Finset.range (N + 1), |coeff n q| * R ^ n from rfl,
            h1, Finset.sum_insert (by simp), hq0, abs_one, pow_zero, mul_one]
        have hterm : ∀ n ∈ Finset.Ico 1 (N + 1),
            |coeff n q| * R ^ n ≤
            ∑ k ∈ Finset.range (n + 1),
              (|coeff k u| * R ^ k) * (|coeff (n - k) q| * R ^ (n - k)) := by
          intro n hn
          have hn0 : n ≠ 0 := by
            simp only [Finset.mem_Ico] at hn
            omega
          have hqn : coeff n q = - ∑ k ∈ Finset.range (n + 1), coeff k u * coeff (n - k) q := by
            have h := congrArg (PowerSeries.coeff n) hq_eq
            rw [map_sub, PowerSeries.coeff_one, coeff_mul_eq_sum_range] at h
            have hif : (if n = 0 then (1 : ℝ) else 0) = 0 := by simp [hn0]
            rw [hif, zero_sub] at h
            exact h
          rw [hqn, abs_neg]
          calc
            |∑ k ∈ Finset.range (n + 1), coeff k u * coeff (n - k) q| * R ^ n
              ≤ (∑ k ∈ Finset.range (n + 1), |coeff k u * coeff (n - k) q|) * R ^ n :=
                mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _)
                  (pow_nonneg (le_of_lt hR_pos) n)
            _ = ∑ k ∈ Finset.range (n + 1),
                  (|coeff k u| * R ^ k) * (|coeff (n - k) q| * R ^ (n - k)) := by
                rw [Finset.sum_mul]
                refine Finset.sum_congr rfl fun k hk => ?_
                have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
                have hpow : R ^ n = R ^ k * R ^ (n - k) := by
                  rw [← pow_add, Nat.add_sub_of_le hkn]
                rw [abs_mul, hpow]
                ring
        have hsum_Ico : ∑ n ∈ Finset.Ico 1 (N + 1), |coeff n q| * R ^ n ≤
            ∑ n ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (n + 1),
              (|coeff k u| * R ^ k) * (|coeff (n - k) q| * R ^ (n - k)) := by
          calc
            ∑ n ∈ Finset.Ico 1 (N + 1), |coeff n q| * R ^ n
              ≤ ∑ n ∈ Finset.Ico 1 (N + 1), ∑ k ∈ Finset.range (n + 1),
                  (|coeff k u| * R ^ k) * (|coeff (n - k) q| * R ^ (n - k)) :=
                Finset.sum_le_sum hterm
            _ ≤ ∑ n ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (n + 1),
                  (|coeff k u| * R ^ k) * (|coeff (n - k) q| * R ^ (n - k)) := by
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by
                  exact Finset.sum_nonneg fun _ _ => by positivity)
                intro n hn
                simp only [Finset.mem_Ico, Finset.mem_range] at hn ⊢
                exact hn.2
        have htri : ∑ n ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (n + 1),
            (|coeff k u| * R ^ k) * (|coeff (n - k) q| * R ^ (n - k)) ≤
            (∑ k ∈ Finset.range (N + 1), |coeff k u| * R ^ k) * SN := by
          have hsig : ∑ n ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (n + 1),
              (|coeff k u| * R ^ k) * (|coeff (n - k) q| * R ^ (n - k)) =
              ∑ p ∈ (Finset.range (N + 1)).sigma (fun n => Finset.range (n + 1)),
                (|coeff p.2 u| * R ^ p.2) * (|coeff (p.1 - p.2) q| * R ^ (p.1 - p.2)) := by
            rw [Finset.sum_sigma']
          rw [hsig, Finset.sum_mul_sum, ← Finset.sum_product']
          have himg :
              ∑ p ∈ (Finset.range (N + 1)).sigma (fun n => Finset.range (n + 1)),
                (|coeff p.2 u| * R ^ p.2) * (|coeff (p.1 - p.2) q| * R ^ (p.1 - p.2)) =
              ∑ x ∈ (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter (fun x => x.1 + x.2 ≤ N),
                (|coeff x.1 u| * R ^ x.1) * (|coeff x.2 q| * R ^ x.2) := by
            refine Finset.sum_bij (fun p _ => (p.2, p.1 - p.2)) ?_ ?_ ?_ ?_
            · intro p hp
              simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter,
                Finset.mem_product] at hp ⊢
              omega
            · rintro ⟨n1, k1⟩ hp1 ⟨n2, k2⟩ hp2 heq
              simp only [Finset.mem_sigma, Finset.mem_range] at hp1 hp2
              have h1 : k1 = k2 := congrArg Prod.fst heq
              have h2 : n1 - k1 = n2 - k2 := congrArg Prod.snd heq
              have hn : n1 = n2 := by omega
              subst h1
              subst hn
              rfl
            · intro x hx
              simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx
              refine ⟨⟨x.1 + x.2, x.1⟩, ?_, ?_⟩
              · simp only [Finset.mem_sigma, Finset.mem_range]
                omega
              · ext <;> simp
            · intro p _
              rfl
          rw [himg]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => by positivity)
        have hu_part : ∑ k ∈ Finset.range (N + 1), |coeff k u| * R ^ k ≤ 9 / 10 :=
          le_trans (hu_summable.sum_le_tsum (Finset.range (N + 1)) (fun _ _ => by positivity))
            hu_norm_le
        have hSN_nonneg : 0 ≤ SN := Finset.sum_nonneg fun _ _ => by positivity
        have hprod : (∑ k ∈ Finset.range (N + 1), |coeff k u| * R ^ k) * SN ≤ (9 / 10) * SN :=
          mul_le_mul_of_nonneg_right hu_part hSN_nonneg
        calc
          SN = 1 + ∑ n ∈ Finset.Ico 1 (N + 1), |coeff n q| * R ^ n := hsplit
          _ ≤ 1 + ∑ n ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (n + 1),
                (|coeff k u| * R ^ k) * (|coeff (n - k) q| * R ^ (n - k)) :=
                add_le_add le_rfl hsum_Ico
          _ ≤ 1 + (∑ k ∈ Finset.range (N + 1), |coeff k u| * R ^ k) * SN :=
                add_le_add le_rfl htri
          _ ≤ 1 + (9 / 10) * SN := add_le_add le_rfl hprod
      linarith only [hSN_le]
  have hq_summable : Summable (fun n : ℕ => |coeff n q| * R ^ n) :=
    summable_of_sum_range_le (fun n => by positivity) hq_partial
  have hq_norm_le : ∑' n : ℕ, |coeff n q| * R ^ n ≤ 10 :=
    tsum_le_of_sum_range_le hq_summable hq_partial
  have hr0_lt1 : r₀ < 1 := by
    have hR_lt : R < 1 := by norm_num [R]
    linarith only [hr0_lt_R, hR_lt]
  have hht_r0_abs : Summable (fun n : ℕ => ‖coeff n ht * r₀ ^ n‖) := by
    have hdom : Summable (fun n : ℕ => (3 : ℝ) * r₀ ^ n) :=
      (summable_geometric_of_lt_one (le_of_lt hr0_pos) hr0_lt1).mul_left 3
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hdom
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (le_of_lt hr0_pos)]
    exact mul_le_mul_of_nonneg_right (hht_bound n) (pow_nonneg (le_of_lt hr0_pos) n)
  have hq_r0_abs : Summable (fun n : ℕ => ‖coeff n q * r₀ ^ n‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hq_summable
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (le_of_lt hr0_pos)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_of_lt hr0_pos) (le_of_lt hr0_lt_R) n)
      (abs_nonneg _)
  have hht_q_eval : (∑' n : ℕ, coeff n ht * r₀ ^ n) * (∑' n : ℕ, coeff n q * r₀ ^ n) = 1 := by
    rw [tsum_eval_mul ht q r₀ hht_r0_abs hq_r0_abs, hht_q]
    have h1 : ∀ n : ℕ, coeff n (1 : PowerSeries ℝ) * r₀ ^ n = if n = 0 then 1 else 0 := by
      intro n
      rw [PowerSeries.coeff_one]
      split_ifs with hn
      · subst hn; simp
      · simp
    simp_rw [h1]
    rw [tsum_ite_eq]
  have hht_eval_pos : (1 : ℝ) / 10 ≤ ∑' n : ℕ, coeff n ht * r₀ ^ n := by
    have hu_r0_abs : Summable (fun n : ℕ => ‖coeff n u * r₀ ^ n‖) := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hu_summable
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (le_of_lt hr0_pos)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_of_lt hr0_pos) (le_of_lt hr0_lt_R) n)
        (abs_nonneg _)
    have hht_split : ∑' n : ℕ, coeff n ht * r₀ ^ n = 1 + ∑' n : ℕ, coeff n u * r₀ ^ n := by
      rw [hht_r0_abs.of_norm.tsum_eq_zero_add, hu_r0_abs.of_norm.tsum_eq_zero_add,
        hht0, hu0, pow_zero, mul_one, zero_mul, zero_add]
      congr 1
      congr 1
      ext n
      rw [hu_succ]
    have habs : |∑' n : ℕ, coeff n u * r₀ ^ n| ≤ 9 / 10 := by
      calc
        |∑' n : ℕ, coeff n u * r₀ ^ n|
          = ‖∑' n : ℕ, coeff n u * r₀ ^ n‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∑' n : ℕ, ‖coeff n u * r₀ ^ n‖ := norm_tsum_le_tsum_norm hu_r0_abs
        _ ≤ ∑' n : ℕ, |coeff n u| * R ^ n := by
            refine Summable.tsum_le_tsum (fun n => ?_) hu_r0_abs hu_summable
            rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (le_of_lt hr0_pos)]
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (le_of_lt hr0_pos) (le_of_lt hr0_lt_R) n) (abs_nonneg _)
        _ ≤ 9 / 10 := hu_norm_le
    linarith only [hht_split, (abs_le.mp habs).1]
  have hq_eval_pos : 0 < ∑' n : ℕ, coeff n q * r₀ ^ n := by
    rcases lt_or_ge 0 (∑' n : ℕ, coeff n q * r₀ ^ n) with hpos | hle
    · exact hpos
    · exfalso
      nlinarith only [hht_q_eval, hht_eval_pos, hle]
  exact ⟨q, hht_q, hq0, hq_summable, hq_norm_le, hq_eval_pos⟩

private lemma ratio_limit_of_q (ht q : PowerSeries ℝ) (r₀ L : ℝ)
    (hr0_pos : 0 < r₀) (hr0_lt_R : r₀ < 62 / 100) (hL_def : L = 1 / r₀)
    (hht_eq_g : (1 - PowerSeries.C L * PowerSeries.X) * ht = g)
    (hht_q : ht * q = 1) (hq0 : coeff 0 q = 1)
    (hq_summable : Summable (fun n : ℕ => |coeff n q| * (62 / 100 : ℝ) ^ n))
    (hq_norm_le : ∑' n : ℕ, |coeff n q| * (62 / 100 : ℝ) ^ n ≤ 10)
    (hq_eval_pos : 0 < ∑' n : ℕ, coeff n q * r₀ ^ n) :
    Tendsto (fun n : ℕ => a (n + 1) / a n) atTop (𝓝 L) := by
  set R : ℝ := 62 / 100
  have hR_pos : 0 < R := by norm_num [R]
  have hL_pos : 0 < L := by rw [hL_def]; exact one_div_pos.mpr hr0_pos
  have hL_r0 : L * r₀ = 1 := by rw [hL_def]; exact one_div_mul_cancel (ne_of_gt hr0_pos)
  have hq_r0_abs : Summable (fun n : ℕ => ‖coeff n q * r₀ ^ n‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hq_summable
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (le_of_lt hr0_pos)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_of_lt hr0_pos) (le_of_lt hr0_lt_R) n)
      (abs_nonneg _)
  let p : PowerSeries ℝ := (1 + PowerSeries.X) * q
  have hp_coeff0 : coeff 0 p = coeff 0 q := by
    simp only [p]
    rw [add_mul, one_mul, map_add, PowerSeries.coeff_zero_X_mul, add_zero]
  have hp_coeff_succ : ∀ n : ℕ, coeff (n + 1) p = coeff (n + 1) q + coeff n q := by
    intro n
    simp only [p]
    rw [add_mul, one_mul, map_add, PowerSeries.coeff_succ_X_mul]
  have hp_summable : Summable (fun n : ℕ => |coeff n p| * R ^ n) := by
    have hshift : Summable (fun n : ℕ => |coeff (n + 1) p| * R ^ (n + 1)) := by
      have h1 : Summable (fun n : ℕ => |coeff (n + 1) q| * R ^ (n + 1)) :=
        hq_summable.comp_injective (add_left_injective 1)
      have h2 : Summable (fun n : ℕ => R * (|coeff n q| * R ^ n)) := hq_summable.mul_left R
      refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) (h1.add h2)
      rw [hp_coeff_succ, pow_succ]
      have htri := abs_add_le (coeff (n + 1) q) (coeff n q)
      have hRp : 0 ≤ R ^ n * R := mul_nonneg (pow_nonneg (le_of_lt hR_pos) n) (le_of_lt hR_pos)
      nlinarith only [htri, hRp]
    exact (summable_nat_add_iff 1).mp hshift
  have hp_norm_le : ∑' n : ℕ, |coeff n p| * R ^ n ≤ 20 := by
    have hq_shift : Summable (fun n : ℕ => |coeff (n + 1) q| * R ^ (n + 1)) :=
      hq_summable.comp_injective (add_left_injective 1)
    have hp_shift : Summable (fun n : ℕ => |coeff (n + 1) p| * R ^ (n + 1)) :=
      hp_summable.comp_injective (add_left_injective 1)
    rw [hp_summable.tsum_eq_zero_add, hp_coeff0, hq0, abs_one, pow_zero, mul_one]
    have hle : ∑' n : ℕ, |coeff (n + 1) p| * R ^ (n + 1) ≤
        ∑' n : ℕ, (|coeff (n + 1) q| * R ^ (n + 1) + R * (|coeff n q| * R ^ n)) := by
      refine Summable.tsum_le_tsum (fun n => ?_) hp_shift (hq_shift.add (hq_summable.mul_left R))
      rw [hp_coeff_succ, pow_succ]
      have htri := abs_add_le (coeff (n + 1) q) (coeff n q)
      have hRp : 0 ≤ R ^ n * R := mul_nonneg (pow_nonneg (le_of_lt hR_pos) n) (le_of_lt hR_pos)
      nlinarith only [htri, hRp]
    rw [hq_shift.tsum_add (hq_summable.mul_left R), tsum_mul_left] at hle
    have hq_tail : ∑' n : ℕ, |coeff (n + 1) q| * R ^ (n + 1) ≤ 9 := by
      have h := hq_summable.tsum_eq_zero_add
      rw [hq0, abs_one, pow_zero, mul_one] at h
      linarith only [h, hq_norm_le]
    have hR_eq : R = 62 / 100 := rfl
    have hmul : R * ∑' n : ℕ, |coeff n q| * R ^ n ≤ (62 / 100 : ℝ) * 10 := by
      rw [hR_eq]
      exact mul_le_mul_of_nonneg_left hq_norm_le (by norm_num)
    calc
      1 + ∑' n : ℕ, |coeff (n + 1) p| * R ^ (n + 1)
        ≤ 1 + (∑' n : ℕ, |coeff (n + 1) q| * R ^ (n + 1) + R * ∑' n : ℕ, |coeff n q| * R ^ n) :=
          add_le_add le_rfl hle
      _ ≤ 1 + (9 + (62 / 100 : ℝ) * 10) := add_le_add le_rfl (add_le_add hq_tail hmul)
      _ ≤ 20 := by norm_num
  have hp_coeff_bound : ∀ m : ℕ, |coeff m p| ≤ 20 / R ^ m := by
    intro m
    rw [le_div_iff₀ (pow_pos hR_pos m)]
    have hle := hp_summable.sum_le_tsum {m} (fun _ _ => by positivity)
    simp only [Finset.sum_singleton] at hle
    linarith only [hle, hp_norm_le]
  have hp_r0_abs : Summable (fun n : ℕ => ‖coeff n p * r₀ ^ n‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hp_summable
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (le_of_lt hr0_pos)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_of_lt hr0_pos) (le_of_lt hr0_lt_R) n)
      (abs_nonneg _)
  set C : ℝ := ∑' n : ℕ, coeff n p * r₀ ^ n
  have hC_pos : 0 < C := by
    have hC_eq : C = (1 + r₀) * ∑' n : ℕ, coeff n q * r₀ ^ n := by
      have h1X : Summable (fun n : ℕ => ‖coeff n (1 + PowerSeries.X : PowerSeries ℝ) * r₀ ^ n‖) := by
        refine summable_of_ne_finset_zero (s := Finset.range 2) fun n hn => ?_
        simp only [Finset.mem_range] at hn
        have hn0 : n ≠ 0 := by omega
        have hn1 : n ≠ 1 := by omega
        have hc : coeff n (1 + PowerSeries.X : PowerSeries ℝ) = 0 := by
          rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_X]
          simp [hn0, hn1]
        rw [hc, zero_mul, norm_zero]
      have h1X_eval : ∑' n : ℕ, coeff n (1 + PowerSeries.X : PowerSeries ℝ) * r₀ ^ n = 1 + r₀ := by
        rw [tsum_eq_sum (s := Finset.range 2)]
        · simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
            map_add, PowerSeries.coeff_one, PowerSeries.coeff_X]
          norm_num
        · intro n hn
          simp only [Finset.mem_range] at hn
          have hn0 : n ≠ 0 := by omega
          have hn1 : n ≠ 1 := by omega
          rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_X]
          simp [hn0, hn1]
      have hmul := tsum_eval_mul (1 + PowerSeries.X) q r₀ h1X hq_r0_abs
      rw [h1X_eval] at hmul
      exact hmul.symm
    rw [hC_eq]
    exact mul_pos (by linarith only [hr0_pos]) hq_eval_pos
  have hpow_rew : ∀ n k : ℕ,
      (20 / R ^ (n + k + 1)) * r₀ ^ (k + 1) = (20 / R ^ n) * (r₀ / R) * (r₀ / R) ^ k := by
    intro n k
    rw [div_pow r₀ R k, pow_add R (n + k) 1, pow_add R n k, pow_one, pow_succ r₀ k,
      div_mul_eq_mul_div, div_mul_div_comm, div_mul_div_comm]
    congr 1 <;> ring
  let s : PowerSeries ℝ := PowerSeries.mk fun n => - ∑' k : ℕ, coeff (n + k + 1) p * r₀ ^ (k + 1)
  have hsum_s_tail : ∀ n : ℕ, Summable (fun k : ℕ => ‖coeff (n + k + 1) p * r₀ ^ (k + 1)‖) := by
    intro n
    have hdom : Summable (fun k : ℕ => (20 / R ^ n) * (r₀ / R) * (r₀ / R) ^ k) :=
      (summable_geometric_of_lt_one (div_nonneg (le_of_lt hr0_pos) (le_of_lt hR_pos))
        ((div_lt_one hR_pos).mpr hr0_lt_R)).mul_left ((20 / R ^ n) * (r₀ / R))
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) hdom
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (le_of_lt hr0_pos), ← hpow_rew]
    exact mul_le_mul_of_nonneg_right (hp_coeff_bound (n + k + 1)) (pow_nonneg (le_of_lt hr0_pos) _)
  have hs_eq : PowerSeries.C C + (1 - PowerSeries.C L * PowerSeries.X) * s = p := by
    ext n
    rw [map_add, sub_mul, one_mul, mul_assoc, map_sub, PowerSeries.coeff_C_mul]
    cases n with
    | zero =>
      rw [PowerSeries.coeff_zero_C, PowerSeries.coeff_zero_X_mul, mul_zero, sub_zero]
      have hC_split := hp_r0_abs.of_norm.tsum_eq_zero_add
      have hC_eq : C = coeff 0 p + ∑' k : ℕ, coeff (k + 1) p * r₀ ^ (k + 1) := by
        simpa [C] using hC_split
      simp only [s, PowerSeries.coeff_mk, zero_add]
      linarith only [hC_eq]
    | succ n =>
      rw [PowerSeries.coeff_C, PowerSeries.coeff_succ_X_mul]
      have hif : (if n + 1 = 0 then C else 0) = 0 := by simp
      rw [hif, zero_add]
      have hs := (hsum_s_tail n).of_norm.tsum_eq_zero_add
      have hshift : coeff n s = -r₀ * coeff (n + 1) p + r₀ * coeff (n + 1) s := by
        simp only [s, PowerSeries.coeff_mk]
        rw [hs, add_zero, pow_one]
        have hfactor : ∑' k : ℕ, coeff (n + (k + 1) + 1) p * r₀ ^ (k + 1 + 1) =
            r₀ * ∑' k : ℕ, coeff (n + 1 + k + 1) p * r₀ ^ (k + 1) := by
          rw [← tsum_mul_left]
          congr 1
          ext k
          rw [show n + (k + 1) + 1 = n + 1 + k + 1 by omega, pow_succ]
          ring
        rw [hfactor]
        ring
      calc
        coeff (n + 1) s - L * coeff n s
          = coeff (n + 1) s - L * (-r₀ * coeff (n + 1) p + r₀ * coeff (n + 1) s) := by rw [hshift]
        _ = (L * r₀) * coeff (n + 1) p + (1 - L * r₀) * coeff (n + 1) s := by ring
        _ = coeff (n + 1) p := by rw [hL_r0]; ring
  set M : ℝ := 20 * (r₀ / R) / (1 - r₀ / R)
  have hs_bound : ∀ n : ℕ, |coeff n s| ≤ M / R ^ n := by
    intro n
    simp only [s, PowerSeries.coeff_mk, abs_neg]
    have hdom : Summable (fun k : ℕ => (20 / R ^ n) * (r₀ / R) * (r₀ / R) ^ k) :=
      (summable_geometric_of_lt_one (div_nonneg (le_of_lt hr0_pos) (le_of_lt hR_pos))
        ((div_lt_one hR_pos).mpr hr0_lt_R)).mul_left ((20 / R ^ n) * (r₀ / R))
    calc
      |∑' k : ℕ, coeff (n + k + 1) p * r₀ ^ (k + 1)|
        = ‖∑' k : ℕ, coeff (n + k + 1) p * r₀ ^ (k + 1)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' k : ℕ, ‖coeff (n + k + 1) p * r₀ ^ (k + 1)‖ :=
          norm_tsum_le_tsum_norm (hsum_s_tail n)
      _ ≤ ∑' k : ℕ, (20 / R ^ n) * (r₀ / R) * (r₀ / R) ^ k := by
          refine Summable.tsum_le_tsum (fun k => ?_) (hsum_s_tail n) hdom
          rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (le_of_lt hr0_pos), ← hpow_rew]
          exact mul_le_mul_of_nonneg_right (hp_coeff_bound (n + k + 1))
            (pow_nonneg (le_of_lt hr0_pos) _)
      _ = M / R ^ n := by
          rw [tsum_mul_left,
            tsum_geometric_of_lt_one (div_nonneg (le_of_lt hr0_pos) (le_of_lt hR_pos))
              ((div_lt_one hR_pos).mpr hr0_lt_R)]
          simp only [M]
          rw [← div_eq_mul_inv, div_mul_eq_mul_div, div_div, div_div, mul_comm (R ^ n)]
  have hden_p : denominator * p = 1 - PowerSeries.C L * PowerSeries.X := by
    calc
      denominator * p
        = denominator * ((1 + PowerSeries.X) * q) := rfl
      _ = ((1 + PowerSeries.X) * denominator) * q := by ring
      _ = g * q := rfl
      _ = ((1 - PowerSeries.C L * PowerSeries.X) * ht) * q := by rw [hht_eq_g]
      _ = (1 - PowerSeries.C L * PowerSeries.X) * (ht * q) := by ring
      _ = 1 - PowerSeries.C L * PowerSeries.X := by rw [hht_q, mul_one]
  have hden_const : PowerSeries.constantCoeff denominator ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, denominator, PowerSeries.coeff_mk, weight_zero]
    norm_num
  have h1L_const : PowerSeries.constantCoeff (1 - PowerSeries.C L * PowerSeries.X) ≠ 0 := by
    simp [map_sub, map_one, map_mul, PowerSeries.constantCoeff_X]
  have hden_inv : denominator⁻¹ = PowerSeries.C C * (1 - PowerSeries.C L * PowerSeries.X)⁻¹ + s := by
    have h1 : denominator⁻¹ = p * (1 - PowerSeries.C L * PowerSeries.X)⁻¹ := by
      calc
        denominator⁻¹
          = denominator⁻¹ * 1 := (mul_one _).symm
        _ = denominator⁻¹ *
              ((1 - PowerSeries.C L * PowerSeries.X) * (1 - PowerSeries.C L * PowerSeries.X)⁻¹) := by
              rw [PowerSeries.mul_inv_cancel _ h1L_const]
        _ = denominator⁻¹ * ((denominator * p) * (1 - PowerSeries.C L * PowerSeries.X)⁻¹) := by
              rw [hden_p]
        _ = (denominator⁻¹ * denominator) * (p * (1 - PowerSeries.C L * PowerSeries.X)⁻¹) := by
              ring
        _ = p * (1 - PowerSeries.C L * PowerSeries.X)⁻¹ := by
              rw [PowerSeries.inv_mul_cancel _ hden_const, one_mul]
    rw [h1, ← hs_eq, add_mul, mul_comm ((1 - PowerSeries.C L * PowerSeries.X)) s,
      mul_assoc s, PowerSeries.mul_inv_cancel _ h1L_const, mul_one]
  have ha_eq : ∀ n : ℕ, a n = C * L ^ n + coeff n s := by
    intro n
    rw [a, hden_inv, map_add, PowerSeries.coeff_C_mul, geom_inv_eq, PowerSeries.coeff_mk]
  have hs_div_tendsto : Tendsto (fun n : ℕ => coeff n s / L ^ n) atTop (𝓝 0) := by
    have hq_lt : r₀ / R < 1 := (div_lt_one hR_pos).mpr hr0_lt_R
    have hq_nn : 0 ≤ r₀ / R := div_nonneg (le_of_lt hr0_pos) (le_of_lt hR_pos)
    have htend : Tendsto (fun n : ℕ => M * (r₀ / R) ^ n) atTop (𝓝 0) := by
      have h0 := (tendsto_pow_atTop_nhds_zero_of_lt_one hq_nn hq_lt).const_mul M
      simpa using h0
    refine squeeze_zero_norm (fun n => ?_) htend
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hL_pos n)]
    calc
      |coeff n s| / L ^ n
        ≤ (M / R ^ n) / L ^ n := div_le_div_of_nonneg_right (hs_bound n) (le_of_lt (pow_pos hL_pos n))
      _ = M * (r₀ / R) ^ n := by
          rw [div_pow r₀ R n, hL_def, one_div, inv_pow, div_inv_eq_mul,
            div_mul_eq_mul_div, mul_div_assoc]
  have hnum_tendsto : Tendsto (fun n : ℕ => a (n + 1) / L ^ n) atTop (𝓝 (C * L)) := by
    have hshift : Tendsto (fun n : ℕ => L * (coeff (n + 1) s / L ^ (n + 1))) atTop (𝓝 0) := by
      have h0 := (hs_div_tendsto.comp (tendsto_add_atTop_nat 1)).const_mul L
      simpa using h0
    have hsum := tendsto_const_nhds (x := C * L).add hshift
    rw [add_zero] at hsum
    refine hsum.congr fun n => ?_
    rw [ha_eq (n + 1), pow_succ, add_div]
    congr 1
    · rw [mul_comm (L ^ n), ← mul_assoc, mul_div_cancel_right₀ (C * L) (ne_of_gt (pow_pos hL_pos n))]
    · rw [mul_div_assoc', mul_comm (L ^ n), div_mul_eq_div_div, mul_div_cancel_left₀ _ (ne_of_gt hL_pos)]
  have hden_tendsto : Tendsto (fun n : ℕ => a n / L ^ n) atTop (𝓝 C) := by
    have hsum := tendsto_const_nhds (x := C).add hs_div_tendsto
    rw [add_zero] at hsum
    refine hsum.congr fun n => ?_
    rw [ha_eq n, add_div, mul_div_cancel_right₀ C (ne_of_gt (pow_pos hL_pos n))]
  have hdiv := hnum_tendsto.div hden_tendsto (ne_of_gt hC_pos)
  rw [mul_div_cancel_left₀ L (ne_of_gt hC_pos)] at hdiv
  refine hdiv.congr fun n => ?_
  exact div_div_div_cancel_right₀ (ne_of_gt (pow_pos hL_pos n)) (a (n + 1)) (a n)

theorem OMA.solution : type_of% @OMA.S_oeis_a281112.main := by
  rcases exists_root_r0 with ⟨r₀, hr0_lo, hr0_hi, hg0⟩
  have hd_pos : (0 : ℝ) < (digits : ℝ) := by unfold digits; positivity
  have hP85_eq : (P85 : ℝ) = (10 : ℝ) ^ 85 := by unfold P85; norm_num
  have hr0_pos : 0 < r₀ := by
    have hpos : (0 : ℝ) < (P85 : ℝ) / ((digits : ℝ) + 1) := by unfold P85; positivity
    linarith
  have hr0_lt : r₀ < 5921 / 10000 := by
    have hhi : (P85 : ℝ) / (digits : ℝ) ≤ 5921 / 10000 := by unfold P85 digits; norm_num
    linarith
  set L : ℝ := 1 / r₀ with hL_def
  have hL_r0 : L * r₀ = 1 := one_div_mul_cancel (ne_of_gt hr0_pos)
  have hL_lo : (digits : ℝ) / 10 ^ 85 < L := by
    rw [hL_def, div_lt_div_iff₀ (by positivity) hr0_pos, one_mul]
    rw [hP85_eq] at hr0_hi
    have h := (lt_div_iff₀ hd_pos).mp hr0_hi
    linarith
  have hL_hi : L < ((digits : ℝ) + 1) / 10 ^ 85 := by
    rw [hL_def, div_lt_div_iff₀ hr0_pos (by positivity), one_mul]
    rw [hP85_eq] at hr0_lo
    have h := (div_lt_iff₀ (by positivity : (0 : ℝ) < (digits : ℝ) + 1)).mp hr0_lo
    linarith
  have hL_box : (168892 : ℝ) / 100000 ≤ L ∧ L ≤ (168893 : ℝ) / 100000 := by
    have h1 : (168892 : ℝ) / 100000 ≤ (digits : ℝ) / 10 ^ 85 := by unfold digits; norm_num
    have h2 : ((digits : ℝ) + 1) / 10 ^ 85 ≤ (168893 : ℝ) / 100000 := by unfold digits; norm_num
    exact ⟨by linarith, by linarith⟩
  rcases ht_properties r₀ L hr0_pos hr0_lt hL_r0 hL_box hg0 with
    ⟨ht, hht0, hht_eq_g, hht_bound, hu_summable, hu_norm_le⟩
  rcases q_properties ht r₀ hr0_pos (by linarith) hht0 hht_bound hu_summable hu_norm_le with
    ⟨q, hht_q, hq0, hq_summable, hq_norm_le, hq_eval_pos⟩
  have hratio := ratio_limit_of_q ht q r₀ L hr0_pos (by linarith) hL_def hht_eq_g hht_q hq0
    hq_summable hq_norm_le hq_eval_pos
  exact ⟨L, hratio, le_of_lt hL_lo, hL_hi⟩
