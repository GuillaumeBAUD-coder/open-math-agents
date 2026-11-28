import OMAStatements.S_oeis_a201089
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

-- Problem: A201089, bounded four-entry arrays with bounded first and second differences.
-- Source: https://oeis.org/A201089
-- Original sequence: R. H. Hardin; conjectured parity formulas: Colin Barker.
-- Statement credit: @VashaTS.
-- The proof counts independent endpoint intervals after fixing the middle pair,
-- uses negation and reversal to reduce the middle pairs to triangular sectors,
-- and evaluates the resulting polynomial sums exactly.

-- Component: A201089Defs

namespace A201089Proof
open Finset

def lo (n : ℕ) (b c : ℤ) : ℤ := -(n : ℤ) + max 0 (max b (2*b-c))
def hi (n : ℕ) (b c : ℤ) : ℤ := (n : ℤ) + min 0 (min b (2*b-c))
def L (n : ℕ) (b c : ℤ) : ℤ := hi n b c - lo n b c + 1

def validMiddle (n : ℕ) (b c : ℤ) : Prop := -(n : ℤ) ≤ c-b ∧ c-b ≤ n
instance (n : ℕ) (b c : ℤ) : Decidable (validMiddle n b c) := inferInstanceAs (Decidable (_ ∧ _))

def weight (n : ℕ) (b c : ℤ) : ℤ :=
  if validMiddle n b c then L n b c * L n c b else 0

noncomputable def countSum (n : ℕ) : ℤ :=
  ∑ b ∈ Icc (-(n : ℤ)) n, ∑ c ∈ Icc (-(n : ℤ)) n, weight n b c

def M (n : ℕ) : ℤ := 2*n+1

def P (n : ℕ) : ℤ :=
  ∑ c ∈ range (n+1), ∑ b ∈ range (c+1),
    (M n - b - max 0 ((c : ℤ)-2*b)) * (M n - 2*c + b)

def D (n : ℕ) : ℤ := ∑ b ∈ range (n+1), (M n-b)^2

def Q (n : ℕ) : ℤ :=
  ∑ u ∈ range (n+1), ∑ v ∈ range (n-u+1),
    (M n-2*u-v)*(M n-u-2*v)

def C (n : ℕ) : ℤ := ∑ t ∈ range (n+1), (M n-t)*(M n-2*t)

end A201089Proof

-- Component: A201089Count

namespace A201089Proof
open Finset OMA.S_oeis_a201089

lemma mem_box_iff (n : ℕ) (x : ℤ) :
    x ∈ box n ↔ -(n : ℤ) ≤ x ∧ x ≤ n := by
  constructor
  · rintro hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    have := Finset.mem_range.mp hk
    omega
  · intro hx
    have hcast : (((x + n).toNat : ℕ) : ℤ) = x + n := Int.toNat_of_nonneg (by omega)
    apply Finset.mem_image.mpr
    refine ⟨(x + n).toNat, Finset.mem_range.mpr ?_, ?_⟩ <;> omega

lemma endpoint_mem_iff (n : ℕ) (b c x : ℤ) :
    x ∈ Icc (lo n b c) (hi n b c) ↔
      (-(n : ℤ) ≤ x ∧ x ≤ n) ∧
      (-(n : ℤ) ≤ b-x ∧ b-x ≤ n) ∧
      (-(n : ℤ) ≤ c-2*b+x ∧ c-2*b+x ≤ n) := by
  simp only [Finset.mem_Icc, lo, hi]
  omega

private def arrays (n : ℕ) : Finset (Fin 4 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 4 => box n).filter fun x =>
    (∀ i, diff x i ∈ box n) ∧ ∀ i, diff (diff x) i ∈ box n

private lemma arrays_mem_iff (n : ℕ) (x : Fin 4 → ℤ) :
    x ∈ arrays n ↔
      x 1 ∈ Icc (-(n : ℤ)) n ∧ x 2 ∈ Icc (-(n : ℤ)) n ∧
      validMiddle n (x 1) (x 2) ∧
      x 0 ∈ Icc (lo n (x 1) (x 2)) (hi n (x 1) (x 2)) ∧
      x 3 ∈ Icc (lo n (x 2) (x 1)) (hi n (x 2) (x 1)) := by
  rw [endpoint_mem_iff, endpoint_mem_iff]
  simp only [arrays, Finset.mem_filter, Fintype.mem_piFinset, Fin.forall_fin_succ,
    Fin.forall_fin_zero, and_true, diff, mem_box_iff, Finset.mem_Icc, validMiddle]
  simp only [Fin.succ_zero_eq_one, Fin.castSucc_zero,
    show (1 : Fin 2).castSucc = (1 : Fin 3) from rfl,
    show (1 : Fin 2).succ = (2 : Fin 3) from rfl,
    show (1 : Fin 3).castSucc = (1 : Fin 4) from rfl,
    show (1 : Fin 3).succ = (2 : Fin 4) from rfl,
    show (2 : Fin 3).castSucc = (2 : Fin 4) from rfl,
    show (2 : Fin 3).succ = (3 : Fin 4) from rfl]
  omega

private noncomputable def endpoints (n : ℕ) (b c : ℤ) : Finset (ℤ × ℤ) :=
  if validMiddle n b c then
    Icc (lo n b c) (hi n b c) ×ˢ Icc (lo n c b) (hi n c b)
  else ∅

private abbrev Choices := Σ _ : ℤ, Σ _ : ℤ, ℤ × ℤ

private noncomputable def choices (n : ℕ) : Finset Choices :=
  (Icc (-(n : ℤ)) n).sigma fun b =>
    (Icc (-(n : ℤ)) n).sigma fun c => endpoints n b c

private def encode (x : Fin 4 → ℤ) : Choices := ⟨x 1, x 2, x 0, x 3⟩

private def decode (z : Choices) : Fin 4 → ℤ :=
  fun i => match i.val with
    | 0 => z.2.2.1
    | 1 => z.1
    | 2 => z.2.1
    | _ => z.2.2.2

private lemma decode_encode (x : Fin 4 → ℤ) : decode (encode x) = x := by
  funext i
  fin_cases i <;> rfl

private lemma encode_decode (z : Choices) : encode (decode z) = z := by
  rcases z with ⟨b, c, x, y⟩
  rfl

private lemma encode_mem_iff (n : ℕ) (x : Fin 4 → ℤ) :
    encode x ∈ choices n ↔ x ∈ arrays n := by
  rw [arrays_mem_iff]
  simp only [choices, Finset.mem_sigma, encode]
  by_cases h : validMiddle n (x 1) (x 2) <;>
    simp [endpoints, h, and_assoc]

private lemma card_arrays (n : ℕ) : (arrays n).card = (choices n).card := by
  apply Finset.card_bij (fun x _ => encode x)
  · intro x hx
    exact (encode_mem_iff n x).mpr hx
  · intro x hx y hy h
    simpa only [decode_encode] using congrArg decode h
  · intro z hz
    refine ⟨decode z, ?_, encode_decode z⟩
    apply (encode_mem_iff n (decode z)).mp
    simpa only [encode_decode] using hz

lemma endpoint_card (n : ℕ) (b c : ℤ)
    (hb : b ∈ Icc (-(n : ℤ)) n) (hc : c ∈ Icc (-(n : ℤ)) n)
    (hm : validMiddle n b c) :
    ((Icc (lo n b c) (hi n b c)).card : ℤ) = L n b c := by
  have hb' := Finset.mem_Icc.mp hb
  have hc' := Finset.mem_Icc.mp hc
  have hn : 0 ≤ (n : ℤ) := by omega
  have h : lo n b c ≤ hi n b c + 1 := by
    unfold lo hi validMiddle at *
    omega
  rw [Int.card_Icc_of_le _ _ h]
  unfold L
  ring

theorem a_eq_countSum (n : ℕ) : (OMA.S_oeis_a201089.a n : ℤ) = countSum n := by
  change ((arrays n).card : ℤ) = _
  rw [card_arrays]
  simp only [choices, Finset.card_sigma, Nat.cast_sum]
  unfold countSum
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hm : validMiddle n b c
  · have hm' : validMiddle n c b := by unfold validMiddle at *; omega
    simp only [endpoints, hm, if_pos, Finset.card_product, Nat.cast_mul, weight]
    rw [endpoint_card n b c hb hc hm, endpoint_card n c b hc hb hm']
  · simp [endpoints, weight, hm]

end A201089Proof

-- Component: A201089Local

namespace A201089Proof
open Finset

lemma mem_endpoint_iff (n : ℕ) (b c x : ℤ) :
    x ∈ Icc (lo n b c) (hi n b c) ↔
      -(n : ℤ) ≤ x ∧ x ≤ n ∧
      -(n : ℤ) ≤ b-x ∧ b-x ≤ n ∧
      -(n : ℤ) ≤ c-2*b+x ∧ c-2*b+x ≤ n := by
  simp only [mem_Icc, lo, hi]
  constructor
  · rintro ⟨hl, hu⟩
    have h0 := le_max_left (0 : ℤ) (max b (2*b-c))
    have hb := (le_max_left b (2*b-c)).trans (le_max_right 0 (max b (2*b-c)))
    have hc := (le_max_right b (2*b-c)).trans (le_max_right 0 (max b (2*b-c)))
    have h0' := min_le_left (0 : ℤ) (min b (2*b-c))
    have hb' := (min_le_right 0 (min b (2*b-c))).trans (min_le_left b (2*b-c))
    have hc' := (min_le_right 0 (min b (2*b-c))).trans (min_le_right b (2*b-c))
    omega
  · intro h
    constructor
    · have : max (0 : ℤ) (max b (2*b-c)) ≤ x+n := by
        simp only [max_le_iff]
        omega
      omega
    · have : x-n ≤ min (0 : ℤ) (min b (2*b-c)) := by
        simp only [le_min_iff]
        omega
      omega

lemma lo_le_hi (n : ℕ) {b c : ℤ}
    (hb : b ∈ Icc (-(n : ℤ)) n) (hc : c ∈ Icc (-(n : ℤ)) n)
    (hm : validMiddle n b c) : lo n b c ≤ hi n b c := by
  simp only [mem_Icc] at hb hc
  unfold validMiddle at hm
  simp only [lo, hi, max_def, min_def]
  split_ifs <;> omega

lemma weight_swap (n : ℕ) (b c : ℤ) : weight n b c = weight n c b := by
  have h : validMiddle n b c ↔ validMiddle n c b := by unfold validMiddle; omega
  simp only [weight, h]
  split_ifs <;> ring

lemma L_neg (n : ℕ) (b c : ℤ) : L n (-b) (-c) = L n b c := by
  have h : 2*(-b)-(-c) = -(2*b-c) := by ring
  unfold L hi lo
  rw [h, max_neg_neg, min_neg_neg]
  rw [show (0 : ℤ) = -0 by omega, max_neg_neg, min_neg_neg]
  ring

lemma weight_neg (n : ℕ) (b c : ℤ) : weight n (-b) (-c) = weight n b c := by
  have h : validMiddle n (-b) (-c) ↔ validMiddle n b c := by unfold validMiddle; omega
  simp only [weight, h, L_neg]

lemma L_positive (n : ℕ) {b c : ℤ} (hb : 0 ≤ b) (hbc : b ≤ c) :
    L n b c = M n-b-max 0 (c-2*b) := by
  have h1 : 2*b-c ≤ b := by omega
  unfold L hi lo M
  rw [max_eq_left h1, max_eq_right hb, min_eq_right h1]
  by_cases h2 : 0 ≤ c-2*b
  · rw [max_eq_right h2, min_eq_right (by omega)]
    ring
  · rw [max_eq_left (by omega), min_eq_left (by omega)]
    ring

lemma L_positive_swap (n : ℕ) {b c : ℤ} (hb : 0 ≤ b) (hbc : b ≤ c) :
    L n c b = M n-2*c+b := by
  have hc : 0 ≤ c := by omega
  have h1 : c ≤ 2*c-b := by omega
  unfold L hi lo M
  rw [max_eq_right h1, max_eq_right (by omega), min_eq_left h1, min_eq_left hc]
  ring

lemma weight_positive (n b c : ℕ) (hbc : b ≤ c) (hc : c ≤ n) :
    weight n b c = (M n-b-max 0 ((c : ℤ)-2*b))*(M n-2*c+b) := by
  have hm : validMiddle n b c := by unfold validMiddle; omega
  rw [weight, if_pos hm, L_positive n (by omega) (by omega),
    L_positive_swap n (by omega) (by omega)]

lemma weight_cross (n u v : ℕ) :
    weight n (-(u : ℤ)) v =
      if u+v ≤ n then (M n-2*u-v)*(M n-u-2*v) else 0 := by
  have hm : validMiddle n (-(u : ℤ)) v ↔ u+v ≤ n := by unfold validMiddle; omega
  have hl : L n (-(u : ℤ)) v = M n-2*u-v := by
    unfold L hi lo M
    rw [max_eq_left (by omega : 2*(-(u : ℤ))-v ≤ -u), max_eq_left (by omega),
      min_eq_right (by omega : 2*(-(u : ℤ))-v ≤ -u), min_eq_right (by omega)]
    ring
  have hr : L n v (-(u : ℤ)) = M n-u-2*v := by
    unfold L hi lo M
    rw [max_eq_right (by omega : (v : ℤ) ≤ 2*v-(-u)), max_eq_right (by omega),
      min_eq_left (by omega : (v : ℤ) ≤ 2*v-(-u)), min_eq_left (by omega)]
    ring
  simp only [weight, hm, hl, hr]

lemma weight_diag (n b : ℕ) (hb : b ≤ n) : weight n b b = (M n-b)^2 := by
  rw [weight_positive n b b le_rfl hb, max_eq_left (by omega)]
  ring

lemma weight_axis (n t : ℕ) (ht : t ≤ n) :
    weight n 0 t = (M n-t)*(M n-2*t) := by
  simpa only [Nat.cast_zero, mul_zero, sub_zero, add_zero,
    max_eq_right (Int.natCast_nonneg t)] using weight_positive n 0 t (by omega) ht

lemma weight_zero (n : ℕ) : weight n 0 0 = (M n)^2 := by
  simpa using weight_diag n 0 (by omega)

end A201089Proof

-- Component: A201089SumSymmetry

namespace A201089Proof
open Finset

lemma sum_Icc_symmetric (n : ℕ) (f : ℤ → ℤ) :
    (∑ i ∈ Icc (-(n : ℤ)) n, f i) =
      (∑ i ∈ Icc (0 : ℤ) n, f i) + (∑ i ∈ Icc (0 : ℤ) n, f (-i)) - f 0 := by
  have hu : Icc (-(n : ℤ)) 0 ∪ Icc (0 : ℤ) n = Icc (-(n : ℤ)) n := by
    ext x
    simp only [mem_union, mem_Icc]
    omega
  have hi : Icc (-(n : ℤ)) 0 ∩ Icc (0 : ℤ) n = {0} := by
    ext x
    simp only [mem_inter, mem_Icc, mem_singleton]
    omega
  have he : (∑ i ∈ Icc (-(n : ℤ)) 0, f i) = ∑ i ∈ Icc (0 : ℤ) n, f (-i) := by
    apply sum_bij (fun i _ => -i)
    · intro i h
      simp only [mem_Icc] at *
      omega
    · intro i hi j hj hij
      omega
    · intro j hj
      refine ⟨-j, ?_, by omega⟩
      simp only [mem_Icc] at *
      omega
    · intro i hi
      simp
  have h := sum_union_inter (s₁ := Icc (-(n : ℤ)) 0) (s₂ := Icc (0 : ℤ) n) (f := f)
  rw [hu, hi, sum_singleton, he] at h
  omega

lemma sum_Icc_nonnegative (n : ℕ) (f : ℤ → ℤ) :
    (∑ i ∈ Icc (0 : ℤ) n, f i) = ∑ i ∈ range (n+1), f i := by
  apply sum_bij (fun i _ => i.toNat)
  · intro i hi
    simp only [mem_Icc, mem_range] at *
    omega
  · intro i hi j hj hij
    simp only [mem_Icc] at *
    omega
  · intro j hj
    refine ⟨j, ?_, by simp⟩
    simp only [mem_Icc, mem_range] at *
    omega
  · intro i hi
    have h : (i.toNat : ℤ) = i := by simp only [mem_Icc] at hi; omega
    rw [h]

lemma square_quadrants (n : ℕ) (f : ℤ → ℤ → ℤ)
    (hs : ∀ b c, f b c = f c b) (hn : ∀ b c, f (-b) (-c) = f b c) :
    (∑ b ∈ Icc (-(n : ℤ)) n, ∑ c ∈ Icc (-(n : ℤ)) n, f b c) =
      2 * (∑ b ∈ range (n+1), ∑ c ∈ range (n+1), f b c) +
      2 * (∑ b ∈ range (n+1), ∑ c ∈ range (n+1), f (-b) c) -
      4 * (∑ t ∈ range (n+1), f 0 t) + f 0 0 := by
  have hcross (b c : ℤ) : f b (-c) = f (-b) c := by simpa using hn (-b) c
  have haxis (b : ℤ) : f b 0 = f 0 b := hs b 0
  have hzero (c : ℤ) : f 0 (-c) = f 0 c := by simpa using hn 0 c
  rw [sum_Icc_symmetric]
  simp_rw [sum_Icc_symmetric]
  simp only [sum_add_distrib, sum_sub_distrib]
  simp_rw [hn, hcross, haxis, hzero]
  simp_rw [sum_Icc_nonnegative]
  ring

lemma square_triangle (m : ℕ) (f : ℕ → ℕ → ℤ) (hs : ∀ b c, f b c = f c b) :
    (∑ b ∈ range m, ∑ c ∈ range m, f b c) =
      2 * (∑ c ∈ range m, ∑ b ∈ range (c+1), f b c) - ∑ b ∈ range m, f b b := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsym : (∑ b ∈ range m, f m b) = ∑ b ∈ range m, f b m := by
      apply sum_congr rfl
      intro b hb
      exact hs m b
    have hsq : (∑ b ∈ range (m+1), ∑ c ∈ range (m+1), f b c) =
        (∑ b ∈ range m, ∑ c ∈ range m, f b c) +
        2 * (∑ b ∈ range m, f b m) + f m m := by
      rw [sum_range_succ]
      simp_rw [sum_range_succ]
      rw [sum_add_distrib, hsym]
      ring
    have htri : (∑ c ∈ range (m+1), ∑ b ∈ range (c+1), f b c) =
        (∑ c ∈ range m, ∑ b ∈ range (c+1), f b c) +
        (∑ b ∈ range m, f b m) + f m m := by
      rw [sum_range_succ (f := fun c => ∑ b ∈ range (c+1), f b c),
        sum_range_succ (f := fun b => f b m)]
      ring
    rw [hsq, htri, sum_range_succ, ih]
    ring

lemma sum_cut_triangle (n u : ℕ) (hu : u ≤ n) (f : ℕ → ℤ) :
    (∑ v ∈ range (n+1), if u+v ≤ n then f v else 0) =
      ∑ v ∈ range (n-u+1), f v := by
  have hs : range (n-u+1) ⊆ range (n+1) := by intro v hv; simp only [mem_range] at *; omega
  have h := sum_subset hs (f := fun v => if u+v ≤ n then f v else 0) (by
    intro v hv hnot
    simp only [mem_range] at *
    rw [if_neg (by omega)])
  rw [← h]
  apply sum_congr rfl
  intro v hv
  simp only [mem_range] at hv
  rw [if_pos (by omega)]

end A201089Proof

-- Component: A201089Geometry

namespace A201089Proof
open Finset

lemma countSum_eq (n : ℕ) :
    countSum n = 4 * P n - 2 * D n + 2 * Q n - 4 * C n + (M n)^2 := by
  have ht : (∑ c ∈ range (n+1), ∑ b ∈ range (c+1), weight n b c) = P n := by
    unfold P
    apply sum_congr rfl
    intro c hc
    apply sum_congr rfl
    intro b hb
    apply weight_positive
    · simp only [mem_range] at hb
      omega
    · simp only [mem_range] at hc
      omega
  have hd : (∑ b ∈ range (n+1), weight n b b) = D n := by
    unfold D
    apply sum_congr rfl
    intro b hb
    apply weight_diag
    simp only [mem_range] at hb
    omega
  have hp : (∑ b ∈ range (n+1), ∑ c ∈ range (n+1), weight n b c) = 2*P n-D n := by
    rw [square_triangle (n+1) (fun b c => weight n b c) (fun b c => weight_swap n b c), ht, hd]
  have hq : (∑ u ∈ range (n+1), ∑ v ∈ range (n+1), weight n (-(u : ℤ)) v) = Q n := by
    unfold Q
    apply sum_congr rfl
    intro u hu
    simp_rw [weight_cross]
    apply sum_cut_triangle
    simp only [mem_range] at hu
    omega
  have hc : (∑ t ∈ range (n+1), weight n 0 t) = C n := by
    unfold C
    apply sum_congr rfl
    intro t ht
    apply weight_axis
    simp only [mem_range] at ht
    omega
  unfold countSum
  rw [square_quadrants n (weight n) (weight_swap n) (weight_neg n), hp, hq, hc, weight_zero]
  ring

end A201089Proof

-- Component: A201089SimpleSums

namespace A201089Proof
open Finset

private lemma simple_sum_quadratic (n : ℕ) (a b c : ℤ) :
    6 * (∑ i ∈ range (n+1), (a*(i:ℤ)^2+b*i+c)) =
      a*n*(n+1)*(2*n+1)+3*b*n*(n+1)+6*c*(n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    simp only [Nat.cast_succ]
    linear_combination ih

private lemma square_sum_formula (m : ℤ) (n : ℕ) :
    6 * (∑ b ∈ range (n+1), (m-b)^2) =
      6*m^2*n+6*m^2-6*m*n^2-6*m*n+2*(n:ℤ)^3+3*n^2+n := by
  have he : (∑ b ∈ range (n+1), (m-b)^2) =
      ∑ b ∈ range (n+1), (1*(b:ℤ)^2+(-2*m)*b+m^2) := by
    apply sum_congr rfl
    intro b hb
    ring
  rw [he, simple_sum_quadratic]
  ring

private lemma axis_sum_formula (m : ℤ) (n : ℕ) :
    6 * (∑ b ∈ range (n+1), (m-b)*(m-2*b)) =
      6*m^2*n+6*m^2-9*m*n^2-9*m*n+4*(n:ℤ)^3+6*n^2+2*n := by
  have he : (∑ b ∈ range (n+1), (m-b)*(m-2*b)) =
      ∑ b ∈ range (n+1), (2*(b:ℤ)^2+(-3*m)*b+m^2) := by
    apply sum_congr rfl
    intro b hb
    ring
  rw [he, simple_sum_quadratic]
  ring

private def qTerm (m : ℤ) (u v : ℕ) : ℤ := (m-2*u-v)*(m-u-2*v)

private def triangularSum (m : ℤ) (n : ℕ) : ℤ :=
  ∑ u ∈ range (n+1), ∑ v ∈ range (n-u+1), qTerm m u v

private lemma triangularSum_succ (m : ℤ) (n : ℕ) :
    triangularSum m (n+1) = triangularSum m n +
      ∑ u ∈ range (n+2), qTerm m u (n+1-u) := by
  have he : (∑ u ∈ range (n+1), ∑ v ∈ range (n+1-u+1), qTerm m u v) =
      (∑ u ∈ range (n+1), ∑ v ∈ range (n-u+1), qTerm m u v) +
      ∑ u ∈ range (n+1), qTerm m u (n+1-u) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro u hu
    have hu' := mem_range.mp hu
    have h1 : n+1-u+1 = (n-u+1)+1 := by omega
    have h2 : n-u+1 = n+1-u := by omega
    rw [h1, sum_range_succ, h2]
  unfold triangularSum
  rw [sum_range_succ (f := fun u => ∑ v ∈ range (n+1-u+1), qTerm m u v), he]
  rw [sum_range_succ (n := n+1) (f := fun u => qTerm m u (n+1-u))]
  simp
  ring

private lemma boundary_sum_formula (m : ℤ) (n : ℕ) :
    6 * (∑ u ∈ range (n+1), qTerm m u (n-u)) =
      -(n:ℤ)*(n+1)*(2*n+1)+3*n*n*(n+1)+
        6*(m^2-3*m*n+2*n^2)*(n+1) := by
  have he : (∑ u ∈ range (n+1), qTerm m u (n-u)) =
      ∑ u ∈ range (n+1), (-1*(u:ℤ)^2+(n:ℤ)*u+(m^2-3*m*n+2*n^2)) := by
    apply sum_congr rfl
    intro u hu
    have hu' : u ≤ n := by simpa only [mem_range, Nat.lt_succ_iff] using hu
    unfold qTerm
    rw [Nat.cast_sub hu']
    ring
  rw [he, simple_sum_quadratic]
  ring

private lemma triangular_sum_formula (m : ℤ) (n : ℕ) :
    24 * triangularSum m n =
      12*m^2*n^2+36*m^2*n+24*m^2-24*m*n^3-72*m*n^2-48*m*n+
        13*(n:ℤ)^4+42*n^3+35*n^2+6*n := by
  induction n with
  | zero => simp [triangularSum, qTerm] <;> ring
  | succ n ih =>
    rw [triangularSum_succ]
    have hb := boundary_sum_formula m (n+1)
    push_cast at hb ⊢
    linear_combination ih + 4*hb

lemma D_formula (n : ℕ) :
    24 * D n = 56*(n:ℤ)^3+132*n^2+100*n+24 := by
  have h := square_sum_formula (M n) n
  unfold D M at *
  linear_combination 4*h

lemma C_formula (n : ℕ) :
    24 * C n = 40*(n:ℤ)^3+108*n^2+92*n+24 := by
  have h := axis_sum_formula (M n) n
  unfold C M at *
  linear_combination 4*h

lemma Q_formula (n : ℕ) :
    24 * Q n = 13*(n:ℤ)^4+66*n^3+119*n^2+90*n+24 := by
  have h := triangular_sum_formula (M n) n
  unfold triangularSum qTerm M at h
  unfold Q M
  linear_combination h

end A201089Proof

-- Component: A201089Algebra

namespace A201089Proof
open Finset

lemma sum_quadratic (n : ℕ) (a b c : ℤ) :
    6 * (∑ i ∈ range (n+1), (a*(i:ℤ)^2+b*i+c)) =
      a*n*(n+1)*(2*n+1)+3*b*n*(n+1)+6*c*(n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    simp only [Nat.cast_succ]
    linear_combination ih

lemma sum_cubic (n : ℕ) (a b c d : ℤ) :
    12 * (∑ i ∈ range (n+1), (a*(i:ℤ)^3+b*i^2+c*i+d)) =
      3*a*n^2*(n+1)^2+2*b*n*(n+1)*(2*n+1)+6*c*n*(n+1)+12*d*(n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    simp only [Nat.cast_succ]
    linear_combination ih

def row (m : ℤ) (c : ℕ) : ℤ :=
  ∑ b ∈ range (c+1), (m-b-max 0 ((c:ℤ)-2*b))*(m-2*c+b)

lemma row_split (m : ℤ) (c k : ℕ) (h0 : 2*k ≤ c) (h1 : c ≤ 2*k+1) :
    row m c = (∑ b ∈ range (c+1), (m-b)*(m-2*c+b)) -
      ∑ b ∈ range (k+1), ((c:ℤ)-2*b)*(m-2*c+b) := by
  have hcut : (∑ b ∈ range (c+1), max 0 ((c:ℤ)-2*b)*(m-2*c+b)) =
      ∑ b ∈ range (k+1), ((c:ℤ)-2*b)*(m-2*c+b) := by
    calc
      _ = ∑ b ∈ range (k+1), max 0 ((c:ℤ)-2*b)*(m-2*c+b) := by
        symm
        apply sum_subset (range_mono (by omega))
        intro b hb hbk
        have hb' : k+1 ≤ b := by simpa only [mem_range, not_lt] using hbk
        have hc' : (c:ℤ) ≤ 2*k+1 := by exact_mod_cast h1
        have hb'' : (k:ℤ)+1 ≤ b := by exact_mod_cast hb'
        rw [max_eq_left (by omega)]
        ring
      _ = _ := by
        apply sum_congr rfl
        intro b hb
        have hb' : b ≤ k := by simpa only [mem_range, Nat.lt_succ_iff] using hb
        have hc' : (2:ℤ)*k ≤ c := by exact_mod_cast h0
        have hb'' : (b:ℤ) ≤ k := by exact_mod_cast hb'
        rw [max_eq_right (by omega)]
  unfold row
  calc
    _ = (∑ b ∈ range (c+1), (m-b)*(m-2*c+b)) -
        ∑ b ∈ range (c+1), max 0 ((c:ℤ)-2*b)*(m-2*c+b) := by
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro b hb
      ring
    _ = _ := by rw [hcut]

lemma row_formula (m : ℤ) (c k : ℕ) (h0 : 2*k ≤ c) (h1 : c ≤ 2*k+1) :
    6 * row m c =
      -(c:ℤ)*(c+1)*(2*c+1)+6*c*c*(c+1)+6*(m^2-2*m*c)*(c+1) -
      (-2*(k:ℤ)*(k+1)*(2*k+1)+3*(5*c-2*m)*k*(k+1)+6*(c*m-2*c^2)*(k+1)) := by
  rw [row_split m c k h0 h1, mul_sub]
  have hb := sum_quadratic c (-1) (2*c) (m^2-2*m*c)
  have hc := sum_quadratic k (-2) (5*c-2*m) (c*m-2*c^2)
  have e1 : (∑ b ∈ range (c+1), (m-b)*(m-2*c+b)) =
      ∑ b ∈ range (c+1), (-1*(b:ℤ)^2+(2*c)*b+(m^2-2*m*c)) := by
    apply sum_congr rfl
    intro b hb
    ring
  have e2 : (∑ b ∈ range (k+1), ((c:ℤ)-2*b)*(m-2*c+b)) =
      ∑ b ∈ range (k+1), (-2*(b:ℤ)^2+(5*c-2*m)*b+(c*m-2*c^2)) := by
    apply sum_congr rfl
    intro b hb
    ring
  rw [e1, e2, hb, hc]
  ring

lemma row_even (m : ℤ) (k : ℕ) :
    6*row m (2*k) = 54*(k:ℤ)^3-54*k^2*m+36*k^2+12*k*m^2-30*k*m+6*m^2 := by
  have h := row_formula m (2*k) k (by omega) (by omega)
  push_cast at h
  linear_combination h

lemma row_odd (m : ℤ) (k : ℕ) :
    6*row m (2*k+1) = 54*(k:ℤ)^3-54*k^2*m+117*k^2+12*k*m^2-84*k*m+
      81*k+12*m^2-30*m+18 := by
  have h := row_formula m (2*k+1) k (by omega) (by omega)
  push_cast at h
  linear_combination h

def triangle (m : ℤ) (n : ℕ) : ℤ := ∑ c ∈ range (n+1), row m c

lemma triangle_even (m : ℤ) (k : ℕ) :
    12*triangle m (2*k) = 54*(k:ℤ)^4-72*k^3*m+102*k^3+24*k^2*m^2-
      114*k^2*m+54*k^2+36*k*m^2-42*k*m+6*k+12*m^2 := by
  induction k with
  | zero => simp [triangle, row, pow_two]
  | succ k ih =>
    have h : triangle m (2*(k+1)) = triangle m (2*k)+row m (2*k+1)+row m (2*(k+1)) := by
      unfold triangle
      have e : 2*(k+1)+1 = (2*k+1)+1+1 := by omega
      rw [e, sum_range_succ, sum_range_succ]
      congr 1
    rw [h]
    have h1 := row_odd m k
    have h2 := row_even m (k+1)
    push_cast at h2 ⊢
    linear_combination ih + 2*h1 + 2*h2

lemma triangle_odd (m : ℤ) (k : ℕ) :
    12*triangle m (2*k+1) = 54*(k:ℤ)^4-72*k^3*m+210*k^3+24*k^2*m^2-
      222*k^2*m+288*k^2+60*k*m^2-210*k*m+168*k+36*m^2-60*m+36 := by
  have h : triangle m (2*k+1) = triangle m (2*k)+row m (2*k+1) := by
    unfold triangle
    rw [sum_range_succ]
  rw [h]
  linear_combination triangle_even m k + 2*row_odd m k

lemma P_even (k : ℕ) :
    24*P (2*k) = 300*(k:ℤ)^4+684*k^3+552*k^2+192*k+24 := by
  change 24*triangle (M (2*k)) (2*k) = _
  have h := triangle_even (M (2*k)) k
  unfold M at h ⊢
  push_cast at h ⊢
  linear_combination 2*h

lemma P_odd (k : ℕ) :
    24*P (2*k+1) = 300*(k:ℤ)^4+1284*k^3+2028*k^2+1404*k+360 := by
  change 24*triangle (M (2*k+1)) (2*k+1) = _
  have h := triangle_odd (M (2*k+1)) k
  unfold M at h ⊢
  push_cast at h ⊢
  linear_combination 2*h

end A201089Proof

-- Component: A201089Finish

namespace A201089Proof
open OMA.S_oeis_a201089

lemma count_even (k : ℕ) :
    24*countSum (2*k) = 101*(2*(k:ℤ))^4+202*(2*k)^3+190*(2*k)^2+92*(2*k)+24 := by
  rw [countSum_eq]
  have hp := P_even k
  have hd := D_formula (2*k)
  have hc := C_formula (2*k)
  have hq := Q_formula (2*k)
  unfold M
  push_cast at hd hc hq ⊢
  linear_combination 4*hp-2*hd+2*hq-4*hc

lemma count_odd (k : ℕ) :
    24*countSum (2*k+1) = 101*(2*(k:ℤ)+1)^4+202*(2*k+1)^3+190*(2*k+1)^2+86*(2*k+1)+21 := by
  rw [countSum_eq]
  have hp := P_odd k
  have hd := D_formula (2*k+1)
  have hc := C_formula (2*k+1)
  have hq := Q_formula (2*k+1)
  unfold M
  push_cast at hd hc hq ⊢
  linear_combination 4*hp-2*hd+2*hq-4*hc

lemma formula_even (k : ℕ) :
    (a (2*k):ℚ) = (101*(2*(k:ℚ))^4+202*(2*k)^3+190*(2*k)^2+92*(2*k)+24)/24 := by
  have hz : 24*(a (2*k):ℤ) =
      101*(2*(k:ℤ))^4+202*(2*k)^3+190*(2*k)^2+92*(2*k)+24 := by
    rw [a_eq_countSum]
    exact count_even k
  have hq : 24*(a (2*k):ℚ) =
      101*(2*(k:ℚ))^4+202*(2*k)^3+190*(2*k)^2+92*(2*k)+24 := by
    exact_mod_cast hz
  linear_combination hq/24

lemma formula_odd (k : ℕ) :
    (a (2*k+1):ℚ) = (101*(2*(k:ℚ)+1)^4+202*(2*k+1)^3+190*(2*k+1)^2+86*(2*k+1)+21)/24 := by
  have hz : 24*(a (2*k+1):ℤ) =
      101*(2*(k:ℤ)+1)^4+202*(2*k+1)^3+190*(2*k+1)^2+86*(2*k+1)+21 := by
    rw [a_eq_countSum]
    exact count_odd k
  have hq : 24*(a (2*k+1):ℚ) =
      101*(2*(k:ℚ)+1)^4+202*(2*k+1)^3+190*(2*k+1)^2+86*(2*k+1)+21 := by
    exact_mod_cast hz
  linear_combination hq/24

end A201089Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a201089.main := by
  intro n hn
  constructor
  · intro he
    obtain ⟨k, hk⟩ := he
    have e : n = 2*k := by omega
    rw [e]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using A201089Proof.formula_even k
  · intro ho
    obtain ⟨k, hk⟩ := ho
    have e : n = 2*k+1 := by omega
    rw [e]
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using A201089Proof.formula_odd k
