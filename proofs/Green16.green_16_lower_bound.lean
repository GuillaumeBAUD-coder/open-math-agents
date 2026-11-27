import FormalConjectures.GreensOpenProblems.«16»
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

open Finset Filter Asymptotics

namespace OMA

lemma parabola_eq : ∀ x y z w : ZMod 5,
    x + 3 * y = 2 * z + 2 * w →
    x ^ 2 + 3 * y ^ 2 = 2 * z ^ 2 + 2 * w ^ 2 →
    x = y ∧ y = z ∧ z = w := by
  decide

def M (d : ℕ) : ℕ := 1 + 4 * (5 ^ d - 1)

def y1 (d : ℕ) (t : Fin d → Fin 5) : ℕ :=
  ∑ j : Fin d, (t j).val * 5 ^ (j : ℕ)

def y2 (d : ℕ) (t : Fin d → Fin 5) : ℕ :=
  ∑ j : Fin d, ((t j).val ^ 2 % 5) * 5 ^ (j : ℕ)

def zcode (d : ℕ) (t : Fin d → Fin 5) : ℕ := 1 + y1 d t + M d * y2 d t

lemma geom4 (d : ℕ) : ∑ k ∈ range d, 4 * 5 ^ k = 5 ^ d - 1 := by
  rw [← Finset.mul_sum]
  have h := geom_sum_mul_add (4 : ℕ) d
  have hs : (∑ k ∈ range d, (4 + 1) ^ k) * 4 + 1 = (4 + 1) ^ d := h
  simp only [show (4 : ℕ) + 1 = 5 by decide] at hs
  have hp : 1 ≤ 5 ^ d := Nat.one_le_pow d 5 (by decide)
  omega

lemma sum_fin_range (d : ℕ) (f : ℕ → ℕ) :
    ∑ j : Fin d, f (j : ℕ) = ∑ k ∈ range d, f k :=
  Fin.sum_univ_eq_sum_range f d

lemma y1_le (d : ℕ) (t : Fin d → Fin 5) : y1 d t ≤ 5 ^ d - 1 := by
  unfold y1
  calc
    ∑ j : Fin d, (t j).val * 5 ^ (j : ℕ) ≤ ∑ j : Fin d, 4 * 5 ^ (j : ℕ) := by
      gcongr with j
      exact Nat.le_of_lt_succ (t j).isLt
    _ = ∑ k ∈ range d, 4 * 5 ^ k := sum_fin_range d (fun k => 4 * 5 ^ k)
    _ = 5 ^ d - 1 := geom4 d

lemma y2_le (d : ℕ) (t : Fin d → Fin 5) : y2 d t ≤ 5 ^ d - 1 := by
  unfold y2
  calc
    ∑ j : Fin d, ((t j).val ^ 2 % 5) * 5 ^ (j : ℕ)
        ≤ ∑ j : Fin d, 4 * 5 ^ (j : ℕ) := by
      gcongr with j
      exact Nat.le_of_lt_succ (Nat.mod_lt ((t j).val ^ 2) (by decide : 0 < 5))
    _ = 5 ^ d - 1 := by
      rw [sum_fin_range d (fun k => 4 * 5 ^ k)]
      exact geom4 d

lemma pow_le_M (d : ℕ) : 5 ^ d ≤ M d := by
  have h : 1 ≤ 5 ^ d := Nat.one_le_pow d 5 (by decide)
  have hsub : 4 * (5 ^ d - 1) = 4 * 5 ^ d - 4 := Nat.mul_sub_left_distrib 4 (5 ^ d) 1
  unfold M
  omega

lemma y1_lt_M (d : ℕ) (t : Fin d → Fin 5) : y1 d t < M d := by
  have h1 := y1_le d t
  have h2 := pow_le_M d
  have h3 : 1 ≤ 5 ^ d := Nat.one_le_pow d 5 (by decide)
  omega

lemma y2_lt_M (d : ℕ) (t : Fin d → Fin 5) : y2 d t < M d := by
  have h1 := y2_le d t
  have h2 := pow_le_M d
  have h3 : 1 ≤ 5 ^ d := Nat.one_le_pow d 5 (by decide)
  omega

lemma w1_lt (d : ℕ) (t u : Fin d → Fin 5) : y1 d t + 3 * y1 d u < M d := by
  have ht := y1_le d t
  have hu := y1_le d u
  unfold M
  omega

lemma w1_lt' (d : ℕ) (t u : Fin d → Fin 5) : 2 * y1 d t + 2 * y1 d u < M d := by
  have ht := y1_le d t
  have hu := y1_le d u
  unfold M
  omega

lemma w2_lt (d : ℕ) (t u : Fin d → Fin 5) : y2 d t + 3 * y2 d u < M d := by
  have ht := y2_le d t
  have hu := y2_le d u
  unfold M
  omega

lemma w2_lt' (d : ℕ) (t u : Fin d → Fin 5) : 2 * y2 d t + 2 * y2 d u < M d := by
  have ht := y2_le d t
  have hu := y2_le d u
  unfold M
  omega

lemma zcode_pos (d : ℕ) (t : Fin d → Fin 5) : 0 < zcode d t := by
  unfold zcode
  omega

lemma bound_poly (p : ℕ) (hp : 1 ≤ p) (h3 : 3 ≤ 4 * p) :
    p + (4 * p - 3) * (p - 1) ≤ (4 * p - 3) ^ 2 := by
  zify [hp, h3]
  nlinarith

lemma zcode_le_sq (d : ℕ) (t : Fin d → Fin 5) : zcode d t ≤ M d ^ 2 := by
  have h1 := y1_le d t
  have h2 := y2_le d t
  have hp : 1 ≤ 5 ^ d := Nat.one_le_pow d 5 (by decide)
  have h3 : 3 ≤ 4 * 5 ^ d := by omega
  have hM : M d = 4 * 5 ^ d - 3 := by
    unfold M
    have : 4 * (5 ^ d - 1) = 4 * 5 ^ d - 4 := Nat.mul_sub_left_distrib 4 (5 ^ d) 1
    omega
  have hz : zcode d t ≤ 5 ^ d + (4 * 5 ^ d - 3) * (5 ^ d - 1) := by
    unfold zcode
    rw [hM]
    have : 1 + y1 d t ≤ 5 ^ d := by omega
    calc
      1 + y1 d t + (4 * 5 ^ d - 3) * y2 d t
          ≤ 5 ^ d + (4 * 5 ^ d - 3) * y2 d t := by omega
      _ ≤ 5 ^ d + (4 * 5 ^ d - 3) * (5 ^ d - 1) := by gcongr
  have hb := bound_poly (5 ^ d) hp h3
  rw [hM]
  exact hz.trans hb

lemma split_base (d : ℕ) (t u v w : Fin d → Fin 5)
    (h : zcode d t + 3 * zcode d u = 2 * zcode d v + 2 * zcode d w) :
    y1 d t + 3 * y1 d u = 2 * y1 d v + 2 * y1 d w ∧
      y2 d t + 3 * y2 d u = 2 * y2 d v + 2 * y2 d w := by
  unfold zcode at h
  have hlin :
      y1 d t + 3 * y1 d u + M d * (y2 d t + 3 * y2 d u) =
        2 * y1 d v + 2 * y1 d w + M d * (2 * y2 d v + 2 * y2 d w) := by
    have hI : (zcode d t + 3 * zcode d u : ℤ) =
        (2 * zcode d v + 2 * zcode d w : ℤ) := by exact_mod_cast h
    simp only [zcode] at hI
    apply Nat.cast_injective (R := ℤ)
    push_cast at hI ⊢
    linarith
  have hA := w1_lt d t u
  have hC := w1_lt' d v w
  have hB := w2_lt d t u
  have hD := w2_lt' d v w
  have hm : 0 < M d := by unfold M; omega
  have h1 : y1 d t + 3 * y1 d u = 2 * y1 d v + 2 * y1 d w := by
    have hmod := congrArg (fun n => n % M d) hlin
    rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hA,
      Nat.mod_eq_of_lt hC] at hmod
    exact hmod
  refine ⟨h1, ?_⟩
  have : M d * (y2 d t + 3 * y2 d u) = M d * (2 * y2 d v + 2 * y2 d w) := by omega
  exact Nat.eq_of_mul_eq_mul_left hm this

def linDigit (a b c e : ℕ) : ℤ := (a : ℤ) + 3 * b - 2 * c - 2 * e

lemma cast_y1 (d : ℕ) (t : Fin d → Fin 5) :
    (y1 d t : ℤ) = ∑ j : Fin d, ((t j).val : ℤ) * (5 : ℤ) ^ (j : ℕ) := by
  unfold y1
  simp [Int.cast_sum, Int.cast_mul, Int.cast_pow]

lemma sum_lin_y1 (d : ℕ) (t u v w : Fin d → Fin 5) :
    (y1 d t : ℤ) + 3 * ↑(y1 d u) - 2 * ↑(y1 d v) - 2 * ↑(y1 d w) =
      ∑ j : Fin d, linDigit (t j).val (u j).val (v j).val (w j).val *
        (5 : ℤ) ^ (j : ℕ) := by
  rw [cast_y1 d t, cast_y1 d u, cast_y1 d v, cast_y1 d w, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _
  unfold linDigit
  push_cast
  ring

lemma cast_y2 (d : ℕ) (t : Fin d → Fin 5) :
    (y2 d t : ℤ) = ∑ j : Fin d, (((t j).val ^ 2 % 5 : ℕ) : ℤ) * (5 : ℤ) ^ (j : ℕ) := by
  unfold y2
  simp [Int.cast_sum, Int.cast_mul, Int.cast_pow]

lemma sum_lin_y2 (d : ℕ) (t u v w : Fin d → Fin 5) :
    (y2 d t : ℤ) + 3 * ↑(y2 d u) - 2 * ↑(y2 d v) - 2 * ↑(y2 d w) =
      ∑ j : Fin d, linDigit ((t j).val ^ 2 % 5) ((u j).val ^ 2 % 5)
        ((v j).val ^ 2 % 5) ((w j).val ^ 2 % 5) * (5 : ℤ) ^ (j : ℕ) := by
  rw [cast_y2 d t, cast_y2 d u, cast_y2 d v, cast_y2 d w, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _
  unfold linDigit
  push_cast
  ring

lemma five_dvd_coeff (d : ℕ) (δ : Fin d → ℤ) (ℓ : ℕ) (hℓ : ℓ < d)
    (h0 : ∀ j : Fin d, (j : ℕ) < ℓ → δ j = 0)
    (hsum : ∑ j : Fin d, δ j * (5 : ℤ) ^ (j : ℕ) = 0) :
    (5 : ℤ) ∣ δ ⟨ℓ, hℓ⟩ := by
  classical
  have htail : ∑ j : Fin d, δ j * (5 : ℤ) ^ (j : ℕ) =
      ∑ j ∈ univ.filter fun j : Fin d => ℓ ≤ (j : ℕ), δ j * (5 : ℤ) ^ (j : ℕ) := by
    have hlow : ∑ j ∈ univ.filter fun j : Fin d => (j : ℕ) < ℓ,
        δ j * (5 : ℤ) ^ (j : ℕ) = 0 := by
      refine sum_eq_zero ?_
      intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj
      simp [h0 j hj]
    have hsplit := sum_filter_add_sum_filter_not (s := univ)
      (p := fun j : Fin d => (j : ℕ) < ℓ)
      (f := fun j => δ j * (5 : ℤ) ^ (j : ℕ))
    have hnot : univ.filter (fun j : Fin d => ¬ (j : ℕ) < ℓ) =
        univ.filter (fun j : Fin d => ℓ ≤ (j : ℕ)) := by
      ext j; simp
    rw [← hsplit, hlow, zero_add, hnot]
  rw [htail] at hsum
  have hfac : ∑ j ∈ univ.filter fun j : Fin d => ℓ ≤ (j : ℕ),
      δ j * (5 : ℤ) ^ (j : ℕ) =
      (5 : ℤ) ^ ℓ * ∑ j ∈ univ.filter fun j : Fin d => ℓ ≤ (j : ℕ),
        δ j * (5 : ℤ) ^ ((j : ℕ) - ℓ) := by
    rw [mul_sum]
    refine sum_congr rfl ?_
    intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj
    have hpow : (5 : ℤ) ^ (j : ℕ) = (5 : ℤ) ^ ℓ * (5 : ℤ) ^ ((j : ℕ) - ℓ) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow]
    ring
  rw [hfac] at hsum
  have hquot : ∑ j ∈ univ.filter fun j : Fin d => ℓ ≤ (j : ℕ),
      δ j * (5 : ℤ) ^ ((j : ℕ) - ℓ) = 0 :=
    mul_eq_zero.mp hsum |>.resolve_left (by positivity)
  have hcut : δ ⟨ℓ, hℓ⟩ + ∑ j ∈ univ.filter fun j : Fin d => ℓ < (j : ℕ),
      δ j * (5 : ℤ) ^ ((j : ℕ) - ℓ) = 0 := by
    have hjoin := sum_filter_add_sum_filter_not
      (s := univ.filter fun j : Fin d => ℓ ≤ (j : ℕ))
      (p := fun j : Fin d => (j : ℕ) = ℓ)
      (f := fun j => δ j * (5 : ℤ) ^ ((j : ℕ) - ℓ))
    have heq : ∑ j ∈ (univ.filter fun j : Fin d => ℓ ≤ (j : ℕ)).filter
        (fun j : Fin d => (j : ℕ) = ℓ), δ j * (5 : ℤ) ^ ((j : ℕ) - ℓ) =
        δ ⟨ℓ, hℓ⟩ := by
      rw [sum_eq_single ⟨ℓ, hℓ⟩]
      · simp
      · intro j hj hne
        simp only [mem_filter, mem_univ, true_and] at hj
        exact absurd (Fin.ext hj.2) hne
      · intro hnot
        simp [mem_filter] at hnot
    have hrest : (univ.filter fun j : Fin d => ℓ ≤ (j : ℕ)).filter
        (fun j : Fin d => ¬ (j : ℕ) = ℓ) =
        univ.filter fun j : Fin d => ℓ < (j : ℕ) := by
      ext j
      simp
      omega
    rw [← hjoin, heq, hrest] at hquot
    exact hquot
  have hmul : (5 : ℤ) ∣ ∑ j ∈ univ.filter fun j : Fin d => ℓ < (j : ℕ),
      δ j * (5 : ℤ) ^ ((j : ℕ) - ℓ) := by
    refine dvd_sum ?_
    intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj
    have hge : 1 ≤ (j : ℕ) - ℓ := by omega
    refine dvd_mul_of_dvd_right ?_ _
    have : (5 : ℤ) ^ ((j : ℕ) - ℓ) = 5 * (5 : ℤ) ^ ((j : ℕ) - ℓ - 1) := by
      have hpos : (j : ℕ) - ℓ ≠ 0 := by omega
      calc
        (5 : ℤ) ^ ((j : ℕ) - ℓ) = (5 : ℤ) ^ (1 + ((j : ℕ) - ℓ - 1)) := by congr 1; omega
        _ = 5 * (5 : ℤ) ^ ((j : ℕ) - ℓ - 1) := by rw [pow_add, pow_one]
    rw [this]
    exact dvd_mul_right _ _
  have : (5 : ℤ) ∣ δ ⟨ℓ, hℓ⟩ + ∑ j ∈ univ.filter fun j : Fin d => ℓ < (j : ℕ),
      δ j * (5 : ℤ) ^ ((j : ℕ) - ℓ) := by simp [hcut]
  exact (Int.dvd_add_left hmul).mp this

lemma y1_as_range (d : ℕ) (t : Fin d → Fin 5) :
    y1 d t = ∑ k ∈ range d, if h : k < d then (t ⟨k, h⟩).val * 5 ^ k else 0 := by
  unfold y1
  rw [← Fin.sum_univ_eq_sum_range (fun k => if h : k < d then (t ⟨k, h⟩).val * 5 ^ k else 0)]
  refine Finset.sum_congr rfl ?_
  intro j _
  simp [j.isLt]

lemma y1_digit (d : ℕ) (t : Fin d → Fin 5) (j : Fin d) :
    y1 d t / 5 ^ (j : ℕ) % 5 = (t j).val := by
  let ℓ := (j : ℕ)
  have hℓ : ℓ < d := j.isLt
  have hle : ℓ ≤ d := le_of_lt hℓ
  have hy := y1_as_range d t
  have hsplitRange : ∑ k ∈ range d, (if h : k < d then (t ⟨k, h⟩).val * 5 ^ k else 0) =
      ∑ k ∈ range ℓ, (if h : k < d then (t ⟨k, h⟩).val * 5 ^ k else 0) +
        ∑ k ∈ Ico ℓ d, (if h : k < d then (t ⟨k, h⟩).val * 5 ^ k else 0) := by
    simpa using (Finset.sum_range_add_sum_Ico
      (fun k => if h : k < d then (t ⟨k, h⟩).val * 5 ^ k else 0) hle).symm
  rw [hy, hsplitRange]
  have hlow : ∑ k ∈ range ℓ, (if h : k < d then (t ⟨k, h⟩).val * 5 ^ k else 0) ≤ 5 ^ ℓ - 1 := by
    calc
      _ ≤ ∑ k ∈ range ℓ, 4 * 5 ^ k := by
        gcongr with k hk
        simp only [Finset.mem_range] at hk
        have hk' : k < d := lt_trans hk hℓ
        simp [hk']
        exact Nat.le_of_lt_succ (t ⟨k, hk'⟩).isLt
      _ = 5 ^ ℓ - 1 := geom4 ℓ
  set low := ∑ k ∈ range ℓ, (if h : k < d then (t ⟨k, h⟩).val * 5 ^ k else 0)
  set high := ∑ k ∈ Ico ℓ d, (if h : k < d then (t ⟨k, h⟩).val * 5 ^ k else 0)
  have hlowlt : low < 5 ^ ℓ := by
    have hone : 1 ≤ 5 ^ ℓ := Nat.one_le_pow ℓ 5 (by decide)
    omega
  have hhigh : high = 5 ^ ℓ * ∑ k ∈ Ico ℓ d,
      (if h : k < d then (t ⟨k, h⟩).val * 5 ^ (k - ℓ) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp only [Finset.mem_Ico] at hk
    have hk' : k < d := hk.2
    simp only [hk', dite_true]
    have hpow : 5 ^ k = 5 ^ ℓ * 5 ^ (k - ℓ) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [hpow]
    ring
  set rest := ∑ k ∈ Ico ℓ d, (if h : k < d then (t ⟨k, h⟩).val * 5 ^ (k - ℓ) else 0)
  have hdiv : y1 d t / 5 ^ ℓ = rest := by
    rw [hy, hsplitRange, hhigh]
    have hc : 0 < 5 ^ ℓ := Nat.pow_pos (by decide)
    rw [Nat.add_mul_div_left _ _ hc, Nat.div_eq_of_lt hlowlt, zero_add]
  have hmem : ℓ ∈ Ico ℓ d := by simp [hℓ]
  have hrest : rest % 5 = (t j).val := by
    have hsum := (Finset.add_sum_erase (s := Ico ℓ d)
      (f := fun k => if h : k < d then (t ⟨k, h⟩).val * 5 ^ (k - ℓ) else 0) hmem).symm
    unfold rest
    rw [hsum]
    have hhead : (if h : ℓ < d then (t ⟨ℓ, h⟩).val * 5 ^ (ℓ - ℓ) else 0) = (t j).val := by
      have hj : (⟨ℓ, hℓ⟩ : Fin d) = j := Fin.ext rfl
      simp [hℓ, Nat.sub_self, pow_zero, hj]
    have htail : (∑ k ∈ (Ico ℓ d).erase ℓ,
        (if h : k < d then (t ⟨k, h⟩).val * 5 ^ (k - ℓ) else 0)) % 5 = 0 := by
      refine Nat.mod_eq_zero_of_dvd ?_
      refine Finset.dvd_sum ?_
      intro k hk
      simp only [Finset.mem_erase, Finset.mem_Ico] at hk
      have hk' : k < d := hk.2.2
      simp only [hk', dite_true]
      have hge : k - ℓ ≠ 0 := by omega
      exact dvd_mul_of_dvd_right (dvd_pow_self 5 hge) _
    rw [hhead, Nat.add_mod, htail, add_zero, Nat.mod_mod]
    exact Nat.mod_eq_of_lt (t j).isLt
  have hyeq : y1 d t = low + high := by rw [hy, hsplitRange]
  rw [← hyeq, hdiv]
  exact hrest

lemma zcode_inj (d : ℕ) : Function.Injective (zcode d) := by
  intro t u hzu
  have ht := y1_lt_M d t
  have hu := y1_lt_M d u
  have ht1 : zcode d t - 1 = y1 d t + M d * y2 d t := by unfold zcode; omega
  have hu1 : zcode d u - 1 = y1 d u + M d * y2 d u := by unfold zcode; omega
  have hmodt : (zcode d t - 1) % M d = y1 d t := by
    rw [ht1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
  have hmodu : (zcode d u - 1) % M d = y1 d u := by
    rw [hu1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu]
  have hy1 : y1 d t = y1 d u := by
    have : zcode d t - 1 = zcode d u - 1 := by omega
    rw [← hmodt, ← hmodu, this]
  ext j
  have htj := y1_digit d t j
  have huj := y1_digit d u j
  rw [hy1] at htj
  exact htj.symm.trans huj

def Aset (d : ℕ) : Finset ℕ := (univ : Finset (Fin d → Fin 5)).image (zcode d)

lemma Aset_card (d : ℕ) : (Aset d).card = 5 ^ d := by
  rw [Aset, card_image_of_injective _ (zcode_inj d), card_univ, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin]

lemma Aset_subset (d : ℕ) : Aset d ⊆ Icc 1 (M d ^ 2) := by
  intro n hn
  obtain ⟨t, _, rfl⟩ := mem_image.mp hn
  refine mem_Icc.mpr ⟨zcode_pos d t, zcode_le_sq d t⟩

lemma sqCast (a : Fin 5) : ((a.val ^ 2 % 5 : ℕ) : ZMod 5) = (a.val : ZMod 5) ^ 2 := by
  rw [ZMod.natCast_mod (a.val ^ 2) 5]
  exact Nat.cast_pow a.val 2

lemma Aset_free (d : ℕ) : Green16.SolutionFree (Aset d) := by
  intro x hx y hy z hz w hw hnd heq
  obtain ⟨tx, -, rfl⟩ := mem_image.mp hx
  obtain ⟨ty, -, rfl⟩ := mem_image.mp hy
  obtain ⟨tz, -, rfl⟩ := mem_image.mp hz
  obtain ⟨tw, -, rfl⟩ := mem_image.mp hw
  have hsplit := split_base d tx ty tz tw heq
  have hsum1 : ∑ j : Fin d, linDigit (tx j).val (ty j).val (tz j).val (tw j).val *
      (5 : ℤ) ^ (j : ℕ) = 0 := by
    rw [← sum_lin_y1]
    have := hsplit.1
    exact_mod_cast (by omega :
      (y1 d tx : ℤ) + 3 * y1 d ty - 2 * y1 d tz - 2 * y1 d tw = 0)
  have hsum2 : ∑ j : Fin d, linDigit ((tx j).val ^ 2 % 5) ((ty j).val ^ 2 % 5)
      ((tz j).val ^ 2 % 5) ((tw j).val ^ 2 % 5) * (5 : ℤ) ^ (j : ℕ) = 0 := by
    rw [← sum_lin_y2]
    have := hsplit.2
    exact_mod_cast (by omega :
      (y2 d tx : ℤ) + 3 * y2 d ty - 2 * y2 d tz - 2 * y2 d tw = 0)
  have hdistinct : tx ≠ ty ∨ tx ≠ tz ∨ tx ≠ tw ∨ ty ≠ tz ∨ ty ≠ tw ∨ tz ≠ tw := by
    by_contra h
    push Not at h
    have hxy : zcode d tx = zcode d ty := by rw [h.1]
    simp [List.nodup_cons] at hnd
    exact hnd.left.left hxy
  -- the four values are pairwise distinct, so the codes are not all identical
  have hsome : ∃ n, ∃ j : Fin d, (j : ℕ) = n ∧
      ¬ (tx j = ty j ∧ ty j = tz j ∧ tz j = tw j) := by
    by_contra h
    push Not at h
    have hxy : tx = ty := by
      ext j
      exact congrArg Fin.val ((h (j : ℕ) j rfl).1)
    have : zcode d tx = zcode d ty := congrArg (zcode d) hxy
    simp [List.nodup_cons] at hnd
    exact hnd.left.left this
  let ℓ := Nat.find hsome
  obtain ⟨j0, hj0, hne⟩ := Nat.find_spec hsome
  have hℓ : ℓ < d := by omega
  have hbefore : ∀ i : Fin d, (i : ℕ) < ℓ →
      tx i = ty i ∧ ty i = tz i ∧ tz i = tw i := by
    intro i hi
    by_contra hbad
    exact Nat.find_min hsome hi ⟨i, rfl, hbad⟩
  let δ : Fin d → ℤ := fun i =>
    linDigit (tx i).val (ty i).val (tz i).val (tw i).val
  have hδ0 : ∀ i : Fin d, (i : ℕ) < ℓ → δ i = 0 := by
    intro i hi
    obtain ⟨h1, h2, h3⟩ := hbefore i hi
    simp only [δ, linDigit, h1, h2, h3]
    ring
  have hdvd := five_dvd_coeff d δ ℓ hℓ hδ0 (by simpa [δ] using hsum1)
  let δ2 : Fin d → ℤ := fun i =>
    linDigit ((tx i).val ^ 2 % 5) ((ty i).val ^ 2 % 5)
      ((tz i).val ^ 2 % 5) ((tw i).val ^ 2 % 5)
  have hδ20 : ∀ i : Fin d, (i : ℕ) < ℓ → δ2 i = 0 := by
    intro i hi
    obtain ⟨h1, h2, h3⟩ := hbefore i hi
    simp only [δ2, linDigit, h1, h2, h3]
    ring
  have hdvd2 := five_dvd_coeff d δ2 ℓ hℓ hδ20 (by simpa [δ2] using hsum2)
  have hidx : (⟨ℓ, hℓ⟩ : Fin d) = j0 := Fin.ext hj0.symm
  have hZ : ((tx ⟨ℓ, hℓ⟩).val : ZMod 5) + 3 * ((ty ⟨ℓ, hℓ⟩).val : ZMod 5) =
      2 * ((tz ⟨ℓ, hℓ⟩).val : ZMod 5) + 2 * ((tw ⟨ℓ, hℓ⟩).val : ZMod 5) := by
    have h0 : ((linDigit (tx ⟨ℓ, hℓ⟩).val (ty ⟨ℓ, hℓ⟩).val (tz ⟨ℓ, hℓ⟩).val
        (tw ⟨ℓ, hℓ⟩).val : ℤ) : ZMod 5) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).2 (by simpa [δ, hidx] using hdvd)
    simp only [linDigit, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
      Int.cast_ofNat] at h0
    linear_combination h0
  have hZ2 : ((tx ⟨ℓ, hℓ⟩).val : ZMod 5) ^ 2 + 3 * ((ty ⟨ℓ, hℓ⟩).val : ZMod 5) ^ 2 =
      2 * ((tz ⟨ℓ, hℓ⟩).val : ZMod 5) ^ 2 + 2 * ((tw ⟨ℓ, hℓ⟩).val : ZMod 5) ^ 2 := by
    have h0 : ((linDigit ((tx ⟨ℓ, hℓ⟩).val ^ 2 % 5) ((ty ⟨ℓ, hℓ⟩).val ^ 2 % 5)
        ((tz ⟨ℓ, hℓ⟩).val ^ 2 % 5) ((tw ⟨ℓ, hℓ⟩).val ^ 2 % 5) : ℤ) : ZMod 5) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).2 (by simpa [δ2, hidx] using hdvd2)
    simp only [linDigit, sqCast, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
      Int.cast_ofNat] at h0
    linear_combination h0
  have heqZ := parabola_eq ((tx ⟨ℓ, hℓ⟩).val : ZMod 5) ((ty ⟨ℓ, hℓ⟩).val)
    ((tz ⟨ℓ, hℓ⟩).val) ((tw ⟨ℓ, hℓ⟩).val) hZ hZ2
  have hfin : tx ⟨ℓ, hℓ⟩ = ty ⟨ℓ, hℓ⟩ ∧ ty ⟨ℓ, hℓ⟩ = tz ⟨ℓ, hℓ⟩ ∧
      tz ⟨ℓ, hℓ⟩ = tw ⟨ℓ, hℓ⟩ := by
    refine ⟨Fin.ext ?_, Fin.ext ?_, Fin.ext ?_⟩
    · have h := heqZ.1
      rw [ZMod.natCast_eq_natCast_iff] at h
      exact Nat.ModEq.eq_of_lt_of_lt h (tx ⟨ℓ, hℓ⟩).isLt (ty ⟨ℓ, hℓ⟩).isLt
    · have h := heqZ.2.1
      rw [ZMod.natCast_eq_natCast_iff] at h
      exact Nat.ModEq.eq_of_lt_of_lt h (ty ⟨ℓ, hℓ⟩).isLt (tz ⟨ℓ, hℓ⟩).isLt
    · have h := heqZ.2.2
      rw [ZMod.natCast_eq_natCast_iff] at h
      exact Nat.ModEq.eq_of_lt_of_lt h (tz ⟨ℓ, hℓ⟩).isLt (tw ⟨ℓ, hℓ⟩).isLt
  exact hne (by simpa [hidx] using hfin)

lemma card_le_f {N : ℕ} (A : Finset ℕ) (hA : A ⊆ Icc 1 N) (hf : Green16.SolutionFree A) :
    A.card ≤ Green16.f N := by
  have hbdd : BddAbove {k | ∃ B : Finset ℕ, B ⊆ Icc 1 N ∧ Green16.SolutionFree B ∧ B.card = k} := by
    refine ⟨N, ?_⟩
    rintro k ⟨B, hB, -, rfl⟩
    exact (card_le_card hB).trans (by rw [Nat.card_Icc]; omega)
  exact le_csSup hbdd ⟨A, hA, hf, rfl⟩

end OMA

theorem OMA.solution : type_of% @Green16.green_16_lower_bound := by
  show (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 2)) =O[atTop] fun N => (Green16.f N : ℝ)
  refine IsBigO.of_bound 20 ?_
  filter_upwards [eventually_ge_atTop (OMA.M 1 ^ 2)] with N hN
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have hsq : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by positivity
  have hf : (0 : ℝ) ≤ (Green16.f N : ℝ) := by positivity
  rw [abs_of_nonneg hsq, abs_of_nonneg hf]
  have hex : ∃ k, N < OMA.M k ^ 2 := by
    refine ⟨N + 1, ?_⟩
    have hlt : N < 5 ^ (N + 1) := by
      have hpow : N + 1 < 5 ^ (N + 1) := Nat.lt_pow_self (by decide : 1 < 5)
      omega
    have hM : 5 ^ (N + 1) ≤ OMA.M (N + 1) := OMA.pow_le_M _
    have : N < OMA.M (N + 1) := lt_of_lt_of_le hlt hM
    have hpos : 1 ≤ OMA.M (N + 1) := by
      have := OMA.pow_le_M (N + 1)
      omega
    nlinarith
  have hk0 : Nat.find hex ≠ 0 := by
    intro hk
    have hspec0 := Nat.find_spec hex
    rw [hk] at hspec0
    have hM0 : OMA.M 0 = 1 := by decide
    rw [hM0] at hspec0
    have hone : (1 : ℕ) ^ 2 = 1 := by decide
    rw [hone] at hspec0
    have h1N : (1 : ℕ) ≤ N := by
      have honeM : (1 : ℕ) ≤ OMA.M 1 ^ 2 := by decide
      exact le_trans honeM hN
    exact (Nat.not_lt.mpr h1N) hspec0
  let k := Nat.find hex
  have hk0' : k ≠ 0 := hk0
  let d := k - 1
  have hk : k = d + 1 := by omega
  have hle : OMA.M d ^ 2 ≤ N := by
    have hmin := Nat.find_min hex (show d < k by omega)
    exact not_lt.mp hmin
  have hltN : N < OMA.M (d + 1) ^ 2 := by
    have hspec' : N < OMA.M (Nat.find hex) ^ 2 := Nat.find_spec hex
    rwa [show Nat.find hex = d + 1 from hk] at hspec'
  have hsubset : OMA.Aset d ⊆ Icc 1 N := by
    intro n hn
    have hmem := OMA.Aset_subset d hn
    exact mem_Icc.mpr ⟨(mem_Icc.mp hmem).1, (mem_Icc.mp hmem).2.trans hle⟩
  have hcard : (OMA.Aset d).card ≤ Green16.f N :=
    OMA.card_le_f (OMA.Aset d) hsubset (OMA.Aset_free d)
  have hsize : 5 ^ d ≤ Green16.f N := by
    rw [← OMA.Aset_card d]
    exact hcard
  have hsqrt : (N : ℝ) ^ ((1 : ℝ) / 2) < (OMA.M (d + 1) : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq (show (0 : ℝ) ≤ OMA.M (d + 1) by positivity)]
    exact Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast hltN)
  have hMle : (OMA.M (d + 1) : ℝ) ≤ 20 * (5 : ℝ) ^ d := by
    have hform : OMA.M (d + 1) = 4 * 5 ^ (d + 1) - 3 := by
      have hp : 1 ≤ 5 ^ (d + 1) := Nat.one_le_pow _ 5 (by decide)
      unfold OMA.M
      have : 4 * (5 ^ (d + 1) - 1) = 4 * 5 ^ (d + 1) - 4 :=
        Nat.mul_sub_left_distrib 4 _ 1
      omega
    have hleN : OMA.M (d + 1) ≤ 4 * 5 ^ (d + 1) := by omega
    have hpow : 4 * 5 ^ (d + 1) = 20 * 5 ^ d := by
      rw [pow_succ, Nat.mul_comm (5 ^ d) 5]
      ring
    calc
      (OMA.M (d + 1) : ℝ) ≤ (4 * 5 ^ (d + 1) : ℝ) := by exact_mod_cast hleN
      _ = 20 * (5 : ℝ) ^ d := by exact_mod_cast hpow
  have hfive : (20 : ℝ) * (5 : ℝ) ^ d ≤ 20 * (Green16.f N : ℝ) := by
    gcongr
    exact_mod_cast hsize
  linarith
