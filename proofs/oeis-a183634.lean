import OMAStatements.S_oeis_a183634
import Mathlib

namespace OMA.S_oeis_a183634

open Classical

def rsum (r : Fin 2 → Fin 4) : ℕ := (r 0 : ℕ) + r 1

def Valid (n : ℕ) (x : Fin (n + 1) → Fin 2 → Fin 4) : Prop :=
  ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ)

def T (s : ℕ) (j : ℕ) : ℕ := if j % 2 = 0 then s else 6 - s

lemma rsum_le (r : Fin 2 → Fin 4) : rsum r ≤ 6 := by
  unfold rsum
  have h0 := (r 0).isLt
  have h1 := (r 1).isLt
  omega

lemma valid_iff (n : ℕ) (x : Fin (n + 1) → Fin 2 → Fin 4) :
    Valid n x ↔ ∀ j : Fin (n + 1), rsum (x j) = T (rsum (x 0)) j := by
  constructor
  · intro h
    have key : ∀ j : ℕ, (hj : j < n + 1) → rsum (x ⟨j, hj⟩) = T (rsum (x 0)) j := by
      intro j
      induction j with
      | zero => intro hj; simp [T]
      | succ k ih =>
        intro hj
        have hk : k < n := by omega
        have ih' := ih (by omega)
        have hb := h ⟨k, hk⟩
        unfold BlockOK at hb
        have e1 : rsum (x ⟨k, by omega⟩) + rsum (x ⟨k + 1, hj⟩) = 6 := by
          unfold rsum; simp at hb ⊢; omega
        have := rsum_le (x 0)
        unfold T at ih' ⊢
        split_ifs at ih' ⊢ <;> omega
    intro j
    exact key j.val j.isLt
  · intro h i
    have h1 := h i.castSucc
    have h2 := h i.succ
    have h0 := rsum_le (x 0)
    unfold T at h1 h2
    unfold BlockOK
    have : rsum (x i.castSucc) + rsum (x i.succ) = 6 := by
      simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
      split_ifs at h1 h2 <;> omega
    unfold rsum at this; omega

def cnt (t : ℕ) : ℕ := Fintype.card {r : Fin 2 → Fin 4 // rsum r = t}

lemma cnt_symm : ∀ s : Fin 7, cnt (6 - s.val) = cnt s.val := by
  unfold cnt rsum; decide

lemma cnt_vals : cnt 0 = 1 ∧ cnt 1 = 2 ∧ cnt 2 = 3 ∧ cnt 3 = 4 ∧ cnt 4 = 3 ∧ cnt 5 = 2 ∧ cnt 6 = 1 := by
  unfold cnt rsum; decide

lemma fiber_card (n s : ℕ) :
    Fintype.card {x : {x : Fin (n + 1) → Fin 2 → Fin 4 // Valid n x} // rsum (x.1 0) = s} =
      ∏ j : Fin (n + 1), cnt (T s j) := by
  have : Fintype.card {x : {x : Fin (n + 1) → Fin 2 → Fin 4 // Valid n x} // rsum (x.1 0) = s} =
      Fintype.card (∀ j : Fin (n + 1), {r : Fin 2 → Fin 4 // rsum r = T s j}) := by
    apply Fintype.card_congr
    refine
      { toFun := fun x j => ⟨x.1.1 j, ?_⟩
        invFun := fun f => ⟨⟨fun j => (f j).1, ?_⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have := (valid_iff n x.1.1).1 x.1.2 j
      rw [this, x.2]
    · rw [valid_iff]
      intro j
      have h0 : rsum (f 0).1 = T s 0 := (f 0).2
      have hj : rsum (f j).1 = T s j := (f j).2
      show rsum (f j).1 = T (rsum (f 0).1) j
      rw [hj, h0]
      simp [T]
    · have h0 : rsum (f 0).1 = T s 0 := (f 0).2
      simpa [T] using h0
    · intro x; rfl
    · intro f; rfl
  rw [this, Fintype.card_pi]
  rfl

lemma a_eq (n : ℕ) : a n = ∑ s ∈ Finset.range 7, cnt s ^ (n + 1) := by
  unfold a
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype]
  have hv : ∀ x : Fin (n + 1) → Fin 2 → Fin 4,
      (∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ)) ↔ Valid n x := fun _ => Iff.rfl
  have e : (Finset.univ.filter fun x : Fin (n + 1) → Fin 2 → Fin 4 =>
      ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ)) =
      Finset.univ.filter fun x => Valid n x := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rfl
  rw [e]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => rsum (x 0)) (t := Finset.range 7)]
  · apply Finset.sum_congr rfl
    intro s hs
    have : (Finset.filter (fun x => rsum (x 0) = s) (Finset.filter (fun x => Valid n x) Finset.univ)).card
        = Fintype.card {x : {x : Fin (n + 1) → Fin 2 → Fin 4 // Valid n x} // rsum (x.1 0) = s} := by
      symm
      rw [Fintype.card_subtype]
      rw [← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩]
      congr 1
      ext x
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨⟨y, hy⟩, hs', rfl⟩
        exact ⟨hy, hs'⟩
      · rintro ⟨hy, hs'⟩
        exact ⟨⟨x, hy⟩, hs', rfl⟩
    rw [this, fiber_card]
    have hs7 : s < 7 := Finset.mem_range.1 hs
    have : ∀ j : Fin (n + 1), cnt (T s j) = cnt s := by
      intro j
      unfold T
      split_ifs
      · rfl
      · exact cnt_symm ⟨s, hs7⟩
    simp [this]
  · intro x _
    have := rsum_le (x 0)
    show rsum (x 0) ∈ Finset.range 7
    rw [Finset.mem_range]; omega

lemma closed (n : ℕ) : a n = 2 + 2 ^ (2 + n) + 2 * 3 ^ (1 + n) + 4 ^ (1 + n) := by
  rw [a_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cnt_vals.1, cnt_vals.2.1,
    cnt_vals.2.2.1, cnt_vals.2.2.2.1, cnt_vals.2.2.2.2.1, cnt_vals.2.2.2.2.2.1,
    cnt_vals.2.2.2.2.2.2]
  ring

lemma closedQ (n : ℕ) : (a n : ℚ) = 2 + 2 ^ (2 + n) + 2 * 3 ^ (1 + n) + 4 ^ (1 + n) := by
  rw [closed]; push_cast; ring

open PowerSeries in
theorem sol : type_of% @OMA.S_oeis_a183634.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have e1 : m + 5 - 1 = m + 4 := by omega
    have e2 : m + 5 - 2 = m + 3 := by omega
    have e3 : m + 5 - 3 = m + 2 := by omega
    have e4 : m + 5 - 4 = m + 1 := by omega
    rw [e1, e2, e3, e4]
    simp only [closed]
    push_cast
    ring
  · set b : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hb
    have hD : constantCoeff ((1 - X) * (1 - 2 * X) * (1 - 3 * X) * (1 - 4 * X) : PowerSeries ℚ) ≠ 0 := by
      simp
    unfold G
    rw [eq_mul_inv_iff_mul_eq hD]
    have hX : ∀ (k : ℕ) (n : ℕ), coeff n ((X : PowerSeries ℚ) ^ k * mk b) = if k ≤ n then b (n - k) else 0 := by
      intro k n; rw [coeff_X_pow_mul']; simp
    have e : mk b * ((1 - X) * (1 - 2 * X) * (1 - 3 * X) * (1 - 4 * X) : PowerSeries ℚ) =
        mk b - C (10:ℚ) * (X ^ 1 * mk b) + C (35:ℚ) * (X ^ 2 * mk b) - C (50:ℚ) * (X ^ 3 * mk b)
          + C (24:ℚ) * (X ^ 4 * mk b) := by
      have h10 : (C (10:ℚ) : PowerSeries ℚ) = 10 := map_ofNat C 10
      have h35 : (C (35:ℚ) : PowerSeries ℚ) = 35 := map_ofNat C 35
      have h50 : (C (50:ℚ) : PowerSeries ℚ) = 50 := map_ofNat C 50
      have h24 : (C (24:ℚ) : PowerSeries ℚ) = 24 := map_ofNat C 24
      rw [h10, h35, h50, h24]; ring
    have eN : (4 * X * (11 - 76 * X + 158 * X ^ 2 - 96 * X ^ 3) : PowerSeries ℚ) =
        C (44:ℚ) * X ^ 1 - C (304:ℚ) * X ^ 2 + C (632:ℚ) * X ^ 3 - C (384:ℚ) * X ^ 4 := by
      have h1 : (C (44:ℚ) : PowerSeries ℚ) = 44 := map_ofNat C 44
      have h2 : (C (304:ℚ) : PowerSeries ℚ) = 304 := map_ofNat C 304
      have h3 : (C (632:ℚ) : PowerSeries ℚ) = 632 := map_ofNat C 632
      have h4 : (C (384:ℚ) : PowerSeries ℚ) = 384 := map_ofNat C 384
      rw [h1, h2, h3, h4]; ring
    rw [e, eN]
    ext n
    simp only [map_sub, map_add, coeff_C_mul, hX, coeff_X_pow]
    rcases n with _ | _ | _ | _ | _ | m
    · simp [hb]
    · simp [hb, closedQ]; norm_num
    · simp [hb, closedQ]; norm_num
    · simp [hb, closedQ]; norm_num
    · simp [hb, closedQ]; norm_num
    · simp [hb, closedQ]
      ring
  · intro n hn
    exact closed n

end OMA.S_oeis_a183634

theorem OMA.solution : type_of% @OMA.S_oeis_a183634.main := OMA.S_oeis_a183634.sol
