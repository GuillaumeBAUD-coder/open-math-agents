import OMAStatements.S_oeis_a183624
import Mathlib

namespace OMA.A183624Proof

open OMA.S_oeis_a183624
open PowerSeries

/-- Sum of a row. -/
def rs (r : Fin 2 → Fin 3) : ℕ := (r 0).val + (r 1).val

/-- Rows with a given sum. -/
def T (t : ℕ) : Finset (Fin 2 → Fin 3) := Finset.univ.filter (fun r => rs r = t)

/-- Row sums alternate between s and 4 - s. -/
def alt (s i : ℕ) : ℕ := if i % 2 = 0 then s else 4 - s

theorem key (n : ℕ) (g : Grid n) :
    IsValid g ↔ ∃ s, s < 5 ∧ ∀ i : Fin (n + 1), rs (g i) = alt s i.val := by
  constructor
  · intro hv
    refine ⟨rs (g 0), ?_, ?_⟩
    · unfold rs
      have h0 := (g 0 0).isLt
      have h1 := (g 0 1).isLt
      omega
    · have hk : ∀ k (hk : k < n + 1), rs (g ⟨k, hk⟩) = alt (rs (g 0)) k := by
        intro k
        induction k with
        | zero => intro hk; simp [alt]
        | succ k ih =>
          intro hk
          have h := hv ⟨k, by omega⟩
          have e1 : (Fin.castSucc (⟨k, by omega⟩ : Fin n)) = (⟨k, by omega⟩ : Fin (n + 1)) := rfl
          have e2 : (Fin.succ (⟨k, by omega⟩ : Fin n)) = (⟨k + 1, hk⟩ : Fin (n + 1)) := rfl
          rw [e1, e2] at h
          have ih' := ih (by omega)
          have hs : rs (g 0) ≤ 4 := by
            unfold rs
            have h0 := (g 0 0).isLt
            have h1 := (g 0 1).isLt
            omega
          unfold rs at ih' ⊢ hs
          unfold alt at ih' ⊢
          split_ifs at ih' ⊢ with p1 p2 p2 <;> omega
      intro i
      exact hk i.val i.isLt
  · rintro ⟨s, hs, H⟩ i
    have h1 := H i.castSucc
    have h2 := H i.succ
    simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
    unfold rs at h1 h2
    unfold alt at h1 h2
    split_ifs at h1 h2 with p1 p2 p2 <;> omega

theorem cardT0 : (T 0).card = 1 := by decide
theorem cardT1 : (T 1).card = 2 := by decide
theorem cardT2 : (T 2).card = 3 := by decide
theorem cardT3 : (T 3).card = 2 := by decide
theorem cardT4 : (T 4).card = 1 := by decide

theorem cardT_alt (s i : ℕ) (hs : s < 5) : (T (alt s i)).card = (T s).card := by
  unfold alt
  split_ifs
  · rfl
  · interval_cases s <;> simp [cardT0, cardT1, cardT2, cardT3, cardT4]

theorem filter_eq (n : ℕ) :
    Finset.univ.filter (fun g : Grid n => IsValid g) =
      (Finset.range 5).biUnion
        (fun s => Fintype.piFinset (fun i : Fin (n + 1) => T (alt s i.val))) := by
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_range,
    Fintype.mem_piFinset, T, key]

theorem card_eq (n : ℕ) :
    (Finset.univ.filter (fun g : Grid n => IsValid g)).card = 2 + 2 ^ (n + 2) + 3 ^ (n + 1) := by
  rw [filter_eq, Finset.card_biUnion]
  · have h : ∀ s ∈ Finset.range 5,
        (Fintype.piFinset (fun i : Fin (n + 1) => T (alt s i.val))).card = (T s).card ^ (n + 1) := by
      intro s hs
      rw [Fintype.card_piFinset]
      rw [Finset.prod_congr rfl (fun i _ => cardT_alt s i.val (Finset.mem_range.1 hs))]
      simp
    rw [Finset.sum_congr rfl h]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, cardT0, cardT1, cardT2, cardT3,
      cardT4]
    ring
  · intro s _ s' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro g h1 h2
    rw [Fintype.mem_piFinset] at h1 h2
    have e1 := h1 0
    have e2 := h2 0
    simp only [Fin.val_zero, alt, Nat.zero_mod, if_true, T, Finset.mem_filter] at e1 e2
    exact hne (e1.2.symm.trans e2.2)

theorem closed (n : ℕ) (hn : 1 ≤ n) : a n = 2 + 2 ^ (2 + n) + 3 ^ (1 + n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  show ((Finset.univ.filter (fun g : Grid (m + 1) => IsValid g)).card : ℤ) = _
  rw [card_eq]
  push_cast
  ring

end OMA.A183624Proof

open OMA.S_oeis_a183624 OMA.A183624Proof PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a183624.main := by
  refine ⟨closed, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
      show m + 4 - 3 = m + 1 by omega, closed (m + 4) (by omega), closed (m + 3) (by omega),
      closed (m + 2) (by omega), closed (m + 1) (by omega)]
    ring
  · ext k
    have e1 : ∀ A : PowerSeries ℤ, A * ((1 - X) * (1 - 2 * X) * (1 - 3 * X)) =
        A - C (6 : ℤ) * (A * X ^ 1) + C (11 : ℤ) * (A * X ^ 2) - C (6 : ℤ) * (A * X ^ 3) := by
      intro A
      rw [show (C (6 : ℤ) : PowerSeries ℤ) = 6 from map_ofNat C 6,
        show (C (11 : ℤ) : PowerSeries ℤ) = 11 from map_ofNat C 11]
      ring
    have e2 : (X * (19 - 69 * X + 54 * X ^ 2) : PowerSeries ℤ) =
        C (19 : ℤ) * X ^ 1 - C (69 : ℤ) * X ^ 2 + C (54 : ℤ) * X ^ 3 := by
      rw [show (C (19 : ℤ) : PowerSeries ℤ) = 19 from map_ofNat C 19,
        show (C (69 : ℤ) : PowerSeries ℤ) = 69 from map_ofNat C 69,
        show (C (54 : ℤ) : PowerSeries ℤ) = 54 from map_ofNat C 54]
      ring
    rw [e1, e2]
    simp only [map_add, map_sub, coeff_mul_X_pow', coeff_C_mul, coeff_C, coeff_mk]
    rcases (show k ≤ 3 ∨ 4 ≤ k by omega) with hk | hk
    · have v0 : a 0 = 0 := rfl
      have v1 : a 1 = 19 := by rw [closed 1 le_rfl]; norm_num
      have v2 : a 2 = 45 := by rw [closed 2 (by norm_num)]; norm_num
      have v3 : a 3 = 115 := by rw [closed 3 (by norm_num)]; norm_num
      interval_cases k <;> simp [v0, v1, v2, v3]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
      simp only [show j + 4 - 1 = j + 3 by omega, show j + 4 - 2 = j + 2 by omega,
        show j + 4 - 3 = j + 1 by omega,
        if_pos (show 1 ≤ j + 4 by omega), if_pos (show 2 ≤ j + 4 by omega),
        if_pos (show 3 ≤ j + 4 by omega),
        if_neg (show j + 3 ≠ 0 by omega), if_neg (show j + 2 ≠ 0 by omega),
        if_neg (show j + 1 ≠ 0 by omega),
        closed (j + 4) (by omega), closed (j + 3) (by omega), closed (j + 2) (by omega),
        closed (j + 1) (by omega)]
      ring
