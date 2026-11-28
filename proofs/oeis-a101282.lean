import OMAStatements.S_oeis_a101282
import Mathlib

/-!
# A101282: Schroder paths by valleys and the triangle recursion

Proof idea. Let VA(L, h) be the valley generating polynomial of all valid Schroder suffixes of
length L starting at height h, and VB(L, h) the same with a down step in front. First-step
decomposition gives VA(L+2, h) = VA(L+1, h+1) + [h > 0] VB(L+1, h-1) + VA(L, h) and
VB(L+1, h) = VA(L+1, h) + (X - 1) VA(L, h+1). Then kurkovR n k = VA(2n-k, k) - VA(2n-k-1, k+1)
(paths with exactly k leading up steps) by induction, and the row polynomial is VA(2n, 0).
-/

namespace OMA.Helpers

open OMA.S_oeis_a101282 Polynomial

/-- All valid Schroder suffixes of total length `L` starting at height `h`. -/
def schGen : ℕ → ℕ → List (List SchroderStep)
  | 0, h => if h = 0 then [[]] else []
  | 1, h => (schGen 0 (h + 1)).map (List.cons .U) ++
      (if 0 < h then (schGen 0 (h - 1)).map (List.cons .D) else [])
  | L + 2, h => (schGen (L + 1) (h + 1)).map (List.cons .U) ++
      (if 0 < h then (schGen (L + 1) (h - 1)).map (List.cons .D) else []) ++
      (schGen L h).map (List.cons .H)

theorem schGen_mem : ∀ (p : List SchroderStep) (L h : ℕ),
    p ∈ schGen L h ↔ isSchroderAux h p ∧ stepLen p = L := by
  intro p
  induction p with
  | nil =>
    intro L h
    rcases L with _ | _ | L <;> simp [schGen, isSchroderAux, stepLen]
  | cons s q ih =>
    intro L h
    rcases L with _ | _ | L
    · rw [schGen.eq_1]
      cases s <;> simp [isSchroderAux, stepLen] <;> omega
    · rw [schGen.eq_2]
      cases s <;> simp [isSchroderAux, stepLen, ih] <;>
        first | omega | (intro _; omega) | (constructor <;> intro hh <;> omega) | tauto |
          exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, by omega⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, by omega⟩⟩
    · rw [schGen.eq_3]
      cases s <;> simp [isSchroderAux, stepLen, ih] <;>
        first | omega | (intro _; omega) | (constructor <;> intro hh <;> omega) | tauto |
          exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, by omega⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, by omega⟩⟩

theorem schGen_nodup : ∀ (L h : ℕ), (schGen L h).Nodup
  | 0, h => by unfold schGen; split_ifs <;> simp
  | 1, h => by
    unfold schGen
    rw [List.nodup_append]
    refine ⟨(schGen_nodup 0 _).map (fun _ _ e => List.cons_injective e), ?_, ?_⟩
    · split_ifs
      · exact (schGen_nodup 0 _).map (fun _ _ e => List.cons_injective e)
      · simp
    · intro a ha b hb
      simp only [List.mem_map] at ha
      split_ifs at hb
      · simp only [List.mem_map] at hb
        obtain ⟨x, -, rfl⟩ := ha
        obtain ⟨y, -, rfl⟩ := hb
        simp
      · simp at hb
  | L + 2, h => by
    unfold schGen
    rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨(schGen_nodup (L + 1) _).map (fun _ _ e => List.cons_injective e), ?_, ?_⟩,
      (schGen_nodup L _).map (fun _ _ e => List.cons_injective e), ?_⟩
    · split_ifs
      · exact (schGen_nodup (L + 1) _).map (fun _ _ e => List.cons_injective e)
      · simp
    · intro a ha b hb
      simp only [List.mem_map] at ha
      split_ifs at hb
      · simp only [List.mem_map] at hb
        obtain ⟨x, -, rfl⟩ := ha
        obtain ⟨y, -, rfl⟩ := hb
        simp
      · simp at hb
    · intro a ha b hb
      simp only [List.mem_map] at hb
      obtain ⟨y, -, rfl⟩ := hb
      simp only [List.mem_append, List.mem_map] at ha
      rcases ha with ⟨x, -, rfl⟩ | ha
      · simp
      · split_ifs at ha
        · simp only [List.mem_map] at ha
          obtain ⟨x, -, rfl⟩ := ha
          simp
        · simp at ha

theorem schGen_nil : ∀ (L h : ℕ), L < h → schGen L h = []
  | 0, h, hh => by unfold schGen; rw [if_neg (by omega)]
  | 1, h, hh => by
    unfold schGen
    rw [schGen_nil 0 (h + 1) (by omega), schGen_nil 0 (h - 1) (by omega)]
    simp
  | L + 2, h, hh => by
    unfold schGen
    rw [schGen_nil (L + 1) (h + 1) (by omega), schGen_nil (L + 1) (h - 1) (by omega),
      schGen_nil L h (by omega)]
    simp

theorem sch_valleys_U (l : List SchroderStep) : valleys (.U :: l) = valleys l := rfl
theorem sch_valleys_H (l : List SchroderStep) : valleys (.H :: l) = valleys l := rfl
theorem sch_valleys_DU (l : List SchroderStep) :
    valleys (.D :: .U :: l) = 1 + valleys l := rfl
theorem sch_valleys_DD (l : List SchroderStep) :
    valleys (.D :: .D :: l) = valleys (.D :: l) := rfl
theorem sch_valleys_DH (l : List SchroderStep) :
    valleys (.D :: .H :: l) = valleys l := rfl

theorem sch_valleys_le : ∀ p : List SchroderStep,
    2 * valleys p + (if p.head? = some .U then 1 else 0) ≤ stepLen p := by
  intro p
  induction p with
  | nil => simp [valleys, stepLen]
  | cons s q ih =>
    cases s with
    | U => simp [sch_valleys_U, stepLen] at ih ⊢; split_ifs at ih <;> omega
    | H => simp [sch_valleys_H, stepLen] at ih ⊢; split_ifs at ih <;> omega
    | D =>
      rcases q with _ | ⟨t, r⟩
      · simp [valleys, stepLen]
      · cases t with
        | U => simp [sch_valleys_DU, sch_valleys_U, stepLen] at ih ⊢; omega
        | D => simp [sch_valleys_DD, stepLen] at ih ⊢; omega
        | H => simp [sch_valleys_DH, sch_valleys_H, stepLen] at ih ⊢; omega

/-- Valley generating polynomial of the suffixes. -/
noncomputable def schVA (L h : ℕ) : ℤ[X] :=
  ((schGen L h).map (fun p => (X : ℤ[X]) ^ valleys p)).sum

/-- Same, with a preceding down step. -/
noncomputable def schVB (L h : ℕ) : ℤ[X] :=
  ((schGen L h).map (fun p => (X : ℤ[X]) ^ valleys (SchroderStep.D :: p))).sum

theorem schVA_zero_lt (L h : ℕ) (hh : L < h) : schVA L h = 0 := by
  simp [schVA, schGen_nil L h hh]

theorem schVA_rec (L h : ℕ) : schVA (L + 2) h =
    schVA (L + 1) (h + 1) + (if 0 < h then schVB (L + 1) (h - 1) else 0) + schVA L h := by
  unfold schVA schVB
  rw [schGen.eq_3]
  split_ifs <;> simp [Function.comp_def, sch_valleys_U, sch_valleys_H] <;> ring

theorem schVB_rec (L h : ℕ) :
    schVB (L + 1) h = schVA (L + 1) h + (X - 1) * schVA L (h + 1) := by
  rcases L with _ | L
  · unfold schVA schVB
    rw [schGen.eq_2]
    split_ifs <;>
      simp [Function.comp_def, sch_valleys_DU, sch_valleys_DD, pow_add,
        sch_valleys_U, sch_valleys_H, List.sum_map_mul_left] <;> ring
  · unfold schVA schVB
    rw [schGen.eq_3]
    split_ifs <;>
      simp [List.map_map, Function.comp_def, sch_valleys_DU, sch_valleys_DD, sch_valleys_DH,
        sch_valleys_U, sch_valleys_H, pow_add, List.sum_map_mul_left] <;> ring

theorem schVA_zero_zero : schVA 0 0 = 1 := by simp [schVA, schGen, valleys]

theorem schVA_diag : ∀ h : ℕ, schVA h h = 1
  | 0 => schVA_zero_zero
  | 1 => by simp [schVA, schGen, valleys]
  | h + 2 => by
    rw [schVA_rec, if_pos (by omega), schVB_rec, schVA_zero_lt (h + 1) (h + 2 + 1) (by omega),
      schVA_zero_lt h (h + 2) (by omega), show h + 2 - 1 = h + 1 by omega, schVA_diag (h + 1),
      schVA_zero_lt h (h + 1 + 1) (by omega)]
    ring

theorem sch_row (n : ℕ) : schroderRowPoly n = schVA (2 * n) 0 := by
  classical
  have hset : ∀ k, {p : List SchroderStep | isSchroderAux 0 p ∧ stepLen p = 2 * n ∧
      valleys p = k} = ↑(((schGen (2 * n) 0).toFinset).filter (fun p => valleys p = k)) := by
    intro k
    ext p
    simp [schGen_mem, and_assoc]
  have hcount : ∀ k, schroderValleyCount n k =
      (((schGen (2 * n) 0).toFinset).filter (fun p => valleys p = k)).card := by
    intro k
    unfold schroderValleyCount
    rw [hset k, Set.ncard_coe_finset]
  unfold schroderRowPoly schVA
  rw [← List.sum_toFinset _ (schGen_nodup _ _)]
  rw [← Finset.sum_fiberwise_of_maps_to' (s := (schGen (2 * n) 0).toFinset)
    (t := Finset.range (n + 1)) (g := valleys) (f := fun k => (X : ℤ[X]) ^ k)]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hcount k, Finset.sum_const, nsmul_eq_mul]
  · intro p hp
    rw [List.mem_toFinset, schGen_mem] at hp
    have := sch_valleys_le p
    simp only [Finset.mem_range]
    omega

theorem sch_kurkov : ∀ n k : ℕ, k ≤ n →
    kurkovR n k = schVA (2 * n - k) k - schVA (2 * n - k - 1) (k + 1) := by
  intro n
  induction n with
  | zero =>
    intro k hk
    obtain rfl : k = 0 := by omega
    rw [kurkovR]
    simp [schVA_zero_zero, schVA_zero_lt 0 1 (by omega)]
  | succ m ih =>
    have hsum : ∀ k, k ≤ m + 1 → ∑ j ∈ Finset.range k, kurkovR m j =
        schVA (2 * m) 0 - schVA (2 * m - k) k := by
      intro k hk
      have : ∀ j ∈ Finset.range k, kurkovR m j =
          schVA (2 * m - j) j - schVA (2 * m - (j + 1)) (j + 1) := by
        intro j hj
        rw [Finset.mem_range] at hj
        rw [ih j (by omega)]
        congr 2
      rw [Finset.sum_congr rfl this, Finset.sum_range_sub' (fun j => schVA (2 * m - j) j)]
      simp
    have h0 : kurkovR (m + 1) 0 = schVA (2 * m) 0 := by
      rw [kurkovR, if_neg (by omega), if_pos rfl]
      try simp only
      rw [hsum (m + 1) le_rfl, schVA_zero_lt (2 * m - (m + 1)) (m + 1) (by omega), sub_zero]
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [h0]
      have := schVA_rec (2 * m) 0
      simp only [lt_irrefl, if_false, add_zero] at this
      rw [show 2 * (m + 1) - 0 = 2 * m + 2 by omega, show 2 * m + 2 - 1 = 2 * m + 1 by omega,
        this]
      ring
    rcases Nat.lt_or_ge k (m + 1) with hlt | hge
    · rw [kurkovR, if_neg (by omega), if_neg (by omega), if_pos hlt]
      try simp only
      rw [h0, hsum k (by omega), ih (k - 1) (by omega)]
      obtain ⟨L, hL⟩ : ∃ L, 2 * m - k = L := ⟨_, rfl⟩
      have e1 : 2 * m - (k - 1) = L + 1 := by omega
      have e2 : 2 * m - (k - 1) - 1 = L := by omega
      have e3 : k - 1 + 1 = k := by omega
      have e4 : 2 * (m + 1) - k = L + 2 := by omega
      have e5 : 2 * (m + 1) - k - 1 = L + 1 := by omega
      rw [e2, e1, e3, e5, e4, hL, schVA_rec L k, if_pos hkpos, schVB_rec, e3]
      ring
    · obtain rfl : k = m + 1 := by omega
      rw [kurkovR, if_pos rfl]
      rw [show 2 * (m + 1) - (m + 1) = m + 1 by omega, schVA_diag,
        schVA_zero_lt _ _ (by omega)]
      simp

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a101282.main := by
  intro n
  rw [sch_row, sch_kurkov (n + 1) 0 (by omega)]
  have := schVA_rec (2 * n) 0
  simp only [lt_irrefl, if_false, add_zero] at this
  rw [show 2 * (n + 1) - 0 = 2 * n + 2 by omega, show 2 * n + 2 - 1 = 2 * n + 1 by omega,
    this]
  ring
