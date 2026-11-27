import OMAStatements.S_oeis_a183761

namespace OMA.P_oeis_a183761

open OMA.S_oeis_a183761

def sw (M : (ℕ × ℕ) × (ℕ × ℕ)) : (ℕ × ℕ) × (ℕ × ℕ) := (M.2, M.1)

lemma det_sw (M : (ℕ × ℕ) × (ℕ × ℕ)) : det (sw M) = -det M := by
  simp only [sw, det]; ring

lemma sw_sw (M : (ℕ × ℕ) × (ℕ × ℕ)) : sw (sw M) = M := rfl

lemma mem_sw {n : ℕ} {M : (ℕ × ℕ) × (ℕ × ℕ)} : sw M ∈ mats n ↔ M ∈ mats n := by
  simp only [sw, mats, Finset.mem_product]; tauto

lemma rowLt_asymm {r s : ℕ × ℕ} (h : RowLt r s) : ¬ RowLt s r := by
  obtain ⟨a, b⟩ := r; obtain ⟨c, d⟩ := s
  simp only [RowLt] at *; omega

lemma rowLt_total {r s : ℕ × ℕ} (h : r ≠ s) (h' : ¬ RowLt r s) : RowLt s r := by
  obtain ⟨a, b⟩ := r; obtain ⟨c, d⟩ := s
  simp only [RowLt, ne_eq, Prod.mk.injEq] at *; omega

lemma ne_of_det {M : (ℕ × ℕ) × (ℕ × ℕ)} (h : det M ≠ 0) : M.1 ≠ M.2 := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := M
  intro he
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact h (by simp only [det]; ring)

end OMA.P_oeis_a183761

open OMA.S_oeis_a183761 OMA.P_oeis_a183761

theorem OMA.solution : type_of% @OMA.S_oeis_a183761.main := by
  intro n _
  classical
  refine Finset.card_bij' (fun M _ => if 0 < det M then M else sw M)
    (fun M _ => if RowLt M.1 M.2 then M else sw M) ?_ ?_ ?_ ?_
  · intro M hM
    obtain ⟨hm, hr, hd⟩ := Finset.mem_filter.1 hM
    apply Finset.mem_filter.2
    split_ifs with h
    · exact ⟨hm, h⟩
    · refine ⟨mem_sw.2 hm, ?_⟩
      rw [det_sw]; omega
  · intro M hM
    obtain ⟨hm, hd⟩ := Finset.mem_filter.1 hM
    apply Finset.mem_filter.2
    split_ifs with h
    · exact ⟨hm, h, by omega⟩
    · refine ⟨mem_sw.2 hm, rowLt_total (ne_of_det (by omega)) h, ?_⟩
      rw [det_sw]; omega
  · intro M hM
    obtain ⟨hm, hr, hd⟩ := Finset.mem_filter.1 hM
    by_cases h : 0 < det M
    · simp only [h, if_true, hr]
    · have h2 : ¬ RowLt (sw M).1 (sw M).2 := rowLt_asymm hr
      simp only [h, if_false, h2, sw_sw]
  · intro M hM
    obtain ⟨hm, hd⟩ := Finset.mem_filter.1 hM
    by_cases h : RowLt M.1 M.2
    · simp only [h, if_true, hd]
    · have h2 : ¬ 0 < det (sw M) := by rw [det_sw]; omega
      simp only [h, if_false, h2, sw_sw]
