import OMAStatements.S_mo_302956
import Mathlib

open OMA.S_mo_302956

theorem OMA.solution : type_of% @OMA.S_mo_302956.main := by
  have hp2 : (Finset.univ : Finset (Fin 3)).powersetCard 2 = {{0, 1}, {0, 2}, {1, 2}} := by decide
  have hp3 : (Finset.univ : Finset (Fin 3)).powersetCard 3 = {{0, 1, 2}} := by decide
  have hf : (Finset.univ.filter (fun i : Fin 3 => i.val < 2)) = {0, 1} := by decide
  refine ⟨3, ![9, 2, 2], ![6, 6, 1], by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num
  · intro i
    fin_cases i <;> norm_num
  · simp [Fin.sum_univ_three]
    norm_num
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [Fin.le_def] <;> norm_num
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [Fin.le_def] <;> norm_num
  · intro k hk1 hk2
    interval_cases k
    · simp only [esymm, psum, hp2, Fin.sum_univ_three]
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
        Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
      simp [Finset.prod_pair]
      norm_num
    · simp only [esymm, psum, hp3, Fin.sum_univ_three, Finset.sum_singleton]
      rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton,
        Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
      simp [Matrix.cons_val]
      norm_num
  · rintro ⟨-, -, -, h⟩
    have h2 := h 2 (by norm_num) (by norm_num)
    rw [hf, Finset.sum_pair (by decide), Finset.sum_pair (by decide)] at h2
    norm_num at h2
