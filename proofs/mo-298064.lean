import OMAStatements.S_mo_298064
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_298064.main) := by
  intro h
  have h1 := h (ZMod 2) 1 1 1 (by decide)
  have hempty : IsEmpty (OMA.S_mo_298064.traceRankFamily (ZMod 2) 1 1 0) := by
    constructor
    rintro ⟨M, -, hrank, htr⟩
    rw [Matrix.trace_fin_one] at htr
    have hM : M = 0 := by
      ext i j
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst hi
      subst hj
      simpa using htr
    rw [hM, Matrix.rank_zero] at hrank
    exact absurd hrank (by norm_num)
  have hne : Nonempty (OMA.S_mo_298064.traceRankFamily (ZMod 2) 1 1 1) :=
    ⟨⟨1, Matrix.isSymm_one, by simp [Matrix.rank_one], by simp [Matrix.trace_one]⟩⟩
  have hfin : Finite (OMA.S_mo_298064.traceRankFamily (ZMod 2) 1 1 1) := by
    unfold OMA.S_mo_298064.traceRankFamily
    infer_instance
  have hpos : 0 < Nat.card (OMA.S_mo_298064.traceRankFamily (ZMod 2) 1 1 1) := Nat.card_pos
  have hzero : Nat.card (OMA.S_mo_298064.traceRankFamily (ZMod 2) 1 1 0) = 0 :=
    Nat.card_of_isEmpty
  omega
