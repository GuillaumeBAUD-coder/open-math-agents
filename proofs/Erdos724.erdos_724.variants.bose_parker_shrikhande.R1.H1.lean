import OMAReductions.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1
import Mathlib

-- Step Erdos724.erdos_724.variants.bose_parker_shrikhande.R1.H1: hypothesis H1 of reduction Erdos724.erdos_724.variants.bose_parker_shrikhande.R1
-- Credit: @luciusacarr

/-! For odd `n`, the Latin squares `i + j` and `i + 2j` (mod `n`) are distinct and orthogonal. -/

open Erdos724

namespace OMA724odd

lemma fin_eq_of_modEq {n : ℕ} {a b : Fin n} (h : a.val ≡ b.val [MOD n]) : a = b :=
  Fin.ext (Nat.ModEq.eq_of_lt_of_lt h a.isLt b.isLt)

/-- The Latin square `(i, j) ↦ i + c * j (mod n)` for `c` coprime to `n`. -/
def sq (n c : ℕ) (hc : Nat.Coprime c n) (hn : 0 < n) : LatinSquare n where
  mat i j := ⟨(i.val + c * j.val) % n, Nat.mod_lt _ hn⟩
  row_injective i j j' h := by
    have h' : i.val + c * j.val ≡ i.val + c * j'.val [MOD n] := by
      unfold Nat.ModEq; simpa [Fin.ext_iff] using h
    exact fin_eq_of_modEq (Nat.ModEq.cancel_left_of_coprime (by
      rw [Nat.gcd_comm]; exact hc) (Nat.ModEq.add_left_cancel' _ h'))
  col_injective j i i' h := by
    have h' : i.val + c * j.val ≡ i'.val + c * j.val [MOD n] := by
      unfold Nat.ModEq
      exact congrArg Fin.val h
    exact fin_eq_of_modEq (Nat.ModEq.add_right_cancel' _ h')

theorem main_H1 : OMA.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1.H1 := by
  unfold OMA.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1.H1
  intro n hodd hn
  have hn0 : 0 < n := by omega
  have h2 : Nat.Coprime 2 n := (Nat.coprime_two_left).mpr hodd
  refine ⟨sq n 1 (Nat.coprime_one_left n) hn0, sq n 2 h2 hn0, ?_, ?_⟩
  · intro h
    have := congrArg (fun L : LatinSquare n => (L.mat ⟨0, hn0⟩ ⟨1, by omega⟩).val) h
    simp only [sq] at this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  · rintro ⟨i, j⟩ ⟨i', j'⟩ h
    simp only [sq, Prod.mk.injEq, Fin.ext_iff] at h
    obtain ⟨ha, hb⟩ := h
    have ha' : i.val + j.val ≡ i'.val + j'.val [MOD n] := by unfold Nat.ModEq; simpa using ha
    have hb' : (i.val + j.val) + j.val ≡ (i.val + j.val) + j'.val [MOD n] := by
      have : i.val + 2 * j.val ≡ i'.val + 2 * j'.val [MOD n] := hb
      have e1 : i.val + 2 * j.val = (i.val + j.val) + j.val := by ring
      have e2 : i'.val + 2 * j'.val = (i'.val + j'.val) + j'.val := by ring
      rw [e1, e2] at this
      exact this.trans (Nat.ModEq.add_right _ ha'.symm)
    have hj : j = j' := fin_eq_of_modEq (Nat.ModEq.add_left_cancel' _ hb')
    subst hj
    have hi : i = i' := fin_eq_of_modEq (Nat.ModEq.add_right_cancel' _ ha')
    subst hi
    rfl

end OMA724odd

theorem OMA.solution : OMA.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1.H1 := OMA724odd.main_H1
