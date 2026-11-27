import OMAReductions.R_LatinSquare_numTransversalsZn_R1
import Mathlib

-- Step LatinSquare.numTransversalsZn.R1.H2: hypothesis H2 of reduction LatinSquare.numTransversalsZn.R1
-- Credit: @ivillar

/-!
# The cyclic Latin square of odd order `n ≥ 3` has a transversal, but fewer than `n!` of them

The identity column selector is a transversal because doubling is injective modulo an odd `n`.
Every transversal is an injective selector, there are `n!` injective selectors, and negation is an
injective selector that is not a transversal (`i + (-i) = 0` for every `i`).
-/

namespace LatinSquareCountStep

open LatinSquare

theorem count : ∀ n : ℕ, 3 ≤ n → Odd n → 0 < z n ∧ z n < n.factorial := by
  intro n hn hodd
  have : NeZero n := ⟨by omega⟩
  unfold z numTransversals
  constructor
  · rw [Fintype.card_pos_iff]
    refine ⟨⟨id, Function.injective_id, ?_⟩⟩
    intro i j hij
    simp only [Matrix.of_apply, id_eq] at hij
    have h1 : (i + i).val = (j + j).val := congrArg Fin.val hij
    rw [Fin.val_add, Fin.val_add] at h1
    have h2 : 2 * i.val ≡ 2 * j.val [MOD n] := by
      unfold Nat.ModEq
      rw [two_mul, two_mul]
      exact h1
    have hcop : Nat.gcd n 2 = 1 := by
      rcases hodd with ⟨k, rfl⟩
      simp
    have h3 : i.val ≡ j.val [MOD n] := Nat.ModEq.cancel_left_of_coprime hcop h2
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt h3 i.isLt j.isLt)
  · have hcard : Fintype.card {σ : Fin n → Fin n // Function.Injective σ} = n.factorial := by
      rw [Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin n) (Fin n)),
        Fintype.card_embedding_eq, Fintype.card_fin, Nat.descFactorial_self]
    rw [← hcard]
    refine Fintype.card_lt_of_injective_not_surjective
      (fun x => (⟨x.1, x.2.1⟩ : {σ : Fin n → Fin n // Function.Injective σ})) ?_ ?_
    · intro x y hxy
      have h := congrArg Subtype.val hxy
      exact Subtype.ext h
    · intro hsurj
      obtain ⟨x, hx⟩ := hsurj ⟨fun i => -i, neg_injective⟩
      have hx1 : x.1 = fun i : Fin n => -i := congrArg Subtype.val hx
      have hinj := x.2.2
      rw [hx1] at hinj
      have h01 : (0 : Fin n) = 1 := by
        apply hinj
        simp only [Matrix.of_apply]
        rw [add_neg_cancel, add_neg_cancel]
      have h2 : (0 : Fin n).val = (1 : Fin n).val := congrArg Fin.val h01
      rw [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (by omega)] at h2
      omega

end LatinSquareCountStep

theorem OMA.solution : OMA.R_LatinSquare_numTransversalsZn_R1.H2 :=
  LatinSquareCountStep.count
