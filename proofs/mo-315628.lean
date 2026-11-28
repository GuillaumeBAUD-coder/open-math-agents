import OMAStatements.S_mo_315628
import Mathlib

open Finset

open OMA.S_mo_315628

private def tripleBits : Bool × Bool × Bool ≃ (Fin 3 → Bool) where
  toFun b := ![b.1,b.2.1,b.2.2]
  invFun x := (x 0,x 1,x 2)
  left_inv _ := rfl
  right_inv x := by funext i; fin_cases i <;> rfl

@[simp] private theorem tripleBits_zero (a b c : Bool) : tripleBits (a,b,c) 0 = a := rfl
@[simp] private theorem tripleBits_one (a b c : Bool) : tripleBits (a,b,c) 1 = b := rfl
@[simp] private theorem tripleBits_two (a b c : Bool) : tripleBits (a,b,c) 2 = c := rfl

private theorem successes_triple (a b c : Bool) :
    successes (tripleBits (a,b,c)) =
      (if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0) := by
  cases a <;> cases b <;> cases c <;> decide

private noncomputable def pairMass (x : Fin 3 → Bool) : ℝ :=
  if successes x = 0 then 1/2 else if successes x = 2 then 1/6 else 0

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_315628.main) := by
  intro h
  have hnonneg (x : Fin 3 → Bool) : 0 ≤ pairMass x := by
    unfold pairMass
    split <;> norm_num
    split <;> norm_num
  have hsum : ∑ x, pairMass x = 1 := by
    rw [← Equiv.sum_comp tripleBits]
    norm_num [Fintype.sum_prod_type,Fintype.sum_bool,pairMass,successes_triple]
  have hperm (x : Fin 3 → Bool) (σ : Equiv.Perm (Fin 3)) : pairMass (x ∘ σ) = pairMass x := by
    have he : successes (x ∘ σ) = successes x := Equiv.sum_comp σ (fun i => if x i then 1 else 0)
    simp only [pairMass,he]
  have hbound (x : Fin 3 → Bool) (hx : 0 < pairMass x) : successes x ≤ 2 := by
    unfold pairMass at hx
    split at hx
    · omega
    · split at hx
      · omega
      · exact (lt_irrefl (0 : ℝ) hx).elim
  have hbad := h 3 2 (by decide) pairMass hnonneg hsum hperm hbound 0 1 (by decide)
  unfold meanProduct meanBit at hbad
  simp only [← Equiv.sum_comp tripleBits] at hbad
  norm_num [Fintype.sum_prod_type,Fintype.sum_bool,pairMass,successes_triple] at hbad
