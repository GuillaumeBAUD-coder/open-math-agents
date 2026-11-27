import OMAReductions.R_Green92_green_92_variants_chase_upper_R1
import Mathlib

open Finset Green92

theorem OMA.solution : OMA.R_Green92_green_92_variants_chase_upper_R1.H2 := by
  classical
  intro n m D antisym error
  let wins (o : Fin m → List Bool) (x : Fin n → Bool) := ∀ y, x ≠ y → D x y o
  let R (o : Fin m → List Bool) : Fin n → Bool :=
    if h : ∃ x, wins o x then h.choose else fun _ => false
  have correct o x (hw : wins o x) : R o = x := by
    have h : ∃ x, wins o x := ⟨x,hw⟩
    simp only [R,dif_pos h]
    by_contra ne
    exact antisym _ _ _ ne (h.choose_spec x ne) (hw _ (Ne.symm ne))
  refine ⟨R,?_⟩
  intro x
  let A := Fin m → Finset (Fin n)
  let T := Fintype.card A
  let obs (s : A) := fun j => Green92.trace x (s j)
  let bad (y : Fin n → Bool) : Finset A :=
    univ.filter fun s => x ≠ y ∧ ¬ D x y (obs s)
  have bound y : (bad y).card ≤ T / (10 * 2^n) := by
    by_cases h : x = y
    · simp [bad,h]
    · simpa [bad,h,T,obs,A] using error x y h
  let fail : Finset A := univ.filter fun s => R (obs s) ≠ x
  have sub : fail ⊆ univ.biUnion bad := by
    intro s hs
    have nw : ¬ wins (obs s) x := fun hw => (mem_filter.mp hs).2 (correct _ _ hw)
    simp only [wins, not_forall] at nw
    obtain ⟨y,hy,he⟩ := nw
    exact mem_biUnion.mpr ⟨y,mem_univ _,mem_filter.mpr ⟨mem_univ _,hy,he⟩⟩
  have count : fail.card ≤ 2^n * (T / (10 * 2^n)) := by
    refine (card_le_card sub).trans ?_
    simpa [Fintype.card_fun] using card_biUnion_le_card_mul univ bad _ (fun y _ => bound y)
  have failCount : 10*fail.card ≤ T := calc
    _ ≤ 10 * (2^n * (T / (10 * 2^n))) := Nat.mul_le_mul_left 10 count
    _ ≤ T := by rw [← Nat.mul_assoc]; exact Nat.mul_div_le T _
  let good : Finset A := univ.filter fun s => R (obs s) = x
  have total : good.card + fail.card = T := by
    simpa only [card_univ] using card_filter_add_card_filter_not (s := (univ : Finset A))
      (fun s => R (obs s) = x)
  have inequality : 9 * T ≤ 10 * good.card := by omega
  have den : 0 < (T:ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  change 9/10 ≤ (good.card:ℝ) / T
  apply (le_div_iff₀ den).mpr
  have h : 9 * (T:ℝ) ≤ 10 * (good.card:ℝ) := by exact_mod_cast inequality
  linarith
