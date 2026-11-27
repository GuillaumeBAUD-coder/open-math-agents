import OMAReductions.R_LatinSquare_numTransversalsZn_R1
import Mathlib

open LatinSquare

theorem OMA.solution : OMA.R_LatinSquare_numTransversalsZn_R1.H2 := by
  classical
  intro n hn ho
  letI : NeZero n := ⟨by omega⟩
  let A := {σ : Fin n → Fin n // Function.Injective σ ∧ Function.Injective (fun i ↦ i + σ i)}
  change 0 < Fintype.card A ∧ Fintype.card A < n.factorial
  have two : IsUnit (2 : ZMod n) := by
    simpa using (ZMod.isUnit_iff_coprime 2 n).mpr ho.coprime_two_left
  have diag : Function.Injective (fun i : Fin n ↦ i + i) := by
    intro a b he
    apply (ZMod.finEquiv n).injective
    apply two.mul_right_injective
    simpa only [two_mul,map_add] using congrArg (ZMod.finEquiv n) he
  refine ⟨Fintype.card_pos_iff.mpr ⟨⟨id,Function.injective_id,diag⟩⟩,?_⟩
  let toPerm (s : A) : Equiv.Perm (Fin n) := Equiv.ofBijective s.val
    (Finite.injective_iff_bijective.mp s.property.1)
  have inj : Function.Injective toPerm := by
    intro s t he
    exact Subtype.ext (funext (fun i ↦ congrArg (fun f : Equiv.Perm (Fin n) ↦ f i) he))
  let negP : Equiv.Perm (Fin n) := neg_involutive.toPerm
  have missed : negP ∉ Set.range toPerm := by
    rintro ⟨s,hs⟩
    have hs' (i : Fin n) : s.val i = -i := congrArg (fun f : Equiv.Perm (Fin n) ↦ f i) hs
    let i : Fin n := ⟨0,by omega⟩
    let j : Fin n := ⟨1,by omega⟩
    have h := s.property.2 (a₁ := i) (a₂ := j) (by simp only [hs', add_neg_cancel])
    have hval := congrArg Fin.val h
    contradiction
  have card := Fintype.card_lt_of_injective_of_notMem toPerm inj missed
  simpa [Fintype.card_perm] using card
