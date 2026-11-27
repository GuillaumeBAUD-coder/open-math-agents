import OMAStatements.S_oeis_a165640
import Mathlib

/-! A multiplicity triple is parametrized by t = z+n+2-x.
The two endpoints of the resulting integer interval give Layman's formula. -/
namespace Deldor14.Multiplicities
open Finset OMA.S_oeis_a165640
private theorem membership (n x y z : ℕ) :
    (x,y,z) ∈ S n ↔ x+y+z=n ∧ (y:ℤ)+3*z-2*x=3 := by
  simp only [S,mem_filter,mem_product,mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨by omega,by omega,by omega⟩,h⟩
theorem result : type_of% @OMA.S_oeis_a165640.main := by
  intro n hn
  let L := 2*(n+4)/3
  let U := 4*(n+4)/5
  have card : (S n).card=(Ioc L U).card := by
    apply card_bij (fun t _ => t.2.2+n+2-t.1)
    · rintro ⟨x,y,z⟩ h
      obtain ⟨eq₁,eq₂⟩ := (membership n x y z).mp h
      rw [mem_Ioc]
      dsimp [L,U]
      omega
    · rintro ⟨x,y,z⟩ h ⟨x',y',z'⟩ h' same
      obtain ⟨eq₁,eq₂⟩ := (membership n x y z).mp h
      obtain ⟨eq₃,eq₄⟩ := (membership n x' y' z').mp h'
      change z+n+2-x=z'+n+2-x' at same
      have : x=x' := by omega
      have : y=y' := by omega
      have : z=z' := by omega
      simp_all
    · intro t ht
      obtain ⟨l,u⟩ := mem_Ioc.mp ht
      dsimp [L,U] at l u
      let x := 2*t-n-7
      let y := 4*(n+4)-5*t
      let z := 3*t-2*n-9
      have mem : (x,y,z) ∈ S n := by
        rw [membership]
        dsimp [x,y,z]
        omega
      exact ⟨(x,y,z),mem,by change z+n+2-x=t;dsimp [x,z];omega⟩
  rw [a,card,Nat.card_Ioc]
  change ((U-L : ℕ) : ℤ)=(U:ℤ)-(L:ℤ)
  apply Nat.cast_sub
  dsimp [L,U]
  omega
end Deldor14.Multiplicities
theorem OMA.solution : type_of% @OMA.S_oeis_a165640.main := Deldor14.Multiplicities.result
