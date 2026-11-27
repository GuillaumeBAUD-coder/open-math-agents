import OMAReductions.R_Erdos372_erdos_372_R1
import Mathlib

/-! Heath-Brown’s difference-divisible sets, as in Sungjin Kim,
*Two remarks on the largest prime factors of n and n+1*, Lemma 3.1. -/
open Finset
namespace Kim372
/-- Enlarging a difference-divisible set by translating it onto a factorial
and adjoining the factorial itself. -/
lemma family (k : ℕ) : ∃ A : Finset ℕ, A.card = k ∧ (∀ a ∈ A, 0 < a) ∧
    ∀ a ∈ A, ∀ b ∈ A, a < b → b-a ∣ a := by
  classical
  induction k with
  | zero => exact ⟨∅,by simp,by simp,by simp⟩
  | succ k ih =>
    obtain ⟨A,hc,ha,hd⟩ := ih
    let M := (A.sup id).factorial
    let S := A.image (M+·)
    have fp (a : ℕ) (h : a ∈ A) : a ∣ M :=
      Nat.dvd_factorial (ha a h) (le_sup (f:=id) h)
    have notmem : M ∉ S := by
      intro h
      obtain ⟨a,haa,he⟩ := mem_image.mp h
      have := ha a haa; omega
    refine ⟨insert M S,?_,?_,?_⟩
    · rw [card_insert_of_notMem notmem,card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h),hc]
    · intro x hx
      rcases mem_insert.mp hx with rfl|h
      · exact Nat.factorial_pos _
      · obtain ⟨a,haa,rfl⟩ := mem_image.mp h
        have := ha a haa; omega
    · intro x hx y hy hxy
      rcases mem_insert.mp hy with rfl|h
      · rcases mem_insert.mp hx with rfl|h'
        · omega
        · obtain ⟨a,haa,rfl⟩ := mem_image.mp h'; omega
      obtain ⟨b,hb,rfl⟩ := mem_image.mp h
      rcases mem_insert.mp hx with rfl|h'
      · simpa using fp b hb
      obtain ⟨a,haa,rfl⟩ := mem_image.mp h'
      have hab := hd a haa b hb (by omega)
      have hdiff : M+b-(M+a)=b-a := by omega
      rw [hdiff]
      exact dvd_add (hab.trans (fp a haa)) hab
end Kim372

theorem OMA.solution : OMA.R_Erdos372_erdos_372_R1.H2 := Kim372.family
