import OMAReductions.R_OeisA1818_conjecture2_R1
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! Group the two matrix expansions by cycle type. Fixed points contribute zero.
A perfect matching on an even number of vertices has a fixed sign. The remaining
inputs are cancellation for long cycles and the determinant evaluation, corresponding
to Lemmas 10 and 14 and Proposition 11 in Yang and Zhang, arXiv:2605.19502. -/

namespace OMA.R_OeisA1818_conjecture2_R1_H2_R1

open Finset Equiv

private lemma signed_permanent {n : ℕ} {R : Type*} [CommRing R]
    (C : Matrix (Fin n) (Fin n) R) (diag : ∀ i, C i i = 0)
    (cancel : ∀ c : Multiset ℕ, (∃ k ∈ c, 3 ≤ k) →
      (∑ σ ∈ univ.filter (fun σ : Perm (Fin n) => σ.cycleType = c), ∏ i, C (σ i) i) = 0) :
    C.det = (-1 : R)^(n/2) * C.permanent := by
  classical
  let w (σ : Perm (Fin n)) : R := ∏ i, C (σ i) i
  let u : R := (-1 : R)^(n/2)
  let eps (σ : Perm (Fin n)) : R := ((Perm.sign σ : ℤ) : R)
  let typ (σ : Perm (Fin n)) := σ.cycleType
  let types := univ.image typ
  have parts (f : Perm (Fin n) → R) :
      (∑ σ, f σ) = ∑ c ∈ types, ∑ σ ∈ univ.filter (fun σ => typ σ = c), f σ :=
    (sum_fiberwise_of_maps_to (fun σ hσ => mem_image_of_mem typ hσ) f).symm
  rw [Matrix.det_apply', Matrix.permanent]
  change (∑ σ, eps σ * w σ) = u * ∑ σ, w σ
  rw [parts (fun σ => eps σ * w σ), parts w, mul_sum]
  apply sum_congr rfl
  intro c hc
  by_cases long : ∃ k ∈ c, 3 ≤ k
  · let v : R := ((((-1 : ℤˣ) ^ (c.sum+c.card) : ℤˣ) : ℤ) : R)
    have same : ∀ σ ∈ univ.filter (fun σ => typ σ = c), eps σ * w σ = v * w σ := by
      intro σ hσ
      have eq : σ.cycleType = c := (mem_filter.mp hσ).2
      dsimp [eps, v]
      rw [σ.sign_of_cycleType, eq]
      simp [Units.val_pow_eq_pow_val]
    rw [sum_congr rfl same, ←mul_sum]
    have vanish : (∑ σ ∈ univ.filter (fun σ => typ σ = c), w σ) = 0 := cancel c long
    rw [vanish, mul_zero, mul_zero]
  · rw [mul_sum]
    apply sum_congr rfl
    intro σ hσ
    have eq : σ.cycleType = c := (mem_filter.mp hσ).2
    by_cases fixed : ∃ i, σ i = i
    · obtain ⟨i,hi⟩ := fixed
      have zero : w σ = 0 := prod_eq_zero (mem_univ i) (by rw [hi, diag])
      rw [zero, mul_zero, mul_zero]
    · have twos : σ.cycleType = Multiset.replicate σ.cycleType.card 2 := by
        apply Multiset.eq_replicate_card.mpr
        intro k hk
        have hlow := Perm.two_le_of_mem_cycleType hk
        have hhigh : ¬ 3 ≤ k := fun h => long ⟨k, eq ▸ hk, h⟩
        omega
      have nofix : IsEmpty (Function.fixedPoints σ) := ⟨fun x => fixed ⟨x.val,x.property⟩⟩
      have hz := Fintype.card_eq_zero_iff.mpr nofix
      have sign := Perm.sign_of_cycleType_eq_replicate zero_lt_two twos
      have e : eps σ = u := by
        dsimp [eps,u]
        rw [sign, if_neg (Nat.not_odd_iff.mpr rfl), hz]
        simp [Units.val_pow_eq_pow_val]
      rw [e]

-- Cancellation is required separately for each cycle type containing a long cycle.
def H1 : Prop := ∀ p : ℕ, p.Prime → p ≠ 2 →
    let C : Matrix (Fin (p-1)) (Fin (p-1)) (ZMod (p^2)) := fun i j =>
      if i=j then 0 else ((i.val : ZMod (p^2)) - j.val)⁻¹
    ∀ c : Multiset ℕ, (∃ k ∈ c, 3 ≤ k) →
      (∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin (p-1)) => σ.cycleType = c),
        ∏ i, C (σ i) i) = 0

-- The determinant of the reciprocal-difference matrix is one modulo p squared.
def H2 : Prop := ∀ p : ℕ, p.Prime → p ≠ 2 →
    let C : Matrix (Fin (p-1)) (Fin (p-1)) (ZMod (p^2)) := fun i j =>
      if i=j then 0 else ((i.val : ZMod (p^2)) - j.val)⁻¹
    C.det = 1

theorem main : H1 → H2 → OMA.R_OeisA1818_conjecture2_R1.H2 := by
  intro cancellation determinant p hp hn
  let C : Matrix (Fin (p-1)) (Fin (p-1)) (ZMod (p^2)) := fun i j =>
      if i=j then 0 else ((i.val : ZMod (p^2)) - j.val)⁻¹
  have relation := signed_permanent C (fun i => by simp [C]) (cancellation p hp hn)
  have detOne : C.det = 1 := determinant p hp hn
  rw [detOne] at relation
  change C.permanent = _
  let h := (p-1)/2
  calc
    C.permanent = ((-1 : ZMod (p^2))^h * (-1)^h) * C.permanent := by
      rw [←mul_pow]; simp
    _ = (-1)^h * 1 := by rw [mul_assoc, ←relation]
    _ = _ := mul_one _

end OMA.R_OeisA1818_conjecture2_R1_H2_R1
