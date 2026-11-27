import OMAReductions.R_Erdos964_erdos_964_variants_eberhard_R1

/-! Credit: @marcusbuffett. A Chinese remainder change of variable separates the
elementary normalization from the admissible-triple theorem of Goldston,
Graham, Pintz and Yıldırım (as used in Eberhard, arXiv:2505.00727). -/

namespace OMA.R_Erdos964_erdos_964_variants_eberhard_R1_H1_R1

open Finset

/-- The unweighted admissible-triple theorem with primes above a prescribed threshold. -/
def H1 : Prop :=
  ∀ a b : Fin 3 → ℕ, (∀ i, 0 < a i ∧ 0 < b i) →
    (∀ i j, i ≠ j → a i * b j ≠ a j * b i) →
    (∀ p : ℕ, p.Prime → ∃ z : ℕ, ∀ i, ¬p ∣ a i*z+b i) →
    ∀ T : ℕ, ∃ i j : Fin 3, i < j ∧
      {z : ℕ | ∀ l ∈ ({i,j} : Finset (Fin 3)), ∃ p s : ℕ,
        p.Prime ∧ s.Prime ∧ p ≠ s ∧ T < p ∧ T < s ∧ a l*z+b l=p*s}.Infinite

/-- A single arithmetic progression removes the prescribed factors and
produces a primitive admissible system with three distinct roots. -/
def H2 : Prop :=
  ∀ A r : Fin 3 → ℕ, ((∀ i, 0 < A i ∧ 0 < r i ∧ (r i).Coprime (A i)) ∧ StrictMono A ∧
     (∀ i j, i ≠ j → (r i).Coprime (r j) ∧
       (r i).Coprime (if A i > A j then A i - A j else A j - A i))) →
    ∃ M x : ℕ, ∃ a b : Fin 3 → ℕ, 0 < M ∧
      (∀ i, 0 < a i ∧ 0 < b i) ∧
      (∀ i j, i ≠ j → a i * b j ≠ a j * b i) ∧
      (∀ p : ℕ, p.Prime → ∃ z : ℕ, ∀ i, ¬p ∣ a i*z+b i) ∧
      ∀ i z, A i*(M*z+x)+1 = r i*(a i*z+b i)

theorem main : H1 → H2 → OMA.R_Erdos964_erdos_964_variants_eberhard_R1.H1 := by
  intro ggpy crt A r h T
  obtain ⟨M,x,a,b,hM,hpos,hdist,hadm,hid⟩ := crt A r h
  obtain ⟨i,j,hij,hInf⟩ := ggpy a b hpos hdist hadm T
  refine ⟨i,j,hij,?_⟩
  let f (z : ℕ) := M*z+x
  have hf : Function.Injective f := fun z w he =>
    Nat.eq_of_mul_eq_mul_left hM (Nat.add_right_cancel he)
  apply (hInf.image hf.injOn).mono
  rintro y ⟨z,hz,rfl⟩ l hl
  obtain ⟨p,s,hp,hs,hps,hT,hT',he⟩ := hz l hl
  exact ⟨p,s,hp,hs,hps,hT,hT',(hid l z).trans (congrArg (r l * ·) he)⟩

end OMA.R_Erdos964_erdos_964_variants_eberhard_R1_H1_R1
