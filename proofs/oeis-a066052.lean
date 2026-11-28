import OMAStatements.S_oeis_a066052
import Mathlib

namespace OMA.Aux066052

open Equiv

noncomputable def Inv (α : Type*) [Fintype α] [DecidableEq α] : ℕ :=
  Fintype.card {σ : Perm α // σ * σ = 1}

theorem inv_congr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) : Inv α = Inv β := by
  unfold Inv
  refine Fintype.card_congr (e.permCongr.subtypeEquiv ?_)
  intro σ
  constructor
  · intro h
    ext x
    have := congrArg (fun f : Perm α => f (e.symm x)) h
    simp only [Perm.mul_apply, Perm.one_apply] at this
    simp [Equiv.permCongr_apply, Perm.mul_apply, this]
  · intro h
    ext x
    have := congrArg (fun f : Perm β => f (e x)) h
    simpa [Equiv.permCongr_apply, Perm.mul_apply] using this

theorem lemA {α : Type*} [DecidableEq α] (σ : Perm α) :
    (swap none none * σ.optionCongr) * (swap none none * σ.optionCongr) = 1 ↔ σ * σ = 1 := by
  rw [swap_self, Perm.refl_mul]
  constructor
  · intro h
    ext x
    have := congrArg (fun f : Perm (Option α) => f (some x)) h
    simpa [Perm.mul_apply] using this
  · intro h
    ext x
    rcases x with _ | x
    · simp [Perm.mul_apply]
    · have := congrArg (fun f : Perm α => f x) h
      simp only [Perm.mul_apply, Perm.one_apply] at this
      simp [Perm.mul_apply, this]

theorem lemB {α : Type*} [DecidableEq α] (a : α) (σ : Perm α) :
    (swap none (some a) * σ.optionCongr) * (swap none (some a) * σ.optionCongr) = 1 ↔
      σ * σ = 1 ∧ σ a = a := by
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = swap none (some a) * σ.optionCongr := ⟨_, rfl⟩
  rw [← hτ]
  have key : ∀ x : α, τ (some x) = if σ x = a then none else some (σ x) := by
    intro x
    rw [hτ]
    simp only [Perm.mul_apply, optionCongr_apply, Option.map_some]
    split_ifs with h
    · rw [h, swap_apply_right]
    · exact swap_apply_of_ne_of_ne (Option.some_ne_none _) (fun h' => h (Option.some_injective _ h'))
  have hnone : τ none = some a := by
    rw [hτ]
    simp [Perm.mul_apply]
  have tt : τ * τ = 1 ↔ ∀ x, τ (τ x) = x := by
    constructor
    · intro h x
      rw [← Perm.mul_apply, h, Perm.one_apply]
    · intro h
      ext x
      rw [Perm.mul_apply, h, Perm.one_apply]
  rw [tt]
  constructor
  · intro h
    have h1 := h none
    rw [hnone, key] at h1
    have hfix : σ a = a := by
      by_contra hc
      rw [if_neg hc] at h1
      exact Option.some_ne_none _ h1
    refine ⟨?_, hfix⟩
    ext x
    simp only [Perm.mul_apply, Perm.one_apply]
    by_cases hx : x = a
    · rw [hx, hfix, hfix]
    · have hsx : σ x ≠ a := fun h' => hx (σ.injective (h'.trans hfix.symm))
      have hssx : σ (σ x) ≠ a := by
        intro h'
        exact hsx (σ.injective (h'.trans hfix.symm))
      have h2 := h (some x)
      rw [key, if_neg hsx, key, if_neg hssx] at h2
      exact Option.some_injective _ h2
  · rintro ⟨h, hfix⟩ x
    rcases x with _ | x
    · rw [hnone, key, if_pos hfix]
    · by_cases hx : x = a
      · subst hx
        rw [key, if_pos hfix, hnone]
      · have hsx : σ x ≠ a := fun h' => hx (σ.injective (h'.trans hfix.symm))
        have hssx : σ (σ x) ≠ a := by
          intro h'
          exact hsx (σ.injective (h'.trans hfix.symm))
        rw [key, if_neg hsx, key, if_neg hssx]
        have := congrArg (fun f : Perm α => f x) h
        simp only [Perm.mul_apply, Perm.one_apply] at this
        rw [this]

theorem inv_option (α : Type*) [Fintype α] [DecidableEq α] :
    Inv (Option α) = Inv α + ∑ a : α, Fintype.card {σ : Perm α // σ * σ = 1 ∧ σ a = a} := by
  unfold Inv
  have e1 : {σ : Perm (Option α) // σ * σ = 1} ≃
      {p : Option α × Perm α // (Perm.decomposeOption.symm p) * (Perm.decomposeOption.symm p) = 1} :=
    (Perm.decomposeOption.symm.subtypeEquiv (fun _ => Iff.rfl)).symm
  rw [Fintype.card_congr e1,
    Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun (o : Option α) (s : Perm α) =>
        (Perm.decomposeOption.symm (o, s)) * (Perm.decomposeOption.symm (o, s)) = 1)),
    Fintype.card_sigma, Fintype.sum_option]
  congr 1
  · exact Fintype.card_congr (Equiv.subtypeEquivRight (fun s => lemA s))
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun s => lemB a s))

theorem fix_count {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    Fintype.card {σ : Perm α // σ * σ = 1 ∧ σ a = a} = Inv {x : α // x ≠ a} := by
  unfold Inv
  symm
  have e2 : {τ : Perm {x : α // x ≠ a} // τ * τ = 1} ≃
      {f : {f : Perm α // ∀ b, ¬ b ≠ a → f b = b} // f.1 * f.1 = 1} := by
    refine (Perm.subtypeEquivSubtypePerm (fun x : α => x ≠ a)).subtypeEquiv ?_
    intro τ
    change τ * τ = 1 ↔ Perm.ofSubtype τ * Perm.ofSubtype τ = 1
    rw [← map_mul, ← (Perm.ofSubtype (p := fun x : α => x ≠ a)).map_one]
    exact (Perm.ofSubtype_injective).eq_iff.symm
  rw [Fintype.card_congr e2]
  refine (Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun f : Perm α => ∀ b, ¬ b ≠ a → f b = b) (fun f : Perm α => f * f = 1))).trans ?_
  refine Fintype.card_congr (Equiv.subtypeEquivRight ?_)
  intro f
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, h1 a (by simp)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1⟩
    intro b hb
    have : b = a := by simpa using hb
    rw [this, h2]

noncomputable def I (n : ℕ) : ℕ := Inv (Fin n)

theorem I_rec (n : ℕ) : I (n + 2) = I (n + 1) + (n + 1) * I n := by
  unfold I
  rw [inv_congr (finSuccEquiv (n + 1)), inv_option]
  congr 1
  have : ∀ a : Fin (n + 1), Fintype.card {σ : Perm (Fin (n + 1)) // σ * σ = 1 ∧ σ a = a} =
      Inv (Fin n) := by
    intro a
    rw [fix_count]
    apply inv_congr
    apply Fintype.equivFinOfCardEq
    simp
  rw [Finset.sum_congr rfl (fun a _ => this a)]
  simp

theorem a_eq (n : ℕ) : (OMA.S_oeis_a066052.a n : ℤ) = (n.factorial : ℤ) - I n := by
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Perm (Fin n)))) (fun σ => 3 ≤ orderOf σ)
  have hc : (Finset.univ.filter fun σ : Perm (Fin n) => ¬ 3 ≤ orderOf σ).card = I n := by
    unfold I Inv
    rw [Fintype.card_subtype]
    congr 1
    apply Finset.filter_congr
    intro σ _
    have hpos := orderOf_pos σ
    rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, Nat.dvd_prime Nat.prime_two]
    omega
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin, hc] at hsum
  unfold OMA.S_oeis_a066052.a
  omega

end OMA.Aux066052

open OMA.Aux066052 in
theorem OMA.solution : type_of% @OMA.S_oeis_a066052.main := by
  have r1 : ∀ m : ℕ, (I (m + 2) : ℤ) = I (m + 1) + (m + 1) * I m := by
    intro m
    rw [I_rec]
    push_cast
    ring
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have e1 : m + 3 - 1 = m + 2 := by omega
    have e2 : m + 3 - 2 = m + 1 := by omega
    have e3 : m + 3 - 3 = m := by omega
    rw [e1, e2, e3, a_eq, a_eq, a_eq, a_eq]
    have h3 := r1 (m + 1)
    have h2 := r1 m
    simp only [Nat.factorial_succ] at *
    push_cast at *
    rw [h3, h2]
    ring
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have e1 : m + 4 - 1 = m + 3 := by omega
    have e2 : m + 4 - 2 = m + 2 := by omega
    have e3 : m + 4 - 3 = m + 1 := by omega
    have e4 : m + 4 - 4 = m := by omega
    rw [e1, e2, e3, e4, a_eq, a_eq, a_eq, a_eq, a_eq]
    have h4 := r1 (m + 2)
    have h3 := r1 (m + 1)
    have h2 := r1 m
    simp only [Nat.factorial_succ] at *
    push_cast at *
    rw [h4, h3, h2]
    ring
