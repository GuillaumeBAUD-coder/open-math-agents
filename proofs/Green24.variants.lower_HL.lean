import FormalConjectures.GreensOpenProblems.«24»

/-! The interval of length 6m contains a translate for each of 3m starts
and each step between 1 and m. -/

open Green24 Green24.variants Filter

namespace OMA.Translates

def pairs (A : Finset ℤ) := (A ×ˢ A).filter (fun (x,y) => x ≠ y ∧ x + 3*(y-x) ∈ A)

lemma interval_count (m : ℕ) : 3*m*m ≤ max013AffineTranslates (6*m) := by
  let A : Finset ℤ := Finset.Ico 0 (6*(m : ℤ))
  have size : A.card = 6*m := by simp [A, Int.card_Ico]; omega
  let f (u : Fin (3*m) × Fin m) : ℤ × ℤ :=
    ((u.1.val : ℤ), (u.1.val : ℤ) + u.2.val + 1)
  have mem (u : Fin (3*m) × Fin m) : f u ∈ pairs A := by
    have hx := u.1.isLt
    have hd := u.2.isLt
    simp [pairs, A, f, Finset.mem_product]
    omega
  let emb : (Fin (3*m) × Fin m) ↪ ↥(pairs A) := ⟨fun u => ⟨f u, mem u⟩, by
    intro u v he
    have hh := congrArg Subtype.val he
    have h₁ := congrArg Prod.fst hh
    have h₂ := congrArg Prod.snd hh
    dsimp [f] at h₁ h₂
    apply Prod.ext <;> apply Fin.ext <;> omega⟩
  have lower := Fintype.card_le_of_embedding emb
  have upper : (pairs A).card ≤ max013AffineTranslates (6*m) := by
    apply le_csSup
    · refine ⟨(6*m)^2, ?_⟩
      rintro k ⟨B,hB,rfl⟩
      exact (Finset.card_filter_le _ _).trans_eq (by simp [hB,pow_two])
    · exact ⟨A, size, rfl⟩
  exact (by simpa using lower : 3*m*m ≤ (pairs A).card).trans upper

end OMA.Translates

theorem OMA.solution : type_of% @Green24.variants.lower_HL := by
  unfold gamma
  apply le_limsup_of_frequently_le
  · apply frequently_atTop.mpr
    intro n
    let m := n+1
    refine ⟨6*m, by dsimp [m]; omega, ?_⟩
    have hm : (0 : ℝ) < m := by dsimp [m]; positivity
    have hh : 3*(m : ℝ)*m ≤ max013AffineTranslates (6*m) := by
      exact_mod_cast OMA.Translates.interval_count m
    push_cast
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  · refine ⟨1, ?_⟩
    change ∀ᶠ n : ℕ in atTop, (max013AffineTranslates n : ℝ) / (n : ℝ)^2 ≤ 1
    apply Eventually.of_forall
    intro n
    by_cases hn : n = 0
    · simp [hn]
    have h : (max013AffineTranslates n : ℝ) ≤ (n : ℝ)^2 := by
      exact_mod_cast (upper_trivial (n := n))
    exact (div_le_one (by positivity)).mpr h
