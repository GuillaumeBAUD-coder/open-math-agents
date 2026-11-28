import FormalConjectures.ErdosProblems.«539»

/-! Erdős–Szemerédi lower bound `√n ≪ h(n)`: fixing a nonzero `a ∈ A`, the map
`b ↦ (a / (a, b), b / (a, b))` is injective from `A` into `B × B`, where `B` is the cofactor set,
so `|A| ≤ |B|^2`. -/

open Filter Finset

namespace OMA539

lemma card_le_sq (A : Finset ℕ) :
    #A ≤ #((A ×ˢ A).image fun (p : ℕ × ℕ) ↦ p.1 / p.1.gcd p.2) *
      #((A ×ˢ A).image fun (p : ℕ × ℕ) ↦ p.1 / p.1.gcd p.2) := by
  set B := (A ×ˢ A).image fun (p : ℕ × ℕ) ↦ p.1 / p.1.gcd p.2 with hB
  by_cases h : ∃ a ∈ A, a ≠ 0
  · obtain ⟨a, ha, ha0⟩ := h
    have hmap : ∀ b ∈ A, (a / a.gcd b, b / a.gcd b) ∈ B ×ˢ B := by
      intro b hb
      rw [Finset.mem_product]
      constructor
      · rw [hB, Finset.mem_image]
        exact ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩
      · rw [hB, Finset.mem_image]
        refine ⟨(b, a), Finset.mem_product.mpr ⟨hb, ha⟩, ?_⟩
        simp [Nat.gcd_comm]
    have hinj : Set.InjOn (fun b ↦ (a / a.gcd b, b / a.gcd b)) (A : Set ℕ) := by
      intro b1 _ b2 _ heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨h1, h2⟩ := heq
      have hg : a.gcd b1 = a.gcd b2 :=
        (Nat.div_eq_iff_eq_of_dvd_dvd ha0 (Nat.gcd_dvd_left a b1) (Nat.gcd_dvd_left a b2)).mp h1
      rw [← Nat.div_mul_cancel (Nat.gcd_dvd_right a b1),
        ← Nat.div_mul_cancel (Nat.gcd_dvd_right a b2), h2, hg]
    calc #A ≤ #(B ×ˢ B) := Finset.card_le_card_of_injOn _ hmap hinj
      _ = #B * #B := Finset.card_product _ _
  · simp only [not_exists, not_and, not_not] at h
    have hsub : A ⊆ {0} := fun x hx ↦ by simp [h x hx]
    rcases Finset.subset_singleton_iff.mp hsub with rfl | rfl <;> simp [B]

lemma sqrt_le_threshold (n : ℕ) : Nat.sqrt n ≤ Erdos539.cofactorThreshold n := by
  unfold Erdos539.cofactorThreshold
  apply le_csSup
  · refine ⟨n * n, ?_⟩
    intro m hm
    have h := hm (Finset.range n) (by simp)
    exact h.trans ((Finset.card_image_le).trans (by simp))
  · intro A hA
    have h := card_le_sq A
    rw [hA] at h
    calc Nat.sqrt n ≤ Nat.sqrt (#((A ×ˢ A).image fun (p : ℕ × ℕ) ↦ p.1 / p.1.gcd p.2) *
          #((A ×ˢ A).image fun (p : ℕ × ℕ) ↦ p.1 / p.1.gcd p.2)) := Nat.sqrt_le_sqrt h
      _ = _ := Nat.sqrt_eq _

end OMA539

theorem OMA.solution : type_of% @Erdos539.erdos_539.variants.sq_isBigO := by
  apply Asymptotics.IsBigO.of_bound 2
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hs := OMA539.sqrt_le_threshold n
  have hs1 : 1 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by simpa using hn)
  have hlt : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
  have hreal : Real.sqrt n < (Nat.sqrt n : ℝ) + 1 := by
    rw [Real.sqrt_lt' (by positivity)]
    have : ((n : ℕ) : ℝ) < ((Nat.sqrt n + 1) * (Nat.sqrt n + 1) : ℕ) := by exact_mod_cast hlt
    push_cast at this
    nlinarith
  have hs' : (Nat.sqrt n : ℝ) ≤ (Erdos539.cofactorThreshold n : ℝ) := by exact_mod_cast hs
  have hs1' : (1 : ℝ) ≤ (Nat.sqrt n : ℝ) := by exact_mod_cast hs1
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (by positivity)]
  linarith
