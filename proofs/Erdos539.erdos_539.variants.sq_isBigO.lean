import FormalConjectures.ErdosProblems.«539»

/-! Fix a nonzero element and encode every element by its two reduced cofactors
with respect to that element. Original formalization by @Genbox (#565). -/

open Filter Finset Erdos539

private theorem cofactor_count (A : Finset ℕ) :
    #A ≤ #((A ×ˢ A).image fun (a, b) ↦ a / a.gcd b) ^ 2 := by
  let B := (A ×ˢ A).image fun (a, b) ↦ a / a.gcd b
  by_cases h : ∃ a ∈ A, a ≠ 0
  · obtain ⟨a, ha, ha0⟩ := h
    have mem {x y : ℕ} (hx : x ∈ A) (hy : y ∈ A) : x / x.gcd y ∈ B :=
      mem_image.mpr ⟨(x, y), mk_mem_product hx hy, rfl⟩
    rw [pow_two, ← card_product]
    refine card_le_card_of_injOn (fun b => (a / a.gcd b, b / b.gcd a))
      (fun b hb => mk_mem_product (mem ha hb) (mem hb ha)) ?_
    intro x _ y _ hxy
    have hg := (Nat.div_eq_iff_eq_of_dvd_dvd ha0 (Nat.gcd_dvd_left a x)
      (Nat.gcd_dvd_left a y)).1 (congrArg Prod.fst hxy)
    have hq : x / x.gcd a = y / y.gcd a := congrArg Prod.snd hxy
    calc
      x = (x / x.gcd a) * x.gcd a := (Nat.div_mul_cancel (Nat.gcd_dvd_left x a)).symm
      _ = (y / y.gcd a) * y.gcd a := by rw [hq, Nat.gcd_comm x a, hg, Nat.gcd_comm a y]
      _ = y := Nat.div_mul_cancel (Nat.gcd_dvd_left y a)
  · push Not at h
    have hsub : A ⊆ {0} := fun x hx => by simp [h x hx]
    rcases subset_singleton_iff.mp hsub with rfl | rfl <;> simp

theorem OMA.solution : type_of% @Erdos539.erdos_539.variants.sq_isBigO := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [] with n
  rw [one_mul, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (by positivity)]
  apply Nat.le_of_ceil_le
  apply le_csSup
  · exact ⟨n * n, fun m hm => (hm (range n) (card_range n)).trans
      (card_image_le.trans (by simp))⟩
  · intro A hA
    rw [Nat.ceil_le, Real.sqrt_le_left (by positivity), ← hA]
    exact_mod_cast cofactor_count A
