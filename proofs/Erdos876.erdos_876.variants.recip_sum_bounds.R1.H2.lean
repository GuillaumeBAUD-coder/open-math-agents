import OMAReductions.R_Erdos876_erdos_876_variants_recip_sum_bounds_R1

/-! Abbott-type witness for the lower bound `2.064 < R`: the block `{1, 2, 4, 8}`,
`25 + 24 i` (`i < 55`), `36167 + 24 i` (`i < 46`), followed by the doubling tail `T · 2^i`
with `T = 1725553`. Sum-freeness of the block is checked through a subset-sum bitmask; the tail
is sum-free because each `T · 2^i` exceeds the sum of all smaller elements. -/

namespace OMA.E876

open Erdos876

/-- Abbott-type block: `{1, 2, 4, 8}`, then `25 + 24 i` for `i < 55`, then `36167 + 24 i` for
`i < 46`. -/
def Blist : List ℕ :=
  [1, 2, 4, 8] ++ (List.range 55).map (fun i => 25 + 24 * i) ++
    (List.range 46).map (fun i => 36167 + 24 * i)

/-- One more than the sum of the block. -/
def T : ℕ := 1725553

/-- Bit `s` of `mask L` is set whenever `s` is a sum of distinct members of `L`. -/
def mask : List ℕ → ℕ
  | [] => 1
  | a :: L => mask L ||| (mask L <<< a)

theorem mask_spec (L : List ℕ) :
    ∀ C : Finset ℕ, (∀ x ∈ C, x ∈ L) → (mask L).testBit (∑ i ∈ C, i) = true := by
  induction L with
  | nil =>
    intro C hC
    have hC' : C = ∅ := Finset.eq_empty_of_forall_notMem (fun x hx => by simpa using hC x hx)
    subst hC'
    simp [mask]
  | cons a L ih =>
    intro C hC
    rw [mask, Nat.testBit_or]
    by_cases ha : a ∈ C
    · have hsum : ∑ i ∈ C, i = a + ∑ i ∈ C.erase a, i :=
        (Finset.add_sum_erase C (fun i => i) ha).symm
      have h1 := ih (C.erase a) (fun x hx => by
        rcases List.mem_cons.mp (hC x (Finset.mem_of_mem_erase hx)) with h | h
        · exact absurd h (Finset.ne_of_mem_erase hx)
        · exact h)
      rw [hsum, Nat.testBit_shiftLeft]
      simp [h1]
    · have h1 := ih C (fun x hx => by
        rcases List.mem_cons.mp (hC x hx) with h | h
        · exact absurd (h ▸ hx) ha
        · exact h)
      simp [h1]

theorem B_check : ∀ a ∈ Blist, (mask (Blist.filter (fun x => x < a))).testBit a = false := by
  decide +kernel

theorem B_lt : ∀ a ∈ Blist, 0 < a ∧ a < T := by decide +kernel

theorem B_sum : (Blist.map (fun b => b)).sum = T - 1 := by decide +kernel

theorem B_nodup : Blist.Nodup := by decide +kernel

theorem B_val : 2064 * 10 ^ 9 < (Blist.map (fun b => 10 ^ 12 / b)).sum + 2 * 10 ^ 12 / T := by
  decide +kernel

/-- The block followed by the doubling tail `T, 2T, 4T, …`. -/
def A : Set ℕ := (↑Blist.toFinset : Set ℕ) ∪ Set.range (fun i : ℕ => T * 2 ^ i)

theorem T_pos : 0 < T := by decide

theorem tail_inj : Function.Injective (fun i : ℕ => T * 2 ^ i) := by
  intro i j h
  exact Nat.pow_right_injective (le_refl 2) (Nat.eq_of_mul_eq_mul_left T_pos h)

theorem geom (i : ℕ) : ∑ j ∈ Finset.range i, T * 2 ^ j + T = T * 2 ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h : T * (2 ^ i * 2) = T * 2 ^ i + T * 2 ^ i := by ring
    omega

theorem A_sumfree : IsSubsetSumFree A := by
  intro a ha
  rcases ha with ha | ⟨i, rfl⟩
  · have haL : a ∈ Blist := by simpa using ha
    refine ⟨(B_lt a haL).1, ?_⟩
    rintro ⟨C, hC, hsum⟩
    have h := mask_spec (Blist.filter (fun x => x < a)) C (fun x hx => by
      have hx' := hC hx
      rcases hx'.1 with h | ⟨j, rfl⟩
      · exact List.mem_filter.mpr ⟨by simpa using h, by simpa using hx'.2⟩
      · exfalso
        have h1 : T * 2 ^ j < a := hx'.2
        have h2 := (B_lt a haL).2
        have h3 : T ≤ T * 2 ^ j := Nat.le_mul_of_pos_right T (by positivity)
        omega)
    rw [← hsum, B_check a haL] at h
    exact Bool.false_ne_true h
  · refine ⟨Nat.mul_pos T_pos (by positivity), ?_⟩
    rintro ⟨C, hC, hsum⟩
    have hsub : C ⊆ Blist.toFinset ∪ (Finset.range i).image (fun j => T * 2 ^ j) := by
      intro x hx
      have hx' := hC hx
      rcases hx'.1 with h | ⟨j, rfl⟩
      · exact Finset.mem_union_left _ (by simpa using h)
      · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr ?_, rfl⟩)
        have h1 : T * 2 ^ j < T * 2 ^ i := hx'.2
        have h2 : 2 ^ j < 2 ^ i := Nat.lt_of_mul_lt_mul_left h1
        exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h2
    have h1 : ∑ x ∈ C, x ≤ ∑ x ∈ Blist.toFinset ∪ (Finset.range i).image (fun j => T * 2 ^ j), x :=
      Finset.sum_le_sum_of_subset hsub
    have h2 := Finset.sum_union_inter (s₁ := Blist.toFinset)
      (s₂ := (Finset.range i).image (fun j => T * 2 ^ j)) (f := fun x : ℕ => x)
    beta_reduce at h2
    have h3 : ∑ x ∈ Blist.toFinset, x = T - 1 := by
      rw [List.sum_toFinset (fun b => b) B_nodup]
      exact B_sum
    have h4 : ∑ x ∈ (Finset.range i).image (fun j => T * 2 ^ j), x =
        ∑ j ∈ Finset.range i, T * 2 ^ j :=
      Finset.sum_image (fun a _ b _ h => tail_inj h)
    have h5 := geom i
    have hT := T_pos
    have hsum' : T * 2 ^ i = ∑ x ∈ C, x := hsum
    omega

theorem A_infinite : A.Infinite :=
  (Set.infinite_range_of_injective tail_inj).mono Set.subset_union_right

theorem A_hasSum : HasSum (fun a : A => (1 : ℝ) / (a : ℕ))
    (∑ b ∈ Blist.toFinset, (1 : ℝ) / b + 2 / T) := by
  have hdisj : Disjoint (↑Blist.toFinset : Set ℕ) (Set.range (fun i : ℕ => T * 2 ^ i)) := by
    rw [Set.disjoint_left]
    rintro x hx ⟨j, rfl⟩
    have h1 := (B_lt _ (by simpa using hx)).2
    have h3 : T ≤ T * 2 ^ j := Nat.le_mul_of_pos_right T (by positivity)
    omega
  have hB : HasSum ((fun b : ℕ => (1 : ℝ) / b) ∘ ((↑) : (↑Blist.toFinset : Set ℕ) → ℕ))
      (∑ b ∈ Blist.toFinset, (1 : ℝ) / b) := Finset.hasSum Blist.toFinset (fun b : ℕ => (1 : ℝ) / b)
  have hT : HasSum ((fun b : ℕ => (1 : ℝ) / b) ∘ ((↑) : Set.range (fun i : ℕ => T * 2 ^ i) → ℕ))
      (2 / T) := by
    refine (Function.Injective.hasSum_range_iff (α := ℝ) (f := fun b : ℕ => (1 : ℝ) / b)
      tail_inj).mpr ?_
    have h := hasSum_geometric_two' ((2 : ℝ) / T)
    convert h using 1
    funext n
    have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast T_pos.ne'
    simp only [Function.comp_apply]
    push_cast
    field_simp
  exact hB.add_disjoint hdisj hT

theorem floor_le (N b : ℕ) (hb : 0 < b) (hN : 0 < N) :
    ((N / b : ℕ) : ℝ) / N ≤ 1 / b := by
  have h := Nat.cast_div_le (α := ℝ) (m := N) (n := b)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_div_iff₀ hN' hb']
  have := (le_div_iff₀ hb').mp h
  linarith

theorem A_val : (2.064 : ℝ) < ∑ b ∈ Blist.toFinset, (1 : ℝ) / b + 2 / T := by
  have h1 : (∑ b ∈ Blist.toFinset, ((10 ^ 12 / b : ℕ) : ℝ)) / (10 ^ 12 : ℕ) ≤
      ∑ b ∈ Blist.toFinset, (1 : ℝ) / b := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum (fun b hb => ?_)
    exact floor_le _ b (B_lt b (by simpa using hb)).1 (by positivity)
  have h2 : ((2 * 10 ^ 12 / T : ℕ) : ℝ) / (10 ^ 12 : ℕ) ≤ 2 / T := by
    have h := Nat.cast_div_le (α := ℝ) (m := 2 * 10 ^ 12) (n := T)
    have hT0 : (0 : ℝ) < T := by exact_mod_cast T_pos
    rw [div_le_div_iff₀ (by positivity) hT0]
    have := (le_div_iff₀ hT0).mp h
    push_cast at this ⊢
    linarith
  have h3 : ((2064 * 10 ^ 9 : ℕ) : ℝ) <
      ((∑ b ∈ Blist.toFinset, (10 ^ 12 / b) + 2 * 10 ^ 12 / T : ℕ) : ℝ) := by
    have := B_val
    rw [← List.sum_toFinset (fun b => 10 ^ 12 / b) B_nodup] at this
    exact_mod_cast this
  have h4 : (2.064 : ℝ) = ((2064 * 10 ^ 9 : ℕ) : ℝ) / (10 ^ 12 : ℕ) := by norm_num
  rw [h4]
  have h5 : ((2064 * 10 ^ 9 : ℕ) : ℝ) / (10 ^ 12 : ℕ) <
      ((∑ b ∈ Blist.toFinset, (10 ^ 12 / b) + 2 * 10 ^ 12 / T : ℕ) : ℝ) / (10 ^ 12 : ℕ) :=
    div_lt_div_of_pos_right h3 (by positivity)
  have h6 : ((∑ b ∈ Blist.toFinset, (10 ^ 12 / b) + 2 * 10 ^ 12 / T : ℕ) : ℝ) / (10 ^ 12 : ℕ) =
      (∑ b ∈ Blist.toFinset, ((10 ^ 12 / b : ℕ) : ℝ)) / (10 ^ 12 : ℕ) +
        ((2 * 10 ^ 12 / T : ℕ) : ℝ) / (10 ^ 12 : ℕ) := by
    push_cast
    ring
  linarith

theorem lower : ∃ A : Set ℕ, A.Infinite ∧ IsSubsetSumFree A ∧
    ∃ s : ℝ, 2.064 < s ∧ HasSum (fun a : A ↦ (1 : ℝ) / (a : ℕ)) s :=
  ⟨A, A_infinite, A_sumfree, _, A_val, A_hasSum⟩

end OMA.E876

theorem OMA.solution : OMA.R_Erdos876_erdos_876_variants_recip_sum_bounds_R1.H2 :=
  OMA.E876.lower
