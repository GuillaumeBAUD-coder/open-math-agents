import OMAReductions.R_HardyLittlewood_second_hardy_littlewood_conjecture_R1

-- Step HardyLittlewood.second_hardy_littlewood_conjecture.R1.H1
-- Credit: @caa1982

open Finset

private lemma prime_mod_six {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : ¬ 2 ∣ p := by
    intro h
    rcases hp.eq_one_or_self_of_dvd 2 h with h1 | h2
    · omega
    · omega
  have h3 : ¬ 3 ∣ p := by
    intro h
    rcases hp.eq_one_or_self_of_dvd 3 h with h1 | h3
    · omega
    · omega
  omega

private lemma small_xy :
    ∀ x ∈ Finset.Icc 2 3, ∀ y ∈ Finset.Icc 2 26,
      Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y := by
  decide +kernel

private lemma window_coprime6_le :
    ∀ r ∈ Finset.range 6, ∀ y ∈ Finset.Icc 2 26,
      ((Finset.Ioc 0 y).filter (fun j => (r + j) % 6 = 1 ∨ (r + j) % 6 = 5)).card ≤
        Nat.primeCounting y := by
  decide +kernel

private lemma hl_of_le_26 {x y : ℕ} (hx : 2 ≤ x) (hy2 : 2 ≤ y) (hy26 : y ≤ 26) :
    HardyLittlewood.SecondHardyLittlewoodConjectureFor x y := by
  unfold HardyLittlewood.SecondHardyLittlewoodConjectureFor
  by_cases hx3 : x ≤ 3
  · exact small_xy x (Finset.mem_Icc.mpr ⟨hx, hx3⟩) y (Finset.mem_Icc.mpr ⟨hy2, hy26⟩)
  · have hx4 : 4 ≤ x := by omega
    have hsplit : Nat.primeCounting (x + y) =
        Nat.primeCounting x + ((Finset.Ioc x (x + y)).filter Nat.Prime).card := by
      simp only [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
      have hunion : Finset.range (x + 1) ∪ Finset.Ioc x (x + y) = Finset.range (x + y + 1) := by
        ext k
        simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ioc]
        omega
      have hdisj : Disjoint (Finset.range (x + 1)) (Finset.Ioc x (x + y)) := by
        rw [Finset.disjoint_left]
        intro k hk1 hk2
        simp only [Finset.mem_range, Finset.mem_Ioc] at hk1 hk2
        omega
      rw [← hunion, Finset.filter_union, Finset.card_union_of_disjoint
        (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
    have hsub : (Finset.Ioc x (x + y)).filter Nat.Prime ⊆
        (Finset.Ioc x (x + y)).filter (fun k => k % 6 = 1 ∨ k % 6 = 5) := by
      intro p hp
      obtain ⟨hpIoc, hpp⟩ := Finset.mem_filter.mp hp
      have hp5 : 5 ≤ p := by
        have := (Finset.mem_Ioc.mp hpIoc).1
        omega
      exact Finset.mem_filter.mpr ⟨hpIoc, prime_mod_six hpp hp5⟩
    have hbij : ((Finset.Ioc x (x + y)).filter (fun k => k % 6 = 1 ∨ k % 6 = 5)).card =
        ((Finset.Ioc 0 y).filter (fun j => (x % 6 + j) % 6 = 1 ∨ (x % 6 + j) % 6 = 5)).card := by
      refine Finset.card_bij (fun k _ => k - x) ?_ ?_ ?_
      · intro k hk
        obtain ⟨hkIoc, hkmod⟩ := Finset.mem_filter.mp hk
        simp only [Finset.mem_Ioc] at hkIoc
        refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
        have hmod : (x % 6 + (k - x)) % 6 = k % 6 := by omega
        rwa [hmod]
      · intro k₁ hk₁ k₂ hk₂ heq
        have h1 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hk₁).1).1
        have h2 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hk₂).1).1
        omega
      · intro j hj
        obtain ⟨hjIoc, hjmod⟩ := Finset.mem_filter.mp hj
        simp only [Finset.mem_Ioc] at hjIoc
        refine ⟨x + j, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩, by omega⟩
        have hmod : (x + j) % 6 = (x % 6 + j) % 6 := by omega
        rwa [hmod]
    have hwin : ((Finset.Ioc 0 y).filter (fun j => (x % 6 + j) % 6 = 1 ∨ (x % 6 + j) % 6 = 5)).card ≤
        Nat.primeCounting y :=
      window_coprime6_le (x % 6) (Finset.mem_range.mpr (Nat.mod_lt x (by decide))) y
        (Finset.mem_Icc.mpr ⟨hy2, hy26⟩)
    have hcard : ((Finset.Ioc x (x + y)).filter Nat.Prime).card ≤ Nat.primeCounting y :=
      (Finset.card_le_card hsub).trans (hbij ▸ hwin)
    omega

theorem OMA.solution : OMA.R_HardyLittlewood_second_hardy_littlewood_conjecture_R1.H1 := by
  intro x y hx hy hle
  rcases hle with hx26 | hy26
  · have h := hl_of_le_26 hy hx hx26
    unfold HardyLittlewood.SecondHardyLittlewoodConjectureFor at h ⊢
    rw [add_comm x y, add_comm (Nat.primeCounting x)]
    exact h
  · exact hl_of_le_26 hx hy hy26
