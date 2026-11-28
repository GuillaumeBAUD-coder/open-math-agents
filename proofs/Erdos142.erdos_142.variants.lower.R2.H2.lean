import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2

/-!
Refines the packing argument first proved by @Salofe (#5265), shortened
by @weizj99 (#32324), and the ratio proof in #37256. The consolidated
witness pattern also follows @pmcao's shorter proof in #38355.
Choose all block witnesses once. Separation only needs inequalities between
the scale powers; the second and third terms then bound d, and induction
places all terms in the first block.
-/

lemma OMA.scale {i j : ℕ}
    (h : 4 ^ i < 4 * 4 ^ j ∧ 4 ^ j < 4 * 4 ^ i) : i = j := by
  by_contra ne
  rcases Nat.lt_or_gt_of_ne ne with hlt | hlt
  all_goals
    have hp := Nat.pow_le_pow_right (by decide : 0 < 4) hlt
    rw [Nat.pow_succ] at hp
    omega

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2.H2 := by
  intro k hk B hB hf ⟨a,d,hd,h⟩
  choose! j b hb e using h
  have Q {i} (t : i < k) := And.intro (Finset.mem_Icc.1 (hB _ (hb i t))) (e i t)
  have q1 := Q (by omega : 1 < k)
  have q2 := Q (by omega : 2 < k)
  have h12 : j 1 = j 2 := OMA.scale (by omega)
  rw [h12] at q1
  have da : d ≤ a := by omega
  have S i : i < k → j i = j 0 := by
    induction i with
    | zero => simp
    | succ i ih =>
      intro t
      have qi := Q (by omega : i < k)
      have qs := Q t
      have _ := Nat.add_mul i 1 d
      have eq : j i = j (i + 1) := OMA.scale (by omega)
      exact eq.symm.trans (ih (by omega))
  refine hf (j 0) ⟨b 0,d,hd,fun i t => ?_⟩
  have q0 := Q (by omega : 0 < k)
  have qi := Q t
  have hbi := hb i t
  rw [S i t] at *
  rwa [show b 0 + i * d = b i by omega]
