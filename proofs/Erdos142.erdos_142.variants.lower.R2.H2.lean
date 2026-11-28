import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2

/-!
A shorter proof of the block-packing step, first proved by @Salofe in PR #5265
and previously shortened by @weizj99 in PR #32324.
Points in distinct blocks have ratio greater than two. Applying this to the
second and third progression terms shows that their blocks agree and d ≤ a.
Each consecutive pair then has ratio at most two, so induction keeps every
term in one block, where translation contradicts its progression freeness.
-/

lemma OMA.block {i j x y : Nat}
    (hx : 4 * 4 ^ i < x ∧ x ≤ 5 * 4 ^ i)
    (hy : 4 * 4 ^ j < y ∧ y ≤ 5 * 4 ^ j)
    (h : x ≤ 2 * y ∧ y ≤ 2 * x) : i = j := by
  by_contra ne
  rcases Nat.lt_or_gt_of_ne ne with hlt | hlt
  all_goals
    have hp := Nat.pow_le_pow_right (by decide : 0 < 4) hlt
    rw [Nat.pow_succ] at hp
    omega

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2.H2 := by
  rintro k hk B hB hf ⟨a,d,hd,h⟩
  have bounds {i j b} (hb : b ∈ B j)
      (e : a + i * d = 4 * 4 ^ j + b) :
      4 * 4 ^ j < a + i * d ∧ a + i * d ≤ 5 * 4 ^ j := by
    have := Finset.mem_Icc.mp (hB j hb)
    omega
  obtain ⟨j,b,hb,e⟩ := h 1 (by omega)
  obtain ⟨j',b',hb',e'⟩ := h 2 (by omega)
  have h1 := bounds hb e
  have h2 := bounds hb' e'
  cases OMA.block h1 h2 (by omega)
  have da : d ≤ a := by omega
  have all : ∀ i, i < k → ∃ b, b ∈ B j ∧ a + i * d = 4 * 4 ^ j + b := by
    intro i
    induction i with
    | zero =>
      intro hi
      obtain ⟨l,c,hc,ec⟩ := h 0 hi
      cases OMA.block (bounds hc ec) h1 (by omega)
      exact ⟨c,hc,ec⟩
    | succ i ih =>
      intro hi
      obtain ⟨c,hc,ec⟩ := ih (by omega)
      obtain ⟨l,b,hb,eb⟩ := h (i+1) hi
      cases OMA.block (bounds hc ec) (bounds hb eb) (by simp only [Nat.add_mul, Nat.one_mul]; omega)
      exact ⟨b,hb,eb⟩
  apply hf j
  refine ⟨a - 4 * 4 ^ j,d,hd,?_⟩
  intro i hi
  obtain ⟨b,hb,e⟩ := all i hi
  obtain ⟨b0,hb0,e0⟩ := all 0 (by omega)
  rwa [show a - 4 * 4 ^ j + i * d = b by omega]
