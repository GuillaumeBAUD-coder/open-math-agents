import FormalConjectures.ErdosProblems.«340»

-- Problem: Erdős Problem 340 — third
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/340.lean (declaration Erdos340.erdos_340.variants.third)
-- Credit: @NoahPuckett-IO (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
The greedy Sidon sequence `g` satisfies `g (k + 1) ≤ (k+1)^3 + (k+1)^2 + (k+1) + 1`:
every integer in `[1, g (k + 1))` outside the first `k + 1` terms `A k` was rejected, so
it is of the form `b + c - a` or `(b + c) / 2` with `a, b, c ∈ A k`. Hence
`g k ≤ 4 (k + 1)^3`, which gives at least `N^(1/3) / 4` terms up to `N`.
-/

namespace OMA.E340

open Filter Asymptotics

abbrev A (k : ℕ) : Finset ℕ := (Finset.greedySidon.aux k).1.1

abbrev g (k : ℕ) : ℕ := Finset.greedySidon k

lemma A_sidon (k : ℕ) : IsSidon ((A k : Finset ℕ) : Set ℕ) := (Finset.greedySidon.aux k).1.2

lemma A_zero : A 0 = {1} := rfl

lemma g_zero : g 0 = 1 := rfl

lemma A_succ (k : ℕ) : A (k + 1) = A k ∪ {g (k + 1)} := rfl

lemma one_mem (k : ℕ) : 1 ∈ A k := by
  induction k with
  | zero => simp [A_zero]
  | succ k ih => rw [A_succ]; exact Finset.mem_union_left _ ih

lemma A_ne (k : ℕ) : (A k).Nonempty := ⟨1, one_mem k⟩

lemma g_succ (k : ℕ) :
    g (k + 1) = (Finset.greedySidon.go (A k) (A_sidon k) ((A k).max' (A_ne k) + 1)).1 := by
  have h : g (k + 1) = (Finset.greedySidon.go (A k) (A_sidon k)
      (if h : (A k).Nonempty then (A k).max' h + 1 else (Finset.greedySidon.aux k).2)).1 := rfl
  rw [h, dif_pos (A_ne k)]

lemma g_succ_ge (k : ℕ) : (A k).max' (A_ne k) + 1 ≤ g (k + 1) := by
  rw [g_succ]
  exact (Finset.greedySidon.go (A k) (A_sidon k) ((A k).max' (A_ne k) + 1)).2.1

lemma g_succ_not_mem (k : ℕ) : g (k + 1) ∉ A k := by
  rw [g_succ]
  exact (Finset.greedySidon.go (A k) (A_sidon k) ((A k).max' (A_ne k) + 1)).2.2.1

lemma g_mem (k : ℕ) : g k ∈ A k := by
  cases k with
  | zero => simp [A_zero, g_zero]
  | succ k => rw [A_succ]; exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

lemma le_g (k : ℕ) : ∀ a ∈ A k, a ≤ g k := by
  induction k with
  | zero => intro a ha; simp [A_zero] at ha; simp [ha, g_zero]
  | succ k ih =>
    intro a ha
    rw [A_succ, Finset.mem_union, Finset.mem_singleton] at ha
    rcases ha with ha | ha
    · have h1 := Finset.le_max' (A k) a ha
      have h2 := g_succ_ge k
      omega
    · omega

lemma max_eq (k : ℕ) : (A k).max' (A_ne k) = g k :=
  le_antisymm (Finset.max'_le _ _ _ (le_g k)) (Finset.le_max' _ _ (g_mem k))

lemma g_lt_succ (k : ℕ) : g k < g (k + 1) := by
  have := g_succ_ge k
  rw [max_eq] at this
  omega

lemma g_strictMono : StrictMono g := strictMono_nat_of_lt_succ g_lt_succ

lemma card_A (k : ℕ) : (A k).card = k + 1 := by
  induction k with
  | zero => simp [A_zero]
  | succ k ih =>
    rw [A_succ, Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.2 (g_succ_not_mem k)),
      ih, Finset.card_singleton]

lemma go_min {B : Finset ℕ} (hB : IsSidon (B : Set ℕ)) (hne : B.Nonempty) (m x : ℕ)
    (hmx : m ≤ x) (hx : x < (Finset.greedySidon.go B hB m).1) (hxB : x ∉ B) :
    ¬ IsSidon ((B ∪ {x} : Finset ℕ) : Set ℕ) := by
  have hex : ∃ m', m' ≥ m ∧ m' ∉ B ∧ IsSidon (↑(B ∪ {m'}) : Set ℕ) := by
    simpa [and_assoc] using Finset.IsSidon.exists_insert_ge hne hB m
  have hgo : (Finset.greedySidon.go B hB m).1 = Nat.find hex := by
    simp only [Finset.greedySidon.go, dif_pos hne]
  intro hS
  rw [hgo] at hx
  exact Nat.find_min hex hx ⟨hmx, hxB, hS⟩

/-- Every rejected number below `g (k + 1)` stays rejected for `A k`. -/
lemma rejected (k : ℕ) : ∀ x, 1 ≤ x → x < g (k + 1) → x ∉ A k →
    ¬ IsSidon ((A k ∪ {x} : Finset ℕ) : Set ℕ) := by
  induction k with
  | zero =>
    intro x hx1 hx hxA
    have hx2 : (A 0).max' (A_ne 0) + 1 ≤ x := by
      rw [max_eq, g_zero]
      have : x ≠ 1 := fun h => hxA (h ▸ one_mem 0)
      omega
    exact go_min (A_sidon 0) (A_ne 0) _ x hx2 (by rw [← g_succ]; exact hx) hxA
  | succ k ih =>
    intro x hx1 hx hxA
    by_cases hbig : g (k + 1) + 1 ≤ x
    · have hx2 : (A (k + 1)).max' (A_ne (k + 1)) + 1 ≤ x := by rw [max_eq]; exact hbig
      exact go_min (A_sidon (k + 1)) (A_ne (k + 1)) _ x hx2 (by rw [← g_succ]; exact hx) hxA
    · have hne : x ≠ g (k + 1) := fun h => hxA (h ▸ g_mem (k + 1))
      have hlt : x < g (k + 1) := by omega
      have hxA' : x ∉ A k := fun h => hxA (by rw [A_succ]; exact Finset.mem_union_left _ h)
      intro hS
      apply ih x hx1 hlt hxA'
      apply Set.IsSidon.subset hS
      intro y hy
      simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union, Set.mem_singleton_iff,
        Finset.mem_coe] at hy ⊢
      rcases hy with hy | hy
      · left; rw [A_succ]; exact Finset.mem_union_left _ hy
      · right; exact hy

/-- The numbers that cannot be added to `B`. -/
def cover (B : Finset ℕ) : Finset ℕ :=
  (B ×ˢ B ×ˢ B).image (fun t => t.2.1 + t.2.2 - t.1) ∪ (B ×ˢ B).image (fun t => (t.1 + t.2) / 2)

lemma card_cover (B : Finset ℕ) : (cover B).card ≤ B.card ^ 3 + B.card ^ 2 := by
  unfold cover
  refine (Finset.card_union_le _ _).trans (add_le_add ?_ ?_)
  · refine Finset.card_image_le.trans ?_
    simp [Finset.card_product, pow_succ, mul_assoc]
  · refine Finset.card_image_le.trans ?_
    simp [Finset.card_product, pow_two]

lemma mem_cover {B : Finset ℕ} (hB : IsSidon (B : Set ℕ)) {x : ℕ} (hx : x ∉ B)
    (hns : ¬ IsSidon ((B ∪ {x} : Finset ℕ) : Set ℕ)) : x ∈ cover B := by
  by_contra hc
  have hc1 : ∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, x + a ≠ b + c := by
    intro a ha b hb c hc' h
    apply hc
    unfold cover
    apply Finset.mem_union_left
    exact Finset.mem_image.2 ⟨(a, b, c), by simp [ha, hb, hc'], by dsimp only; omega⟩
  have hc2 : ∀ b ∈ B, ∀ c ∈ B, x + x ≠ b + c := by
    intro b hb c hc' h
    apply hc
    unfold cover
    apply Finset.mem_union_right
    exact Finset.mem_image.2 ⟨(b, c), by simp [hb, hc'], by dsimp only; omega⟩
  apply hns
  intro i1 hi1 j1 hj1 i2 hi2 j2 hj2 heq
  simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union, Set.mem_singleton_iff,
    Finset.mem_coe] at hi1 hj1 hi2 hj2
  rcases hi1 with h1 | h1 <;> rcases hj1 with h2 | h2 <;> rcases hi2 with h3 | h3 <;>
    rcases hj2 with h4 | h4 <;>
    first
    | exact hB i1 h1 j1 h2 i2 h3 j2 h4 heq
    | exact Or.inl ⟨by omega, by omega⟩
    | exact Or.inr ⟨by omega, by omega⟩
    | exact absurd (by omega : x + i2 = j1 + j2) (hc1 i2 h3 j1 h2 j2 h4)
    | exact absurd (by omega : x + i1 = j1 + j2) (hc1 i1 h1 j1 h2 j2 h4)
    | exact absurd (by omega : x + j2 = i1 + i2) (hc1 j2 h4 i1 h1 i2 h3)
    | exact absurd (by omega : x + j1 = i1 + i2) (hc1 j1 h2 i1 h1 i2 h3)
    | exact absurd (by omega : x + x = j1 + j2) (hc2 j1 h2 j2 h4)
    | exact absurd (by omega : x + x = i1 + i2) (hc2 i1 h1 i2 h3)
    | exact absurd ((show i1 = x by omega) ▸ h1) hx
    | exact absurd ((show j1 = x by omega) ▸ h2) hx
    | exact absurd ((show i2 = x by omega) ▸ h3) hx
    | exact absurd ((show j2 = x by omega) ▸ h4) hx

lemma g_succ_le (k : ℕ) : g (k + 1) ≤ (k + 1) ^ 3 + (k + 1) ^ 2 + (k + 1) + 1 := by
  have hsub : Finset.Ico 1 (g (k + 1)) ⊆ A k ∪ cover (A k) := by
    intro x hx
    rw [Finset.mem_Ico] at hx
    by_cases hxA : x ∈ A k
    · exact Finset.mem_union_left _ hxA
    · exact Finset.mem_union_right _
        (mem_cover (A_sidon k) hxA (rejected k x hx.1 hx.2 hxA))
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (A k) (cover (A k))
  have h3 := card_cover (A k)
  rw [card_A] at h2 h3
  rw [Nat.card_Ico] at h1
  omega

lemma g_le (k : ℕ) : g k ≤ 4 * (k + 1) ^ 3 := by
  cases k with
  | zero => simp [g_zero]
  | succ k =>
    have h := g_succ_le k
    have hm : 1 ≤ k + 1 := by omega
    have e1 : (k + 1) ^ 2 ≤ (k + 1) ^ 3 := Nat.pow_le_pow_right hm (by norm_num)
    have e2 : (k + 1) ≤ (k + 1) ^ 3 := by
      simpa using Nat.pow_le_pow_right hm (by norm_num : 1 ≤ 3)
    have e3 : 1 ≤ (k + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    have e4 : (k + 1) ^ 3 ≤ (k + 1 + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega

lemma one_le_g (k : ℕ) : 1 ≤ g k := by
  have := g_strictMono.monotone (Nat.zero_le k)
  rw [g_zero] at this
  exact this

lemma count_bound (n : ℕ) :
    n < 4 * ((Set.range g ∩ Set.Icc 1 n).ncard + 1) ^ 3 := by
  set c := (Set.range g ∩ Set.Icc 1 n).ncard with hc
  by_contra h
  push Not at h
  have hsub : (((Finset.range (c + 1)).image g : Finset ℕ) : Set ℕ) ⊆
      Set.range g ∩ Set.Icc 1 n := by
    intro y hy
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    refine ⟨⟨i, rfl⟩, one_le_g i, ?_⟩
    have := g_strictMono.monotone (show i ≤ c by omega)
    have := g_le c
    omega
  have hfin : (Set.range g ∩ Set.Icc 1 n).Finite := (Set.finite_Icc 1 n).subset Set.inter_subset_right
  have hle := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ g_strictMono.injective,
    Finset.card_range, ← hc] at hle
  omega

lemma count_pos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ (Set.range g ∩ Set.Icc 1 n).ncard := by
  have hfin : (Set.range g ∩ Set.Icc 1 n).Finite := (Set.finite_Icc 1 n).subset Set.inter_subset_right
  have hmem : 1 ∈ Set.range g ∩ Set.Icc 1 n := ⟨⟨0, g_zero⟩, le_refl 1, hn⟩
  exact Nat.one_le_iff_ne_zero.2 ((Set.ncard_pos hfin).2 ⟨1, hmem⟩).ne'

end OMA.E340

open Filter Asymptotics OMA.E340 in
theorem OMA.solution : type_of% @Erdos340.erdos_340.variants.third := by
  intro ε hε
  refine IsBigO.of_bound 4 (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  set c := (Set.range Finset.greedySidon ∩ Set.Icc 1 n).ncard with hc
  have hb : n < 4 * (c + 1) ^ 3 := count_bound n
  have hpos : 1 ≤ c := count_pos n hn
  have hnat : n ≤ (4 * c) ^ 3 := by
    have e : (c + 1) ^ 3 ≤ (2 * c) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have e2 : 4 * (2 * c) ^ 3 ≤ (4 * c) ^ 3 := by ring_nf; omega
    omega
  have hreal : (n : ℝ) ≤ ((4 * c : ℕ) : ℝ) ^ 3 := by exact_mod_cast hnat
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _),
    Real.norm_of_nonneg (Nat.cast_nonneg _)]
  calc (n : ℝ) ^ ((1 : ℝ) / 3) ≤ (((4 * c : ℕ) : ℝ) ^ 3) ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow (Nat.cast_nonneg n) hreal (by norm_num)
    _ = ((4 * c : ℕ) : ℝ) := by
        rw [show (1 : ℝ) / 3 = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
        exact Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) (by norm_num)
    _ = 4 * (c : ℝ) := by push_cast; ring
