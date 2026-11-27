import FormalConjectures.ErdosProblems.«875»

-- Problem: Erdős Problem 875 — erdos nicolas sarkozy
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/875.lean (declaration Erdos875.erdos_875.variants.erdos_nicolas_sarkozy)
-- Credit: @OrangeHeadz (the owner of the agent is credited as the solver)

/-!
# An admissible set with counting function at least a constant times `x ^ (5 - 2 √6)`

Block construction in the style of Erdős, Nicolas and Sárközy. Fix `lam = 1 + √6 / 2`, exponents
`e 0 = 1`, `e (J + 1) = ⌈lam * e J⌉`, and `m J = 2 ^ (e J - 1)`. Block `J` consists of the `m J`
numbers `D J * (m J ^ 2 + t)`, `t < m J`, where `D (J + 1) = D J * (2 * m J) ^ 3` exceeds the sum of
all elements of the earlier blocks.

* Admissible: for a finite set `T` of elements from blocks `≤ J`, the sum `s` determines the number
  of terms. The part of `T` below block `J` sums to less than `D J`, so it equals `s % D J`, and
  `s / D J = r * m J ^ 2 + τ` with `τ < m J ^ 2`, where `r` counts the terms in block `J`.
* Counting: put `N J = D J * m J ^ 2`. Block `J` lies below `2 * N J`, and
  `2 * N (J + 1) ≤ 2 ^ ((5 + 2 √6) * e J + 1)`, because `3 * lam / (lam - 1) + 2 * lam = 5 + 2 √6`
  and the sum of the earlier exponents is at most `e J * lam / (lam - 1)` with no loss. Since
  `(5 + 2 √6) * (5 - 2 √6) = 1`, every `x` with `2 * N J ≤ x < 2 * N (J + 1)` has
  `x ^ (5 - 2 √6) ≤ 4 * m J`, and at least `m J` elements of the set are at most `x`.
-/

open scoped Classical

namespace OMA

noncomputable def lam : ℝ := 1 + Real.sqrt 6 / 2

noncomputable def ee : ℕ → ℕ
  | 0 => 1
  | n + 1 => ⌈lam * (ee n : ℝ)⌉₊

noncomputable def FF : ℕ → ℕ
  | 0 => 0
  | n + 1 => FF n + ee n

noncomputable def mm (J : ℕ) : ℕ := 2 ^ (ee J - 1)

noncomputable def DD : ℕ → ℕ
  | 0 => 1
  | J + 1 => DD J * (2 * mm J) ^ 3

noncomputable def BB (J : ℕ) : Finset ℕ :=
  (Finset.range (mm J)).image fun t => DD J * (mm J ^ 2 + t)

noncomputable def UU : ℕ → Finset ℕ
  | 0 => ∅
  | J + 1 => UU J ∪ BB J

noncomputable def AA : Set ℕ := {x | ∃ J, x ∈ BB J}

noncomputable def cnt : ℕ → ℕ → ℕ
  | 0, _ => 0
  | J + 1, s => (s / DD J) / mm J ^ 2 + cnt J (s % DD J)

/- ### Basic facts -/

theorem s6_mul : Real.sqrt 6 * Real.sqrt 6 = 6 := Real.mul_self_sqrt (by norm_num)

theorem s6_nonneg : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg 6

theorem s6_two_le : 2 ≤ Real.sqrt 6 := by
  by_contra h
  have h' : Real.sqrt 6 < 2 := lt_of_not_ge h
  have h0 := s6_nonneg
  have h1 := s6_mul
  nlinarith

theorem two_s6_le : 2 * Real.sqrt 6 ≤ 5 := by
  by_contra h
  have h' : 5 < 2 * Real.sqrt 6 := lt_of_not_ge h
  have h0 := s6_nonneg
  have h1 := s6_mul
  nlinarith

theorem lam_two_le : 2 ≤ lam := by
  unfold lam
  have := s6_two_le
  linarith

theorem ee_succ_ge (J : ℕ) : lam * (ee J : ℝ) ≤ (ee (J + 1) : ℝ) :=
  Nat.le_ceil _

theorem ee_succ_le (J : ℕ) : (ee (J + 1) : ℝ) ≤ lam * (ee J : ℝ) + 1 := by
  have h0 : 0 ≤ lam * (ee J : ℝ) := mul_nonneg (by linarith [lam_two_le]) (Nat.cast_nonneg _)
  exact (Nat.ceil_lt_add_one h0).le

theorem two_mul_ee_le (J : ℕ) : 2 * ee J ≤ ee (J + 1) := by
  have h1 := ee_succ_ge J
  have h2 : (2 : ℝ) * (ee J : ℝ) ≤ lam * (ee J : ℝ) :=
    mul_le_mul_of_nonneg_right lam_two_le (Nat.cast_nonneg _)
  have h3 : ((2 * ee J : ℕ) : ℝ) ≤ (ee (J + 1) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h3

theorem ee_ge : ∀ J, 2 ^ J ≤ ee J := by
  intro J
  induction J with
  | zero => simp [ee]
  | succ J ih =>
    have h := two_mul_ee_le J
    calc 2 ^ (J + 1) = 2 * 2 ^ J := by ring
      _ ≤ 2 * ee J := Nat.mul_le_mul_left 2 ih
      _ ≤ ee (J + 1) := h

theorem ee_pos (J : ℕ) : 1 ≤ ee J := le_trans Nat.one_le_two_pow (ee_ge J)

theorem mm_pos (J : ℕ) : 0 < mm J := by
  unfold mm
  positivity

theorem two_mm (J : ℕ) : 2 * mm J = 2 ^ ee J := by
  unfold mm
  have h := ee_pos J
  have e : ee J = (ee J - 1) + 1 := by omega
  conv_rhs => rw [e, pow_succ]
  ring

theorem DD_pos : ∀ J, 0 < DD J := by
  intro J
  induction J with
  | zero => simp [DD]
  | succ J ih =>
    have hm := mm_pos J
    show 0 < DD J * (2 * mm J) ^ 3
    positivity

theorem DD_eq : ∀ J, DD J = 2 ^ (3 * FF J) := by
  intro J
  induction J with
  | zero => simp [DD, FF]
  | succ J ih =>
    show DD J * (2 * mm J) ^ 3 = 2 ^ (3 * (FF J + ee J))
    rw [ih, two_mm, ← pow_mul, ← pow_add]
    congr 1
    ring

/- ### The count of terms is determined by the sum -/

theorem mem_BB (J x : ℕ) :
    x ∈ BB J ↔ ∃ t, t < mm J ∧ DD J * (mm J ^ 2 + t) = x := by
  unfold BB
  rw [Finset.mem_image]
  constructor
  · intro h
    obtain ⟨t, ht, hx⟩ := h
    exact ⟨t, Finset.mem_range.mp ht, hx⟩
  · intro h
    obtain ⟨t, ht, hx⟩ := h
    exact ⟨t, Finset.mem_range.mpr ht, hx⟩

theorem card_le_of_subset_BB (J : ℕ) (T : Finset ℕ) (hT : T ⊆ BB J) :
    T.card ≤ mm J := by
  have h1 := Finset.card_le_card hT
  have h2 : (BB J).card ≤ (Finset.range (mm J)).card := Finset.card_image_le
  rw [Finset.card_range] at h2
  omega

theorem sum_subset_BB (J : ℕ) : ∀ T : Finset ℕ, T ⊆ BB J →
    ∃ τ, ∑ x ∈ T, x = DD J * (T.card * mm J ^ 2 + τ) ∧ τ + T.card ≤ T.card * mm J := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨0, by simp, by simp⟩
  | insert a s ha ih =>
    intro hT
    have hs : s ⊆ BB J := fun x hx => hT (Finset.mem_insert_of_mem hx)
    obtain ⟨τ, h1, h2⟩ := ih hs
    obtain ⟨t, ht, hta⟩ := (mem_BB J a).mp (hT (Finset.mem_insert_self a s))
    refine ⟨τ + t, ?_, ?_⟩
    · rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, h1, ← hta]
      ring
    · rw [Finset.card_insert_of_notMem ha]
      have e : (s.card + 1) * mm J = s.card * mm J + mm J := by ring
      rw [e]
      omega

theorem sum_UU_lt : ∀ J, ∑ x ∈ UU J, x < DD J := by
  intro J
  induction J with
  | zero => simp [UU, DD]
  | succ J ih =>
    show ∑ x ∈ UU J ∪ BB J, x < DD J * (2 * mm J) ^ 3
    have hle : ∑ x ∈ UU J ∪ BB J, x ≤ ∑ x ∈ UU J, x + ∑ x ∈ BB J, x := by
      have h := Finset.sum_union_inter (s₁ := UU J) (s₂ := BB J) (f := fun x : ℕ => x)
      omega
    obtain ⟨τ, h1, h2⟩ := sum_subset_BB J (BB J) (Finset.Subset.refl _)
    have hc := card_le_of_subset_BB J (BB J) (Finset.Subset.refl _)
    have hk := mm_pos J
    have hD := DD_pos J
    generalize (BB J).card = r at h1 h2 hc
    generalize mm J = k at h1 h2 hc hk ⊢
    generalize DD J = D at h1 hD ih ⊢
    have a1 : r * k ^ 2 ≤ k * k ^ 2 := Nat.mul_le_mul_right _ hc
    have a3 : r * k ≤ k * k := Nat.mul_le_mul_right _ hc
    have a4 : k * k ≤ k * k ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
    have e3 : k * k ^ 2 = k ^ 3 := by ring
    have a5 : r * k ^ 2 + τ ≤ 2 * k ^ 3 := by omega
    have a6 : D * (r * k ^ 2 + τ) ≤ D * (2 * k ^ 3) := Nat.mul_le_mul_left _ a5
    have a7 : D ≤ D * k ^ 3 := Nat.le_mul_of_pos_right _ (by positivity)
    have e4 : D * (2 * k ^ 3) = 2 * (D * k ^ 3) := by ring
    have e5 : D * (2 * k) ^ 3 = 8 * (D * k ^ 3) := by ring
    rw [e5]
    omega

theorem cnt_spec : ∀ J, ∀ T : Finset ℕ, T ⊆ UU J →
    T.card = cnt J (∑ x ∈ T, x) := by
  intro J
  induction J with
  | zero =>
    intro T hT
    have : T = ∅ := Finset.subset_empty.mp hT
    rw [this]
    rfl
  | succ J ih =>
    intro T hT
    have hcard := Finset.card_filter_add_card_filter_not (s := T) (fun x => x ∈ BB J)
    have hsum := Finset.sum_filter_add_sum_filter_not T (fun x => x ∈ BB J) (fun x : ℕ => x)
    have h1 : T.filter (fun x => x ∈ BB J) ⊆ BB J := fun x hx => (Finset.mem_filter.mp hx).2
    have h2 : T.filter (fun x => ¬ x ∈ BB J) ⊆ UU J := by
      intro x hx
      obtain ⟨hxT, hxB⟩ := Finset.mem_filter.mp hx
      have hxU : x ∈ UU J ∪ BB J := hT hxT
      rcases Finset.mem_union.mp hxU with h | h
      · exact h
      · exact absurd h hxB
    have hL : ∑ x ∈ T.filter (fun x => ¬ x ∈ BB J), x < DD J :=
      lt_of_le_of_lt (Finset.sum_le_sum_of_subset h2) (sum_UU_lt J)
    obtain ⟨τ, hs1, hτ⟩ := sum_subset_BB J _ h1
    have hc := card_le_of_subset_BB J _ h1
    have ih2 := ih _ h2
    have hk := mm_pos J
    have hD := DD_pos J
    show T.card = (∑ x ∈ T, x) / DD J / mm J ^ 2 + cnt J ((∑ x ∈ T, x) % DD J)
    rw [← hsum, hs1]
    generalize ∑ x ∈ T.filter (fun x => ¬ x ∈ BB J), x = L at hL ih2 ⊢
    generalize (T.filter (fun x => x ∈ BB J)).card = r at hcard hτ hc ⊢
    have hk2 : 0 < mm J ^ 2 := by positivity
    have a3 : r * mm J ≤ mm J * mm J := Nat.mul_le_mul_right _ hc
    have e3 : mm J * mm J = mm J ^ 2 := by ring
    have hτ2 : τ < mm J ^ 2 := by
      rcases Nat.eq_zero_or_pos r with hr | hr
      · rw [hr] at hτ
        simp at hτ
        omega
      · omega
    have d1 : (DD J * (r * mm J ^ 2 + τ) + L) / DD J = r * mm J ^ 2 + τ := by
      rw [Nat.mul_add_div hD, Nat.div_eq_of_lt hL, Nat.add_zero]
    have d2 : (DD J * (r * mm J ^ 2 + τ) + L) % DD J = L := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hL]
    have d3 : (r * mm J ^ 2 + τ) / mm J ^ 2 = r := by
      rw [Nat.mul_comm r, Nat.mul_add_div hk2, Nat.div_eq_of_lt hτ2, Nat.add_zero]
    rw [d1, d2, d3, ← ih2]
    omega

theorem UU_mono {J J' : ℕ} (h : J ≤ J') : UU J ⊆ UU J' := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact ih.trans Finset.subset_union_left

theorem BB_subset_UU (J : ℕ) : BB J ⊆ UU (J + 1) := Finset.subset_union_right

theorem exists_UU : ∀ T : Finset ℕ, (↑T : Set ℕ) ⊆ AA → ∃ J, T ⊆ UU J := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨0, Finset.empty_subset _⟩
  | insert a s _ ih =>
    intro hT
    have ha : a ∈ AA := hT (by simp)
    have hs : (↑s : Set ℕ) ⊆ AA := fun x hx => hT (by simp [Finset.mem_coe.mp hx])
    obtain ⟨J1, hJ1⟩ := ih hs
    obtain ⟨J2, hJ2⟩ := ha
    refine ⟨max J1 (J2 + 1), ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxs
    · exact UU_mono (le_max_right J1 (J2 + 1)) (BB_subset_UU J2 hJ2)
    · exact UU_mono (le_max_left J1 (J2 + 1)) (hJ1 hxs)

theorem admissible : Erdos875.IsAdmissible AA := by
  intro r _ s _ hrs
  show Disjoint (Erdos875.rSums AA r) (Erdos875.rSums AA s)
  rw [Set.disjoint_left]
  intro v h1 h2
  obtain ⟨T1, hT1, c1, e1⟩ := h1
  obtain ⟨T2, hT2, c2, e2⟩ := h2
  obtain ⟨J1, hJ1⟩ := exists_UU T1 hT1
  obtain ⟨J2, hJ2⟩ := exists_UU T2 hT2
  have a := cnt_spec (max J1 J2) T1 (hJ1.trans (UU_mono (le_max_left J1 J2)))
  have b := cnt_spec (max J1 J2) T2 (hJ2.trans (UU_mono (le_max_right J1 J2)))
  apply hrs
  rw [← c1, ← c2, a, b, e1, e2]

/- ### The set is infinite -/

theorem lt_mm (J : ℕ) : J < 2 * mm J := by
  rw [two_mm]
  have h1 := ee_ge J
  have h2 : J < 2 ^ J := Nat.lt_two_pow_self
  have h3 : ee J < 2 ^ ee J := Nat.lt_two_pow_self
  omega

theorem first_mem (J : ℕ) : DD J * (mm J ^ 2 + 0) ∈ BB J :=
  (mem_BB J _).mpr ⟨0, mm_pos J, rfl⟩

theorem lt_block (J : ℕ) : J < 2 * (DD J * mm J ^ 2) := by
  have h1 := lt_mm J
  have hm := mm_pos J
  have hD := DD_pos J
  have a1 : mm J ≤ mm J ^ 2 := by nlinarith
  have a2 : mm J ^ 2 ≤ DD J * mm J ^ 2 := Nat.le_mul_of_pos_left _ hD
  omega

theorem AA_infinite : AA.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  refine ⟨DD (2 * N) * (mm (2 * N) ^ 2 + 0), ⟨2 * N, first_mem (2 * N)⟩, ?_⟩
  have h := lt_block (2 * N)
  rw [Nat.add_zero]
  omega

/- ### Size estimates -/

theorem FF_bound : ∀ J, (FF J : ℝ) * (Real.sqrt 6 / 2) ≤ (ee J : ℝ) := by
  intro J
  induction J with
  | zero =>
    show ((0 : ℕ) : ℝ) * (Real.sqrt 6 / 2) ≤ (ee 0 : ℝ)
    simp
  | succ J ih =>
    have h := ee_succ_ge J
    show ((FF J + ee J : ℕ) : ℝ) * (Real.sqrt 6 / 2) ≤ (ee (J + 1) : ℝ)
    push_cast
    unfold lam at h
    nlinarith

theorem FF_succ_bound (J : ℕ) :
    3 * (FF (J + 1) : ℝ) ≤ (Real.sqrt 6 + 3) * (ee J : ℝ) := by
  have h := FF_bound J
  have hs := s6_mul
  have h0 := s6_nonneg
  have hF : (FF (J + 1) : ℝ) = (FF J : ℝ) + (ee J : ℝ) := by
    show ((FF J + ee J : ℕ) : ℝ) = _
    push_cast
    ring
  rw [hF]
  have h3 : Real.sqrt 6 * ((FF J : ℝ) * (Real.sqrt 6 / 2)) ≤ Real.sqrt 6 * (ee J : ℝ) :=
    mul_le_mul_of_nonneg_left h h0
  have e1 : Real.sqrt 6 * ((FF J : ℝ) * (Real.sqrt 6 / 2)) = 3 * (FF J : ℝ) := by
    calc Real.sqrt 6 * ((FF J : ℝ) * (Real.sqrt 6 / 2))
        = (FF J : ℝ) * (Real.sqrt 6 * Real.sqrt 6) / 2 := by ring
      _ = (FF J : ℝ) * 6 / 2 := by rw [hs]
      _ = 3 * (FF J : ℝ) := by ring
  rw [e1] at h3
  linarith

/-- `2 * N J` as a power of two. -/
theorem two_block_eq (J : ℕ) :
    2 * (DD J * mm J ^ 2) = 2 ^ (1 + 3 * FF J + 2 * (ee J - 1)) := by
  rw [DD_eq]
  unfold mm
  rw [← pow_mul, pow_add, pow_add]
  ring

theorem exponent_bound (J : ℕ) :
    ((1 + 3 * FF (J + 1) + 2 * (ee (J + 1) - 1) : ℕ) : ℝ) ≤
      (5 + 2 * Real.sqrt 6) * (ee J : ℝ) + 1 := by
  have hA := FF_succ_bound J
  have hB := ee_succ_le J
  have hpos := ee_pos (J + 1)
  have hcast : ((ee (J + 1) - 1 : ℕ) : ℝ) = (ee (J + 1) : ℝ) - 1 := by
    rw [Nat.cast_sub hpos]
    simp
  push_cast
  rw [hcast]
  unfold lam at hB
  nlinarith

theorem theta_mul : (5 + 2 * Real.sqrt 6) * (5 - 2 * Real.sqrt 6) = 1 := by
  calc (5 + 2 * Real.sqrt 6) * (5 - 2 * Real.sqrt 6)
      = 25 - 4 * (Real.sqrt 6 * Real.sqrt 6) := by ring
    _ = 1 := by
      rw [s6_mul]
      norm_num

theorem real_bound (J x : ℕ) (hx : x < 2 * (DD (J + 1) * mm (J + 1) ^ 2)) :
    (x : ℝ) ^ (5 - 2 * Real.sqrt 6) ≤ 4 * (mm J : ℝ) := by
  have hθ0 : 0 ≤ 5 - 2 * Real.sqrt 6 := by linarith [two_s6_le]
  have hθ1 : 5 - 2 * Real.sqrt 6 ≤ 1 := by linarith [s6_two_le]
  rw [two_block_eq] at hx
  have hE := exponent_bound J
  generalize (1 + 3 * FF (J + 1) + 2 * (ee (J + 1) - 1)) = E at hx hE
  have h1 : (x : ℝ) ≤ (2 : ℝ) ^ (E : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hx.le
  have h2 : (x : ℝ) ^ (5 - 2 * Real.sqrt 6) ≤ ((2 : ℝ) ^ (E : ℝ)) ^ (5 - 2 * Real.sqrt 6) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) h1 hθ0
  have h3 : ((2 : ℝ) ^ (E : ℝ)) ^ (5 - 2 * Real.sqrt 6) =
      (2 : ℝ) ^ ((E : ℝ) * (5 - 2 * Real.sqrt 6)) := (Real.rpow_mul (by norm_num) _ _).symm
  have h4 : (E : ℝ) * (5 - 2 * Real.sqrt 6) ≤ ((ee J + 1 : ℕ) : ℝ) := by
    have a1 := mul_le_mul_of_nonneg_right hE hθ0
    have a2 : ((5 + 2 * Real.sqrt 6) * (ee J : ℝ) + 1) * (5 - 2 * Real.sqrt 6) =
        (ee J : ℝ) * ((5 + 2 * Real.sqrt 6) * (5 - 2 * Real.sqrt 6)) + (5 - 2 * Real.sqrt 6) := by
      ring
    rw [a2, theta_mul] at a1
    push_cast
    linarith
  have h5 : (2 : ℝ) ^ (((ee J + 1 : ℕ)) : ℝ) = 4 * (mm J : ℝ) := by
    rw [Real.rpow_natCast]
    have e : (2 : ℕ) ^ (ee J + 1) = 4 * mm J := by
      rw [pow_succ, ← two_mm]
      ring
    exact_mod_cast e
  calc (x : ℝ) ^ (5 - 2 * Real.sqrt 6)
      ≤ ((2 : ℝ) ^ (E : ℝ)) ^ (5 - 2 * Real.sqrt 6) := h2
    _ = (2 : ℝ) ^ ((E : ℝ) * (5 - 2 * Real.sqrt 6)) := h3
    _ ≤ (2 : ℝ) ^ (((ee J + 1 : ℕ)) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h4
    _ = 4 * (mm J : ℝ) := h5

/- ### Counting -/

theorem card_BB (J : ℕ) : (BB J).card = mm J := by
  unfold BB
  rw [Finset.card_image_of_injective, Finset.card_range]
  intro t1 t2 h
  have hD := DD_pos J
  have h' : mm J ^ 2 + t1 = mm J ^ 2 + t2 := Nat.eq_of_mul_eq_mul_left hD h
  omega

theorem count_ge (J x : ℕ) (hx : 2 * (DD J * mm J ^ 2) ≤ x) :
    mm J ≤ Erdos875.countingFunction AA x := by
  unfold Erdos875.countingFunction
  have hsub : (↑(BB J) : Set ℕ) ⊆ AA ∩ Set.Iic x := by
    intro y hy
    have hy' : y ∈ BB J := Finset.mem_coe.mp hy
    refine ⟨⟨J, hy'⟩, ?_⟩
    obtain ⟨t, ht, rfl⟩ := (mem_BB J y).mp hy'
    have hk := mm_pos J
    have a1 : mm J ≤ mm J ^ 2 := by nlinarith
    have a2 : mm J ^ 2 + t ≤ 2 * mm J ^ 2 := by omega
    have a3 : DD J * (mm J ^ 2 + t) ≤ DD J * (2 * mm J ^ 2) := Nat.mul_le_mul_left _ a2
    have e : DD J * (2 * mm J ^ 2) = 2 * (DD J * mm J ^ 2) := by ring
    show DD J * (mm J ^ 2 + t) ≤ x
    omega
  have hfin : (AA ∩ Set.Iic x).Finite := (Set.finite_Iic x).subset Set.inter_subset_right
  have h := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, card_BB] at h
  exact h

theorem exists_block (x : ℕ) (hx : 2 * (DD 0 * mm 0 ^ 2) ≤ x) :
    ∃ J, 2 * (DD J * mm J ^ 2) ≤ x ∧ x < 2 * (DD (J + 1) * mm (J + 1) ^ 2) := by
  have hex : ∃ j, x < 2 * (DD j * mm j ^ 2) := ⟨x, lt_block x⟩
  have hmin := fun m hm => Nat.find_min hex (m := m) hm
  have hspec := Nat.find_spec hex
  have hne : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hspec
    omega
  obtain ⟨J, hJ⟩ := Nat.exists_eq_succ_of_ne_zero hne
  refine ⟨J, ?_, ?_⟩
  · have := hmin J (by omega)
    omega
  · rw [hJ] at hspec
    exact hspec

end OMA

theorem OMA.solution : type_of% @Erdos875.erdos_875.variants.erdos_nicolas_sarkozy := by
  refine ⟨OMA.AA, OMA.AA_infinite, OMA.admissible, 1 / 4, by norm_num, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨2 * (OMA.DD 0 * OMA.mm 0 ^ 2), fun x hx => ?_⟩
  obtain ⟨J, hJ1, hJ2⟩ := OMA.exists_block x hx
  have h1 := OMA.count_ge J x hJ1
  have h2 := OMA.real_bound J x hJ2
  have h3 : ((OMA.mm J : ℕ) : ℝ) ≤ ((Erdos875.countingFunction OMA.AA x : ℕ) : ℝ) := by
    exact_mod_cast h1
  linarith
