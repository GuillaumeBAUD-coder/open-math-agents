import FormalConjectures.ErdosProblems.«875»

-- Problem: Erdős Problem 875 — polynomial gaps
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/875.lean (declaration Erdos875.erdos_875.variants.polynomial_gaps)
-- Credit: @OrangeHeadz (the owner of the agent is credited as the solver)

/-!
# An admissible set with polynomial gaps

Block construction in the style of Erdős, Nicolas and Sárközy. Fix `lam = 1 + √6 / 2` and
exponents `e (J + 1) = ⌈lam * e J⌉`. Block `J` consists of the `k J = 2 ^ e J` numbers
`D J * (k J ^ 2 + t)`, `t < k J`, where `D (J + 1) = 3 * D J * k J ^ 3` exceeds the sum of all
elements of the earlier blocks.

* Admissible: for a finite set `T` of elements from blocks `≤ J`, the sum `s` determines the number
  of terms. The part of `T` below block `J` sums to less than `D J`, so it equals `s % D J`, and
  `s / D J = r * k J ^ 2 + τ` with `τ < k J ^ 2`, where `r` counts the terms in block `J`.
* Gaps: block `J + 1` alone has `k (J + 1)` elements below `2 * D (J + 1) * k (J + 1) ^ 2`, which is
  at most `k J ^ c` because `3 * lam / (lam - 1) + 2 * lam = 5 + 2 * √6 < c`. So the `n`-th element
  is at most `n ^ c` for `k J ≤ n < k (J + 1)`.
-/

open scoped Classical

namespace OMA

noncomputable def lam : ℝ := 1 + Real.sqrt 6 / 2

noncomputable def ee (e0 : ℕ) : ℕ → ℕ
  | 0 => e0
  | n + 1 => ⌈lam * (ee e0 n : ℝ)⌉₊

noncomputable def FF (e0 : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => FF e0 n + ee e0 n

noncomputable def kk (e0 J : ℕ) : ℕ := 2 ^ ee e0 J

noncomputable def DD (e0 : ℕ) : ℕ → ℕ
  | 0 => 1
  | J + 1 => 3 * DD e0 J * kk e0 J ^ 3

noncomputable def BB (e0 J : ℕ) : Finset ℕ :=
  (Finset.range (kk e0 J)).image fun t => DD e0 J * (kk e0 J ^ 2 + t)

noncomputable def UU (e0 : ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | J + 1 => UU e0 J ∪ BB e0 J

noncomputable def AA (e0 : ℕ) : Set ℕ := {x | ∃ J, x ∈ BB e0 J}

noncomputable def cnt (e0 : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | J + 1, s => (s / DD e0 J) / kk e0 J ^ 2 + cnt e0 J (s % DD e0 J)

/- ### Basic facts -/

theorem s6_mul : Real.sqrt 6 * Real.sqrt 6 = 6 := Real.mul_self_sqrt (by norm_num)

theorem s6_nonneg : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg 6

theorem s6_two_le : 2 ≤ Real.sqrt 6 := by
  by_contra h
  push_neg at h
  have h0 := s6_nonneg
  have h1 := s6_mul
  nlinarith

theorem lam_two_le : 2 ≤ lam := by
  unfold lam
  have := s6_two_le
  linarith

theorem ee_succ_ge (e0 J : ℕ) : lam * (ee e0 J : ℝ) ≤ (ee e0 (J + 1) : ℝ) :=
  Nat.le_ceil _

theorem ee_succ_le (e0 J : ℕ) : (ee e0 (J + 1) : ℝ) ≤ lam * (ee e0 J : ℝ) + 1 := by
  have h0 : 0 ≤ lam * (ee e0 J : ℝ) := mul_nonneg (by linarith [lam_two_le]) (Nat.cast_nonneg _)
  exact (Nat.ceil_lt_add_one h0).le

theorem two_mul_ee_le (e0 J : ℕ) : 2 * ee e0 J ≤ ee e0 (J + 1) := by
  have h1 := ee_succ_ge e0 J
  have h2 : (2 : ℝ) * (ee e0 J : ℝ) ≤ lam * (ee e0 J : ℝ) :=
    mul_le_mul_of_nonneg_right lam_two_le (Nat.cast_nonneg _)
  have h3 : ((2 * ee e0 J : ℕ) : ℝ) ≤ (ee e0 (J + 1) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h3

theorem ee_ge (e0 : ℕ) : ∀ J, 2 ^ J * e0 ≤ ee e0 J := by
  intro J
  induction J with
  | zero => simp [ee]
  | succ J ih =>
    have h := two_mul_ee_le e0 J
    calc 2 ^ (J + 1) * e0 = 2 * (2 ^ J * e0) := by ring
      _ ≤ 2 * ee e0 J := Nat.mul_le_mul_left 2 ih
      _ ≤ ee e0 (J + 1) := h

theorem kk_pos (e0 J : ℕ) : 0 < kk e0 J := by
  unfold kk
  positivity

theorem DD_pos (e0 : ℕ) : ∀ J, 0 < DD e0 J := by
  intro J
  induction J with
  | zero => simp [DD]
  | succ J ih =>
    have hk := kk_pos e0 J
    show 0 < 3 * DD e0 J * kk e0 J ^ 3
    positivity

/- ### The count of terms is determined by the sum -/

theorem mem_BB (e0 J x : ℕ) :
    x ∈ BB e0 J ↔ ∃ t, t < kk e0 J ∧ DD e0 J * (kk e0 J ^ 2 + t) = x := by
  unfold BB
  rw [Finset.mem_image]
  constructor
  · intro h
    obtain ⟨t, ht, hx⟩ := h
    exact ⟨t, Finset.mem_range.mp ht, hx⟩
  · intro h
    obtain ⟨t, ht, hx⟩ := h
    exact ⟨t, Finset.mem_range.mpr ht, hx⟩

theorem card_le_of_subset_BB (e0 J : ℕ) (T : Finset ℕ) (hT : T ⊆ BB e0 J) :
    T.card ≤ kk e0 J := by
  have h1 := Finset.card_le_card hT
  have h2 : (BB e0 J).card ≤ (Finset.range (kk e0 J)).card := Finset.card_image_le
  rw [Finset.card_range] at h2
  omega

theorem sum_subset_BB (e0 J : ℕ) : ∀ T : Finset ℕ, T ⊆ BB e0 J →
    ∃ τ, ∑ x ∈ T, x = DD e0 J * (T.card * kk e0 J ^ 2 + τ) ∧ τ + T.card ≤ T.card * kk e0 J := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨0, by simp, by simp⟩
  | insert a s ha ih =>
    intro hT
    have hs : s ⊆ BB e0 J := fun x hx => hT (Finset.mem_insert_of_mem hx)
    obtain ⟨τ, h1, h2⟩ := ih hs
    obtain ⟨t, ht, hta⟩ := (mem_BB e0 J a).mp (hT (Finset.mem_insert_self a s))
    refine ⟨τ + t, ?_, ?_⟩
    · rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, h1, ← hta]
      ring
    · rw [Finset.card_insert_of_notMem ha]
      have e : (s.card + 1) * kk e0 J = s.card * kk e0 J + kk e0 J := by ring
      rw [e]
      omega

theorem sum_UU_lt (e0 : ℕ) : ∀ J, ∑ x ∈ UU e0 J, x < DD e0 J := by
  intro J
  induction J with
  | zero => simp [UU, DD]
  | succ J ih =>
    show ∑ x ∈ UU e0 J ∪ BB e0 J, x < 3 * DD e0 J * kk e0 J ^ 3
    have hle : ∑ x ∈ UU e0 J ∪ BB e0 J, x ≤ ∑ x ∈ UU e0 J, x + ∑ x ∈ BB e0 J, x := by
      have h := Finset.sum_union_inter (s₁ := UU e0 J) (s₂ := BB e0 J) (f := fun x : ℕ => x)
      omega
    obtain ⟨τ, h1, h2⟩ := sum_subset_BB e0 J (BB e0 J) (Finset.Subset.refl _)
    have hc := card_le_of_subset_BB e0 J (BB e0 J) (Finset.Subset.refl _)
    have hk := kk_pos e0 J
    have hD := DD_pos e0 J
    generalize (BB e0 J).card = r at h1 h2 hc
    generalize kk e0 J = k at h1 h2 hc hk ⊢
    generalize DD e0 J = D at h1 hD ih ⊢
    have a1 : r * k ^ 2 ≤ k * k ^ 2 := Nat.mul_le_mul_right _ hc
    have a3 : r * k ≤ k * k := Nat.mul_le_mul_right _ hc
    have a4 : k * k ≤ k * k ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
    have e3 : k * k ^ 2 = k ^ 3 := by ring
    have a5 : r * k ^ 2 + τ ≤ 2 * k ^ 3 := by omega
    have a6 : D * (r * k ^ 2 + τ) ≤ D * (2 * k ^ 3) := Nat.mul_le_mul_left _ a5
    have a7 : D ≤ D * k ^ 3 := Nat.le_mul_of_pos_right _ (by positivity)
    have e4 : D * (2 * k ^ 3) = 2 * (D * k ^ 3) := by ring
    have e5 : 3 * D * k ^ 3 = 3 * (D * k ^ 3) := by ring
    rw [e5]
    omega

theorem cnt_spec (e0 : ℕ) : ∀ J, ∀ T : Finset ℕ, T ⊆ UU e0 J →
    T.card = cnt e0 J (∑ x ∈ T, x) := by
  intro J
  induction J with
  | zero =>
    intro T hT
    have : T = ∅ := Finset.subset_empty.mp hT
    rw [this]
    rfl
  | succ J ih =>
    intro T hT
    have hcard := Finset.card_filter_add_card_filter_not (s := T) (fun x => x ∈ BB e0 J)
    have hsum := Finset.sum_filter_add_sum_filter_not T (fun x => x ∈ BB e0 J) (fun x : ℕ => x)
    have h1 : T.filter (fun x => x ∈ BB e0 J) ⊆ BB e0 J := fun x hx => (Finset.mem_filter.mp hx).2
    have h2 : T.filter (fun x => ¬ x ∈ BB e0 J) ⊆ UU e0 J := by
      intro x hx
      obtain ⟨hxT, hxB⟩ := Finset.mem_filter.mp hx
      have hxU : x ∈ UU e0 J ∪ BB e0 J := hT hxT
      rcases Finset.mem_union.mp hxU with h | h
      · exact h
      · exact absurd h hxB
    have hL : ∑ x ∈ T.filter (fun x => ¬ x ∈ BB e0 J), x < DD e0 J :=
      lt_of_le_of_lt (Finset.sum_le_sum_of_subset h2) (sum_UU_lt e0 J)
    obtain ⟨τ, hs1, hτ⟩ := sum_subset_BB e0 J _ h1
    have hc := card_le_of_subset_BB e0 J _ h1
    have ih2 := ih _ h2
    have hk := kk_pos e0 J
    have hD := DD_pos e0 J
    show T.card = (∑ x ∈ T, x) / DD e0 J / kk e0 J ^ 2 + cnt e0 J ((∑ x ∈ T, x) % DD e0 J)
    rw [← hsum, hs1]
    generalize ∑ x ∈ T.filter (fun x => ¬ x ∈ BB e0 J), x = L at hL ih2 ⊢
    generalize (T.filter (fun x => x ∈ BB e0 J)).card = r at hcard hτ hc ⊢
    have hk2 : 0 < kk e0 J ^ 2 := by positivity
    have a3 : r * kk e0 J ≤ kk e0 J * kk e0 J := Nat.mul_le_mul_right _ hc
    have e3 : kk e0 J * kk e0 J = kk e0 J ^ 2 := by ring
    have hτ2 : τ < kk e0 J ^ 2 := by
      rcases Nat.eq_zero_or_pos r with hr | hr
      · rw [hr] at hτ
        simp at hτ
        omega
      · omega
    have d1 : (DD e0 J * (r * kk e0 J ^ 2 + τ) + L) / DD e0 J = r * kk e0 J ^ 2 + τ := by
      rw [Nat.mul_add_div hD, Nat.div_eq_of_lt hL, Nat.add_zero]
    have d2 : (DD e0 J * (r * kk e0 J ^ 2 + τ) + L) % DD e0 J = L := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hL]
    have d3 : (r * kk e0 J ^ 2 + τ) / kk e0 J ^ 2 = r := by
      rw [Nat.mul_comm r, Nat.mul_add_div hk2, Nat.div_eq_of_lt hτ2, Nat.add_zero]
    rw [d1, d2, d3, ← ih2]
    omega

theorem UU_mono (e0 : ℕ) {J J' : ℕ} (h : J ≤ J') : UU e0 J ⊆ UU e0 J' := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact ih.trans Finset.subset_union_left

theorem BB_subset_UU (e0 J : ℕ) : BB e0 J ⊆ UU e0 (J + 1) := Finset.subset_union_right

theorem exists_UU (e0 : ℕ) : ∀ T : Finset ℕ, (↑T : Set ℕ) ⊆ AA e0 → ∃ J, T ⊆ UU e0 J := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨0, Finset.empty_subset _⟩
  | insert a s _ ih =>
    intro hT
    have ha : a ∈ AA e0 := hT (by simp)
    have hs : (↑s : Set ℕ) ⊆ AA e0 := fun x hx => hT (by simp [Finset.mem_coe.mp hx])
    obtain ⟨J1, hJ1⟩ := ih hs
    obtain ⟨J2, hJ2⟩ := ha
    refine ⟨max J1 (J2 + 1), ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxs
    · exact UU_mono e0 (le_max_right J1 (J2 + 1)) (BB_subset_UU e0 J2 hJ2)
    · exact UU_mono e0 (le_max_left J1 (J2 + 1)) (hJ1 hxs)

theorem admissible (e0 : ℕ) : Erdos875.IsAdmissible (AA e0) := by
  intro r _ s _ hrs
  show Disjoint (Erdos875.rSums (AA e0) r) (Erdos875.rSums (AA e0) s)
  rw [Set.disjoint_left]
  intro v h1 h2
  obtain ⟨T1, hT1, c1, e1⟩ := h1
  obtain ⟨T2, hT2, c2, e2⟩ := h2
  obtain ⟨J1, hJ1⟩ := exists_UU e0 T1 hT1
  obtain ⟨J2, hJ2⟩ := exists_UU e0 T2 hT2
  have a := cnt_spec e0 (max J1 J2) T1 (hJ1.trans (UU_mono e0 (le_max_left J1 J2)))
  have b := cnt_spec e0 (max J1 J2) T2 (hJ2.trans (UU_mono e0 (le_max_right J1 J2)))
  apply hrs
  rw [← c1, ← c2, a, b, e1, e2]

/- ### The set is infinite -/

theorem three_pow_le_DD (e0 : ℕ) : ∀ J, 3 ^ J ≤ DD e0 J := by
  intro J
  induction J with
  | zero => simp [DD]
  | succ J ih =>
    have hk : 1 ≤ kk e0 J ^ 3 := Nat.one_le_pow _ _ (kk_pos e0 J)
    show 3 ^ (J + 1) ≤ 3 * DD e0 J * kk e0 J ^ 3
    calc 3 ^ (J + 1) = 3 * 3 ^ J * 1 := by ring
      _ ≤ 3 * DD e0 J * kk e0 J ^ 3 := Nat.mul_le_mul (Nat.mul_le_mul_left 3 ih) hk

theorem first_mem (e0 J : ℕ) : DD e0 J * (kk e0 J ^ 2 + 0) ∈ BB e0 J :=
  (mem_BB e0 J _).mpr ⟨0, kk_pos e0 J, rfl⟩

theorem AA_infinite (e0 : ℕ) : (AA e0).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  refine ⟨DD e0 N * (kk e0 N ^ 2 + 0), ⟨N, first_mem e0 N⟩, ?_⟩
  have h1 : N < 3 ^ N := Nat.lt_pow_self (by norm_num)
  have h2 := three_pow_le_DD e0 N
  have h3 : 1 ≤ kk e0 N ^ 2 + 0 := by
    have := kk_pos e0 N
    have : 0 < kk e0 N ^ 2 := by positivity
    omega
  have h4 : DD e0 N ≤ DD e0 N * (kk e0 N ^ 2 + 0) := Nat.le_mul_of_pos_right _ h3
  omega

/- ### Size estimates -/

theorem DD_le (e0 : ℕ) : ∀ J, DD e0 J ≤ 2 ^ (2 * J + 3 * FF e0 J) := by
  intro J
  induction J with
  | zero =>
    show 1 ≤ 2 ^ (2 * 0 + 3 * FF e0 0)
    exact Nat.one_le_two_pow
  | succ J ih =>
    show 3 * DD e0 J * kk e0 J ^ 3 ≤ 2 ^ (2 * (J + 1) + 3 * (FF e0 J + ee e0 J))
    have h1 : kk e0 J ^ 3 = 2 ^ (3 * ee e0 J) := by
      unfold kk
      rw [← pow_mul, Nat.mul_comm]
    have h2 : 2 ^ (2 * (J + 1) + 3 * (FF e0 J + ee e0 J)) =
        4 * 2 ^ (2 * J + 3 * FF e0 J) * 2 ^ (3 * ee e0 J) := by
      have : 2 * (J + 1) + 3 * (FF e0 J + ee e0 J) = 2 + (2 * J + 3 * FF e0 J) + 3 * ee e0 J := by
        ring
      rw [this, pow_add, pow_add]
      norm_num
    rw [h1, h2]
    apply Nat.mul_le_mul_right
    calc 3 * DD e0 J ≤ 4 * DD e0 J := Nat.mul_le_mul_right _ (by norm_num)
      _ ≤ 4 * 2 ^ (2 * J + 3 * FF e0 J) := Nat.mul_le_mul_left 4 ih

theorem block_bound_nat (e0 J : ℕ) :
    2 * DD e0 J * kk e0 J ^ 2 ≤ 2 ^ (1 + (2 * J + 3 * FF e0 J) + 2 * ee e0 J) := by
  have h1 : kk e0 J ^ 2 = 2 ^ (2 * ee e0 J) := by
    unfold kk
    rw [← pow_mul, Nat.mul_comm]
  have h2 : 2 ^ (1 + (2 * J + 3 * FF e0 J) + 2 * ee e0 J) =
      2 * 2 ^ (2 * J + 3 * FF e0 J) * 2 ^ (2 * ee e0 J) := by
    rw [pow_add, pow_add]
    norm_num
  rw [h1, h2]
  apply Nat.mul_le_mul_right
  exact Nat.mul_le_mul_left 2 (DD_le e0 J)

theorem FF_bound (e0 : ℕ) : ∀ J, (FF e0 J : ℝ) * (Real.sqrt 6 / 2) ≤ (ee e0 J : ℝ) := by
  intro J
  induction J with
  | zero =>
    show ((0 : ℕ) : ℝ) * (Real.sqrt 6 / 2) ≤ (ee e0 0 : ℝ)
    simp
  | succ J ih =>
    have h := ee_succ_ge e0 J
    show ((FF e0 J + ee e0 J : ℕ) : ℝ) * (Real.sqrt 6 / 2) ≤ (ee e0 (J + 1) : ℝ)
    push_cast
    unfold lam at h
    nlinarith

theorem FF_succ_bound (e0 J : ℕ) :
    3 * (FF e0 (J + 1) : ℝ) ≤ (Real.sqrt 6 + 3) * (ee e0 J : ℝ) := by
  have h := FF_bound e0 J
  have hs := s6_mul
  have h0 := s6_nonneg
  have hF : (FF e0 (J + 1) : ℝ) = (FF e0 J : ℝ) + (ee e0 J : ℝ) := by
    show ((FF e0 J + ee e0 J : ℕ) : ℝ) = _
    push_cast
    ring
  rw [hF]
  have h3 : Real.sqrt 6 * ((FF e0 J : ℝ) * (Real.sqrt 6 / 2)) ≤ Real.sqrt 6 * (ee e0 J : ℝ) :=
    mul_le_mul_of_nonneg_left h h0
  have e1 : Real.sqrt 6 * ((FF e0 J : ℝ) * (Real.sqrt 6 / 2)) = 3 * (FF e0 J : ℝ) := by
    calc Real.sqrt 6 * ((FF e0 J : ℝ) * (Real.sqrt 6 / 2))
        = (FF e0 J : ℝ) * (Real.sqrt 6 * Real.sqrt 6) / 2 := by ring
      _ = (FF e0 J : ℝ) * 6 / 2 := by rw [hs]
      _ = 3 * (FF e0 J : ℝ) := by ring
  rw [e1] at h3
  linarith

theorem linear_le (J : ℕ) : 2 * J + 5 ≤ 5 * 2 ^ J := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    have : 2 ^ (J + 1) = 2 * 2 ^ J := by ring
    rw [this]
    have h1 : 1 ≤ 2 ^ J := Nat.one_le_two_pow
    omega

theorem exponent_bound (e0 J : ℕ) (c : ℝ)
    (hδ : 5 ≤ (c - 5 - 2 * Real.sqrt 6) * (e0 : ℝ)) (hc : 5 + 2 * Real.sqrt 6 < c) :
    ((1 + (2 * (J + 1) + 3 * FF e0 (J + 1)) + 2 * ee e0 (J + 1) : ℕ) : ℝ) ≤ c * (ee e0 J : ℝ) := by
  have hA := FF_succ_bound e0 J
  have hB := ee_succ_le e0 J
  have hC : ((2 * J + 5 : ℕ) : ℝ) ≤ ((5 * 2 ^ J : ℕ) : ℝ) := by exact_mod_cast linear_le J
  have hE : ((2 ^ J * e0 : ℕ) : ℝ) ≤ (ee e0 J : ℝ) := by exact_mod_cast ee_ge e0 J
  have hδpos : 0 < c - 5 - 2 * Real.sqrt 6 := by linarith
  have hD : (5 : ℝ) * (2 : ℝ) ^ J ≤ (c - 5 - 2 * Real.sqrt 6) * (ee e0 J : ℝ) := by
    have h1 : (5 : ℝ) * (2 : ℝ) ^ J ≤ (c - 5 - 2 * Real.sqrt 6) * (e0 : ℝ) * (2 : ℝ) ^ J :=
      mul_le_mul_of_nonneg_right hδ (by positivity)
    have h2 : (c - 5 - 2 * Real.sqrt 6) * ((2 : ℝ) ^ J * (e0 : ℝ)) ≤
        (c - 5 - 2 * Real.sqrt 6) * (ee e0 J : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hδpos.le
      push_cast at hE
      exact hE
    calc (5 : ℝ) * (2 : ℝ) ^ J ≤ (c - 5 - 2 * Real.sqrt 6) * (e0 : ℝ) * (2 : ℝ) ^ J := h1
      _ = (c - 5 - 2 * Real.sqrt 6) * ((2 : ℝ) ^ J * (e0 : ℝ)) := by ring
      _ ≤ (c - 5 - 2 * Real.sqrt 6) * (ee e0 J : ℝ) := h2
  push_cast at hC ⊢
  unfold lam at hB
  nlinarith

theorem block_bound_real (e0 J : ℕ) (c : ℝ)
    (hδ : 5 ≤ (c - 5 - 2 * Real.sqrt 6) * (e0 : ℝ)) (hc : 5 + 2 * Real.sqrt 6 < c) :
    ((2 * DD e0 (J + 1) * kk e0 (J + 1) ^ 2 : ℕ) : ℝ) ≤ ((kk e0 J : ℕ) : ℝ) ^ c := by
  have h1 := block_bound_nat e0 (J + 1)
  have h2 := exponent_bound e0 J c hδ hc
  have h3 : ((2 * DD e0 (J + 1) * kk e0 (J + 1) ^ 2 : ℕ) : ℝ) ≤
      ((2 ^ (1 + (2 * (J + 1) + 3 * FF e0 (J + 1)) + 2 * ee e0 (J + 1)) : ℕ) : ℝ) := by
    exact_mod_cast h1
  have h4 : ((2 ^ (1 + (2 * (J + 1) + 3 * FF e0 (J + 1)) + 2 * ee e0 (J + 1)) : ℕ) : ℝ) =
      (2 : ℝ) ^ (((1 + (2 * (J + 1) + 3 * FF e0 (J + 1)) + 2 * ee e0 (J + 1) : ℕ)) : ℝ) := by
    rw [Real.rpow_natCast]
    push_cast
    ring
  have h5 : ((kk e0 J : ℕ) : ℝ) ^ c = (2 : ℝ) ^ ((ee e0 J : ℝ) * c) := by
    unfold kk
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
    push_cast
    ring
  rw [h5]
  refine h3.trans ?_
  rw [h4]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  linarith [mul_comm (ee e0 J : ℝ) c]

/- ### The `n`-th element -/

theorem card_BB (e0 J : ℕ) : (BB e0 J).card = kk e0 J := by
  unfold BB
  rw [Finset.card_image_of_injective, Finset.card_range]
  intro t1 t2 h
  have hD := DD_pos e0 J
  have h' : kk e0 J ^ 2 + t1 = kk e0 J ^ 2 + t2 := Nat.eq_of_mul_eq_mul_left hD h
  omega

theorem nth_lt (e0 J n : ℕ) (hn : n < kk e0 J) :
    Nat.nth (· ∈ AA e0) n < 2 * DD e0 J * kk e0 J ^ 2 + 1 := by
  have hinf : (Set.ofPred (fun x => x ∈ AA e0)).Infinite := AA_infinite e0
  rw [← Nat.lt_nth_iff_count_lt hinf, Nat.count_eq_card_filter_range]
  have hsub : BB e0 J ⊆
      (Finset.range (2 * DD e0 J * kk e0 J ^ 2 + 1)).filter (· ∈ AA e0) := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ⟨J, hx⟩⟩
    obtain ⟨t, ht, rfl⟩ := (mem_BB e0 J x).mp hx
    have hk := kk_pos e0 J
    have a1 : kk e0 J ≤ kk e0 J ^ 2 := by nlinarith
    have a2 : kk e0 J ^ 2 + t ≤ 2 * kk e0 J ^ 2 := by omega
    have a3 : DD e0 J * (kk e0 J ^ 2 + t) ≤ DD e0 J * (2 * kk e0 J ^ 2) := Nat.mul_le_mul_left _ a2
    have e : DD e0 J * (2 * kk e0 J ^ 2) = 2 * DD e0 J * kk e0 J ^ 2 := by ring
    omega
  have h := Finset.card_le_card hsub
  rw [card_BB] at h
  omega

theorem kk_lt_succ (e0 : ℕ) (he : 1 ≤ e0) (J : ℕ) : kk e0 J < kk e0 (J + 1) := by
  unfold kk
  apply Nat.pow_lt_pow_right (by norm_num)
  have h1 := two_mul_ee_le e0 J
  have h2 := ee_ge e0 J
  have h3 : 1 ≤ 2 ^ J * e0 := Nat.mul_pos (by positivity) he
  omega

theorem exists_block (e0 : ℕ) (he : 1 ≤ e0) (n : ℕ) (hn : kk e0 0 ≤ n) :
    ∃ J, kk e0 J ≤ n ∧ n < kk e0 (J + 1) := by
  have hex : ∃ j, n < kk e0 j := by
    refine ⟨n, ?_⟩
    have h1 := ee_ge e0 n
    have h2 : 2 ^ n ≤ 2 ^ n * e0 := Nat.le_mul_of_pos_right _ he
    have h3 : n < 2 ^ n := Nat.lt_two_pow_self
    have h4 : n < ee e0 n := by omega
    have h5 : ee e0 n < 2 ^ ee e0 n := Nat.lt_two_pow_self
    unfold kk
    omega
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

theorem OMA.solution : type_of% @Erdos875.erdos_875.variants.polynomial_gaps := by
  intro c hc
  have hδpos : 0 < c - 5 - 2 * Real.sqrt 6 := by linarith
  have hcpos : 0 ≤ c := by
    have := OMA.s6_nonneg
    linarith
  obtain ⟨e0, he0⟩ := exists_nat_gt (5 / (c - 5 - 2 * Real.sqrt 6))
  have hδ : 5 ≤ (c - 5 - 2 * Real.sqrt 6) * (e0 : ℝ) := by
    have h1 := (div_lt_iff₀ hδpos).mp he0
    linarith
  have he : 1 ≤ e0 := by
    by_contra h
    have h0 : e0 = 0 := by omega
    rw [h0] at hδ
    simp at hδ
    linarith
  refine ⟨OMA.AA e0, OMA.AA_infinite e0, OMA.admissible e0, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨OMA.kk e0 0, fun n hn => ?_⟩
  obtain ⟨J, hJ1, hJ2⟩ := OMA.exists_block e0 he n hn
  have h1 := OMA.nth_lt e0 (J + 1) n hJ2
  have h2 : Erdos875.gap (OMA.AA e0) n ≤ 2 * OMA.DD e0 (J + 1) * OMA.kk e0 (J + 1) ^ 2 := by
    unfold Erdos875.gap
    omega
  have h3 : ((Erdos875.gap (OMA.AA e0) n : ℕ) : ℝ) ≤
      ((2 * OMA.DD e0 (J + 1) * OMA.kk e0 (J + 1) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast h2
  have h4 := OMA.block_bound_real e0 J c hδ hc
  have h5 : ((OMA.kk e0 J : ℕ) : ℝ) ^ c ≤ (n : ℝ) ^ c :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hJ1) hcpos
  exact h3.trans (h4.trans h5)
