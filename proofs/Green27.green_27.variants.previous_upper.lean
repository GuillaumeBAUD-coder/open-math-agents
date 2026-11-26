import FormalConjectures.GreensOpenProblems.«27»

-- Problem: Green's Open Problem 27 — previous upper
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/27.lean:141 (declaration Green27.green_27.variants.previous_upper)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMAGreen27

/-- The construction: an initial segment of length `3k` together with the multiples
`0, k, 2k, …, Mk`, reduced modulo `p`. -/
def S (p k M : ℕ) : Finset (ZMod p) :=
  (Finset.range (3 * k)).image (fun x : ℕ => (x : ZMod p)) ∪
    (Finset.range (M + 1)).image (fun j : ℕ => ((j * k : ℕ) : ZMod p))

lemma card_S_le (p k M : ℕ) : (S p k M).card ≤ 3 * k + (M + 1) := by
  unfold S
  refine (Finset.card_union_le _ _).trans ?_
  have h1 := Finset.card_image_le (s := Finset.range (3 * k)) (f := fun x : ℕ => (x : ZMod p))
  have h2 := Finset.card_image_le (s := Finset.range (M + 1))
    (f := fun j : ℕ => ((j * k : ℕ) : ZMod p))
  simp only [Finset.card_range] at h1 h2
  omega

/-- Every residue has three representations `x + q` with `x` in the segment and `q` a
multiple, with pairwise distinct `q`. -/
lemma three_reps (p k : ℕ) [NeZero p] (hk : 0 < k) (h2k : 2 * k < p) (n : ZMod p) :
    ∃ x₀ q₀ x₁ q₁ x₂ q₂ : ZMod p,
      x₀ ∈ S p k ((p + 2 * k) / k + 1) ∧ q₀ ∈ S p k ((p + 2 * k) / k + 1) ∧
      x₁ ∈ S p k ((p + 2 * k) / k + 1) ∧ q₁ ∈ S p k ((p + 2 * k) / k + 1) ∧
      x₂ ∈ S p k ((p + 2 * k) / k + 1) ∧ q₂ ∈ S p k ((p + 2 * k) / k + 1) ∧
      x₀ + q₀ = n ∧ x₁ + q₁ = n ∧ x₂ + q₂ = n ∧ q₀ ≠ q₁ ∧ q₀ ≠ q₂ ∧ q₁ ≠ q₂ := by
  set M := (p + 2 * k) / k + 1 with hM
  set t := n.val with ht
  have htp : t < p := ZMod.val_lt n
  set u := if 2 * k ≤ t then t else t + p with hu
  have hun : ((u : ℕ) : ZMod p) = n := by
    rw [hu]
    split_ifs
    · exact ZMod.natCast_zmod_val n
    · push_cast
      rw [ZMod.natCast_self, add_zero]
      exact ZMod.natCast_zmod_val n
  have hu2 : 2 * k ≤ u := by rw [hu]; split_ifs <;> omega
  have hu3 : u < p + 2 * k := by rw [hu]; split_ifs <;> omega
  set j := u / k with hj
  have hjk1 : j * k ≤ u := Nat.div_mul_le_self u k
  have hjk2 : u < j * k + k := Nat.lt_div_mul_add hk
  have hj2 : 2 ≤ j := (Nat.le_div_iff_mul_le hk).mpr (by linarith)
  have hjM : j ≤ (p + 2 * k) / k := Nat.div_le_div_right hu3.le
  have hjk3 : 2 * k ≤ j * k := Nat.mul_le_mul_right k hj2
  have e1 : (j - 1) * k = j * k - k := Nat.sub_one_mul j k
  have e2 : (j - 2) * k = j * k - 2 * k := Nat.sub_mul j 2 k
  have hmemP : ∀ x : ℕ, x < 3 * k → ((x : ℕ) : ZMod p) ∈ S p k M := by
    intro x hx
    unfold S
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, Finset.mem_range.mpr hx, rfl⟩)
  have hmemQ : ∀ i : ℕ, i ≤ M → (((i * k : ℕ)) : ZMod p) ∈ S p k M := by
    intro i hi
    unfold S
    exact Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩)
  have hne : ∀ a b : ℕ, b < a → a - b < p → 0 < a - b →
      ((a : ℕ) : ZMod p) ≠ ((b : ℕ) : ZMod p) := by
    intro a b hba hab hab0 heq
    have : (((a - b : ℕ)) : ZMod p) = 0 := by
      rw [Nat.cast_sub hba.le, heq, sub_self]
    rw [ZMod.natCast_eq_zero_iff] at this
    exact absurd (Nat.le_of_dvd hab0 this) (by omega)
  refine ⟨((u - j * k : ℕ) : ZMod p), ((j * k : ℕ) : ZMod p),
    ((u - (j - 1) * k : ℕ) : ZMod p), (((j - 1) * k : ℕ) : ZMod p),
    ((u - (j - 2) * k : ℕ) : ZMod p), (((j - 2) * k : ℕ) : ZMod p),
    hmemP _ (by omega), hmemQ _ (by omega), hmemP _ (by omega), hmemQ _ (by omega),
    hmemP _ (by omega), hmemQ _ (by omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Nat.cast_add, Nat.sub_add_cancel hjk1, hun]
  · rw [← Nat.cast_add, Nat.sub_add_cancel (by omega), hun]
  · rw [← Nat.cast_add, Nat.sub_add_cancel (by omega), hun]
  · exact hne _ _ (by omega) (by omega) (by omega)
  · exact hne _ _ (by omega) (by omega) (by omega)
  · exact hne _ _ (by omega) (by omega) (by omega)

lemma noUnique (p k : ℕ) [NeZero p] (hk : 0 < k) (h2k : 2 * k < p) :
    HasNoUniqueRepresentation (S p k ((p + 2 * k) / k + 1)) := by
  unfold HasNoUniqueRepresentation
  rw [Set.eq_empty_iff_forall_notMem]
  rintro n ⟨pr, -, -, -, h4⟩
  obtain ⟨x₀, q₀, x₁, q₁, x₂, q₂, hx₀, hq₀, hx₁, hq₁, hx₂, hq₂, e₀, e₁, e₂, d01, d02, d12⟩ :=
    three_reps p k hk h2k n
  have c₀ := h4 x₀ hx₀ q₀ hq₀ e₀
  have c₁ := h4 x₁ hx₁ q₁ hq₁ e₁
  have c₂ := h4 x₂ hx₂ q₂ hq₂ e₂
  rcases c₀ with ⟨-, h₀⟩ | ⟨-, h₀⟩ <;> rcases c₁ with ⟨-, h₁⟩ | ⟨-, h₁⟩ <;>
    rcases c₂ with ⟨-, h₂⟩ | ⟨-, h₂⟩ <;> simp_all

end OMAGreen27

open Green27 in
theorem OMA.solution : type_of% @Green27.green_27.variants.previous_upper := by
  apply Asymptotics.IsBigO.of_bound 11
  unfold primesAtTop
  rw [Filter.eventually_inf_principal]
  filter_upwards [Filter.eventually_ge_atTop 16] with p hp16 hp
  have hp : p.Prime := hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  set s := Nat.sqrt p with hs
  set k := s + 1 with hk
  have hs4 : 4 ≤ s := Nat.le_sqrt.mpr (by omega)
  have hss : s * s ≤ p := Nat.sqrt_le p
  have h2k : 2 * k < p := by nlinarith
  set M := (p + 2 * k) / k + 1 with hM
  set A := OMAGreen27.S p k M with hA
  have hno : HasNoUniqueRepresentation A := OMAGreen27.noUnique p k (by omega) h2k
  have hA2 : 2 ≤ A.card := by
    have hsub : ({(0 : ZMod p), 1} : Finset (ZMod p)) ⊆ A := by
      intro x hx
      rw [hA]
      unfold OMAGreen27.S
      apply Finset.mem_union_left
      rcases Finset.mem_insert.mp hx with h | h
      · exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), by simp [h]⟩
      · rw [Finset.mem_singleton] at h
        exact Finset.mem_image.mpr ⟨1, Finset.mem_range.mpr (by omega), by simp [h]⟩
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair zero_ne_one] at this
  have hmle : m p ≤ A.card := by
    unfold m
    exact csInf_le ⟨0, by rintro x ⟨B, -, -, rfl⟩; positivity⟩ ⟨A, hA2, hno, rfl⟩
  have hcard : A.card ≤ 3 * k + (M + 1) := OMAGreen27.card_S_le p k M
  have hMeq : (p + 2 * k) / k = p / k + 2 := by
    rw [show p + 2 * k = p + k * 2 by ring, Nat.add_mul_div_left _ _ (by omega)]
  -- real estimates
  have hsqrt_ge : (s : ℝ) ≤ Real.sqrt p := Real.nat_sqrt_le_real_sqrt
  have hsqrt_lt : Real.sqrt p < (k : ℝ) := by
    rw [hk]; push_cast; exact Real.real_sqrt_lt_nat_sqrt_succ
  have hsq0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg _
  have hsq1 : 1 ≤ Real.sqrt p := by
    rw [Real.one_le_sqrt]; exact_mod_cast (by omega : 1 ≤ p)
  have hpk : ((p / k : ℕ) : ℝ) ≤ Real.sqrt p := by
    have h1 : ((p / k : ℕ) : ℝ) * k ≤ p := by exact_mod_cast Nat.div_mul_le_self p k
    have h2 : (p : ℝ) = Real.sqrt p * Real.sqrt p := (Real.mul_self_sqrt (by positivity)).symm
    by_contra hcon
    push_neg at hcon
    have : Real.sqrt p * Real.sqrt p < ((p / k : ℕ) : ℝ) * k :=
      mul_lt_mul'' hcon hsqrt_lt hsq0 hsq0
    linarith
  have hm0 : 0 ≤ m p := by
    unfold m
    exact Real.sInf_nonneg (by rintro x ⟨B, -, -, rfl⟩; positivity)
  rw [Real.norm_of_nonneg hm0, Real.norm_of_nonneg hsq0]
  have hcardR : (A.card : ℝ) ≤ 3 * k + ((p / k : ℕ) + 2 + 1 + 1) := by
    have : A.card ≤ 3 * k + (p / k + 2 + 1 + 1) := by omega
    exact_mod_cast this
  have hkR : (k : ℝ) ≤ Real.sqrt p + 1 := by
    rw [hk]; push_cast; linarith
  linarith
