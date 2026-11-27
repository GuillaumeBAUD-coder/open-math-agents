import OMAReductions.R_Erdos261_erdos_261_parts_iii_R1

/-! With `c = ρ - ℓ - 1` the canonical orbit is `c ↦ 2c - ℓ` (take, when `c ≥ 1`) or `c ↦ 2c + ℓ`
(skip). A path that follows the rule "take when its own `c` is `≥ 1`, skip when it is `≤ -1`" and
chooses freely at the zeros has `c`-value `± c`, the sign being `-` exactly when the last zero
before it was taken. So the set of taken levels of the path attached to `b : ℕ → Bool` has a closed
description (`taken` below), `1 = ∑_{taken a < ℓ} a / 2^a + ρ / 2^ℓ` with `0 ≤ ρ ≤ 2ℓ + 2`, and the
sum over the taken levels is `1`. The set is infinite because the residual is positive at each
zero, and the `i`-th zero is taken exactly when `b i` holds, which gives injectivity. -/

open Filter Topology

namespace OMA.E261b

def F (p : ℕ × ℕ) : ℕ × ℕ :=
  (p.1 + 1, if p.1 + 1 < p.2 then 2 * (p.2 - p.1) else 2 * p.2)

/-- `c j = ρ - ℓ - 1` after `j` steps (`ℓ = j + 1`). -/
def c (j : ℕ) : ℤ := ((F^[j] (1, 2)).2 : ℤ) - j - 2

theorem F_fst (j : ℕ) : (F^[j] (1, 2)).1 = j + 1 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    show (F^[j] (1, 2)).1 + 1 = j + 1 + 1
    omega

theorem c_zero : c 0 = 0 := by
  simp [c]

theorem c_succ (j : ℕ) :
    c (j + 1) = if 1 ≤ c j then 2 * c j - (j + 1) else 2 * c j + (j + 1) := by
  have h1 := F_fst j
  unfold c
  rw [Function.iterate_succ_apply']
  generalize F^[j] (1, 2) = p at h1 ⊢
  obtain ⟨l, r⟩ := p
  simp only at h1
  subst h1
  show (((if j + 1 + 1 < r then 2 * (r - (j + 1)) else 2 * r : ℕ)) : ℤ) - ((j + 1 : ℕ) : ℤ) - 2 = _
  by_cases h : j + 1 + 1 < r
  · rw [if_pos h, if_pos (by omega)]
    push_cast [Nat.cast_sub (show j + 1 ≤ r by omega)]
    ring
  · rw [if_neg h, if_neg (by omega)]
    push_cast
    ring

theorem c_bound (j : ℕ) : -((j : ℤ) + 2) ≤ c j ∧ c j ≤ (j : ℤ) + 2 := by
  induction j with
  | zero => simp [c_zero]
  | succ j ih =>
    rw [c_succ]
    split_ifs <;> constructor <;> push_cast <;> omega

/-- Number of zeros before step `j`. -/
def r (j : ℕ) : ℕ := Nat.count (fun t => c t = 0) j

theorem r_succ (j : ℕ) : r (j + 1) = r j + (if c j = 0 then 1 else 0) :=
  Nat.count_succ _ _

/-- Whether the path attached to `b` takes the level `j + 1`. -/
def taken (b : ℕ → Bool) (j : ℕ) : Bool :=
  if c j = 0 then b (r j)
  else if b (r j - 1) then decide (c j ≤ -1) else decide (1 ≤ c j)

/-- The `c`-value of the path attached to `b`. -/
def d (b : ℕ → Bool) (j : ℕ) : ℤ := if b (r j - 1) then - c j else c j

theorem d_succ (b : ℕ → Bool) (j : ℕ) :
    d b (j + 1) = 2 * d b j + (j + 1) - (if taken b j then 2 * ((j : ℤ) + 1) else 0) := by
  unfold d taken
  rw [c_succ, r_succ]
  by_cases h0 : c j = 0
  · simp only [h0, if_true, Nat.add_sub_cancel]
    cases b (r j) <;> cases b (r j - 1) <;> simp <;> ring
  · simp only [if_neg h0, Nat.add_zero]
    cases hb : b (r j - 1) <;> simp <;> split_ifs <;> omega

theorem d_bound (b : ℕ → Bool) (j : ℕ) : -((j : ℤ) + 2) ≤ d b j ∧ d b j ≤ (j : ℤ) + 2 := by
  have h := c_bound j
  unfold d
  split_ifs <;> constructor <;> omega

/-- Sum of the taken levels below `j + 1`. -/
noncomputable def T (b : ℕ → Bool) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, if taken b i then ((i : ℝ) + 1) / 2 ^ (i + 1) else 0

theorem inv (b : ℕ → Bool) (j : ℕ) : T b j + ((d b j : ℝ) + j + 2) / 2 ^ (j + 1) = 1 := by
  induction j with
  | zero =>
    simp [T, d, c_zero]
  | succ j ih =>
    have hT : T b j = 1 - ((d b j : ℝ) + j + 2) / 2 ^ (j + 1) := by linarith
    have hd : (d b (j + 1) : ℝ) =
        2 * d b j + (j + 1) - (if taken b j then 2 * ((j : ℝ) + 1) else 0) := by
      rw [d_succ]
      split_ifs <;> push_cast <;> ring
    unfold T at hT ⊢
    rw [Finset.sum_range_succ, hT, hd]
    split_ifs
    · push_cast
      field_simp
      ring
    · push_cast
      field_simp
      ring

theorem T_formula (b : ℕ → Bool) (j : ℕ) :
    T b j = 1 - ((d b j : ℝ) + j + 2) / 2 ^ (j + 1) := by
  have := inv b j
  linarith

theorem T_tendsto (b : ℕ → Bool) : Tendsto (T b) atTop (𝓝 1) := by
  have hlow : Tendsto (fun j : ℕ => (1 : ℝ) - ((j : ℝ) ^ 1 / 2 ^ j + 2 * (1 / 2) ^ j)) atTop
      (𝓝 1) := by
    have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (one_lt_two (α := ℝ))
    have h2 : Tendsto (fun j : ℕ => (2 : ℝ) * (1 / 2) ^ j) atTop (𝓝 (2 * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul 2
    have h3 := (tendsto_const_nhds (x := (1 : ℝ))).sub (h1.add h2)
    simpa using h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds ?_ ?_
  · intro j
    have hb := (d_bound b j).2
    have hb' : (d b j : ℝ) ≤ (j : ℝ) + 2 := by exact_mod_cast hb
    show (1 : ℝ) - ((j : ℝ) ^ 1 / 2 ^ j + 2 * (1 / 2) ^ j) ≤ T b j
    rw [T_formula]
    have h2 : ((d b j : ℝ) + j + 2) / 2 ^ (j + 1) ≤ (2 * (j : ℝ) + 4) / 2 ^ (j + 1) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h3 : (2 * (j : ℝ) + 4) / 2 ^ (j + 1) = (j : ℝ) ^ 1 / 2 ^ j + 2 * (1 / 2) ^ j := by
      rw [one_div_pow, pow_succ]
      field_simp
      ring
    linarith
  · intro j
    have hb := (d_bound b j).1
    have hb' : -((j : ℝ) + 2) ≤ (d b j : ℝ) := by exact_mod_cast hb
    show T b j ≤ 1
    rw [T_formula]
    have : 0 ≤ ((d b j : ℝ) + j + 2) / 2 ^ (j + 1) := div_nonneg (by linarith) (by positivity)
    linarith

/-- The set of taken levels. -/
def A (b : ℕ → Bool) : Set ℕ := {a | 1 ≤ a ∧ taken b (a - 1) = true}

theorem sum_range (b : ℕ → Bool) (M : ℕ) :
    ∑ a ∈ Finset.range (M + 1), (A b).indicator (fun a : ℕ => (a : ℝ) / 2 ^ a) a = T b M := by
  classical
  rw [Finset.sum_range_succ']
  have h0 : (A b).indicator (fun a : ℕ => (a : ℝ) / 2 ^ a) 0 = 0 := by
    simp [Set.indicator, A]
  rw [h0, add_zero]
  unfold T
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases ht : taken b i = true
  · have hmem : i + 1 ∈ A b := ⟨by omega, by simpa using ht⟩
    rw [Set.indicator_of_mem hmem, if_pos ht]
    push_cast
    ring
  · have hmem : i + 1 ∉ A b := fun h => ht (by simpa using h.2)
    rw [Set.indicator_of_notMem hmem, if_neg ht]

theorem A_hasSum (b : ℕ → Bool) :
    HasSum ((A b).indicator (fun a : ℕ => (a : ℝ) / 2 ^ a)) 1 := by
  refine (hasSum_iff_tendsto_nat_of_nonneg (fun a => ?_) 1).mpr ?_
  · exact Set.indicator_nonneg (fun a _ => by positivity) a
  · refine (tendsto_add_atTop_iff_nat 1).mp ?_
    simpa [sum_range] using T_tendsto b

theorem d_zero_of (b : ℕ → Bool) (z : ℕ) (hz : c z = 0) : d b z = 0 := by
  unfold d
  split_ifs <;> omega

theorem A_infinite (hZ : {t : ℕ | c t = 0}.Infinite) (b : ℕ → Bool) : (A b).Infinite := by
  intro hfin
  obtain ⟨J, hJ⟩ := hfin.bddAbove
  obtain ⟨z, hz, hzJ⟩ := hZ.exists_gt J
  have hnot : ∀ i, z ≤ i → taken b i = false := by
    intro i hi
    by_contra h
    have hmem : i + 1 ∈ A b := ⟨by omega, by simpa using h⟩
    have := hJ hmem
    omega
  have hconst : ∀ N, z ≤ N → T b N = T b z := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => rfl
    | succ N hN ih =>
      unfold T at ih ⊢
      rw [Finset.sum_range_succ, ih, hnot N hN]
      simp
  have hlim : T b z = 1 :=
    tendsto_nhds_unique (tendsto_atTop_of_eventually_const (i₀ := z) hconst) (T_tendsto b)
  have hinv := inv b z
  rw [hlim, d_zero_of b z hz] at hinv
  have hpos : (0 : ℝ) < (((0 : ℤ) : ℝ) + z + 2) / 2 ^ (z + 1) := by
    push_cast
    positivity
  linarith

theorem A_injective (hZ : {t : ℕ | c t = 0}.Infinite) : Function.Injective A := by
  intro b b' hAA
  funext i
  have hZ' : (Set.ofPred fun t => c t = 0).Infinite := hZ
  have hz0 : c (Nat.nth (fun t => c t = 0) i) = 0 := Nat.nth_mem_of_infinite hZ' i
  have hr : r (Nat.nth (fun t => c t = 0) i) = i := Nat.count_nth_of_infinite hZ' i
  have key : ∀ b0 : ℕ → Bool,
      (Nat.nth (fun t => c t = 0) i + 1 ∈ A b0 ↔ b0 i = true) := by
    intro b0
    constructor
    · intro h
      have h2 := h.2
      simp only [Nat.add_sub_cancel] at h2
      unfold taken at h2
      rw [if_pos hz0, hr] at h2
      exact h2
    · intro h
      refine ⟨by omega, ?_⟩
      simp only [Nat.add_sub_cancel]
      unfold taken
      rw [if_pos hz0, hr]
      exact h
  have h1 := key b
  have h2 := key b'
  rw [hAA] at h1
  have h3 : b i = true ↔ b' i = true := h1.symm.trans h2
  cases hb : b i <;> cases hb' : b' i <;> simp_all

end OMA.E261b

theorem OMA.solution : OMA.R_Erdos261_erdos_261_parts_iii_R1.H2 := by
  intro hinf
  have hZ : {t : ℕ | OMA.E261b.c t = 0}.Infinite := by
    have heq : {t : ℕ | OMA.E261b.c t = 0} =
        {j : ℕ | (OMA.E261b.F^[j] (1, 2)).2 = j + 2} := by
      ext t
      simp only [Set.mem_setOf_eq, OMA.E261b.c]
      omega
    rw [heq]
    exact hinf
  refine ⟨OMA.E261b.A, OMA.E261b.A_injective hZ, fun b => ⟨OMA.E261b.A_infinite hZ b, ?_,
    OMA.E261b.A_hasSum b⟩⟩
  intro a ha
  exact ha.1
