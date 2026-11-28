import OMAStatements.S_mo_178758

open Finset

namespace Claude178758

/-- A sum of a periodic function over `n` consecutive integers does not depend on the start. -/
lemma sum_shift (g : ℕ → ℝ) (n : ℕ) (hg : ∀ m, g (m + n) = g m) (i : ℕ) :
    ∑ k ∈ range n, g (i + k) = ∑ k ∈ range n, g k := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [← ih]
    have h1 : ∑ k ∈ range (n+1), g (i + k) = ∑ k ∈ range n, g (i + k) + g (i + n) :=
      sum_range_succ _ _
    have h2 : ∑ k ∈ range (n+1), g (i + k) = ∑ k ∈ range n, g (i + (k+1)) + g (i + 0) :=
      sum_range_succ' _ _
    have h3 : ∀ k, g (i + 1 + k) = g (i + (k+1)) := fun k => by
      congr 1; omega
    simp only [h3]
    have h4 := hg i
    simp only [add_zero] at h2
    linarith

/-- The chord between two points of the unit circle. -/
lemma chord (a b : ℝ) :
    ‖Complex.exp (Complex.I * (b : ℂ)) - Complex.exp (Complex.I * (a : ℂ))‖
      = 2 * |Real.sin ((b - a) / 2)| := by
  have h1 : Complex.exp (Complex.I * (b : ℂ)) - Complex.exp (Complex.I * (a : ℂ))
      = Complex.exp (Complex.I * (a : ℂ)) * (Complex.exp (Complex.I * ((b - a : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast
    ring
  rw [h1, norm_mul, Complex.norm_exp_I_mul_ofReal_sub_one]
  have h2 : ‖Complex.exp (Complex.I * (a : ℂ))‖ = 1 := by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I a
  rw [h2, one_mul, Real.norm_eq_abs, abs_mul]
  norm_num

/-- The double sum of chords of a quasi-periodic monotone family of angles, grouped by step. -/
lemma double_sum (n : ℕ) (u : ℕ → ℝ)
    (hper : ∀ m, u (m + n) = u m + 2 * Real.pi)
    (hmono : ∀ m, u m ≤ u (m + 1)) :
    ∑ i ∈ range n, ∑ j ∈ range n,
        ‖Complex.exp (Complex.I * (u j : ℂ)) - Complex.exp (Complex.I * (u i : ℂ))‖
      = ∑ k ∈ range n, ∑ i ∈ range n, 2 * Real.sin ((u (i + k) - u i) / 2) := by
  have hmon : Monotone u := monotone_nat_of_le_succ hmono
  rw [sum_comm (s := range n) (t := range n)
    (f := fun k i => 2 * Real.sin ((u (i + k) - u i) / 2))]
  refine sum_congr rfl fun i _ => ?_
  have hperw : ∀ m, Complex.exp (Complex.I * (u (m + n) : ℂ)) = Complex.exp (Complex.I * (u m : ℂ)) := by
    intro m
    rw [hper m]
    push_cast
    rw [mul_add, Complex.exp_add]
    have : Complex.exp (Complex.I * (2 * (Real.pi : ℂ))) = 1 := by
      rw [mul_comm]; exact Complex.exp_two_pi_mul_I
    rw [this, mul_one]
  have hs := sum_shift
    (fun j => ‖Complex.exp (Complex.I * (u j : ℂ)) - Complex.exp (Complex.I * (u i : ℂ))‖) n
    (fun m => by simp only [hperw m]) i
  rw [← hs]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k < n := mem_range.mp hk
  rw [chord]
  have h0 : 0 ≤ u (i + k) - u i := sub_nonneg.mpr (hmon (Nat.le_add_right i k))
  have h1 : u (i + k) ≤ u (i + n) := hmon (by omega)
  have h2 := hper i
  have hpi := Real.pi_pos
  rw [abs_of_nonneg]
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)

/-- The sum of the `k`-step arcs is `2πk`. -/
lemma arc_sum (n : ℕ) (u : ℕ → ℝ)
    (hper : ∀ m, u (m + n) = u m + 2 * Real.pi) (k : ℕ) :
    ∑ i ∈ range n, (u (i + k) - u i) = 2 * Real.pi * k := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h := hper 0
    simp only [add_zero] at h
    have hpi := Real.pi_pos
    linarith
  have hn' : (n : ℝ) ≠ 0 := by positivity
  set g : ℕ → ℝ := fun m => u m - 2 * Real.pi * m / n with hg
  have hgper : ∀ m, g (m + n) = g m := by
    intro m
    simp only [hg, hper m]
    push_cast
    field_simp
    ring
  have hs := sum_shift g n hgper k
  have hu : ∀ m, u m = g m + 2 * Real.pi * m / n := fun m => by simp [hg]
  have e1 : ∑ i ∈ range n, (u (i + k) - u i)
      = ∑ i ∈ range n, g (k + i) - ∑ i ∈ range n, g i
        + ∑ i ∈ range n, (2 * Real.pi * k / n) := by
    rw [← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [hu (i + k), hu i, add_comm k i]
    push_cast
    ring
  rw [e1, hs, sum_const, card_range, nsmul_eq_mul]
  field_simp
  ring

/-- Jensen for the sine: the `k`-step chords of any configuration are at most those of the
regular polygon. -/
lemma step_bound (n : ℕ) (hn : 0 < n) (u : ℕ → ℝ)
    (hper : ∀ m, u (m + n) = u m + 2 * Real.pi)
    (hmono : ∀ m, u m ≤ u (m + 1)) (k : ℕ) (hk : k < n) :
    ∑ i ∈ range n, 2 * Real.sin ((u (i + k) - u i) / 2)
      ≤ n * (2 * Real.sin (Real.pi * k / n)) := by
  have hmon : Monotone u := monotone_nat_of_le_succ hmono
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi := Real.pi_pos
  have hJ := (strictConcaveOn_sin_Icc.concaveOn).le_map_sum
    (t := range n) (w := fun _ => (1 : ℝ) / n) (p := fun i => (u (i + k) - u i) / 2)
    (fun _ _ => by positivity)
    (by rw [sum_const, card_range, nsmul_eq_mul]; field_simp)
    (fun i _ => by
      have h0 : 0 ≤ u (i + k) - u i := sub_nonneg.mpr (hmon (Nat.le_add_right i k))
      have h1 : u (i + k) ≤ u (i + n) := hmon (by omega)
      have h2 := hper i
      exact ⟨by linarith, by linarith⟩)
  have harc := arc_sum n u hper k
  have e2 : ∑ i ∈ range n, (fun _ => (1 : ℝ) / n) i • (fun i => (u (i + k) - u i) / 2) i
      = Real.pi * k / n := by
    simp only [smul_eq_mul]
    have : ∑ i ∈ range n, (1 : ℝ) / n * ((u (i + k) - u i) / 2)
        = (1 / n / 2) * ∑ i ∈ range n, (u (i + k) - u i) := by
      rw [mul_sum]
      refine sum_congr rfl fun i _ => by ring
    rw [this, harc]
    field_simp
  rw [e2] at hJ
  simp only [smul_eq_mul] at hJ
  have e3 : ∑ i ∈ range n, 2 * Real.sin ((u (i + k) - u i) / 2)
      = n * (2 * ∑ i ∈ range n, (1 : ℝ) / n * Real.sin ((u (i + k) - u i) / 2)) := by
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    field_simp
  rw [e3]
  have := mul_le_mul_of_nonneg_left hJ (by positivity : (0 : ℝ) ≤ 2)
  exact mul_le_mul_of_nonneg_left this hn'.le

/-- The regular angles. -/
noncomputable def v (n : ℕ) (m : ℕ) : ℝ := 2 * Real.pi * m / n

lemma v_per (n : ℕ) (hn : 0 < n) (m : ℕ) : v n (m + n) = v n m + 2 * Real.pi := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp only [v]
  push_cast
  field_simp

lemma v_mono (n : ℕ) (m : ℕ) : v n m ≤ v n (m + 1) := by
  simp only [v]
  have hpi := Real.pi_pos
  push_cast
  gcongr
  linarith

lemma regular_sum (n : ℕ) (hn : 0 < n) :
    ∑ i : Fin n, ∑ j : Fin n, ‖OMA.S_mo_178758.regular n j - OMA.S_mo_178758.regular n i‖
      = ∑ k ∈ range n, (n : ℝ) * (2 * Real.sin (Real.pi * k / n)) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have e : ∀ i : Fin n, OMA.S_mo_178758.regular n i
      = Complex.exp (Complex.I * (v n i.val : ℂ)) := fun i => rfl
  simp only [e]
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin n,
    ‖Complex.exp (Complex.I * (v n j.val : ℂ)) - Complex.exp (Complex.I * (v n i : ℂ))‖) n]
  have : ∀ i : ℕ, ∑ j : Fin n,
      ‖Complex.exp (Complex.I * (v n j.val : ℂ)) - Complex.exp (Complex.I * (v n i : ℂ))‖
      = ∑ j ∈ range n,
      ‖Complex.exp (Complex.I * (v n j : ℂ)) - Complex.exp (Complex.I * (v n i : ℂ))‖ :=
    fun i => Fin.sum_univ_eq_sum_range (fun j =>
      ‖Complex.exp (Complex.I * (v n j : ℂ)) - Complex.exp (Complex.I * (v n i : ℂ))‖) n
  simp only [this]
  rw [double_sum n (v n) (v_per n hn) (v_mono n)]
  refine sum_congr rfl fun k _ => ?_
  have hc : ∀ i ∈ range n, 2 * Real.sin ((v n (i + k) - v n i) / 2)
      = 2 * Real.sin (Real.pi * k / n) := by
    intro i _
    congr 2
    simp only [v]
    push_cast
    field_simp
    ring
  rw [sum_congr rfl hc, sum_const, card_range, nsmul_eq_mul]

/-- Sorted angles of a configuration, extended quasi-periodically. -/
noncomputable def ang (n : ℕ) (t : ℕ → ℝ) (m : ℕ) : ℝ := t (m % n) + 2 * Real.pi * (m / n : ℕ)

lemma ang_val (n : ℕ) (t : ℕ → ℝ) (q r : ℕ) (hr : r < n) :
    ang n t (n * q + r) = t r + 2 * Real.pi * q := by
  have hn : 0 < n := by omega
  simp only [ang, Nat.mul_add_mod, Nat.mod_eq_of_lt hr, Nat.mul_add_div hn,
    Nat.div_eq_of_lt hr, add_zero]

end Claude178758

open Claude178758 in
theorem OMA.solution : type_of% @OMA.S_mo_178758.main := by
  intro n hn z hz
  -- sort the arguments
  set θ : Fin n → ℝ := fun i => Complex.arg (z i) with hθ
  set σ : Equiv.Perm (Fin n) := Tuple.sort θ with hσ
  have hsorted : Monotone (θ ∘ σ) := Tuple.monotone_sort θ
  set t : ℕ → ℝ := fun r => if h : r < n then θ (σ ⟨r, h⟩) else 0 with ht
  have ht_val : ∀ (r : ℕ) (h : r < n), t r = θ (σ ⟨r, h⟩) := fun r h => by simp [ht, h]
  have hpi := Real.pi_pos
  have hlow : ∀ r, r < n → -Real.pi < t r := fun r h => by
    rw [ht_val r h]; exact Complex.neg_pi_lt_arg _
  have hupp : ∀ r, r < n → t r ≤ Real.pi := fun r h => by
    rw [ht_val r h]; exact Complex.arg_le_pi _
  set u : ℕ → ℝ := ang n t with hu
  have hper : ∀ m, u (m + n) = u m + 2 * Real.pi := by
    intro m
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < n ∧ m = n * q + r :=
      ⟨m / n, m % n, Nat.mod_lt _ hn, (Nat.div_add_mod m n).symm⟩
    have e : n * q + r + n = n * (q + 1) + r := by ring
    rw [e, hu, ang_val n t (q + 1) r hr, ang_val n t q r hr]
    push_cast
    ring
  have hmono : ∀ m, u m ≤ u (m + 1) := by
    intro m
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < n ∧ m = n * q + r :=
      ⟨m / n, m % n, Nat.mod_lt _ hn, (Nat.div_add_mod m n).symm⟩
    by_cases h : r + 1 < n
    · have e : n * q + r + 1 = n * q + (r + 1) := by ring
      rw [e, hu, ang_val n t q (r + 1) h, ang_val n t q r hr, ht_val r hr, ht_val (r + 1) h]
      have : (θ ∘ σ) ⟨r, hr⟩ ≤ (θ ∘ σ) ⟨r + 1, h⟩ := hsorted (by simp [Fin.le_def])
      simp only [Function.comp] at this
      linarith
    · have e : n * q + r + 1 = n * (q + 1) + 0 := by
        have : r + 1 = n := by omega
        rw [mul_add, mul_one, add_zero, add_assoc, this]
      rw [e, hu, ang_val n t (q + 1) 0 hn, ang_val n t q r hr]
      have h1 := hlow 0 hn
      have h2 := hupp r hr
      push_cast
      linarith
  have hz' : ∀ (i : ℕ) (h : i < n), z (σ ⟨i, h⟩) = Complex.exp (Complex.I * (u i : ℂ)) := by
    intro i h
    have e : u i = t i := by
      have := ang_val n t 0 i h
      simp only [mul_zero, zero_add, Nat.cast_zero, add_zero] at this
      rw [hu, this]
    rw [e, ht_val i h, hθ]
    have := Complex.norm_mul_exp_arg_mul_I (z (σ ⟨i, h⟩))
    rw [hz, Complex.ofReal_one, one_mul] at this
    rw [mul_comm]
    exact this.symm
  -- rewrite the configuration's sum
  have e1 : ∑ i : Fin n, ∑ j : Fin n, ‖z j - z i‖
      = ∑ i ∈ range n, ∑ j ∈ range n,
        ‖Complex.exp (Complex.I * (u j : ℂ)) - Complex.exp (Complex.I * (u i : ℂ))‖ := by
    rw [← Equiv.sum_comp σ (fun i => ∑ j : Fin n, ‖z j - z i‖)]
    have : ∀ i : Fin n, ∑ j : Fin n, ‖z j - z (σ i)‖ = ∑ j : Fin n, ‖z (σ j) - z (σ i)‖ :=
      fun i => (Equiv.sum_comp σ (fun j => ‖z j - z (σ i)‖)).symm
    simp only [this]
    have h3 : ∀ i j : Fin n, ‖z (σ j) - z (σ i)‖
        = ‖Complex.exp (Complex.I * (u j.val : ℂ)) - Complex.exp (Complex.I * (u i.val : ℂ))‖ := by
      intro i j
      rw [← hz' j.val j.isLt, ← hz' i.val i.isLt]
    simp only [h3]
    rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin n,
      ‖Complex.exp (Complex.I * (u j.val : ℂ)) - Complex.exp (Complex.I * (u i : ℂ))‖) n]
    refine sum_congr rfl fun i _ => ?_
    exact Fin.sum_univ_eq_sum_range (fun j =>
      ‖Complex.exp (Complex.I * (u j : ℂ)) - Complex.exp (Complex.I * (u i : ℂ))‖) n
  unfold OMA.S_mo_178758.distanceSum
  rw [e1, regular_sum n hn, double_sum n u hper hmono]
  have : ∑ k ∈ range n, ∑ i ∈ range n, 2 * Real.sin ((u (i + k) - u i) / 2)
      ≤ ∑ k ∈ range n, (n : ℝ) * (2 * Real.sin (Real.pi * k / n)) :=
    sum_le_sum fun k hk => step_bound n hn u hper hmono k (mem_range.mp hk)
  linarith
