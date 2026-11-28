import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R2

/-!
# Step H1 of the reduction Erdos142.erdos_142.variants.lower.R2.H1.R2

Let B_j be the slice of A in block j, shifted down by 4 4^j, so B_j lies in [1, 4^j].
If from some J on every slice had fewer than 4^j / (j+1)^2 elements, block j would add at most
|B_j| / (4 4^j) < 1 / (4 (j+1)^2) to the reciprocal sum, and the sum would converge.
So for infinitely many j the slice is dense: |B_j| (j+1)^2 is at least 4^j.
For such j, with N = 4^j, L = log N and q = (ceil L + 1)^4, we get 2 N L < q |B_j|, because
ceil L + 1 is at least j + 1 (log 4 > 1) and at least L + 1, while (L + 1)^2 > 2 L.
A union bound over random shifts in [0, 2N) then covers every x + N with x in [1, N].
-/

namespace OMA.Helpers

open Finset

/-- The union bound: N bad events, each of probability (1 - s / 2N)^q, cover less than
everything. -/
theorem e142_block_count_bound (N q s : ℕ) (hN : 0 < N) (hsN : s ≤ N)
    (h : 2 * (N : ℝ) * Real.log (N : ℝ) < (q : ℝ) * (s : ℝ)) :
    N * (2 * N - s) ^ q < (2 * N) ^ q := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsr : (s : ℝ) ≤ N := by exact_mod_cast hsN
  have hMpos : (0 : ℝ) < 2 * N := by positivity
  set a : ℝ := (s : ℝ) / (2 * N) with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by
    rw [ha, div_le_one hMpos]
    linarith
  have hcast : (((2 * N - s : ℕ)) : ℝ) = (2 * N) * (1 - a) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rw [ha]
    field_simp
  have hexp : (1 - a) ^ q ≤ Real.exp (-(q * a)) := by
    calc (1 - a) ^ q ≤ Real.exp (-a) ^ q := by
          apply pow_le_pow_left₀ (by linarith)
          linarith [Real.add_one_le_exp (-a)]
      _ = Real.exp (-(q * a)) := by
          rw [← Real.exp_nat_mul]
          ring_nf
  have hlog : Real.log N < q * a := by
    rw [ha, mul_div_assoc', lt_div_iff₀ hMpos]
    linarith
  have hlt : Real.exp (-(q * a)) < 1 / N := by
    have h1 : Real.exp (-(q * a)) < Real.exp (-Real.log N) :=
      Real.exp_lt_exp.mpr (by linarith)
    have h2 : Real.exp (-Real.log N) = 1 / N := by
      rw [Real.exp_neg, Real.exp_log hNr, one_div]
    rwa [h2] at h1
  have hkey : (N : ℝ) * (1 - a) ^ q < 1 := by
    calc (N : ℝ) * (1 - a) ^ q ≤ N * Real.exp (-(q * a)) :=
          mul_le_mul_of_nonneg_left hexp hNr.le
      _ < N * (1 / N) := mul_lt_mul_of_pos_left hlt hNr
      _ = 1 := by field_simp
  have hreal : ((N * (2 * N - s) ^ q : ℕ) : ℝ) < (((2 * N) ^ q : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_pow, hcast, mul_pow, Nat.cast_pow]
    have hpow : (0 : ℝ) < (2 * N) ^ q := by positivity
    have e2 : (((2 * N : ℕ)) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
    rw [e2]
    calc (N : ℝ) * ((2 * N) ^ q * (1 - a) ^ q) = (2 * N) ^ q * ((N : ℝ) * (1 - a) ^ q) := by ring
      _ < (2 * N) ^ q * 1 := mul_lt_mul_of_pos_left hkey hpow
      _ = (2 * N) ^ q := mul_one _
  exact_mod_cast hreal

theorem e142_block_cover (N q : ℕ) (S : Finset ℕ) (hN : 0 < N) (hS : S ⊆ Icc 1 N)
    (h : 2 * (N : ℝ) * Real.log (N : ℝ) < (q : ℝ) * (S.card : ℝ)) :
    ∃ shifts : Fin q → ℕ, ∀ x ∈ Icc 1 N, ∃ t : Fin q, ∃ b ∈ S, x + N = shifts t + b := by
  have hsN : S.card ≤ N := by
    have := card_le_card hS
    simpa using this
  let A : ℕ → Finset (Fin (2 * N)) := fun x =>
    univ.filter (fun r : Fin (2 * N) => ∀ b ∈ S, r.val + b ≠ x + N)
  have hA : ∀ x ∈ Icc 1 N, (A x).card ≤ 2 * N - S.card := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := mem_Icc.mp hx
    let C := univ.filter (fun r : Fin (2 * N) => ¬ ∀ b ∈ S, r.val + b ≠ x + N)
    have hC : S.card ≤ C.card := by
      apply card_le_card_of_injOn
        (fun b => (⟨(x + N - b) % (2 * N), Nat.mod_lt _ (by omega)⟩ : Fin (2 * N)))
      · intro b hb
        rw [mem_coe] at hb
        have hb' := mem_Icc.mp (hS hb)
        rw [mem_coe, mem_filter]
        refine ⟨mem_univ _, ?_⟩
        intro hall
        apply hall b hb
        simp only
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      · intro b hb b' hb' heq
        rw [mem_coe] at hb hb'
        have h1 := mem_Icc.mp (hS hb)
        have h2 := mem_Icc.mp (hS hb')
        have hv := congrArg Fin.val heq
        simp only at hv
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
        omega
    have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * N))))
      (fun r : Fin (2 * N) => ∀ b ∈ S, r.val + b ≠ x + N)
    rw [card_univ, Fintype.card_fin] at hsum
    change (A x).card + C.card = 2 * N at hsum
    omega
  let Bad : ℕ → Finset (Fin q → Fin (2 * N)) := fun x => Fintype.piFinset (fun _ => A x)
  let U := (Icc 1 N).biUnion Bad
  have hU : U.card < (univ : Finset (Fin q → Fin (2 * N))).card := by
    calc U.card ≤ ∑ x ∈ Icc 1 N, (Bad x).card := card_biUnion_le
      _ ≤ ∑ x ∈ Icc 1 N, (2 * N - S.card) ^ q := by
          apply sum_le_sum
          intro x hx
          change (Fintype.piFinset fun _ : Fin q => A x).card ≤ _
          rw [Fintype.card_piFinset_const]
          exact Nat.pow_le_pow_left (hA x hx) q
      _ = N * (2 * N - S.card) ^ q := by
          rw [sum_const, Nat.card_Icc, smul_eq_mul]
          simp
      _ < (2 * N) ^ q := e142_block_count_bound N q S.card hN hsN h
      _ = (univ : Finset (Fin q → Fin (2 * N))).card := by
          rw [card_univ]
          simp
  obtain ⟨f, -, hf⟩ := exists_mem_notMem_of_card_lt_card hU
  refine ⟨fun t => (f t).val, ?_⟩
  intro x hx
  have hnot : f ∉ Bad x := fun hmem => hf (mem_biUnion.mpr ⟨x, hx, hmem⟩)
  rw [Fintype.mem_piFinset] at hnot
  push Not at hnot
  obtain ⟨t, ht⟩ := hnot
  simp only [A, mem_filter, mem_univ, true_and, not_forall, not_not] at ht
  obtain ⟨b, hb, hbeq⟩ := ht
  exact ⟨t, b, hb, hbeq.symm⟩

/-- The numeric core: a slice of density at least 1/(j+1)^2 beats 2 N log N with
q = (ceil(log N) + 1)^4 shifts, since ceil(log N) + 1 is at least j + 1 and at least log N + 1. -/
theorem e142_dense_ineq (j s : ℕ) (hs : 4 ^ j ≤ s * (j + 1) ^ 2) :
    2 * ((4 ^ j : ℕ) : ℝ) * Real.log ((4 ^ j : ℕ) : ℝ) <
      (((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ) * (s : ℝ) := by
  have hlog4 : 1 ≤ Real.log 4 := by
    have h2 := Real.log_two_gt_d9
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    linarith
  have hLj : (j : ℝ) ≤ Real.log ((4 ^ j : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    push_cast
    nlinarith [hlog4, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  set L := Real.log ((4 ^ j : ℕ) : ℝ) with hL
  have hL0 : 0 ≤ L := le_trans (Nat.cast_nonneg j) hLj
  have hc : L ≤ (⌈L⌉₊ : ℝ) := Nat.le_ceil L
  have hN : (0 : ℝ) < ((4 ^ j : ℕ) : ℝ) := by positivity
  have hsr : (((4 ^ j : ℕ) : ℝ)) ≤ (s : ℝ) * ((j : ℝ) + 1) ^ 2 := by exact_mod_cast hs
  set M : ℝ := (⌈L⌉₊ : ℝ) + 1 with hM
  have hcast : (((⌈L⌉₊ + 1) ^ 4 : ℕ) : ℝ) = M ^ 4 := by
    rw [hM]
    push_cast
    ring
  rw [hcast]
  have h1 : (j : ℝ) + 1 ≤ M := by rw [hM]; linarith
  have h2 : ((j : ℝ) + 1) ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  have h3 : ((4 ^ j : ℕ) : ℝ) ≤ s * M ^ 2 :=
    le_trans hsr (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg s))
  have h4 : 2 * L < M ^ 2 := by
    have : L + 1 ≤ M := by rw [hM]; linarith
    nlinarith
  calc 2 * ((4 ^ j : ℕ) : ℝ) * L = (2 * L) * ((4 ^ j : ℕ) : ℝ) := by ring
    _ < M ^ 2 * ((4 ^ j : ℕ) : ℝ) := mul_lt_mul_of_pos_right h4 hN
    _ ≤ M ^ 2 * (s * M ^ 2) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = M ^ 4 * s := by ring

/-- A dense block slice yields the required shifts. -/
theorem e142_cover_of_dense (A : Set ℕ) [DecidablePred (· ∈ A)] (j : ℕ)
    (hs : 4 ^ j ≤ ((Icc 1 (4 ^ j)).filter (fun b => 4 * 4 ^ j + b ∈ A)).card * (j + 1) ^ 2) :
    ∃ shifts : Fin ((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4) → ℕ,
      ∀ x ∈ Icc 1 (4 ^ j),
        ∃ t : Fin ((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4),
          ∃ b ∈ Icc 1 (4 ^ j), 4 * 4 ^ j + b ∈ A ∧ x + 4 ^ j = shifts t + b := by
  obtain ⟨shifts, hsh⟩ := e142_block_cover (4 ^ j) ((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4)
    ((Icc 1 (4 ^ j)).filter (fun b => 4 * 4 ^ j + b ∈ A))
    (by positivity) (filter_subset _ _) (e142_dense_ineq j _ hs)
  refine ⟨shifts, fun x hx => ?_⟩
  obtain ⟨t, b, hb, he⟩ := hsh x hx
  rw [mem_filter] at hb
  exact ⟨t, b, hb.1, hb.2, he⟩

/-- If every block slice from J on is sparse (density below 1/(j+1)^2), the reciprocal sum
converges: block j contributes at most |B_j| / (4 4^j) < 1/(4 (j+1)^2). -/
theorem e142_summable_of_sparse (A : Set ℕ) [DecidablePred (· ∈ A)]
    (hA : ∀ x ∈ A, ∃ j : ℕ, 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j) (J : ℕ)
    (hsp : ∀ j, J ≤ j →
      ((Icc 1 (4 ^ j)).filter (fun b => 4 * 4 ^ j + b ∈ A)).card * (j + 1) ^ 2 < 4 ^ j) :
    Summable (A.indicator (fun n : ℕ ↦ (n : ℝ)⁻¹)) := by
  set S : ℕ → Finset ℕ := fun j => (Icc 1 (4 ^ j)).filter (fun b => 4 * 4 ^ j + b ∈ A)
    with hSdef
  set c : ℕ → ℝ := fun j => ((S j).card : ℝ) / (4 * 4 ^ j) with hcdef
  have hc0 : ∀ j, 0 ≤ c j := fun j => by simp only [hcdef]; positivity
  have hcs : Summable c := by
    refine Summable.of_norm_bounded_eventually_nat (g := fun j : ℕ => 1 / (j : ℝ) ^ 2)
      (Real.summable_one_div_nat_pow.mpr one_lt_two) ?_
    filter_upwards [Filter.eventually_ge_atTop (max J 1)] with j hj
    have hjJ : J ≤ j := le_of_max_le_left hj
    have hj1 : 1 ≤ j := le_of_max_le_right hj
    rw [Real.norm_of_nonneg (hc0 j)]
    have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    have hcard : ((S j).card : ℝ) * ((j : ℝ) + 1) ^ 2 < (4 : ℝ) ^ j := by
      exact_mod_cast hsp j hjJ
    have hmono : ((S j).card : ℝ) * (j : ℝ) ^ 2 ≤ ((S j).card : ℝ) * ((j : ℝ) + 1) ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) (Nat.cast_nonneg _)
    have h4 : (0 : ℝ) < (4 : ℝ) ^ j := by positivity
    simp only [hcdef]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hf0 : ∀ n, 0 ≤ A.indicator (fun n : ℕ ↦ (n : ℝ)⁻¹) n :=
    fun n => Set.indicator_nonneg (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg i)) n
  refine summable_of_sum_range_le hf0 (c := ∑' j, c j) (fun n => ?_)
  calc ∑ i ∈ range n, A.indicator (fun n : ℕ ↦ (n : ℝ)⁻¹) i
      = ∑ i ∈ (range n).filter (· ∈ A), ((i : ℕ) : ℝ)⁻¹ := by
        rw [sum_filter]
        exact sum_congr rfl (fun i _ => Set.indicator_apply _ _ _)
    _ ≤ ∑ i ∈ ((range n).sigma S).image (fun p => 4 * 4 ^ p.1 + p.2), ((i : ℕ) : ℝ)⁻¹ := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro i hi
          rw [mem_filter, mem_range] at hi
          obtain ⟨j, hj1, hj2⟩ := hA i hi.2
          rw [mem_image]
          refine ⟨⟨j, i - 4 * 4 ^ j⟩, ?_, ?_⟩
          · rw [mem_sigma, mem_range]
            constructor
            · show j < n
              have := (Nat.lt_pow_self (by norm_num) : j < 4 ^ j)
              omega
            · simp only [hSdef, mem_filter, mem_Icc]
              refine ⟨⟨by omega, by omega⟩, ?_⟩
              rw [show 4 * 4 ^ j + (i - 4 * 4 ^ j) = i by omega]
              exact hi.2
          · simp only
            omega
        · intro i _ _
          exact inv_nonneg.mpr (Nat.cast_nonneg i)
    _ ≤ ∑ p ∈ (range n).sigma S, (((4 * 4 ^ p.1 + p.2 : ℕ)) : ℝ)⁻¹ :=
        sum_image_le_of_nonneg (fun u _ => inv_nonneg.mpr (Nat.cast_nonneg u))
    _ = ∑ j ∈ range n, ∑ b ∈ S j, (((4 * 4 ^ j + b : ℕ)) : ℝ)⁻¹ := sum_sigma _ _ _
    _ ≤ ∑ j ∈ range n, c j := by
        apply sum_le_sum
        intro j _
        calc ∑ b ∈ S j, (((4 * 4 ^ j + b : ℕ)) : ℝ)⁻¹ ≤ ∑ _b ∈ S j, ((4 * 4 ^ j : ℝ))⁻¹ := by
              apply sum_le_sum
              intro b _
              apply inv_anti₀ (by positivity)
              push_cast
              linarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ b)]
          _ = c j := by
              rw [sum_const, nsmul_eq_mul]
              simp only [hcdef]
              rw [div_eq_mul_inv]
    _ ≤ ∑' j, c j := Summable.sum_le_tsum (range n) (fun j _ => hc0 j) hcs

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R2.H1 := by
  unfold OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R2.H1
  intro A hA hns J
  classical
  by_contra hcon
  apply hns
  apply OMA.Helpers.e142_summable_of_sparse A hA J
  intro j hj
  by_contra hle
  exact hcon ⟨j, hj, OMA.Helpers.e142_cover_of_dense A j (not_lt.mp hle)⟩
