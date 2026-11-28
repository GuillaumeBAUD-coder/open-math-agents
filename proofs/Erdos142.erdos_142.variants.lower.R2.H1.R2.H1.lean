import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R2

-- Step Erdos142.erdos_142.variants.lower.R2.H1.R2.H1:
-- Divergent reciprocal sum on 4-adic blocks produces arbitrarily large shift-covering scales.
-- Credit: @jktcv2kz4f-cyber

open Finset Filter Real

namespace OMA.Helpers

lemma one_le_log_four : (1 : ℝ) ≤ Real.log 4 := by
  have h : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log 4 := (Real.log_lt_log (Real.exp_pos 1) h).le

lemma count_bound (N q s : ℕ) (hN : 0 < N) (hsN : s ≤ N)
    (h : 2 * (N : ℝ) * Real.log (N : ℝ) < (q : ℝ) * (s : ℝ)) :
    N * (2 * N - s) ^ q < (2 * N) ^ q := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsr : (s : ℝ) ≤ N := by exact_mod_cast hsN
  have hMpos : (0 : ℝ) < 2 * N := by positivity
  set a : ℝ := (s : ℝ) / (2 * N) with ha
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
    rw [one_div, ← Real.exp_log hNr, ← Real.exp_neg, Real.exp_lt_exp]
    linarith
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

lemma shift_cover (N q : ℕ) (hN : 0 < N) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 N)
    (h : 2 * (N : ℝ) * Real.log (N : ℝ) < (q : ℝ) * (S.card : ℝ)) :
    ∃ shifts : Fin q → ℕ, ∀ x ∈ Finset.Icc 1 N,
      ∃ t : Fin q, ∃ b ∈ S, x + N = shifts t + b := by
  have hsN : S.card ≤ N := by
    have := card_le_card hS
    simpa using this
  let Miss : ℕ → Finset (Fin (2 * N)) := fun x =>
    univ.filter (fun r : Fin (2 * N) => ∀ b ∈ S, r.val + b ≠ x + N)
  have hMiss : ∀ x ∈ Icc 1 N, (Miss x).card ≤ 2 * N - S.card := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := mem_Icc.mp hx
    let Hit := univ.filter (fun r : Fin (2 * N) => ¬ ∀ b ∈ S, r.val + b ≠ x + N)
    have hHit : S.card ≤ Hit.card := by
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
    change (Miss x).card + Hit.card = 2 * N at hsum
    omega
  let Bad : ℕ → Finset (Fin q → Fin (2 * N)) := fun x => Fintype.piFinset (fun _ => Miss x)
  let U := (Icc 1 N).biUnion Bad
  have hU : U.card < (univ : Finset (Fin q → Fin (2 * N))).card := by
    calc U.card ≤ ∑ x ∈ Icc 1 N, (Bad x).card := card_biUnion_le
      _ ≤ ∑ x ∈ Icc 1 N, (2 * N - S.card) ^ q := by
          apply sum_le_sum
          intro x hx
          change (Fintype.piFinset fun _ : Fin q => Miss x).card ≤ _
          rw [Fintype.card_piFinset_const]
          exact Nat.pow_le_pow_left (hMiss x hx) q
      _ = N * (2 * N - S.card) ^ q := by
          rw [sum_const, Nat.card_Icc, smul_eq_mul]
          simp
      _ < (2 * N) ^ q := count_bound N q S.card hN hsN h
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
  have ht' : ¬ ∀ b ∈ S, (f t).val + b ≠ x + N := by
    intro hall
    exact ht (mem_filter.mpr ⟨mem_univ _, hall⟩)
  push Not at ht'
  obtain ⟨b, hb, heq⟩ := ht'
  exact ⟨t, b, hb, heq.symm⟩

lemma sum_biUnion_le_nonneg {ι α : Type*} [DecidableEq α] (s : Finset ι) (t : ι → Finset α)
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑ x ∈ s.biUnion t, f x) ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hun : (∑ x ∈ t a ∪ s.biUnion t, f x) ≤ (∑ x ∈ t a, f x) + (∑ x ∈ s.biUnion t, f x) := by
      have h1 := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
      have h2 : 0 ≤ ∑ x ∈ t a ∩ s.biUnion t, f x := Finset.sum_nonneg fun x _ => hf x
      linarith
    linarith

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R2.H1 := by
  classical
  intro A hsupp hdiv J
  let B : ℕ → Finset ℕ := fun j => (Finset.Icc 1 (4 ^ j)).filter (fun b => 4 * 4 ^ j + b ∈ A)
  let q : ℕ → ℕ := fun j => (⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4
  have hex : ∃ j : ℕ, max J 1 ≤ j ∧
      2 * ((4 ^ j : ℕ) : ℝ) * Real.log ((4 ^ j : ℕ) : ℝ) < (q j : ℝ) * ((B j).card : ℝ) := by
    by_contra hall
    push_neg at hall
    have hp3 : Summable (fun j : ℕ => 2 * ((j : ℝ) ^ 3)⁻¹) := by
      apply Summable.mul_left 2
      simpa only [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] using
        (Real.summable_nat_rpow_inv (p := (3 : ℝ))).mpr (by norm_num)
    have hsumB : Summable (fun j : ℕ => ((B j).card : ℝ) / (4 * (4 : ℝ) ^ j)) := by
      refine Summable.of_norm_bounded_eventually_nat hp3 ?_
      filter_upwards [eventually_ge_atTop (max J 1)] with j hj
      have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
      have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
      have h4j : (0 : ℝ) < (4 : ℝ) ^ j := by positivity
      have hlog4 : (1 : ℝ) ≤ Real.log 4 := OMA.Helpers.one_le_log_four
      have hlog_eq : Real.log ((4 ^ j : ℕ) : ℝ) = (j : ℝ) * Real.log 4 := by
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
      have hlog_pos : 0 < Real.log ((4 ^ j : ℕ) : ℝ) := by
        rw [hlog_eq]; positivity
      have hlog_ge_j : (j : ℝ) ≤ Real.log ((4 ^ j : ℕ) : ℝ) := by
        rw [hlog_eq]; nlinarith
      have hceil_ge : Real.log ((4 ^ j : ℕ) : ℝ) ≤ (⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1 : ℝ) := by
        have := Nat.le_ceil (Real.log ((4 ^ j : ℕ) : ℝ))
        linarith
      have hq_ge : (Real.log ((4 ^ j : ℕ) : ℝ)) ^ 4 ≤ (q j : ℝ) := by
        have hqcast : (q j : ℝ) = ((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1 : ℝ)) ^ 4 := by
          dsimp [q]; push_cast; rfl
        rw [hqcast]
        exact pow_le_pow_left₀ hlog_pos.le hceil_ge 4
      have hjbound := hall j hj
      have h4jcast : ((4 ^ j : ℕ) : ℝ) = (4 : ℝ) ^ j := by norm_num
      have hjbound' : (q j : ℝ) * ((B j).card : ℝ) ≤
          2 * (4 : ℝ) ^ j * Real.log ((4 ^ j : ℕ) : ℝ) := by
        calc (q j : ℝ) * ((B j).card : ℝ)
            ≤ 2 * ((4 ^ j : ℕ) : ℝ) * Real.log ((4 ^ j : ℕ) : ℝ) := hjbound
          _ = 2 * (4 : ℝ) ^ j * Real.log ((4 ^ j : ℕ) : ℝ) := by rw [h4jcast]
      have hmul : (Real.log ((4 ^ j : ℕ) : ℝ)) ^ 4 * ((B j).card : ℝ) ≤
          2 * (4 : ℝ) ^ j * Real.log ((4 ^ j : ℕ) : ℝ) := by
        calc (Real.log ((4 ^ j : ℕ) : ℝ)) ^ 4 * ((B j).card : ℝ)
            ≤ (q j : ℝ) * ((B j).card : ℝ) :=
              mul_le_mul_of_nonneg_right hq_ge (Nat.cast_nonneg _)
          _ ≤ 2 * (4 : ℝ) ^ j * Real.log ((4 ^ j : ℕ) : ℝ) := hjbound'
      have hcard_le : ((B j).card : ℝ) ≤ 2 * (4 : ℝ) ^ j / (j : ℝ) ^ 3 := by
        have hj3 : (j : ℝ) ^ 3 ≤ (Real.log ((4 ^ j : ℕ) : ℝ)) ^ 3 :=
          pow_le_pow_left₀ hjpos.le hlog_ge_j 3
        have hdiv : (Real.log ((4 ^ j : ℕ) : ℝ)) ^ 3 * ((B j).card : ℝ) ≤ 2 * (4 : ℝ) ^ j := by
          have h1 : Real.log ((4 ^ j : ℕ) : ℝ) * ((Real.log ((4 ^ j : ℕ) : ℝ)) ^ 3 * ((B j).card : ℝ)) ≤
              Real.log ((4 ^ j : ℕ) : ℝ) * (2 * (4 : ℝ) ^ j) := by linarith
          exact le_of_mul_le_mul_left h1 hlog_pos
        have h2 : (j : ℝ) ^ 3 * ((B j).card : ℝ) ≤ 2 * (4 : ℝ) ^ j :=
          le_trans (mul_le_mul_of_nonneg_right hj3 (Nat.cast_nonneg _)) hdiv
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) ^ 3)]
        linarith
      rw [Real.norm_of_nonneg (by positivity)]
      calc ((B j).card : ℝ) / (4 * (4 : ℝ) ^ j)
          ≤ (2 * (4 : ℝ) ^ j / (j : ℝ) ^ 3) / (4 * (4 : ℝ) ^ j) :=
            div_le_div_of_nonneg_right hcard_le (by positivity)
        _ = (1 / 2) * ((j : ℝ) ^ 3)⁻¹ := by
            field_simp [h4j.ne', hjpos.ne']
            ring
        _ ≤ 2 * ((j : ℝ) ^ 3)⁻¹ := by
            have : (0 : ℝ) ≤ ((j : ℝ) ^ 3)⁻¹ := by positivity
            linarith
    apply hdiv
    apply summable_of_sum_le (fun n => by
      by_cases hn : n ∈ A <;> simp [Set.indicator, hn])
      (c := ∑' j : ℕ, ((B j).card : ℝ) / (4 * (4 : ℝ) ^ j))
    intro F
    let M : ℕ := F.sup id + 1
    let T : Finset ℕ := F.filter (fun x => x ∈ A)
    have hFT : ∑ x ∈ F, A.indicator (fun n : ℕ => (n : ℝ)⁻¹) x = ∑ x ∈ T, (x : ℝ)⁻¹ := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : x ∈ A <;> simp [Set.indicator, hx]
    rw [hFT]
    let Cov : Finset ℕ := (Finset.range M).biUnion (fun j => (B j).image (fun b => 4 * 4 ^ j + b))
    have hTsub : T ⊆ Cov := by
      intro x hx
      have hxF : x ∈ F := (Finset.mem_filter.mp hx).1
      have hxA : x ∈ A := (Finset.mem_filter.mp hx).2
      obtain ⟨j, hjlo, hjhi⟩ := hsupp x hxA
      have hjM : j < M := by
        have h1 : j < 4 ^ j := Nat.lt_pow_self (by decide : 1 < 4)
        have h2 : x ≤ F.sup id := Finset.le_sup (f := id) hxF
        dsimp [M]
        omega
      refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hjM, ?_⟩
      refine Finset.mem_image.mpr ⟨x - 4 * 4 ^ j, ?_, by omega⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
        by rwa [show 4 * 4 ^ j + (x - 4 * 4 ^ j) = x by omega]⟩
    calc ∑ x ∈ T, (x : ℝ)⁻¹
        ≤ ∑ x ∈ Cov, (x : ℝ)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hTsub (fun _ _ _ => by positivity)
      _ ≤ ∑ j ∈ Finset.range M, ∑ x ∈ (B j).image (fun b : ℕ => 4 * 4 ^ j + b), (x : ℝ)⁻¹ :=
          OMA.Helpers.sum_biUnion_le_nonneg _ _ (fun x : ℕ => (x : ℝ)⁻¹) (fun _ => by positivity)
      _ ≤ ∑ j ∈ Finset.range M, ((B j).card : ℝ) / (4 * (4 : ℝ) ^ j) := by
          refine Finset.sum_le_sum fun j _ => ?_
          calc ∑ x ∈ (B j).image (fun b : ℕ => 4 * 4 ^ j + b), (x : ℝ)⁻¹
              ≤ ∑ _x ∈ (B j).image (fun b : ℕ => 4 * 4 ^ j + b), (4 * (4 : ℝ) ^ j)⁻¹ := by
                  refine Finset.sum_le_sum fun x hx => ?_
                  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
                  have hb1 : 1 ≤ b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
                  apply inv_anti₀ (by positivity)
                  exact_mod_cast (show 4 * 4 ^ j ≤ 4 * 4 ^ j + b by omega)
            _ = (((B j).image (fun b : ℕ => 4 * 4 ^ j + b)).card : ℝ) * (4 * (4 : ℝ) ^ j)⁻¹ := by
                  simp
            _ ≤ ((B j).card : ℝ) * (4 * (4 : ℝ) ^ j)⁻¹ := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  exact_mod_cast Finset.card_image_le
            _ = ((B j).card : ℝ) / (4 * (4 : ℝ) ^ j) := by rw [div_eq_mul_inv]
      _ ≤ ∑' j : ℕ, ((B j).card : ℝ) / (4 * (4 : ℝ) ^ j) :=
          hsumB.sum_le_tsum _ (fun _ _ => by positivity)
  obtain ⟨j, hj, hbig⟩ := hex
  have hjJ : J ≤ j := le_trans (le_max_left _ _) hj
  obtain ⟨shifts, hcov⟩ := OMA.Helpers.shift_cover (4 ^ j) (q j) (by positivity) (B j)
    (Finset.filter_subset _ _) hbig
  refine ⟨j, hjJ, shifts, fun x hx => ?_⟩
  obtain ⟨t, b, hb, heq⟩ := hcov x hx
  exact ⟨t, b, (Finset.mem_filter.mp hb).1, (Finset.mem_filter.mp hb).2, heq⟩
