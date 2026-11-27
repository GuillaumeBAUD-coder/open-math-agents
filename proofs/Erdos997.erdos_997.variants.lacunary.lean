import FormalConjectures.ErdosProblems.«997»

-- Problem: Erdős Problem 997 — lacunary
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/997.lean:77 (declaration Erdos997.erdos_997.variants.lacunary)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter MeasureTheory Set

namespace Erdos997LacunaryProof

private lemma one_add_pow_ge_quad (h : ℝ) (hh : 0 ≤ h) (r : ℕ) :
    1 + (r : ℝ) * h + ((r : ℝ) * ((r : ℝ) - 1) / 2) * h ^ 2 ≤ (1 + h) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hr : 0 ≤ (r : ℝ) * ((r : ℝ) - 1) := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · simp [h0]
      · have : (1:ℝ) ≤ r := by exact_mod_cast h0
        nlinarith
    have h1 : 0 ≤ 1 + h := by linarith
    have h2 : (1 + (r : ℝ) * h + ((r : ℝ) * ((r : ℝ) - 1) / 2) * h ^ 2) * (1 + h)
        ≤ (1 + h) ^ r * (1 + h) := mul_le_mul_of_nonneg_right ih h1
    have h3 : 0 ≤ ((r : ℝ) * ((r : ℝ) - 1) / 2) * h ^ 3 := by positivity
    rw [pow_succ (1 + h) r]
    push_cast
    nlinarith [h2, h3]

private lemma exists_pow_ge_mul (c : ℝ) (hc : 1 < c) :
    ∃ r : ℕ, 1 ≤ r ∧ 24 * (r : ℝ) ≤ c ^ r := by
  set h : ℝ := c - 1
  have hh : 0 < h := by linarith
  set r : ℕ := max 2 (Nat.ceil (48 / h ^ 2) + 1)
  refine ⟨r, by omega, ?_⟩
  have hr1 : 48 / h ^ 2 ≤ (r : ℝ) - 1 := by
    have hceil : (Nat.ceil (48 / h ^ 2) : ℝ) + 1 ≤ (r : ℝ) := by
      have h0 : Nat.ceil (48 / h ^ 2) + 1 ≤ r := le_max_right _ _
      exact_mod_cast h0
    have hle : 48 / h ^ 2 ≤ (Nat.ceil (48 / h ^ 2) : ℝ) := Nat.le_ceil _
    linarith
  have hquad := one_add_pow_ge_quad h hh.le r
  have hc_eq : 1 + h = c := by ring
  rw [hc_eq] at hquad
  have hterm : 24 ≤ ((r : ℝ) - 1) / 2 * h ^ 2 := by
    have hh2 : 0 < h ^ 2 := sq_pos_of_pos hh
    have hmul : 48 ≤ ((r : ℝ) - 1) * h ^ 2 := by
      rwa [div_le_iff₀ hh2] at hr1
    linarith
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hmul2 : 24 * (r : ℝ) ≤ ((r : ℝ) * ((r : ℝ) - 1) / 2) * h ^ 2 := by
    have := mul_le_mul_of_nonneg_left hterm hr0
    linarith
  have hpos : 0 ≤ 1 + (r : ℝ) * h := by positivity
  linarith

private def sumLen (L : List (ℝ × ℝ)) : ℝ :=
  (L.map (fun I => I.2 - I.1)).sum

private lemma sumLen_nil : sumLen [] = 0 := rfl

private lemma sumLen_cons (I : ℝ × ℝ) (L : List (ℝ × ℝ)) :
    sumLen (I :: L) = (I.2 - I.1) + sumLen L := rfl

private lemma sumLen_append (L₁ L₂ : List (ℝ × ℝ)) :
    sumLen (L₁ ++ L₂) = sumLen L₁ + sumLen L₂ := by
  simp [sumLen, List.map_append, List.sum_append]

private lemma sumLen_nonneg (L : List (ℝ × ℝ)) (h : ∀ I ∈ L, I.1 ≤ I.2) :
    0 ≤ sumLen L := by
  induction L with
  | nil => simp [sumLen]
  | cons I L ih =>
    rw [sumLen_cons]
    have hI : 0 ≤ I.2 - I.1 := sub_nonneg.mpr (h I List.mem_cons_self)
    have hL : 0 ≤ sumLen L := ih (fun J hJ => h J (List.mem_cons_of_mem I hJ))
    linarith

private lemma volume_biUnion_list_le (L : List (ℝ × ℝ)) (h : ∀ I ∈ L, I.1 ≤ I.2) :
    volume (⋃ I ∈ L, Ico I.1 I.2) ≤ ENNReal.ofReal (sumLen L) := by
  induction L with
  | nil => simp [sumLen]
  | cons I L ih =>
    have hI : 0 ≤ I.2 - I.1 := sub_nonneg.mpr (h I List.mem_cons_self)
    have hL : ∀ J ∈ L, J.1 ≤ J.2 := fun J hJ => h J (List.mem_cons_of_mem I hJ)
    have hsumL : 0 ≤ sumLen L := sumLen_nonneg L hL
    have hunion : (⋃ J ∈ (I :: L), Ico J.1 J.2) = Ico I.1 I.2 ∪ (⋃ J ∈ L, Ico J.1 J.2) := by
      ext x
      simp
    rw [hunion, sumLen_cons, ENNReal.ofReal_add hI hsumL]
    calc
      volume (Ico I.1 I.2 ∪ ⋃ J ∈ L, Ico J.1 J.2)
          ≤ volume (Ico I.1 I.2) + volume (⋃ J ∈ L, Ico J.1 J.2) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (I.2 - I.1) + ENNReal.ofReal (sumLen L) := by
          rw [Real.volume_Ico]
          exact add_le_add le_rfl (ih hL)

private lemma split_step (u v δ : ℝ) (N : ℕ) (hN : 0 < N) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hLen : 6 ≤ (N : ℝ) * (v - u)) :
    ∃ G B : List (ℝ × ℝ),
      (∀ I ∈ G, I.2 - I.1 = δ / (N : ℝ)) ∧
      (∀ I ∈ G, Ico I.1 I.2 ⊆ Ico u v) ∧
      (∀ I ∈ G, ∀ α ∈ Ico I.1 I.2, Int.fract (α * (N : ℝ)) ∈ Ico 0 δ) ∧
      (∀ I ∈ B, δ / (N : ℝ) ≤ I.2 - I.1) ∧
      (∀ α ∈ Ico u v, (∃ I ∈ G, α ∈ Ico I.1 I.2) ∨ (∃ I ∈ B, α ∈ Ico I.1 I.2)) ∧
      sumLen G + sumLen B = v - u ∧
      (δ / 2) * (v - u) ≤ sumLen G := by
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  set qmin : ℤ := ⌈(N : ℝ) * u⌉ + 1
  set qmax : ℤ := ⌊(N : ℝ) * v⌋ - 1
  have hdiff_real : (1 / 2 : ℝ) * ((N : ℝ) * (v - u)) ≤ (qmax : ℝ) - (qmin : ℝ) + 1 := by
    have hceil : (⌈(N : ℝ) * u⌉ : ℝ) < (N : ℝ) * u + 1 := Int.ceil_lt_add_one _
    have hfloor : (N : ℝ) * v - 1 < (⌊(N : ℝ) * v⌋ : ℝ) := Int.sub_one_lt_floor _
    have hqmin : (qmin : ℝ) = (⌈(N : ℝ) * u⌉ : ℝ) + 1 := by simp [qmin]
    have hqmax : (qmax : ℝ) = (⌊(N : ℝ) * v⌋ : ℝ) - 1 := by simp [qmax]
    linarith
  have hqle : qmin ≤ qmax := by
    have h1 : (0 : ℝ) < (qmax : ℝ) - (qmin : ℝ) + 1 := by linarith
    have h2 : (0 : ℤ) < qmax - qmin + 1 := by exact_mod_cast h1
    omega
  set m : ℕ := (qmax - qmin + 1).toNat
  have hm_int : (m : ℤ) = qmax - qmin + 1 := Int.toNat_of_nonneg (by omega)
  have hm_pos : 1 ≤ m := by omega
  have hm_real : (m : ℝ) = (qmax : ℝ) - (qmin : ℝ) + 1 := by exact_mod_cast hm_int
  let q : ℕ → ℤ := fun i => qmin + (i : ℤ)
  let G : List (ℝ × ℝ) :=
    (List.range m).map (fun i => ((q i : ℝ) / (N : ℝ), ((q i : ℝ) + δ) / (N : ℝ)))
  let b_left : ℝ × ℝ := (u, (qmin : ℝ) / (N : ℝ))
  let b_right : ℝ × ℝ := (((qmax : ℝ) + δ) / (N : ℝ), v)
  let b_mid : List (ℝ × ℝ) :=
    (List.range (m - 1)).map (fun i => (((q i : ℝ) + δ) / (N : ℝ), ((q i : ℝ) + 1) / (N : ℝ)))
  let B : List (ℝ × ℝ) := b_left :: b_right :: b_mid
  refine ⟨G, B, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Lengths of intervals in G
    intro I hI
    rcases List.mem_map.mp hI with ⟨i, _, rfl⟩
    dsimp
    field_simp
    ring
  · -- Intervals in G are subsets of Ico u v
    intro I hI
    rcases List.mem_map.mp hI with ⟨i, hi, rfl⟩
    rw [List.mem_range] at hi
    intro α hα
    rcases hα with ⟨hα1, hα2⟩
    have hceil : (N : ℝ) * u ≤ (⌈(N : ℝ) * u⌉ : ℝ) := Int.le_ceil _
    have hfloor : (⌊(N : ℝ) * v⌋ : ℝ) ≤ (N : ℝ) * v := Int.floor_le _
    have hqi_lo : (qmin : ℝ) ≤ (q i : ℝ) := by
      simp only [q]
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) i]
    have hqi_hi : (q i : ℝ) ≤ (qmax : ℝ) := by
      have : q i ≤ qmax := by
        simp only [q]
        omega
      exact_mod_cast this
    have hu_le : u ≤ (q i : ℝ) / (N : ℝ) := by
      rw [le_div_iff₀ hNpos]
      have hqmin : (qmin : ℝ) = (⌈(N : ℝ) * u⌉ : ℝ) + 1 := by simp [qmin]
      linarith
    have hv_ge : ((q i : ℝ) + δ) / (N : ℝ) ≤ v := by
      rw [div_le_iff₀ hNpos]
      have hqmax : (qmax : ℝ) = (⌊(N : ℝ) * v⌋ : ℝ) - 1 := by simp [qmax]
      linarith
    exact ⟨le_trans hu_le hα1, lt_of_lt_of_le hα2 hv_ge⟩
  · -- Int.fract property on G
    intro I hI α hα
    rcases List.mem_map.mp hI with ⟨i, _, rfl⟩
    rcases hα with ⟨hα1, hα2⟩
    dsimp at hα1 hα2
    rw [div_le_iff₀ hNpos] at hα1
    rw [lt_div_iff₀ hNpos] at hα2
    have hfloor : ⌊α * (N : ℝ)⌋ = q i := by
      rw [Int.floor_eq_iff]
      exact ⟨hα1, by linarith⟩
    rw [Int.fract, hfloor]
    exact ⟨by linarith, by linarith⟩
  · -- Lengths of intervals in B
    intro I hI
    rcases List.mem_cons.mp hI with rfl | hI
    · -- b_left
      dsimp [b_left]
      have hceil : (N : ℝ) * u ≤ (⌈(N : ℝ) * u⌉ : ℝ) := Int.le_ceil _
      have hqmin : (qmin : ℝ) = (⌈(N : ℝ) * u⌉ : ℝ) + 1 := by simp [qmin]
      rw [div_le_iff₀ hNpos]
      have : ((qmin : ℝ) / (N : ℝ) - u) * (N : ℝ) = (qmin : ℝ) - (N : ℝ) * u := by
        field_simp
      linarith
    · rcases List.mem_cons.mp hI with rfl | hI
      · -- b_right
        dsimp [b_right]
        have hfloor : (⌊(N : ℝ) * v⌋ : ℝ) ≤ (N : ℝ) * v := Int.floor_le _
        have hqmax : (qmax : ℝ) = (⌊(N : ℝ) * v⌋ : ℝ) - 1 := by simp [qmax]
        rw [div_le_iff₀ hNpos]
        have : (v - ((qmax : ℝ) + δ) / (N : ℝ)) * (N : ℝ) = (N : ℝ) * v - ((qmax : ℝ) + δ) := by
          field_simp
        linarith
      · -- b_mid
        rcases List.mem_map.mp hI with ⟨i, _, rfl⟩
        dsimp
        rw [div_le_iff₀ hNpos]
        have : (((q i : ℝ) + 1) / (N : ℝ) - ((q i : ℝ) + δ) / (N : ℝ)) * (N : ℝ) = 1 - δ := by
          field_simp
          ring
        linarith
  · -- Covering property
    intro α hα
    rcases hα with ⟨hαu, hαv⟩
    by_cases h1 : α < (qmin : ℝ) / (N : ℝ)
    · right
      exact ⟨b_left, List.mem_cons_self, ⟨hαu, h1⟩⟩
    · push_neg at h1
      by_cases h2 : ((qmax : ℝ) + δ) / (N : ℝ) ≤ α
      · right
        exact ⟨b_right, List.mem_cons_of_mem _ List.mem_cons_self, ⟨h2, hαv⟩⟩
      · push_neg at h2
        set k : ℤ := ⌊α * (N : ℝ)⌋
        have hk_le : (k : ℝ) ≤ α * (N : ℝ) := Int.floor_le _
        have hk_lt : α * (N : ℝ) < (k : ℝ) + 1 := Int.lt_floor_add_one _
        have h1' : (qmin : ℝ) ≤ α * (N : ℝ) := (div_le_iff₀ hNpos).mp h1
        have h2' : α * (N : ℝ) < (qmax : ℝ) + δ := (lt_div_iff₀ hNpos).mp h2
        have hk_lo : qmin ≤ k := Int.le_floor.mpr h1'
        have hk_hi : k ≤ qmax := by
          have : (k : ℝ) < (qmax : ℝ) + 1 := by linarith
          have : k < qmax + 1 := by exact_mod_cast this
          omega
        set i : ℕ := (k - qmin).toNat
        have hi_lt : i < m := by omega
        have hqi : q i = k := by
          simp only [q, i]
          omega
        by_cases h3 : α * (N : ℝ) < (k : ℝ) + δ
        · left
          refine ⟨((q i : ℝ) / (N : ℝ), ((q i : ℝ) + δ) / (N : ℝ)),
            List.mem_map.mpr ⟨i, List.mem_range.mpr hi_lt, rfl⟩, ?_⟩
          rw [hqi]
          exact ⟨(div_le_iff₀ hNpos).mpr hk_le, (lt_div_iff₀ hNpos).mpr h3⟩
        · push_neg at h3
          have hk_lt_qmax : k < qmax := by
            by_contra hge
            have hkeq : k = qmax := by omega
            have hkr : (k : ℝ) = (qmax : ℝ) := by exact_mod_cast hkeq
            linarith
          have hi_lt_pred : i < m - 1 := by omega
          right
          refine ⟨(((q i : ℝ) + δ) / (N : ℝ), ((q i : ℝ) + 1) / (N : ℝ)),
            List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_map.mpr ⟨i, List.mem_range.mpr hi_lt_pred, rfl⟩)), ?_⟩
          rw [hqi]
          exact ⟨(div_le_iff₀ hNpos).mpr h3, (lt_div_iff₀ hNpos).mpr hk_lt⟩
  · -- Sum of lengths equals v - u
    have hsumG : sumLen G = (m : ℝ) * (δ / (N : ℝ)) := by
      simp only [sumLen, G, List.map_map]
      have hconst : ((fun I : ℝ × ℝ => I.2 - I.1) ∘
          fun i : ℕ => ((q i : ℝ) / (N : ℝ), ((q i : ℝ) + δ) / (N : ℝ))) =
          fun _ => δ / (N : ℝ) := by
        funext i
        dsimp
        field_simp
        ring
      rw [hconst, List.map_const', List.length_range, List.sum_replicate, nsmul_eq_mul]
    have hsumMid : sumLen b_mid = ((m - 1 : ℕ) : ℝ) * ((1 - δ) / (N : ℝ)) := by
      simp only [sumLen, b_mid, List.map_map]
      have hconst : ((fun I : ℝ × ℝ => I.2 - I.1) ∘
          fun i : ℕ => (((q i : ℝ) + δ) / (N : ℝ), ((q i : ℝ) + 1) / (N : ℝ))) =
          fun _ => (1 - δ) / (N : ℝ) := by
        funext i
        dsimp
        field_simp
        ring
      rw [hconst, List.map_const', List.length_range, List.sum_replicate, nsmul_eq_mul]
    have hsumB : sumLen B = ((qmin : ℝ) / (N : ℝ) - u) +
        (v - ((qmax : ℝ) + δ) / (N : ℝ)) + ((m - 1 : ℕ) : ℝ) * ((1 - δ) / (N : ℝ)) := by
      simp only [B, sumLen_cons, b_left, b_right, hsumMid]
      ring
    rw [hsumG, hsumB]
    have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub hm_pos, Nat.cast_one]
    rw [hm1, hm_real]
    field_simp
    ring
  · -- Lower bound on sumLen G
    have hsumG : sumLen G = (m : ℝ) * (δ / (N : ℝ)) := by
      simp only [sumLen, G, List.map_map]
      have hconst : ((fun I : ℝ × ℝ => I.2 - I.1) ∘
          fun i : ℕ => ((q i : ℝ) / (N : ℝ), ((q i : ℝ) + δ) / (N : ℝ))) =
          fun _ => δ / (N : ℝ) := by
        funext i
        dsimp
        field_simp
        ring
      rw [hconst, List.map_const', List.length_range, List.sum_replicate, nsmul_eq_mul]
    rw [hsumG, hm_real]
    have hmul := mul_le_mul_of_nonneg_right hdiff_real (div_nonneg hδ0.le hNpos.le)
    have heq : (1 / 2 : ℝ) * ((N : ℝ) * (v - u)) * (δ / (N : ℝ)) = (δ / 2) * (v - u) := by
      field_simp
    linarith

private lemma split_step_list (L : List (ℝ × ℝ)) (δ : ℝ) (N M : ℕ)
    (hN : 0 < N) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hM : 6 ≤ (M : ℝ) * (δ / (N : ℝ)))
    (hL : ∀ I ∈ L, 6 ≤ (N : ℝ) * (I.2 - I.1)) :
    ∃ G B : List (ℝ × ℝ),
      (∀ I ∈ G, 6 ≤ (M : ℝ) * (I.2 - I.1)) ∧
      (∀ I ∈ G, ∃ I₀ ∈ L, Ico I.1 I.2 ⊆ Ico I₀.1 I₀.2) ∧
      (∀ I ∈ G, ∀ α ∈ Ico I.1 I.2, Int.fract (α * (N : ℝ)) ∈ Ico 0 δ) ∧
      (∀ I ∈ B, 6 ≤ (M : ℝ) * (I.2 - I.1)) ∧
      (∀ I₀ ∈ L, ∀ α ∈ Ico I₀.1 I₀.2,
        (∃ I ∈ G, α ∈ Ico I.1 I.2) ∨ (∃ I ∈ B, α ∈ Ico I.1 I.2)) ∧
      sumLen G + sumLen B = sumLen L ∧
      (δ / 2) * sumLen L ≤ sumLen G := by
  induction L with
  | nil =>
    refine ⟨[], [], by simp, by simp, by simp, by simp, by simp, by simp [sumLen], by simp [sumLen]⟩
  | cons I₀ L ih =>
    have hI₀ : 6 ≤ (N : ℝ) * (I₀.2 - I₀.1) := hL I₀ List.mem_cons_self
    have hL' : ∀ I ∈ L, 6 ≤ (N : ℝ) * (I.2 - I.1) :=
      fun I hI => hL I (List.mem_cons_of_mem I₀ hI)
    obtain ⟨G₁, B₁, hG1len, hG1sub, hG1fr, hB1len, hcov1, hsum1, hge1⟩ :=
      split_step I₀.1 I₀.2 δ N hN hδ0 hδ1 hI₀
    obtain ⟨G₂, B₂, hG2len, hG2sub, hG2fr, hB2len, hcov2, hsum2, hge2⟩ := ih hL'
    refine ⟨G₁ ++ G₂, B₁ ++ B₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro I hI
      rcases List.mem_append.mp hI with hI | hI
      · rw [hG1len I hI]; exact hM
      · exact hG2len I hI
    · intro I hI
      rcases List.mem_append.mp hI with hI | hI
      · exact ⟨I₀, List.mem_cons_self, hG1sub I hI⟩
      · obtain ⟨J, hJ, hsub⟩ := hG2sub I hI
        exact ⟨J, List.mem_cons_of_mem I₀ hJ, hsub⟩
    · intro I hI α hα
      rcases List.mem_append.mp hI with hI | hI
      · exact hG1fr I hI α hα
      · exact hG2fr I hI α hα
    · intro I hI
      rcases List.mem_append.mp hI with hI | hI
      · have hle := hB1len I hI
        have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
        exact le_trans hM (mul_le_mul_of_nonneg_left hle hM0)
      · exact hB2len I hI
    · intro J hJ α hα
      rcases List.mem_cons.mp hJ with rfl | hJ
      · rcases hcov1 α hα with ⟨I, hI, hαI⟩ | ⟨I, hI, hαI⟩
        · exact Or.inl ⟨I, List.mem_append_left G₂ hI, hαI⟩
        · exact Or.inr ⟨I, List.mem_append_left B₂ hI, hαI⟩
      · rcases hcov2 J hJ α hα with ⟨I, hI, hαI⟩ | ⟨I, hI, hαI⟩
        · exact Or.inl ⟨I, List.mem_append_right G₁ hI, hαI⟩
        · exact Or.inr ⟨I, List.mem_append_right B₁ hI, hαI⟩
    · rw [sumLen_append, sumLen_append, sumLen_cons]
      linarith
    · rw [sumLen_append, sumLen_cons]
      linarith

private lemma split_block (a : ℕ → ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (J : ℕ)
    (ha_pos : ∀ j ≥ J + 1, 0 < a j)
    (ha_mono : ∀ j ≥ J + 1, a j ≤ a (j + 1))
    (ha_step : ∀ j ≥ J + 1, 6 ≤ (a (j + 1) : ℝ) * (δ / (a j : ℝ)))
    (k : ℕ) (u v : ℝ) (hLen : 6 ≤ (a (J + 1) : ℝ) * (v - u)) :
    ∃ G B : List (ℝ × ℝ),
      (∀ I ∈ G, 6 ≤ (a (J + k + 1) : ℝ) * (I.2 - I.1)) ∧
      (∀ I ∈ G, ∀ α ∈ Ico I.1 I.2,
        ∀ j ∈ Finset.Ioc J (J + k), Int.fract (α * (a j : ℝ)) ∈ Ico 0 δ) ∧
      (∀ I ∈ B, 6 ≤ (a (J + k + 1) : ℝ) * (I.2 - I.1)) ∧
      (∀ α ∈ Ico u v, (∃ I ∈ G, α ∈ Ico I.1 I.2) ∨ (∃ I ∈ B, α ∈ Ico I.1 I.2)) ∧
      sumLen G + sumLen B = v - u ∧
      (δ / 2) ^ k * (v - u) ≤ sumLen G := by
  induction k with
  | zero =>
    refine ⟨[(u, v)], [], ?_, ?_, by simp, ?_, ?_, ?_⟩
    · intro I hI
      rw [List.mem_singleton] at hI
      subst hI
      simpa using hLen
    · intro I _ α _ j hj
      simp at hj
    · intro α hα
      exact Or.inl ⟨(u, v), List.mem_singleton.mpr rfl, hα⟩
    · simp [sumLen]
    · simp [sumLen]
  | succ k ih =>
    obtain ⟨G, B, hGlen, hGfr, hBlen, hcov, hsum, hge⟩ := ih
    have hj_ge : J + k + 1 ≥ J + 1 := by omega
    obtain ⟨G', B', hG'len, hG'sub, hG'fr, hB'len, hcov', hsum', hge'⟩ :=
      split_step_list G δ (a (J + k + 1)) (a (J + k + 2))
        (ha_pos _ hj_ge) hδ0 hδ1 (ha_step _ hj_ge) hGlen
    refine ⟨G', B ++ B', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [Nat.add_assoc] using hG'len
    · intro I hI α hα j hj
      rw [Finset.mem_Ioc] at hj
      by_cases hjeq : j = J + k + 1
      · subst hjeq
        exact hG'fr I hI α hα
      · have hjlt : j ∈ Finset.Ioc J (J + k) := by
          rw [Finset.mem_Ioc]
          omega
        obtain ⟨I₀, hI₀, hsub⟩ := hG'sub I hI
        exact hGfr I₀ hI₀ α (hsub hα) j hjlt
    · intro I hI
      rcases List.mem_append.mp hI with hI | hI
      · have h1 := hBlen I hI
        have hpos : (0 : ℝ) < (a (J + k + 1) : ℝ) := Nat.cast_pos.mpr (ha_pos _ hj_ge)
        have hnonneg : 0 ≤ I.2 - I.1 := by nlinarith
        have hle : (a (J + k + 1) : ℝ) ≤ (a (J + k + 2) : ℝ) :=
          Nat.cast_le.mpr (ha_mono _ hj_ge)
        have : (a (J + k + 1) : ℝ) * (I.2 - I.1) ≤ (a (J + k + 2) : ℝ) * (I.2 - I.1) :=
          mul_le_mul_of_nonneg_right hle hnonneg
        have heq : J + (k + 1) + 1 = J + k + 2 := by omega
        rw [heq]
        linarith
      · have heq : J + (k + 1) + 1 = J + k + 2 := by omega
        rw [heq]
        exact hB'len I hI
    · intro α hα
      rcases hcov α hα with ⟨I₀, hI₀, hα0⟩ | ⟨I₀, hI₀, hα0⟩
      · rcases hcov' I₀ hI₀ α hα0 with ⟨I, hI, hαI⟩ | ⟨I, hI, hαI⟩
        · exact Or.inl ⟨I, hI, hαI⟩
        · exact Or.inr ⟨I, List.mem_append_right B hI, hαI⟩
      · exact Or.inr ⟨I₀, List.mem_append_left B' hI₀, hα0⟩
    · rw [sumLen_append]
      linarith
    · have hmul := mul_le_mul_of_nonneg_left hge (by linarith : (0 : ℝ) ≤ δ / 2)
      rw [pow_succ']
      linarith

private lemma refine_bad_list (a : ℕ → ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (J K : ℕ)
    (ha_pos : ∀ j ≥ J + 1, 0 < a j)
    (ha_mono : ∀ j ≥ J + 1, a j ≤ a (j + 1))
    (ha_step : ∀ j ≥ J + 1, 6 ≤ (a (j + 1) : ℝ) * (δ / (a j : ℝ)))
    (L : List (ℝ × ℝ)) (hL : ∀ I ∈ L, 6 ≤ (a (J + 1) : ℝ) * (I.2 - I.1)) :
    ∃ L' : List (ℝ × ℝ),
      (∀ I ∈ L', 6 ≤ (a (J + K + 1) : ℝ) * (I.2 - I.1)) ∧
      sumLen L' ≤ (1 - (δ / 2) ^ K) * sumLen L ∧
      (∀ I ∈ L, ∀ α ∈ Ico I.1 I.2,
        (¬ ∀ j ∈ Finset.Ioc J (J + K), Int.fract (α * (a j : ℝ)) ∈ Ico 0 δ) →
        ∃ I' ∈ L', α ∈ Ico I'.1 I'.2) := by
  induction L with
  | nil =>
    refine ⟨[], by simp, by simp [sumLen], by simp⟩
  | cons I₀ L ih =>
    have hI₀ := hL I₀ List.mem_cons_self
    have hL' : ∀ I ∈ L, 6 ≤ (a (J + 1) : ℝ) * (I.2 - I.1) :=
      fun I hI => hL I (List.mem_cons_of_mem I₀ hI)
    obtain ⟨G, B, _, hGfr, hBlen, hcov, hsum, hge⟩ :=
      split_block a δ hδ0 hδ1 J ha_pos ha_mono ha_step K I₀.1 I₀.2 hI₀
    obtain ⟨L', hL'len, hL'sum, hL'cov⟩ := ih hL'
    refine ⟨B ++ L', ?_, ?_, ?_⟩
    · intro I hI
      rcases List.mem_append.mp hI with hI | hI
      · exact hBlen I hI
      · exact hL'len I hI
    · rw [sumLen_append, sumLen_cons]
      have hBsum : sumLen B ≤ (1 - (δ / 2) ^ K) * (I₀.2 - I₀.1) := by linarith
      linarith
    · intro I hI α hα hfail
      rcases List.mem_cons.mp hI with rfl | hI
      · rcases hcov α hα with ⟨I', hI', hα'⟩ | ⟨I', hI', hα'⟩
        · exact absurd (hGfr I' hI' α hα') hfail
        · exact ⟨I', List.mem_append_left L' hI', hα'⟩
      · obtain ⟨I', hI', hα'⟩ := hL'cov I hI α hα hfail
        exact ⟨I', List.mem_append_right B hI', hα'⟩

private lemma bad_cover_iter (a : ℕ → ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (j₀ K : ℕ) (m : ℤ)
    (ha_pos : ∀ j ≥ j₀ + 1, 0 < a j)
    (ha_mono : ∀ j ≥ j₀ + 1, a j ≤ a (j + 1))
    (ha_step : ∀ j ≥ j₀ + 1, 6 ≤ (a (j + 1) : ℝ) * (δ / (a j : ℝ)))
    (ha_init : 6 ≤ (a (j₀ + 1) : ℝ)) (T : ℕ) :
    ∃ L : List (ℝ × ℝ),
      (∀ I ∈ L, 6 ≤ (a (j₀ + T * K + 1) : ℝ) * (I.2 - I.1)) ∧
      sumLen L ≤ (1 - (δ / 2) ^ K) ^ T ∧
      (∀ α ∈ Ico (m : ℝ) ((m : ℝ) + 1),
        (¬ ∃ J : ℕ, ∀ j ∈ Finset.Ioc J (J + K), Int.fract (α * (a j : ℝ)) ∈ Ico 0 δ) →
        ∃ I ∈ L, α ∈ Ico I.1 I.2) := by
  induction T with
  | zero =>
    refine ⟨[(m, (m : ℝ) + 1)], ?_, ?_, ?_⟩
    · intro I hI
      rw [List.mem_singleton] at hI
      subst hI
      simpa using ha_init
    · simp [sumLen]
    · intro α hα _
      exact ⟨(m, (m : ℝ) + 1), List.mem_singleton.mpr rfl, hα⟩
  | succ T ih =>
    obtain ⟨L, hLlen, hLsum, hLcov⟩ := ih
    set J := j₀ + T * K
    have hJ : j₀ + 1 ≤ J + 1 := by omega
    obtain ⟨L', hL'len, hL'sum, hL'cov⟩ :=
      refine_bad_list a δ hδ0 hδ1 J K
        (fun j hj => ha_pos j (by omega))
        (fun j hj => ha_mono j (by omega))
        (fun j hj => ha_step j (by omega))
        L hLlen
    have hJeq : J + K + 1 = j₀ + (T + 1) * K + 1 := by
      simp only [J]
      ring
    refine ⟨L', ?_, ?_, ?_⟩
    · simpa [hJeq] using hL'len
    · have hbase_nonneg : 0 ≤ 1 - (δ / 2) ^ K := by
        have hlt : δ / 2 ≤ 1 := by linarith
        have hpow : (δ / 2) ^ K ≤ 1 := pow_le_one₀ (by linarith) hlt
        linarith
      have hmul := mul_le_mul_of_nonneg_left hLsum hbase_nonneg
      rw [pow_succ']
      linarith
    · intro α hα hfail
      obtain ⟨I, hI, hαI⟩ := hLcov α hα hfail
      have hfailJ : ¬ ∀ j ∈ Finset.Ioc J (J + K), Int.fract (α * (a j : ℝ)) ∈ Ico 0 δ :=
        fun h => hfail ⟨J, h⟩
      exact hL'cov I hI α hαI hfailJ

private lemma volume_bad_Ico_eq_zero (a : ℕ → ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (j₀ K : ℕ) (hK : 1 ≤ K) (m : ℤ)
    (ha_pos : ∀ j ≥ j₀ + 1, 0 < a j)
    (ha_mono : ∀ j ≥ j₀ + 1, a j ≤ a (j + 1))
    (ha_step : ∀ j ≥ j₀ + 1, 6 ≤ (a (j + 1) : ℝ) * (δ / (a j : ℝ)))
    (ha_init : 6 ≤ (a (j₀ + 1) : ℝ)) :
    volume {α ∈ Ico (m : ℝ) ((m : ℝ) + 1) |
      ¬ ∃ J : ℕ, ∀ j ∈ Finset.Ioc J (J + K), Int.fract (α * (a j : ℝ)) ∈ Ico 0 δ} = 0 := by
  set S : Set ℝ := {α ∈ Ico (m : ℝ) ((m : ℝ) + 1) |
    ¬ ∃ J : ℕ, ∀ j ∈ Finset.Ioc J (J + K), Int.fract (α * (a j : ℝ)) ∈ Ico 0 δ}
  have hle_T : ∀ T : ℕ, volume S ≤ ENNReal.ofReal ((1 - (δ / 2) ^ K) ^ T) := by
    intro T
    obtain ⟨L, hLlen, hLsum, hLcov⟩ :=
      bad_cover_iter a δ hδ0 hδ1 j₀ K m ha_pos ha_mono ha_step ha_init T
    have hsub : S ⊆ ⋃ I ∈ L, Ico I.1 I.2 := by
      intro α hα
      obtain ⟨I, hI, hαI⟩ := hLcov α hα.1 hα.2
      exact mem_biUnion hI hαI
    have hnonneg : ∀ I ∈ L, I.1 ≤ I.2 := by
      intro I hI
      have h1 := hLlen I hI
      have hpos : (0 : ℝ) < (a (j₀ + T * K + 1) : ℝ) :=
        Nat.cast_pos.mpr (ha_pos _ (by omega))
      nlinarith
    calc
      volume S ≤ volume (⋃ I ∈ L, Ico I.1 I.2) := measure_mono hsub
      _ ≤ ENNReal.ofReal (sumLen L) := volume_biUnion_list_le L hnonneg
      _ ≤ ENNReal.ofReal ((1 - (δ / 2) ^ K) ^ T) := ENNReal.ofReal_le_ofReal hLsum
  have hbase_lt : 1 - (δ / 2) ^ K < 1 := by
    have : 0 < (δ / 2) ^ K := pow_pos (by linarith) K
    linarith
  have hbase_nonneg : 0 ≤ 1 - (δ / 2) ^ K := by
    have hlt : δ / 2 ≤ 1 := by linarith
    have hpow : (δ / 2) ^ K ≤ 1 := pow_le_one₀ (by linarith) hlt
    linarith
  have htend_real : Tendsto (fun T : ℕ => (1 - (δ / 2) ^ K) ^ T) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase_nonneg hbase_lt
  have htend : Tendsto (fun T : ℕ => ENNReal.ofReal ((1 - (δ / 2) ^ K) ^ T)) atTop (nhds 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal htend_real
  have hzero : volume S ≤ 0 :=
    ge_of_tendsto' htend hle_T
  exact nonpos_iff_eq_zero.mp hzero

private lemma ae_all_blocks (a : ℕ → ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (j₀ : ℕ)
    (ha_pos : ∀ j ≥ j₀ + 1, 0 < a j)
    (ha_mono : ∀ j ≥ j₀ + 1, a j ≤ a (j + 1))
    (ha_step : ∀ j ≥ j₀ + 1, 6 ≤ (a (j + 1) : ℝ) * (δ / (a j : ℝ)))
    (ha_init : 6 ≤ (a (j₀ + 1) : ℝ)) :
    ∀ᵐ α : ℝ, ∀ K : ℕ,
      ∃ J : ℕ, ∀ j ∈ Finset.Ioc J (J + K), Int.fract (α * (a j : ℝ)) ∈ Ico 0 δ := by
  rw [ae_all_iff]
  intro K
  rcases K with _ | K'
  · exact Eventually.of_forall fun _ => ⟨0, fun j hj => by simp at hj⟩
  · rw [ae_iff]
    have hsub : {α : ℝ | ¬ ∃ J : ℕ,
        ∀ j ∈ Finset.Ioc J (J + (K' + 1)), Int.fract (α * (a j : ℝ)) ∈ Ico 0 δ} ⊆
        ⋃ m : ℤ, {α ∈ Ico (m : ℝ) ((m : ℝ) + 1) |
          ¬ ∃ J : ℕ, ∀ j ∈ Finset.Ioc J (J + (K' + 1)), Int.fract (α * (a j : ℝ)) ∈ Ico 0 δ} := by
      intro α hα
      refine mem_iUnion.mpr ⟨⌊α⌋, ?_, hα⟩
      exact ⟨Int.floor_le α, Int.lt_floor_add_one α⟩
    refine measure_mono_null hsub (measure_iUnion_null fun m => ?_)
    exact volume_bad_Ico_eq_zero a δ hδ0 hδ1 j₀ (K' + 1) (Nat.succ_pos K') m
      ha_pos ha_mono ha_step ha_init

private lemma not_isWellDistributed_of_blocks (n : ℕ → ℕ) (r : ℕ) (hr : 1 ≤ r) (α : ℝ)
    (hblocks : ∀ K : ℕ, ∃ J : ℕ, ∀ j ∈ Finset.Ioc J (J + K),
      Int.fract (α * (n (r * j) : ℝ)) ∈ Ico 0 (1 / (4 * (r : ℝ)))) :
    ¬ Erdos997.IsWellDistributed (fun k ↦ Int.fract (α * (n k : ℝ))) := by
  intro hwd
  set δ : ℝ := 1 / (4 * (r : ℝ))
  have hrpos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hδpos : 0 < δ := by positivity
  have hδle1 : δ ≤ 1 := by
    dsimp [δ]
    rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ (r : ℝ) := Nat.one_le_cast.mpr hr
    linarith
  have hspec := hwd δ hδpos
  rw [Filter.eventually_atTop] at hspec
  obtain ⟨K₀, hK₀⟩ := hspec
  set K : ℕ := max K₀ 1
  have hK1 : 1 ≤ K := le_max_right K₀ 1
  have hK0 : K₀ ≤ K := le_max_left K₀ 1
  have hrK : K₀ ≤ r * K := le_trans hK0 (Nat.le_mul_of_pos_left K hr)
  obtain ⟨J, hJ⟩ := hblocks K
  have hineq := hK₀ (r * K) hrK (r * J) 0 δ le_rfl hδpos.le hδle1
  set count := (Finset.Ioc (r * J) (r * J + r * K)).filter
    (fun m ↦ Int.fract (α * (n m : ℝ)) ∈ Ico 0 δ)
  have hcard : K ≤ count.card := by
    have hinj : Function.Injective (fun j : ℕ => r * j) :=
      fun j₁ j₂ h => Nat.eq_of_mul_eq_mul_left hr h
    have hsub : (Finset.Ioc J (J + K)).image (fun j => r * j) ⊆ count := by
      intro m hm
      rcases Finset.mem_image.mp hm with ⟨j, hj, rfl⟩
      rw [Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨?_, ?_⟩, hJ j hj⟩
      · rw [Finset.mem_Ioc] at hj
        exact Nat.mul_lt_mul_of_pos_left hj.1 hr
      · rw [Finset.mem_Ioc] at hj
        calc
          r * j ≤ r * (J + K) := Nat.mul_le_mul_left r hj.2
          _ = r * J + r * K := Nat.mul_add r J K
    calc
      K = (Finset.Ioc J (J + K)).card := by simp
      _ = ((Finset.Ioc J (J + K)).image (fun j => r * j)).card :=
        (Finset.card_image_of_injective _ hinj).symm
      _ ≤ count.card := Finset.card_le_card hsub
  have hcard_real : (K : ℝ) ≤ (count.card : ℝ) := Nat.cast_le.mpr hcard
  have hKpos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK1
  have hmul_eq : δ * ((r * K : ℕ) : ℝ) = (K : ℝ) / 4 := by
    dsimp [δ]
    push_cast
    field_simp
  have hsub_ge : (3 / 4 : ℝ) * (K : ℝ) ≤ (count.card : ℝ) - (δ - 0) * ((r * K : ℕ) : ℝ) := by
    rw [sub_zero, hmul_eq]
    linarith
  have habs : (3 / 4 : ℝ) * (K : ℝ) ≤ |(count.card : ℝ) - (δ - 0) * ((r * K : ℕ) : ℝ)| :=
    le_trans hsub_ge (le_abs_self _)
  dsimp only [count] at habs
  rw [hmul_eq] at hineq
  linarith

end Erdos997LacunaryProof

theorem OMA.solution : type_of% @Erdos997.erdos_997.variants.lacunary := by
  intro n h
  obtain ⟨c, hc, hfl⟩ := h
  rw [Filter.eventually_atTop] at hfl
  obtain ⟨N₀, hN₀⟩ := hfl
  obtain ⟨r, hr1, hcr⟩ := Erdos997LacunaryProof.exists_pow_ge_mul c hc
  set δ : ℝ := 1 / (4 * (r : ℝ))
  have hrpos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr1
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 2 := by
    dsimp [δ]
    have hr1' : (1 : ℝ) ≤ (r : ℝ) := Nat.one_le_cast.mpr hr1
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hn_pos : ∀ k ≥ N₀ + 1, 0 < n k := by
    intro k hk
    have h1 := hN₀ (k - 1) (by omega)
    have h2 : k - 1 + 1 = k := by omega
    rw [h2] at h1
    have h0 : (0 : ℝ) ≤ c * (n (k - 1) : ℝ) := by positivity
    have hgt : (0 : ℝ) < (n k : ℝ) := lt_of_le_of_lt h0 h1
    exact_mod_cast hgt
  have hn_pow : ∀ k ≥ N₀ + 1, ∀ t : ℕ, c ^ t * (n k : ℝ) ≤ (n (k + t) : ℝ) := by
    intro k hk t
    induction t with
    | zero => simp
    | succ t ih =>
      have hstep := hN₀ (k + t) (by omega)
      have hmul : c * (c ^ t * (n k : ℝ)) ≤ c * (n (k + t) : ℝ) :=
        mul_le_mul_of_nonneg_left ih (by linarith)
      have heq : k + (t + 1) = k + t + 1 := by omega
      rw [heq, pow_succ']
      linarith
  let a : ℕ → ℕ := fun j => n (r * j)
  set j₀ : ℕ := N₀ + 1
  have ha_pos : ∀ j ≥ j₀ + 1, 0 < a j := by
    intro j hj
    exact hn_pos (r * j) (le_trans (by omega) (Nat.le_mul_of_pos_left j hr1))
  have ha_mul : ∀ j ≥ j₀, (24 * (r : ℝ)) * (a j : ℝ) ≤ (a (j + 1) : ℝ) := by
    intro j hj
    have hge : N₀ + 1 ≤ r * j := le_trans (by omega) (Nat.le_mul_of_pos_left j hr1)
    have h1 := hn_pow (r * j) hge r
    have heq : r * j + r = r * (j + 1) := by ring
    rw [heq] at h1
    have h2 : (24 * (r : ℝ)) * (a j : ℝ) ≤ c ^ r * (a j : ℝ) :=
      mul_le_mul_of_nonneg_right hcr (Nat.cast_nonneg _)
    exact le_trans h2 h1
  have ha_mono : ∀ j ≥ j₀ + 1, a j ≤ a (j + 1) := by
    intro j hj
    have h1 := ha_mul j (by omega)
    have hr1' : (1 : ℝ) ≤ (r : ℝ) := Nat.one_le_cast.mpr hr1
    have h2 : (a j : ℝ) ≤ (a (j + 1) : ℝ) := by nlinarith
    exact_mod_cast h2
  have ha_step : ∀ j ≥ j₀ + 1, 6 ≤ (a (j + 1) : ℝ) * (δ / (a j : ℝ)) := by
    intro j hj
    have h1 := ha_mul j (by omega)
    have haj : (0 : ℝ) < (a j : ℝ) := Nat.cast_pos.mpr (ha_pos j hj)
    have h2 : (24 * (r : ℝ)) * (a j : ℝ) * (δ / (a j : ℝ)) ≤
        (a (j + 1) : ℝ) * (δ / (a j : ℝ)) :=
      mul_le_mul_of_nonneg_right h1 (div_nonneg hδ0.le haj.le)
    have heq : (24 * (r : ℝ)) * (a j : ℝ) * (δ / (a j : ℝ)) = 6 := by
      dsimp [δ]
      field_simp
      ring
    linarith
  have ha_init : 6 ≤ (a (j₀ + 1) : ℝ) := by
    have h1 := ha_mul j₀ le_rfl
    have haj0 : 0 < a j₀ :=
      hn_pos (r * j₀) (le_trans le_rfl (Nat.le_mul_of_pos_left j₀ hr1))
    have haj0' : (1 : ℝ) ≤ (a j₀ : ℝ) := Nat.one_le_cast.mpr haj0
    have hr1' : (1 : ℝ) ≤ (r : ℝ) := Nat.one_le_cast.mpr hr1
    nlinarith
  filter_upwards [Erdos997LacunaryProof.ae_all_blocks a δ hδ0 hδ1 j₀
    ha_pos ha_mono ha_step ha_init] with α hα
  exact Erdos997LacunaryProof.not_isWellDistributed_of_blocks n r hr1 α hα
