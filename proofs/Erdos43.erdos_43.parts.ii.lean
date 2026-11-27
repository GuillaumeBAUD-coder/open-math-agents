import FormalConjectures.ErdosProblems.«43»

/-!
Erdős 43 (ii) : réponse négative de K. Barreto (fil 43 du forum erdosproblems.com).
On découpe par parité un ensemble de Sidon de Ruzsa modulo p(p-1) (au lieu de Bose–Chowla),
puis on conclut avec la borne d'Erdős–Turán–Lindström, recopiée de
proofs/Erdos30.erdos_30.variants.erdos_turan.lean (auteur @michielkosters).
-/

open scoped Pointwise

lemma oma_sum_ge_of_pos_et (D : Finset ℕ) (hD : ∀ x ∈ D, 1 ≤ x) :
    D.card * (D.card + 1) ≤ 2 * ∑ x ∈ D, x := by
  let e := D.orderIsoOfFin rfl
  have hge : ∀ i : ℕ, (hi : i < D.card) → i + 1 ≤ (e ⟨i, hi⟩ : ℕ) := by
    intro i
    induction i with
    | zero =>
      intro hi
      exact hD _ (e ⟨0, hi⟩).2
    | succ i ih =>
      intro hi
      have hi' : i < D.card := by omega
      have hprev := ih hi'
      have hlt : (e ⟨i, hi'⟩ : ℕ) < (e ⟨i + 1, hi⟩ : ℕ) :=
        e.strictMono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self i))
      omega
  have hsum_eq : ∑ x ∈ D, x = ∑ i : Fin D.card, (e i : ℕ) := by
    rw [← Finset.sum_coe_sort D (fun x => x)]
    exact (Fintype.sum_equiv e.toEquiv (fun i => (e i : ℕ)) (fun x : ↥D => (x : ℕ)) (fun _ => rfl)).symm
  rw [hsum_eq]
  have hle : ∑ i : Fin D.card, (i.val + 1) ≤ ∑ i : Fin D.card, (e i : ℕ) :=
    Finset.sum_le_sum fun i _ => hge i.val i.isLt
  have hid : 2 * ∑ i : Fin D.card, (i.val + 1) = D.card * (D.card + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => i + 1)]
    have : 2 * ∑ i ∈ Finset.range D.card, (i + 1) = D.card * (D.card + 1) := by
      induction D.card with
      | zero => simp
      | succ m ihm =>
        rw [Finset.sum_range_succ, mul_add, ihm]
        ring
    exact this
  omega

lemma oma_sidon_lindstrom_et (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N)
    (hS : IsSidon (A : Set ℕ)) :
    (A.card : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 := by
  by_cases hN0 : N = 0
  · subst hN0
    have hAe : A = ∅ := Finset.subset_empty.mp (by simpa using hA)
    simp [hAe]
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
  have hNreal : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hNpos
  set k := A.card
  set u : ℝ := (N : ℝ) ^ (4⁻¹ : ℝ)
  set r : ℕ := Nat.floor u + 1
  have hu_nonneg : 0 ≤ u := by positivity
  have hr_gt : u < (r : ℝ) := by
    have := Nat.lt_floor_add_one u
    push_cast [r]
    exact this
  have hr_le : (r : ℝ) ≤ u + 1 := by
    have := Nat.floor_le hu_nonneg
    push_cast [r]
    linarith
  have hr_pos : 1 ≤ r := by omega
  by_cases hkr : k ≤ r
  · have h1 : (k : ℝ) ≤ (r : ℝ) := Nat.cast_le.mpr hkr
    have h2 : (0 : ℝ) ≤ (N : ℝ).sqrt := Real.sqrt_nonneg _
    linarith
  have hrk : r < k := by omega
  let e := A.orderIsoOfFin rfl
  let a : Fin k → ℕ := fun i => (e i : ℕ)
  have ha_mono : StrictMono a := fun i j hij => e.strictMono hij
  have ha_mem : ∀ i : Fin k, a i ∈ A := fun i => (e i).2
  have ha_le : ∀ i : Fin k, a i ≤ N := fun i => (Finset.mem_Icc.mp (hA (ha_mem i))).2
  let P : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 r).biUnion fun d => (Finset.range (k - d)).image fun j => (d, j)
  have hP_mem : ∀ p ∈ P, 1 ≤ p.1 ∧ p.1 ≤ r ∧ p.2 + p.1 < k := by
    intro ⟨d, j⟩ hp
    simp only [P, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image, Finset.mem_range] at hp
    rcases hp with ⟨d', ⟨hd1, hd2⟩, j', hj', heq⟩
    rcases Prod.ext_iff.mp heq with ⟨rfl, rfl⟩
    exact ⟨hd1, hd2, by omega⟩
  let diffFn : ℕ × ℕ → ℕ := fun p =>
    if h : p.2 + p.1 < k then a ⟨p.2 + p.1, h⟩ - a ⟨p.2, by omega⟩ else 0
  have hdiff_inj : Set.InjOn diffFn (P : Set (ℕ × ℕ)) := by
    intro ⟨d₁, j₁⟩ h1 ⟨d₂, j₂⟩ h2 heq
    have hm1 := hP_mem (d₁, j₁) (Finset.mem_coe.mp h1)
    have hm2 := hP_mem (d₂, j₂) (Finset.mem_coe.mp h2)
    have hlt1 : a ⟨j₁, by omega⟩ < a ⟨j₁ + d₁, hm1.2.2⟩ :=
      ha_mono (Fin.mk_lt_mk.mpr (by omega))
    have hlt2 : a ⟨j₂, by omega⟩ < a ⟨j₂ + d₂, hm2.2.2⟩ :=
      ha_mono (Fin.mk_lt_mk.mpr (by omega))
    simp only [diffFn, dif_pos hm1.2.2, dif_pos hm2.2.2] at heq
    have hpair := Finset.IsSidon.eq_of_tsub hS
      (ha_mem ⟨j₁ + d₁, hm1.2.2⟩) (ha_mem ⟨j₁, by omega⟩)
      (ha_mem ⟨j₂ + d₂, hm2.2.2⟩) (ha_mem ⟨j₂, by omega⟩)
      hlt1 hlt2 heq
    have hj_eq : j₁ = j₂ := by
      have := ha_mono.injective hpair.2
      exact congrArg Fin.val this
    have hjd_eq : j₁ + d₁ = j₂ + d₂ := by
      have := ha_mono.injective hpair.1
      exact congrArg Fin.val this
    ext <;> omega
  let D : Finset ℕ := P.image diffFn
  have hD_card : D.card = P.card := Finset.card_image_of_injOn hdiff_inj
  have hD_pos : ∀ x ∈ D, 1 ≤ x := by
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨⟨d, j⟩, hp, rfl⟩
    have hm := hP_mem (d, j) hp
    have hlt : a ⟨j, by omega⟩ < a ⟨j + d, hm.2.2⟩ :=
      ha_mono (Fin.mk_lt_mk.mpr (by omega))
    simp only [diffFn, dif_pos hm.2.2]
    omega
  have hP_card : P.card = r * k - r * (r + 1) / 2 := by
    have hdisj : (Finset.Icc 1 r : Set ℕ).PairwiseDisjoint fun d =>
        (Finset.range (k - d)).image fun j => (d, j) := by
      intro d₁ _ d₂ _ hne
      dsimp [Function.onFun]
      rw [Finset.disjoint_left]
      intro ⟨a₁, b₁⟩ h1 h2
      simp only [Finset.mem_image] at h1 h2
      rcases h1 with ⟨_, _, e1⟩
      rcases h2 with ⟨_, _, e2⟩
      exact hne (congrArg Prod.fst (e1.trans e2.symm))
    dsimp [P]
    rw [Finset.card_biUnion hdisj]
    have hterm : ∀ d ∈ Finset.Icc 1 r,
        ((Finset.range (k - d)).image fun j => (d, j)).card = k - d := by
      intro d _
      rw [Finset.card_image_of_injective]
      · exact Finset.card_range _
      · intro j₁ j₂ h; exact congrArg Prod.snd h
    rw [Finset.sum_congr rfl hterm]
    have hsum_d : ∑ d ∈ Finset.Icc 1 r, (k - d) = r * k - ∑ d ∈ Finset.Icc 1 r, d := by
      have h1 : ∑ d ∈ Finset.Icc 1 r, (k - d) + ∑ d ∈ Finset.Icc 1 r, d =
          ∑ d ∈ Finset.Icc 1 r, k := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun d hd => ?_
        have hdle : d ≤ k := by
          have := (Finset.mem_Icc.mp hd).2
          omega
        exact Nat.sub_add_cancel hdle
      have h2 : ∑ _d ∈ Finset.Icc 1 r, k = r * k := by
        simp [Nat.card_Icc]
      omega
    have htri : 2 * ∑ d ∈ Finset.Icc 1 r, d = r * (r + 1) := by
      induction r with
      | zero => simp
      | succ m ihm =>
        rw [Finset.sum_Icc_succ_top (by omega), mul_add, ihm]
        ring
    rw [hsum_d, show ∑ d ∈ Finset.Icc 1 r, d = r * (r + 1) / 2 by omega]
  have h_lower := oma_sum_ge_of_pos_et D hD_pos
  rw [hD_card] at h_lower
  have hsum_D_eq : ∑ x ∈ D, x = ∑ p ∈ P, diffFn p := Finset.sum_image (fun x hx y hy h => hdiff_inj hx hy h)
  have h_upper_nat : ∑ p ∈ P, diffFn p ≤ (r * (r + 1) / 2) * N := by
    have hdisj : (Finset.Icc 1 r : Set ℕ).PairwiseDisjoint fun d =>
        (Finset.range (k - d)).image fun j => (d, j) := by
      intro d₁ _ d₂ _ hne
      dsimp [Function.onFun]
      rw [Finset.disjoint_left]
      intro ⟨a₁, b₁⟩ h1 h2
      simp only [Finset.mem_image] at h1 h2
      rcases h1 with ⟨_, _, e1⟩
      rcases h2 with ⟨_, _, e2⟩
      exact hne (congrArg Prod.fst (e1.trans e2.symm))
    dsimp [P]
    rw [Finset.sum_biUnion hdisj]
    have h_each : ∀ d ∈ Finset.Icc 1 r,
        ∑ p ∈ (Finset.range (k - d)).image (fun j => (d, j)), diffFn p ≤ d * N := by
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hdr : d ≤ r := (Finset.mem_Icc.mp hd).2
      have hdk : d < k := by omega
      rw [Finset.sum_image (fun j₁ _ j₂ _ h => congrArg Prod.snd h)]
      let a' : ℕ → ℝ := fun i => if h : i < k then (a ⟨i, h⟩ : ℝ) else 0
      have hcast_sum : ((∑ j ∈ Finset.range (k - d), diffFn (d, j) : ℕ) : ℝ) =
          ∑ j ∈ Finset.range (k - d), (a' (j + d) - a' j) := by
        rw [Nat.cast_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        have hjd : j + d < k := by omega
        have hj' : j < k := by omega
        have hle : a ⟨j, hj'⟩ ≤ a ⟨j + d, hjd⟩ :=
          (ha_mono.monotone (Fin.mk_le_mk.mpr (by omega)))
        simp only [diffFn, dif_pos hjd, a', dif_pos hjd, dif_pos hj']
        exact Nat.cast_sub hle
      have htele : ∑ j ∈ Finset.range (k - d), (a' (j + d) - a' j) ≤ (d : ℝ) * (N : ℝ) := by
        rw [Finset.sum_sub_distrib]
        have hshift : ∑ j ∈ Finset.range (k - d), a' (j + d) = ∑ i ∈ Finset.Ico d k, a' i := by
          refine Finset.sum_bij (fun j _ => j + d) ?_ ?_ ?_ ?_
          · intro j hj; rw [Finset.mem_range] at hj; rw [Finset.mem_Ico]; omega
          · intro j₁ _ j₂ _ h; omega
          · intro i hi; rw [Finset.mem_Ico] at hi; exact ⟨i - d, Finset.mem_range.mpr (by omega), by omega⟩
          · intro _ _; rfl
        rw [hshift]
        have hsplit1 : ∑ i ∈ Finset.Ico d k, a' i =
            ∑ i ∈ (Finset.Ico d k) ∩ (Finset.range (k - d)), a' i +
            ∑ i ∈ (Finset.Ico d k) \ (Finset.range (k - d)), a' i :=
          (Finset.sum_inter_add_sum_sdiff _ _ _).symm
        have hsplit2 : ∑ i ∈ Finset.range (k - d), a' i =
            ∑ i ∈ (Finset.range (k - d)) ∩ (Finset.Ico d k), a' i +
            ∑ i ∈ (Finset.range (k - d)) \ (Finset.Ico d k), a' i :=
          (Finset.sum_inter_add_sum_sdiff _ _ _).symm
        rw [hsplit1, hsplit2, Finset.inter_comm (Finset.range (k - d)) (Finset.Ico d k)]
        have hnonneg : 0 ≤ ∑ i ∈ (Finset.range (k - d)) \ (Finset.Ico d k), a' i := by
          refine Finset.sum_nonneg fun i _ => ?_
          dsimp [a']; split_ifs <;> positivity
        have hsub_ico : (Finset.Ico d k) \ (Finset.range (k - d)) ⊆ Finset.Ico (k - d) k := by
          intro x hx
          simp only [Finset.mem_sdiff, Finset.mem_Ico, Finset.mem_range] at hx ⊢
          omega
        have hcard_le : ((Finset.Ico d k) \ (Finset.range (k - d))).card ≤ d := by
          have := Finset.card_le_card hsub_ico
          rw [Nat.card_Ico] at this
          omega
        have hbound : ∑ i ∈ (Finset.Ico d k) \ (Finset.range (k - d)), a' i ≤
            ((Finset.Ico d k) \ (Finset.range (k - d))).card * (N : ℝ) := by
          calc ∑ i ∈ (Finset.Ico d k) \ (Finset.range (k - d)), a' i
            _ ≤ ∑ _i ∈ (Finset.Ico d k) \ (Finset.range (k - d)), (N : ℝ) := by
              refine Finset.sum_le_sum fun i hi => ?_
              have hik : i < k := (Finset.mem_Ico.mp (Finset.mem_sdiff.mp hi).1).2
              simp only [a', dif_pos hik]
              exact_mod_cast ha_le ⟨i, hik⟩
            _ = _ := by simp
        have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        have hcard_r : (((Finset.Ico d k) \ (Finset.range (k - d))).card : ℝ) ≤ (d : ℝ) :=
          Nat.cast_le.mpr hcard_le
        nlinarith
      exact_mod_cast hcast_sum.symm ▸ htele
    calc ∑ d ∈ Finset.Icc 1 r, ∑ p ∈ (Finset.range (k - d)).image (fun j => (d, j)), diffFn p
      _ ≤ ∑ d ∈ Finset.Icc 1 r, d * N := Finset.sum_le_sum h_each
      _ = (∑ d ∈ Finset.Icc 1 r, d) * N := (Finset.sum_mul _ _ _).symm
      _ = (r * (r + 1) / 2) * N := by
        congr 1
        have htri : 2 * ∑ d ∈ Finset.Icc 1 r, d = r * (r + 1) := by
          induction r with
          | zero => simp
          | succ m ihm =>
            rw [Finset.sum_Icc_succ_top (by omega), mul_add, ihm]
            ring
        omega
  have hineq_nat : P.card * (P.card + 1) ≤ r * (r + 1) * N := by
    have h1 : P.card * (P.card + 1) ≤ 2 * (r * (r + 1) / 2 * N) := by linarith
    have heven : 2 ∣ r * (r + 1) := Nat.even_mul_succ_self r |>.two_dvd
    have h2 : 2 * (r * (r + 1) / 2 * N) = r * (r + 1) * N := by
      rw [← mul_assoc, Nat.mul_div_cancel' heven]
    linarith
  have hP_real : (P.card : ℝ) = (r : ℝ) * (k : ℝ) - (r : ℝ) * ((r : ℝ) + 1) / 2 := by
    have heven : 2 ∣ r * (r + 1) := Nat.even_mul_succ_self r |>.two_dvd
    have hle : r * (r + 1) / 2 ≤ r * k := by
      have : r * (r + 1) ≤ 2 * (r * k) := by
        nlinarith [show r + 1 ≤ k by omega]
      exact Nat.div_le_of_le_mul this
    rw [hP_card, Nat.cast_sub hle, Nat.cast_div heven (by norm_num)]
    push_cast
    ring
  have hineq_real : (P.card : ℝ) ^ 2 ≤ (r : ℝ) * ((r : ℝ) + 1) * (N : ℝ) := by
    have h1 : (P.card : ℝ) * ((P.card : ℝ) + 1) ≤ (r : ℝ) * ((r : ℝ) + 1) * (N : ℝ) := by
      exact_mod_cast hineq_nat
    have hPnn : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
    nlinarith
  by_contra! hgt
  have hu2 : u ^ 2 = (N : ℝ).sqrt := by
    dsimp [u]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hNreal.le]
    norm_num
  have hu4 : u ^ 4 = (N : ℝ) := by
    calc u ^ 4 = (u ^ 2) ^ 2 := by ring
      _ = ((N : ℝ).sqrt) ^ 2 := by rw [hu2]
      _ = (N : ℝ) := Real.sq_sqrt hNreal.le
  have hr_pos_r : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr (by omega)
  have hP_gt : (r : ℝ) * ((N : ℝ).sqrt + u / 2) < (P.card : ℝ) := by
    rw [hP_real]
    nlinarith
  have hsqrt_nn : 0 ≤ (N : ℝ).sqrt := Real.sqrt_nonneg _
  have hP_sq_gt : (r : ℝ) ^ 2 * ((N : ℝ) + u * (N : ℝ).sqrt + u ^ 2 / 4) < (P.card : ℝ) ^ 2 := by
    have hpos_lhs : 0 ≤ (r : ℝ) * ((N : ℝ).sqrt + u / 2) := by positivity
    have h1 : ((r : ℝ) * ((N : ℝ).sqrt + u / 2)) ^ 2 < (P.card : ℝ) ^ 2 := by
      nlinarith
    have h2 : ((r : ℝ) * ((N : ℝ).sqrt + u / 2)) ^ 2 =
        (r : ℝ) ^ 2 * ((N : ℝ) + u * (N : ℝ).sqrt + u ^ 2 / 4) := by
      have : ((N : ℝ).sqrt) ^ 2 = (N : ℝ) := Real.sq_sqrt hNreal.le
      calc ((r : ℝ) * ((N : ℝ).sqrt + u / 2)) ^ 2
        _ = (r : ℝ) ^ 2 * (((N : ℝ).sqrt) ^ 2 + u * (N : ℝ).sqrt + u ^ 2 / 4) := by ring
        _ = (r : ℝ) ^ 2 * ((N : ℝ) + u * (N : ℝ).sqrt + u ^ 2 / 4) := by rw [this]
    linarith
  have h_gap : (r : ℝ) * ((r : ℝ) + 1) * (N : ℝ) <
      (r : ℝ) ^ 2 * ((N : ℝ) + u * (N : ℝ).sqrt + u ^ 2 / 4) := by
    have hu_pos : 0 < u := Real.rpow_pos_of_pos hNreal _
    have hsqrt_pos : 0 < (N : ℝ).sqrt := Real.sqrt_pos.mpr hNreal
    have hru : (N : ℝ) < (r : ℝ) * u * (N : ℝ).sqrt := by
      have hNeq : (N : ℝ) = u * u * (N : ℝ).sqrt := by
        calc (N : ℝ) = ((N : ℝ).sqrt) ^ 2 := (Real.sq_sqrt hNreal.le).symm
          _ = (N : ℝ).sqrt * (N : ℝ).sqrt := sq _
          _ = u ^ 2 * (N : ℝ).sqrt := by rw [hu2]
          _ = u * u * (N : ℝ).sqrt := by ring
      nlinarith
    have : 0 ≤ (r : ℝ) ^ 2 * (u ^ 2 / 4) := by positivity
    nlinarith
  linarith

/- ## Partie propre à Erdős 43 (ii) -/

/-- Borne d'Erdős–Turán–Lindström pour `f`. -/
lemma oma43_f_le (N : ℕ) :
    (Erdos43.f N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 := by
  have hsup : ((Finset.Icc 1 N).powerset.filter fun B : Finset ℕ => IsSidon (B : Set ℕ)).sup
      Finset.card ≤ Nat.floor ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
    refine Finset.sup_le fun B hB => ?_
    rw [Finset.mem_filter, Finset.mem_powerset] at hB
    exact Nat.le_floor (oma_sidon_lindstrom_et N B hB.1 hB.2)
  have h1 := Nat.cast_le (α := ℝ).mpr hsup
  have h2 : (Nat.floor ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) : ℝ) ≤
      (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 :=
    Nat.floor_le (by positivity)
  exact h1.trans h2

/-- Deux paires d'un corps de même somme et de même produit coïncident. -/
lemma oma43_pair {K : Type*} [Field K] {u v s t : K} (h1 : u + v = s + t)
    (h2 : u * v = s * t) : (u = s ∧ v = t) ∨ (u = t ∧ v = s) := by
  have h3 : (u - s) * (u - t) = 0 := by linear_combination u * h1 - h2
  rcases mul_eq_zero.mp h3 with h | h
  · left
    exact ⟨by linear_combination h, by linear_combination h1 - h⟩
  · right
    exact ⟨by linear_combination h, by linear_combination h1 - h⟩

/-- Ensemble de Ruzsa modulo `2m(2m+1)` : `x i ≡ i (mod 2m)`, `x i ≡ g^i (mod 2m+1)`. -/
lemma oma43_ruzsa (m : ℕ) (hm : 1 ≤ m) (hp : (2 * m + 1).Prime) :
    ∃ x : ℕ → ℕ, (∀ i, x i < 2 * m * (2 * m + 1)) ∧ (∀ i, x i % 2 = i % 2) ∧
      ∀ i₁ i₂ i₃ i₄, i₁ < 2 * m → i₂ < 2 * m → i₃ < 2 * m → i₄ < 2 * m →
        x i₁ + x i₂ = x i₃ + x i₄ → (i₁ = i₃ ∧ i₂ = i₄) ∨ (i₁ = i₄ ∧ i₂ = i₃) := by
  have : Fact (2 * m + 1).Prime := ⟨hp⟩
  have : IsCyclic (ZMod (2 * m + 1))ˣ := ZMod.isCyclic_units_prime hp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod (2 * m + 1))ˣ)
  have hord : orderOf g = 2 * m := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime hp]
    omega
  have hco : Nat.Coprime (2 * m) (2 * m + 1) :=
    Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ZMod (2 * m + 1),
      ∀ i, G i = ((g ^ i : (ZMod (2 * m + 1))ˣ) : ZMod (2 * m + 1)) := ⟨_, fun _ => rfl⟩
  obtain ⟨x, hx1, hx2, hxlt⟩ : ∃ x : ℕ → ℕ, (∀ i, x i ≡ i [MOD 2 * m]) ∧
      (∀ i, x i ≡ (G i).val [MOD 2 * m + 1]) ∧ (∀ i, x i < 2 * m * (2 * m + 1)) :=
    ⟨fun i => (Nat.chineseRemainder hco i (G i).val : ℕ),
      fun i => (Nat.chineseRemainder hco i (G i).val).2.1,
      fun i => (Nat.chineseRemainder hco i (G i).val).2.2,
      fun i => Nat.chineseRemainder_lt_mul hco _ _ (by omega) (by omega)⟩
  refine ⟨x, hxlt, fun i => Nat.ModEq.of_dvd (dvd_mul_right 2 m) (hx1 i), ?_⟩
  intro i₁ i₂ i₃ i₄ h₁ h₂ h₃ h₄ hsum
  have hA : i₁ + i₂ ≡ i₃ + i₄ [MOD 2 * m] := by
    have e1 := (hx1 i₁).add (hx1 i₂)
    have e2 := (hx1 i₃).add (hx1 i₄)
    rw [hsum] at e1
    exact e1.symm.trans e2
  have hB : (G i₁).val + (G i₂).val ≡ (G i₃).val + (G i₄).val [MOD 2 * m + 1] := by
    have e1 := (hx2 i₁).add (hx2 i₂)
    have e2 := (hx2 i₃).add (hx2 i₄)
    rw [hsum] at e1
    exact e1.symm.trans e2
  have hsumG : G i₁ + G i₂ = G i₃ + G i₄ := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hB
    simp only [Nat.cast_add, ZMod.natCast_zmod_val] at this
    exact this
  have hprodG : G i₁ * G i₂ = G i₃ * G i₄ := by
    have hpow : g ^ (i₁ + i₂) = g ^ (i₃ + i₄) := by
      rw [pow_eq_pow_iff_modEq, hord]
      exact hA
    rw [hG, hG, hG, hG, ← Units.val_mul, ← Units.val_mul, ← pow_add, ← pow_add, hpow]
  have hinj : ∀ a b, a < 2 * m → b < 2 * m → G a = G b → a = b := by
    intro a b ha hb hab
    rw [hG, hG] at hab
    have h' : g ^ a = g ^ b := Units.ext hab
    exact pow_injOn_Iio_orderOf (show a < orderOf g by rw [hord]; exact ha)
      (show b < orderOf g by rw [hord]; exact hb) h'
  rcases oma43_pair hsumG hprodG with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact Or.inl ⟨hinj _ _ h₁ h₃ e1, hinj _ _ h₂ h₄ e2⟩
  · exact Or.inr ⟨hinj _ _ h₁ h₄ e1, hinj _ _ h₂ h₃ e2⟩

/-- Découpe par parité de Barreto. -/
lemma oma43_split (m : ℕ) (hm : 1 ≤ m) (x : ℕ → ℕ)
    (hlt : ∀ i, x i < 2 * m * (2 * m + 1)) (hpar : ∀ i, x i % 2 = i % 2)
    (hS : ∀ i₁ i₂ i₃ i₄, i₁ < 2 * m → i₂ < 2 * m → i₃ < 2 * m → i₄ < 2 * m →
        x i₁ + x i₂ = x i₃ + x i₄ → (i₁ = i₃ ∧ i₂ = i₄) ∨ (i₁ = i₄ ∧ i₂ = i₃)) :
    ∃ A B : Finset ℕ, A ⊆ Finset.Icc 1 (m * (2 * m + 1)) ∧
      B ⊆ Finset.Icc 1 (m * (2 * m + 1)) ∧
      IsSidon (A : Set ℕ) ∧ IsSidon (B : Set ℕ) ∧ A.card = m ∧ B.card = m ∧
      (A - A) ∩ (B - B) = {0} := by
  have hM : 2 * m * (2 * m + 1) = 2 * (m * (2 * m + 1)) := by ring
  have hpe : ∀ j, x (2 * j) % 2 = 0 := fun j => by have := hpar (2 * j); omega
  have hpo : ∀ j, x (2 * j + 1) % 2 = 1 := fun j => by have := hpar (2 * j + 1); omega
  have hxinj : ∀ i j, i < 2 * m → j < 2 * m → x i = x j → i = j := by
    intro i j hi hj hij
    rcases hS i i j j hi hi hj hj (by rw [hij]) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> exact h1
  refine ⟨(Finset.range m).image (fun j => x (2 * j) / 2 + 1),
    (Finset.range m).image (fun j => x (2 * j + 1) / 2 + 1), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨j, -, rfl⟩ := ha
    have := hlt (2 * j)
    rw [Finset.mem_Icc]
    constructor <;> omega
  · intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨j, -, rfl⟩ := ha
    have := hlt (2 * j + 1)
    rw [Finset.mem_Icc]
    constructor <;> omega
  · intro a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂ hsum
    simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_range] at ha₁ hb₁ ha₂ hb₂
    obtain ⟨k₁, hk₁, rfl⟩ := ha₁
    obtain ⟨l₁, hl₁, rfl⟩ := hb₁
    obtain ⟨k₂, hk₂, rfl⟩ := ha₂
    obtain ⟨l₂, hl₂, rfl⟩ := hb₂
    have e1 := hpe k₁
    have e2 := hpe l₁
    have e3 := hpe k₂
    have e4 := hpe l₂
    rcases hS (2 * k₁) (2 * k₂) (2 * l₁) (2 * l₂) (by omega) (by omega) (by omega) (by omega)
      (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain rfl : k₁ = l₁ := by omega
      obtain rfl : k₂ = l₂ := by omega
      exact Or.inl ⟨rfl, rfl⟩
    · obtain rfl : k₁ = l₂ := by omega
      obtain rfl : k₂ = l₁ := by omega
      exact Or.inr ⟨rfl, rfl⟩
  · intro a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂ hsum
    simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_range] at ha₁ hb₁ ha₂ hb₂
    obtain ⟨k₁, hk₁, rfl⟩ := ha₁
    obtain ⟨l₁, hl₁, rfl⟩ := hb₁
    obtain ⟨k₂, hk₂, rfl⟩ := ha₂
    obtain ⟨l₂, hl₂, rfl⟩ := hb₂
    have e1 := hpo k₁
    have e2 := hpo l₁
    have e3 := hpo k₂
    have e4 := hpo l₂
    rcases hS (2 * k₁ + 1) (2 * k₂ + 1) (2 * l₁ + 1) (2 * l₂ + 1) (by omega) (by omega)
      (by omega) (by omega) (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain rfl : k₁ = l₁ := by omega
      obtain rfl : k₂ = l₂ := by omega
      exact Or.inl ⟨rfl, rfl⟩
    · obtain rfl : k₁ = l₂ := by omega
      obtain rfl : k₂ = l₁ := by omega
      exact Or.inr ⟨rfl, rfl⟩
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro j₁ hj₁ j₂ hj₂ hj
    have hj₁' : j₁ < m := Finset.mem_range.mp (Finset.mem_coe.mp hj₁)
    have hj₂' : j₂ < m := Finset.mem_range.mp (Finset.mem_coe.mp hj₂)
    have hj' : x (2 * j₁) / 2 + 1 = x (2 * j₂) / 2 + 1 := hj
    have e1 := hpe j₁
    have e2 := hpe j₂
    have := hxinj (2 * j₁) (2 * j₂) (by omega) (by omega) (by omega)
    omega
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro j₁ hj₁ j₂ hj₂ hj
    have hj₁' : j₁ < m := Finset.mem_range.mp (Finset.mem_coe.mp hj₁)
    have hj₂' : j₂ < m := Finset.mem_range.mp (Finset.mem_coe.mp hj₂)
    have hj' : x (2 * j₁ + 1) / 2 + 1 = x (2 * j₂ + 1) / 2 + 1 := hj
    have e1 := hpo j₁
    have e2 := hpo j₂
    have := hxinj (2 * j₁ + 1) (2 * j₂ + 1) (by omega) (by omega) (by omega)
    omega
  · ext d
    simp only [Finset.mem_inter, Finset.mem_sub, Finset.mem_image, Finset.mem_range,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨_, ⟨k₁, hk₁, rfl⟩, _, ⟨k₂, hk₂, rfl⟩, hd₁⟩,
        ⟨_, ⟨l₁, hl₁, rfl⟩, _, ⟨l₂, hl₂, rfl⟩, hd₂⟩⟩
      by_contra hne
      have e1 := hpe k₁
      have e2 := hpe k₂
      have e3 := hpo l₁
      have e4 := hpo l₂
      rcases hS (2 * k₁) (2 * l₂ + 1) (2 * l₁ + 1) (2 * k₂) (by omega) (by omega) (by omega)
        (by omega) (by omega) with ⟨h1, _⟩ | ⟨h1, _⟩
      · omega
      · obtain rfl : k₁ = k₂ := by omega
        omega
    · rintro rfl
      exact ⟨⟨_, ⟨0, by omega, rfl⟩, _, ⟨0, by omega, rfl⟩, Nat.sub_self _⟩,
        ⟨_, ⟨0, by omega, rfl⟩, _, ⟨0, by omega, rfl⟩, Nat.sub_self _⟩⟩

/-- Le cœur polynomial du calcul final : si `m(m-1) ≤ (1-c/2)(u²+u+1)²/2` avec `u⁴ = 2m²+m`,
alors `u ≤ 22/c`. -/
lemma oma43_poly (m u c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hu1 : 1 ≤ u) (hm0 : 0 ≤ m)
    (hu4 : u ^ 4 = 2 * m ^ 2 + m)
    (h1 : m * (m - 1) ≤ (1 - c / 2) * ((u ^ 2 + u + 1) ^ 2 / 2)) : u ≤ 22 / c := by
  have hu0 : 0 < u := by linarith
  have hu12 : u ≤ u ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hu1 hu0.le
    calc u = u * 1 := (mul_one u).symm
      _ ≤ u * u := h
      _ = u ^ 2 := (sq u).symm
  have hu23 : u ^ 2 ≤ u ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hu1 (sq_nonneg u)
    calc u ^ 2 = u ^ 2 * 1 := (mul_one _).symm
      _ ≤ u ^ 2 * u := h
      _ = u ^ 3 := by ring
  have hsq : (u ^ 2 + u + 1) ^ 2 ≤ u ^ 4 + 8 * u ^ 3 := by
    have e : (u ^ 2 + u + 1) ^ 2 = u ^ 4 + 2 * u ^ 3 + 3 * u ^ 2 + 2 * u + 1 := by ring
    rw [e]
    linarith only [hu1, hu12, hu23]
  have h1' : (1 - c / 2) * ((u ^ 2 + u + 1) ^ 2 / 2) ≤
      (1 - c / 2) * ((u ^ 4 + 8 * u ^ 3) / 2) :=
    mul_le_mul_of_nonneg_left (by linarith only [hsq]) (by linarith only [hc1])
  have hm2 : m ^ 2 ≤ (u ^ 2) ^ 2 := by
    have e : (u ^ 2) ^ 2 = u ^ 4 := by ring
    rw [e, hu4]
    nlinarith only [hm0]
  have hmu : m ≤ u ^ 2 := by nlinarith only [hm2, hm0, sq_nonneg u]
  have hcu : 0 ≤ c * u ^ 3 := mul_nonneg hc.le (pow_pos hu0 3).le
  have key : c / 2 * u ^ 4 ≤ 11 * u ^ 3 := by
    first
    | linarith only [h1, h1', hu4, hmu, hu23, hcu]
    | nlinarith only [h1, h1', hu4, hmu, hu23, hcu]
  have h5 : c / 2 * u ≤ 11 := by nlinarith only [key, pow_pos hu0 3]
  rw [le_div_iff₀ hc]
  linarith only [h5]

/-- La contradiction numérique. -/
lemma oma43_numeric (m F : ℕ) (c t : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hN : (22 / c) ^ 4 < ((m * (2 * m + 1) : ℕ) : ℝ))
    (hF : (F : ℝ) ≤ ((m * (2 * m + 1) : ℕ) : ℝ).sqrt +
      ((m * (2 * m + 1) : ℕ) : ℝ) ^ (4⁻¹ : ℝ) + 1)
    (ht : t ≤ 1 - c / 2)
    (h : ((m.choose 2 + m.choose 2 : ℕ) : ℝ) ≤ t * ((F.choose 2 : ℕ) : ℝ)) : False := by
  have hM : ((m.choose 2 + m.choose 2 : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) := by
    push_cast [Nat.cast_choose_two]
    ring
  have hC : ((F.choose 2 : ℕ) : ℝ) = (F : ℝ) * ((F : ℝ) - 1) / 2 := Nat.cast_choose_two ℝ F
  generalize hNdef : ((m * (2 * m + 1) : ℕ) : ℝ) = N at hN hF
  have hNm : N = 2 * (m : ℝ) ^ 2 + m := by
    rw [← hNdef]
    push_cast
    ring
  have hpos4 : (0 : ℝ) < (22 / c) ^ 4 := pow_pos (div_pos (by norm_num) hc) 4
  have hNpos : 0 < N := lt_trans hpos4 hN
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmpos : (0 : ℝ) < m := by nlinarith only [hNm, hNpos, hm0]
  have hm1 : (1 : ℝ) ≤ m := by
    have h0 : 0 < m := by exact_mod_cast hmpos
    exact_mod_cast h0
  have hN1 : (1 : ℝ) ≤ N := by nlinarith only [hNm, hm1]
  generalize hudef : N ^ (4⁻¹ : ℝ) = u at hF
  have hu1 : 1 ≤ u := by
    rw [← hudef]
    exact Real.one_le_rpow hN1 (by norm_num)
  have hu0 : 0 < u := by linarith only [hu1]
  have hu2 : u ^ 2 = N.sqrt := by
    rw [← hudef, Real.sqrt_eq_rpow, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hNpos.le]
    norm_num
  have hu4 : u ^ 4 = N := by
    calc u ^ 4 = (u ^ 2) ^ 2 := by ring
      _ = (N.sqrt) ^ 2 := by rw [hu2]
      _ = N := Real.sq_sqrt hNpos.le
  have hF' : (F : ℝ) ≤ u ^ 2 + u + 1 := by rw [hu2]; exact hF
  have hF0 : (0 : ℝ) ≤ F := Nat.cast_nonneg F
  have hC0 : 0 ≤ ((F.choose 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ u ^ 2 + u + 1 := by
    have := sq_nonneg u
    linarith only [this, hu1]
  have hFF : (F : ℝ) * F ≤ (u ^ 2 + u + 1) * (u ^ 2 + u + 1) := mul_le_mul hF' hF' hF0 hs0
  have hCle : ((F.choose 2 : ℕ) : ℝ) ≤ (u ^ 2 + u + 1) ^ 2 / 2 := by
    rw [hC]
    nlinarith only [hFF, hF0]
  have h1 : (m : ℝ) * ((m : ℝ) - 1) ≤ (1 - c / 2) * ((u ^ 2 + u + 1) ^ 2 / 2) := by
    rw [← hM]
    calc _ ≤ t * ((F.choose 2 : ℕ) : ℝ) := h
      _ ≤ (1 - c / 2) * ((F.choose 2 : ℕ) : ℝ) := mul_le_mul_of_nonneg_right ht hC0
      _ ≤ (1 - c / 2) * ((u ^ 2 + u + 1) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left hCle (by linarith only [hc1])
  have h3 : u ≤ 22 / c := oma43_poly m u c hc hc1 hu1 hm0 (by rw [hu4, hNm]) h1
  have h6 : u ^ 4 ≤ (22 / c) ^ 4 := by
    first
    | exact pow_le_pow_left₀ hu0.le h3 4
    | exact pow_le_pow_left hu0.le h3 4
  linarith only [h6, hu4, hN]

theorem OMA.solution : type_of% @Erdos43.erdos_43.parts.ii := by
  rintro ⟨c, hc, o, ho, hev⟩
  have hc'pos : 0 < min c 1 := lt_min hc one_pos
  have hc'le : min c 1 ≤ c := min_le_left _ _
  have hc'1 : min c 1 ≤ 1 := min_le_right _ _
  have ho' : ∀ᶠ N in Filter.atTop, |o N| ≤ min c 1 / 2 := by
    have h := ho.def (show (0 : ℝ) < min c 1 / 2 by positivity)
    filter_upwards [h] with N hN
    simpa using hN
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (hev.and ho')
  obtain ⟨p, hpge, hpp⟩ := Nat.exists_infinite_primes (N0 + ⌈(22 / min c 1) ^ 4⌉₊ + 5)
  obtain ⟨m, rfl⟩ : Odd p := hpp.odd_of_ne_two (by omega)
  have hm1 : 1 ≤ m := by omega
  obtain ⟨x, hxlt, hxpar, hxS⟩ := oma43_ruzsa m hm1 hpp
  obtain ⟨A, B, hA, hB, hSA, hSB, hcA, hcB, hdisj⟩ := oma43_split m hm1 x hxlt hxpar hxS
  have hle : 2 * m + 1 ≤ m * (2 * m + 1) := Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨hbound, hoN⟩ := hN0 (m * (2 * m + 1)) (by omega)
  have key := hbound A B hA hB hSA hSB (hcA.trans hcB.symm) hdisj
  rw [hcA, hcB] at key
  have hNreal : (22 / min c 1) ^ 4 < ((m * (2 * m + 1) : ℕ) : ℝ) := by
    have h1 : (22 / min c 1) ^ 4 ≤ (⌈(22 / min c 1) ^ 4⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ⌈(22 / min c 1) ^ 4⌉₊ < m * (2 * m + 1) := by omega
    have h3 : ((⌈(22 / min c 1) ^ 4⌉₊ : ℕ) : ℝ) < ((m * (2 * m + 1) : ℕ) : ℝ) := by
      exact_mod_cast h2
    linarith
  have ht : 1 - c + o (m * (2 * m + 1)) ≤ 1 - min c 1 / 2 := by
    have := (abs_le.mp hoN).2
    linarith
  exact oma43_numeric m (Erdos43.f (m * (2 * m + 1))) (min c 1) _ hc'pos hc'1 hNreal
    (oma43_f_le _) ht key
