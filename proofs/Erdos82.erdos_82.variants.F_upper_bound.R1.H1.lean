import OMAReductions.R_Erdos82_erdos_82_variants_F_upper_bound_R1

/-! Step H1 of Erdos82.erdos_82.variants.F_upper_bound.R1 -/

open scoped Classical

section Helpers

private lemma factorial_mul_exp_ge_pow (j : ℕ) :
    (j : ℝ) ^ j ≤ (Real.exp 1) ^ j * (j.factorial : ℝ) := by
  have hj_pos : (0 : ℝ) < (j.factorial : ℝ) := by positivity
  have hsum : (j : ℝ) ^ j / (j.factorial : ℝ) ≤ Real.exp (j : ℝ) := by
    have h1 : (j : ℝ) ^ j / (j.factorial : ℝ) ≤
        ∑ i ∈ Finset.range (j + 1), (j : ℝ) ^ i / (i.factorial : ℝ) :=
      Finset.single_le_sum (f := fun i => (j : ℝ) ^ i / (i.factorial : ℝ))
        (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self j))
    exact h1.trans (Real.sum_le_exp_of_nonneg (Nat.cast_nonneg j) (j + 1))
  have hexp : Real.exp (j : ℝ) = (Real.exp 1) ^ j := by
    rw [← mul_one (j : ℝ), Real.exp_nat_mul]
  rw [hexp, div_le_iff₀ hj_pos] at hsum
  exact hsum

private lemma central_binom_sq_mul_le (r : ℕ) :
    Nat.choose (2 * r) r ^ 2 * (2 * r + 1) ≤ 16 ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hstep : (r + 1) * Nat.choose (2 * r + 2) (r + 1) =
        2 * (2 * r + 1) * Nat.choose (2 * r) r := by
      have h1 : (r + 1) * Nat.choose (2 * r + 2) (r + 1) =
          (2 * r + 2) * Nat.choose (2 * r + 1) r := by
        rw [Nat.mul_comm, ← Nat.add_one_mul_choose_eq (2 * r + 1) r]
      have h2 : (r + 1) * Nat.choose (2 * r + 1) r =
          (2 * r + 1) * Nat.choose (2 * r) r := by
        rw [← Nat.choose_symm_half r, Nat.mul_comm (r + 1), ← Nat.add_one_mul_choose_eq (2 * r) r]
      calc (r + 1) * Nat.choose (2 * r + 2) (r + 1)
          = (2 * r + 2) * Nat.choose (2 * r + 1) r := h1
        _ = 2 * ((r + 1) * Nat.choose (2 * r + 1) r) := by ring
        _ = 2 * ((2 * r + 1) * Nat.choose (2 * r) r) := by rw [h2]
        _ = 2 * (2 * r + 1) * Nat.choose (2 * r) r := by ring
    have hmul : (Nat.choose (2 * (r + 1)) (r + 1) ^ 2 * (2 * (r + 1) + 1)) * (r + 1) ^ 2 ≤
        16 ^ (r + 1) * (r + 1) ^ 2 := by
      have h2r : 2 * (r + 1) = 2 * r + 2 := by ring
      rw [h2r]
      calc (Nat.choose (2 * r + 2) (r + 1) ^ 2 * (2 * r + 3)) * (r + 1) ^ 2
          = ((r + 1) * Nat.choose (2 * r + 2) (r + 1)) ^ 2 * (2 * r + 3) := by ring
        _ = (2 * (2 * r + 1) * Nat.choose (2 * r) r) ^ 2 * (2 * r + 3) := by rw [hstep]
        _ = (4 * (2 * r + 1) * (2 * r + 3)) * (Nat.choose (2 * r) r ^ 2 * (2 * r + 1)) := by ring
        _ ≤ (4 * (2 * r + 1) * (2 * r + 3)) * 16 ^ r := Nat.mul_le_mul_left _ ih
        _ ≤ (16 * (r + 1) ^ 2) * 16 ^ r := by
            refine Nat.mul_le_mul_right _ ?_
            nlinarith
        _ = 16 ^ (r + 1) * (r + 1) ^ 2 := by rw [pow_succ]; ring
    exact Nat.le_of_mul_le_mul_right hmul (by positivity)

private lemma choose_div_pow_le_inv_sqrt (R s : ℕ) :
    (Nat.choose R s : ℝ) / (2 : ℝ) ^ R ≤ 1 / Real.sqrt ((R + 1 : ℕ) : ℝ) := by
  have hmid : Nat.choose R s ≤ Nat.choose R (R / 2) := Nat.choose_le_middle s R
  rcases Nat.even_or_odd' R with ⟨r, rfl | rfl⟩
  · have hdiv : 2 * r / 2 = r := by omega
    rw [hdiv] at hmid
    have hnat : Nat.choose (2 * r) r ^ 2 * (2 * r + 1) ≤ 16 ^ r := central_binom_sq_mul_le r
    have hreal : (Nat.choose (2 * r) r : ℝ) ^ 2 * ((2 * r + 1 : ℕ) : ℝ) ≤ ((2 : ℝ) ^ (2 * r)) ^ 2 := by
      have h16 : (16 : ℝ) ^ r = ((2 : ℝ) ^ (2 * r)) ^ 2 := by
        calc (16 : ℝ) ^ r = ((2 : ℝ) ^ 4) ^ r := by norm_num
          _ = (2 : ℝ) ^ (4 * r) := by rw [← pow_mul]
          _ = ((2 : ℝ) ^ (2 * r)) ^ 2 := by rw [← pow_mul]; congr 1; ring
      exact (by exact_mod_cast hnat : (Nat.choose (2 * r) r : ℝ) ^ 2 * ((2 * r + 1 : ℕ) : ℝ) ≤ (16 : ℝ) ^ r).trans_eq h16
    have hsq : ((Nat.choose (2 * r) r : ℝ) / (2 : ℝ) ^ (2 * r)) ^ 2 ≤
        (1 / Real.sqrt ((2 * r + 1 : ℕ) : ℝ)) ^ 2 := by
      rw [div_pow, div_pow, one_pow, Real.sq_sqrt (by positivity)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have hle : (Nat.choose (2 * r) r : ℝ) / (2 : ℝ) ^ (2 * r) ≤
        1 / Real.sqrt ((2 * r + 1 : ℕ) : ℝ) := by
      by_contra! hgt
      have := mul_self_lt_mul_self (by positivity) hgt
      rw [← sq, ← sq] at this
      linarith
    have hsub : (Nat.choose (2 * r) s : ℝ) / (2 : ℝ) ^ (2 * r) ≤
        (Nat.choose (2 * r) r : ℝ) / (2 : ℝ) ^ (2 * r) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hmid) (by positivity)
    exact hsub.trans hle
  · have hdiv : (2 * r + 1) / 2 = r := by omega
    rw [hdiv] at hmid
    have hdbl : 2 * Nat.choose (2 * r + 1) r = Nat.choose (2 * r + 2) (r + 1) := by
      have hsym : Nat.choose (2 * r + 1) (r + 1) = Nat.choose (2 * r + 1) r := Nat.choose_symm_half r
      rw [Nat.choose_succ_succ (2 * r + 1) r, hsym]
      omega
    have hnat : Nat.choose (2 * (r + 1)) (r + 1) ^ 2 * (2 * (r + 1) + 1) ≤ 16 ^ (r + 1) :=
      central_binom_sq_mul_le (r + 1)
    have h2r : 2 * (r + 1) = 2 * r + 2 := by ring
    rw [h2r] at hnat
    have hreal : (Nat.choose (2 * r + 2) (r + 1) : ℝ) ^ 2 * ((2 * r + 3 : ℕ) : ℝ) ≤
        ((2 : ℝ) ^ (2 * r + 2)) ^ 2 := by
      have h16 : (16 : ℝ) ^ (r + 1) = ((2 : ℝ) ^ (2 * r + 2)) ^ 2 := by
        calc (16 : ℝ) ^ (r + 1) = ((2 : ℝ) ^ 4) ^ (r + 1) := by norm_num
          _ = (2 : ℝ) ^ (4 * (r + 1)) := by rw [← pow_mul]
          _ = ((2 : ℝ) ^ (2 * r + 2)) ^ 2 := by rw [← pow_mul]; congr 1; ring
      have hnat' : Nat.choose (2 * r + 2) (r + 1) ^ 2 * (2 * r + 3) ≤ 16 ^ (r + 1) := by
        simpa [add_assoc] using hnat
      exact (by exact_mod_cast hnat' : (Nat.choose (2 * r + 2) (r + 1) : ℝ) ^ 2 * ((2 * r + 3 : ℕ) : ℝ) ≤ (16 : ℝ) ^ (r + 1)).trans_eq h16
    have hsq : ((Nat.choose (2 * r + 2) (r + 1) : ℝ) / (2 : ℝ) ^ (2 * r + 2)) ^ 2 ≤
        (1 / Real.sqrt ((2 * r + 3 : ℕ) : ℝ)) ^ 2 := by
      rw [div_pow, div_pow, one_pow, Real.sq_sqrt (by positivity)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have hle1 : (Nat.choose (2 * r + 2) (r + 1) : ℝ) / (2 : ℝ) ^ (2 * r + 2) ≤
        1 / Real.sqrt ((2 * r + 3 : ℕ) : ℝ) := by
      by_contra! hgt
      have := mul_self_lt_mul_self (by positivity) hgt
      rw [← sq, ← sq] at this
      linarith
    have hle2 : 1 / Real.sqrt ((2 * r + 3 : ℕ) : ℝ) ≤
        1 / Real.sqrt ((2 * r + 1 + 1 : ℕ) : ℝ) := by
      refine one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity)) ?_
      refine Real.sqrt_le_sqrt ?_
      norm_cast
      omega
    have heq : (Nat.choose (2 * r + 1) r : ℝ) / (2 : ℝ) ^ (2 * r + 1) =
        (Nat.choose (2 * r + 2) (r + 1) : ℝ) / (2 : ℝ) ^ (2 * r + 2) := by
      have hdbl_r : (2 : ℝ) * (Nat.choose (2 * r + 1) r : ℝ) =
          (Nat.choose (2 * r + 2) (r + 1) : ℝ) := by exact_mod_cast hdbl
      rw [← hdbl_r, pow_succ]
      field_simp
      ring
    have hsub : (Nat.choose (2 * r + 1) s : ℝ) / (2 : ℝ) ^ (2 * r + 1) ≤
        (Nat.choose (2 * r + 1) r : ℝ) / (2 : ℝ) ^ (2 * r + 1) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hmid) (by positivity)
    exact hsub.trans (heq ▸ hle1.trans hle2)

private lemma nat_succ_mul_three_quarters_le (q : ℕ) :
    ((q + 1 : ℕ) : ℝ) * (3 / 4 : ℝ) ^ q ≤ 2 := by
  induction q with
  | zero => norm_num
  | succ q ih =>
    rcases Nat.lt_or_ge q 2 with hq | hq
    · interval_cases q <;> norm_num
    · have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      have hstep : ((q + 2 : ℕ) : ℝ) * (3 / 4 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by
        push_cast
        linarith
      calc ((q + 1 + 1 : ℕ) : ℝ) * (3 / 4 : ℝ) ^ (q + 1)
          = (((q + 2 : ℕ) : ℝ) * (3 / 4 : ℝ)) * (3 / 4 : ℝ) ^ q := by
            rw [pow_succ]; ring_nf
        _ ≤ ((q + 1 : ℕ) : ℝ) * (3 / 4 : ℝ) ^ q :=
            mul_le_mul_of_nonneg_right hstep (by positivity)
        _ ≤ 2 := ih

private lemma bool_subset_card_sum {m : ℕ} (F : Finset (Fin m)) (s₀ : ℕ) :
    (∑ g : ({i : Fin m // i ∈ F} → Bool),
      if (Finset.univ.filter (fun i => g i = true)).card = s₀ then (1 : ℝ) else 0) =
    (Nat.choose F.card s₀ : ℝ) := by
  let S : Finset ({i : Fin m // i ∈ F} → Bool) :=
    Finset.univ.filter (fun g => (Finset.univ.filter (fun i => g i = true)).card = s₀)
  have h1 : (∑ g : ({i : Fin m // i ∈ F} → Bool),
      if (Finset.univ.filter (fun i => g i = true)).card = s₀ then (1 : ℝ) else 0) =
      (S.card : ℝ) := by
    rw [Finset.sum_boole]
  rw [h1]
  let e : ({i : Fin m // i ∈ F} → Bool) ≃ Finset {i : Fin m // i ∈ F} :=
    { toFun := fun g => Finset.univ.filter (fun i => g i = true)
      invFun := fun A i => decide (i ∈ A)
      left_inv := fun g => by ext i; simp
      right_inv := fun A => by ext i; simp }
  have hcard : S.card = ((Finset.univ : Finset (Finset {i : Fin m // i ∈ F})).filter
      (fun A => A.card = s₀)).card := by
    refine Finset.card_bij (fun g _ => e g) ?_ ?_ ?_
    · intro g hg
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      exact hg
    · intro g₁ _ g₂ _ h
      exact e.injective h
    · intro A hA
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
      refine ⟨e.symm A, ?_, e.apply_symm_apply A⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      change (e (e.symm A)).card = s₀
      rw [e.apply_symm_apply A]
      exact hA
  rw [hcard]
  have hpow : (Finset.univ : Finset (Finset {i : Fin m // i ∈ F})).filter (fun A => A.card = s₀) =
      Finset.univ.powersetCard s₀ := by
    ext A
    simp [Finset.mem_powersetCard]
  rw [hpow, Finset.card_powersetCard, Finset.card_univ, Fintype.card_coe]

private lemma bernoulli_point_le {m : ℕ} (hm : 1 ≤ m) (p : Fin m → ℝ)
    (hp : ∀ i, 1 / 16 ≤ p i ∧ p i ≤ 9 / 16) (t : ℕ) :
    (∑ f : Fin m → Bool,
      (if (Finset.univ.filter (fun i => f i = true)).card = t then (1 : ℝ) else 0) *
      (∏ i : Fin m, if f i = true then p i else 1 - p i)) ≤
    12 / Real.sqrt (m : ℝ) := by
  let w₃ : Fin m → Fin 3 → ℝ := fun i c =>
    match c with
    | ⟨0, _⟩ => p i - 1 / 16
    | ⟨1, _⟩ => 15 / 16 - p i
    | ⟨2, _⟩ => 1 / 8
  let q₃ : Fin m → Fin 3 → Bool → ℝ := fun _ c b =>
    match c with
    | ⟨0, _⟩ => if b = true then 1 else 0
    | ⟨1, _⟩ => if b = false then 1 else 0
    | ⟨2, _⟩ => 1 / 2
  have hw_nonneg : ∀ i c, 0 ≤ w₃ i c := by
    intro i c
    have := hp i
    fin_cases c <;> simp only [w₃] <;> linarith
  have hw_sum : ∀ i, ∑ c : Fin 3, w₃ i c = 1 := by
    intro i
    simp [Fin.sum_univ_three, w₃]
    ring
  have hq_nonneg : ∀ i c b, 0 ≤ q₃ i c b := by
    intro i c b
    fin_cases c <;> cases b <;> simp [q₃]
  have hmix : ∀ i b, (if b = true then p i else 1 - p i) = ∑ c : Fin 3, w₃ i c * q₃ i c b := by
    intro i b
    cases b <;> simp [Fin.sum_univ_three, w₃, q₃] <;> ring
  have hexpand : ∀ f : Fin m → Bool,
      (∏ i : Fin m, if f i = true then p i else 1 - p i) =
      ∑ c : Fin m → Fin 3, (∏ i : Fin m, w₃ i (c i)) * (∏ i : Fin m, q₃ i (c i) (f i)) := by
    intro f
    calc (∏ i : Fin m, if f i = true then p i else 1 - p i)
        = ∏ i : Fin m, ∑ c : Fin 3, w₃ i c * q₃ i c (f i) := by
          refine Finset.prod_congr rfl fun i _ => hmix i (f i)
      _ = ∑ c : Fin m → Fin 3, ∏ i : Fin m, (w₃ i (c i) * q₃ i (c i) (f i)) :=
          Fintype.prod_sum (fun i c => w₃ i c * q₃ i c (f i))
      _ = ∑ c : Fin m → Fin 3, (∏ i : Fin m, w₃ i (c i)) * (∏ i : Fin m, q₃ i (c i) (f i)) := by
          refine Finset.sum_congr rfl fun c _ => Finset.prod_mul_distrib
  have hswap :
      (∑ f : Fin m → Bool,
        (if (Finset.univ.filter (fun i => f i = true)).card = t then (1 : ℝ) else 0) *
        (∏ i : Fin m, if f i = true then p i else 1 - p i)) =
      ∑ c : Fin m → Fin 3, (∏ i : Fin m, w₃ i (c i)) *
        (∑ f : Fin m → Bool,
          (if (Finset.univ.filter (fun i => f i = true)).card = t then (1 : ℝ) else 0) *
          (∏ i : Fin m, q₃ i (c i) (f i))) := by
    simp_rw [hexpand, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun f _ => by ring
  have hinner : ∀ c : Fin m → Fin 3,
      (∑ f : Fin m → Bool,
        (if (Finset.univ.filter (fun i => f i = true)).card = t then (1 : ℝ) else 0) *
        (∏ i : Fin m, q₃ i (c i) (f i))) ≤
      1 / Real.sqrt (((Finset.univ.filter (fun i => c i = 2)).card + 1 : ℕ) : ℝ) := by
    intro c
    let F := Finset.univ.filter (fun i : Fin m => c i = 2)
    let eBool : (Fin m → Bool) ≃ ({i : Fin m // i ∈ F} → Bool) × ({i : Fin m // i ∉ F} → Bool) :=
      { toFun := fun f => (fun i => f i.1, fun i => f i.1)
        invFun := fun p i => if h : i ∈ F then p.1 ⟨i, h⟩ else p.2 ⟨i, h⟩
        left_inv := fun f => by ext i; by_cases h : i ∈ F <;> simp [h]
        right_inv := fun p => by ext i <;> simp [i.2] }
    have hsum_split :
        (∑ f : Fin m → Bool,
          (if (Finset.univ.filter (fun i => f i = true)).card = t then (1 : ℝ) else 0) *
          (∏ i : Fin m, q₃ i (c i) (f i))) =
        ∑ f_out : ({i : Fin m // i ∉ F} → Bool),
          (∏ i : {i : Fin m // i ∉ F}, q₃ i.1 (c i.1) (f_out i)) *
          (∑ f_in : ({i : Fin m // i ∈ F} → Bool),
            (if (Finset.univ.filter (fun i => f_in i = true)).card +
                (Finset.univ.filter (fun i => f_out i = true)).card = t then (1 : ℝ) else 0) *
            (1 / 2 : ℝ) ^ F.card) := by
      rw [Fintype.sum_equiv eBool _ (fun p =>
          (if (Finset.univ.filter (fun i => (eBool.symm p) i = true)).card = t then (1 : ℝ) else 0) *
          (∏ i : Fin m, q₃ i (c i) ((eBool.symm p) i)))
        (fun f => by simp)]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun f_out _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun f_in _ => ?_
      let g := eBool.symm (f_in, f_out)
      have hcard_g : (Finset.univ.filter (fun i => g i = true)).card =
          (Finset.univ.filter (fun i => f_in i = true)).card +
          (Finset.univ.filter (fun i => f_out i = true)).card := by
        have hpart : Finset.univ.filter (fun i => g i = true) =
            (Finset.univ.filter (fun i => f_in i = true)).map ⟨Subtype.val, Subtype.val_injective⟩ ∪
            (Finset.univ.filter (fun i => f_out i = true)).map ⟨Subtype.val, Subtype.val_injective⟩ := by
          ext i
          simp only [Finset.mem_union, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
            Function.Embedding.coeFn_mk, g, eBool]
          constructor
          · intro hg
            by_cases hi : i ∈ F
            · left; refine ⟨⟨i, hi⟩, ?_, rfl⟩; simpa [hi] using hg
            · right; refine ⟨⟨i, hi⟩, ?_, rfl⟩; simpa [hi] using hg
          · rintro (⟨⟨j, hj⟩, h1, rfl⟩ | ⟨⟨j, hj⟩, h1, rfl⟩)
            · simpa [hj] using h1
            · simpa [hj] using h1
        have hdisj : Disjoint
            ((Finset.univ.filter (fun i => f_in i = true)).map ⟨Subtype.val, Subtype.val_injective⟩)
            ((Finset.univ.filter (fun i => f_out i = true)).map ⟨Subtype.val, Subtype.val_injective⟩) := by
          rw [Finset.disjoint_left]
          rintro x hx1 hx2
          simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
            Function.Embedding.coeFn_mk] at hx1 hx2
          rcases hx1 with ⟨⟨j1, hj1⟩, _, rfl⟩
          rcases hx2 with ⟨⟨j2, hj2⟩, _, hjeq⟩
          dsimp only at hjeq
          exact hj2 (hjeq ▸ hj1)
        rw [hpart, Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map]
      have hprod_g : (∏ i : Fin m, q₃ i (c i) (g i)) =
          (∏ i : {i : Fin m // i ∉ F}, q₃ i.1 (c i.1) (f_out i)) * (1 / 2 : ℝ) ^ F.card := by
        have hpart : (∏ i : Fin m, q₃ i (c i) (g i)) =
            (∏ i ∈ F, q₃ i (c i) (g i)) * (∏ i ∈ Finset.univ \ F, q₃ i (c i) (g i)) := by
          rw [← Finset.prod_sdiff (Finset.subset_univ F)]
          ring
        rw [hpart]
        have hF : (∏ i ∈ F, q₃ i (c i) (g i)) = (1 / 2 : ℝ) ^ F.card := by
          calc ∏ i ∈ F, q₃ i (c i) (g i)
              = ∏ _ ∈ F, (1 / 2 : ℝ) := by
                refine Finset.prod_congr rfl fun i hi => ?_
                have hc2 : c i = 2 := (Finset.mem_filter.mp hi).2
                simp [hc2, q₃]
            _ = (1 / 2 : ℝ) ^ F.card := by rw [Finset.prod_const]
        have hFc : (∏ i ∈ Finset.univ \ F, q₃ i (c i) (g i)) =
            ∏ i : {i : Fin m // i ∉ F}, q₃ i.1 (c i.1) (f_out i) := by
          rw [← Finset.prod_coe_sort (Finset.univ \ F)]
          refine Finset.prod_bij (fun i _ => ⟨i.1, (Finset.mem_sdiff.mp i.2).2⟩) ?_ ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro a _ b _ h; exact Subtype.ext (congr_arg (fun x : {i : Fin m // i ∉ F} => x.1) h)
          · intro j _
            refine ⟨⟨j.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, j.2⟩⟩, Finset.mem_univ _, rfl⟩
          · intro ⟨i, hi⟩ _
            have hni : i ∉ F := (Finset.mem_sdiff.mp hi).2
            simp [g, eBool, hni]
        rw [hF, hFc, mul_comm]
      rw [hcard_g, hprod_g]
      ring
    rw [hsum_split]
    have hinner_f : ∀ f_out : ({i : Fin m // i ∉ F} → Bool),
        (∑ f_in : ({i : Fin m // i ∈ F} → Bool),
          (if (Finset.univ.filter (fun i => f_in i = true)).card +
              (Finset.univ.filter (fun i => f_out i = true)).card = t then (1 : ℝ) else 0) *
          (1 / 2 : ℝ) ^ F.card) ≤
        1 / Real.sqrt ((F.card + 1 : ℕ) : ℝ) := by
      intro f_out
      set k_out := (Finset.univ.filter (fun i => f_out i = true)).card
      by_cases hkt : k_out ≤ t
      · have heq :
            (∑ f_in : ({i : Fin m // i ∈ F} → Bool),
              (if (Finset.univ.filter (fun i => f_in i = true)).card + k_out = t then (1 : ℝ) else 0) *
              (1 / 2 : ℝ) ^ F.card) =
            (Nat.choose F.card (t - k_out) : ℝ) / (2 : ℝ) ^ F.card := by
          rw [← Finset.sum_mul]
          have hs : (∑ f_in : ({i : Fin m // i ∈ F} → Bool),
              if (Finset.univ.filter (fun i => f_in i = true)).card + k_out = t then (1 : ℝ) else 0) =
              (Nat.choose F.card (t - k_out) : ℝ) := by
            rw [← bool_subset_card_sum F (t - k_out)]
            refine Finset.sum_congr rfl fun f_in _ => ?_
            split_ifs with h1 h2
            · rfl
            · exact absurd (by omega : (Finset.univ.filter (fun i => f_in i = true)).card = t - k_out) h2
            · exact absurd (by omega : (Finset.univ.filter (fun i => f_in i = true)).card + k_out = t) h1
            · rfl
          rw [hs, one_div, inv_pow, ← div_eq_mul_inv]
        rw [heq]
        exact choose_div_pow_le_inv_sqrt F.card (t - k_out)
      · have hzero :
            (∑ f_in : ({i : Fin m // i ∈ F} → Bool),
              (if (Finset.univ.filter (fun i => f_in i = true)).card + k_out = t then (1 : ℝ) else 0) *
              (1 / 2 : ℝ) ^ F.card) = 0 := by
          refine Finset.sum_eq_zero fun f_in _ => ?_
          have : (Finset.univ.filter (fun i => f_in i = true)).card + k_out ≠ t := by omega
          rw [if_neg this, zero_mul]
        rw [hzero]
        positivity
    have hprod_out : (∑ f_out : ({i : Fin m // i ∉ F} → Bool),
        ∏ i : {i : Fin m // i ∉ F}, q₃ i.1 (c i.1) (f_out i)) ≤ 1 := by
      rw [← Fintype.prod_sum (fun (i : {i : Fin m // i ∉ F}) (b : Bool) => q₃ i.1 (c i.1) b)]
      refine Finset.prod_le_one (fun i _ => ?_) (fun i _ => ?_)
      · exact Finset.sum_nonneg fun b _ => hq_nonneg i.1 (c i.1) b
      · have hni : c i.1 ≠ 2 := by
          intro hc2
          exact i.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc2⟩)
        have hlt3 : (c i.1).val < 3 := (c i.1).isLt
        have h012 : c i.1 = 0 ∨ c i.1 = 1 ∨ c i.1 = 2 := by
          rcases (by omega : (c i.1).val = 0 ∨ (c i.1).val = 1 ∨ (c i.1).val = 2) with h | h | h
          · exact Or.inl (Fin.ext h)
          · exact Or.inr (Or.inl (Fin.ext h))
          · exact Or.inr (Or.inr (Fin.ext h))
        rcases h012 with h0 | h1 | h2
        · simp [h0, q₃]
        · simp [h1, q₃]
        · exact absurd h2 hni
    calc ∑ f_out : ({i : Fin m // i ∉ F} → Bool),
          (∏ i : {i : Fin m // i ∉ F}, q₃ i.1 (c i.1) (f_out i)) *
          (∑ f_in : ({i : Fin m // i ∈ F} → Bool),
            (if (Finset.univ.filter (fun i => f_in i = true)).card +
                (Finset.univ.filter (fun i => f_out i = true)).card = t then (1 : ℝ) else 0) *
            (1 / 2 : ℝ) ^ F.card)
        ≤ ∑ f_out : ({i : Fin m // i ∉ F} → Bool),
          (∏ i : {i : Fin m // i ∉ F}, q₃ i.1 (c i.1) (f_out i)) *
          (1 / Real.sqrt ((F.card + 1 : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum fun f_out _ => ?_
          refine mul_le_mul_of_nonneg_left (hinner_f f_out) ?_
          exact Finset.prod_nonneg fun i _ => hq_nonneg i.1 (c i.1) (f_out i)
      _ = (∑ f_out : ({i : Fin m // i ∉ F} → Bool),
            ∏ i : {i : Fin m // i ∉ F}, q₃ i.1 (c i.1) (f_out i)) *
          (1 / Real.sqrt ((F.card + 1 : ℕ) : ℝ)) := (Finset.sum_mul _ _ _).symm
      _ ≤ 1 * (1 / Real.sqrt ((F.card + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hprod_out (by positivity)
      _ = 1 / Real.sqrt ((F.card + 1 : ℕ) : ℝ) := one_mul _
  rw [hswap]
  set q : ℕ := m / 16
  let Rfn (c : Fin m → Fin 3) : ℕ := (Finset.univ.filter (fun i => c i = 2)).card
  have hpoint : ∀ c : Fin m → Fin 3,
      (1 / Real.sqrt ((Rfn c + 1 : ℕ) : ℝ)) ≤
      (1 / Real.sqrt ((q + 1 : ℕ) : ℝ)) + (2 : ℝ) ^ q * (1 / 2 : ℝ) ^ Rfn c := by
    intro c
    by_cases hR : q ≤ Rfn c
    · have h1 : 1 / Real.sqrt ((Rfn c + 1 : ℕ) : ℝ) ≤ 1 / Real.sqrt ((q + 1 : ℕ) : ℝ) := by
        refine one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity)) ?_
        exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.add_le_add_right hR 1)
      have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ q * (1 / 2 : ℝ) ^ Rfn c := by positivity
      linarith
    · have hRlt : Rfn c ≤ q := le_of_not_ge hR
      have h1 : 1 / Real.sqrt ((Rfn c + 1 : ℕ) : ℝ) ≤ 1 := by
        refine div_le_one_of_le₀ ?_ (by positivity)
        rw [Real.le_sqrt (by norm_num) (by positivity)]
        norm_num
      have h2 : 1 ≤ (2 : ℝ) ^ q * (1 / 2 : ℝ) ^ Rfn c := by
        have hp : (2 : ℝ) ^ Rfn c ≤ (2 : ℝ) ^ q := pow_le_pow_right₀ (by norm_num) hRlt
        rw [one_div, inv_pow, ← div_eq_mul_inv, one_le_div (by positivity)]
        exact hp
      have h3 : (0 : ℝ) ≤ 1 / Real.sqrt ((q + 1 : ℕ) : ℝ) := by positivity
      linarith
  have hsum_w : (∑ c : Fin m → Fin 3, ∏ i : Fin m, w₃ i (c i)) = 1 := by
    rw [← Fintype.prod_sum (fun (i : Fin m) (x : Fin 3) => w₃ i x)]
    exact Finset.prod_eq_one fun i _ => hw_sum i
  have hsum_exp : (∑ c : Fin m → Fin 3, (∏ i : Fin m, w₃ i (c i)) * (1 / 2 : ℝ) ^ Rfn c) =
      (15 / 16 : ℝ) ^ m := by
    have hrw : ∀ c : Fin m → Fin 3,
        (∏ i : Fin m, w₃ i (c i)) * (1 / 2 : ℝ) ^ Rfn c =
        ∏ i : Fin m, w₃ i (c i) * (if c i = 2 then (1 / 2 : ℝ) else 1) := by
      intro c
      have hpow : (1 / 2 : ℝ) ^ Rfn c = ∏ i : Fin m, (if c i = 2 then (1 / 2 : ℝ) else 1) := by
        rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
      rw [hpow, Finset.prod_mul_distrib]
    simp_rw [hrw]
    rw [← Fintype.prod_sum (fun (i : Fin m) (x : Fin 3) => w₃ i x * (if x = 2 then (1 / 2 : ℝ) else 1))]
    calc ∏ i : Fin m, ∑ c : Fin 3, w₃ i c * (if c = 2 then (1 / 2 : ℝ) else 1)
        = ∏ _ : Fin m, (15 / 16 : ℝ) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          simp [Fin.sum_univ_three, w₃]
          ring
      _ = (15 / 16 : ℝ) ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hterm1 : 1 / Real.sqrt ((q + 1 : ℕ) : ℝ) ≤ 4 / Real.sqrt (m : ℝ) := by
    have hm_lt : m < 16 * (q + 1) := by omega
    have hsqrt_le : Real.sqrt (m : ℝ) ≤ 4 * Real.sqrt ((q + 1 : ℕ) : ℝ) := by
      have h1 : (m : ℝ) ≤ 16 * ((q + 1 : ℕ) : ℝ) := by exact_mod_cast hm_lt.le
      calc Real.sqrt (m : ℝ)
          ≤ Real.sqrt (16 * ((q + 1 : ℕ) : ℝ)) := Real.sqrt_le_sqrt h1
        _ = Real.sqrt 16 * Real.sqrt ((q + 1 : ℕ) : ℝ) := Real.sqrt_mul (by norm_num) _
        _ = 4 * Real.sqrt ((q + 1 : ℕ) : ℝ) := by
            have : Real.sqrt 16 = 4 := by
              rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
            rw [this]
    rw [div_le_div_iff₀ (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_pos.mpr (by exact_mod_cast hm))]
    linarith
  have hterm2 : (2 : ℝ) ^ q * (15 / 16 : ℝ) ^ m ≤ 8 / Real.sqrt (m : ℝ) := by
    have h16q : 16 * q ≤ m := by omega
    have hpow : (15 / 16 : ℝ) ^ m ≤ (15 / 16 : ℝ) ^ (16 * q) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) h16q
    have h215 : (2 : ℝ) * (15 / 16 : ℝ) ^ 16 ≤ 3 / 4 := by norm_num
    have hq_pow : (2 : ℝ) ^ q * (15 / 16 : ℝ) ^ m ≤ (3 / 4 : ℝ) ^ q := by
      calc (2 : ℝ) ^ q * (15 / 16 : ℝ) ^ m
          ≤ (2 : ℝ) ^ q * (15 / 16 : ℝ) ^ (16 * q) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = ((2 : ℝ) * (15 / 16 : ℝ) ^ 16) ^ q := by rw [pow_mul, ← mul_pow]
        _ ≤ (3 / 4 : ℝ) ^ q := pow_le_pow_left₀ (by positivity) h215 q
    have hsqrt_le : Real.sqrt (m : ℝ) ≤ 4 * ((q + 1 : ℕ) : ℝ) := by
      have hm_lt : m < 16 * (q + 1) := by omega
      have h1 : (m : ℝ) ≤ 16 * ((q + 1 : ℕ) : ℝ) := by exact_mod_cast hm_lt.le
      have hq1 : (1 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos q
      calc Real.sqrt (m : ℝ)
          ≤ Real.sqrt (16 * ((q + 1 : ℕ) : ℝ)) := Real.sqrt_le_sqrt h1
        _ = 4 * Real.sqrt ((q + 1 : ℕ) : ℝ) := by
            rw [Real.sqrt_mul (by norm_num), show Real.sqrt 16 = 4 by
              rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        _ ≤ 4 * ((q + 1 : ℕ) : ℝ) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            rw [Real.sqrt_le_left (by positivity)]
            nlinarith
    rw [le_div_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast hm))]
    calc ((2 : ℝ) ^ q * (15 / 16 : ℝ) ^ m) * Real.sqrt (m : ℝ)
        ≤ (3 / 4 : ℝ) ^ q * (4 * ((q + 1 : ℕ) : ℝ)) :=
          mul_le_mul hq_pow hsqrt_le (Real.sqrt_nonneg _) (by positivity)
      _ = 4 * (((q + 1 : ℕ) : ℝ) * (3 / 4 : ℝ) ^ q) := by ring
      _ ≤ 4 * 2 := mul_le_mul_of_nonneg_left (nat_succ_mul_three_quarters_le q) (by norm_num)
      _ = 8 := by norm_num
  calc ∑ c : Fin m → Fin 3, (∏ i : Fin m, w₃ i (c i)) *
        (∑ f : Fin m → Bool,
          (if (Finset.univ.filter (fun i => f i = true)).card = t then (1 : ℝ) else 0) *
          (∏ i : Fin m, q₃ i (c i) (f i)))
      ≤ ∑ c : Fin m → Fin 3, (∏ i : Fin m, w₃ i (c i)) *
          ((1 / Real.sqrt ((q + 1 : ℕ) : ℝ)) + (2 : ℝ) ^ q * (1 / 2 : ℝ) ^ Rfn c) := by
        refine Finset.sum_le_sum fun c _ => ?_
        refine mul_le_mul_of_nonneg_left ((hinner c).trans (hpoint c)) ?_
        exact Finset.prod_nonneg fun i _ => hw_nonneg i (c i)
    _ = (∑ c : Fin m → Fin 3, ∏ i : Fin m, w₃ i (c i)) * (1 / Real.sqrt ((q + 1 : ℕ) : ℝ)) +
          (2 : ℝ) ^ q * (∑ c : Fin m → Fin 3, (∏ i : Fin m, w₃ i (c i)) * (1 / 2 : ℝ) ^ Rfn c) := by
        simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => by ring
    _ = (1 / Real.sqrt ((q + 1 : ℕ) : ℝ)) + (2 : ℝ) ^ q * (15 / 16 : ℝ) ^ m := by
        rw [hsum_w, one_mul, hsum_exp]
    _ ≤ 4 / Real.sqrt (m : ℝ) + 8 / Real.sqrt (m : ℝ) := add_le_add hterm1 hterm2
    _ = 12 / Real.sqrt (m : ℝ) := by ring

private lemma sum_graph_weight_eq_one (k : ℕ) (q : Fin k → Fin k → ℝ) :
    (∑ G : SimpleGraph (Fin k),
      ∏ e ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2),
        if G.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2) = 1 := by
  let E := Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2)
  let eGraph : SimpleGraph (Fin k) ≃ ({p : Fin k × Fin k // p ∈ E} → Bool) :=
    { toFun := fun G e => decide (G.Adj e.1.1 e.1.2)
      invFun := fun f =>
        { Adj := fun u v =>
            if h : u < v then f ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩ = true
            else if h' : v < u then f ⟨(v, u), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩⟩ = true
            else False
          symm := ⟨by
            intro u v h
            rcases lt_trichotomy u v with huv | rfl | hvu
            · have hn : ¬ v < u := lt_asymm huv
              simpa [huv, hn] using h
            · simp at h
            · have hn : ¬ u < v := lt_asymm hvu
              simpa [hvu, hn] using h⟩
          loopless := ⟨by intro u h; simp at h⟩ }
      left_inv := fun G => by
        ext u v
        rcases lt_trichotomy u v with huv | rfl | hvu
        · simp [huv]
        · simp
        · have hn : ¬ u < v := lt_asymm hvu
          simp [hn, hvu, G.adj_comm]
      right_inv := fun f => by
        ext ⟨⟨u, v⟩, he⟩
        have huv : u < v := (Finset.mem_filter.mp he).2
        simp [huv] }
  let q' : {p : Fin k × Fin k // p ∈ E} → ℝ := fun e => q e.1.1 e.1.2
  have h1 :
      (∑ G : SimpleGraph (Fin k),
        ∏ e ∈ E, if G.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2) =
      ∑ f : ({p : Fin k × Fin k // p ∈ E} → Bool),
        ∏ e : {p : Fin k × Fin k // p ∈ E}, if f e = true then q' e else 1 - q' e := by
    refine Fintype.sum_equiv eGraph _ _ fun G => ?_
    rw [← Finset.prod_coe_sort E]
    refine Finset.prod_congr rfl fun ⟨e, he⟩ _ => ?_
    simp [eGraph, q']
  rw [h1, ← Fintype.prod_sum (fun (e : {p : Fin k × Fin k // p ∈ E}) (b : Bool) =>
    if b = true then q' e else 1 - q' e)]
  refine Finset.prod_eq_one fun e _ => ?_
  simp

private lemma graph_target_le : ∀ (k : ℕ), 1 ≤ k → ∀ (q : Fin k → Fin k → ℝ),
    (∀ i j, 1 / 16 ≤ q i j ∧ q i j ≤ 9 / 16) → ∀ (target : Fin k → ℕ),
    (∑ G : SimpleGraph (Fin k),
      (if ∀ u : Fin k, (Finset.univ.filter (fun v => G.Adj u v)).card = target u then (1 : ℝ) else 0) *
      (∏ e ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2),
        if G.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2))
    ≤ (12 : ℝ) ^ (k - 1) / Real.sqrt (((k - 1).factorial : ℕ) : ℝ)
  | 0, hk, _, _, _ => by omega
  | 1, _, q, hq, target => by
    rw [Nat.sub_self, pow_zero, Nat.factorial_zero, Nat.cast_one, Real.sqrt_one, div_one]
    calc (∑ G : SimpleGraph (Fin 1),
          (if ∀ u : Fin 1, (Finset.univ.filter (fun v => G.Adj u v)).card = target u then (1 : ℝ) else 0) *
          (∏ e ∈ Finset.univ.filter (fun p : Fin 1 × Fin 1 => p.1 < p.2),
            if G.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2))
        ≤ ∑ G : SimpleGraph (Fin 1),
          (∏ e ∈ Finset.univ.filter (fun p : Fin 1 × Fin 1 => p.1 < p.2),
            if G.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2) := by
          refine Finset.sum_le_sum fun G _ => ?_
          have hw : 0 ≤ ∏ e ∈ Finset.univ.filter (fun p : Fin 1 × Fin 1 => p.1 < p.2),
              if G.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2 := by
            refine Finset.prod_nonneg fun e _ => ?_
            have := hq e.1 e.2
            split_ifs <;> linarith
          by_cases hcond : ∀ u : Fin 1, (Finset.univ.filter (fun v => G.Adj u v)).card = target u
          · rw [if_pos hcond, one_mul]
          · rw [if_neg hcond, zero_mul]
            exact hw
      _ = 1 := sum_graph_weight_eq_one 1 q
  | m + 2, _, q, hq, target => by
    let k := m + 1
    have hk1 : 1 ≤ k := by omega
    let eSplit : SimpleGraph (Fin (k + 1)) ≃ (Fin k → Bool) × SimpleGraph (Fin k) :=
      { toFun := fun G =>
          (fun i => decide (G.Adj 0 i.succ),
           { Adj := fun i j => G.Adj i.succ j.succ
             symm := ⟨fun _ _ h => (G.adj_comm _ _).mp h⟩
             loopless := ⟨fun _ h => G.loopless.irrefl _ h⟩ })
        invFun := fun p =>
          { Adj := fun u v =>
              if hu : u = 0 then
                if hv : v = 0 then False else p.1 (v.pred hv) = true
              else
                if hv : v = 0 then p.1 (u.pred hu) = true
                else p.2.Adj (u.pred hu) (v.pred hv)
            symm := ⟨by
              intro u v h
              by_cases hu : u = 0 <;> by_cases hv : v = 0 <;> simp only [hu, hv, ↓reduceDIte] at h ⊢
              all_goals first | exact h | exact (p.2.adj_comm _ _).mp h⟩
            loopless := ⟨by
              intro u h
              by_cases hu : u = 0 <;> simp only [hu, ↓reduceDIte] at h
              · exact p.2.loopless.irrefl _ h⟩ }
        left_inv := fun G => by
          ext u v
          by_cases hu : u = 0 <;> by_cases hv : v = 0 <;> simp only [hu, hv, ↓reduceDIte]
          · subst hu; simp
          · subst hu; simp [Fin.succ_pred]
          · subst hv; simp [Fin.succ_pred, G.adj_comm]
          · simp [Fin.succ_pred]
        right_inv := fun ⟨s, G'⟩ => by
          refine Prod.ext ?_ ?_
          · ext i; simp [Fin.succ_ne_zero]
          · ext i j; simp [Fin.succ_ne_zero] }
    let q_top : Fin k → ℝ := fun i => q 0 i.succ
    let q_sub : Fin k → Fin k → ℝ := fun i j => q i.succ j.succ
    have hq_top : ∀ i, 1 / 16 ≤ q_top i ∧ q_top i ≤ 9 / 16 := fun i => hq 0 i.succ
    have hq_sub : ∀ i j, 1 / 16 ≤ q_sub i j ∧ q_sub i j ≤ 9 / 16 := fun i j => hq i.succ j.succ
    have hprod_split : ∀ (s : Fin k → Bool) (G' : SimpleGraph (Fin k)),
        (∏ e ∈ Finset.univ.filter (fun p : Fin (k + 1) × Fin (k + 1) => p.1 < p.2),
          if (eSplit.symm (s, G')).Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2) =
        (∏ i : Fin k, if s i = true then q_top i else 1 - q_top i) *
        (∏ e ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2),
          if G'.Adj e.1 e.2 then q_sub e.1 e.2 else 1 - q_sub e.1 e.2) := by
      intro s G'
      let E := Finset.univ.filter (fun p : Fin (k + 1) × Fin (k + 1) => p.1 < p.2)
      let E0 := E.filter (fun p => p.1 = 0)
      let E1 := E.filter (fun p => p.1 ≠ 0)
      have hpart : E = E0 ∪ E1 := by
        ext p; simp only [E0, E1, Finset.mem_union, Finset.mem_filter]; tauto
      have hdisj : Disjoint E0 E1 := by
        rw [Finset.disjoint_left]
        intro p hp0 hp1
        simp only [E0, E1, Finset.mem_filter] at hp0 hp1
        exact hp1.2 hp0.2
      change (∏ e ∈ E, if (eSplit.symm (s, G')).Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2) = _
      rw [hpart, Finset.prod_union hdisj]
      have hE0 : (∏ e ∈ E0, if (eSplit.symm (s, G')).Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2) =
          ∏ i : Fin k, if s i = true then q_top i else 1 - q_top i := by
        refine Finset.prod_bij (fun p hp => p.2.pred (by
          simp only [E0, E, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          intro h0
          rw [hp.2, h0] at hp
          exact lt_irrefl 0 hp.1)) ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro p1 hp1 p2 hp2 h
          simp only [E0, E, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
          refine Prod.ext ?_ (Fin.pred_inj.mp h)
          rw [hp1.2, hp2.2]
        · intro i _
          refine ⟨(0, i.succ), ?_, by simp⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.succ_pos i⟩, rfl⟩
        · intro p hp
          simp only [E0, E, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          have hp2 : p.2 ≠ 0 := by intro h0; rw [hp.2, h0] at hp; exact lt_irrefl 0 hp.1
          have hp1 : p.1 = 0 := hp.2
          simp only [eSplit, Equiv.coe_fn_symm_mk, hp1, hp2, ↓reduceDIte, q_top, Fin.succ_pred]
      have hE1 : (∏ e ∈ E1, if (eSplit.symm (s, G')).Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2) =
          ∏ e ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2),
            if G'.Adj e.1 e.2 then q_sub e.1 e.2 else 1 - q_sub e.1 e.2 := by
        refine Finset.prod_bij (fun p hp => (p.1.pred (Finset.mem_filter.mp hp).2, p.2.pred (by
          simp only [E1, E, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          intro h0
          have : p.1 < 0 := h0 ▸ hp.1
          exact absurd this (Fin.not_lt_zero p.1)))) ?_ ?_ ?_ ?_
        · intro p hp
          simp only [E1, E, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          rw [← Fin.succ_lt_succ_iff, Fin.succ_pred, Fin.succ_pred]
          exact hp.1
        · intro p1 hp1 p2 hp2 h
          simp only [Prod.mk.injEq] at h
          exact Prod.ext (Fin.pred_inj.mp h.1) (Fin.pred_inj.mp h.2)
        · intro e he
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
          refine ⟨(e.1.succ, e.2.succ), ?_, by simp⟩
          simp only [E1, E, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨Fin.succ_lt_succ_iff.mpr he, Fin.succ_ne_zero e.1⟩
        · intro p hp
          simp only [E1, E, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          have hp2 : p.2 ≠ 0 := by intro h0; have : p.1 < 0 := h0 ▸ hp.1; exact absurd this (Fin.not_lt_zero p.1)
          simp only [eSplit, Equiv.coe_fn_symm_mk, hp.2, hp2, ↓reduceDIte, q_sub, Fin.succ_pred]
      rw [hE0, hE1]
    have hdeg_split : ∀ (s : Fin k → Bool) (G' : SimpleGraph (Fin k)),
        (∀ u : Fin (k + 1), (Finset.univ.filter (fun v => (eSplit.symm (s, G')).Adj u v)).card = target u) →
        ((Finset.univ.filter (fun i : Fin k => s i = true)).card = target 0 ∧
         ∀ i : Fin k, (Finset.univ.filter (fun j : Fin k => G'.Adj i j)).card =
           target i.succ - (if s i = true then 1 else 0)) := by
      intro s G' hG
      have heSplit_zero : ∀ v : Fin (k + 1),
          (eSplit.symm (s, G')).Adj 0 v = (if hv : v = 0 then False else s (v.pred hv) = true) := by
        intro v
        simp only [eSplit, Equiv.coe_fn_symm_mk, ↓reduceDIte]
      have heSplit_succ : ∀ (i : Fin k) (v : Fin (k + 1)),
          (eSplit.symm (s, G')).Adj i.succ v = (if hv : v = 0 then s i = true else G'.Adj i (v.pred hv)) := by
        intro i v
        simp only [eSplit, Equiv.coe_fn_symm_mk, Fin.succ_ne_zero, ↓reduceDIte, Fin.pred_succ]
      constructor
      · have h0 := hG 0
        have heq : (Finset.univ.filter (fun v : Fin (k + 1) => (eSplit.symm (s, G')).Adj 0 v)).card =
            (Finset.univ.filter (fun i : Fin k => s i = true)).card := by
          refine Finset.card_bij (fun v hv => v.pred (by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, heSplit_zero] at hv
            intro h0'; simp [h0'] at hv)) ?_ ?_ ?_
          · intro v hv
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, heSplit_zero] at hv ⊢
            by_cases hv0 : v = 0
            · rw [dif_pos hv0] at hv; exact hv.elim
            · rw [dif_neg hv0] at hv; exact hv
          · intro v1 _ v2 _ h; exact Fin.pred_inj.mp h
          · intro i hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
            refine ⟨i.succ, ?_, by simp⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, heSplit_zero,
              Fin.succ_ne_zero, ↓reduceDIte, Fin.pred_succ]
            exact hi
        omega
      · intro i
        have hi := hG i.succ
        let F := Finset.univ.filter (fun v : Fin (k + 1) => (eSplit.symm (s, G')).Adj i.succ v)
        let F' := Finset.univ.filter (fun j : Fin k => G'.Adj i j)
        have hF_split : F.card = F'.card + (if s i = true then 1 else 0) := by
          have hsub : (F.erase 0).card = F'.card := by
            refine Finset.card_bij (fun v hv => v.pred (Finset.mem_erase.mp hv).1) ?_ ?_ ?_
            · intro v hv
              have hv0 : v ≠ 0 := (Finset.mem_erase.mp hv).1
              have hvF := (Finset.mem_erase.mp hv).2
              simp only [F, Finset.mem_filter, Finset.mem_univ, true_and, heSplit_succ,
                hv0, ↓reduceDIte] at hvF
              simp only [F', Finset.mem_filter, Finset.mem_univ, true_and]
              exact hvF
            · intro v1 _ v2 _ h; exact Fin.pred_inj.mp h
            · intro j hj
              simp only [F', Finset.mem_filter, Finset.mem_univ, true_and] at hj
              refine ⟨j.succ, ?_, by simp⟩
              rw [Finset.mem_erase]
              refine ⟨Fin.succ_ne_zero j, ?_⟩
              simp only [F, Finset.mem_filter, Finset.mem_univ, true_and, heSplit_succ,
                Fin.succ_ne_zero, ↓reduceDIte, Fin.pred_succ]
              exact hj
          by_cases hsi : s i = true
          · have h0mem : (0 : Fin (k + 1)) ∈ F := by
              simp only [F, Finset.mem_filter, Finset.mem_univ, true_and, heSplit_succ, ↓reduceDIte]
              exact hsi
            rw [← Finset.card_erase_add_one h0mem, hsub, if_pos hsi]
          · have h0not : (0 : Fin (k + 1)) ∉ F := by
              simp only [F, Finset.mem_filter, Finset.mem_univ, true_and, heSplit_succ, ↓reduceDIte]
              exact hsi
            rw [← Finset.erase_eq_of_notMem h0not, hsub, if_neg hsi, add_zero]
        have hF_eq : F.card = target i.succ := hi
        have hF'_eq : F'.card = (Finset.univ.filter (fun j : Fin k => G'.Adj i j)).card := rfl
        rw [hF_eq, hF'_eq] at hF_split
        omega
    have hw_nonneg_s : ∀ s : Fin k → Bool,
        0 ≤ ∏ i : Fin k, if s i = true then q_top i else 1 - q_top i := by
      intro s
      refine Finset.prod_nonneg fun i _ => ?_
      have := hq_top i
      split_ifs <;> linarith
    have hw_nonneg_G' : ∀ G' : SimpleGraph (Fin k),
        0 ≤ ∏ e ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2),
          if G'.Adj e.1 e.2 then q_sub e.1 e.2 else 1 - q_sub e.1 e.2 := by
      intro G'
      refine Finset.prod_nonneg fun e _ => ?_
      have := hq_sub e.1 e.2
      split_ifs <;> linarith
    have hsplit_sum :
        (∑ G : SimpleGraph (Fin (m + 2)),
          (if ∀ u : Fin (m + 2), (Finset.univ.filter (fun v => G.Adj u v)).card = target u then (1 : ℝ) else 0) *
          (∏ e ∈ Finset.univ.filter (fun p : Fin (m + 2) × Fin (m + 2) => p.1 < p.2),
            if G.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2)) =
        ∑ s : Fin k → Bool, ∑ G' : SimpleGraph (Fin k),
          (if ∀ u : Fin (k + 1), (Finset.univ.filter (fun v => (eSplit.symm (s, G')).Adj u v)).card = target u then (1 : ℝ) else 0) *
          (∏ e ∈ Finset.univ.filter (fun p : Fin (k + 1) × Fin (k + 1) => p.1 < p.2),
            if (eSplit.symm (s, G')).Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2) := by
      rw [← Fintype.sum_equiv eSplit.symm _ _ (fun _ => rfl), Fintype.sum_prod_type]
    have hstep1 :
        (∑ s : Fin k → Bool, ∑ G' : SimpleGraph (Fin k),
          (if ∀ u : Fin (k + 1), (Finset.univ.filter (fun v => (eSplit.symm (s, G')).Adj u v)).card = target u then (1 : ℝ) else 0) *
          (∏ e ∈ Finset.univ.filter (fun p : Fin (k + 1) × Fin (k + 1) => p.1 < p.2),
            if (eSplit.symm (s, G')).Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2)) ≤
        ∑ s : Fin k → Bool,
          (if (Finset.univ.filter (fun i : Fin k => s i = true)).card = target 0 then (1 : ℝ) else 0) *
          (∏ i : Fin k, if s i = true then q_top i else 1 - q_top i) *
          (∑ G' : SimpleGraph (Fin k),
            (if ∀ i : Fin k, (Finset.univ.filter (fun j : Fin k => G'.Adj i j)).card =
                target i.succ - (if s i = true then 1 else 0) then (1 : ℝ) else 0) *
            (∏ e ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2),
              if G'.Adj e.1 e.2 then q_sub e.1 e.2 else 1 - q_sub e.1 e.2)) := by
      refine Finset.sum_le_sum fun s _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun G' _ => ?_
      rw [hprod_split s G']
      have hwG' := hw_nonneg_G' G'
      have hws := hw_nonneg_s s
      by_cases hcond : ∀ u : Fin (k + 1),
          (Finset.univ.filter (fun v => (eSplit.symm (s, G')).Adj u v)).card = target u
      · obtain ⟨hs0, hGi⟩ := hdeg_split s G' hcond
        rw [if_pos hcond, if_pos hs0, if_pos hGi]
        ring_nf
        exact le_rfl
      · rw [if_neg hcond, zero_mul]
        positivity
    have hIH : ∀ s : Fin k → Bool,
        (∑ G' : SimpleGraph (Fin k),
          (if ∀ i : Fin k, (Finset.univ.filter (fun j : Fin k => G'.Adj i j)).card =
              target i.succ - (if s i = true then 1 else 0) then (1 : ℝ) else 0) *
          (∏ e ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2),
            if G'.Adj e.1 e.2 then q_sub e.1 e.2 else 1 - q_sub e.1 e.2)) ≤
        (12 : ℝ) ^ (k - 1) / Real.sqrt (((k - 1).factorial : ℕ) : ℝ) :=
      fun s => graph_target_le k hk1 q_sub hq_sub (fun i => target i.succ - (if s i = true then 1 else 0))
    have houter : (∑ s : Fin k → Bool,
          (if (Finset.univ.filter (fun i : Fin k => s i = true)).card = target 0 then (1 : ℝ) else 0) *
          (∏ i : Fin k, if s i = true then q_top i else 1 - q_top i)) ≤
        12 / Real.sqrt (k : ℝ) :=
      bernoulli_point_le hk1 q_top hq_top (target 0)
    have hmul_eq : (12 / Real.sqrt (k : ℝ)) * ((12 : ℝ) ^ (k - 1) / Real.sqrt (((k - 1).factorial : ℕ) : ℝ)) =
        (12 : ℝ) ^ (m + 2 - 1) / Real.sqrt (((m + 2 - 1).factorial : ℕ) : ℝ) := by
      have hk_eq : m + 2 - 1 = k := rfl
      have hkm : k = (k - 1) + 1 := by omega
      have hfact : (k.factorial : ℝ) = (k : ℝ) * ((k - 1).factorial : ℝ) := by
        have hnat : k.factorial = k * (k - 1).factorial := by
          conv_lhs => rw [hkm, Nat.factorial_succ, ← hkm]
        exact_mod_cast hnat
      have hsqrt_mul : Real.sqrt (k : ℝ) * Real.sqrt (((k - 1).factorial : ℕ) : ℝ) =
          Real.sqrt ((k.factorial : ℕ) : ℝ) := by
        rw [← Real.sqrt_mul (Nat.cast_nonneg k), ← hfact]
      have hpow : (12 : ℝ) * (12 : ℝ) ^ (k - 1) = (12 : ℝ) ^ k := by
        conv_rhs => rw [hkm, pow_succ']
      rw [hk_eq, div_mul_div_comm, hpow, hsqrt_mul]
    calc (∑ G : SimpleGraph (Fin (m + 2)),
          (if ∀ u : Fin (m + 2), (Finset.univ.filter (fun v => G.Adj u v)).card = target u then (1 : ℝ) else 0) *
          (∏ e ∈ Finset.univ.filter (fun p : Fin (m + 2) × Fin (m + 2) => p.1 < p.2),
            if G.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2))
        = ∑ s : Fin k → Bool, ∑ G' : SimpleGraph (Fin k),
            (if ∀ u : Fin (k + 1), (Finset.univ.filter (fun v => (eSplit.symm (s, G')).Adj u v)).card = target u then (1 : ℝ) else 0) *
            (∏ e ∈ Finset.univ.filter (fun p : Fin (k + 1) × Fin (k + 1) => p.1 < p.2),
              if (eSplit.symm (s, G')).Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2) := hsplit_sum
      _ ≤ ∑ s : Fin k → Bool,
            (if (Finset.univ.filter (fun i : Fin k => s i = true)).card = target 0 then (1 : ℝ) else 0) *
            (∏ i : Fin k, if s i = true then q_top i else 1 - q_top i) *
            (∑ G' : SimpleGraph (Fin k),
              (if ∀ i : Fin k, (Finset.univ.filter (fun j : Fin k => G'.Adj i j)).card =
                  target i.succ - (if s i = true then 1 else 0) then (1 : ℝ) else 0) *
              (∏ e ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2),
                if G'.Adj e.1 e.2 then q_sub e.1 e.2 else 1 - q_sub e.1 e.2)) := hstep1
      _ ≤ ∑ s : Fin k → Bool,
            (if (Finset.univ.filter (fun i : Fin k => s i = true)).card = target 0 then (1 : ℝ) else 0) *
            (∏ i : Fin k, if s i = true then q_top i else 1 - q_top i) *
            ((12 : ℝ) ^ (k - 1) / Real.sqrt (((k - 1).factorial : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum fun s _ => ?_
          refine mul_le_mul_of_nonneg_left (hIH s) ?_
          exact mul_nonneg (by split_ifs <;> norm_num) (hw_nonneg_s s)
      _ = (∑ s : Fin k → Bool,
            (if (Finset.univ.filter (fun i : Fin k => s i = true)).card = target 0 then (1 : ℝ) else 0) *
            (∏ i : Fin k, if s i = true then q_top i else 1 - q_top i)) *
            ((12 : ℝ) ^ (k - 1) / Real.sqrt (((k - 1).factorial : ℕ) : ℝ)) := (Finset.sum_mul _ _ _).symm
      _ ≤ (12 / Real.sqrt (k : ℝ)) * ((12 : ℝ) ^ (k - 1) / Real.sqrt (((k - 1).factorial : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right houter (by positivity)
      _ = (12 : ℝ) ^ (m + 2 - 1) / Real.sqrt (((m + 2 - 1).factorial : ℕ) : ℝ) := hmul_eq

end Helpers

theorem OMA.solution : OMA.R_Erdos82_erdos_82_variants_F_upper_bound_R1.H1 := by
  refine ⟨1000, by norm_num, fun n hn U hU => ?_⟩
  set k : ℕ := U.card
  have hk2 : 2 ≤ k := hU
  have hk1 : 1 ≤ k := by omega
  have hkn : k ≤ n := by
    simpa [k] using (U.card_le_univ.trans_eq (Fintype.card_fin n))
  let emb : Fin k ↪o Fin n := U.orderEmbOfFin rfl
  let p_edge : Fin n → Fin n → ℝ := fun u v =>
    (1 / 4 + (u : ℝ) / (2 * n)) * (1 / 4 + (v : ℝ) / (2 * n))
  have hp_bound : ∀ u v : Fin n, 1 / 16 ≤ p_edge u v ∧ p_edge u v ≤ 9 / 16 := by
    intro u v
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h1 (w : Fin n) : 1 / 4 ≤ 1 / 4 + (w : ℝ) / (2 * n) ∧ 1 / 4 + (w : ℝ) / (2 * n) ≤ 3 / 4 := by
      have hw0 : (0 : ℝ) ≤ (w : ℝ) := Nat.cast_nonneg w
      have hw1 : (w : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr w.isLt.le
      constructor
      · have : 0 ≤ (w : ℝ) / (2 * (n : ℝ)) := by positivity
        linarith
      · have : (w : ℝ) / (2 * (n : ℝ)) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          linarith
        linarith
    obtain ⟨hu0, hu1⟩ := h1 u
    obtain ⟨hv0, hv1⟩ := h1 v
    dsimp only [p_edge]
    exact ⟨by nlinarith, by nlinarith⟩
  let q : Fin k → Fin k → ℝ := fun i j => p_edge (emb i) (emb j)
  have hq_bound : ∀ i j, 1 / 16 ≤ q i j ∧ q i j ≤ 9 / 16 := fun i j => hp_bound (emb i) (emb j)
  let E_n := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)
  let E_U := E_n.filter (fun p => p.1 ∈ U ∧ p.2 ∈ U)
  let E_out := E_n \ E_U
  let E_k := Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2)
  let eEdge : {p : Fin k × Fin k // p ∈ E_k} ≃ {p : Fin n × Fin n // p ∈ E_U} :=
    { toFun := fun p => ⟨(emb p.1.1, emb p.1.2), by
        have hp := (Finset.mem_filter.mp p.2).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, emb.lt_iff_lt.mpr hp⟩, ?_, ?_⟩
        · have : emb p.1.1 ∈ Set.range emb := Set.mem_range_self _
          rwa [Finset.range_orderEmbOfFin] at this
        · have : emb p.1.2 ∈ Set.range emb := Set.mem_range_self _
          rwa [Finset.range_orderEmbOfFin] at this⟩
      invFun := fun p =>
        let hmem1 : p.1.1 ∈ Set.range emb := by
          rw [Finset.range_orderEmbOfFin]; exact (Finset.mem_filter.mp p.2).2.1
        let hmem2 : p.1.2 ∈ Set.range emb := by
          rw [Finset.range_orderEmbOfFin]; exact (Finset.mem_filter.mp p.2).2.2
        ⟨(Classical.choose hmem1, Classical.choose hmem2), by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rw [← emb.lt_iff_lt, Classical.choose_spec hmem1, Classical.choose_spec hmem2]
          exact (Finset.mem_filter.mp (Finset.mem_filter.mp p.2).1).2⟩
      left_inv := fun ⟨⟨i, j⟩, _⟩ => by
        refine Subtype.ext (Prod.ext ?_ ?_) <;> dsimp only
        · exact emb.injective (Classical.choose_spec (show emb i ∈ Set.range emb from ⟨i, rfl⟩))
        · exact emb.injective (Classical.choose_spec (show emb j ∈ Set.range emb from ⟨j, rfl⟩))
      right_inv := fun ⟨⟨u, v⟩, hp⟩ => by
        refine Subtype.ext (Prod.ext ?_ ?_) <;> dsimp only
        · exact Classical.choose_spec (show u ∈ Set.range emb by
            rw [Finset.range_orderEmbOfFin]; exact (Finset.mem_filter.mp hp).2.1)
        · exact Classical.choose_spec (show v ∈ Set.range emb by
            rw [Finset.range_orderEmbOfFin]; exact (Finset.mem_filter.mp hp).2.2) }
  let eGraph_n : SimpleGraph (Fin n) ≃ ({p : Fin n × Fin n // p ∈ E_n} → Bool) :=
    { toFun := fun G e => decide (G.Adj e.1.1 e.1.2)
      invFun := fun f =>
        { Adj := fun u v =>
            if h : u < v then f ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩ = true
            else if h' : v < u then f ⟨(v, u), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩⟩ = true
            else False
          symm := ⟨by
            intro u v h
            rcases lt_trichotomy u v with huv | rfl | hvu
            · have hn : ¬ v < u := lt_asymm huv; simpa [huv, hn] using h
            · simp at h
            · have hn : ¬ u < v := lt_asymm hvu; simpa [hvu, hn] using h⟩
          loopless := ⟨by intro u h; simp at h⟩ }
      left_inv := fun G => by
        ext u v
        rcases lt_trichotomy u v with huv | rfl | hvu
        · simp [huv]
        · simp
        · have hn : ¬ u < v := lt_asymm hvu; simp [hn, hvu, G.adj_comm]
      right_inv := fun f => by
        ext ⟨⟨u, v⟩, he⟩
        have huv : u < v := (Finset.mem_filter.mp he).2
        simp only [dif_pos huv]
        cases f ⟨(u, v), he⟩ <;> simp }
  let eGraph_k : SimpleGraph (Fin k) ≃ ({p : Fin k × Fin k // p ∈ E_k} → Bool) :=
    { toFun := fun H e => decide (H.Adj e.1.1 e.1.2)
      invFun := fun f =>
        { Adj := fun u v =>
            if h : u < v then f ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩ = true
            else if h' : v < u then f ⟨(v, u), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩⟩ = true
            else False
          symm := ⟨by
            intro u v h
            rcases lt_trichotomy u v with huv | rfl | hvu
            · have hn : ¬ v < u := lt_asymm huv; simpa [huv, hn] using h
            · simp at h
            · have hn : ¬ u < v := lt_asymm hvu; simpa [hvu, hn] using h⟩
          loopless := ⟨by intro u h; simp at h⟩ }
      left_inv := fun H => by
        ext u v
        rcases lt_trichotomy u v with huv | rfl | hvu
        · simp [huv]
        · simp
        · have hn : ¬ u < v := lt_asymm hvu; simp [hn, hvu, H.adj_comm]
      right_inv := fun f => by
        ext ⟨⟨u, v⟩, he⟩
        have huv : u < v := (Finset.mem_filter.mp he).2
        simp only [dif_pos huv]
        cases f ⟨(u, v), he⟩ <;> simp }
  let eFnSplit : ({p : Fin n × Fin n // p ∈ E_n} → Bool) ≃
      ({p : Fin n × Fin n // p ∈ E_U} → Bool) × ({p : Fin n × Fin n // p ∈ E_out} → Bool) :=
    { toFun := fun f => (fun p => f ⟨p.1, (Finset.mem_filter.mp p.2).1⟩,
        fun p => f ⟨p.1, (Finset.mem_sdiff.mp p.2).1⟩)
      invFun := fun pr p =>
        if h : p.1 ∈ E_U then pr.1 ⟨p.1, h⟩
        else pr.2 ⟨p.1, Finset.mem_sdiff.mpr ⟨p.2, h⟩⟩
      left_inv := fun f => by ext p; by_cases h : p.1 ∈ E_U <;> simp [h]
      right_inv := fun pr => by
        ext p
        · simp [p.2]
        · have hn : p.1 ∉ E_U := (Finset.mem_sdiff.mp p.2).2
          simp [hn] }
  let eSplit : SimpleGraph (Fin n) ≃ SimpleGraph (Fin k) × ({p : Fin n × Fin n // p ∈ E_out} → Bool) :=
    eGraph_n.trans (eFnSplit.trans (Equiv.prodCongr (Equiv.arrowCongr eEdge.symm (Equiv.refl Bool) |>.trans eGraph_k.symm) (Equiv.refl _)))
  have heSplit_adj : ∀ (H : SimpleGraph (Fin k)) (f_out : {p : Fin n × Fin n // p ∈ E_out} → Bool) (u v : Fin n),
      (eSplit.symm (H, f_out)).Adj u v =
        (if h : u < v then
          (if hu : (u, v) ∈ E_U then decide (H.Adj (eEdge.symm ⟨(u, v), hu⟩).1.1 (eEdge.symm ⟨(u, v), hu⟩).1.2)
           else f_out ⟨(u, v), Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, hu⟩⟩) = true
         else if h' : v < u then
          (if hv : (v, u) ∈ E_U then decide (H.Adj (eEdge.symm ⟨(v, u), hv⟩).1.1 (eEdge.symm ⟨(v, u), hv⟩).1.2)
           else f_out ⟨(v, u), Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩, hv⟩⟩) = true
         else False) :=
    fun _ _ _ _ => rfl
  have hadj_eq : ∀ (H : SimpleGraph (Fin k)) (f_out : {p : Fin n × Fin n // p ∈ E_out} → Bool)
      (i j : Fin k), (eSplit.symm (H, f_out)).Adj (emb i) (emb j) ↔ H.Adj i j := by
    intro H f_out i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · have hij' : emb i < emb j := emb.lt_iff_lt.mpr hij
      have hmem : (emb i, emb j) ∈ E_U := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij'⟩, ?_, ?_⟩
        · have : emb i ∈ Set.range emb := Set.mem_range_self _
          rwa [Finset.range_orderEmbOfFin] at this
        · have : emb j ∈ Set.range emb := Set.mem_range_self _
          rwa [Finset.range_orderEmbOfFin] at this
      have he1 : eEdge.symm ⟨(emb i, emb j), hmem⟩ = ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩⟩ := by
        rw [Equiv.symm_apply_eq]; ext <;> rfl
      rw [heSplit_adj]
      simp [hij', hmem, he1]
    · simp
    · have hji' : emb j < emb i := emb.lt_iff_lt.mpr hji
      have hij' : ¬ emb i < emb j := lt_asymm hji'
      have hmem : (emb j, emb i) ∈ E_U := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji'⟩, ?_, ?_⟩
        · have : emb j ∈ Set.range emb := Set.mem_range_self _
          rwa [Finset.range_orderEmbOfFin] at this
        · have : emb i ∈ Set.range emb := Set.mem_range_self _
          rwa [Finset.range_orderEmbOfFin] at this
      have he1 : eEdge.symm ⟨(emb j, emb i), hmem⟩ = ⟨(j, i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji⟩⟩ := by
        rw [Equiv.symm_apply_eq]; ext <;> rfl
      rw [heSplit_adj]
      simp [hij', hji', hmem, he1, H.adj_comm]
  have hdeg_iff : ∀ (H : SimpleGraph (Fin k)) (f_out : {p : Fin n × Fin n // p ∈ E_out} → Bool),
      (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => (eSplit.symm (H, f_out)).Adj u v)).card = d) ↔
      (∃ d ∈ Finset.range k, ∀ i : Fin k, (Finset.univ.filter (fun j : Fin k => H.Adj i j)).card = d) := by
    intro H f_out
    have hcard : ∀ i : Fin k,
        (U.filter (fun v => (eSplit.symm (H, f_out)).Adj (emb i) v)).card =
        (Finset.univ.filter (fun j : Fin k => H.Adj i j)).card := by
      intro i
      refine Finset.card_bij (fun v hv =>
        let hmem : v ∈ Set.range emb := by
          rw [Finset.range_orderEmbOfFin]; exact (Finset.mem_filter.mp hv).1
        Classical.choose hmem) ?_ ?_ ?_
      · intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        have hmem : v ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hv.1
        have heq : emb (Classical.choose hmem) = v := Classical.choose_spec hmem
        rw [← heq] at hv
        exact (hadj_eq H f_out i _).mp hv.2
      · intro v1 hv1 v2 hv2 h
        have h1 : v1 ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact (Finset.mem_filter.mp hv1).1
        have h2 : v2 ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact (Finset.mem_filter.mp hv2).1
        have := congrArg emb h
        rwa [Classical.choose_spec h1, Classical.choose_spec h2] at this
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        have hU : emb j ∈ U := by
          have : emb j ∈ Set.range emb := Set.mem_range_self _; rwa [Finset.range_orderEmbOfFin] at this
        refine ⟨emb j, Finset.mem_filter.mpr ⟨hU, (hadj_eq H f_out i j).mpr hj⟩, ?_⟩
        exact emb.injective (Classical.choose_spec (show emb j ∈ Set.range emb by
          rw [Finset.range_orderEmbOfFin]; exact hU))
    constructor
    · rintro ⟨d, hd⟩
      have hd' : ∀ i : Fin k, (Finset.univ.filter (fun j : Fin k => H.Adj i j)).card = d := by
        intro i
        have hU : emb i ∈ U := by
          have : emb i ∈ Set.range emb := Set.mem_range_self _; rwa [Finset.range_orderEmbOfFin] at this
        rw [← hcard i]
        exact hd (emb i) hU
      have hdlt : d < k := by
        let i0 : Fin k := ⟨0, hk1⟩
        rw [← hd' i0]
        have hnot : i0 ∉ Finset.univ.filter (fun j : Fin k => H.Adj i0 j) := by
          simp
        have hss : Finset.univ.filter (fun j : Fin k => H.Adj i0 j) ⊂ Finset.univ :=
          Finset.ssubset_univ_iff.mpr (fun h => by rw [h] at hnot; exact hnot (Finset.mem_univ _))
        simpa using Finset.card_lt_card hss
      exact ⟨d, Finset.mem_range.mpr hdlt, hd'⟩
    · rintro ⟨d, _, hd⟩
      refine ⟨d, fun u hu => ?_⟩
      have hmem : u ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hu
      obtain ⟨i, rfl⟩ := hmem
      rw [hcard i]
      exact hd i
  have hw_split : ∀ (H : SimpleGraph (Fin k)) (f_out : {p : Fin n × Fin n // p ∈ E_out} → Bool),
      (∏ e ∈ E_n,
        if (eSplit.symm (H, f_out)).Adj e.1 e.2
        then (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))
        else 1 - (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))) =
      (∏ e ∈ E_k, if H.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2) *
      (∏ e : {p : Fin n × Fin n // p ∈ E_out},
        if f_out e = true then p_edge e.1.1 e.1.2 else 1 - p_edge e.1.1 e.1.2) := by
    intro H f_out
    have hpart : E_n = E_U ∪ E_out := (Finset.union_sdiff_of_subset (Finset.filter_subset _ _)).symm
    have hdisj : Disjoint E_U E_out :=
      Finset.disjoint_left.mpr fun _ hx1 hx2 => (Finset.mem_sdiff.mp hx2).2 hx1
    rw [hpart, Finset.prod_union hdisj]
    have hEU : (∏ e ∈ E_U, if (eSplit.symm (H, f_out)).Adj e.1 e.2 then p_edge e.1 e.2 else 1 - p_edge e.1 e.2) =
        ∏ e ∈ E_k, if H.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2 := by
      rw [← Finset.prod_coe_sort E_U, ← Finset.prod_coe_sort E_k]
      refine Fintype.prod_equiv eEdge.symm _ _ fun ⟨⟨u, v⟩, huv⟩ => ?_
      have huU : u ∈ U := (Finset.mem_filter.mp huv).2.1
      have hvU : v ∈ U := (Finset.mem_filter.mp huv).2.2
      have hmu : u ∈ Set.range emb := by rwa [Finset.range_orderEmbOfFin]
      have hmv : v ∈ Set.range emb := by rwa [Finset.range_orderEmbOfFin]
      obtain ⟨i, rfl⟩ := hmu
      obtain ⟨j, rfl⟩ := hmv
      have hadj : (eSplit.symm (H, f_out)).Adj (emb i) (emb j) ↔ H.Adj i j := hadj_eq H f_out i j
      have heij : (eEdge.symm ⟨(emb i, emb j), huv⟩).1 = (i, j) := by
        have : eEdge.symm ⟨(emb i, emb j), huv⟩ = ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            emb.lt_iff_lt.mp (Finset.mem_filter.mp (Finset.mem_filter.mp huv).1).2⟩⟩ := by
          rw [Equiv.symm_apply_eq]; ext <;> rfl
        rw [this]
      have heij1 : (eEdge.symm ⟨(emb i, emb j), huv⟩).1.1 = i := congrArg Prod.fst heij
      have heij2 : (eEdge.symm ⟨(emb i, emb j), huv⟩).1.2 = j := congrArg Prod.snd heij
      rw [heij1, heij2]
      dsimp only [q]
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd (hadj.mp h1) h2
      · exact absurd (hadj.mpr h2) h1
      · rfl
    have hEout : (∏ e ∈ E_out, if (eSplit.symm (H, f_out)).Adj e.1 e.2 then p_edge e.1 e.2 else 1 - p_edge e.1 e.2) =
        ∏ e : {p : Fin n × Fin n // p ∈ E_out},
          if f_out e = true then p_edge e.1.1 e.1.2 else 1 - p_edge e.1.1 e.1.2 := by
      rw [← Finset.prod_coe_sort E_out]
      refine Finset.prod_congr rfl fun ⟨⟨u, v⟩, huv⟩ _ => ?_
      have huv_n : (u, v) ∈ E_n := (Finset.mem_sdiff.mp huv).1
      have hlt : u < v := (Finset.mem_filter.mp huv_n).2
      have hnotU : (u, v) ∉ E_U := (Finset.mem_sdiff.mp huv).2
      rw [heSplit_adj]
      simp [hlt, hnotU]
    rw [hEU, hEout]
  have hsum_out : (∑ f_out : {p : Fin n × Fin n // p ∈ E_out} → Bool,
      ∏ e : {p : Fin n × Fin n // p ∈ E_out},
        if f_out e = true then p_edge e.1.1 e.1.2 else 1 - p_edge e.1.1 e.1.2) = 1 := by
    rw [← Fintype.prod_sum (fun (e : {p : Fin n × Fin n // p ∈ E_out}) (b : Bool) =>
      if b = true then p_edge e.1.1 e.1.2 else 1 - p_edge e.1.1 e.1.2)]
    refine Finset.prod_eq_one fun e _ => ?_
    rw [Fintype.sum_bool]
    simp
  have hreduce :
      (∑ G : SimpleGraph (Fin n),
        (if ∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d then (1 : ℝ) else 0) *
        (∏ e ∈ E_n,
          if G.Adj e.1 e.2
          then (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))
          else 1 - (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n)))) =
      ∑ H : SimpleGraph (Fin k),
        (if ∃ d ∈ Finset.range k, ∀ i : Fin k, (Finset.univ.filter (fun j : Fin k => H.Adj i j)).card = d
          then (1 : ℝ) else 0) *
        (∏ e ∈ E_k, if H.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2) := by
    rw [← Fintype.sum_equiv eSplit.symm _ _ (fun p => by rfl)]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun H _ => ?_
    have hrw : ∀ f_out : {p : Fin n × Fin n // p ∈ E_out} → Bool,
        (if ∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => (eSplit.symm (H, f_out)).Adj u v)).card = d then (1 : ℝ) else 0) *
        (∏ e ∈ E_n,
          if (eSplit.symm (H, f_out)).Adj e.1 e.2
          then (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))
          else 1 - (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))) =
        ((if ∃ d ∈ Finset.range k, ∀ i : Fin k, (Finset.univ.filter (fun j : Fin k => H.Adj i j)).card = d
            then (1 : ℝ) else 0) *
          (∏ e ∈ E_k, if H.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2)) *
        (∏ e : {p : Fin n × Fin n // p ∈ E_out},
          if f_out e = true then p_edge e.1.1 e.1.2 else 1 - p_edge e.1.1 e.1.2) := by
      intro f_out
      have hite : (if ∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => (eSplit.symm (H, f_out)).Adj u v)).card = d
            then (1 : ℝ) else 0) =
          if ∃ d ∈ Finset.range k, ∀ i : Fin k, (Finset.univ.filter (fun j : Fin k => H.Adj i j)).card = d
            then (1 : ℝ) else 0 := by
        split_ifs with h1 h2 h2
        · rfl
        · exact absurd ((hdeg_iff H f_out).mp h1) h2
        · exact absurd ((hdeg_iff H f_out).mpr h2) h1
        · rfl
      rw [hite]
      change _ * (∏ e ∈ E_n, if (eSplit.symm (H, f_out)).Adj e.1 e.2 then p_edge e.1 e.2 else 1 - p_edge e.1 e.2) = _
      rw [hw_split H f_out]
      ring
    simp_rw [hrw, ← Finset.mul_sum, hsum_out, mul_one]
  have hw_k_nonneg : ∀ H : SimpleGraph (Fin k),
      0 ≤ ∏ e ∈ E_k, if H.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2 := by
    intro H
    refine Finset.prod_nonneg fun e _ => ?_
    have := hq_bound e.1 e.2
    split_ifs <;> linarith
  have hsum_d :
      (∑ H : SimpleGraph (Fin k),
        (if ∃ d ∈ Finset.range k, ∀ i : Fin k, (Finset.univ.filter (fun j : Fin k => H.Adj i j)).card = d
          then (1 : ℝ) else 0) *
        (∏ e ∈ E_k, if H.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2)) ≤
      ∑ d ∈ Finset.range k, ∑ H : SimpleGraph (Fin k),
        (if ∀ i : Fin k, (Finset.univ.filter (fun j : Fin k => H.Adj i j)).card = d then (1 : ℝ) else 0) *
        (∏ e ∈ E_k, if H.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2) := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun H _ => ?_
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (hw_k_nonneg H)
    by_cases hH : ∃ d ∈ Finset.range k, ∀ i : Fin k, (Finset.univ.filter (fun j : Fin k => H.Adj i j)).card = d
    · obtain ⟨d, hd, hdi⟩ := hH
      rw [if_pos ⟨d, hd, hdi⟩]
      refine le_trans ?_ (Finset.single_le_sum (fun d' _ => by split_ifs <;> norm_num) hd)
      rw [if_pos hdi]
    · rw [if_neg hH]
      exact Finset.sum_nonneg fun d' _ => by split_ifs <;> norm_num
  have hbound_k : (k : ℝ) * ((12 : ℝ) ^ (k - 1) / Real.sqrt (((k - 1).factorial : ℕ) : ℝ)) ≤
      (n : ℝ) * (1000 / (k : ℝ)) ^ ((k : ℝ) / 2) := by
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hkn_real : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    have hfact_eq : Real.sqrt (((k - 1).factorial : ℕ) : ℝ) * Real.sqrt (k : ℝ) =
        Real.sqrt ((k.factorial : ℕ) : ℝ) := by
      have hkm : k = (k - 1) + 1 := by omega
      have hf : (k.factorial : ℝ) = ((k - 1).factorial : ℝ) * (k : ℝ) := by
        have hf_nat : k.factorial = (k - 1).factorial * k := by
          calc k.factorial = ((k - 1) + 1).factorial := by rw [← hkm]
            _ = (k - 1 + 1) * (k - 1).factorial := Nat.factorial_succ (k - 1)
            _ = (k - 1).factorial * k := by rw [← hkm, mul_comm]
        exact_mod_cast hf_nat
      rw [← Real.sqrt_mul (by positivity), ← hf]
    have hfact_lb := factorial_mul_exp_ge_pow k
    have hsqrt_fact : (k : ℝ) ^ ((k : ℝ) / 2) ≤ (Real.exp 1) ^ ((k : ℝ) / 2) * Real.sqrt ((k.factorial : ℕ) : ℝ) := by
      have hsq : ((k : ℝ) ^ ((k : ℝ) / 2)) ^ 2 ≤ ((Real.exp 1) ^ ((k : ℝ) / 2) * Real.sqrt ((k.factorial : ℕ) : ℝ)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        have hp1 : ((k : ℝ) ^ ((k : ℝ) / 2)) ^ 2 = (k : ℝ) ^ k := by
          rw [← Real.rpow_natCast ((k : ℝ) ^ ((k : ℝ) / 2)) 2, ← Real.rpow_mul (Nat.cast_nonneg k),
            show ((k : ℝ) / 2) * ((2 : ℕ) : ℝ) = (k : ℝ) by push_cast; ring, Real.rpow_natCast]
        have hp2 : ((Real.exp 1) ^ ((k : ℝ) / 2)) ^ 2 = (Real.exp 1) ^ k := by
          rw [← Real.rpow_natCast ((Real.exp 1) ^ ((k : ℝ) / 2)) 2, ← Real.rpow_mul (Real.exp_pos 1).le,
            show ((k : ℝ) / 2) * ((2 : ℕ) : ℝ) = (k : ℝ) by push_cast; ring, Real.rpow_natCast]
        rw [hp1, hp2]
        exact hfact_lb
      by_contra! hgt
      have := mul_self_lt_mul_self (by positivity) hgt
      rw [← sq, ← sq] at this
      linarith
    have hsqrt_k_le : Real.sqrt (k : ℝ) ≤ (2 : ℝ) ^ ((k : ℝ) / 2) := by
      have hk_2k : k ≤ 2 ^ k := Nat.lt_pow_self (by decide : 1 < 2) |>.le
      have hk_2k_r : (k : ℝ) ≤ (2 : ℝ) ^ (k : ℝ) := by
        rw [Real.rpow_natCast]
        exact_mod_cast hk_2k
      have h1 : Real.sqrt (k : ℝ) ≤ Real.sqrt ((2 : ℝ) ^ (k : ℝ)) := Real.sqrt_le_sqrt hk_2k_r
      have h2 : Real.sqrt ((2 : ℝ) ^ (k : ℝ)) = (2 : ℝ) ^ ((k : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
        congr 1; ring
      exact h1.trans_eq h2
    have h12_le : (12 : ℝ) ^ (k - 1) ≤ (144 : ℝ) ^ ((k : ℝ) / 2) := by
      have h1 : (12 : ℝ) ^ (k - 1) ≤ (12 : ℝ) ^ k :=
        pow_le_pow_right₀ (by norm_num) (Nat.sub_le k 1)
      have h2 : (12 : ℝ) ^ k = (144 : ℝ) ^ ((k : ℝ) / 2) := by
        rw [← Real.rpow_natCast 12 k]
        have : (12 : ℝ) ^ (k : ℝ) = ((12 : ℝ) ^ (2 : ℝ)) ^ ((k : ℝ) / 2) := by
          rw [← Real.rpow_mul (by norm_num)]; congr 1; ring
        rw [this]; norm_num
      exact h1.trans_eq h2
    have hmain_frac : (12 : ℝ) ^ (k - 1) / Real.sqrt (((k - 1).factorial : ℕ) : ℝ) ≤
        (1000 / (k : ℝ)) ^ ((k : ℝ) / 2) := by
      have hnum : (12 : ℝ) ^ (k - 1) * Real.sqrt (k : ℝ) ≤
          (144 : ℝ) ^ ((k : ℝ) / 2) * (2 : ℝ) ^ ((k : ℝ) / 2) :=
        mul_le_mul h12_le hsqrt_k_le (by positivity) (by positivity)
      have hexp3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
      have h288 : 144 * 2 * Real.exp 1 ≤ 1000 := by linarith
      have hrpow_comb : (144 : ℝ) ^ ((k : ℝ) / 2) * (2 : ℝ) ^ ((k : ℝ) / 2) * (Real.exp 1) ^ ((k : ℝ) / 2) ≤
          (1000 : ℝ) ^ ((k : ℝ) / 2) := by
        rw [← Real.mul_rpow (by positivity) (by positivity), ← Real.mul_rpow (by positivity) (Real.exp_pos 1).le]
        exact Real.rpow_le_rpow (by positivity) h288 (by positivity)
      have hlhs_eq : (12 : ℝ) ^ (k - 1) / Real.sqrt (((k - 1).factorial : ℕ) : ℝ) =
          ((12 : ℝ) ^ (k - 1) * Real.sqrt (k : ℝ)) / Real.sqrt ((k.factorial : ℕ) : ℝ) := by
        rw [← hfact_eq]
        have : Real.sqrt (k : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hk_pos).ne'
        field_simp [this]
      rw [hlhs_eq, Real.div_rpow (by norm_num) (Nat.cast_nonneg k)]
      rw [div_le_div_iff₀ (Real.sqrt_pos.mpr (by positivity)) (Real.rpow_pos_of_pos hk_pos _)]
      calc ((12 : ℝ) ^ (k - 1) * Real.sqrt (k : ℝ)) * (k : ℝ) ^ ((k : ℝ) / 2)
          ≤ ((144 : ℝ) ^ ((k : ℝ) / 2) * (2 : ℝ) ^ ((k : ℝ) / 2)) *
              ((Real.exp 1) ^ ((k : ℝ) / 2) * Real.sqrt ((k.factorial : ℕ) : ℝ)) :=
            mul_le_mul hnum hsqrt_fact (by positivity) (by positivity)
        _ = ((144 : ℝ) ^ ((k : ℝ) / 2) * (2 : ℝ) ^ ((k : ℝ) / 2) * (Real.exp 1) ^ ((k : ℝ) / 2)) *
              Real.sqrt ((k.factorial : ℕ) : ℝ) := by ring
        _ ≤ (1000 : ℝ) ^ ((k : ℝ) / 2) * Real.sqrt ((k.factorial : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right hrpow_comb (Real.sqrt_nonneg _)
    exact mul_le_mul hkn_real hmain_frac (by positivity) (Nat.cast_nonneg n)
  calc (∑ G : SimpleGraph (Fin n),
        (if ∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d then (1 : ℝ) else 0) *
        (∏ e ∈ E_n,
          if G.Adj e.1 e.2
          then (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))
          else 1 - (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))))
      = ∑ H : SimpleGraph (Fin k),
          (if ∃ d ∈ Finset.range k, ∀ i : Fin k, (Finset.univ.filter (fun j : Fin k => H.Adj i j)).card = d
            then (1 : ℝ) else 0) *
          (∏ e ∈ E_k, if H.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2) := hreduce
    _ ≤ ∑ d ∈ Finset.range k, ∑ H : SimpleGraph (Fin k),
          (if ∀ i : Fin k, (Finset.univ.filter (fun j : Fin k => H.Adj i j)).card = d then (1 : ℝ) else 0) *
          (∏ e ∈ E_k, if H.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2) := hsum_d
    _ ≤ ∑ _ ∈ Finset.range k, (12 : ℝ) ^ (k - 1) / Real.sqrt (((k - 1).factorial : ℕ) : ℝ) :=
        Finset.sum_le_sum fun d _ => graph_target_le k hk1 q hq_bound (fun _ => d)
    _ = (k : ℝ) * ((12 : ℝ) ^ (k - 1) / Real.sqrt (((k - 1).factorial : ℕ) : ℝ)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (n : ℝ) * (1000 / (k : ℝ)) ^ ((k : ℝ) / 2) := hbound_k

