import OMAReductions.R_Green43_green_43_variants_range_N051_N052_R1

-- Step Green43.green_43.variants.range_N051_N052.R1.H1: the second moment bound
-- Credit: @LordMike

open Filter Finset

open scoped Classical in
/-- Cauchy–Schwarz for a family of sets `{n ∈ I | D p n}`, `p ∈ P`, any two of which share at
most one point. -/
lemma g43r_core (P : Finset ℕ) (I : Finset ℤ) (D : ℕ → ℤ → Prop)
    (huniq : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → ∀ n ∈ I, ∀ n' ∈ I,
      D p n → D q n → D p n' → D q n' → n = n') :
    (∑ p ∈ P, (I.filter (D p)).card) ^ 2 ≤
      (I.filter (fun n => ∃ p ∈ P, D p n)).card *
        (∑ p ∈ P, (I.filter (D p)).card +
          ((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2 ∧ ∃ n ∈ I, D pq.1 n ∧ D pq.2 n)).card) := by
  have hT : ∑ n ∈ I, (P.filter (fun p => D p n)).card = ∑ p ∈ P, (I.filter (D p)).card :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun n p => D p n)
  have hsq : ∀ n, (P.filter (fun p => D p n)).card ^ 2 =
      ((P ×ˢ P).filter (fun pq => D pq.1 n ∧ D pq.2 n)).card := by
    intro n
    rw [sq, ← Finset.card_product]
    congr 1
    ext ⟨p, q⟩
    simp only [mem_product, mem_filter]
    tauto
  have hT2 : ∑ n ∈ I, (P.filter (fun p => D p n)).card ^ 2 =
      ∑ pq ∈ P ×ˢ P, (I.filter (fun n => D pq.1 n ∧ D pq.2 n)).card := by
    simp_rw [hsq]
    exact Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (fun (n : ℤ) (pq : ℕ × ℕ) => D pq.1 n ∧ D pq.2 n)
  have hbound : ∑ pq ∈ P ×ˢ P, (I.filter (fun n => D pq.1 n ∧ D pq.2 n)).card ≤
      ∑ p ∈ P, (I.filter (D p)).card +
        ((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2 ∧ ∃ n ∈ I, D pq.1 n ∧ D pq.2 n)).card := by
    rw [← Finset.sum_filter_add_sum_filter_not (P ×ˢ P) (fun pq => pq.1 = pq.2)]
    apply add_le_add
    · have hdiag : (P ×ˢ P).filter (fun pq => pq.1 = pq.2) = P.image (fun p => (p, p)) := by
        ext ⟨p, q⟩
        simp only [mem_filter, mem_product, mem_image, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨hp, _⟩, rfl⟩
          exact ⟨p, hp, rfl, rfl⟩
        · rintro ⟨x, hx, rfl, rfl⟩
          exact ⟨⟨hx, hx⟩, rfl⟩
      rw [hdiag, Finset.sum_image (by intro x _ y _ h; exact (Prod.mk.inj h).1)]
      apply Finset.sum_le_sum
      intro p _
      apply Finset.card_le_card
      intro n hn
      rw [mem_filter] at hn ⊢
      exact ⟨hn.1, hn.2.1⟩
    · rw [← Finset.filter_filter, Finset.card_filter]
      apply Finset.sum_le_sum
      intro pq hpq
      rw [mem_filter, mem_product] at hpq
      split_ifs with hex
      · apply Finset.card_le_one.2
        intro n hn n' hn'
        rw [mem_filter] at hn hn'
        exact huniq pq.1 hpq.1.1 pq.2 hpq.1.2 hpq.2 n hn.1 n' hn'.1 hn.2.1 hn.2.2 hn'.2.1 hn'.2.2
      · apply le_of_eq
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro n hn hD
        exact hex ⟨n, hn, hD⟩
  have hS : ∑ n ∈ I.filter (fun n => ∃ p ∈ P, D p n), (P.filter (fun p => D p n)).card =
      ∑ n ∈ I, (P.filter (fun p => D p n)).card := by
    apply Finset.sum_filter_of_ne
    intro n _ h
    obtain ⟨p, hp⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero h)
    rw [mem_filter] at hp
    exact ⟨p, hp.1, hp.2⟩
  calc (∑ p ∈ P, (I.filter (D p)).card) ^ 2
      = (∑ n ∈ I.filter (fun n => ∃ p ∈ P, D p n), (P.filter (fun p => D p n)).card) ^ 2 := by
        rw [hS, hT]
    _ ≤ (I.filter (fun n => ∃ p ∈ P, D p n)).card *
          ∑ n ∈ I.filter (fun n => ∃ p ∈ P, D p n), (P.filter (fun p => D p n)).card ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ (I.filter (fun n => ∃ p ∈ P, D p n)).card *
          ∑ n ∈ I, (P.filter (fun p => D p n)).card ^ 2 :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
    _ ≤ _ := Nat.mul_le_mul_left _ (hT2 ▸ hbound)

open scoped Classical in
/-- A residue class modulo `p` has at least `N / p - 1` points in `[1, N]`. -/
lemma g43r_class (N p : ℕ) (hp : 0 < p) (v : ℤ) :
    (N : ℝ) / p - 1 ≤ (((Icc (1 : ℤ) N).filter (fun n => (p : ℤ) ∣ n - v)).card : ℝ) := by
  have hp' : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
  have h := Int.Ioc_filter_modEq_card 0 (N : ℤ) hp' v
  have hc : ((Icc (1 : ℤ) N).filter (fun n => (p : ℤ) ∣ n - v)).card =
      ((Ioc (0 : ℤ) N).filter (fun x => x ≡ v [ZMOD (p : ℤ)])).card := by
    congr 1
    ext n
    simp only [mem_filter, mem_Icc, mem_Ioc, Int.modEq_iff_dvd]
    rw [dvd_sub_comm]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by omega, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by omega, h2⟩, h3⟩
  rw [hc]
  set c := ((Ioc (0 : ℤ) N).filter (fun x => x ≡ v [ZMOD (p : ℤ)])).card with hcdef
  have h3 : ⌊(((N : ℤ) : ℚ) - v) / ((p : ℤ) : ℚ)⌋ - ⌊(((0 : ℤ) : ℚ) - v) / ((p : ℤ) : ℚ)⌋ ≤ (c : ℤ) := by
    rw [h]
    exact le_max_left _ _
  have h1 := Int.sub_one_lt_floor ((((N : ℤ) : ℚ) - v) / ((p : ℤ) : ℚ))
  have h2 := Int.floor_le ((((0 : ℤ) : ℚ) - v) / ((p : ℤ) : ℚ))
  have h3' : ((⌊(((N : ℤ) : ℚ) - v) / ((p : ℤ) : ℚ)⌋ : ℤ) : ℚ) -
      ((⌊(((0 : ℤ) : ℚ) - v) / ((p : ℤ) : ℚ)⌋ : ℤ) : ℚ) ≤ (c : ℚ) := by
    exact_mod_cast h3
  have h4 : (((N : ℤ) : ℚ) - v) / ((p : ℤ) : ℚ) - (((0 : ℤ) : ℚ) - v) / ((p : ℤ) : ℚ) =
      (N : ℚ) / (p : ℚ) := by
    push_cast
    ring
  have h5 : (N : ℚ) / (p : ℚ) - 1 ≤ (c : ℚ) := by linarith
  have h6 := (Rat.cast_le (K := ℝ)).2 h5
  push_cast at h6
  exact h6

/-- `C * log N * N ^ α ≤ N ^ β` for large `N`, if `α < β`. -/
lemma g43r_ev (C α β : ℝ) (hC : 0 ≤ C) (h : α < β) :
    ∀ᶠ N : ℕ in atTop, C * Real.log N * (N : ℝ) ^ α ≤ (N : ℝ) ^ β := by
  have hγ : 0 < (β - α) / 2 := by linarith
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ ((β - α) / 2)) atTop atTop :=
    (tendsto_rpow_atTop hγ).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop (C / ((β - α) / 2)), eventually_ge_atTop 1] with N hN h1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast h1
  have hlog : Real.log N ≤ (N : ℝ) ^ ((β - α) / 2) / ((β - α) / 2) :=
    Real.log_le_rpow_div hN0.le hγ
  have hNa : 0 < (N : ℝ) ^ α := Real.rpow_pos_of_pos hN0 _
  have hNg : 0 < (N : ℝ) ^ ((β - α) / 2) := Real.rpow_pos_of_pos hN0 _
  have e : (N : ℝ) ^ β = (N : ℝ) ^ ((β - α) / 2) * (N : ℝ) ^ ((β - α) / 2) * (N : ℝ) ^ α := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
    congr 1
    ring
  rw [e]
  have hmain : C * Real.log N ≤ (N : ℝ) ^ ((β - α) / 2) * (N : ℝ) ^ ((β - α) / 2) := by
    calc C * Real.log N ≤ C * ((N : ℝ) ^ ((β - α) / 2) / ((β - α) / 2)) :=
          mul_le_mul_of_nonneg_left hlog hC
      _ = C / ((β - α) / 2) * (N : ℝ) ^ ((β - α) / 2) := by ring
      _ ≤ (N : ℝ) ^ ((β - α) / 2) * (N : ℝ) ^ ((β - α) / 2) :=
          mul_le_mul_of_nonneg_right hN hNg.le
  exact mul_le_mul_of_nonneg_right hmain hNa.le

open scoped Classical in
/-- Chebyshev: there are at least `N ^ (0.52 - δ)` primes in `[N ^ 0.51, N ^ 0.52)`. -/
lemma g43r_primes (δ : ℝ) (hδ : 0 < δ) : ∀ᶠ N : ℕ in atTop,
    (N : ℝ) ^ (0.52 - δ) ≤ (((range (N + 1)).filter (fun p : ℕ => p.Prime ∧
      (N : ℝ) ^ (0.51 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ (0.52 : ℝ))).card : ℝ) := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (0.52 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [g43r_ev 8 (0.52 - δ) 0.52 (by norm_num) (by linarith),
    g43r_ev 8 0.51 0.52 (by norm_num) (by norm_num),
    g43r_ev 16 0 0.52 (by norm_num) (by norm_num),
    ht.eventually_ge_atTop 12, eventually_ge_atTop 1] with N e1 e2 e3 e4 hN1
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  rw [Real.rpow_zero, mul_one] at e3
  set hi : ℝ := (N : ℝ) ^ (0.52 : ℝ) with hhi
  set lo : ℝ := (N : ℝ) ^ (0.51 : ℝ) with hlo
  set L : ℝ := Real.log N with hL
  have hlo0 : 0 < lo := Real.rpow_pos_of_pos hN0 _
  have hhiN : hi ≤ N := by
    calc hi ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1' (by norm_num)
      _ = N := Real.rpow_one _
  have hN12 : (12 : ℝ) ≤ N := le_trans e4 hhiN
  have hLpos : 0 < L := Real.log_pos (by linarith)
  have hceil : 0 < ⌈hi⌉₊ := Nat.ceil_pos.2 (by linarith)
  obtain ⟨m, hm1⟩ : ∃ m, m + 1 = ⌈hi⌉₊ := ⟨⌈hi⌉₊ - 1, by omega⟩
  have hm_lt : (m : ℝ) < hi := Nat.lt_ceil.1 (by omega)
  have hm_ge : hi - 1 ≤ m := by
    have h1 := Nat.le_ceil hi
    have h2 : ((m + 1 : ℕ) : ℝ) = (⌈hi⌉₊ : ℝ) := by rw [hm1]
    push_cast at h2
    linarith
  have hmN : (m : ℝ) ≤ N := hm_lt.le.trans hhiN
  have hm11 : (11 : ℝ) ≤ m := by linarith
  have hlogm : 0 < Real.log m := Real.log_pos (by linarith)
  have hlogm_le : Real.log m ≤ L := Real.log_le_log (by linarith) hmN
  have hlogm1 : Real.log ((m : ℝ) + 1) ≤ Real.log 2 + L := by
    rw [hL, ← Real.log_mul (by norm_num) hN0.ne']
    exact Real.log_le_log (by linarith) (by linarith)
  have hlog2a : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hlog2b : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hpi := Chebyshev.pi_ge m
  rw [div_le_iff₀ hlogm] at hpi
  have hpi0 : (0 : ℝ) ≤ (Nat.primeCounting m : ℝ) := Nat.cast_nonneg _
  have hpiL : (hi - 1) / 2 - 1 - L ≤ (Nat.primeCounting m : ℝ) * L := by
    have h1 : (Nat.primeCounting m : ℝ) * Real.log m ≤ (Nat.primeCounting m : ℝ) * L :=
      mul_le_mul_of_nonneg_left hlogm_le hpi0
    have h2 : (hi - 1) * (1 / 2) ≤ (m : ℝ) * Real.log 2 :=
      mul_le_mul hm_ge hlog2b (by norm_num) (by linarith)
    linarith
  have hX : (N : ℝ) ^ (0.52 - δ) + lo + 1 ≤ (Nat.primeCounting m : ℝ) := by
    have h1 : ((N : ℝ) ^ (0.52 - δ) + lo + 1) * L ≤ (Nat.primeCounting m : ℝ) * L := by
      have : ((N : ℝ) ^ (0.52 - δ) + lo + 1) * L =
          (8 * L * (N : ℝ) ^ (0.52 - δ)) / 8 + (8 * L * lo) / 8 + L := by ring
      linarith
    exact le_of_mul_le_mul_right h1 hLpos
  have hπ : Nat.primeCounting m = ((range (m + 1)).filter Nat.Prime).card := by
    simp [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hmN' : m ≤ N := by exact_mod_cast hmN
  have hsub : (range (m + 1)).filter Nat.Prime \ range ⌈lo⌉₊ ⊆
      (range (N + 1)).filter (fun p : ℕ => p.Prime ∧ lo ≤ (p : ℝ) ∧ (p : ℝ) < hi) := by
    intro p hp
    rw [Finset.mem_sdiff, mem_filter, mem_range, mem_range] at hp
    obtain ⟨⟨hpm, hpp⟩, hplo⟩ := hp
    rw [mem_filter, mem_range]
    refine ⟨by omega, hpp, Nat.ceil_le.1 (by omega), lt_of_le_of_lt ?_ hm_lt⟩
    exact_mod_cast Nat.lt_succ_iff.1 hpm
  have hcard : Nat.primeCounting m ≤
      ((range (N + 1)).filter (fun p : ℕ => p.Prime ∧ lo ≤ (p : ℝ) ∧ (p : ℝ) < hi)).card + ⌈lo⌉₊ := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.le_card_sdiff (range ⌈lo⌉₊) ((range (m + 1)).filter Nat.Prime)
    rw [card_range] at h2
    omega
  have hcard' : (Nat.primeCounting m : ℝ) ≤
      (((range (N + 1)).filter (fun p : ℕ => p.Prime ∧ lo ≤ (p : ℝ) ∧ (p : ℝ) < hi)).card : ℝ) +
        (⌈lo⌉₊ : ℝ) := by
    exact_mod_cast hcard
  have hceil_lo : (⌈lo⌉₊ : ℝ) < lo + 1 := Nat.ceil_lt_add_one hlo0.le
  linarith

set_option maxHeartbeats 1000000 in
theorem OMA.solution : OMA.R_Green43_green_43_variants_range_N051_N052_R1.H1 := by
  intro ε hε
  have t1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (0.48 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have t2 : Tendsto (fun N : ℕ => (N : ℝ) ^ (ε / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  filter_upwards [g43r_primes (ε / 2) (by positivity), t1.eventually_ge_atTop 2,
    t2.eventually_ge_atTop 4, eventually_ge_atTop 1] with N hP h48 hε4 hN1 a hE
  classical
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  set hi : ℝ := (N : ℝ) ^ (0.52 : ℝ) with hhi
  set lo : ℝ := (N : ℝ) ^ (0.51 : ℝ) with hlo
  have hlo0 : 0 < lo := Real.rpow_pos_of_pos hN0 _
  have hhi0 : 0 < hi := Real.rpow_pos_of_pos hN0 _
  have hhiN : hi ≤ N := by
    calc hi ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1' (by norm_num)
      _ = N := Real.rpow_one _
  have hlolo : (N : ℝ) ≤ lo * lo := by
    rw [hlo, ← Real.rpow_add hN0]
    calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1' (by norm_num)
  have h48hi : (N : ℝ) ^ (0.48 : ℝ) * hi = N := by
    rw [hhi, ← Real.rpow_add hN0]
    norm_num
  set P : Finset ℕ := (range (N + 1)).filter (fun p : ℕ => p.Prime ∧ lo ≤ (p : ℝ) ∧ (p : ℝ) < hi)
    with hPdef
  set I : Finset ℤ := Icc (1 : ℤ) (N : ℤ) with hI
  have hPmem : ∀ p ∈ P, p.Prime ∧ lo ≤ (p : ℝ) ∧ (p : ℝ) < hi := by
    intro p hp
    rw [hPdef, mem_filter] at hp
    exact hp.2
  have huniq : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → ∀ n ∈ I, ∀ n' ∈ I,
      (p : ℤ) ∣ n - a p → (q : ℤ) ∣ n - a q → (p : ℤ) ∣ n' - a p → (q : ℤ) ∣ n' - a q →
        n = n' := by
    intro p hp q hq hpq n hn n' hn' h1 h2 h3 h4
    obtain ⟨hpp, hplo, -⟩ := hPmem p hp
    obtain ⟨hqp, hqlo, -⟩ := hPmem q hq
    rw [hI, mem_Icc] at hn hn'
    have hd1 : (p : ℤ) ∣ n - n' := by
      have := dvd_sub h1 h3
      rwa [sub_sub_sub_cancel_right] at this
    have hd2 : (q : ℤ) ∣ n - n' := by
      have := dvd_sub h2 h4
      rwa [sub_sub_sub_cancel_right] at this
    have hcop : IsCoprime (p : ℤ) (q : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hpp hqp).2 hpq)
    have hd : (p : ℤ) * (q : ℤ) ∣ n - n' := hcop.mul_dvd hd1 hd2
    have hNpq : (N : ℝ) ≤ (p : ℝ) * (q : ℝ) :=
      hlolo.trans (mul_le_mul hplo hqlo hlo0.le (hlo0.le.trans hplo))
    have hNpq' : (N : ℤ) ≤ (p : ℤ) * (q : ℤ) := by exact_mod_cast hNpq
    have habs : |n - n'| < (p : ℤ) * (q : ℤ) := by
      rw [abs_lt]
      constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd hd habs
    omega
  set T : ℕ := ∑ p ∈ P, (I.filter (fun n => (p : ℤ) ∣ n - a p)).card with hT
  set S : Finset ℤ := I.filter (fun n => ∃ p ∈ P, (p : ℤ) ∣ n - a p) with hS
  set F : Finset (ℕ × ℕ) := (P ×ˢ P).filter
    (fun pq => pq.1 ≠ pq.2 ∧ ∃ n ∈ I, (pq.1 : ℤ) ∣ n - a pq.1 ∧ (pq.2 : ℤ) ∣ n - a pq.2) with hF
  have hcore : T ^ 2 ≤ S.card * (T + F.card) := by
    have h := g43r_core P I (fun p n => (p : ℤ) ∣ n - a p) huniq
    convert h
  -- the sieved set contains `S`
  have hSle : S.card ≤ Green43.sievedCard N a lo hi := by
    unfold Green43.sievedCard Green43.sievedSet
    apply Finset.card_le_card
    intro n hn
    rw [hS, mem_filter] at hn
    obtain ⟨hnI, p, hp, hd⟩ := hn
    obtain ⟨h1, h2, h3⟩ := hPmem p hp
    rw [mem_filter]
    exact ⟨hnI, p, h1, h2, h3, hd⟩
  -- the colliding pairs
  set A : Set (ℕ × ℕ) := {pq : ℕ × ℕ | pq.1.Prime ∧ pq.2.Prime ∧ pq.1 < pq.2 ∧
        lo ≤ (pq.1 : ℝ) ∧ (pq.2 : ℝ) < hi ∧
        ∃ n : ℤ, 1 ≤ n ∧ n ≤ (N : ℤ) ∧ (pq.1 : ℤ) ∣ n - a pq.1 ∧
          (pq.2 : ℤ) ∣ n - a pq.2} with hA
  have hAfin : A.Finite := by
    apply Set.Finite.subset (Finset.finite_toSet (range (N + 1) ×ˢ range (N + 1)))
    rintro ⟨p, q⟩ ⟨-, -, hpq, -, hq, -⟩
    have hqN : (q : ℝ) ≤ N := hq.le.trans hhiN
    have hqN' : q ≤ N := by exact_mod_cast hqN
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_range]
    constructor <;> omega
  have hFA : F.card ≤ 2 * A.ncard := by
    have hsplit : F = F.filter (fun pq => pq.1 < pq.2) ∪ F.filter (fun pq => pq.2 < pq.1) := by
      rw [← Finset.filter_or]
      symm
      apply Finset.filter_true_of_mem
      intro pq hpq
      rw [hF, mem_filter] at hpq
      exact lt_or_gt_of_ne hpq.2.1
    have h1 : (F.filter (fun pq => pq.1 < pq.2)).card ≤ A.ncard := by
      rw [← Set.ncard_coe_finset]
      apply Set.ncard_le_ncard _ hAfin
      intro pq hpq
      rw [Finset.mem_coe, mem_filter, hF, mem_filter, mem_product] at hpq
      obtain ⟨⟨⟨hp, hq⟩, -, n, hn, hd1, hd2⟩, hlt⟩ := hpq
      rw [hI, mem_Icc] at hn
      exact ⟨(hPmem _ hp).1, (hPmem _ hq).1, hlt, (hPmem _ hp).2.1, (hPmem _ hq).2.2,
        n, hn.1, hn.2, hd1, hd2⟩
    have h2 : (F.filter (fun pq => pq.2 < pq.1)).card ≤ A.ncard := by
      rw [← Finset.card_image_of_injective _ Prod.swap_injective, ← Set.ncard_coe_finset]
      apply Set.ncard_le_ncard _ hAfin
      intro pq hpq
      rw [Finset.mem_coe, mem_image] at hpq
      obtain ⟨pq', hpq', rfl⟩ := hpq
      rw [mem_filter, hF, mem_filter, mem_product] at hpq'
      obtain ⟨⟨⟨hp, hq⟩, -, n, hn, hd1, hd2⟩, hlt⟩ := hpq'
      rw [hI, mem_Icc] at hn
      exact ⟨(hPmem _ hq).1, (hPmem _ hp).1, hlt, (hPmem _ hq).2.1, (hPmem _ hp).2.2,
        n, hn.1, hn.2, hd2, hd1⟩
    have hle : F.card ≤ (F.filter (fun pq => pq.1 < pq.2)).card +
        (F.filter (fun pq => pq.2 < pq.1)).card := by
      conv_lhs => rw [hsplit]
      exact Finset.card_union_le _ _
    omega
  -- lower bound for `T`
  have hTge : (P.card : ℝ) * ((N : ℝ) ^ (0.48 : ℝ) / 2) ≤ (T : ℝ) := by
    rw [hT, Nat.cast_sum, ← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hpp, -, hphi⟩ := hPmem p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hcl := g43r_class N p hpp.pos (a p)
    have h1 : (N : ℝ) ^ (0.48 : ℝ) ≤ (N : ℝ) / p := by
      rw [le_div_iff₀ hp0]
      calc (N : ℝ) ^ (0.48 : ℝ) * (p : ℝ) ≤ (N : ℝ) ^ (0.48 : ℝ) * hi :=
            mul_le_mul_of_nonneg_left hphi.le (Real.rpow_nonneg hN0.le _)
        _ = N := h48hi
    rw [hI]
    linarith
  set X : ℝ := (N : ℝ) ^ (1 - ε) with hXdef
  have hX0 : 0 < X := Real.rpow_pos_of_pos hN0 _
  have hT2X : 2 * X ≤ (T : ℝ) := by
    have e1 : (N : ℝ) ^ (0.52 - ε / 2) * (N : ℝ) ^ (0.48 : ℝ) = X * (N : ℝ) ^ (ε / 2) := by
      rw [hXdef, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 1
      ring
    have h1 : (N : ℝ) ^ (0.52 - ε / 2) * ((N : ℝ) ^ (0.48 : ℝ) / 2) ≤ (T : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_right hP (by positivity)) hTge
    have h2 : X * 4 ≤ X * (N : ℝ) ^ (ε / 2) := mul_le_mul_of_nonneg_left hε4 hX0.le
    have h3 : (N : ℝ) ^ (0.52 - ε / 2) * ((N : ℝ) ^ (0.48 : ℝ) / 2) =
        X * (N : ℝ) ^ (ε / 2) / 2 := by
      rw [← e1]
      ring
    linarith
  -- conclusion
  by_contra hcon
  rw [not_le] at hcon
  set s : ℝ := (N : ℝ) ^ (1 - 3 * ε) with hsdef
  set Y : ℝ := (N : ℝ) ^ (1 + ε) with hYdef
  have hs0 : 0 < s := Real.rpow_pos_of_pos hN0 _
  have hsX : s ≤ X := Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  have hsY : s * Y = X * X := by
    rw [hsdef, hYdef, hXdef, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
    congr 1
    ring
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hN0 _
  have hScard : (S.card : ℝ) < s :=
    lt_of_le_of_lt (by exact_mod_cast hSle) hcon
  have hFY : (F.card : ℝ) ≤ 2 * Y := by
    have : (F.card : ℝ) ≤ 2 * (A.ncard : ℝ) := by exact_mod_cast hFA
    linarith
  have hcoreR : (T : ℝ) ^ 2 ≤ (S.card : ℝ) * ((T : ℝ) + (F.card : ℝ)) := by
    exact_mod_cast hcore
  have hT0 : (0 : ℝ) < T := by linarith
  have h1 : (S.card : ℝ) * ((T : ℝ) + (F.card : ℝ)) ≤ (S.card : ℝ) * ((T : ℝ) + 2 * Y) :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  have h2 : (S.card : ℝ) * ((T : ℝ) + 2 * Y) < s * ((T : ℝ) + 2 * Y) :=
    mul_lt_mul_of_pos_right hScard (by linarith)
  have h3 : s * (T : ℝ) ≤ X * (T : ℝ) := mul_le_mul_of_nonneg_right hsX hT0.le
  have h4 : X * (T : ℝ) ≤ (T : ℝ) / 2 * (T : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hT0.le
  have h5 : (2 * X) * (2 * X) ≤ (T : ℝ) * (T : ℝ) :=
    mul_le_mul hT2X hT2X (by linarith) hT0.le
  nlinarith
