import FormalConjectures.ErdosProblems.«436»

-- Problem: Erdős Problem 436 — even three
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/436.lean:127 (declaration Erdos436.erdos_436.variants.even_three)
-- Credit: @michielkosters (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter

private lemma exists_nonsquare_nat {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    ∃ a : ℕ, 0 < a ∧ a < q ∧ ¬ IsSquare (a : ZMod q) := by
  have : NeZero q := ⟨hq.ne_zero⟩
  have hnot_surj : ¬ Function.Surjective (fun x : ZMod q => x ^ 2) := by
    intro hsurj
    have hinj := Finite.injective_iff_surjective.mpr hsurj
    have h1 : (1 : ZMod q) ^ 2 = (-1 : ZMod q) ^ 2 := by ring
    have h2 : (1 : ZMod q) = -1 := hinj h1
    have h20 : ((2 : ℕ) : ZMod q) = ((0 : ℕ) : ZMod q) := by
      calc ((2 : ℕ) : ZMod q) = 1 - (-1) := by norm_num
        _ = 1 - 1 := by rw [← h2]
        _ = ((0 : ℕ) : ZMod q) := by norm_num
    have hmod : 2 ≡ 0 [MOD q] := (ZMod.natCast_eq_natCast_iff 2 0 q).mp h20
    have hdvd : q ∣ 2 := Nat.dvd_of_mod_eq_zero (by simpa [Nat.ModEq] using hmod)
    exact hq2 ((Nat.dvd_prime Nat.prime_two).mp hdvd |>.resolve_left hq.ne_one)
  simp only [Function.Surjective, not_forall] at hnot_surj
  obtain ⟨y, hy⟩ := hnot_surj
  have hnsq : ¬ IsSquare y := fun ⟨x, hx⟩ => hy ⟨x, by rw [hx, sq]⟩
  have hy0 : y ≠ 0 := fun h => hnsq (h ▸ IsSquare.zero)
  refine ⟨y.val, ?_, ZMod.val_lt y, ?_⟩
  · by_contra h0
    have hval : y.val = 0 := by omega
    apply hy0
    rw [← ZMod.natCast_zmod_val y, hval, Nat.cast_zero]
  · rw [ZMod.natCast_zmod_val]
    exact hnsq

private lemma exists_prime_avoiding_three_consec (M N : ℕ) :
    ∃ p ≥ N, p.Prime ∧ ∀ n, 1 ≤ n → n ≤ M →
      ¬ ∀ i < 3, Erdos436.IsPowerResidue 2 p (n + i) := by
  classical
  let P : Finset ℕ := (Finset.Icc 5 (M + 2)).filter Nat.Prime
  let t : Finset ℕ := insert 8 P
  let a : ℕ → ℕ := fun q =>
    if q = 8 then 5
    else if q % 3 = 1 then 1
    else if h : q.Prime ∧ q ≠ 2 then Classical.choose (exists_nonsquare_nat h.1 h.2)
    else 1
  have hs : ∀ q ∈ t, (id q) ≠ 0 := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hqP
    · decide
    · exact ((Finset.mem_filter.mp hqP).2.ne_zero)
  have pp : Set.Pairwise (t : Set ℕ) (Function.onFun Nat.Coprime id) := by
    intro q₁ hq₁ q₂ hq₂ hne
    change Nat.Coprime q₁ q₂
    rcases Finset.mem_insert.mp hq₁ with rfl | hq₁P <;>
      rcases Finset.mem_insert.mp hq₂ with rfl | hq₂P
    · exact absurd rfl hne
    · have hp₂ : q₂.Prime := (Finset.mem_filter.mp hq₂P).2
      have hge5 : 5 ≤ q₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq₂P).1).1
      rw [Nat.coprime_comm]
      refine hp₂.coprime_iff_not_dvd.mpr fun hdvd => ?_
      have h2 : q₂ ∣ 2 ^ 3 := by simpa using hdvd
      have h2' : q₂ ∣ 2 := hp₂.dvd_of_dvd_pow h2
      have hle2 : q₂ ≤ 2 := Nat.le_of_dvd (by decide) h2'
      omega
    · have hp₁ : q₁.Prime := (Finset.mem_filter.mp hq₁P).2
      have hge5 : 5 ≤ q₁ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq₁P).1).1
      refine hp₁.coprime_iff_not_dvd.mpr fun hdvd => ?_
      have h2 : q₁ ∣ 2 ^ 3 := by simpa using hdvd
      have h2' : q₁ ∣ 2 := hp₁.dvd_of_dvd_pow h2
      have hle2 : q₁ ≤ 2 := Nat.le_of_dvd (by decide) h2'
      omega
    · exact (Nat.coprime_primes (Finset.mem_filter.mp hq₁P).2
        (Finset.mem_filter.mp hq₂P).2).mpr hne
  obtain ⟨r, hr⟩ := Nat.chineseRemainderOfFinset a id t hs pp
  let B : ℕ := ∏ q ∈ t, q
  have hB : B ≠ 0 := Finset.prod_ne_zero_iff.mpr hs
  have ha_bounds : ∀ q ∈ P, 0 < a q ∧ a q < q := by
    intro q hqP
    have hq_mem := Finset.mem_filter.mp hqP
    have hq_ge5 : 5 ≤ q := (Finset.mem_Icc.mp hq_mem.1).1
    have hq_prime : q.Prime := hq_mem.2
    have hq8 : q ≠ 8 := by
      intro h
      subst h
      norm_num at hq_prime
    have hq2 : q ≠ 2 := by omega
    simp only [a, hq8, ↓reduceIte]
    by_cases hmod : q % 3 = 1
    · simp only [hmod, ↓reduceIte]
      omega
    · have hq_cond : q.Prime ∧ q ≠ 2 := ⟨hq_prime, hq2⟩
      simp only [hmod, ↓reduceIte, dif_pos hq_cond]
      have hspec := Classical.choose_spec (exists_nonsquare_nat hq_prime hq2)
      exact ⟨hspec.1, hspec.2.1⟩
  have hcop : r.Coprime B := by
    refine Nat.coprime_prod_right_iff.mpr fun q hq => ?_
    have hrq : r ≡ a q [MOD q] := hr q hq
    rcases Finset.mem_insert.mp hq with rfl | hqP
    · have ha8 : a 8 = 5 := by simp [a]
      rw [ha8] at hrq
      have hmod : r % 8 = 5 := by simpa [Nat.ModEq] using hrq
      rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec, hmod]
      decide
    · have hq_prime : q.Prime := (Finset.mem_filter.mp hqP).2
      obtain ⟨hpos, hlt⟩ := ha_bounds q hqP
      have hmod : r % q = a q := by
        have : r % q = a q % q := hrq
        rw [this, Nat.mod_eq_of_lt hlt]
      rw [Nat.coprime_comm]
      refine hq_prime.coprime_iff_not_dvd.mpr fun hdvd => ?_
      have h0 : r % q = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
      omega
  obtain ⟨p, hp_gt, hp_prime, hp_mod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max N (M + 2)) hB hcop
  refine ⟨p, le_trans (le_max_left _ _) hp_gt.le, hp_prime, ?_⟩
  have hp_gtM : M + 2 < p := lt_of_le_of_lt (le_max_right _ _) hp_gt
  have hp_mod_t : ∀ q ∈ t, p ≡ a q [MOD q] := fun q hq =>
    (hp_mod.of_dvd (Finset.dvd_prod_of_mem _ hq)).trans (hr q hq)
  have hp8 : p % 8 = 5 := by
    have h8 := hp_mod_t 8 (Finset.mem_insert_self _ _)
    have ha8 : a 8 = 5 := by simp [a]
    rw [ha8] at h8
    simpa [Nat.ModEq] using h8
  have hp4 : p % 4 = 1 := by omega
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp_prime⟩
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have h_not_sq_two_three : ¬ IsSquare (2 : ZMod 3) := by
    rw [ZMod.exists_sq_eq_two_iff (by decide : 3 ≠ 2)]
    decide
  have h_prime_leg : ∀ q, q.Prime → q ≤ M + 2 → q ≠ 3 →
      legendreSym p q = legendreSym 3 q := by
    intro q hq hq_le hq3
    have : Fact q.Prime := ⟨hq⟩
    rcases eq_or_ne q 2 with rfl | hq2
    · have h2p : ¬ IsSquare (2 : ZMod p) := by
        rw [ZMod.exists_sq_eq_two_iff hp2]
        omega
      rw [(legendreSym.eq_neg_one_iff' p).mpr h2p,
        (legendreSym.eq_neg_one_iff' 3).mpr h_not_sq_two_three]
    · have hq5 : 5 ≤ q := by
        have h2le := hq.two_le
        by_contra hlt
        interval_cases q <;> first | exact absurd rfl hq2 | exact absurd rfl hq3 | norm_num at hq
      have hqP : q ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq5, hq_le⟩, hq⟩
      have hqp_mod : p ≡ a q [MOD q] := hp_mod_t q (Finset.mem_insert_of_mem hqP)
      have hqp_zmod : (p : ZMod q) = (a q : ZMod q) :=
        (ZMod.natCast_eq_natCast_iff p (a q) q).mpr hqp_mod
      have hqr : legendreSym p q = legendreSym q p :=
        (legendreSym.quadratic_reciprocity_one_mod_four hp4 hq2).symm
      rw [hqr]
      have hq8 : q ≠ 8 := by
        intro h
        subst h
        norm_num at hq
      by_cases hmod3 : q % 3 = 1
      · have haq : a q = 1 := by simp [a, hq8, hmod3]
        rw [haq] at hqp_zmod
        have hsq_qp : IsSquare (p : ZMod q) := ⟨1, by rw [hqp_zmod]; norm_num⟩
        have hnz_qp : (p : ZMod q) ≠ 0 := by rw [hqp_zmod]; norm_num
        have hq3_mod : (q : ZMod 3) = (1 : ZMod 3) :=
          (ZMod.natCast_eq_natCast_iff q 1 3).mpr (by simpa [Nat.ModEq] using hmod3)
        have hsq_3q : IsSquare (q : ZMod 3) := ⟨1, by rw [hq3_mod]; norm_num⟩
        have hnz_3q : (q : ZMod 3) ≠ 0 := by rw [hq3_mod]; norm_num
        rw [(legendreSym.eq_one_iff' q hnz_qp).mpr hsq_qp,
          (legendreSym.eq_one_iff' 3 hnz_3q).mpr hsq_3q]
      · have hq_cond : q.Prime ∧ q ≠ 2 := ⟨hq, hq2⟩
        have haq_eq : a q = Classical.choose (exists_nonsquare_nat hq hq2) := by
          simp only [a, hq8, ↓reduceIte, hmod3, dif_pos hq_cond]
        have hspec := Classical.choose_spec (exists_nonsquare_nat hq hq2)
        have hnsq_aq : ¬ IsSquare (a q : ZMod q) := by
          rw [haq_eq]
          exact hspec.2.2
        have hnsq_qp : ¬ IsSquare (p : ZMod q) := by rwa [hqp_zmod]
        have hmod3_2 : q % 3 = 2 := by
          have hdvd3 : ¬ 3 ∣ q := fun h => hq3 (((Nat.dvd_prime hq).mp h |>.resolve_left (by decide)).symm)
          have h0 : q % 3 ≠ 0 := fun h => hdvd3 (Nat.dvd_of_mod_eq_zero h)
          omega
        have hq3_mod : (q : ZMod 3) = (2 : ZMod 3) :=
          (ZMod.natCast_eq_natCast_iff q 2 3).mpr (by simpa [Nat.ModEq] using hmod3_2)
        have hnsq_3q : ¬ IsSquare (q : ZMod 3) := by rwa [hq3_mod]
        rw [(legendreSym.eq_neg_one_iff' q).mpr hnsq_qp,
          (legendreSym.eq_neg_one_iff' 3).mpr hnsq_3q]
  have h_leg_m : ∀ m, 1 ≤ m → m ≤ M + 2 → ¬ 3 ∣ m →
      legendreSym p m = legendreSym 3 m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm1 hm_le hm3
      rcases eq_or_lt_of_le hm1 with rfl | hm_gt1
      · simp
      · let q := m.minFac
        have hq : q.Prime := Nat.minFac_prime (by omega)
        have hqm : q ∣ m := Nat.minFac_dvd m
        have hq_le : q ≤ M + 2 := (Nat.le_of_dvd (by omega) hqm).trans hm_le
        have hq3 : q ≠ 3 := fun h => hm3 (h ▸ hqm)
        have hmq : m = q * (m / q) := (Nat.mul_div_cancel' hqm).symm
        have hmq_lt : m / q < m := Nat.div_lt_self (by omega) hq.one_lt
        have hmq_pos : 1 ≤ m / q := Nat.div_pos (Nat.le_of_dvd (by omega) hqm) hq.pos
        have hmq_le : m / q ≤ M + 2 := (Nat.div_le_self m q).trans hm_le
        have hmq3 : ¬ 3 ∣ (m / q) := fun h => hm3 (dvd_trans h (Nat.div_dvd_of_dvd hqm))
        conv_lhs => rw [hmq]
        conv_rhs => rw [hmq]
        rw [Nat.cast_mul, legendreSym.mul, legendreSym.mul,
          h_prime_leg q hq hq_le hq3, ih (m / q) hmq_lt hmq_pos hmq_le hmq3]
  intro n hn1 hnM hall
  have hex : ∃ i < 3, (n + i) % 3 = 2 := by
    rcases Nat.mod_lt n (by decide : 0 < 3) with hlt
    have hcas : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hcas with h | h | h
    · exact ⟨2, by omega, by omega⟩
    · exact ⟨1, by omega, by omega⟩
    · exact ⟨0, by omega, by omega⟩
  obtain ⟨i, hi3, hm_mod⟩ := hex
  have hm1 : 1 ≤ n + i := by omega
  have hm_le : n + i ≤ M + 2 := by omega
  have hm3 : ¬ 3 ∣ (n + i) := by omega
  have hleg : legendreSym p (n + i) = legendreSym 3 (n + i) := h_leg_m (n + i) hm1 hm_le hm3
  have hm_zmod3 : ((n + i : ℕ) : ZMod 3) = (2 : ZMod 3) :=
    (ZMod.natCast_eq_natCast_iff (n + i) 2 3).mpr (by simpa [Nat.ModEq] using hm_mod)
  have hleg3 : legendreSym 3 (n + i) = -1 := by
    rw [← Nat.cast_add, legendreSym.eq_neg_one_iff']
    simpa [hm_zmod3] using h_not_sq_two_three
  have hlegp : legendreSym p (n + i) = -1 := hleg.trans hleg3
  have hnsq : ¬ IsSquare ((n + i : ℕ) : ZMod p) := (legendreSym.eq_neg_one_iff' p).mp hlegp
  obtain ⟨_, x, hx⟩ := hall i hi3
  exact hnsq ⟨x, by rw [← hx, sq]⟩

theorem OMA.solution : type_of% @Erdos436.erdos_436.variants.even_three := by
  intro k _ hk
  obtain ⟨t, rfl⟩ := hk
  unfold Erdos436.runLimsup
  rw [limsup_eq_iInf_iSup, eq_top_iff]
  refine le_iInf₂ fun s hs => ?_
  rw [mem_inf_principal, mem_atTop_sets] at hs
  obtain ⟨N, hN⟩ := hs
  suffices h : ∀ M : ℕ, (M : ℕ∞) ≤ ⨆ a ∈ s, Erdos436.r (t + t) 3 a by
    cases hx : (⨆ a ∈ s, Erdos436.r (t + t) 3 a) with
    | top => exact le_rfl
    | coe n =>
      exfalso
      have h' := h (n + 1)
      rw [hx] at h'
      norm_cast at h'
      omega
  intro M
  obtain ⟨p, hpN, hp_prime, hp_avoid⟩ := exists_prime_avoiding_three_consec M N
  have hps : p ∈ s := hN p hpN hp_prime
  refine le_trans ?_ (le_iSup₂ p hps)
  unfold Erdos436.r
  refine le_iInf₂ fun n ⟨hn1, hn_res⟩ => ?_
  have hn_res2 : ∀ i < 3, Erdos436.IsPowerResidue 2 p (n + i) := by
    intro i hi
    obtain ⟨hnz, x, hx⟩ := hn_res i hi
    exact ⟨hnz, x ^ t, by rw [← hx, ← pow_mul, mul_two]⟩
  have hgt : M < n := by
    by_contra hle
    exact hp_avoid n hn1 (by omega) hn_res2
  exact Nat.cast_le.mpr hgt.le
