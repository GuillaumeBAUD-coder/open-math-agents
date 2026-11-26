import FormalConjectures.ErdosProblems.«329»

-- Problem: Erdős Problem 329: Maximum Density of Sidon Sets — turan 1941
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/329.lean:85 (declaration Erdos329.erdos_329.variants.turan_1941)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA

open Finset

/-- Sliding-window double counting (Erdős–Turán) for a finite Sidon set in `[0, N]`. -/
lemma window_count (F : Finset ℕ) (N u : ℕ) (hF : ∀ a ∈ F, a ≤ N)
    (hS : ∀ a ∈ F, ∀ b ∈ F, ∀ c ∈ F, ∀ d ∈ F, a + c = b + d →
      (a = b ∧ c = d) ∨ (a = d ∧ c = b)) :
    (F.card * u) ^ 2 ≤ (N + u) * (F.card * u + u * u) := by
  classical
  set W : ℕ → Finset ℕ := fun t => F.filter (fun a => a ≤ t ∧ t < a + u) with hW
  have h1 : ∑ t ∈ range (N + u), (W t).card = F.card * u := by
    have : ∀ t, (W t).card = ∑ a ∈ F, if (a ≤ t ∧ t < a + u) then 1 else 0 := by
      intro t
      simp only [hW, Finset.card_filter]
    simp_rw [this]
    rw [Finset.sum_comm]
    have h : ∀ a ∈ F, (∑ t ∈ range (N + u), if (a ≤ t ∧ t < a + u) then 1 else 0) = u := by
      intro a ha
      rw [← Finset.card_filter]
      have : (range (N + u)).filter (fun t => a ≤ t ∧ t < a + u) = Finset.Ico a (a + u) := by
        ext t
        have := hF a ha
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega
      rw [this]
      simp
    rw [Finset.sum_congr rfl h]
    simp
  have h2 : ∑ t ∈ range (N + u), (W t).offDiag.card ≤ u * u := by
    rw [← Finset.card_sigma]
    have hle : ((range (N + u)).sigma (fun t => (W t).offDiag)).card ≤ (range u).offDiag.card := by
      apply Finset.card_le_card_of_injOn (fun p => (p.1 - p.2.1, p.1 - p.2.2))
      · rintro ⟨t, a, b⟩ hp
        simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_offDiag,
          hW, Finset.mem_filter, Finset.mem_range] at hp ⊢
        omega
      · rintro ⟨t, a, b⟩ hp ⟨t', a', b'⟩ hp' heq
        simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_offDiag,
          hW, Finset.mem_filter, Finset.mem_range] at hp hp'
        simp only [Prod.mk.injEq] at heq
        obtain ⟨-, ⟨haF, ha1, ha2⟩, ⟨hbF, hb1, hb2⟩, hab⟩ := hp
        obtain ⟨-, ⟨haF', ha1', ha2'⟩, ⟨hbF', hb1', hb2'⟩, hab'⟩ := hp'
        obtain ⟨e1, e2⟩ := heq
        have hsum : a + b' = a' + b := by omega
        rcases hS a haF a' haF' b' hbF' b hbF hsum with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · subst h1; subst h2
          have : t = t' := by omega
          subst this
          rfl
        · exact absurd h1 hab
    refine hle.trans ?_
    rw [Finset.offDiag_card]
    simp
  have h3 : (∑ t ∈ range (N + u), (W t).card) ^ 2 ≤
      (range (N + u)).card * ∑ t ∈ range (N + u), (W t).card ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h4 : ∀ t, (W t).card ^ 2 = (W t).card + (W t).offDiag.card := by
    intro t
    rw [Finset.offDiag_card, sq]
    have := Nat.le_mul_self (W t).card
    omega
  simp_rw [h4] at h3
  rw [Finset.sum_add_distrib, h1, Finset.card_range] at h3
  exact h3.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left h2 _))

/-- Analytic cleanup: from the counting inequality with `u ≈ ε N` one gets a bound on `k`. -/
lemma real_bound (ε N u k : ℝ) (hε : 0 < ε) (hN : 0 < N) (hk1 : 1 ≤ k)
    (hu1 : ε * N ≤ u) (hu2 : u ≤ ε * N + 1)
    (h : k ^ 2 * u ≤ (N + u) * (k + u))
    (hk : (1 + ε) ^ 2 * N < k ^ 2) :
    ε ^ 2 * k < 2 * (1 + ε) ^ 2 := by
  have hu : 0 < u := lt_of_lt_of_le (mul_pos hε hN) hu1
  -- ε k² ≤ (1+ε)(k+u)
  have s1 : ε * k ^ 2 ≤ (1 + ε) * (k + u) := by
    have e1 : ε * (N + u) ≤ (1 + ε) * u := by nlinarith
    have e2 : ε * (k ^ 2 * u) ≤ (1 + ε) * u * (k + u) := by
      calc ε * (k ^ 2 * u) ≤ ε * ((N + u) * (k + u)) := by gcongr
        _ = (ε * (N + u)) * (k + u) := by ring
        _ ≤ ((1 + ε) * u) * (k + u) := by gcongr
    have e3 : (ε * k ^ 2) * u ≤ ((1 + ε) * (k + u)) * u := by nlinarith
    exact le_of_mul_le_mul_right e3 hu
  have s2 : ε * k ^ 2 ≤ (1 + ε) * (k + 1) + ε * ((1 + ε) * N) := by nlinarith
  have s3 : (1 + ε) * (ε * ((1 + ε) * N)) < ε * k ^ 2 := by nlinarith
  have s4 : ε ^ 2 * k ^ 2 < (1 + ε) ^ 2 * (k + 1) := by nlinarith
  have s5 : ε ^ 2 * k ^ 2 < (2 * (1 + ε) ^ 2) * k := by nlinarith [sq_nonneg (1 + ε)]
  have hk0 : 0 < k := by linarith
  have s6 : (ε ^ 2 * k) * k < (2 * (1 + ε) ^ 2) * k := by nlinarith
  exact lt_of_mul_lt_mul_right s6 hk0.le

end OMA

theorem OMA.solution : type_of% @Erdos329.erdos_329.variants.turan_1941 := by
  classical
  intro A hA
  unfold Erdos329.sidonUpperDensity
  apply le_of_forall_pos_le_add
  intro ε hε
  have hnn : ∀ N : ℕ, 0 ≤ Erdos329.sqrtPartialDensity A N := by
    intro N
    unfold Erdos329.sqrtPartialDensity
    positivity
  refine Filter.limsup_le_of_le (Filter.isCoboundedUnder_le_of_le Filter.atTop hnn) ?_
  set K : ℝ := 2 * (1 + ε) ^ 2 / ε ^ 2 with hK
  obtain ⟨N0, hN0⟩ := exists_nat_ge (K ^ 2 + 1)
  filter_upwards [Filter.eventually_ge_atTop (N0 + 1)] with N hN
  have hNpos : (0 : ℝ) < N := by
    have : 1 ≤ N := by omega
    exact_mod_cast this
  have hNK : K ^ 2 < N := by
    have : (N0 : ℝ) + 1 ≤ N := by exact_mod_cast hN
    linarith
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  unfold Erdos329.sqrtPartialDensity
  set F : Finset ℕ := (Finset.Icc 1 N).filter (fun a => a ∈ A) with hFdef
  have hcoe : (A ∩ Set.Icc 1 N) = (F : Set ℕ) := by
    ext x
    simp only [hFdef, Set.mem_inter_iff, Set.mem_Icc, Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq]
    tauto
  rw [hcoe, Set.ncard_coe_finset, div_le_iff₀ hsq]
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = (F.card : ℝ) := ⟨_, rfl⟩
  rw [← hk] at hcon
  have hk0 : 0 < k := lt_of_le_of_lt (by positivity) hcon
  have hk1 : 1 ≤ k := by
    rw [hk] at hk0 ⊢
    have : 0 < F.card := by exact_mod_cast hk0
    have : 1 ≤ F.card := this
    exact_mod_cast this
  set u : ℕ := ⌈ε * N⌉₊ with hu
  have hu1 : ε * N ≤ (u : ℝ) := Nat.le_ceil _
  have hu2 : (u : ℝ) ≤ ε * N + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hupos : (0 : ℝ) < u := lt_of_lt_of_le (mul_pos hε hNpos) hu1
  have hwin := OMA.window_count F N u
    (fun a ha => (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2)
    (fun a ha b hb c hc d hd h =>
      hA a (Finset.mem_filter.mp ha).2 b (Finset.mem_filter.mp hb).2
        c (Finset.mem_filter.mp hc).2 d (Finset.mem_filter.mp hd).2 h)
  have hwinR : (k * u) ^ 2 ≤ ((N : ℝ) + u) * (k * u + u * u) := by
    rw [hk]
    exact_mod_cast hwin
  have h' : k ^ 2 * u ≤ ((N : ℝ) + u) * (k + u) := by
    have : (k ^ 2 * u) * u ≤ (((N : ℝ) + u) * (k + u)) * u := by nlinarith
    exact le_of_mul_le_mul_right this hupos
  have hkk : (1 + ε) ^ 2 * N < k ^ 2 := by
    have h0 : 0 ≤ (1 + ε) * Real.sqrt N := by positivity
    have := mul_self_lt_mul_self h0 hcon
    have hs := Real.mul_self_sqrt hNpos.le
    nlinarith
  have hb := OMA.real_bound ε N u k hε hNpos hk1 hu1 hu2 h' hkk
  have hkK : k < K := by
    rw [hK, lt_div_iff₀ (by positivity)]
    linarith
  have hsqk : Real.sqrt N < k := by
    have : Real.sqrt N ≤ (1 + ε) * Real.sqrt N := by nlinarith
    linarith
  have hK0 : 0 ≤ K := by positivity
  have : (N : ℝ) < K ^ 2 := by
    have hs := Real.mul_self_sqrt hNpos.le
    nlinarith
  linarith
