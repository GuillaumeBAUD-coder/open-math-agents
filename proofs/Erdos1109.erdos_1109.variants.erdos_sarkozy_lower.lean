import FormalConjectures.ErdosProblems.«1109»

-- Problem: Erdős Problem 1109 — erdos sarkozy lower
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1109.lean:76 (declaration Erdos1109.erdos_1109.variants.erdos_sarkozy_lower)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Finset
open scoped Pointwise

-- Erdős–Sárközy lower bound: greedy choice of k elements 1 + Q t, Q = 4 (primorial (2k))^2,
-- so every pairwise sum is 2 mod p^2 for p ≤ 2k; larger primes are excluded by counting.
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @Erdos1109.erdos_1109.variants.erdos_sarkozy_lower := by
  have cnt : ∀ (T q D c : ℕ), 0 < q → Nat.Coprime q D →
      ((range T).filter (fun t => q ∣ c + D * t)).card ≤ T / q + 1 := by
    intro T q D c hq hD
    have : ((range T).filter (fun t => q ∣ c + D * t)).card ≤ (range (T / q + 1)).card := by
      apply Finset.card_le_card_of_injOn (fun t => t / q)
      · intro t ht
        simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ht
        simp only [Finset.coe_range, Set.mem_Iio]
        have h2 : t / q ≤ T / q := Nat.div_le_div_right ht.1.le
        omega
      · intro t1 h1 t2 h2 heq
        simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at h1 h2
        have e1 : c + D * t1 ≡ c + D * t2 [MOD q] :=
          (Nat.modEq_zero_iff_dvd.2 h1.2).trans (Nat.modEq_zero_iff_dvd.2 h2.2).symm
        have e2 : D * t1 ≡ D * t2 [MOD q] := Nat.ModEq.add_left_cancel' c e1
        have e3 : t1 ≡ t2 [MOD q] := Nat.ModEq.cancel_left_of_coprime hD e2
        have h3 := Nat.div_add_mod t1 q
        have h4 := Nat.div_add_mod t2 q
        unfold Nat.ModEq at e3
        simp only at heq
        rw [heq, e3] at h3
        omega
    simpa using this
  have sumsq : ∀ (P L : ℕ), 1 ≤ P → P ≤ L →
      ∑ n ∈ Ioc P L, (1 : ℚ) / ((n : ℚ) * n) ≤ 1 / P - 1 / L := by
    intro P L hP hL
    induction L, hL using Nat.le_induction with
    | base => simp
    | succ L hPL ih =>
      rw [Finset.sum_Ioc_succ_top hPL]
      have hL1 : (1 : ℚ) ≤ L := by exact_mod_cast le_trans hP hPL
      have key : (1 : ℚ) / (((L + 1 : ℕ) : ℚ) * ((L + 1 : ℕ) : ℚ)) ≤ 1 / L - 1 / ((L + 1 : ℕ) : ℚ) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
  have key : ∀ k : ℕ, 1 ≤ k → ∃ A : Finset ℕ, A ⊆ Icc 1 (2 ^ (32 * k)) ∧
      (∀ n ∈ A + A, Squarefree n) ∧ A.card = k := by
    intro k hk
    set P := 2 * k with hPdef
    set R := primorial P with hRdef
    set Q := 4 * R ^ 2 with hQdef
    set T := 64 * k ^ 2 * Q with hTdef
    set L := 12 * k * Q with hLdef
    have hR : 0 < R := primorial_pos P
    have hQ : 0 < Q := by positivity
    have small : ∀ p, p.Prime → p ≤ P → ∀ m, ¬ p * p ∣ 2 + Q * m := by
      intro p hp hpP m h
      have hpR : p ∣ R := Finset.dvd_prod_of_mem _
        (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hp⟩)
      have hQd : p * p ∣ Q := by
        have : p * p ∣ R ^ 2 := by rw [sq]; exact Nat.mul_dvd_mul hpR hpR
        exact this.trans (Dvd.intro_left 4 rfl)
      have h2 : p * p ∣ 2 := (Nat.dvd_add_right (Dvd.dvd.mul_right hQd m)).1 (by rwa [add_comm] at h)
      have := Nat.le_of_dvd (by norm_num) h2
      have := hp.two_le
      nlinarith
    have big : ∀ p, p.Prime → P < p → Nat.Coprime (p * p) (2 * Q) := by
      intro p hp hPp
      have hc : Nat.Coprime p (2 * Q) := by
        rw [hp.coprime_iff_not_dvd]
        intro hd
        have h2 : ¬ p ∣ 2 := fun h => by
          have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h
          omega
        rw [hQdef, ← mul_assoc] at hd
        rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
        · rcases (Nat.Prime.dvd_mul hp).1 h with h' | h'
          · exact h2 h'
          · exact h2 ((Nat.Prime.dvd_mul hp).1 (by simpa using h') |>.elim id id)
        · have hR' : p ∣ R := hp.dvd_of_dvd_pow h
          rw [hRdef, primorial] at hR'
          obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finset_prod_iff hp.prime _).1 hR'
          obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
          have := (Nat.prime_dvd_prime_iff_eq hp hq2).1 hpq
          have := Finset.mem_range.1 hq1
          omega
      exact Nat.Coprime.mul hc hc
    set x : ℕ → ℕ := fun t => 1 + Q * t with hx
    have hxx : ∀ t s, x t + x s = 2 + Q * (t + s) := by intro t s; simp only [hx]; ring
    have hbound : ∀ t s, t < T → s < T → 2 + Q * (t + s) ≤ L * L := by
      intro t s ht hs
      have : Q * (t + s) ≤ Q * (2 * T) := Nat.mul_le_mul_left _ (by omega)
      have h1 : 1 ≤ k := hk
      have h2 : 2 ≤ 16 * k ^ 2 * Q ^ 2 := by
        have : 1 ≤ k ^ 2 * Q ^ 2 := Nat.one_le_iff_ne_zero.2 (by positivity)
        nlinarith
      simp only [hLdef, hTdef] at this ⊢
      nlinarith
    have sqf : ∀ t s, t < T → s < T →
        (∀ p ∈ (Ioc P L).filter Nat.Prime, ¬ p * p ∣ 2 + Q * (t + s)) → Squarefree (x t + x s) := by
      intro t s ht hs H
      rw [Nat.squarefree_iff_prime_squarefree]
      intro p hp hdvd
      have hp' : p.Prime := hp
      rw [hxx] at hdvd
      by_cases hpP : p ≤ P
      · exact small p hp' hpP _ hdvd
      · have hle : p * p ≤ L * L := (Nat.le_of_dvd (by omega) hdvd).trans (hbound t s ht hs)
        have hpL : p ≤ L := Nat.mul_self_le_mul_self_iff.1 hle
        exact H p (Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨by omega, hpL⟩, hp'⟩) hdvd
    set G : Finset ℕ → Prop := fun S => ∀ t ∈ S, ∀ s ∈ S, Squarefree (x t + x s) with hG
    have hPpos : 1 ≤ P := by omega
    have hPL : P ≤ L := by
      have : 1 ≤ Q := hQ
      simp only [hPdef, hLdef]; nlinarith
    have step : ∀ S : Finset ℕ, S ⊆ range T → S.card < k → G S →
        ∃ t ∈ range T, t ∉ S ∧ G (insert t S) := by
      intro S hST hSk hGS
      set Pr := (Ioc P L).filter Nat.Prime with hPr
      set B := S ∪ Pr.biUnion (fun p => (S.biUnion fun s =>
          (range T).filter (fun t => p * p ∣ (2 + Q * s) + Q * t)) ∪
          (range T).filter (fun t => p * p ∣ 2 + (2 * Q) * t)) with hB
      have hcp : ∀ p ∈ Pr, ∀ c D, Nat.Coprime (p * p) D → 
          ((range T).filter (fun t => p * p ∣ c + D * t)).card ≤ T / (p * p) + 1 := by
        intro p hp c D hD
        have := (Finset.mem_filter.1 hp).2.pos
        exact cnt T (p * p) D c (by positivity) hD
      have hcardB : B.card ≤ S.card + ∑ p ∈ Pr, (S.card + 1) * (T / (p * p) + 1) := by
        refine (Finset.card_union_le _ _).trans (Nat.add_le_add_left ?_ _)
        refine (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun p hp => ?_)
        have hpP : P < p := (Finset.mem_Ioc.1 (Finset.mem_filter.1 hp).1).1
        have hcop := big p (Finset.mem_filter.1 hp).2 hpP
        refine (Finset.card_union_le _ _).trans ?_
        have h1 : (S.biUnion fun s => (range T).filter (fun t => p * p ∣ (2 + Q * s) + Q * t)).card
            ≤ S.card * (T / (p * p) + 1) := by
          refine (Finset.card_biUnion_le).trans ?_
          have : ∀ s ∈ S, ((range T).filter (fun t => p * p ∣ (2 + Q * s) + Q * t)).card
              ≤ T / (p * p) + 1 := fun s _ =>
            hcp p hp _ _ (Nat.Coprime.coprime_mul_left_right hcop)
          calc _ ≤ ∑ s ∈ S, (T / (p * p) + 1) := Finset.sum_le_sum this
            _ = _ := by rw [Finset.sum_const, smul_eq_mul]
        have h2 := hcp p hp 2 (2 * Q) hcop
        nlinarith
      have hsumQ : ((∑ p ∈ Pr, (T / (p * p) + 1) : ℕ) : ℚ) ≤ (T : ℚ) / P + L := by
        have hsub : Pr ⊆ Ioc P L := Finset.filter_subset _ _
        have e1 : (∑ p ∈ Pr, (T / (p * p) + 1) : ℕ) ≤ ∑ n ∈ Ioc P L, (T / (n * n) + 1) :=
          Finset.sum_le_sum_of_subset hsub
        have e2 : ((∑ n ∈ Ioc P L, (T / (n * n) + 1) : ℕ) : ℚ) ≤ (T : ℚ) / P + L := by
          push_cast
          rw [Finset.sum_add_distrib]
          have e3 : ∑ n ∈ Ioc P L, ((T / (n * n) : ℕ) : ℚ) ≤ T * ∑ n ∈ Ioc P L, (1 : ℚ) / ((n : ℚ) * n) := by
            rw [Finset.mul_sum]
            refine Finset.sum_le_sum fun n hn => ?_
            rw [mul_one_div]
            have := Nat.cast_div_le (α := ℚ) (m := T) (n := n * n)
            push_cast at this
            exact this
          have e4 := sumsq P L hPpos hPL
          have e5 : (T : ℚ) * (1 / P - 1 / L) ≤ T / P := by
            rw [mul_sub, mul_one_div, mul_one_div]
            have : (0 : ℚ) ≤ T / L := by positivity
            linarith
          simp only [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
          have : ((L - P : ℕ) : ℚ) ≤ L := by exact_mod_cast Nat.sub_le L P
          nlinarith [mul_le_mul_of_nonneg_left e4 (show (0 : ℚ) ≤ T by positivity)]
        exact (Nat.cast_le.2 e1).trans e2
      have hBlt : B.card < T := by
        have h1 : (B.card : ℚ) ≤ S.card + (S.card + 1) * ((T : ℚ) / P + L) := by
          have := hcardB
          rw [← Finset.mul_sum] at this
          have h2 : (B.card : ℚ) ≤ S.card + (S.card + 1) * ((∑ p ∈ Pr, (T / (p * p) + 1) : ℕ) : ℚ) := by
            exact_mod_cast this
          refine h2.trans ?_
          have : (0 : ℚ) ≤ S.card + 1 := by positivity
          nlinarith
        have hS : (S.card : ℚ) + 1 ≤ k := by exact_mod_cast hSk
        have hP' : (P : ℚ) = 2 * k := by simp [hPdef]
        have hkpos : (0 : ℚ) < k := by exact_mod_cast hk
        have h3 : ((S.card : ℚ) + 1) * ((T : ℚ) / P) ≤ T / 2 := by
          rw [hP']
          have : ((S.card : ℚ) + 1) * ((T : ℚ) / (2 * k)) ≤ k * ((T : ℚ) / (2 * k)) :=
            mul_le_mul_of_nonneg_right hS (by positivity)
          refine this.trans (le_of_eq ?_)
          field_simp
        have h4 : ((S.card : ℚ) + 1) * L ≤ k * L := mul_le_mul_of_nonneg_right hS (by positivity)
        have hTq : (T : ℚ) = 64 * k ^ 2 * Q := by simp [hTdef]
        have hLq : (L : ℚ) = 12 * k * Q := by simp [hLdef]
        have hQq : (1 : ℚ) ≤ Q := by exact_mod_cast hQ
        have h5 : (B.card : ℚ) < T := by
          have : (S.card : ℚ) ≤ k := by linarith
          rw [mul_add] at h1
          have hkk : (k : ℚ) ≤ k ^ 2 * Q := by nlinarith
          rw [hLq] at h4 h1
          rw [hTq] at h3 h1 ⊢
          nlinarith
        exact_mod_cast h5
      obtain ⟨t, htT, htB⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := B) (t := range T)
        (by simpa using hBlt)
      have htS : t ∉ S := fun h => htB (Finset.mem_union_left _ h)
      have htT' : t < T := Finset.mem_range.1 htT
      refine ⟨t, htT, htS, ?_⟩
      have hts : ∀ s ∈ S, Squarefree (x t + x s) := by
        intro s hs
        have hsT : s < T := Finset.mem_range.1 (hST hs)
        apply sqf t s htT' hsT
        intro p hp hdvd
        apply htB
        refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_union_left _
          (Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_filter.2 ⟨htT, ?_⟩⟩)⟩)
        have : 2 + Q * s + Q * t = 2 + Q * (t + s) := by ring
        rw [this]; exact hdvd
      have htt : Squarefree (x t + x t) := by
        apply sqf t t htT' htT'
        intro p hp hdvd
        apply htB
        refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_union_right _
          (Finset.mem_filter.2 ⟨htT, ?_⟩)⟩)
        have : 2 + 2 * Q * t = 2 + Q * (t + t) := by ring
        rw [this]; exact hdvd
      intro a ha b hb
      rcases Finset.mem_insert.1 ha with h1 | h1 <;> rcases Finset.mem_insert.1 hb with h2 | h2
      · rw [h1, h2]; exact htt
      · rw [h1]; exact hts b h2
      · rw [h2, add_comm]; exact hts a h1
      · exact hGS a h1 b h2
    have build : ∀ i ≤ k, ∃ S : Finset ℕ, S ⊆ range T ∧ S.card = i ∧ G S := by
      intro i
      induction i with
      | zero => intro _; exact ⟨∅, by simp, by simp, by simp [hG]⟩
      | succ i ih =>
        intro hi
        obtain ⟨S, hST, hSc, hGS⟩ := ih (by omega)
        obtain ⟨t, htT, htS, hG'⟩ := step S hST (by omega) hGS
        refine ⟨insert t S, ?_, by rw [Finset.card_insert_of_notMem htS, hSc], hG'⟩
        exact Finset.insert_subset htT hST
    obtain ⟨S, hST, hSc, hGS⟩ := build k le_rfl
    have hxinj : Function.Injective x := by
      intro a b h
      simp only [hx] at h
      exact Nat.eq_of_mul_eq_mul_left hQ (by omega)
    have hRb : R ≤ 2 ^ (4 * k) := by
      have := primorial_le_four_pow P
      calc R ≤ 4 ^ P := this
        _ = 2 ^ (4 * k) := by rw [hPdef, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
    have hk2 : k ^ 2 ≤ 2 ^ (2 * k) := by
      have := (Nat.lt_two_pow_self (n := k)).le
      calc k ^ 2 ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left this 2
        _ = 2 ^ (2 * k) := by rw [← pow_mul]; ring_nf
    have hQb : Q ≤ 2 ^ (8 * k + 2) := by
      calc Q = 4 * R ^ 2 := rfl
        _ ≤ 4 * (2 ^ (4 * k)) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hRb 2)
        _ = 2 ^ (8 * k + 2) := by rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; ring_nf
    have hxb : ∀ t < T, x t ≤ 2 ^ (32 * k) := by
      intro t ht
      have h1 : x t ≤ 1 + Q * T := by simp only [hx]; nlinarith
      have h2 : Q * T ≤ 2 ^ (18 * k + 10) := by
        calc Q * T = 64 * k ^ 2 * Q * Q := by rw [hTdef]; ring
          _ ≤ 64 * 2 ^ (2 * k) * 2 ^ (8 * k + 2) * 2 ^ (8 * k + 2) := by gcongr
          _ = 2 ^ (18 * k + 10) := by
            rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_add, ← pow_add, ← pow_add]; ring_nf
      have h3 : 1 + 2 ^ (18 * k + 10) ≤ 2 ^ (32 * k) := by
        have : 2 ^ (18 * k + 11) ≤ 2 ^ (32 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have : 2 ^ (18 * k + 11) = 2 * 2 ^ (18 * k + 10) := by ring
        have : 1 ≤ 2 ^ (18 * k + 10) := Nat.one_le_two_pow
        omega
      omega
    refine ⟨S.image x, ?_, ?_, ?_⟩
    · intro y hy
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
      have htT := Finset.mem_range.1 (hST ht)
      exact Finset.mem_Icc.2 ⟨by simp only [hx]; omega, hxb t htT⟩
    · intro n hn
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 hn
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hb
      exact hGS t ht s hs
    · rw [Finset.card_image_of_injective _ hxinj, hSc]
  have hf : ∀ k N, 1 ≤ k → 2 ^ (32 * k) ≤ N → k ≤ Erdos1109.f N := by
    intro k N hk hN
    obtain ⟨A, hA, hsq, hc⟩ := key k hk
    unfold Erdos1109.f
    apply le_csSup
    · refine ⟨N, ?_⟩
      rintro m ⟨B, hB, -, rfl⟩
      simpa using Finset.card_le_card hB
    · exact ⟨A, hA.trans (Finset.Icc_subset_Icc le_rfl hN), hsq, hc⟩
  apply Asymptotics.IsBigO.of_bound 64
  filter_upwards [Filter.eventually_ge_atTop (2 ^ 32)] with N hN
  set m := Nat.log 2 N with hmdef
  have hN0 : N ≠ 0 := by positivity
  have hm : 32 ≤ m := Nat.le_log_of_pow_le (by norm_num) hN
  have hk := hf (m / 32) N (by omega)
    ((Nat.pow_le_pow_right (by norm_num) (by omega : 32 * (m / 32) ≤ m)).trans
      (Nat.pow_log_le_self 2 hN0))
  have hlt : N < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  have hlog : Real.log N ≤ (m + 1) * Real.log 2 := by
    have : (N : ℝ) ≤ 2 ^ (m + 1) := by exact_mod_cast hlt.le
    have := Real.log_le_log hNpos this
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hm1 : ((m : ℝ) + 1) ≤ 64 * ((m / 32 : ℕ) : ℝ) := by
    have : m + 1 ≤ 64 * (m / 32) := by omega
    exact_mod_cast this
  have hkR : ((m / 32 : ℕ) : ℝ) ≤ Erdos1109.f N := by exact_mod_cast hk
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hN0)),
    abs_of_nonneg (by positivity)]
  have h0 : (0 : ℝ) ≤ m + 1 := by positivity
  nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]
