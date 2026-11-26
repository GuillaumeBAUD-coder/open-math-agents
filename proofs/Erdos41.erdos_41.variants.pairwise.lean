import FormalConjectures.ErdosProblems.«41»

/-!
# Erdős Problem 41 (Pairwise Case)

Proof that if `A ⊆ ℕ` is an infinite set with distinct pairwise sums (`NtupleCondition A 2`,
equivalently `IsSidon A`), then `liminf_{N → ∞} |A ∩ [1, N]| / √N = 0`, by deducing from the
Halberstam--Roth bound that `|A ∩ [1, x]| ≤ 120 √(x / log x)` holds for arbitrarily large `x`.
-/

-- Problem: Erdős Problem 41 — pairwise
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/41.lean:65 (declaration Erdos41.erdos_41.variants.pairwise)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Real Finset

open scoped Classical

private lemma isSidon_of_ntupleCondition_two {A : Set ℕ} (hA : Erdos41.NtupleCondition A 2) :
    IsSidon A := by
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
  have heq : (i₁ ::ₘ {i₂} : Multiset ℕ) = (j₁ ::ₘ {j₂} : Multiset ℕ) := by
    apply hA
    · intro x hx
      simp only [Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · intro x hx
      simp only [Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · simp
    · simp
    · simpa using hsum
  have hmem : i₁ ∈ (j₁ ::ₘ {j₂} : Multiset ℕ) := by
    rw [← heq]
    simp
  simp only [Multiset.mem_cons, Multiset.mem_singleton] at hmem
  rcases hmem with rfl | rfl
  · left
    refine ⟨rfl, ?_⟩
    exact Multiset.singleton_inj.mp ((Multiset.cons_inj_right i₁).mp heq)
  · right
    refine ⟨rfl, ?_⟩
    have hswap : (j₁ ::ₘ {i₁} : Multiset ℕ) = (i₁ ::ₘ {j₁} : Multiset ℕ) := Multiset.pair_comm j₁ i₁
    rw [hswap] at heq
    exact Multiset.singleton_inj.mp ((Multiset.cons_inj_right i₁).mp heq)

private lemma sidon_diff_inj {A : Set ℕ} (hA : IsSidon A)
    {a₁ b₁ a₂ b₂ : ℕ} (ha₁ : a₁ ∈ A) (hb₁ : b₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₂ : b₂ ∈ A)
    (h₁ : a₁ < b₁) (h₂ : a₂ < b₂) (heq : b₁ - a₁ = b₂ - a₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have hsum : b₁ + a₂ = b₂ + a₁ := by omega
  rcases hA b₁ hb₁ b₂ hb₂ a₂ ha₂ a₁ ha₁ hsum with ⟨hb, ha⟩ | ⟨hba, _⟩
  · exact ⟨ha.symm, hb⟩
  · omega

private noncomputable def sidonCount (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (· ∈ A)).card

private lemma sidonCount_eq_ncard (A : Set ℕ) (n : ℕ) :
    sidonCount A n = (A ∩ Set.Icc 1 n).ncard := by
  unfold sidonCount
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Icc, Set.mem_inter_iff, Set.mem_Icc]
  tauto

private lemma sidonCount_mul_pred_le {A : Set ℕ} (hA : IsSidon A) (n : ℕ) :
    sidonCount A n * (sidonCount A n - 1) ≤ 2 * n := by
  let S : Finset ℕ := (Finset.Icc 1 n).filter (· ∈ A)
  let P : Finset (ℕ × ℕ) := (S ×ˢ S).filter (fun p => p.1 < p.2)
  have hP_le : P.card ≤ n := by
    have hinj : Set.InjOn (fun p : ℕ × ℕ => p.2 - p.1) (P : Set (ℕ × ℕ)) := by
      intro p₁ hp₁ p₂ hp₂ heq
      simp only [Finset.mem_coe, P, Finset.mem_filter, Finset.mem_product, S] at hp₁ hp₂
      have ⟨h1, h2⟩ := sidon_diff_inj hA hp₁.1.1.2 hp₁.1.2.2 hp₂.1.1.2 hp₂.1.2.2 hp₁.2 hp₂.2 heq
      exact Prod.ext h1 h2
    have hmaps : Set.MapsTo (fun p : ℕ × ℕ => p.2 - p.1) (P : Set (ℕ × ℕ))
        (Finset.Icc 1 n : Set ℕ) := by
      intro p hp
      simp only [Finset.mem_coe, P, Finset.mem_filter, Finset.mem_product, S,
        Finset.mem_Icc] at hp ⊢
      omega
    have hle := Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.2 - p.1) hmaps hinj
    simpa using hle
  have h2P : 2 * P.card = S.card * (S.card - 1) := by
    let Q : Finset (ℕ × ℕ) := (S ×ˢ S).filter (fun p => p.2 < p.1)
    have hdisj : Disjoint P Q := by
      rw [Finset.disjoint_filter]
      intro p _ h1 h2
      omega
    have hunion : P ∪ Q = S.offDiag := by
      ext ⟨a, b⟩
      simp only [P, Q, Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag]
      constructor
      · rintro (⟨⟨ha, hb⟩, hlt⟩ | ⟨⟨ha, hb⟩, hlt⟩)
        · exact ⟨ha, hb, ne_of_lt hlt⟩
        · exact ⟨ha, hb, ne_of_gt hlt⟩
      · rintro ⟨ha, hb, hne⟩
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact Or.inl ⟨⟨ha, hb⟩, hlt⟩
        · exact Or.inr ⟨⟨ha, hb⟩, hlt⟩
    have hPQ : P.card = Q.card := by
      refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
      · intro p hp
        simp only [P, Q, Finset.mem_filter, Finset.mem_product] at hp ⊢
        exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
      · intro p₁ _ p₂ _ h
        exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
      · intro q hq
        simp only [P, Q, Finset.mem_filter, Finset.mem_product] at hq ⊢
        exact ⟨(q.2, q.1), ⟨⟨hq.1.2, hq.1.1⟩, hq.2⟩, rfl⟩
    have hoff : S.offDiag.card = S.card * S.card - S.card := Finset.offDiag_card S
    have hcard : P.card + Q.card = S.offDiag.card := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have hmul : S.card * (S.card - 1) = S.card * S.card - S.card := by
      rw [Nat.mul_sub_left_distrib, mul_one]
    omega
  change S.card * (S.card - 1) ≤ 2 * n
  omega

private lemma sidonCount_le_two_sqrt {A : Set ℕ} (hA : IsSidon A) {n : ℕ} (hn : 1 ≤ n) :
    (sidonCount A n : ℝ) ≤ 2 * Real.sqrt n := by
  have h1 : sidonCount A n * (sidonCount A n - 1) ≤ 2 * n := sidonCount_mul_pred_le hA n
  have hsq : sidonCount A n ^ 2 ≤ 4 * n := by
    rcases Nat.lt_or_ge (sidonCount A n) 2 with hk | hk
    · have : sidonCount A n ≤ 1 := by omega
      nlinarith
    · have h2 : sidonCount A n ≤ 2 * (sidonCount A n - 1) := by omega
      nlinarith
  have hsqR : ((sidonCount A n : ℝ)) ^ 2 ≤ (2 * Real.sqrt n) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    norm_num
    exact_mod_cast hsq
  nlinarith [Real.sqrt_nonneg n]

private lemma sidon_window_sq_sum_le {A : Set ℕ} (hA : IsSidon A) {r : ℕ} (hr : 1 ≤ r) :
    ∑ j ∈ Finset.Icc 1 (r ^ 2), (((Finset.Ioc j (j + r)).filter (· ∈ A)).card) ^ 2 ≤
      5 * r ^ 2 := by
  let W : ℕ → Finset ℕ := fun j => (Finset.Ioc j (j + r)).filter (· ∈ A)
  let P : ℕ → Finset (ℕ × ℕ) := fun j => (W j ×ˢ W j).filter (fun p => p.1 < p.2)
  have hpair_sum : ∑ j ∈ Finset.Icc 1 (r ^ 2), (P j).card ≤ r ^ 2 := by
    rw [← Finset.card_sigma]
    let T := (Finset.Icc 1 (r ^ 2)).sigma P
    have hinj : Set.InjOn (fun x : Σ _ : ℕ, ℕ × ℕ => (x.2.2 - x.2.1, x.2.1 - x.1)) (T : Set _) := by
      intro x₁ hx₁ x₂ hx₂ heq
      simp only [Finset.mem_coe, T, Finset.mem_sigma, P, W, Finset.mem_filter,
        Finset.mem_product, Finset.mem_Ioc] at hx₁ hx₂
      have hdiff : x₁.2.2 - x₁.2.1 = x₂.2.2 - x₂.2.1 := congrArg Prod.fst heq
      have hshift : x₁.2.1 - x₁.1 = x₂.2.1 - x₂.1 := congrArg Prod.snd heq
      have ⟨ha, hb⟩ := sidon_diff_inj hA hx₁.2.1.1.2 hx₁.2.1.2.2 hx₂.2.1.1.2 hx₂.2.1.2.2
        hx₁.2.2 hx₂.2.2 hdiff
      have hj : x₁.1 = x₂.1 := by omega
      cases x₁; cases x₂
      simp only at ha hb hj
      subst hj
      exact congrArg (Sigma.mk _) (Prod.ext ha hb)
    have hmaps : Set.MapsTo (fun x : Σ _ : ℕ, ℕ × ℕ => (x.2.2 - x.2.1, x.2.1 - x.1)) (T : Set _)
        ((Finset.Icc 1 r ×ˢ Finset.Icc 1 r : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
      intro x hx
      simp only [Finset.mem_coe, T, Finset.mem_sigma, P, W, Finset.mem_filter,
        Finset.mem_product, Finset.mem_Ioc, Finset.mem_Icc] at hx ⊢
      exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
    have hle := Finset.card_le_card_of_injOn _ hmaps hinj
    simpa [T, sq] using hle
  have hlin_sum : ∑ j ∈ Finset.Icc 1 (r ^ 2), (W j).card ≤ sidonCount A (r ^ 2 + r) * r := by
    rw [← Finset.card_sigma]
    let T₁ := (Finset.Icc 1 (r ^ 2)).sigma W
    let S := (Finset.Icc 1 (r ^ 2 + r)).filter (· ∈ A)
    have hinj : Set.InjOn (fun x : Σ _ : ℕ, ℕ => (x.2, x.2 - x.1)) (T₁ : Set _) := by
      intro x₁ hx₁ x₂ hx₂ heq
      simp only [Finset.mem_coe, T₁, Finset.mem_sigma, W, Finset.mem_filter,
        Finset.mem_Ioc] at hx₁ hx₂
      have ha : x₁.2 = x₂.2 := congrArg Prod.fst heq
      have hshift : x₁.2 - x₁.1 = x₂.2 - x₂.1 := congrArg Prod.snd heq
      have hj : x₁.1 = x₂.1 := by omega
      cases x₁; cases x₂
      simp only at ha hj
      subst hj; subst ha; rfl
    have hmaps : Set.MapsTo (fun x : Σ _ : ℕ, ℕ => (x.2, x.2 - x.1)) (T₁ : Set _)
        ((S ×ˢ Finset.Icc 1 r : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
      intro x hx
      simp only [Finset.mem_coe, T₁, Finset.mem_sigma, W, S, Finset.mem_filter,
        Finset.mem_product, Finset.mem_Ioc, Finset.mem_Icc] at hx ⊢
      exact ⟨⟨⟨by omega, by omega⟩, hx.2.2⟩, ⟨by omega, by omega⟩⟩
    have hle := Finset.card_le_card_of_injOn _ hmaps hinj
    simpa [T₁, sidonCount, S] using hle
  have hcnt : sidonCount A (r ^ 2 + r) ≤ 3 * r := by
    have h1 := sidonCount_mul_pred_le hA (r ^ 2 + r)
    have hr2 : r ≤ r ^ 2 := Nat.le_self_pow (by norm_num) r
    by_contra hgt
    have hge : 3 * r + 1 ≤ sidonCount A (r ^ 2 + r) := by omega
    have hge1 : 3 * r ≤ sidonCount A (r ^ 2 + r) - 1 := by omega
    have hmul : (3 * r + 1) * (3 * r) ≤ sidonCount A (r ^ 2 + r) * (sidonCount A (r ^ 2 + r) - 1) :=
      Nat.mul_le_mul hge hge1
    nlinarith
  have hsq_decomp : ∀ j, (W j).card ^ 2 = 2 * (P j).card + (W j).card := by
    intro j
    let Q := (W j ×ˢ W j).filter (fun p => p.2 < p.1)
    have hdisj : Disjoint (P j) Q := by
      rw [Finset.disjoint_filter]
      intro p _ h1 h2
      omega
    have hunion : P j ∪ Q = (W j).offDiag := by
      ext ⟨a, b⟩
      simp only [P, Q, Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag]
      constructor
      · rintro (⟨⟨ha, hb⟩, hlt⟩ | ⟨⟨ha, hb⟩, hlt⟩)
        · exact ⟨ha, hb, ne_of_lt hlt⟩
        · exact ⟨ha, hb, ne_of_gt hlt⟩
      · rintro ⟨ha, hb, hne⟩
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact Or.inl ⟨⟨ha, hb⟩, hlt⟩
        · exact Or.inr ⟨⟨ha, hb⟩, hlt⟩
    have hPQ : (P j).card = Q.card := by
      refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
      · intro p hp
        simp only [P, Q, Finset.mem_filter, Finset.mem_product] at hp ⊢
        exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
      · intro p₁ _ p₂ _ h
        exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
      · intro q hq
        simp only [P, Q, Finset.mem_filter, Finset.mem_product] at hq ⊢
        exact ⟨(q.2, q.1), ⟨⟨hq.1.2, hq.1.1⟩, hq.2⟩, rfl⟩
    have hoff : (W j).offDiag.card = (W j).card * (W j).card - (W j).card := Finset.offDiag_card (W j)
    have hcard : (P j).card + Q.card = (W j).offDiag.card := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have hle : (W j).card ≤ (W j).card * (W j).card := Nat.le_mul_self _
    rw [sq]
    omega
  have hsum_eq : ∑ j ∈ Finset.Icc 1 (r ^ 2), (W j).card ^ 2 =
      2 * (∑ j ∈ Finset.Icc 1 (r ^ 2), (P j).card) +
        ∑ j ∈ Finset.Icc 1 (r ^ 2), (W j).card := by
    simp_rw [hsq_decomp, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsum_eq]
  have hlin' : ∑ j ∈ Finset.Icc 1 (r ^ 2), (W j).card ≤ 3 * r ^ 2 := by
    calc ∑ j ∈ Finset.Icc 1 (r ^ 2), (W j).card
        ≤ sidonCount A (r ^ 2 + r) * r := hlin_sum
      _ ≤ (3 * r) * r := Nat.mul_le_mul_right r hcnt
      _ = 3 * r ^ 2 := by ring
  omega

private lemma abel_sum (S b : ℕ → ℝ) (M N : ℕ) (hMN : M ≤ N) :
    ∑ k ∈ Finset.Ioc M N, (S k - S (k - 1)) * b k =
      S N * b N - S M * b M + ∑ k ∈ Finset.Ico M N, S k * (b k - b (k + 1)) := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ N hMN ih =>
    have hIoc : Finset.Ioc M (N + 1) = insert (N + 1) (Finset.Ioc M N) := by
      ext k
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      omega
    have hIco : Finset.Ico M (N + 1) = insert N (Finset.Ico M N) := by
      ext k
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    rw [hIoc, Finset.sum_insert (by simp), hIco, Finset.sum_insert (by simp), ih]
    simp only [Nat.add_sub_cancel]
    ring

private lemma harmonic_Ico_ge_log {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) :
    Real.log (N : ℝ) - Real.log (M : ℝ) ≤ ∑ k ∈ Finset.Ico M N, (1 / (k : ℝ)) := by
  have htel : ∑ k ∈ Finset.Ico M N, (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)) =
      Real.log (N : ℝ) - Real.log (M : ℝ) := by
    induction N, hMN using Nat.le_induction with
    | base => simp
    | succ N hMN ih =>
      have hIco : Finset.Ico M (N + 1) = insert N (Finset.Ico M N) := by
        ext k
        simp only [Finset.mem_Ico, Finset.mem_insert]
        omega
      rw [hIco, Finset.sum_insert (by simp), ih]
      ring
  rw [← htel]
  refine Finset.sum_le_sum fun k hk => ?_
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (by simp only [Finset.mem_Ico] at hk; omega)
  have h1 : Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) ≤ ((k + 1 : ℕ) : ℝ) / (k : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) hkpos.ne'] at h1
  have h2 : ((k + 1 : ℕ) : ℝ) / (k : ℝ) - 1 = 1 / (k : ℝ) := by
    push_cast
    field_simp
    ring
  linarith

private lemma harmonic_Icc_le_log {M N : ℕ} (hM : 2 ≤ M) (hMN : M ≤ N) :
    ∑ k ∈ Finset.Icc M N, (1 / (k : ℝ)) ≤ Real.log (N : ℝ) := by
  have htel : ∑ k ∈ Finset.Icc M N, (Real.log (k : ℝ) - Real.log ((k - 1 : ℕ) : ℝ)) =
      Real.log (N : ℝ) - Real.log ((M - 1 : ℕ) : ℝ) := by
    induction N, hMN using Nat.le_induction with
    | base => simp
    | succ N hMN ih =>
      have hIcc : Finset.Icc M (N + 1) = insert (N + 1) (Finset.Icc M N) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hIcc, Finset.sum_insert (by simp), ih]
      simp only [Nat.add_sub_cancel]
      ring
  have hstep : ∑ k ∈ Finset.Icc M N, (1 / (k : ℝ)) ≤
      ∑ k ∈ Finset.Icc M N, (Real.log (k : ℝ) - Real.log ((k - 1 : ℕ) : ℝ)) := by
    refine Finset.sum_le_sum fun k hk => ?_
    have hk2 : 2 ≤ k := by simp only [Finset.mem_Icc] at hk; omega
    have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
    have hk1pos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    have h1 := Real.log_le_sub_one_of_pos (div_pos hk1pos hkpos)
    rw [Real.log_div hk1pos.ne' hkpos.ne'] at h1
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    have h2 : ((k - 1 : ℕ) : ℝ) / (k : ℝ) - 1 = -(1 / (k : ℝ)) := by
      rw [hcast]
      field_simp
      ring
    linarith
  have hlog_nonneg : 0 ≤ Real.log ((M - 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ M - 1))
  linarith

private lemma inv_sqrt_sub_ge {k : ℕ} (hk : 1 ≤ k) :
    1 / (6 * (k : ℝ) * Real.sqrt k) ≤ 1 / Real.sqrt k - 1 / Real.sqrt (k + 1) := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hkpos
  have hsk1 : 0 < Real.sqrt (k + 1) := Real.sqrt_pos.mpr (by positivity)
  have hdiff : 1 / Real.sqrt k - 1 / Real.sqrt (k + 1) =
      1 / (Real.sqrt k * Real.sqrt (k + 1) * (Real.sqrt (k + 1) + Real.sqrt k)) := by
    have hsq : (Real.sqrt (k + 1) - Real.sqrt k) * (Real.sqrt (k + 1) + Real.sqrt k) = 1 := by
      have h1 : Real.sqrt (k + 1) ^ 2 = (k : ℝ) + 1 := Real.sq_sqrt (by positivity)
      have h2 : Real.sqrt k ^ 2 = (k : ℝ) := Real.sq_sqrt hkpos.le
      nlinarith
    have hsum_pos : 0 < Real.sqrt (k + 1) + Real.sqrt k := by positivity
    field_simp
    linarith
  rw [hdiff]
  apply one_div_le_one_div_of_le (by positivity)
  have hle : Real.sqrt (k + 1) ≤ 2 * Real.sqrt k := by
    have h1 : (k : ℝ) + 1 ≤ 4 * (k : ℝ) := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have h2 : Real.sqrt (k + 1) ^ 2 ≤ (2 * Real.sqrt k) ^ 2 := by
      rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt hkpos.le]
      linarith
    nlinarith
  have hsqk : Real.sqrt k * Real.sqrt k = (k : ℝ) := Real.mul_self_sqrt hkpos.le
  calc Real.sqrt k * Real.sqrt (k + 1) * (Real.sqrt (k + 1) + Real.sqrt k)
      ≤ Real.sqrt k * (2 * Real.sqrt k) * (2 * Real.sqrt k + Real.sqrt k) := by gcongr
    _ = 6 * (Real.sqrt k * Real.sqrt k) * Real.sqrt k := by ring
    _ = 6 * (k : ℝ) * Real.sqrt k := by rw [hsqk]

private lemma exists_sidonCount_le_halberstam_roth {A : Set ℕ} (hAsid : IsSidon A) (N₀ : ℕ) :
    ∃ x ≥ max N₀ 2, (sidonCount A x : ℝ) ≤ 120 * Real.sqrt x / Real.sqrt (Real.log x) := by
  by_contra hno
  push Not at hno
  let r : ℕ := max (max N₀ 4) (Nat.ceil (Real.exp 4) + 1)
  have hrN : N₀ ≤ r := le_trans (le_max_left _ _) (le_max_left _ _)
  have hr4 : 4 ≤ r := le_trans (le_max_right _ _) (le_max_left _ _)
  have hr1 : 1 ≤ r := by omega
  have hr2 : 2 ≤ r := by omega
  have hrexp : Real.exp 4 < (r : ℝ) := by
    have h1 : Real.exp 4 ≤ (Nat.ceil (Real.exp 4) : ℝ) := Nat.le_ceil _
    have h2 : Nat.ceil (Real.exp 4) + 1 ≤ r := le_max_right _ _
    have h2' : (Nat.ceil (Real.exp 4) : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast h2
    linarith
  have hlogr_gt : 4 < Real.log (r : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos 4) hrexp
    rw [Real.log_exp] at h
    exact h
  have hlogr_pos : 0 < Real.log (r : ℝ) := by linarith
  have hslogr_gt : 2 < Real.sqrt (Real.log (r : ℝ)) := by
    have h : (2 : ℝ) ^ 2 < Real.sqrt (Real.log (r : ℝ)) ^ 2 := by
      rw [Real.sq_sqrt hlogr_pos.le]
      linarith
    nlinarith [Real.sqrt_nonneg (Real.log (r : ℝ))]
  have h2r_le_r2 : 2 * r ≤ r ^ 2 := by nlinarith
  let W : ℕ → Finset ℕ := fun j => (Finset.Ioc j (j + r)).filter (· ∈ A)
  have hsum_swap : (r : ℝ) * ∑ a ∈ (Finset.Ioc (2 * r) (r ^ 2)).filter (· ∈ A),
        (1 / Real.sqrt a) ≤
      ∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) / Real.sqrt j := by
    have h1 : ∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) / Real.sqrt j =
        ∑ j ∈ Finset.Icc r (r ^ 2), ∑ a ∈ W j, (1 / Real.sqrt j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [div_eq_mul_inv]
    rw [h1]
    have h2 : ∑ j ∈ Finset.Icc r (r ^ 2), ∑ a ∈ W j, (1 / Real.sqrt j) ≥
        ∑ j ∈ Finset.Icc r (r ^ 2),
          ∑ a ∈ (Finset.Ioc (2 * r) (r ^ 2)).filter (· ∈ A),
            (if a ∈ W j then 1 / Real.sqrt j else 0) := by
      refine Finset.sum_le_sum fun j _ => ?_
      rw [← Finset.sum_filter]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
      intro a ha
      exact (Finset.mem_filter.mp ha).2
    rw [Finset.sum_comm] at h2
    refine le_trans ?_ h2
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a ha => ?_
    simp only [Finset.mem_filter, Finset.mem_Ioc] at ha
    have hsub : Finset.Ico (a - r) a ⊆ (Finset.Icc r (r ^ 2)).filter (fun j => a ∈ W j) := by
      intro j hj
      simp only [Finset.mem_Ico] at hj
      simp only [Finset.mem_filter, Finset.mem_Icc, W, Finset.mem_Ioc]
      exact ⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, ha.2⟩⟩
    calc (r : ℝ) * (1 / Real.sqrt a)
        = ∑ _j ∈ Finset.Ico (a - r) a, (1 / Real.sqrt a) := by
          rw [Finset.sum_const, Nat.card_Ico, show a - (a - r) = r by omega, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.Ico (a - r) a, (1 / Real.sqrt j) := by
          refine Finset.sum_le_sum fun j hj => ?_
          simp only [Finset.mem_Ico] at hj
          have hjpos : (0 : ℝ) < j := Nat.cast_pos.mpr (by omega)
          exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hjpos)
            (Real.sqrt_le_sqrt (by exact_mod_cast hj.2.le))
      _ ≤ ∑ j ∈ (Finset.Icc r (r ^ 2)).filter (fun j => a ∈ W j), (1 / Real.sqrt j) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = ∑ j ∈ Finset.Icc r (r ^ 2), if a ∈ W j then 1 / Real.sqrt j else 0 := by
          rw [Finset.sum_filter]
  have habel_step : 4 * Real.sqrt 2 * Real.sqrt (Real.log (r : ℝ)) ≤
      ∑ a ∈ (Finset.Ioc (2 * r) (r ^ 2)).filter (· ∈ A), (1 / Real.sqrt a) := by
    have hrew : ∑ a ∈ (Finset.Ioc (2 * r) (r ^ 2)).filter (· ∈ A), (1 / Real.sqrt a) =
        ∑ k ∈ Finset.Ioc (2 * r) (r ^ 2),
          ((sidonCount A k : ℝ) - (sidonCount A (k - 1) : ℝ)) * (1 / Real.sqrt k) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk1 : 1 ≤ k := by simp only [Finset.mem_Ioc] at hk; omega
      have hIcc : Finset.Icc 1 k = insert k (Finset.Icc 1 (k - 1)) := by
        ext m
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      by_cases hkA : k ∈ A
      · have hcard : sidonCount A k = sidonCount A (k - 1) + 1 := by
          unfold sidonCount
          rw [hIcc, Finset.filter_insert, if_pos hkA, Finset.card_insert_of_notMem]
          simp
          omega
        rw [if_pos hkA, hcard]
        push_cast
        ring
      · have hcard : sidonCount A k = sidonCount A (k - 1) := by
          unfold sidonCount
          rw [hIcc, Finset.filter_insert, if_neg hkA]
        rw [if_neg hkA, hcard]
        ring
    rw [hrew, abel_sum (fun k => (sidonCount A k : ℝ)) (fun k => 1 / Real.sqrt k)
      (2 * r) (r ^ 2) h2r_le_r2]
    have htail : 0 ≤ (sidonCount A (r ^ 2) : ℝ) * (1 / Real.sqrt (r ^ 2)) := by positivity
    have hhead : (sidonCount A (2 * r) : ℝ) * (1 / Real.sqrt (2 * r)) ≤ 2 := by
      have h1 := sidonCount_le_two_sqrt hAsid (by omega : 1 ≤ 2 * r)
      have hspos : 0 < Real.sqrt (2 * r : ℕ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
      have hcast : ((2 * r : ℕ) : ℝ) = 2 * (r : ℝ) := by push_cast; ring
      rw [hcast] at h1 hspos
      calc (sidonCount A (2 * r) : ℝ) * (1 / Real.sqrt (2 * (r : ℝ)))
          ≤ (2 * Real.sqrt (2 * (r : ℝ))) * (1 / Real.sqrt (2 * (r : ℝ))) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = 2 := by field_simp
    have hmain_sum : 5 * Real.sqrt 2 * Real.sqrt (Real.log (r : ℝ)) ≤
        ∑ k ∈ Finset.Ico (2 * r) (r ^ 2),
          (sidonCount A k : ℝ) * (1 / Real.sqrt k - 1 / Real.sqrt ((k + 1 : ℕ) : ℝ)) := by
      have hterm : ∀ k ∈ Finset.Ico (2 * r) (r ^ 2),
          (20 / (Real.sqrt 2 * Real.sqrt (Real.log (r : ℝ)))) * (1 / (k : ℝ)) ≤
            (sidonCount A k : ℝ) * (1 / Real.sqrt k - 1 / Real.sqrt ((k + 1 : ℕ) : ℝ)) := by
        intro k hk
        simp only [Finset.mem_Ico] at hk
        have hkN : max N₀ 2 ≤ k := by omega
        have hk1 : 1 ≤ k := by omega
        have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk1
        have hcnt := hno k hkN
        have hlogk_pos : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
        have hlogk_le : Real.log (k : ℝ) ≤ 2 * Real.log (r : ℝ) := by
          have h1 : Real.log (k : ℝ) ≤ Real.log ((r : ℝ) ^ 2) :=
            Real.log_le_log hkpos (by exact_mod_cast hk.2.le)
          rwa [Real.log_pow, Nat.cast_ofNat] at h1
        have hslog_le : Real.sqrt (Real.log (k : ℝ)) ≤ Real.sqrt 2 * Real.sqrt (Real.log (r : ℝ)) := by
          rw [← Real.sqrt_mul (by norm_num)]
          exact Real.sqrt_le_sqrt hlogk_le
        have hcnt' : 120 * Real.sqrt k / (Real.sqrt 2 * Real.sqrt (Real.log (r : ℝ))) ≤
            (sidonCount A k : ℝ) := by
          refine le_trans ?_ hcnt.le
          exact div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hlogk_pos) hslog_le
        have hinv := inv_sqrt_sub_ge hk1
        push_cast at hinv ⊢
        have hmul := mul_le_mul hcnt' hinv (by positivity) (Nat.cast_nonneg _)
        have hsimpl : 120 * Real.sqrt k / (Real.sqrt 2 * Real.sqrt (Real.log (r : ℝ))) *
            (1 / (6 * (k : ℝ) * Real.sqrt k)) =
            20 / (Real.sqrt 2 * Real.sqrt (Real.log (r : ℝ))) * (1 / (k : ℝ)) := by
          have hsk : Real.sqrt k ≠ 0 := (Real.sqrt_pos.mpr hkpos).ne'
          field_simp
          ring
        linarith
      have hsum1 : (20 / (Real.sqrt 2 * Real.sqrt (Real.log (r : ℝ)))) *
            (∑ k ∈ Finset.Ico (2 * r) (r ^ 2), (1 / (k : ℝ))) ≤
          ∑ k ∈ Finset.Ico (2 * r) (r ^ 2),
            (sidonCount A k : ℝ) * (1 / Real.sqrt k - 1 / Real.sqrt ((k + 1 : ℕ) : ℝ)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum hterm
      have hharm : (1 / 2) * Real.log (r : ℝ) ≤
          ∑ k ∈ Finset.Ico (2 * r) (r ^ 2), (1 / (k : ℝ)) := by
        have h1 := harmonic_Ico_ge_log (by omega : 1 ≤ 2 * r) h2r_le_r2
        have hrpos : (0 : ℝ) < r := Nat.cast_pos.mpr hr1
        have hlog_eq : Real.log ((r ^ 2 : ℕ) : ℝ) - Real.log ((2 * r : ℕ) : ℝ) =
            Real.log ((r : ℝ) / 2) := by
          push_cast
          rw [← Real.log_div (by positivity) (by positivity)]
          congr 1
          field_simp
        have hhalf : Real.sqrt r ≤ (r : ℝ) / 2 := by
          have hr4R : (4 : ℝ) ≤ r := by exact_mod_cast hr4
          have hsq : Real.sqrt r ^ 2 ≤ ((r : ℝ) / 2) ^ 2 := by
            rw [Real.sq_sqrt hrpos.le]
            nlinarith
          nlinarith [Real.sqrt_nonneg r]
        have hlog_ge : (1 / 2) * Real.log (r : ℝ) ≤ Real.log ((r : ℝ) / 2) := by
          have h2 := Real.log_le_log (Real.sqrt_pos.mpr hrpos) hhalf
          rw [Real.log_sqrt hrpos.le] at h2
          linarith
        linarith
      have hmul2 : (20 / (Real.sqrt 2 * Real.sqrt (Real.log (r : ℝ)))) *
            ((1 / 2) * Real.log (r : ℝ)) = 5 * Real.sqrt 2 * Real.sqrt (Real.log (r : ℝ)) := by
        have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        have hsl : Real.sqrt (Real.log (r : ℝ)) ^ 2 = Real.log (r : ℝ) :=
          Real.sq_sqrt hlogr_pos.le
        have hs2_ne : Real.sqrt 2 ≠ 0 := by positivity
        have hsl_ne : Real.sqrt (Real.log (r : ℝ)) ≠ 0 := by positivity
        field_simp
        nlinarith
      have hmul_le := mul_le_mul_of_nonneg_left hharm
        (by positivity : 0 ≤ 20 / (Real.sqrt 2 * Real.sqrt (Real.log (r : ℝ))))
      linarith
    have h2lt : (2 : ℝ) ≤ Real.sqrt 2 * Real.sqrt (Real.log (r : ℝ)) := by
      have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
        have : (1 : ℝ) ^ 2 ≤ Real.sqrt 2 ^ 2 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
        nlinarith [Real.sqrt_nonneg 2]
      nlinarith
    have hcast2r : ((2 * r : ℕ) : ℝ) = 2 * (r : ℝ) := by push_cast; ring
    have hcastr2 : ((r ^ 2 : ℕ) : ℝ) = (r : ℝ) ^ 2 := by push_cast; ring
    rw [hcast2r, hcastr2] at *
    linarith
  have hL : 4 * Real.sqrt 2 * (r : ℝ) * Real.sqrt (Real.log (r : ℝ)) ≤
      ∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) / Real.sqrt j := by
    have h1 := mul_le_mul_of_nonneg_left habel_step (Nat.cast_nonneg r)
    linarith
  have hCS : (∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) / Real.sqrt j) ^ 2 ≤
      (∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) ^ 2) *
        (∑ j ∈ Finset.Icc r (r ^ 2), (1 / (j : ℝ))) := by
    have hraw := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc r (r ^ 2))
      (fun j => ((W j).card : ℝ)) (fun j => 1 / Real.sqrt j)
    have hlhs : ∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) * (1 / Real.sqrt j) =
        ∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) / Real.sqrt j :=
      Finset.sum_congr rfl fun j _ => by ring
    have hrhs : ∑ j ∈ Finset.Icc r (r ^ 2), (1 / Real.sqrt j) ^ 2 =
        ∑ j ∈ Finset.Icc r (r ^ 2), (1 / (j : ℝ)) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg j)]
    rw [hlhs, hrhs] at hraw
    exact hraw
  have hsum_sq : ∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) ^ 2 ≤ 5 * (r : ℝ) ^ 2 := by
    have hsub : Finset.Icc r (r ^ 2) ⊆ Finset.Icc 1 (r ^ 2) :=
      Finset.Icc_subset_Icc hr1 le_rfl
    have h1 : ∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) ^ 2 ≤
        ∑ j ∈ Finset.Icc 1 (r ^ 2), ((W j).card : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    have h2 : ∑ j ∈ Finset.Icc 1 (r ^ 2), ((W j).card : ℝ) ^ 2 ≤ 5 * (r : ℝ) ^ 2 := by
      exact_mod_cast sidon_window_sq_sum_le hAsid hr1
    exact h1.trans h2
  have hsum_harm : ∑ j ∈ Finset.Icc r (r ^ 2), (1 / (j : ℝ)) ≤ 2 * Real.log (r : ℝ) := by
    have h1 := harmonic_Icc_le_log hr2 (Nat.le_self_pow (by norm_num : 2 ≠ 0) r)
    push_cast at h1
    rw [Real.log_pow, Nat.cast_ofNat] at h1
    exact h1
  have hLHS_sq : 32 * (r : ℝ) ^ 2 * Real.log (r : ℝ) ≤
      (∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) / Real.sqrt j) ^ 2 := by
    have h1 : (4 * Real.sqrt 2 * (r : ℝ) * Real.sqrt (Real.log (r : ℝ))) ^ 2 ≤
        (∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) / Real.sqrt j) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hL 2
    have h2 : (4 * Real.sqrt 2 * (r : ℝ) * Real.sqrt (Real.log (r : ℝ))) ^ 2 =
        32 * (r : ℝ) ^ 2 * Real.log (r : ℝ) := by
      have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hsl : Real.sqrt (Real.log (r : ℝ)) ^ 2 = Real.log (r : ℝ) :=
        Real.sq_sqrt hlogr_pos.le
      calc (4 * Real.sqrt 2 * (r : ℝ) * Real.sqrt (Real.log (r : ℝ))) ^ 2
          = 16 * Real.sqrt 2 ^ 2 * (r : ℝ) ^ 2 * Real.sqrt (Real.log (r : ℝ)) ^ 2 := by ring
        _ = 32 * (r : ℝ) ^ 2 * Real.log (r : ℝ) := by rw [hs2, hsl]; ring
    linarith
  have hRHS_le : (∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) ^ 2) *
        (∑ j ∈ Finset.Icc r (r ^ 2), (1 / (j : ℝ))) ≤
      10 * (r : ℝ) ^ 2 * Real.log (r : ℝ) := by
    have h1 := mul_le_mul hsum_sq hsum_harm
      (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
    linarith
  have hr2log_pos : 0 < (r : ℝ) ^ 2 * Real.log (r : ℝ) := by
    have hrpos : (0 : ℝ) < r := Nat.cast_pos.mpr hr1
    positivity
  linarith

theorem OMA.solution : type_of% @Erdos41.erdos_41.variants.pairwise := by
  intro A hA₂ _
  have hAsid : IsSidon A := isSidon_of_ntupleCondition_two hA₂
  let u : ℕ → ℝ := fun N => ((A ∩ Set.Icc 1 N).ncard : ℝ) / Real.sqrt N
  have hu_nonneg : ∀ N : ℕ, 0 ≤ u N := fun N => by positivity
  have hu_le_two : ∀ N : ℕ, u N ≤ 2 := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [u]
    · dsimp only [u]
      rw [← sidonCount_eq_ncard, div_le_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN))]
      exact sidonCount_le_two_sqrt hAsid hN
  have hbdd : Filter.atTop.IsBoundedUnder (· ≥ ·) u :=
    ⟨0, Filter.eventually_map.mpr (Eventually.of_forall hu_nonneg)⟩
  have hcobdd : Filter.atTop.IsCoboundedUnder (· ≥ ·) u := by
    refine ⟨2, fun a ha => ?_⟩
    rw [Filter.eventually_map] at ha
    obtain ⟨N, hN⟩ := ha.exists
    exact le_trans hN (hu_le_two N)
  apply le_antisymm
  · refine Filter.liminf_le_of_le hbdd fun b hb => ?_
    by_contra hpos
    push Not at hpos
    rw [Filter.eventually_atTop] at hb
    obtain ⟨N₁, hN₁⟩ := hb
    let N₀ : ℕ := max N₁ (Nat.ceil (Real.exp ((120 / b) ^ 2)) + 1)
    obtain ⟨x, hx, hcnt⟩ := exists_sidonCount_le_halberstam_roth hAsid N₀
    have hxN₁ : N₁ ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx)
    have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
    have hx_exp : Real.exp ((120 / b) ^ 2) < (x : ℝ) := by
      have h1 : Real.exp ((120 / b) ^ 2) ≤ (Nat.ceil (Real.exp ((120 / b) ^ 2)) : ℝ) :=
        Nat.le_ceil _
      have h2 : Nat.ceil (Real.exp ((120 / b) ^ 2)) + 1 ≤ x :=
        le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx)
      have h2' : (Nat.ceil (Real.exp ((120 / b) ^ 2)) : ℝ) + 1 ≤ (x : ℝ) := by exact_mod_cast h2
      linarith
    have hlogx : (120 / b) ^ 2 < Real.log (x : ℝ) := by
      have h := Real.log_lt_log (Real.exp_pos _) hx_exp
      rw [Real.log_exp] at h
      exact h
    have hlogx_pos : 0 < Real.log (x : ℝ) := lt_trans (by positivity) hlogx
    have hslogx : 120 / b < Real.sqrt (Real.log (x : ℝ)) := by
      have hsq : (120 / b) ^ 2 < Real.sqrt (Real.log (x : ℝ)) ^ 2 := by
        rw [Real.sq_sqrt hlogx_pos.le]
        exact hlogx
      nlinarith [Real.sqrt_nonneg (Real.log (x : ℝ))]
    have hdiv_lt : 120 / Real.sqrt (Real.log (x : ℝ)) < b := by
      rw [div_lt_iff₀ (Real.sqrt_pos.mpr hlogx_pos)]
      have h1 := (div_lt_iff₀ hpos).mp hslogx
      linarith
    have hux : u x ≤ 120 / Real.sqrt (Real.log (x : ℝ)) := by
      dsimp only [u]
      rw [← sidonCount_eq_ncard]
      have hsx : 0 < Real.sqrt (x : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
      rw [div_le_iff₀ hsx]
      have heq : 120 / Real.sqrt (Real.log (x : ℝ)) * Real.sqrt x =
          120 * Real.sqrt x / Real.sqrt (Real.log (x : ℝ)) := by ring
      linarith
    have hb_le : b ≤ u x := hN₁ x hxN₁
    linarith
  · exact Filter.le_liminf_of_le hcobdd (Eventually.of_forall hu_nonneg)
