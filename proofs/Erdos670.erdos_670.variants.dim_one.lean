import FormalConjectures.ErdosProblems.«670»

-- Problem: Erdős Problem 670 — dim one
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/670.lean:66 (declaration Erdos670.erdos_670.variants.dim_one)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter

namespace OMAProof670

/-- A finite set of nonnegative reals that are pairwise at distance at least `1` has sum at least
`c (c - 1) / 2`, where `c` is its cardinality. -/
lemma sep_sum (T : Finset ℝ) (h0 : ∀ t ∈ T, 0 ≤ t)
    (hsep : ∀ s ∈ T, ∀ t ∈ T, s ≠ t → 1 ≤ |s - t|) :
    (T.card : ℝ) * ((T.card : ℝ) - 1) / 2 ≤ ∑ t ∈ T, t ∧
      (T = ∅ ∨ ∃ m ∈ T, (T.card : ℝ) - 1 ≤ m) := by
  induction T using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have h0s : ∀ t ∈ s, 0 ≤ t := fun t ht => h0 t (Finset.mem_insert_of_mem ht)
    have hseps : ∀ u ∈ s, ∀ t ∈ s, u ≠ t → 1 ≤ |u - t| := fun u hu t ht hne =>
      hsep u (Finset.mem_insert_of_mem hu) t (Finset.mem_insert_of_mem ht) hne
    obtain ⟨ih1, ih2⟩ := ih h0s hseps
    have ha : (s.card : ℝ) ≤ a := by
      rcases ih2 with rfl | ⟨m, hm, hmc⟩
      · simpa using h0 a (Finset.mem_insert_self a _)
      · have h1 := hsep a (Finset.mem_insert_self a _) m (Finset.mem_insert_of_mem hm)
          (fun h => has (h ▸ hm))
        have h2 := hlt m hm
        rw [abs_of_pos (by linarith)] at h1
        linarith
    rw [Finset.card_insert_of_notMem has, Finset.sum_insert has]
    push_cast
    refine ⟨by nlinarith, Or.inr ⟨a, Finset.mem_insert_self a _, by linarith⟩⟩

lemma gauss (K : ℕ) : (∑ k ∈ Finset.Icc 1 K, (k : ℝ)) * 2 = K * (K + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), add_mul, ih]
    push_cast
    ring

/-- The window sum: `∑_{i < n - k} (x (i + k) - x i) ≤ k (x (n-1) - x 0)`. -/
lemma window (n k : ℕ) (hk : k < n) (x : ℕ → ℝ)
    (hmono : ∀ i j, i ≤ j → j < n → x i ≤ x j) :
    ∑ i ∈ Finset.range (n - k), (x (i + k) - x i) ≤ k * (x (n - 1) - x 0) := by
  have e1 := Finset.sum_range_add x k (n - k)
  have e2 := Finset.sum_range_add x (n - k) k
  rw [show k + (n - k) = n by omega] at e1
  rw [show n - k + k = n by omega] at e2
  have hsum : ∑ i ∈ Finset.range (n - k), (x (i + k) - x i) =
      ∑ i ∈ Finset.range k, x (n - k + i) - ∑ i ∈ Finset.range k, x i := by
    rw [Finset.sum_sub_distrib]
    have : ∑ i ∈ Finset.range (n - k), x (i + k) = ∑ i ∈ Finset.range (n - k), x (k + i) := by
      refine Finset.sum_congr rfl fun i _ => by rw [add_comm]
    linarith
  rw [hsum]
  have hup : ∑ i ∈ Finset.range k, x (n - k + i) ≤ ∑ i ∈ Finset.range k, x (n - 1) :=
    Finset.sum_le_sum fun i hi => hmono _ _ (by simp at hi; omega) (by omega)
  have hlo : ∑ i ∈ Finset.range k, x 0 ≤ ∑ i ∈ Finset.range k, x i :=
    Finset.sum_le_sum fun i hi => hmono _ _ (by omega) (by simp at hi; omega)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hup hlo
  nlinarith

lemma core (n K : ℕ) (x : ℕ → ℝ) (hK : 1 ≤ K) (hKn : K < n)
    (hmono : ∀ i j, i < j → j < n → x i < x j)
    (hsep : ∀ i j k l, i < j → j < n → k < l → l < n → (i ≠ k ∨ j ≠ l) →
      1 ≤ |(x j - x i) - (x l - x k)|) :
    ((K : ℝ) * n - K ^ 2) * ((K : ℝ) * n - K ^ 2 - 1) ≤ K * (K + 1) * (x (n - 1) - x 0) := by
  have hmono' : ∀ i j, i ≤ j → j < n → x i ≤ x j := fun i j hij hj => by
    rcases hij.lt_or_eq with h | rfl
    · exact (hmono i j h hj).le
    · exact le_rfl
  set P := (Finset.Icc 1 K).sigma (fun k => Finset.range (n - k)) with hP
  let g : (Σ _ : ℕ, ℕ) → ℝ := fun p => x (p.2 + p.1) - x p.2
  have memP : ∀ p ∈ P, 1 ≤ p.1 ∧ p.1 ≤ K ∧ p.2 + p.1 < n := by
    rintro ⟨k, i⟩ hp
    simp only [hP, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_range] at hp
    show 1 ≤ k ∧ k ≤ K ∧ i + k < n
    exact ⟨hp.1.1, hp.1.2, by omega⟩
  have hinj : Set.InjOn g P := by
    rintro ⟨k, i⟩ hp ⟨k', i'⟩ hq hpq
    obtain ⟨h1, h2, h3⟩ := memP _ hp
    obtain ⟨h1', h2', h3'⟩ := memP _ hq
    dsimp only at h1 h2 h3 h1' h2' h3'
    by_contra hne
    have hor : i ≠ i' ∨ i + k ≠ i' + k' := by
      by_contra hc
      push Not at hc
      apply hne
      have : k = k' := by omega
      rw [hc.1, this]
    have := hsep i (i + k) i' (i' + k') (by omega) h3 (by omega) h3' hor
    simp only [g] at hpq
    rw [hpq, sub_self, abs_zero] at this
    linarith
  set T := P.image g with hT
  have hcardT : T.card = ∑ k ∈ Finset.Icc 1 K, (n - k) := by
    rw [hT, Finset.card_image_of_injOn hinj, hP, Finset.card_sigma]
    simp
  have hcardT' : (K : ℝ) * n - K ^ 2 ≤ T.card := by
    have : K * (n - K) ≤ T.card := by
      rw [hcardT]
      calc K * (n - K) = ∑ k ∈ Finset.Icc 1 K, (n - K) := by simp
        _ ≤ _ := Finset.sum_le_sum fun k hk => by simp at hk; omega
    have h2 : ((K * (n - K) : ℕ) : ℝ) = K * n - K ^ 2 := by
      rw [Nat.cast_mul, Nat.cast_sub hKn.le]; ring
    rw [← h2]; exact_mod_cast this
  have h0 : ∀ t ∈ T, 0 ≤ t := by
    intro t ht
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨h1, -, h3⟩ := memP p hp
    have := hmono p.2 (p.2 + p.1) (by omega) h3
    simp only [g]; linarith
  have hsepT : ∀ s ∈ T, ∀ t ∈ T, s ≠ t → 1 ≤ |s - t| := by
    intro s hs t ht hst
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨h1, -, h3⟩ := memP p hp
    obtain ⟨h1', -, h3'⟩ := memP q hq
    have hor : p.2 ≠ q.2 ∨ p.2 + p.1 ≠ q.2 + q.1 := by
      by_contra hc
      push Not at hc
      apply hst
      simp only [g]
      rw [hc.2, hc.1]
    exact hsep _ _ _ _ (by omega) h3 (by omega) h3' hor
  obtain ⟨hs, -⟩ := sep_sum T h0 hsepT
  have hsumT : ∑ t ∈ T, t ≤ (x (n - 1) - x 0) * (K * (K + 1) / 2) := by
    rw [hT, Finset.sum_image hinj, hP, Finset.sum_sigma]
    calc ∑ k ∈ Finset.Icc 1 K, ∑ i ∈ Finset.range (n - k), g ⟨k, i⟩
        ≤ ∑ k ∈ Finset.Icc 1 K, (k : ℝ) * (x (n - 1) - x 0) :=
          Finset.sum_le_sum fun k hk => by
            simp only [Finset.mem_Icc] at hk
            exact window n k (by omega) x hmono'
      _ = (x (n - 1) - x 0) * (K * (K + 1) / 2) := by
          rw [← Finset.sum_mul, mul_comm]
          have := gauss K
          congr 1
          linarith
  have hL1 : (1 : ℝ) ≤ K * n - K ^ 2 := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have : (K : ℝ) + 1 ≤ n := by exact_mod_cast hKn
    nlinarith
  nlinarith

lemma dist_eq1 (p q : EuclideanSpace ℝ (Fin 1)) : dist p q = |p 0 - q 0| := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_one, Real.sqrt_sq_eq_abs, Real.dist_eq, abs_abs]

lemma final_arith (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (K n D : ℝ) (hK : 1 ≤ K)
    (hKε : 2 ≤ ε * K) (hn : 4 * (K ^ 2 + 1) ≤ n * K * ε) (hn0 : 0 ≤ n)
    (hcore : (K * n - K ^ 2) * (K * n - K ^ 2 - 1) ≤ K * (K + 1) * D) :
    (1 - ε) * n ^ 2 ≤ D := by
  have hL : K * n * (1 - ε / 4) ≤ K * n - K ^ 2 - 1 := by nlinarith
  have hL0 : 0 ≤ K * n * (1 - ε / 4) := by
    apply mul_nonneg (mul_nonneg (by linarith) hn0); linarith
  have h1 : (K * n * (1 - ε / 4)) ^ 2 ≤ (K * n - K ^ 2) * (K * n - K ^ 2 - 1) := by
    have := mul_le_mul hL hL hL0 (by linarith)
    nlinarith
  have h2 : K ^ 2 * n ^ 2 * (1 - ε / 2) ≤ (K * n * (1 - ε / 4)) ^ 2 := by
    have : 0 ≤ K ^ 2 * n ^ 2 * (ε ^ 2 / 16) := by positivity
    nlinarith
  have h3 : K * (K + 1) * (1 - ε) ≤ K ^ 2 * (1 - ε / 2) := by nlinarith
  have h4 : (1 - ε) * n ^ 2 * (K * (K + 1)) ≤ K * (K + 1) * D := by
    have : 0 ≤ n ^ 2 := sq_nonneg n
    nlinarith
  have hKK : 0 < K * (K + 1) := by positivity
  nlinarith

end OMAProof670

open OMAProof670 in
theorem OMA.solution : type_of% @Erdos670.erdos_670.variants.dim_one := by
  intro ε hε
  rcases le_or_gt 1 ε with hε1 | hε1
  · refine Filter.Eventually.of_forall fun n A _ _ => ?_
    have : (1 - ε) * (n : ℝ) ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
    exact this.trans Metric.diam_nonneg
  set K : ℕ := Nat.ceil (2 / ε) + 1 with hKdef
  have hK1 : (1 : ℝ) ≤ K := by
    have : 1 ≤ K := by omega
    exact_mod_cast this
  have hKε : 2 ≤ ε * K := by
    have h1 : 2 / ε ≤ (Nat.ceil (2 / ε) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (2 / ε) : ℕ) : ℝ) ≤ K := by rw [hKdef]; push_cast; linarith
    have : 2 / ε ≤ K := h1.trans h2
    rw [div_le_iff₀ hε] at this
    linarith
  set N0 : ℕ := Nat.ceil (4 * ((K : ℝ) ^ 2 + 1) / (K * ε)) + K + 1 with hN0
  filter_upwards [eventually_ge_atTop N0] with n hn A hA hsepA
  have hKn : K < n := by omega
  have hnK : 4 * ((K : ℝ) ^ 2 + 1) ≤ n * K * ε := by
    have h1 : 4 * ((K : ℝ) ^ 2 + 1) / (K * ε) ≤ (Nat.ceil (4 * ((K : ℝ) ^ 2 + 1) / (K * ε)) : ℝ) :=
      Nat.le_ceil _
    have h2 : (Nat.ceil (4 * ((K : ℝ) ^ 2 + 1) / (K * ε)) : ℝ) ≤ n := by
      have : Nat.ceil (4 * ((K : ℝ) ^ 2 + 1) / (K * ε)) ≤ n := by omega
      exact_mod_cast this
    have := h1.trans h2
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  -- pass to real numbers
  let f : EuclideanSpace ℝ (Fin 1) → ℝ := fun p => p 0
  have finj : Function.Injective f := by
    intro p q h
    ext i
    fin_cases i
    exact h
  set B := A.image f with hB
  have hBcard : B.card = n := by rw [hB, Finset.card_image_of_injective _ finj, hA]
  let emb := B.orderEmbOfFin hBcard
  let x : ℕ → ℝ := fun i => if h : i < n then emb ⟨i, h⟩ else 0
  have hx : ∀ i (h : i < n), x i = emb ⟨i, h⟩ := fun i h => by simp only [x, dif_pos h]
  have hmono : ∀ i j, i < j → j < n → x i < x j := by
    intro i j hij hj
    rw [hx i (by omega), hx j hj]
    exact emb.strictMono (Fin.mk_lt_mk.mpr hij)
  have xinj : ∀ i j, i < n → j < n → x i = x j → i = j := by
    intro i j hi hj h
    rcases lt_trichotomy i j with h' | h' | h'
    · exact absurd h (hmono i j h' hj).ne
    · exact h'
    · exact absurd h (hmono j i h' hi).ne'
  have hPex : ∀ i, i < n → ∃ p ∈ A, f p = x i := by
    intro i hi
    have : emb ⟨i, hi⟩ ∈ B := Finset.orderEmbOfFin_mem B hBcard _
    rw [hB, Finset.mem_image] at this
    obtain ⟨p, hp, hpf⟩ := this
    exact ⟨p, hp, by rw [hpf, hx i hi]⟩
  choose P hPA hPf using hPex
  have hdist : ∀ i j (hi : i < n) (hj : j < n), dist (P i hi) (P j hj) = |x i - x j| := by
    intro i j hi hj
    rw [dist_eq1]
    have h1 := hPf i hi
    have h2 := hPf j hj
    simp only [f] at h1 h2
    rw [h1, h2]
  have hsep : ∀ i j k l, i < j → j < n → k < l → l < n → (i ≠ k ∨ j ≠ l) →
      1 ≤ |(x j - x i) - (x l - x k)| := by
    intro i j k l hij hj hkl hl hor
    have hi : i < n := by omega
    have hk : k < n := by omega
    have hab : P j hj ≠ P i hi := by
      intro h
      have := congrArg f h
      rw [hPf, hPf] at this
      exact absurd (xinj _ _ hj hi this) (by omega)
    have hce : P l hl ≠ P k hk := by
      intro h
      have := congrArg f h
      rw [hPf, hPf] at this
      exact absurd (xinj _ _ hl hk this) (by omega)
    have hs : s(P j hj, P i hi) ≠ s(P l hl, P k hk) := by
      intro h
      rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have e1 := congrArg f h1
        have e2 := congrArg f h2
        rw [hPf, hPf] at e1 e2
        have := xinj _ _ hj hl e1
        have := xinj _ _ hi hk e2
        omega
      · have e1 := congrArg f h1
        have e2 := congrArg f h2
        rw [hPf, hPf] at e1 e2
        have := xinj _ _ hj hk e1
        have := xinj _ _ hi hl e2
        omega
    have := hsepA _ (hPA j hj) _ (hPA i hi) _ (hPA l hl) _ (hPA k hk) hab hce hs
    rw [hdist, hdist, abs_of_pos (sub_pos.mpr (hmono i j hij hj)),
      abs_of_pos (sub_pos.mpr (hmono k l hkl hl))] at this
    exact this
  have hcore := core n K x (by omega) hKn hmono hsep
  have hn1 : n - 1 < n := by omega
  have hn0 : 0 < n := by omega
  have hdiam : x (n - 1) - x 0 ≤ Metric.diam (A : Set (EuclideanSpace ℝ (Fin 1))) := by
    have := Metric.dist_le_diam_of_mem (A.finite_toSet.isBounded)
      (hPA (n - 1) hn1) (hPA 0 hn0)
    rw [hdist] at this
    exact (le_abs_self _).trans this
  have hfin := final_arith ε hε hε1 K n (x (n - 1) - x 0) hK1 hKε hnK (by positivity) hcore
  exact hfin.trans hdiam
