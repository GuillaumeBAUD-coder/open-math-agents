import FormalConjectures.ErdosProblems.«1213»

-- Problem: Erdős Problem 1213 — hegyvari
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1213.lean (declaration Erdos1213.erdos_1213.variants.hegyvari)
-- Credit: @NoahPuckett-IO (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Write `P n = A 0 + ⋯ + A (n - 1)`, so the interval `[u, u + L)` has sum `P (u + L) - P u`.
Take `M = ⌈e^(K+2)⌉` and `Y = M (a + K M)`, and assume `A (s - 1) > 2Y`.

For a fixed length `L ≤ M` the window sums `j ↦ P (j + L) - P j` increase in steps of at most
`K L`, start at most `Y` and end above `2Y`, so at least `Y / (K L) - 1` of them lie in
`(Y, 2Y]`. Over all `L ≤ M` that is more than `(Y / K) log (M + 1) - M ≥ Y + 2Y / K - M > Y`
windows, while `(Y, 2Y]` has only `Y` values. So two different windows have the same sum.
-/

namespace OMA.E1213

open Finset

/-- An increasing sequence with steps at most `D` that starts at most `Y` and ends above `2Y`
spends at least `Y / D - 1` steps in `(Y, 2Y]`. -/
lemma cross (w : ℕ → ℕ) (m D Y : ℕ) (hmono : ∀ j < m, w j < w (j + 1))
    (hstep : ∀ j < m, w (j + 1) ≤ w j + D) (h0 : w 0 ≤ Y) (hm : 2 * Y < w m) :
    ∃ j1 j2, j1 ≤ j2 ∧ j2 ≤ m ∧ Y < D * (j2 - j1 + 1) ∧
      ∀ j, j1 ≤ j → j < j2 → Y < w j ∧ w j ≤ 2 * Y := by
  classical
  have hmon : ∀ t i, i + t ≤ m → w i ≤ w (i + t) := by
    intro t
    induction t with
    | zero => intro i _; simp
    | succ t ih =>
      intro i hi
      have h1 := ih i (by omega)
      have h2 := hmono (i + t) (by omega)
      rw [show i + (t + 1) = i + t + 1 by ring]
      omega
  have hgrow : ∀ t i, i + t ≤ m → w (i + t) ≤ w i + D * t := by
    intro t
    induction t with
    | zero => intro i _; simp
    | succ t ih =>
      intro i hi
      have h1 := ih i (by omega)
      have h2 := hstep (i + t) (by omega)
      rw [show i + (t + 1) = i + t + 1 by ring, Nat.mul_succ]
      omega
  have hex2 : ∃ j, 2 * Y < w j ∧ j ≤ m := ⟨m, hm, le_refl _⟩
  set j2 := Nat.find hex2 with hj2def
  have hj2 := Nat.find_spec hex2
  have hlt2 : ∀ j < j2, ¬ (2 * Y < w j ∧ j ≤ m) := fun j hj => Nat.find_min hex2 hj
  have hex1 : ∃ j, Y < w j ∧ j ≤ j2 := ⟨j2, by rw [← hj2def] at hj2; omega, le_refl _⟩
  set j1 := Nat.find hex1 with hj1def
  have hj1 := Nat.find_spec hex1
  have hlt1 : ∀ j < j1, ¬ (Y < w j ∧ j ≤ j2) := fun j hj => Nat.find_min hex1 hj
  rw [← hj2def] at hj2
  rw [← hj1def] at hj1
  have hj1pos : 1 ≤ j1 := by
    by_contra h
    have : j1 = 0 := by omega
    rw [this] at hj1
    omega
  have hprev : w (j1 - 1) ≤ Y := by
    have := hlt1 (j1 - 1) (by omega)
    by_contra h
    exact this ⟨by omega, by omega⟩
  have hbig := hgrow (j2 - (j1 - 1)) (j1 - 1) (by omega)
  rw [show j1 - 1 + (j2 - (j1 - 1)) = j2 by omega] at hbig
  refine ⟨j1, j2, hj1.2, hj2.2, ?_, ?_⟩
  · have e : j2 - (j1 - 1) = j2 - j1 + 1 := by omega
    rw [e] at hbig
    omega
  · intro j hj1j hjj2
    have hm1 := hmon (j - j1) j1 (by omega)
    rw [show j1 + (j - j1) = j by omega] at hm1
    have h2 := hlt2 j hjj2
    refine ⟨by omega, ?_⟩
    by_contra h
    exact h2 ⟨by omega, by omega⟩

/-- Prefix sums. -/
def P (A : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ range n, A i

lemma P_succ (A : ℕ → ℕ) (n : ℕ) : P A (n + 1) = P A n + A n := by
  simp [P, sum_range_succ]

lemma P_mono (A : ℕ → ℕ) {m n : ℕ} (h : m ≤ n) : P A m ≤ P A n :=
  sum_le_sum_of_subset (range_subset_range.2 h)

lemma sum_Ico_eq (A : ℕ → ℕ) {u v : ℕ} (h : u ≤ v) : ∑ i ∈ Ico u v, A i = P A v - P A u := by
  have := sum_range_add_sum_Ico A h
  unfold P
  omega

end OMA.E1213

open Finset OMA.E1213 in
theorem OMA.solution : type_of% @Erdos1213.erdos_1213.variants.hegyvari := by
  refine ⟨1000, by norm_num, ?_⟩
  intro a K ha hK s A hs hA0 hmono hgap hbig
  by_contra hno
  -- basic facts about the sequence
  have hlt : ∀ i j, i < j → j < s → A i < A j := fun i j hij hj =>
    hmono (Set.mem_Iio.2 (by omega)) (Set.mem_Iio.2 hj) hij
  have hstepA : ∀ t i, i + t < s → A (i + t) ≤ A i + K * t := by
    intro t
    induction t with
    | zero => intro i _; simp
    | succ t ih =>
      intro i hi
      have h1 := ih i (by omega)
      have h2 := hgap (i + t) (by omega)
      have h3 := hlt (i + t) (i + t + 1) (by omega) (by omega)
      rw [show i + (t + 1) = i + t + 1 by ring, Nat.mul_succ]
      omega
  have hAle : ∀ i, i < s → A i ≤ a + K * i := by
    intro i hi
    have := hstepA i 0 (by omega)
    simpa [hA0] using this
  -- the parameters
  set M : ℕ := ⌈Real.exp ((K : ℝ) + 2)⌉₊ with hMdef
  set Y : ℕ := M * (a + K * M) with hYdef
  have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.2 (by
    rw [hMdef]; exact (Nat.ceil_pos.2 (Real.exp_pos _)).ne')
  -- the size condition: 2Y < A (s - 1)
  have hYbig : 2 * Y < A (s - 1) := by
    set E := Real.exp ((K : ℝ) + 2) with hE
    have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
    have hMle : (M : ℝ) ≤ 2 * E := by
      have := Nat.ceil_lt_add_one (Real.exp_pos ((K : ℝ) + 2)).le
      rw [← hMdef, ← hE] at this
      linarith
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have hKe : (K : ℝ) ≤ Real.exp K := by linarith [Real.add_one_le_exp (K : ℝ)]
    have hEE : E * E = Real.exp 4 * Real.exp (2 * K) := by
      rw [hE, ← Real.exp_add, ← Real.exp_add]
      ring_nf
    have he4 : Real.exp 4 < 81 := by
      have h1 := Real.exp_one_lt_d9
      have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [h4]
      have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
      calc Real.exp 1 ^ 4 < 3 ^ 4 := by
            exact pow_lt_pow_left₀ (by linarith) h0 (by norm_num)
        _ = 81 := by norm_num
    have h3K : Real.exp K * Real.exp (2 * K) ≤ Real.exp (1000 * K) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    have hY : ((2 * Y : ℕ) : ℝ) ≤ 1000 * a * Real.exp (1000 * K) := by
      rw [hYdef]
      push_cast
      have hMn : (0 : ℝ) ≤ M := by positivity
      have step1 : 2 * (M : ℝ) * (a + K * M) ≤ 2 * (2 * E) * (a + K * (2 * E)) := by
        gcongr
      have step2 : 2 * (2 * E) * ((a : ℝ) + K * (2 * E)) ≤ 12 * K * a * (E * E) := by
        nlinarith [mul_le_mul hK1 hE1 zero_le_one (by positivity : (0 : ℝ) ≤ K),
          mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ K) (by positivity : (0 : ℝ) ≤ a))
            (sub_nonneg.2 hE1), mul_nonneg (by positivity : (0 : ℝ) ≤ E) (sub_nonneg.2 ha1),
          mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ K) (by positivity : (0 : ℝ) ≤ E))
            (by positivity : (0 : ℝ) ≤ E), mul_nonneg (by positivity : (0 : ℝ) ≤ E)
            (sub_nonneg.2 hK1)]
      have step3 : 12 * (K : ℝ) * a * (E * E) ≤ 1000 * a * Real.exp (1000 * K) := by
        rw [hEE]
        have hpos : (0 : ℝ) ≤ Real.exp (2 * K) := (Real.exp_pos _).le
        have h1 : (K : ℝ) * Real.exp (2 * K) ≤ Real.exp (1000 * K) := by
          nlinarith [mul_le_mul_of_nonneg_right hKe hpos]
        have h2 : (0 : ℝ) ≤ a := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 12 * a),
          mul_le_mul_of_nonneg_left he4.le
            (by positivity : (0 : ℝ) ≤ 12 * a * (K * Real.exp (2 * K))),
          (Real.exp_pos 4).le, mul_nonneg h2 (mul_nonneg (by positivity : (0 : ℝ) ≤ K) hpos)]
      linarith
    have : ((2 * Y : ℕ) : ℝ) < A (s - 1) := lt_of_le_of_lt hY (by exact_mod_cast hbig)
    exact_mod_cast this
  -- s is large
  have hsM : M + 1 < s := by
    have h1 := hAle (s - 1) (by omega)
    have h2 : K * M ≤ Y := by
      rw [hYdef]
      calc K * M ≤ M * (K * M) := Nat.le_mul_of_pos_left _ hM1
        _ ≤ M * (a + K * M) := Nat.mul_le_mul_left _ (by omega)
    have h3 : a ≤ Y := by
      rw [hYdef]
      calc a ≤ M * a := Nat.le_mul_of_pos_left a hM1
        _ ≤ M * (a + K * M) := Nat.mul_le_mul_left _ (by omega)
    have h4 : K * M < K * (s - 1) := by omega
    have := Nat.lt_of_mul_lt_mul_left h4
    omega
  -- no two intervals with equal sums
  have hinj : ∀ u L u' L', 1 ≤ L → u + L ≤ s → 1 ≤ L' → u' + L' ≤ s →
      P A (u + L) - P A u = P A (u' + L') - P A u' → u = u' ∧ L = L' := by
    intro u L u' L' hL hu hL' hu' heq
    by_contra hne
    apply hno
    refine ⟨u, u + L, u', u' + L', by omega, hu, by omega, hu', ?_, ?_⟩
    · intro h
      apply hne
      simp only [Prod.mk.injEq] at h
      omega
    · rw [sum_Ico_eq A (by omega), sum_Ico_eq A (by omega)]
      exact heq
  -- count windows with sums in (Y, 2Y]
  let F : ℕ × ℕ → ℕ := fun q => P A (q.2 + q.1) - P A q.2
  let T : Finset (ℕ × ℕ) := ((Icc 1 M) ×ˢ (range s)).filter
    (fun q => q.2 + q.1 ≤ s ∧ Y < F q ∧ F q ≤ 2 * Y)
  let TL : ℕ → Finset ℕ := fun L => (range s).filter
    (fun u => u + L ≤ s ∧ Y < F (L, u) ∧ F (L, u) ≤ 2 * Y)
  have hcardT : T.card ≤ Y := by
    have hmaps : Set.MapsTo F T (Ioc Y (2 * Y)) := by
      intro q hq
      simp only [T, coe_filter, Set.mem_setOf_eq] at hq
      rw [coe_Ioc, Set.mem_Ioc]
      exact ⟨hq.2.2.1, hq.2.2.2⟩
    have hinjF : Set.InjOn F T := by
      intro q hq q' hq' h
      simp only [T, coe_filter, Set.mem_setOf_eq, mem_product, mem_Icc] at hq hq'
      have := hinj q.2 q.1 q'.2 q'.1 hq.1.1.1 hq.2.1 hq'.1.1.1 hq'.2.1 h
      exact Prod.ext this.2 this.1
    have := card_le_card_of_injOn F hmaps hinjF
    rwa [Nat.card_Ioc, show 2 * Y - Y = Y by omega] at this
  have hsumT : T.card = ∑ L ∈ Icc 1 M, (TL L).card := by
    simp only [T, TL, card_filter, sum_product]
  -- each length contributes
  have hper : ∀ L ∈ Icc 1 M, Y < K * L * ((TL L).card + 1) := by
    intro L hL
    rw [mem_Icc] at hL
    have hLs : L + 1 < s := by omega
    let w : ℕ → ℕ := fun j => P A (j + L) - P A j
    have hwmono : ∀ j < s - L, w j < w (j + 1) := by
      intro j hj
      have e1 := P_succ A j
      have e2 := P_succ A (j + L)
      have e3 := P_mono A (show j ≤ j + L by omega)
      have h := hlt j (j + L) (by omega) (by omega)
      simp only [w]
      rw [show j + 1 + L = j + L + 1 by ring]
      omega
    have hwstep : ∀ j < s - L, w (j + 1) ≤ w j + K * L := by
      intro j hj
      have e1 := P_succ A j
      have e2 := P_succ A (j + L)
      have e3 := P_mono A (show j ≤ j + L by omega)
      have h := hstepA L j (by omega)
      have h' := hlt j (j + L) (by omega) (by omega)
      simp only [w]
      rw [show j + 1 + L = j + L + 1 by ring]
      omega
    have hw0 : w 0 ≤ Y := by
      simp only [w, zero_add]
      have hP0 : P A 0 = 0 := by simp [P]
      rw [hP0, Nat.sub_zero]
      calc P A L = ∑ i ∈ range L, A i := rfl
        _ ≤ ∑ _i ∈ range L, (a + K * L) := by
          apply sum_le_sum
          intro i hi
          rw [mem_range] at hi
          have := hAle i (by omega)
          have : K * i ≤ K * L := Nat.mul_le_mul_left _ hi.le
          omega
        _ = L * (a + K * L) := by simp
        _ ≤ M * (a + K * M) := Nat.mul_le_mul hL.2 (by
            have : K * L ≤ K * M := Nat.mul_le_mul_left _ hL.2
            omega)
    have hwm : 2 * Y < w (s - L) := by
      simp only [w]
      rw [show s - L + L = s by omega]
      have e1 := P_succ A (s - 1)
      rw [show s - 1 + 1 = s by omega] at e1
      have e3 := P_mono A (show s - L ≤ s - 1 by omega)
      omega
    obtain ⟨j1, j2, h12, h2m, hY, hrange⟩ := cross w (s - L) (K * L) Y hwmono hwstep hw0 hwm
    have hsub : Ico j1 j2 ⊆ TL L := by
      intro j hj
      rw [mem_Ico] at hj
      have := hrange j hj.1 hj.2
      simp only [TL, mem_filter, mem_range, F]
      refine ⟨by omega, by omega, ?_⟩
      simpa [w] using this
    have hc := card_le_card hsub
    rw [Nat.card_Ico] at hc
    calc Y < K * L * (j2 - j1 + 1) := hY
      _ ≤ K * L * ((TL L).card + 1) := Nat.mul_le_mul_left _ (by omega)
  -- sum over lengths in the reals
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hreal : ∀ L ∈ Icc 1 M, (Y : ℝ) * (L : ℝ)⁻¹ < K * (((TL L).card : ℝ) + 1) := by
    intro L hL
    have hL1 : (0 : ℝ) < L := by
      have := (mem_Icc.1 hL).1
      exact_mod_cast (show 0 < L by omega)
    have h := hper L hL
    have h' : (Y : ℝ) < K * L * (((TL L).card : ℝ) + 1) := by exact_mod_cast h
    rw [mul_inv_lt_iff₀ hL1]
    nlinarith
  have hne : (Icc 1 M).Nonempty := ⟨1, by simp [hM1]⟩
  have hsum := sum_lt_sum_of_nonempty hne hreal
  rw [← mul_sum, ← mul_sum, sum_add_distrib] at hsum
  have hH : (∑ L ∈ Icc 1 M, ((L : ℝ))⁻¹) = (harmonic M : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  have hlog : (K : ℝ) + 2 ≤ harmonic M := by
    have h1 := log_add_one_le_harmonic M
    have h2 : Real.exp ((K : ℝ) + 2) ≤ M := Nat.le_ceil _
    have h3 : (K : ℝ) + 2 ≤ Real.log ((M + 1 : ℕ) : ℝ) := by
      rw [← Real.log_exp ((K : ℝ) + 2)]
      apply Real.log_le_log (Real.exp_pos _)
      push_cast
      linarith
    linarith
  have hcount : (∑ L ∈ Icc 1 M, ((TL L).card : ℝ)) ≤ Y := by
    have : ((∑ L ∈ Icc 1 M, (TL L).card : ℕ) : ℝ) ≤ Y := by
      rw [← hsumT]; exact_mod_cast hcardT
    push_cast at this
    exact this
  rw [hH] at hsum
  simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, smul_eq_mul, mul_one] at hsum
  have hYge : (K : ℝ) * M ≤ Y := by
    have : K * M ≤ Y := by
      rw [hYdef]
      calc K * M ≤ M * (K * M) := Nat.le_mul_of_pos_left _ hM1
        _ ≤ M * (a + K * M) := Nat.mul_le_mul_left _ (by omega)
    exact_mod_cast this
  have hY0 : (0 : ℝ) ≤ Y := by positivity
  have e1 := mul_le_mul_of_nonneg_left hlog hY0
  have e2 := mul_le_mul_of_nonneg_left hcount hK0.le
  rw [nsmul_eq_mul, mul_one] at hsum
  nlinarith [e1, e2, hsum, hYge]
