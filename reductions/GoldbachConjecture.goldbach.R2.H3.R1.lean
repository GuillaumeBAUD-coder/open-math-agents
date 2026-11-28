import OMAReductions.R_GoldbachConjecture_goldbach_R2

-- Reduction GoldbachConjecture.goldbach.R2.H3.R1 of step GoldbachConjecture.goldbach.R2.H3
-- Credit: @nisbenz

/-!
# Abel summation-by-parts reduction of the long-divisor Goldbach Möbius tail

Applies exact finite summation by parts on each cofactor row `k ≤ K = ⌊(n - 1)/(D + 1)⌋`
(`D = ⌊√(n / ⌊√√n⌋)⌋ ≈ n^{3/8}`, `U_k = ⌊(n - 1)/k⌋`) to strip the monotone weight
`log((n - x)/k)` from the long-divisor tail `T_D(n)`:

* `H1` (elementary odd-cofactor log-totient envelope): for every even `n > 50000`,
  `∑_{k ≤ K, (k,n)=1} log(U_k) / φ(k) ≤ (log n)^2`.
  (Numerically `≈ 0.33 (log n)^2` at `n = 50002` and asymptotically `≈ 0.278 (log n)^2`.)
* `H2` (open reflected prime–Möbius `L^{-2}`-saving row cancellation): for every even `n > 50000`,
  every coprime `k ≤ K`, and every `y ∈ [D, U_k]`,
  `|∑_{y < d ≤ U_k, n - kd prime, (n-kd,n)=1} log(n - kd) μ(d)| ≤ n / (2 φ(k) (log n)^2)`.
-/

namespace OMA.R_GoldbachConjecture_goldbach_R2_H3_R1

/-- Elementary odd-cofactor log-totient envelope bounded by `(log n)^2`. -/
def H1 : Prop :=
  ∀ n : ℕ, 50000 < n → Even n →
    (∑ k ∈ (Finset.Icc 1 ((n - 1) / (Nat.sqrt (n / Nat.sqrt (Nat.sqrt n)) + 1))).filter
        (fun k => Nat.Coprime k n),
      Real.log (((n - 1) / k : ℕ) : ℝ) / (Nat.totient k : ℝ)) ≤
      (Real.log (n : ℝ)) ^ 2

/-- Uniform reflected prime–Möbius row cancellation with `L^{-2}` saving. -/
def H2 : Prop :=
  ∀ n : ℕ, 50000 < n → Even n →
    ∀ k ∈ (Finset.Icc 1 ((n - 1) / (Nat.sqrt (n / Nat.sqrt (Nat.sqrt n)) + 1))).filter
        (fun k => Nat.Coprime k n),
      ∀ y ∈ Finset.Icc (Nat.sqrt (n / Nat.sqrt (Nat.sqrt n))) ((n - 1) / k),
        |∑ d ∈ (Finset.Icc (y + 1) ((n - 1) / k)).filter
            (fun d => Nat.Prime (n - k * d) ∧ Nat.Coprime (n - k * d) n),
          Real.log ((n - k * d : ℕ) : ℝ) * (ArithmeticFunction.moebius d : ℝ)| ≤
          (n : ℝ) / (2 * (Nat.totient k : ℝ) * (Real.log (n : ℝ)) ^ 2)

lemma telescoping_diff (w : ℕ → ℝ) (A B : ℕ) (hAB : A ≤ B) :
    w A + ∑ d ∈ Finset.Ico A B, (w (d + 1) - w d) = w B := by
  induction B with
  | zero =>
    have hA : A = 0 := by omega
    subst hA
    simp
  | succ B ih =>
    rcases eq_or_lt_of_le hAB with rfl | hlt
    · simp
    · have hle : A ≤ B := by omega
      rw [Finset.sum_Ico_succ_top hle]
      linarith [ih hle]

lemma abel_sum_identity (a w : ℕ → ℝ) (D U : ℕ) (hDU : D + 1 ≤ U) :
    ∑ d ∈ Finset.Icc (D + 1) U, a d * w d =
      w (D + 1) * (∑ d ∈ Finset.Icc (D + 1) U, a d) +
      ∑ y ∈ Finset.Ico (D + 1) U,
        (w (y + 1) - w y) * (∑ d ∈ Finset.Icc (y + 1) U, a d) := by
  induction U with
  | zero => omega
  | succ U ih =>
    rcases eq_or_lt_of_le hDU with heq | hlt
    · have h1 : Finset.Icc (D + 1) (U + 1) = {D + 1} := by
        rw [← heq, Finset.Icc_self]
      have h2 : Finset.Ico (D + 1) (U + 1) = ∅ := by
        rw [← heq, Finset.Ico_self]
      rw [h1, h2]
      simp [mul_comm]
    · have hle : D + 1 ≤ U := by omega
      have hIcc : Finset.Icc (D + 1) (U + 1) = insert (U + 1) (Finset.Icc (D + 1) U) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : U + 1 ∉ Finset.Icc (D + 1) U := by simp
      rw [hIcc, Finset.sum_insert hnot, Finset.sum_insert hnot, ih hle]
      rw [Finset.sum_Ico_succ_top hle]
      have htail :
          ∑ y ∈ Finset.Ico (D + 1) U,
            (w (y + 1) - w y) * (∑ d ∈ Finset.Icc (y + 1) (U + 1), a d) =
          (∑ y ∈ Finset.Ico (D + 1) U,
            (w (y + 1) - w y) * (∑ d ∈ Finset.Icc (y + 1) U, a d)) +
          (∑ y ∈ Finset.Ico (D + 1) U, (w (y + 1) - w y) * a (U + 1)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun y hy => ?_
        have hyU : y + 1 ≤ U := by
          have := (Finset.mem_Ico.mp hy).2; omega
        have hsub : Finset.Icc (y + 1) (U + 1) = insert (U + 1) (Finset.Icc (y + 1) U) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hnot' : U + 1 ∉ Finset.Icc (y + 1) U := by simp
        rw [hsub, Finset.sum_insert hnot']
        ring
      have hlast : ∑ d ∈ Finset.Icc (U + 1) (U + 1), a d = a (U + 1) := by simp
      rw [htail, hlast, ← Finset.sum_mul]
      have htel : w (D + 1) + ∑ y ∈ Finset.Ico (D + 1) U, (w (y + 1) - w y) + (w (U + 1) - w U) =
          w (U + 1) := by
        linarith [telescoping_diff w (D + 1) U hle]
      linear_combination a (U + 1) * htel.symm

lemma abel_sum_bound (a w : ℕ → ℝ) (D U : ℕ) (M : ℝ) (hDU : D + 1 ≤ U) (hM : 0 ≤ M)
    (hw0 : 0 ≤ w (D + 1))
    (hwmono : ∀ y ∈ Finset.Ico (D + 1) U, w y ≤ w (y + 1))
    (htail : ∀ y ∈ Finset.Icc D U, |∑ d ∈ Finset.Icc (y + 1) U, a d| ≤ M) :
    ∑ d ∈ Finset.Icc (D + 1) U, a d * w d ≤ w U * M := by
  rw [abel_sum_identity a w D U hDU]
  have h1 : w (D + 1) * (∑ d ∈ Finset.Icc (D + 1) U, a d) ≤ w (D + 1) * M := by
    have hD : ∑ d ∈ Finset.Icc (D + 1) U, a d ≤ M :=
      (le_abs_self _).trans (htail D (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩))
    exact mul_le_mul_of_nonneg_left hD hw0
  have h2 :
      ∑ y ∈ Finset.Ico (D + 1) U,
        (w (y + 1) - w y) * (∑ d ∈ Finset.Icc (y + 1) U, a d) ≤
      ∑ y ∈ Finset.Ico (D + 1) U, (w (y + 1) - w y) * M := by
    refine Finset.sum_le_sum fun y hy => ?_
    have hdiff : 0 ≤ w (y + 1) - w y := sub_nonneg.mpr (hwmono y hy)
    have hyIcc : y ∈ Finset.Icc D U := by
      have := Finset.mem_Ico.mp hy
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hty : ∑ d ∈ Finset.Icc (y + 1) U, a d ≤ M := (le_abs_self _).trans (htail y hyIcc)
    exact mul_le_mul_of_nonneg_left hty hdiff
  have htel := telescoping_diff w (D + 1) U hDU
  rw [← Finset.sum_mul] at h2
  calc
    w (D + 1) * ∑ d ∈ Finset.Icc (D + 1) U, a d +
        ∑ y ∈ Finset.Ico (D + 1) U, (w (y + 1) - w y) * ∑ d ∈ Finset.Icc (y + 1) U, a d
      ≤ w (D + 1) * M + (∑ i ∈ Finset.Ico (D + 1) U, (w (i + 1) - w i)) * M := add_le_add h1 h2
    _ = (w (D + 1) + ∑ d ∈ Finset.Ico (D + 1) U, (w (d + 1) - w d)) * M := by ring
    _ = w U * M := by rw [htel]

theorem main : H1 → H2 → OMA.R_GoldbachConjecture_goldbach_R2.H3 := by
  intro h1 h2 n hn heven
  let D : ℕ := Nat.sqrt (n / Nat.sqrt (Nat.sqrt n))
  let K : ℕ := (n - 1) / (D + 1)
  have hD_pos : 1 ≤ D := by
    have hsq1 : Nat.sqrt n ≤ n := Nat.sqrt_le_self n
    have hsq2 : Nat.sqrt (Nat.sqrt n) ≤ Nat.sqrt n := Nat.sqrt_le_self _
    have hsq2_pos : 1 ≤ Nat.sqrt (Nat.sqrt n) := by
      have h1' : 1 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
      exact Nat.le_sqrt.mpr (by omega)
    have hdiv : 1 ≤ n / Nat.sqrt (Nat.sqrt n) := by
      have hle : Nat.sqrt (Nat.sqrt n) ≤ n := hsq2.trans hsq1
      exact Nat.div_pos hle hsq2_pos
    exact Nat.le_sqrt.mpr (by omega)
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlogn_sq_pos : 0 < (Real.log (n : ℝ)) ^ 2 := by positivity
  have hrow : ∀ k ∈ (Finset.Icc 1 K).filter (fun k => Nat.Coprime k n),
      (∑ x ∈ (Finset.Icc 1 (n - 2)).filter
          (fun x => Nat.Prime x ∧ Nat.Coprime x n ∧ k ∣ (n - x) ∧ x + k * D < n),
        Real.log (x : ℝ) * (ArithmeticFunction.moebius ((n - x) / k) : ℝ) *
          Real.log (((n - x) / k : ℕ) : ℝ)) ≤
      Real.log (((n - 1) / k : ℕ) : ℝ) *
        ((n : ℝ) / (2 * (Nat.totient k : ℝ) * (Real.log (n : ℝ)) ^ 2)) := by
    intro k hk
    have hk_mem := Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1
    have hk_pos : 0 < k := by omega
    let U : ℕ := (n - 1) / k
    have hDU : D + 1 ≤ U := by
      have hmul : k * (D + 1) ≤ n - 1 := by
        have hle := Nat.mul_le_mul_right (D + 1) hk_mem.2
        exact hle.trans (Nat.div_mul_le_self (n - 1) (D + 1))
      exact (Nat.le_div_iff_mul_le hk_pos).mpr (by rwa [mul_comm])
    let a : ℕ → ℝ := fun d =>
      if Nat.Prime (n - k * d) ∧ Nat.Coprime (n - k * d) n then
        Real.log ((n - k * d : ℕ) : ℝ) * (ArithmeticFunction.moebius d : ℝ)
      else 0
    have hreindex :
        (∑ x ∈ (Finset.Icc 1 (n - 2)).filter
            (fun x => Nat.Prime x ∧ Nat.Coprime x n ∧ k ∣ (n - x) ∧ x + k * D < n),
          Real.log (x : ℝ) * (ArithmeticFunction.moebius ((n - x) / k) : ℝ) *
            Real.log (((n - x) / k : ℕ) : ℝ)) =
        ∑ d ∈ Finset.Icc (D + 1) U, a d * Real.log (d : ℝ) := by
      have hfilt :
          ∑ d ∈ Finset.Icc (D + 1) U, a d * Real.log (d : ℝ) =
          ∑ d ∈ (Finset.Icc (D + 1) U).filter
              (fun d => Nat.Prime (n - k * d) ∧ Nat.Coprime (n - k * d) n),
            Real.log ((n - k * d : ℕ) : ℝ) * (ArithmeticFunction.moebius d : ℝ) *
              Real.log (d : ℝ) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun d _ => ?_
        dsimp [a]
        split_ifs <;> simp
      rw [hfilt]
      refine Finset.sum_bij (fun x _ => (n - x) / k) ?_ ?_ ?_ ?_
      · intro x hx
        obtain ⟨hxIcc, hpx, hcopx, hdvd, hlt⟩ := Finset.mem_filter.mp hx
        have hx1 := (Finset.mem_Icc.mp hxIcc).1
        have hx2 := (Finset.mem_Icc.mp hxIcc).2
        have hmul : k * ((n - x) / k) = n - x := Nat.mul_div_cancel' hdvd
        have hsub : n - k * ((n - x) / k) = x := by omega
        have hd_lo : D + 1 ≤ (n - x) / k := by
          have : k * D < k * ((n - x) / k) := by omega
          have := Nat.lt_of_mul_lt_mul_left this
          omega
        have hd_hi : (n - x) / k ≤ U := Nat.div_le_div_right (by omega)
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd_lo, hd_hi⟩, by rw [hsub]; exact hpx, by rw [hsub]; exact hcopx⟩
      · intro x₁ hx₁ x₂ hx₂ heq
        have hdvd₁ := (Finset.mem_filter.mp hx₁).2.2.2.1
        have hdvd₂ := (Finset.mem_filter.mp hx₂).2.2.2.1
        have h1' := (Finset.mem_Icc.mp (Finset.mem_filter.mp hx₁).1).2
        have h2' := (Finset.mem_Icc.mp (Finset.mem_filter.mp hx₂).1).2
        have hm₁ : k * ((n - x₁) / k) = n - x₁ := Nat.mul_div_cancel' hdvd₁
        have hm₂ : k * ((n - x₂) / k) = n - x₂ := Nat.mul_div_cancel' hdvd₂
        have heq' : k * ((n - x₁) / k) = k * ((n - x₂) / k) := congrArg (k * ·) heq
        rw [hm₁, hm₂] at heq'
        omega
      · intro d hd
        obtain ⟨hdIcc, hpd, hcopd⟩ := Finset.mem_filter.mp hd
        have hd_lo := (Finset.mem_Icc.mp hdIcc).1
        have hd_hi := (Finset.mem_Icc.mp hdIcc).2
        have hkd_le : k * d ≤ n - 1 := by
          have := (Nat.le_div_iff_mul_le hk_pos).mp hd_hi
          rwa [mul_comm] at this
        have hkd_ge : 2 ≤ k * d := by nlinarith
        refine ⟨n - k * d, ?_, ?_⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hpd, hcopd, ?_, ?_⟩
          · rw [Nat.sub_sub_self (by omega)]
            exact dvd_mul_right k d
          · have : k * D < k * d := Nat.mul_lt_mul_of_pos_left (by omega) hk_pos
            omega
        · rw [Nat.sub_sub_self (by omega), Nat.mul_div_cancel_left _ hk_pos]
      · intro x hx
        have hdvd := (Finset.mem_filter.mp hx).2.2.2.1
        have hx2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1).2
        have hm : k * ((n - x) / k) = n - x := Nat.mul_div_cancel' hdvd
        have hsub : n - k * ((n - x) / k) = x := by omega
        rw [hsub]
    rw [hreindex]
    have hM_nn : 0 ≤ (n : ℝ) / (2 * (Nat.totient k : ℝ) * (Real.log (n : ℝ)) ^ 2) := by
      have hphi : (0 : ℝ) ≤ (Nat.totient k : ℝ) := Nat.cast_nonneg _
      positivity
    refine abel_sum_bound a (fun d => Real.log (d : ℝ)) D U _ hDU hM_nn ?_ ?_ ?_
    · exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ D + 1))
    · intro y hy
      have hy_pos : (0 : ℝ) < (y : ℝ) := by
        have := (Finset.mem_Ico.mp hy).1
        exact_mod_cast (by omega : 0 < y)
      exact Real.log_le_log hy_pos (by exact_mod_cast Nat.le_succ y)
    · intro y hy
      have hsum_eq : ∑ d ∈ Finset.Icc (y + 1) U, a d =
          ∑ d ∈ (Finset.Icc (y + 1) U).filter
              (fun d => Nat.Prime (n - k * d) ∧ Nat.Coprime (n - k * d) n),
            Real.log ((n - k * d : ℕ) : ℝ) * (ArithmeticFunction.moebius d : ℝ) := by
        rw [Finset.sum_filter]
      rw [hsum_eq]
      exact h2 n hn heven k hk y hy
  have hsum_rows := Finset.sum_le_sum hrow
  have hfactor :
      (∑ k ∈ (Finset.Icc 1 K).filter (fun k => Nat.Coprime k n),
        Real.log (((n - 1) / k : ℕ) : ℝ) *
          ((n : ℝ) / (2 * (Nat.totient k : ℝ) * (Real.log (n : ℝ)) ^ 2))) =
      ((n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 2)) *
        (∑ k ∈ (Finset.Icc 1 K).filter (fun k => Nat.Coprime k n),
          Real.log (((n - 1) / k : ℕ) : ℝ) / (Nat.totient k : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hcoef_nn : 0 ≤ (n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 2) := by positivity
  have hbound :
      ((n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 2)) *
        (∑ k ∈ (Finset.Icc 1 K).filter (fun k => Nat.Coprime k n),
          Real.log (((n - 1) / k : ℕ) : ℝ) / (Nat.totient k : ℝ)) ≤
      (1 : ℝ) / 2 * n := by
    calc
      ((n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 2)) *
          (∑ k ∈ (Finset.Icc 1 K).filter (fun k => Nat.Coprime k n),
            Real.log (((n - 1) / k : ℕ) : ℝ) / (Nat.totient k : ℝ))
        ≤ ((n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 2)) * (Real.log (n : ℝ)) ^ 2 :=
            mul_le_mul_of_nonneg_left (h1 n hn heven) hcoef_nn
      _ = (1 : ℝ) / 2 * n := by
            field_simp [hlogn_sq_pos.ne']
  exact hsum_rows.trans (hfactor ▸ hbound)

end OMA.R_GoldbachConjecture_goldbach_R2_H3_R1
