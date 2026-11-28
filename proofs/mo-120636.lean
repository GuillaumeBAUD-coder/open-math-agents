import OMAStatements.S_mo_120636

-- Problem: Binomial Expectation of Convex Function
-- Upstream: formal-conjectures statements/mo-120636.lean:0 (declaration OMA.S_mo_120636.main)
-- Credit: @umarsxlim (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

private lemma bernstein_eval (n j : ℕ) (p : ℝ) :
    (bernsteinPolynomial ℝ n j).eval p = (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j) := by
  simp [bernsteinPolynomial, mul_assoc]

private lemma hasDerivAt_finset_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℝ → ℝ) (f' : ι → ℝ) (x : ℝ)
    (hf : ∀ i ∈ s, HasDerivAt (f i) (f' i) x) :
    HasDerivAt (fun y => ∑ i ∈ s, f i y) (∑ i ∈ s, f' i) x := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact hasDerivAt_const x (0 : ℝ)
  | @insert a t ha ih =>
    have hfun : (fun y => ∑ i ∈ insert a t, f i y) =
        fun y => f a y + ∑ i ∈ t, f i y := by
      ext y
      exact Finset.sum_insert ha
    rw [hfun, Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a t)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma choose_succ_mul (m k : ℕ) (hk : k ≤ m) :
    (m + 1).choose (k + 1) * (k + 1) = (m + 1) * m.choose k := by
  have hpos : 0 < k.factorial * (m - k).factorial :=
    Nat.mul_pos (Nat.factorial_pos k) (Nat.factorial_pos (m - k))
  apply Nat.mul_right_cancel hpos
  have h1 : (m + 1).choose (k + 1) * (k + 1).factorial * (m - k).factorial = (m + 1).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.succ_le_succ hk)
    simpa [Nat.succ_sub_succ_eq_sub] using h
  have h2 : m.choose k * k.factorial * (m - k).factorial = m.factorial :=
    Nat.choose_mul_factorial_mul_factorial hk
  calc
    (m + 1).choose (k + 1) * (k + 1) * (k.factorial * (m - k).factorial)
      = (m + 1).choose (k + 1) * ((k + 1) * k.factorial) * (m - k).factorial := by ring
    _ = (m + 1).choose (k + 1) * (k + 1).factorial * (m - k).factorial := by
        rw [Nat.factorial_succ]
    _ = (m + 1).factorial := h1
    _ = (m + 1) * m.factorial := Nat.factorial_succ m
    _ = (m + 1) * (m.choose k * k.factorial * (m - k).factorial) := by rw [h2]
    _ = (m + 1) * m.choose k * (k.factorial * (m - k).factorial) := by ring

private lemma choose_mul_sub (m j : ℕ) (hj : j ≤ m) :
    (m + 1).choose j * (m + 1 - j) = (m + 1) * m.choose j := by
  have hpos : 0 < j.factorial * (m - j).factorial :=
    Nat.mul_pos (Nat.factorial_pos j) (Nat.factorial_pos (m - j))
  apply Nat.mul_right_cancel hpos
  have hsub : m + 1 - j = (m - j) + 1 := by omega
  have h1 : (m + 1).choose j * j.factorial * (m + 1 - j).factorial = (m + 1).factorial :=
    Nat.choose_mul_factorial_mul_factorial (Nat.le_succ_of_le hj)
  have h2 : m.choose j * j.factorial * (m - j).factorial = m.factorial :=
    Nat.choose_mul_factorial_mul_factorial hj
  calc
    (m + 1).choose j * (m + 1 - j) * (j.factorial * (m - j).factorial)
      = (m + 1).choose j * j.factorial * ((m + 1 - j) * (m - j).factorial) := by ring
    _ = (m + 1).choose j * j.factorial * (m + 1 - j).factorial := by
        rw [hsub, Nat.factorial_succ]
    _ = (m + 1).factorial := h1
    _ = (m + 1) * m.factorial := Nat.factorial_succ m
    _ = (m + 1) * (m.choose j * j.factorial * (m - j).factorial) := by rw [h2]
    _ = (m + 1) * m.choose j * (j.factorial * (m - j).factorial) := by ring

theorem OMA.solution : type_of% @OMA.S_mo_120636.main := by
  dsimp only
  constructor
  · intro f n p
    cases n with
    | zero =>
      have hfun : (fun x : ℝ => ∑ j ∈ Finset.range 1, f j * (bernsteinPolynomial ℝ 0 j).eval x) =
          fun _ => f 0 := by
        ext x
        simp [bernstein_eval]
      rw [hfun]
      simpa using hasDerivAt_const p (f 0)
    | succ m =>
      let A : ℕ → ℝ := fun j =>
        if j = 0 then 0
        else f j * ((m + 1 : ℕ) : ℝ) * (m.choose (j - 1) : ℝ) * p ^ (j - 1) * (1 - p) ^ (m - (j - 1))
      let B : ℕ → ℝ := fun j =>
        if j = m + 1 then 0
        else f j * ((m + 1 : ℕ) : ℝ) * (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j)
      have hterm : ∀ j ∈ Finset.range (m + 2),
          HasDerivAt (fun x : ℝ => f j * (bernsteinPolynomial ℝ (m + 1) j).eval x)
            (A j - B j) p := by
        intro j hj
        have hle : j ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hfun : (fun x : ℝ => f j * (bernsteinPolynomial ℝ (m + 1) j).eval x) =
            fun x : ℝ => (f j * ((m + 1).choose j : ℝ)) * (x ^ j * (1 - x) ^ (m + 1 - j)) := by
          ext x
          rw [bernstein_eval]
          ring
        rw [hfun]
        have hd1 : HasDerivAt (fun x : ℝ => x ^ j) ((j : ℝ) * p ^ (j - 1)) p :=
          hasDerivAt_pow j p
        have hd2 : HasDerivAt (fun x : ℝ => (1 - x) ^ (m + 1 - j))
            (((m + 1 - j : ℕ) : ℝ) * (1 - p) ^ (m + 1 - j - 1) * (-1)) p := by
          have hsub : HasDerivAt (fun x : ℝ => (1 : ℝ) - x) (-1) p :=
            (hasDerivAt_id' p).const_sub (1 : ℝ)
          exact (hasDerivAt_pow (m + 1 - j) (1 - p)).comp p hsub
        have hdmul := (hd1.mul hd2).const_mul (f j * ((m + 1).choose j : ℝ))
        refine hdmul.congr_deriv ?_
        have hT1 : f j * ((m + 1).choose j : ℝ) * ((j : ℝ) * p ^ (j - 1) * (1 - p) ^ (m + 1 - j)) =
            A j := by
          cases j with
          | zero =>
            simp [A]
          | succ k =>
            have hk : k ≤ m := Nat.le_of_succ_le_succ hle
            have hc : (((m + 1).choose (k + 1) : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) =
                ((m + 1 : ℕ) : ℝ) * (m.choose k : ℝ) := by
              exact_mod_cast choose_succ_mul m k hk
            have hsub1 : m + 1 - (k + 1) = m - k := by omega
            simp only [A, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, hsub1]
            calc
              f (k + 1) * ((m + 1).choose (k + 1) : ℝ) *
                  (((k + 1 : ℕ) : ℝ) * p ^ k * (1 - p) ^ (m - k))
                = f (k + 1) * (((m + 1).choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ)) *
                    p ^ k * (1 - p) ^ (m - k) := by ring
              _ = f (k + 1) * (((m + 1 : ℕ) : ℝ) * (m.choose k : ℝ)) *
                    p ^ k * (1 - p) ^ (m - k) := by rw [hc]
              _ = f (k + 1) * ((m + 1 : ℕ) : ℝ) * (m.choose k : ℝ) *
                    p ^ k * (1 - p) ^ (m - k) := by ring
        have hT2 : f j * ((m + 1).choose j : ℝ) *
            (p ^ j * (((m + 1 - j : ℕ) : ℝ) * (1 - p) ^ (m + 1 - j - 1))) = B j := by
          by_cases hjm : j = m + 1
          · subst hjm
            simp [B]
          · have hjm' : j ≤ m := by omega
            have hc : (((m + 1).choose j : ℕ) : ℝ) * ((m + 1 - j : ℕ) : ℝ) =
                ((m + 1 : ℕ) : ℝ) * (m.choose j : ℝ) := by
              exact_mod_cast choose_mul_sub m j hjm'
            have hsub2 : m + 1 - j - 1 = m - j := by omega
            simp only [B, hjm, ↓reduceIte, hsub2]
            calc
              f j * ((m + 1).choose j : ℝ) *
                  (p ^ j * (((m + 1 - j : ℕ) : ℝ) * (1 - p) ^ (m - j)))
                = f j * (((m + 1).choose j : ℝ) * ((m + 1 - j : ℕ) : ℝ)) *
                    p ^ j * (1 - p) ^ (m - j) := by ring
              _ = f j * (((m + 1 : ℕ) : ℝ) * (m.choose j : ℝ)) *
                    p ^ j * (1 - p) ^ (m - j) := by rw [hc]
              _ = f j * ((m + 1 : ℕ) : ℝ) * (m.choose j : ℝ) *
                    p ^ j * (1 - p) ^ (m - j) := by ring
        rw [← hT1, ← hT2]
        ring
      have hsum := hasDerivAt_finset_sum (Finset.range (m + 2))
        (fun j x => f j * (bernsteinPolynomial ℝ (m + 1) j).eval x) (fun j => A j - B j) p hterm
      refine hsum.congr_deriv ?_
      have hA : ∑ j ∈ Finset.range (m + 2), A j = ∑ j ∈ Finset.range (m + 1), A (j + 1) := by
        rw [Finset.sum_range_succ']
        simp [A]
      have hB : ∑ j ∈ Finset.range (m + 2), B j = ∑ j ∈ Finset.range (m + 1), B j := by
        rw [Finset.sum_range_succ]
        simp [B]
      rw [Nat.add_sub_cancel, Finset.sum_sub_distrib, hA, hB, ← Finset.sum_sub_distrib,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjlt : j < m + 1 := Finset.mem_range.mp hj
      have hjne : j ≠ m + 1 := Nat.ne_of_lt hjlt
      simp only [A, B, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, hjne, bernstein_eval]
      ring
  · refine ⟨fun x : ℝ => x ^ 2 + 1, 1, ?_, ?_, ?_⟩
    · intro x
      positivity
    · refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
      simp only [smul_eq_mul]
      have hdiff : a * (x ^ 2 + 1) + b * (y ^ 2 + 1) - ((a * x + b * y) ^ 2 + 1) =
          a * b * (x - y) ^ 2 := by
        have hb' : b = 1 - a := by linarith
        subst hb'
        ring
      nlinarith [mul_nonneg ha hb, sq_nonneg (x - y)]
    · intro p _
      simp [Finset.sum_range_succ, bernstein_eval]
      ring
