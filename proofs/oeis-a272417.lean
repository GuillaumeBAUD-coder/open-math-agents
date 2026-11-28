import OMAStatements.S_oeis_a272417

-- Problem: A272417: Number of active (ON, black) cells at stage 2^n-1 of the two-dimensional cellular automaton defined by Rule 469, based on the 5-celled von Neumann neighborhood.
-- Upstream: formal-conjectures statements/oeis-a272417.lean:0 (declaration OMA.S_oeis_a272417.main)
-- Credit: @DevinWatson (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.OeisA272417

open OMA.S_oeis_a272417 PowerSeries Finset

/-! ### Part 1: Ulam-Warburton automaton `U` and its basic symmetries -/

private def stepUW (f : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  f x y || decide ((f (x + 1) y).toNat + (f (x - 1) y).toNat +
    (f x (y + 1)).toNat + (f x (y - 1)).toNat = 1)

private def U : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | k + 1 => stepUW (U k)

private lemma stepUW_congr' {f g : ℤ → ℤ → Bool} {x y u v : ℤ}
    (h0 : f x y = g u v) (h1 : f (x + 1) y = g (u + 1) v) (h2 : f (x - 1) y = g (u - 1) v)
    (h3 : f x (y + 1) = g u (v + 1)) (h4 : f x (y - 1) = g u (v - 1)) :
    stepUW f x y = stepUW g u v := by
  simp only [stepUW, h0, h1, h2, h3, h4]

private lemma U_mono (k : ℕ) (x y : ℤ) (h : U k x y = true) : U (k + 1) x y = true := by
  simp only [U, stepUW, h, Bool.true_or]

private lemma U_origin_true (k : ℕ) : U k 0 0 = true := by
  induction k with
  | zero => rfl
  | succ k ih => exact U_mono k 0 0 ih

private lemma U_support (k : ℕ) : ∀ x y : ℤ, k < x.natAbs + y.natAbs → U k x y = false := by
  induction k with
  | zero =>
    intro x y h
    simp only [U]; apply decide_eq_false
    rintro ⟨rfl, rfl⟩; simp at h
  | succ k ih =>
    intro x y h
    simp only [U, stepUW]
    rw [ih x y (by omega), ih (x + 1) y (by omega), ih (x - 1) y (by omega),
      ih x (y + 1) (by omega), ih x (y - 1) (by omega)]
    rfl

private lemma U_symm (k : ℕ) :
    (∀ x y : ℤ, U k (-x) y = U k x y) ∧
    (∀ x y : ℤ, U k x (-y) = U k x y) ∧
    (∀ x y : ℤ, U k y x = U k x y) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_, ?_⟩ <;> intro x y <;> simp [U] <;>
      (by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy])
  | succ k ih =>
    obtain ⟨ihx, ihy, ihs⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro x y
      simp only [U, stepUW]
      have h1 : U k (-x + 1) y = U k (x - 1) y := by rw [← ihx (x - 1) y]; congr 1; omega
      have h2 : U k (-x - 1) y = U k (x + 1) y := by rw [← ihx (x + 1) y]; congr 1; omega
      rw [ihx x y, h1, h2, ihx x (y + 1), ihx x (y - 1)]
      have hsum : (U k (x - 1) y).toNat + (U k (x + 1) y).toNat +
          (U k x (y + 1)).toNat + (U k x (y - 1)).toNat =
          (U k (x + 1) y).toNat + (U k (x - 1) y).toNat +
          (U k x (y + 1)).toNat + (U k x (y - 1)).toNat := by omega
      rw [hsum]
    · intro x y
      simp only [U, stepUW]
      have h3 : U k x (-y + 1) = U k x (y - 1) := by rw [← ihy x (y - 1)]; congr 1; omega
      have h4 : U k x (-y - 1) = U k x (y + 1) := by rw [← ihy x (y + 1)]; congr 1; omega
      rw [ihy x y, ihy (x + 1) y, ihy (x - 1) y, h3, h4]
      have hsum : (U k (x + 1) y).toNat + (U k (x - 1) y).toNat +
          (U k x (y - 1)).toNat + (U k x (y + 1)).toNat =
          (U k (x + 1) y).toNat + (U k (x - 1) y).toNat +
          (U k x (y + 1)).toNat + (U k x (y - 1)).toNat := by omega
      rw [hsum]
    · intro x y
      simp only [U, stepUW]
      rw [ihs x y, ihs x (y + 1), ihs x (y - 1), ihs (x + 1) y, ihs (x - 1) y]
      have hsum : (U k x (y + 1)).toNat + (U k x (y - 1)).toNat +
          (U k (x + 1) y).toNat + (U k (x - 1) y).toNat =
          (U k (x + 1) y).toNat + (U k (x - 1) y).toNat +
          (U k x (y + 1)).toNat + (U k x (y - 1)).toNat := by omega
      rw [hsum]

private lemma U_diag_false (k : ℕ) : ∀ x y : ℤ, x ≠ 0 → x.natAbs = y.natAbs → U k x y = false := by
  induction k with
  | zero => intro x y hx _; simp [U, hx]
  | succ k ih =>
    intro x y hx hxy
    have ⟨_, hsy, hss⟩ := U_symm k
    have h0 : U k x y = false := ih x y hx hxy
    simp only [U, stepUW, h0, Bool.false_or]
    have hcases : y = x ∨ y = -x := by omega
    rcases hcases with hy | hy
    · rw [hy]
      have h1 : U k x (x + 1) = U k (x + 1) x := hss (x + 1) x
      have h2 : U k x (x - 1) = U k (x - 1) x := hss (x - 1) x
      rw [h1, h2]
      cases U k (x + 1) x <;> cases U k (x - 1) x <;> decide
    · rw [hy]
      have h1 : U k x (-x + 1) = U k (x - 1) (-x) := by
        rw [← hsy x (-x + 1), show -(-x + 1) = x - 1 by omega, ← hss x (x - 1), ← hsy (x - 1) x]
      have h2 : U k x (-x - 1) = U k (x + 1) (-x) := by
        rw [← hsy x (-x - 1), show -(-x - 1) = x + 1 by omega, ← hss x (x + 1), ← hsy (x + 1) x]
      rw [h1, h2]
      cases U k (x + 1) (-x) <;> cases U k (x - 1) (-x) <;> decide

private lemma U_axis_true (k : ℕ) : ∀ x : ℤ, x.natAbs ≤ k → U k x 0 = true := by
  induction k with
  | zero =>
    intro x hx
    have : x = 0 := by omega
    subst this; rfl
  | succ k ih =>
    intro x hx
    by_cases hle : x.natAbs ≤ k
    · exact U_mono k x 0 (ih x hle)
    · have heq : x.natAbs = k + 1 := by omega
      simp only [U, stepUW]
      rcases Int.natAbs_eq_iff.mp heq with rfl | rfl
      · have h0 : U k ((k + 1 : ℕ) : ℤ) 0 = false := U_support k _ 0 (by omega)
        have h1 : U k (((k + 1 : ℕ) : ℤ) + 1) 0 = false := U_support k _ 0 (by omega)
        have h2 : U k (((k + 1 : ℕ) : ℤ) - 1) 0 = true := ih _ (by omega)
        have h3 : U k ((k + 1 : ℕ) : ℤ) 1 = false := U_support k _ 1 (by omega)
        have h4 : U k ((k + 1 : ℕ) : ℤ) (-1) = false := U_support k _ (-1) (by omega)
        simp only [zero_add, zero_sub]
        rw [h0, h1, h2, h3, h4]
        rfl
      · have h0 : U k (-((k + 1 : ℕ) : ℤ)) 0 = false := U_support k _ 0 (by omega)
        have h1 : U k (-((k + 1 : ℕ) : ℤ) + 1) 0 = true := ih _ (by omega)
        have h2 : U k (-((k + 1 : ℕ) : ℤ) - 1) 0 = false := U_support k _ 0 (by omega)
        have h3 : U k (-((k + 1 : ℕ) : ℤ)) 1 = false := U_support k _ 1 (by omega)
        have h4 : U k (-((k + 1 : ℕ) : ℤ)) (-1) = false := U_support k _ (-1) (by omega)
        simp only [zero_add, zero_sub]
        rw [h0, h1, h2, h3, h4]
        rfl

/-! ### Part 2: `Combine` doubling law and no-degree-3 invariant for `U` -/

private def Combine (M : ℕ) (g_in g_out : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  if x.natAbs + y.natAbs < M then g_in x y
  else if x.natAbs = y.natAbs then false
  else if y.natAbs < x.natAbs then
    if 0 < x then g_out (x - M) y else g_out (x + M) y
  else
    if 0 < y then g_out x (y - M) else g_out x (y + M)

private lemma Combine_symm {M : ℕ} {g_in g_out : ℤ → ℤ → Bool}
    (hin : (∀ x y : ℤ, g_in (-x) y = g_in x y) ∧
           (∀ x y : ℤ, g_in x (-y) = g_in x y) ∧
           (∀ x y : ℤ, g_in y x = g_in x y))
    (hout : (∀ x y : ℤ, g_out (-x) y = g_out x y) ∧
            (∀ x y : ℤ, g_out x (-y) = g_out x y) ∧
            (∀ x y : ℤ, g_out y x = g_out x y)) :
    (∀ x y : ℤ, Combine M g_in g_out (-x) y = Combine M g_in g_out x y) ∧
    (∀ x y : ℤ, Combine M g_in g_out x (-y) = Combine M g_in g_out x y) ∧
    (∀ x y : ℤ, Combine M g_in g_out y x = Combine M g_in g_out x y) := by
  obtain ⟨hinx, hiny, hins⟩ := hin
  obtain ⟨houtx, houty, houts⟩ := hout
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    simp only [Combine, Int.natAbs_neg]
    by_cases hlt : x.natAbs + y.natAbs < M
    · simp only [if_pos hlt]; exact hinx x y
    · simp only [if_neg hlt]
      by_cases heq : x.natAbs = y.natAbs
      · simp only [if_pos heq]
      · simp only [if_neg heq]
        by_cases hylt : y.natAbs < x.natAbs
        · simp only [if_pos hylt]
          by_cases hx : 0 < x
          · simp only [if_pos hx, if_neg (by omega : ¬ (0 < -x))]
            rw [← houtx (x - M) y]; congr 1; omega
          · simp only [if_neg hx, if_pos (by omega : 0 < -x)]
            rw [← houtx (x + M) y]; congr 1; omega
        · simp only [if_neg hylt]
          by_cases hy : 0 < y
          · simp only [if_pos hy]; exact houtx x (y - M)
          · simp only [if_neg hy]; exact houtx x (y + M)
  · intro x y
    simp only [Combine, Int.natAbs_neg]
    by_cases hlt : x.natAbs + y.natAbs < M
    · simp only [if_pos hlt]; exact hiny x y
    · simp only [if_neg hlt]
      by_cases heq : x.natAbs = y.natAbs
      · simp only [if_pos heq]
      · simp only [if_neg heq]
        by_cases hylt : y.natAbs < x.natAbs
        · simp only [if_pos hylt]
          by_cases hx : 0 < x
          · simp only [if_pos hx]; exact houty (x - M) y
          · simp only [if_neg hx]; exact houty (x + M) y
        · simp only [if_neg hylt]
          by_cases hy : 0 < y
          · simp only [if_pos hy, if_neg (by omega : ¬ (0 < -y))]
            rw [← houty x (y - M)]; congr 1; omega
          · simp only [if_neg hy, if_pos (by omega : 0 < -y)]
            rw [← houty x (y + M)]; congr 1; omega
  · intro x y
    simp only [Combine]
    rw [add_comm y.natAbs x.natAbs]
    by_cases hlt : x.natAbs + y.natAbs < M
    · simp only [if_pos hlt]; exact hins x y
    · simp only [if_neg hlt]
      by_cases heq : x.natAbs = y.natAbs
      · simp only [heq, ↓reduceIte]
      · simp only [if_neg heq, if_neg (Ne.symm heq)]
        by_cases hylt : y.natAbs < x.natAbs
        · simp only [if_pos hylt, if_neg (by omega : ¬ (x.natAbs < y.natAbs))]
          by_cases hx : 0 < x
          · simp only [if_pos hx]; exact houts (x - M) y
          · simp only [if_neg hx]; exact houts (x + M) y
        · simp only [if_neg hylt, if_pos (by omega : x.natAbs < y.natAbs)]
          by_cases hy : 0 < y
          · simp only [if_pos hy]; exact houts x (y - M)
          · simp only [if_neg hy]; exact houts x (y + M)

private lemma symm_reduce {f g : ℤ → ℤ → Bool}
    (hf : (∀ x y : ℤ, f (-x) y = f x y) ∧ (∀ x y : ℤ, f x (-y) = f x y) ∧ (∀ x y : ℤ, f y x = f x y))
    (hg : (∀ x y : ℤ, g (-x) y = g x y) ∧ (∀ x y : ℤ, g x (-y) = g x y) ∧ (∀ x y : ℤ, g y x = g x y))
    (hcone : ∀ x y : ℤ, 0 < x → y.natAbs < x.natAbs → f x y = g x y)
    (hdiag : ∀ x y : ℤ, x.natAbs = y.natAbs → f x y = g x y) :
    ∀ x y : ℤ, f x y = g x y := by
  intro x y
  by_cases hxy : x.natAbs = y.natAbs
  · exact hdiag x y hxy
  · by_cases hlt : y.natAbs < x.natAbs
    · by_cases hx : 0 < x
      · exact hcone x y hx hlt
      · rw [← hf.1 x y, ← hg.1 x y]
        exact hcone (-x) y (by omega) (by simp only [Int.natAbs_neg]; omega)
    · rw [← hf.2.2 x y, ← hg.2.2 x y]
      by_cases hy : 0 < y
      · exact hcone y x hy (by omega)
      · rw [← hf.1 y x, ← hg.1 y x]
        exact hcone (-y) x (by omega) (by simp only [Int.natAbs_neg]; omega)

private lemma Combine_right_cone {M : ℕ} {g_in g_out : ℤ → ℤ → Bool} {x y : ℤ}
    (hge : M ≤ x.natAbs + y.natAbs) (hx : 0 < x) (hlt : y.natAbs < x.natAbs) :
    Combine M g_in g_out x y = g_out (x - M) y := by
  simp only [Combine, if_neg (by omega : ¬ (x.natAbs + y.natAbs < M)),
    if_neg (by omega : ¬ (x.natAbs = y.natAbs)), if_pos hlt, if_pos hx]

private def nbrSum (f : ℤ → ℤ → Bool) (x y : ℤ) : ℕ :=
  (f (x + 1) y).toNat + (f (x - 1) y).toNat + (f x (y + 1)).toNat + (f x (y - 1)).toNat

private lemma nbrSum_symm {f : ℤ → ℤ → Bool}
    (hf : (∀ x y : ℤ, f (-x) y = f x y) ∧ (∀ x y : ℤ, f x (-y) = f x y) ∧ (∀ x y : ℤ, f y x = f x y)) :
    (∀ x y : ℤ, nbrSum f (-x) y = nbrSum f x y) ∧
    (∀ x y : ℤ, nbrSum f x (-y) = nbrSum f x y) ∧
    (∀ x y : ℤ, nbrSum f y x = nbrSum f x y) := by
  obtain ⟨hx, hy, hs⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · intro x y; unfold nbrSum
    have h1 : f (-x + 1) y = f (x - 1) y := by rw [← hx (x - 1) y]; congr 1; omega
    have h2 : f (-x - 1) y = f (x + 1) y := by rw [← hx (x + 1) y]; congr 1; omega
    rw [h1, h2, hx, hx]; omega
  · intro x y; unfold nbrSum
    have h3 : f x (-y + 1) = f x (y - 1) := by rw [← hy x (y - 1)]; congr 1; omega
    have h4 : f x (-y - 1) = f x (y + 1) := by rw [← hy x (y + 1)]; congr 1; omega
    rw [hy, hy, h3, h4]; omega
  · intro x y; unfold nbrSum
    rw [hs x (y + 1), hs x (y - 1), hs (x + 1) y, hs (x - 1) y]; omega

private lemma U_doubling_step {M : ℕ} (hM2 : 2 ≤ M)
    (hbdy : ∀ x y : ℤ, x.natAbs + y.natAbs = M - 1 → U (M - 1) x y = true)
    (hfrozen : ∀ x y : ℤ, x.natAbs + y.natAbs < M → U M x y = U (M - 1) x y) :
    ∀ r : ℕ, r < M → ∀ x y : ℤ, U (M + r) x y = Combine M (U (M - 1)) (U r) x y := by
  intro r
  induction r with
  | zero =>
    intro _
    have hcsymm := Combine_symm (M := M) (U_symm (M - 1)) (U_symm 0)
    apply symm_reduce (U_symm (M + 0)) hcsymm
    · intro x y hx hlt
      by_cases hin : x.natAbs + y.natAbs < M
      · simp only [add_zero, Combine, if_pos hin]; exact hfrozen x y hin
      · have hge : M ≤ x.natAbs + y.natAbs := by omega
        rw [add_zero, Combine_right_cone hge hx hlt]
        by_cases hbd : x.natAbs + y.natAbs = M
        · by_cases hy : y = 0
          · subst hy
            have hxM : x = M := by omega
            subst hxM
            rw [show (M : ℤ) - M = 0 by ring, U_origin_true 0]
            exact U_axis_true M M (by omega)
          · have hrhs : U 0 (x - M) y = false := U_diag_false 0 (x - M) y (by omega) (by omega)
            rw [hrhs]
            have hMsucc : M = (M - 1) + 1 := by omega
            rw [hMsucc]
            simp only [U, stepUW]
            have h0 : U (M - 1) x y = false := U_support (M - 1) x y (by omega)
            have hL : U (M - 1) (x - 1) y = true := hbdy (x - 1) y (by omega)
            by_cases hypos : 0 < y
            · have hD : U (M - 1) x (y - 1) = true := hbdy x (y - 1) (by omega)
              simp only [h0, hL, hD, Bool.false_or, Bool.toNat_true]
              apply decide_eq_false; omega
            · have hU : U (M - 1) x (y + 1) = true := hbdy x (y + 1) (by omega)
              simp only [h0, hL, hU, Bool.false_or, Bool.toNat_true]
              apply decide_eq_false; omega
        · rw [U_support M x y (by omega), U_support 0 (x - M) y (by omega)]
    · intro x y hxy
      by_cases hx0 : x = 0
      · subst hx0
        have hy0 : y = 0 := by omega
        subst hy0
        rw [U_origin_true]; simp only [Combine, Int.natAbs_zero, add_zero, if_pos (by omega : 0 < M)]
        exact (U_origin_true (M - 1)).symm
      · rw [U_diag_false (M + 0) x y hx0 hxy]
        by_cases hin : x.natAbs + y.natAbs < M
        · simp only [Combine, if_pos hin]; exact (U_diag_false (M - 1) x y hx0 hxy).symm
        · simp only [Combine, if_neg hin, if_pos hxy]
  | succ r ihr =>
    intro hrM
    have hcur := ihr (by omega)
    have hcsymm := Combine_symm (M := M) (U_symm (M - 1)) (U_symm (r + 1))
    apply symm_reduce (U_symm (M + (r + 1))) hcsymm
    · intro x y hx hlt
      by_cases hin : x.natAbs + y.natAbs < M
      · simp only [Combine, if_pos hin]
        by_cases hbd : x.natAbs + y.natAbs = M - 1
        · rw [hbdy x y hbd]
          have hprev : U (M + r) x y = true := by
            rw [hcur x y]; simp only [Combine, if_pos hin]; exact hbdy x y hbd
          exact U_mono (M + r) x y hprev
        · have hlt2 : x.natAbs + y.natAbs < M - 1 := by omega
          rw [show M + (r + 1) = (M + r) + 1 by omega]
          change stepUW (U (M + r)) x y = U (M - 1) x y
          have heq0 : U (M + r) x y = U (M - 1) x y := by rw [hcur]; simp [Combine, hin]
          have heq1 : U (M + r) (x + 1) y = U (M - 1) (x + 1) y := by
            rw [hcur]; simp only [Combine, if_pos (by omega : (x + 1).natAbs + y.natAbs < M)]
          have heq2 : U (M + r) (x - 1) y = U (M - 1) (x - 1) y := by
            rw [hcur]; simp only [Combine, if_pos (by omega : (x - 1).natAbs + y.natAbs < M)]
          have heq3 : U (M + r) x (y + 1) = U (M - 1) x (y + 1) := by
            rw [hcur]; simp only [Combine, if_pos (by omega : x.natAbs + (y + 1).natAbs < M)]
          have heq4 : U (M + r) x (y - 1) = U (M - 1) x (y - 1) := by
            rw [hcur]; simp only [Combine, if_pos (by omega : x.natAbs + (y - 1).natAbs < M)]
          rw [stepUW_congr' heq0 heq1 heq2 heq3 heq4]
          have hstep' : stepUW (U (M - 1)) x y = U M x y := by
            have hMsucc : (M - 1) + 1 = M := by omega
            change U ((M - 1) + 1) x y = U M x y
            rw [hMsucc]
          rw [hstep', hfrozen x y hin]
      · have hge : M ≤ x.natAbs + y.natAbs := by omega
        rw [Combine_right_cone hge hx hlt]
        by_cases hbd : x.natAbs + y.natAbs = M
        · by_cases hy : y = 0
          · subst hy
            have hxM : x = M := by omega
            subst hxM
            rw [show (M : ℤ) - M = 0 by ring, U_origin_true (r + 1)]
            exact U_axis_true (M + (r + 1)) M (by omega)
          · rw [U_diag_false (r + 1) (x - M) y (by omega) (by omega)]
            rw [show M + (r + 1) = (M + r) + 1 by omega]
            simp only [U, stepUW]
            have h0 : U (M + r) x y = false := by
              rw [hcur, Combine_right_cone hge hx hlt]
              exact U_diag_false r (x - M) y (by omega) (by omega)
            have hL : U (M + r) (x - 1) y = true := by
              rw [hcur]; simp only [Combine, if_pos (by omega : (x - 1).natAbs + y.natAbs < M)]
              exact hbdy (x - 1) y (by omega)
            by_cases hypos : 0 < y
            · have hD : U (M + r) x (y - 1) = true := by
                rw [hcur]; simp only [Combine, if_pos (by omega : x.natAbs + (y - 1).natAbs < M)]
                exact hbdy x (y - 1) (by omega)
              simp only [h0, hL, hD, Bool.false_or, Bool.toNat_true]
              apply decide_eq_false; omega
            · have hU : U (M + r) x (y + 1) = true := by
                rw [hcur]; simp only [Combine, if_pos (by omega : x.natAbs + (y + 1).natAbs < M)]
                exact hbdy x (y + 1) (by omega)
              simp only [h0, hL, hU, Bool.false_or, Bool.toNat_true]
              apply decide_eq_false; omega
        · have hgt : M < x.natAbs + y.natAbs := by omega
          rw [show M + (r + 1) = (M + r) + 1 by omega]
          change stepUW (U (M + r)) x y = stepUW (U r) (x - M) y
          have hnbr : ∀ u v : ℤ, M ≤ u.natAbs + v.natAbs → 0 < u → v.natAbs ≤ u.natAbs →
              U (M + r) u v = U r (u - M) v := by
            intro u v hge' hu hle'
            rw [hcur u v]
            rcases lt_or_eq_of_le hle' with hlt' | heq'
            · exact Combine_right_cone hge' hu hlt'
            · simp only [Combine, if_neg (by omega : ¬ (u.natAbs + v.natAbs < M)), if_pos heq'.symm]
              by_cases hsmall : 2 * u.natAbs = M
              · exact (U_diag_false r (u - M) v (by omega) (by omega)).symm
              · exact (U_support r (u - M) v (by omega)).symm
          have heq0 : U (M + r) x y = U r (x - M) y := hnbr x y hge hx (by omega)
          have heq1 : U (M + r) (x + 1) y = U r (x - M + 1) y := by
            rw [show x - M + 1 = (x + 1) - M by ring]
            exact hnbr (x + 1) y (by omega) (by omega) (by omega)
          have heq2 : U (M + r) (x - 1) y = U r (x - M - 1) y := by
            rw [show x - M - 1 = (x - 1) - M by ring]
            exact hnbr (x - 1) y (by omega) (by omega) (by omega)
          have heq3 : U (M + r) x (y + 1) = U r (x - M) (y + 1) :=
            hnbr x (y + 1) (by omega) hx (by omega)
          have heq4 : U (M + r) x (y - 1) = U r (x - M) (y - 1) :=
            hnbr x (y - 1) (by omega) hx (by omega)
          exact stepUW_congr' heq0 heq1 heq2 heq3 heq4
    · intro x y hxy
      by_cases hx0 : x = 0
      · subst hx0
        have hy0 : y = 0 := by omega
        subst hy0
        rw [U_origin_true]; simp only [Combine, Int.natAbs_zero, add_zero, if_pos (by omega : 0 < M)]
        exact (U_origin_true (M - 1)).symm
      · rw [U_diag_false (M + (r + 1)) x y hx0 hxy]
        by_cases hin : x.natAbs + y.natAbs < M
        · simp only [Combine, if_pos hin]; exact (U_diag_false (M - 1) x y hx0 hxy).symm
        · simp only [Combine, if_neg hin, if_pos hxy]

private lemma U_master (m : ℕ) (hm : 1 ≤ m) :
    (∀ x y : ℤ, x.natAbs + y.natAbs = 2 ^ m - 1 → U (2 ^ m - 1) x y = true) ∧
    (∀ x y : ℤ, x.natAbs + y.natAbs < 2 ^ m → U (2 ^ m) x y = U (2 ^ m - 1) x y) ∧
    (∀ r : ℕ, r < 2 ^ m → ∀ x y : ℤ,
      U (2 ^ m + r) x y = Combine (2 ^ m) (U (2 ^ m - 1)) (U r) x y) := by
  induction m with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      have hbdy1 : ∀ x y : ℤ, x.natAbs + y.natAbs = 1 → U 1 x y = true := by
        intro x y h
        have hbox : ∀ u ∈ Finset.Icc (-1 : ℤ) 1, ∀ v ∈ Finset.Icc (-1 : ℤ) 1,
            u.natAbs + v.natAbs = 1 → U 1 u v = true := by decide
        exact hbox x (Finset.mem_Icc.mpr (by omega)) y (Finset.mem_Icc.mpr (by omega)) h
      have hfrz1 : ∀ x y : ℤ, x.natAbs + y.natAbs < 2 → U 2 x y = U 1 x y := by
        intro x y h
        have hbox : ∀ u ∈ Finset.Icc (-1 : ℤ) 1, ∀ v ∈ Finset.Icc (-1 : ℤ) 1,
            u.natAbs + v.natAbs < 2 → U 2 u v = U 1 u v := by decide
        exact hbox x (Finset.mem_Icc.mpr (by omega)) y (Finset.mem_Icc.mpr (by omega)) h
      refine ⟨hbdy1, hfrz1, U_doubling_step (M := 2) le_rfl hbdy1 hfrz1⟩
    | succ k =>
      obtain ⟨ih_bdy, ih_frz, ih_dbl⟩ := ih (by omega)
      set M : ℕ := 2 ^ (k + 1)
      have hM2 : 2 ≤ M := by
        have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (show 1 ≤ k + 1 by omega)
        simpa [M] using this
      have h2M : 2 ^ (k + 1 + 1) = 2 * M := by simp [M]; ring
      have h2Msub : 2 * M - 1 = M + (M - 1) := by omega
      have hcomb_top : ∀ x y : ℤ, U (2 * M - 1) x y = Combine M (U (M - 1)) (U (M - 1)) x y := by
        rw [h2Msub]; exact ih_dbl (M - 1) (by omega)
      have hbdy_next : ∀ x y : ℤ, x.natAbs + y.natAbs = 2 * M - 1 → U (2 * M - 1) x y = true := by
        intro x y hsum
        rw [hcomb_top x y]
        simp only [Combine, if_neg (by omega : ¬ (x.natAbs + y.natAbs < M)),
          if_neg (by omega : ¬ (x.natAbs = y.natAbs))]
        split_ifs with hylt hx hy
        · exact ih_bdy (x - M) y (by omega)
        · exact ih_bdy (x + M) y (by omega)
        · exact ih_bdy x (y - M) (by omega)
        · exact ih_bdy x (y + M) (by omega)
      have hfrz_next : ∀ x y : ℤ, x.natAbs + y.natAbs < 2 * M → U (2 * M) x y = U (2 * M - 1) x y := by
        intro x y hlt
        have hstep : U (2 * M) x y = stepUW (U (2 * M - 1)) x y := by
          rw [show 2 * M = (2 * M - 1) + 1 by omega]; rfl
        by_cases ht : U (2 * M - 1) x y = true
        · rw [ht, hstep]; simp [stepUW, ht]
        · have hf : U (2 * M - 1) x y = false := Bool.eq_false_iff.mpr ht
          rw [hf]
          have hnot_eq : ∀ u v : ℤ, u.natAbs + v.natAbs < 2 * M → U (2 * M - 1) u v = false →
              (0 < u → v.natAbs < u.natAbs → U (2 * M) u v = false) := by
            intro u v hlt' hfu hu hylt
            by_cases hin : u.natAbs + v.natAbs < M
            · have hlt2 : u.natAbs + v.natAbs < M - 1 := by
                by_contra hge
                have hbd : u.natAbs + v.natAbs = M - 1 := by omega
                rw [hcomb_top, Combine, if_pos hin, ih_bdy u v hbd] at hfu; cases hfu
              rw [show 2 * M = (2 * M - 1) + 1 by omega]
              change stepUW (U (2 * M - 1)) u v = false
              have heq0 : U (2 * M - 1) u v = U (M - 1) u v := by rw [hcomb_top]; simp [Combine, hin]
              have heq1 : U (2 * M - 1) (u + 1) v = U (M - 1) (u + 1) v := by
                rw [hcomb_top]; simp only [Combine, if_pos (by omega : (u + 1).natAbs + v.natAbs < M)]
              have heq2 : U (2 * M - 1) (u - 1) v = U (M - 1) (u - 1) v := by
                rw [hcomb_top]; simp only [Combine, if_pos (by omega : (u - 1).natAbs + v.natAbs < M)]
              have heq3 : U (2 * M - 1) u (v + 1) = U (M - 1) u (v + 1) := by
                rw [hcomb_top]; simp only [Combine, if_pos (by omega : u.natAbs + (v + 1).natAbs < M)]
              have heq4 : U (2 * M - 1) u (v - 1) = U (M - 1) u (v - 1) := by
                rw [hcomb_top]; simp only [Combine, if_pos (by omega : u.natAbs + (v - 1).natAbs < M)]
              rw [stepUW_congr' heq0 heq1 heq2 heq3 heq4]
              have hstep' : stepUW (U (M - 1)) u v = U M u v := by
                have hMsucc : (M - 1) + 1 = M := by omega
                change U ((M - 1) + 1) u v = U M u v
                rw [hMsucc]
              rw [hstep', ih_frz u v hin, ← heq0, hfu]
            · by_cases hbd : u.natAbs + v.natAbs = M
              · have hv : v ≠ 0 := by
                  intro hv0
                  subst hv0
                  have huM : u = M := by omega
                  subst huM
                  rw [hcomb_top, Combine_right_cone (by omega) (by omega) (by omega),
                    show (M : ℤ) - M = 0 by ring, U_origin_true] at hfu; cases hfu
                rw [show 2 * M = (2 * M - 1) + 1 by omega]
                simp only [U, stepUW, hfu, Bool.false_or]
                have hL : U (2 * M - 1) (u - 1) v = true := by
                  rw [hcomb_top]; simp only [Combine, if_pos (by omega : (u - 1).natAbs + v.natAbs < M)]
                  exact ih_bdy (u - 1) v (by omega)
                by_cases hvpos : 0 < v
                · have hD : U (2 * M - 1) u (v - 1) = true := by
                    rw [hcomb_top]; simp only [Combine, if_pos (by omega : u.natAbs + (v - 1).natAbs < M)]
                    exact ih_bdy u (v - 1) (by omega)
                  simp only [hL, hD, Bool.toNat_true]; apply decide_eq_false; omega
                · have hU : U (2 * M - 1) u (v + 1) = true := by
                    rw [hcomb_top]; simp only [Combine, if_pos (by omega : u.natAbs + (v + 1).natAbs < M)]
                    exact ih_bdy u (v + 1) (by omega)
                  simp only [hL, hU, Bool.toNat_true]; apply decide_eq_false; omega
              · have hgt : M < u.natAbs + v.natAbs := by omega
                have hlt_in : (u - M).natAbs + v.natAbs < M := by omega
                rw [show 2 * M = (2 * M - 1) + 1 by omega]
                change stepUW (U (2 * M - 1)) u v = false
                have hnbr : ∀ a b : ℤ, M ≤ a.natAbs + b.natAbs → 0 < a → b.natAbs ≤ a.natAbs →
                    U (2 * M - 1) a b = U (M - 1) (a - M) b := by
                  intro a b hge' ha hle'
                  rw [hcomb_top a b]
                  rcases lt_or_eq_of_le hle' with hlt'' | heq'
                  · exact Combine_right_cone hge' ha hlt''
                  · simp only [Combine, if_neg (by omega : ¬ (a.natAbs + b.natAbs < M)), if_pos heq'.symm]
                    by_cases hsmall : 2 * a.natAbs = M
                    · exact (U_diag_false (M - 1) (a - M) b (by omega) (by omega)).symm
                    · exact (U_support (M - 1) (a - M) b (by omega)).symm
                have heq0 : U (2 * M - 1) u v = U (M - 1) (u - M) v := hnbr u v (by omega) hu (by omega)
                have heq1 : U (2 * M - 1) (u + 1) v = U (M - 1) (u - M + 1) v := by
                  rw [show u - M + 1 = (u + 1) - M by ring]
                  exact hnbr (u + 1) v (by omega) (by omega) (by omega)
                have heq2 : U (2 * M - 1) (u - 1) v = U (M - 1) (u - M - 1) v := by
                  rw [show u - M - 1 = (u - 1) - M by ring]
                  exact hnbr (u - 1) v (by omega) (by omega) (by omega)
                have heq3 : U (2 * M - 1) u (v + 1) = U (M - 1) (u - M) (v + 1) :=
                  hnbr u (v + 1) (by omega) hu (by omega)
                have heq4 : U (2 * M - 1) u (v - 1) = U (M - 1) (u - M) (v - 1) :=
                  hnbr u (v - 1) (by omega) hu (by omega)
                rw [stepUW_congr' heq0 heq1 heq2 heq3 heq4]
                have hstep' : stepUW (U (M - 1)) (u - M) v = U M (u - M) v := by
                  have hMsucc : (M - 1) + 1 = M := by omega
                  change U ((M - 1) + 1) (u - M) v = U M (u - M) v
                  exact congrFun (congrFun (congrArg U hMsucc) (u - M)) v
                rw [hstep', ih_frz (u - M) v hlt_in, ← heq0, hfu]
          by_cases hxy : x.natAbs = y.natAbs
          · have hx0 : x ≠ 0 := by
              intro hx0
              subst hx0
              have hy0 : y = 0 := by omega
              subst hy0
              rw [U_origin_true] at hf
              cases hf
            exact U_diag_false (2 * M) x y hx0 hxy
          · by_cases hylt : y.natAbs < x.natAbs
            · by_cases hx : 0 < x
              · exact hnot_eq x y hlt hf hx hylt
              · rw [← (U_symm (2 * M)).1 x y]
                exact hnot_eq (-x) y (by simp only [Int.natAbs_neg]; exact hlt)
                  (by rw [(U_symm (2 * M - 1)).1]; exact hf) (by omega) (by simp only [Int.natAbs_neg]; exact hylt)
            · rw [← (U_symm (2 * M)).2.2 x y]
              by_cases hy : 0 < y
              · exact hnot_eq y x (by omega) (by rw [(U_symm (2 * M - 1)).2.2]; exact hf) hy (by omega)
              · rw [← (U_symm (2 * M)).1 y x]
                exact hnot_eq (-y) x (by simp only [Int.natAbs_neg]; omega)
                  (by rw [(U_symm (2 * M - 1)).1, (U_symm (2 * M - 1)).2.2]; exact hf)
                  (by omega) (by simp only [Int.natAbs_neg]; omega)
      rw [h2M]
      exact ⟨hbdy_next, hfrz_next, U_doubling_step (by omega) hbdy_next hfrz_next⟩

private lemma U_no_deg3 : ∀ k : ℕ, ∀ x y : ℤ, U k x y = true → nbrSum (U k) x y ≠ 3 := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro x y hxy
    rcases k with _ | _ | k
    · have h0 : x = 0 ∧ y = 0 := by simp [U] at hxy; exact hxy
      rcases h0 with ⟨rfl, rfl⟩; decide
    · have hbox : ∀ u ∈ Finset.Icc (-1 : ℤ) 1, ∀ v ∈ Finset.Icc (-1 : ℤ) 1,
          U 1 u v = true → nbrSum (U 1) u v ≠ 3 := by decide
      have hle : x.natAbs + y.natAbs ≤ 1 := by
        by_contra hgt; rw [U_support 1 x y (by omega)] at hxy; cases hxy
      exact hbox x (Finset.mem_Icc.mpr (by omega)) y (Finset.mem_Icc.mpr (by omega)) hxy
    · set n := k + 2
      set m := Nat.log 2 n
      have hm1 : 1 ≤ m := by
        have : 2 ^ 1 ≤ n := by omega
        exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr this
      set M := 2 ^ m
      have hMle : M ≤ n := Nat.pow_log_le_self 2 (by omega)
      have hlt2M : n < 2 * M := by
        have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
        simpa [M, pow_succ, mul_comm] using this
      set r := n - M
      have hrM : r < M := by omega
      have hneq : n = M + r := by omega
      obtain ⟨hbdy, _, hdbl⟩ := U_master m hm1
      have hcur : ∀ u v : ℤ, U n u v = Combine M (U (M - 1)) (U r) u v := by
        rw [hneq]; exact hdbl r hrM
      have hM2 : 2 ≤ M := by
        have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hm1; simpa [M] using this
      have hcone : ∀ u v : ℤ, 0 < u → v.natAbs < u.natAbs → U n u v = true → nbrSum (U n) u v ≠ 3 := by
        intro u v hu hylt huv
        by_cases hin : u.natAbs + v.natAbs < M
        · by_cases hbd : u.natAbs + v.natAbs = M - 1
          · by_cases hv0 : v = 0
            · subst hv0
              have huM : u = (M : ℤ) - 1 := by omega
              subst huM
              have h1 : U n ((M : ℤ) - 1 + 1) 0 = true := by
                rw [hcur, Combine_right_cone (by omega) (by omega) (by omega),
                  show (M : ℤ) - 1 + 1 - M = 0 by ring, U_origin_true]
              have h2 : U n ((M : ℤ) - 1 - 1) 0 = true := by
                rw [hcur]; simp only [Combine, Int.natAbs_zero, add_zero, if_pos (by omega : ((M : ℤ) - 1 - 1).natAbs < M)]
                exact U_axis_true (M - 1) _ (by omega)
              have h3 : U n ((M : ℤ) - 1) 1 = false := by
                rw [hcur]
                by_cases hdiag : ((M : ℤ) - 1).natAbs = (1 : ℤ).natAbs
                · simp only [Combine, if_neg (by omega : ¬ (((M : ℤ) - 1).natAbs + (1 : ℤ).natAbs < M)), if_pos hdiag]
                · rw [Combine_right_cone (by omega) (by omega) (by omega)]
                  exact U_diag_false r _ 1 (by omega) (by omega)
              have h4 : U n ((M : ℤ) - 1) (-1) = false := by
                rw [(U_symm n).2.1]; exact h3
              simp only [nbrSum, h1, h2, h3, h4, zero_add, zero_sub]; decide
            · have h1 : U n (u + 1) v = false := by
                rw [hcur, Combine_right_cone (by omega) (by omega) (by omega)]
                exact U_diag_false r _ v (by omega) (by omega)
              by_cases hvpos : 0 < v
              · have h3 : U n u (v + 1) = false := by
                  rw [hcur]
                  by_cases hd : u.natAbs = (v + 1).natAbs
                  · simp only [Combine, if_neg (by omega : ¬ (u.natAbs + (v + 1).natAbs < M)), if_pos hd]
                  · rw [Combine_right_cone (by omega) (by omega) (by omega)]
                    exact U_diag_false r _ _ (by omega) (by omega)
                simp only [nbrSum, h1, h3, Bool.toNat_false]
                have hb1 := Bool.toNat_le (U n (u - 1) v)
                have hb2 := Bool.toNat_le (U n u (v - 1))
                omega
              · have h4 : U n u (v - 1) = false := by
                  rw [hcur]
                  by_cases hd : u.natAbs = (v - 1).natAbs
                  · simp only [Combine, if_neg (by omega : ¬ (u.natAbs + (v - 1).natAbs < M)), if_pos hd]
                  · rw [Combine_right_cone (by omega) (by omega) (by omega)]
                    exact U_diag_false r _ _ (by omega) (by omega)
                simp only [nbrSum, h1, h4, Bool.toNat_false]
                have hb1 := Bool.toNat_le (U n (u - 1) v)
                have hb2 := Bool.toNat_le (U n u (v + 1))
                omega
          · have hlt2 : u.natAbs + v.natAbs < M - 1 := by omega
            have hsum_eq : nbrSum (U n) u v = nbrSum (U (M - 1)) u v := by
              unfold nbrSum
              rw [hcur (u + 1) v, hcur (u - 1) v, hcur u (v + 1), hcur u (v - 1)]
              simp only [Combine, if_pos (by omega : (u + 1).natAbs + v.natAbs < M),
                if_pos (by omega : (u - 1).natAbs + v.natAbs < M),
                if_pos (by omega : u.natAbs + (v + 1).natAbs < M),
                if_pos (by omega : u.natAbs + (v - 1).natAbs < M)]
            rw [hsum_eq]
            have huv' : U (M - 1) u v = true := by rw [hcur] at huv; simp only [Combine, if_pos hin] at huv; exact huv
            exact ih (M - 1) (by omega) u v huv'
        · by_cases hbd : u.natAbs + v.natAbs = M
          · by_cases hv0 : v = 0
            · subst hv0
              have huM : u = M := by omega
              subst huM
              have hL : U n ((M : ℤ) - 1) 0 = true := by
                rw [hcur]; simp only [Combine, Int.natAbs_zero, add_zero, if_pos (by omega : ((M : ℤ) - 1).natAbs < M)]
                exact hbdy _ 0 (by omega)
              have hR : U n ((M : ℤ) + 1) 0 = U r 1 0 := by
                rw [hcur, Combine_right_cone (by omega) (by omega) (by omega)]; congr 1; omega
              have hU : U n M 1 = U r 1 0 := by
                rw [hcur, Combine_right_cone (by omega) (by omega) (by omega),
                  show (M : ℤ) - M = 0 by ring, (U_symm r).2.2]
              have hD : U n M (-1) = U r 1 0 := by
                rw [hcur, Combine_right_cone (by omega) (by omega) (by omega),
                  show (M : ℤ) - M = 0 by ring, (U_symm r).2.1, (U_symm r).2.2]
              simp only [nbrSum, zero_add, zero_sub, hL, hR, hU, hD]
              cases U r 1 0 <;> decide
            · exfalso
              rw [hcur, Combine_right_cone (by omega) hu hylt, U_diag_false r (u - M) v (by omega) (by omega)] at huv
              cases huv
          · have hgt : M < u.natAbs + v.natAbs := by omega
            have hnbr : ∀ a b : ℤ, M ≤ a.natAbs + b.natAbs → 0 < a → b.natAbs ≤ a.natAbs →
                U n a b = U r (a - M) b := by
              intro a b hge' ha hle'
              rw [hcur a b]
              rcases lt_or_eq_of_le hle' with hlt' | heq'
              · exact Combine_right_cone hge' ha hlt'
              · simp only [Combine, if_neg (by omega : ¬ (a.natAbs + b.natAbs < M)), if_pos heq'.symm]
                by_cases hsmall : 2 * a.natAbs = M
                · exact (U_diag_false r (a - M) b (by omega) (by omega)).symm
                · exact (U_support r (a - M) b (by omega)).symm
            have hsum_eq : nbrSum (U n) u v = nbrSum (U r) (u - M) v := by
              unfold nbrSum
              rw [hnbr (u + 1) v (by omega) (by omega) (by omega),
                hnbr (u - 1) v (by omega) (by omega) (by omega),
                hnbr u (v + 1) (by omega) hu (by omega),
                hnbr u (v - 1) (by omega) hu (by omega)]
              rw [show (u + 1) - M = u - M + 1 by ring, show (u - 1) - M = u - M - 1 by ring]
            rw [hsum_eq]
            have huv' : U r (u - M) v = true := by
              rw [hcur, Combine_right_cone (by omega) hu hylt] at huv; exact huv
            exact ih r (by omega) (u - M) v huv'
      by_cases hxy_eq : x.natAbs = y.natAbs
      · have hx0 : x = 0 := by
          by_contra hx0; rw [U_diag_false n x y hx0 hxy_eq] at hxy; cases hxy
        subst hx0
        have hy0 : y = 0 := by omega
        subst hy0
        have h1 : U n 1 0 = true := U_axis_true n 1 (by omega)
        have h2 : U n (-1) 0 = true := by rw [(U_symm n).1]; exact h1
        have h3 : U n 0 1 = true := by rw [(U_symm n).2.2]; exact h1
        have h4 : U n 0 (-1) = true := by rw [(U_symm n).2.1]; exact h3
        simp only [nbrSum, zero_add, zero_sub, h1, h2, h3, h4]; decide
      · by_cases hylt : y.natAbs < x.natAbs
        · by_cases hx : 0 < x
          · exact hcone x y hx hylt hxy
          · rw [← (nbrSum_symm (U_symm n)).1 x y]
            exact hcone (-x) y (by omega) (by simp only [Int.natAbs_neg]; exact hylt)
              (by rw [(U_symm n).1]; exact hxy)
        · rw [← (nbrSum_symm (U_symm n)).2.2 x y]
          by_cases hy : 0 < y
          · exact hcone y x hy (by omega) (by rw [(U_symm n).2.2]; exact hxy)
          · rw [← (nbrSum_symm (U_symm n)).1 y x]
            exact hcone (-y) x (by omega) (by simp only [Int.natAbs_neg]; omega)
              (by rw [(U_symm n).1, (U_symm n).2.2]; exact hxy)

/-! ### Part 3: Exact reduction `cell 469 (2*k) = U k` and `cell 469 (2*k + 1) = !(U k)` -/

private def step469 (c n1 n2 n3 n4 : Bool) : Bool :=
  (469 : ℕ).testBit (c.toNat + 2 * (n1.toNat + n2.toNat + n3.toNat + n4.toNat))

private lemma step469_false (n1 n2 n3 n4 : Bool) : step469 false n1 n2 n3 n4 = true := by
  cases n1 <;> cases n2 <;> cases n3 <;> cases n4 <;> rfl

private lemma step469_true_ne3 (n1 n2 n3 n4 : Bool)
    (h : n1.toNat + n2.toNat + n3.toNat + n4.toNat ≠ 3) :
    step469 true n1 n2 n3 n4 = false := by
  cases n1 <;> cases n2 <;> cases n3 <;> cases n4 <;> simp_all [step469] <;> rfl

private lemma step469_not_eq_stepUW (c n1 n2 n3 n4 : Bool) :
    step469 (!c) (!n1) (!n2) (!n3) (!n4) =
      (c || decide (n1.toNat + n2.toNat + n3.toNat + n4.toNat = 1)) := by
  cases c <;> cases n1 <;> cases n2 <;> cases n3 <;> cases n4 <;> rfl

private lemma cell_469_eq_U (k : ℕ) :
    (∀ x y : ℤ, cell 469 (2 * k) x y = U k x y) ∧
    (∀ x y : ℤ, cell 469 (2 * k + 1) x y = !(U k x y)) := by
  have step_odd : ∀ (j : ℕ), (∀ x y : ℤ, cell 469 (2 * j) x y = U j x y) →
      ∀ x y : ℤ, cell 469 (2 * j + 1) x y = !(U j x y) := by
    intro j hj x y
    change step469 (cell 469 (2 * j) x y) (cell 469 (2 * j) (x + 1) y) (cell 469 (2 * j) (x - 1) y)
      (cell 469 (2 * j) x (y + 1)) (cell 469 (2 * j) x (y - 1)) = !(U j x y)
    rw [hj, hj, hj, hj, hj]
    cases hc : U j x y
    · exact step469_false _ _ _ _
    · exact step469_true_ne3 _ _ _ _ (U_no_deg3 j x y hc)
  induction k with
  | zero =>
    have h0 : ∀ x y : ℤ, cell 469 0 x y = U 0 x y := fun _ _ => rfl
    exact ⟨h0, step_odd 0 h0⟩
  | succ k ih =>
    obtain ⟨_, hodd⟩ := ih
    have heven : ∀ x y : ℤ, cell 469 (2 * (k + 1)) x y = U (k + 1) x y := by
      intro x y
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
      change step469 (cell 469 (2 * k + 1) x y) (cell 469 (2 * k + 1) (x + 1) y)
        (cell 469 (2 * k + 1) (x - 1) y) (cell 469 (2 * k + 1) x (y + 1))
        (cell 469 (2 * k + 1) x (y - 1)) = stepUW (U k) x y
      rw [hodd, hodd, hodd, hodd, hodd]
      exact step469_not_eq_stepUW _ _ _ _ _
    exact ⟨heven, step_odd (k + 1) heven⟩

/-! ### Part 4: Counting `U` at `2^m - 1`, `onCount`, closed form, recurrence, and g.f. -/

private noncomputable def UCount (g : ℤ → ℤ → Bool) (R : ℕ) : ℕ :=
  ∑ p ∈ Finset.Icc (-(R : ℤ)) (R : ℤ) ×ˢ Finset.Icc (-(R : ℤ)) (R : ℤ), (g p.1 p.2).toNat

private lemma UCount_widen {g : ℤ → ℤ → Bool} {R1 R2 : ℕ} (hle : R1 ≤ R2)
    (hsupp : ∀ x y : ℤ, R1 < x.natAbs + y.natAbs → g x y = false) :
    UCount g R2 = UCount g R1 := by
  unfold UCount
  symm
  apply Finset.sum_subset
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_Icc] at hp ⊢; omega
  · intro p _ hnot
    simp only [Finset.mem_product, Finset.mem_Icc] at hnot
    rw [hsupp p.1 p.2 (by omega)]; rfl

private lemma UCount_quadrant_decomp {M : ℕ} (hM : 1 ≤ M) {g : ℤ → ℤ → Bool}
    (hsymm : (∀ x y : ℤ, g (-x) y = g x y) ∧
             (∀ x y : ℤ, g x (-y) = g x y) ∧
             (∀ x y : ℤ, g y x = g x y))
    (h0 : g 0 0 = true)
    (hdiag : ∀ x y : ℤ, x ≠ 0 → x.natAbs = y.natAbs → g x y = false) :
    let S := Finset.Icc (-((M - 1 : ℕ) : ℤ)) ((M - 1 : ℕ) : ℤ) ×ˢ
             Finset.Icc (-((M - 1 : ℕ) : ℤ)) ((M - 1 : ℕ) : ℤ)
    let Q := ∑ p ∈ S.filter (fun p => p.1 < 0 ∧ p.2.natAbs < p.1.natAbs), (g p.1 p.2).toNat
    UCount g (M - 1) = 1 + 4 * Q := by
  intro S Q
  have hQR : ∑ p ∈ S.filter (fun p => 0 < p.1 ∧ p.2.natAbs < p.1.natAbs), (g p.1 p.2).toNat = Q := by
    apply Finset.sum_bij (fun p _ => (-p.1, p.2))
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, S] at hp ⊢
      refine ⟨⟨⟨by omega, by omega⟩, hp.1.2⟩, by omega, by simp only [Int.natAbs_neg]; exact hp.2.2⟩
    · intro p1 _ p2 _ heq; ext <;> simp_all
    · intro q hq
      refine ⟨(-q.1, q.2), ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, S] at hq ⊢
      refine ⟨⟨⟨by omega, by omega⟩, hq.1.2⟩, by omega, by simp only [Int.natAbs_neg]; exact hq.2.2⟩
    · intro p _; exact congrArg Bool.toNat (hsymm.1 p.1 p.2).symm
  have hQU : ∑ p ∈ S.filter (fun p => 0 < p.2 ∧ p.1.natAbs < p.2.natAbs), (g p.1 p.2).toNat = Q := by
    rw [← hQR]
    apply Finset.sum_bij (fun p _ => (p.2, p.1))
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, S] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2.1, hp.2.2⟩
    · intro p1 _ p2 _ heq; ext <;> simp_all
    · intro q hq
      refine ⟨(q.2, q.1), ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, S] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, hq.2.1, hq.2.2⟩
    · intro p _; exact congrArg Bool.toNat (hsymm.2.2 p.1 p.2).symm
  have hQD : ∑ p ∈ S.filter (fun p => p.2 < 0 ∧ p.1.natAbs < p.2.natAbs), (g p.1 p.2).toNat = Q := by
    rw [← hQU]
    apply Finset.sum_bij (fun p _ => (p.1, -p.2))
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, S] at hp ⊢
      refine ⟨⟨hp.1.1, ⟨by omega, by omega⟩⟩, by omega, by simp only [Int.natAbs_neg]; exact hp.2.2⟩
    · intro p1 _ p2 _ heq; ext <;> simp_all
    · intro q hq
      refine ⟨(q.1, -q.2), ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, S] at hq ⊢
      refine ⟨⟨hq.1.1, ⟨by omega, by omega⟩⟩, by omega, by simp only [Int.natAbs_neg]; exact hq.2.2⟩
    · intro p _; exact congrArg Bool.toNat (hsymm.2.1 p.1 p.2).symm
  have hdiag_sum : ∑ p ∈ S.filter (fun p => p.1.natAbs = p.2.natAbs), (g p.1 p.2).toNat = 1 := by
    have hmem0 : (0, 0) ∈ S.filter (fun p => p.1.natAbs = p.2.natAbs) := by
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, S, Int.natAbs_zero]
      exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, trivial⟩
    rw [Finset.sum_eq_single (0, 0)]
    · simp [h0]
    · intro p hp hp0
      simp only [Finset.mem_filter] at hp
      have hne : p.1 ≠ 0 := by
        intro h1; apply hp0; ext
        · exact h1
        · have : p.2.natAbs = 0 := by rw [← hp.2, h1]; rfl
          exact Int.natAbs_eq_zero.mp this
      rw [hdiag p.1 p.2 hne hp.2]; rfl
    · intro h; exact absurd hmem0 h
  unfold UCount
  change ∑ p ∈ S, (g p.1 p.2).toNat = 1 + 4 * Q
  rw [← Finset.sum_filter_add_sum_filter_not S (fun p => p.1.natAbs = p.2.natAbs), hdiag_sum]
  have hrest : S.filter (fun p => ¬ p.1.natAbs = p.2.natAbs) =
      (S.filter (fun p => p.2.natAbs < p.1.natAbs)) ∪ (S.filter (fun p => p.1.natAbs < p.2.natAbs)) := by
    ext p; simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro ⟨h1, h2⟩; rcases lt_or_gt_of_ne h2 with hlt | hgt; exact Or.inr ⟨h1, hlt⟩; exact Or.inl ⟨h1, hgt⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨h1, by omega⟩
  rw [hrest, Finset.sum_union (by rw [Finset.disjoint_filter]; intro p _ h1 h2; omega)]
  have hLR : S.filter (fun p => p.2.natAbs < p.1.natAbs) =
      (S.filter (fun p => 0 < p.1 ∧ p.2.natAbs < p.1.natAbs)) ∪
      (S.filter (fun p => p.1 < 0 ∧ p.2.natAbs < p.1.natAbs)) := by
    ext p; simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro ⟨h1, h2⟩; by_cases hp : 0 < p.1; exact Or.inl ⟨h1, hp, h2⟩; exact Or.inr ⟨h1, by omega, h2⟩
    · rintro (⟨h1, _, h2⟩ | ⟨h1, _, h2⟩) <;> exact ⟨h1, h2⟩
  have hUD : S.filter (fun p => p.1.natAbs < p.2.natAbs) =
      (S.filter (fun p => 0 < p.2 ∧ p.1.natAbs < p.2.natAbs)) ∪
      (S.filter (fun p => p.2 < 0 ∧ p.1.natAbs < p.2.natAbs)) := by
    ext p; simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro ⟨h1, h2⟩; by_cases hp : 0 < p.2; exact Or.inl ⟨h1, hp, h2⟩; exact Or.inr ⟨h1, by omega, h2⟩
    · rintro (⟨h1, _, h2⟩ | ⟨h1, _, h2⟩) <;> exact ⟨h1, h2⟩
  rw [hLR, Finset.sum_union (by rw [Finset.disjoint_filter]; intro p _ h1 h2; omega)]
  rw [hUD, Finset.sum_union (by rw [Finset.disjoint_filter]; intro p _ h1 h2; omega)]
  rw [hQR, hQU, hQD]
  omega

private lemma UCount_Combine {M : ℕ} (hM : 2 ≤ M) {g : ℤ → ℤ → Bool}
    (hsupp : ∀ x y : ℤ, M ≤ x.natAbs + y.natAbs → g x y = false)
    (hsymm : (∀ x y : ℤ, g (-x) y = g x y) ∧
             (∀ x y : ℤ, g x (-y) = g x y) ∧
             (∀ x y : ℤ, g y x = g x y))
    (h0 : g 0 0 = true)
    (hdiag : ∀ x y : ℤ, x ≠ 0 → x.natAbs = y.natAbs → g x y = false) :
    UCount (Combine M g g) (2 * M - 1) = 4 * UCount g (M - 1) + 1 := by
  set S1 := Finset.Icc (-((M - 1 : ℕ) : ℤ)) ((M - 1 : ℕ) : ℤ) ×ˢ
            Finset.Icc (-((M - 1 : ℕ) : ℤ)) ((M - 1 : ℕ) : ℤ)
  set S2 := Finset.Icc (-((2 * M - 1 : ℕ) : ℤ)) ((2 * M - 1 : ℕ) : ℤ) ×ˢ
            Finset.Icc (-((2 * M - 1 : ℕ) : ℤ)) ((2 * M - 1 : ℕ) : ℤ)
  set H := Combine M g g
  have hHsymm := Combine_symm (M := M) hsymm hsymm
  have hQ_eq := UCount_quadrant_decomp (M := M) (by omega) hsymm h0 hdiag
  set Q := ∑ p ∈ S1.filter (fun p => p.1 < 0 ∧ p.2.natAbs < p.1.natAbs), (g p.1 p.2).toNat
  change UCount g (M - 1) = 1 + 4 * Q at hQ_eq
  have hsplit : UCount H (2 * M - 1) =
      (∑ p ∈ S2.filter (fun p => p.1.natAbs + p.2.natAbs < M), (H p.1 p.2).toNat) +
      (∑ p ∈ S2.filter (fun p => ¬ p.1.natAbs + p.2.natAbs < M), (H p.1 p.2).toNat) := by
    unfold UCount
    exact (Finset.sum_filter_add_sum_filter_not S2 (fun p => p.1.natAbs + p.2.natAbs < M) _).symm
  have hsum_in : ∑ p ∈ S2.filter (fun p => p.1.natAbs + p.2.natAbs < M), (H p.1 p.2).toNat =
      UCount g (M - 1) := by
    have hset : S2.filter (fun p => p.1.natAbs + p.2.natAbs < M) =
        S1.filter (fun p => p.1.natAbs + p.2.natAbs < M) := by
      ext p; simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, S1, S2]; omega
    rw [hset]
    have hcongr : ∑ p ∈ S1.filter (fun p => p.1.natAbs + p.2.natAbs < M), (H p.1 p.2).toNat =
        ∑ p ∈ S1.filter (fun p => p.1.natAbs + p.2.natAbs < M), (g p.1 p.2).toNat := by
      apply Finset.sum_congr rfl; intro p hp
      simp only [Finset.mem_filter] at hp
      simp only [H, Combine, if_pos hp.2]
    rw [hcongr]
    unfold UCount
    rw [← Finset.sum_filter_add_sum_filter_not S1 (fun p => p.1.natAbs + p.2.natAbs < M)]
    have hz : ∑ p ∈ S1.filter (fun p => ¬ p.1.natAbs + p.2.natAbs < M), (g p.1 p.2).toNat = 0 := by
      apply Finset.sum_eq_zero; intro p hp
      simp only [Finset.mem_filter] at hp
      rw [hsupp p.1 p.2 (by omega)]; rfl
    omega
  set S2out := S2.filter (fun p => ¬ p.1.natAbs + p.2.natAbs < M)
  set C := ∑ p ∈ S2out.filter (fun p => 0 < p.1 ∧ p.2.natAbs < p.1.natAbs), (H p.1 p.2).toNat
  have hsum_out : ∑ p ∈ S2out, (H p.1 p.2).toNat = 4 * C := by
    have hdiag0 : ∑ p ∈ S2out.filter (fun p => p.1.natAbs = p.2.natAbs), (H p.1 p.2).toNat = 0 := by
      apply Finset.sum_eq_zero; intro p hp
      simp only [Finset.mem_filter, S2out] at hp
      simp only [H, Combine, if_neg hp.1.2, if_pos hp.2]; rfl
    have hCL : ∑ p ∈ S2out.filter (fun p => p.1 < 0 ∧ p.2.natAbs < p.1.natAbs), (H p.1 p.2).toNat = C := by
      apply Finset.sum_bij (fun p _ => (-p.1, p.2))
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, S2out, S2] at hp ⊢
        refine ⟨⟨⟨⟨by omega, by omega⟩, hp.1.1.2⟩, by simp only [Int.natAbs_neg]; exact hp.1.2⟩,
          by omega, by simp only [Int.natAbs_neg]; exact hp.2.2⟩
      · intro p1 _ p2 _ heq; ext <;> simp_all
      · intro q hq
        refine ⟨(-q.1, q.2), ?_, by simp⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, S2out, S2] at hq ⊢
        refine ⟨⟨⟨⟨by omega, by omega⟩, hq.1.1.2⟩, by simp only [Int.natAbs_neg]; exact hq.1.2⟩,
          by omega, by simp only [Int.natAbs_neg]; exact hq.2.2⟩
      · intro p _; exact congrArg Bool.toNat (hHsymm.1 p.1 p.2).symm
    have hCU : ∑ p ∈ S2out.filter (fun p => 0 < p.2 ∧ p.1.natAbs < p.2.natAbs), (H p.1 p.2).toNat = C := by
      apply Finset.sum_bij (fun p _ => (p.2, p.1))
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, S2out, S2] at hp ⊢
        refine ⟨⟨⟨hp.1.1.2, hp.1.1.1⟩, by omega⟩, hp.2.1, hp.2.2⟩
      · intro p1 _ p2 _ heq; ext <;> simp_all
      · intro q hq
        refine ⟨(q.2, q.1), ?_, by simp⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, S2out, S2] at hq ⊢
        refine ⟨⟨⟨hq.1.1.2, hq.1.1.1⟩, by omega⟩, hq.2.1, hq.2.2⟩
      · intro p _; exact congrArg Bool.toNat (hHsymm.2.2 p.1 p.2).symm
    have hCD : ∑ p ∈ S2out.filter (fun p => p.2 < 0 ∧ p.1.natAbs < p.2.natAbs), (H p.1 p.2).toNat = C := by
      rw [← hCU]
      apply Finset.sum_bij (fun p _ => (p.1, -p.2))
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, S2out, S2] at hp ⊢
        refine ⟨⟨⟨hp.1.1.1, ⟨by omega, by omega⟩⟩, by simp only [Int.natAbs_neg]; exact hp.1.2⟩,
          by omega, by simp only [Int.natAbs_neg]; exact hp.2.2⟩
      · intro p1 _ p2 _ heq; ext <;> simp_all
      · intro q hq
        refine ⟨(q.1, -q.2), ?_, by simp⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, S2out, S2] at hq ⊢
        refine ⟨⟨⟨hq.1.1.1, ⟨by omega, by omega⟩⟩, by simp only [Int.natAbs_neg]; exact hq.1.2⟩,
          by omega, by simp only [Int.natAbs_neg]; exact hq.2.2⟩
      · intro p _; exact congrArg Bool.toNat (hHsymm.2.1 p.1 p.2).symm
    rw [← Finset.sum_filter_add_sum_filter_not S2out (fun p => p.1.natAbs = p.2.natAbs), hdiag0, zero_add]
    have hrest : S2out.filter (fun p => ¬ p.1.natAbs = p.2.natAbs) =
        (S2out.filter (fun p => p.2.natAbs < p.1.natAbs)) ∪ (S2out.filter (fun p => p.1.natAbs < p.2.natAbs)) := by
      ext p; simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · intro ⟨h1, h2⟩; rcases lt_or_gt_of_ne h2 with hlt | hgt; exact Or.inr ⟨h1, hlt⟩; exact Or.inl ⟨h1, hgt⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨h1, by omega⟩
    rw [hrest, Finset.sum_union (by rw [Finset.disjoint_filter]; intro p _ h1 h2; omega)]
    have hLR : S2out.filter (fun p => p.2.natAbs < p.1.natAbs) =
        (S2out.filter (fun p => 0 < p.1 ∧ p.2.natAbs < p.1.natAbs)) ∪
        (S2out.filter (fun p => p.1 < 0 ∧ p.2.natAbs < p.1.natAbs)) := by
      ext p; simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · intro ⟨h1, h2⟩; by_cases hp : 0 < p.1; exact Or.inl ⟨h1, hp, h2⟩; exact Or.inr ⟨h1, by omega, h2⟩
      · rintro (⟨h1, _, h2⟩ | ⟨h1, _, h2⟩) <;> exact ⟨h1, h2⟩
    have hUD : S2out.filter (fun p => p.1.natAbs < p.2.natAbs) =
        (S2out.filter (fun p => 0 < p.2 ∧ p.1.natAbs < p.2.natAbs)) ∪
        (S2out.filter (fun p => p.2 < 0 ∧ p.1.natAbs < p.2.natAbs)) := by
      ext p; simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · intro ⟨h1, h2⟩; by_cases hp : 0 < p.2; exact Or.inl ⟨h1, hp, h2⟩; exact Or.inr ⟨h1, by omega, h2⟩
      · rintro (⟨h1, _, h2⟩ | ⟨h1, _, h2⟩) <;> exact ⟨h1, h2⟩
    rw [hLR, Finset.sum_union (by rw [Finset.disjoint_filter]; intro p _ h1 h2; omega)]
    rw [hUD, Finset.sum_union (by rw [Finset.disjoint_filter]; intro p _ h1 h2; omega)]
    rw [hCL, hCU, hCD]
    omega
  have hCQ : C + Q = UCount g (M - 1) := by
    have hS1_split : UCount g (M - 1) =
        Q + ∑ p ∈ S1.filter (fun p => ¬ (p.1 < 0 ∧ p.2.natAbs < p.1.natAbs)), (g p.1 p.2).toNat := by
      unfold UCount
      exact (Finset.sum_filter_add_sum_filter_not S1 (fun p => p.1 < 0 ∧ p.2.natAbs < p.1.natAbs) _).symm
    have hC_eq : C = ∑ p ∈ S1.filter (fun p => ¬ (p.1 < 0 ∧ p.2.natAbs < p.1.natAbs)), (g p.1 p.2).toNat := by
      set R1 := S2out.filter (fun p => 0 < p.1 ∧ p.2.natAbs < p.1.natAbs)
      set R2 := S1.filter (fun p => ¬ (p.1 < 0 ∧ p.2.natAbs < p.1.natAbs))
      change ∑ p ∈ R1, (H p.1 p.2).toNat = ∑ p ∈ R2, (g p.1 p.2).toNat
      rw [← Finset.sum_filter_add_sum_filter_not R1 (fun p => (p.1 - (M : ℤ)).natAbs + p.2.natAbs < M)]
      rw [← Finset.sum_filter_add_sum_filter_not R2 (fun p => p.1.natAbs + p.2.natAbs < M)]
      have hz1 : ∑ p ∈ R1.filter (fun p => ¬ (p.1 - (M : ℤ)).natAbs + p.2.natAbs < M), (H p.1 p.2).toNat = 0 := by
        apply Finset.sum_eq_zero; intro p hp
        simp only [Finset.mem_filter, R1, S2out] at hp
        dsimp only [H]
        rw [Combine_right_cone (M := M) (by omega) hp.1.2.1 hp.1.2.2, hsupp (p.1 - M) p.2 (by omega)]; rfl
      have hz2 : ∑ p ∈ R2.filter (fun p => ¬ p.1.natAbs + p.2.natAbs < M), (g p.1 p.2).toNat = 0 := by
        apply Finset.sum_eq_zero; intro p hp
        simp only [Finset.mem_filter] at hp
        rw [hsupp p.1 p.2 (by omega)]; rfl
      rw [hz1, hz2, add_zero, add_zero]
      apply Finset.sum_bij (fun p _ => (p.1 - (M : ℤ), p.2))
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, R1, R2, S1, S2out, S2] at hp ⊢
        refine ⟨⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by omega⟩, hp.2⟩
      · intro p1 _ p2 _ heq; simp only [Prod.mk.injEq] at heq; ext <;> omega
      · intro q hq
        refine ⟨(q.1 + (M : ℤ), q.2), ?_, by simp⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, R1, R2, S1, S2out, S2] at hq ⊢
        refine ⟨⟨⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by omega⟩, ⟨by omega, by omega⟩⟩, by omega⟩
      · intro p hp
        simp only [Finset.mem_filter, R1, S2out] at hp
        exact congrArg Bool.toNat (@Combine_right_cone M g g p.1 p.2 (by omega) hp.1.2.1 hp.1.2.2)
    omega
  rw [hsplit, hsum_in, hsum_out]
  omega

private lemma UCount_pow2 (m : ℕ) : 3 * UCount (U (2 ^ m - 1)) (2 ^ m - 1) + 1 = 4 ^ (m + 1) := by
  induction m with
  | zero =>
    have h0 : UCount (U 0) 0 = 1 := by unfold UCount; rw [Finset.sum_product]; decide
    simp [h0]
  | succ m ih =>
    cases m with
    | zero =>
      have h1 : UCount (U 1) 1 = 5 := by unfold UCount; rw [Finset.sum_product]; decide
      simp [h1]
    | succ k =>
      set M : ℕ := 2 ^ (k + 1)
      have hM2 : 2 ≤ M := by
        have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (show 1 ≤ k + 1 by omega)
        simpa [M] using this
      have h2M : 2 ^ (k + 1 + 1) = 2 * M := by simp [M]; ring
      have hfn : U (2 * M - 1) = Combine M (U (M - 1)) (U (M - 1)) := by
        funext x y
        rw [show 2 * M - 1 = M + (M - 1) by omega]
        exact (U_master (k + 1) (by omega)).2.2 (M - 1) (by omega) x y
      have hstep : UCount (U (2 * M - 1)) (2 * M - 1) = 4 * UCount (U (M - 1)) (M - 1) + 1 := by
        rw [hfn]
        exact UCount_Combine hM2
          (fun x y hge => U_support (M - 1) x y (by omega))
          (U_symm (M - 1)) (U_origin_true (M - 1)) (U_diag_false (M - 1))
      rw [h2M, hstep]
      have hpow4 : 4 ^ (k + 1 + 1 + 1) = 4 * 4 ^ (k + 1 + 1) := by rw [pow_succ]; ring
      omega

private lemma onCount_469_odd (k : ℕ) :
    onCount 469 (2 * k + 1) + UCount (U k) (2 * k + 1) = (2 * (2 * k + 1) + 1) ^ 2 := by
  unfold onCount UCount
  rw [← Finset.sum_product']
  have hbij : ∑ p ∈ Finset.range (2 * (2 * k + 1) + 1) ×ˢ Finset.range (2 * (2 * k + 1) + 1),
      (if cell 469 (2 * k + 1) ((p.1 : ℤ) - (2 * k + 1 : ℕ)) ((p.2 : ℤ) - (2 * k + 1 : ℕ)) then 1 else 0) =
      ∑ q ∈ Finset.Icc (-((2 * k + 1 : ℕ) : ℤ)) ((2 * k + 1 : ℕ) : ℤ) ×ˢ
            Finset.Icc (-((2 * k + 1 : ℕ) : ℤ)) ((2 * k + 1 : ℕ) : ℤ),
      (!(U k q.1 q.2)).toNat := by
    apply Finset.sum_bij (fun p _ => ((p.1 : ℤ) - (2 * k + 1 : ℕ), (p.2 : ℤ) - (2 * k + 1 : ℕ)))
    · intro p hp; simp only [Finset.mem_product, Finset.mem_range, Finset.mem_Icc] at hp ⊢; omega
    · intro p1 _ p2 _ heq; simp only [Prod.mk.injEq] at heq; ext <;> omega
    · intro q hq
      simp only [Finset.mem_product, Finset.mem_Icc] at hq
      refine ⟨((q.1 + (2 * k + 1 : ℕ)).toNat, (q.2 + (2 * k + 1 : ℕ)).toNat), ?_, ?_⟩
      · simp only [Finset.mem_product, Finset.mem_range]; omega
      · ext <;> simp <;> omega
    · intro p _
      rw [(cell_469_eq_U k).2]
      cases U k ((p.1 : ℤ) - (2 * k + 1 : ℕ)) ((p.2 : ℤ) - (2 * k + 1 : ℕ)) <;> rfl
  rw [hbij, ← Finset.sum_add_distrib]
  have hone : ∀ q ∈ Finset.Icc (-((2 * k + 1 : ℕ) : ℤ)) ((2 * k + 1 : ℕ) : ℤ) ×ˢ
        Finset.Icc (-((2 * k + 1 : ℕ) : ℤ)) ((2 * k + 1 : ℕ) : ℤ),
      (!(U k q.1 q.2)).toNat + (U k q.1 q.2).toNat = 1 := by
    intro q _; cases U k q.1 q.2 <;> rfl
  rw [Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_product]
  have hcard : (Finset.Icc (-((2 * k + 1 : ℕ) : ℤ)) ((2 * k + 1 : ℕ) : ℤ)).card = 2 * (2 * k + 1) + 1 := by
    rw [Int.card_Icc]; omega
  rw [hcard, sq]

private lemma a_closed (n : ℕ) :
    (a n : ℚ) = 4 / 3 - (2 : ℚ) ^ (2 + n) + 11 * (4 : ℚ) ^ n / 3 := by
  cases n with
  | zero =>
    have h0 : a 0 = 1 := by unfold a onCount; decide
    rw [h0]; norm_num
  | succ m =>
    have h2n : 2 ^ (m + 1) - 1 = 2 * (2 ^ m - 1) + 1 := by
      have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
      omega
    have hon : onCount 469 (2 ^ (m + 1) - 1) + UCount (U (2 ^ m - 1)) (2 ^ m - 1) =
        (2 * (2 ^ (m + 1) - 1) + 1) ^ 2 := by
      rw [h2n]
      have hwid : UCount (U (2 ^ m - 1)) (2 * (2 ^ m - 1) + 1) = UCount (U (2 ^ m - 1)) (2 ^ m - 1) :=
        UCount_widen (by omega) (fun x y hgt => U_support (2 ^ m - 1) x y hgt)
      rw [← hwid]
      exact onCount_469_odd (2 ^ m - 1)
    have huc := UCount_pow2 m
    have hpow2 : 2 * (2 ^ (m + 1) - 1) + 1 = 2 ^ (m + 2) - 1 := by
      have h1 : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
      have h2 : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by ring
      omega
    have honQ : (onCount 469 (2 ^ (m + 1) - 1) : ℚ) + (UCount (U (2 ^ m - 1)) (2 ^ m - 1) : ℚ) =
        ((2 : ℚ) ^ (m + 2) - 1) ^ 2 := by
      have h1 : 1 ≤ 2 ^ (m + 2) := Nat.one_le_two_pow
      rw [hpow2] at hon
      have hcast : ((onCount 469 (2 ^ (m + 1) - 1) : ℕ) : ℚ) + (UCount (U (2 ^ m - 1)) (2 ^ m - 1) : ℚ) =
          (((2 ^ (m + 2) - 1 : ℕ) : ℚ)) ^ 2 := by exact_mod_cast hon
      rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at hcast
      exact hcast
    have hucQ : 3 * (UCount (U (2 ^ m - 1)) (2 ^ m - 1) : ℚ) + 1 = (4 : ℚ) ^ (m + 1) := by
      exact_mod_cast huc
    have h4eq : ((2 : ℚ) ^ (m + 2)) ^ 2 = 4 * (4 : ℚ) ^ (m + 1) := by
      rw [← pow_mul, show (m + 2) * 2 = 2 * (m + 2) by ring, pow_mul,
        show (2 : ℚ) ^ 2 = 4 by norm_num, pow_succ]
      ring
    have h2eq : (2 : ℚ) ^ (2 + (m + 1)) = 2 * (2 : ℚ) ^ (m + 2) := by
      rw [show 2 + (m + 1) = (m + 2) + 1 by omega, pow_succ]; ring
    unfold a
    push_cast
    linarith [honQ, hucQ, h4eq, h2eq]

private lemma a_rec (n : ℕ) (hn : 3 ≤ n) :
    (a n : ℚ) = 7 * a (n - 1) - 14 * a (n - 2) + 8 * a (n - 3) := by
  set k : ℕ := n - 3
  have h0 : n = k + 3 := by omega
  have h1 : n - 1 = k + 2 := by omega
  have h2 : n - 2 = k + 1 := by omega
  rw [h1, h2, h0, a_closed (k + 3), a_closed (k + 2), a_closed (k + 1), a_closed k]
  rw [show 2 + (k + 3) = (2 + k) + 3 by omega,
    show 2 + (k + 2) = (2 + k) + 2 by omega,
    show 2 + (k + 1) = (2 + k) + 1 by omega]
  rw [pow_add (2 : ℚ) (2 + k) 3, pow_add (2 : ℚ) (2 + k) 2, pow_add (2 : ℚ) (2 + k) 1,
    pow_add (4 : ℚ) k 3, pow_add (4 : ℚ) k 2, pow_add (4 : ℚ) k 1]
  ring

private lemma gf_eq :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 2 * X) * (1 - 4 * X) : PowerSeries ℚ) =
      1 + X + 2 * X ^ 2 := by
  set P : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))
  have hfac : ((1 - X) * (1 - 2 * X) * (1 - 4 * X) : PowerSeries ℚ) =
      1 - 7 * X + 14 * X ^ 2 - 8 * X ^ 3 := by ring
  rw [hfac]
  have hexp : P * (1 - 7 * X + 14 * X ^ 2 - 8 * X ^ 3) =
      P - C (7 : ℚ) * (P * X ^ 1) + C (14 : ℚ) * (P * X ^ 2) - C (8 : ℚ) * (P * X ^ 3) := by
    have h7 : C (7 : ℚ) = (7 : PowerSeries ℚ) := map_ofNat C 7
    have h14 : C (14 : ℚ) = (14 : PowerSeries ℚ) := map_ofNat C 14
    have h8 : C (8 : ℚ) = (8 : PowerSeries ℚ) := map_ofNat C 8
    rw [h7, h14, h8]; ring
  rw [hexp]
  have hrhs : (1 + X + 2 * X ^ 2 : PowerSeries ℚ) =
      1 + X ^ 1 + C (2 : ℚ) * X ^ 2 := by
    have h2 : C (2 : ℚ) = (2 : PowerSeries ℚ) := map_ofNat C 2
    rw [h2, pow_one]
  rw [hrhs]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_one, PowerSeries.coeff_X_pow, PowerSeries.coeff_C, PowerSeries.coeff_mk, P]
  have ha0 : (a 0 : ℚ) = 1 := by rw [a_closed 0]; norm_num
  have ha1 : (a 1 : ℚ) = 8 := by rw [a_closed 1]; norm_num
  have ha2 : (a 2 : ℚ) = 44 := by rw [a_closed 2]; norm_num
  match n with
  | 0 => simp [ha0]
  | 1 => simp [ha1, ha0]; norm_num
  | 2 => simp [ha2, ha1, ha0]; norm_num
  | n + 3 =>
    have hge3 : 3 ≤ n + 3 := by omega
    have hge2 : 2 ≤ n + 3 := by omega
    have hge1 : 1 ≤ n + 3 := by omega
    have hne0 : n + 3 ≠ 0 := by omega
    have hne1 : n + 3 ≠ 1 := by omega
    have hne2 : n + 3 ≠ 2 := by omega
    have hne2' : n + 3 - 2 ≠ 0 := by omega
    simp only [hge3, hge2, hge1, hne0, hne1, hne2, hne2', ↓reduceIte, sub_zero, add_zero]
    linarith [a_rec (n + 3) hge3]

end OMA.OeisA272417

theorem OMA.solution : type_of% @OMA.S_oeis_a272417.main :=
  ⟨OMA.OeisA272417.a_closed, OMA.OeisA272417.a_rec, OMA.OeisA272417.gf_eq⟩
