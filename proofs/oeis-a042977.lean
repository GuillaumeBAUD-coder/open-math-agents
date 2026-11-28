import OMAStatements.S_oeis_a042977

-- Problem: A042977: Triangle T(n,k) read by rows: coefficients of a polynomial sequence occurring when calculating the n-th derivative of Lambert func
-- Upstream: formal-conjectures statements/oeis-a042977.lean:0 (declaration OMA.S_oeis_a042977.main)
-- Credit: @julianibarz (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


open Set Filter
open scoped Topology

namespace LambertProof

open OMA.S_oeis_a042977

noncomputable def f (y : ℝ) : ℝ := y * Real.exp y

lemma f_strict (y : ℝ) : HasStrictDerivAt f ((1 + y) * Real.exp y) y := by
  convert! (hasStrictDerivAt_id y).mul (Real.hasStrictDerivAt_exp y) using 1
  simp only [id_eq]
  ring

lemma f_mono : StrictMonoOn f (Ici (-1)) := by
  apply strictMonoOn_of_deriv_pos (f := f) (convex_Ici _)
    (continuous_id.mul Real.continuous_exp).continuousOn
  intro y hy
  rw [(f_strict y).hasDerivAt.deriv]
  simp only [interior_Ici, mem_Ioi] at hy
  exact mul_pos (by linarith) (Real.exp_pos _)

lemma exists_inverse {x : ℝ} (hx : -Real.exp (-1) < x) :
    ∃ y : ℝ, -1 < y ∧ f y = x := by
  have hb : 0 ≤ |x| + 1 := by positivity
  have htop : x ≤ f (|x| + 1) := by
    have he := Real.one_le_exp hb
    have ha := le_abs_self x
    dsimp [f]
    nlinarith
  have hbot : f (-1) ≤ x := by simpa [f] using hx.le
  obtain ⟨y, hy, he⟩ := intermediate_value_Icc (f := f)
    (show (-1 : ℝ) ≤ |x| + 1 by linarith [abs_nonneg x])
    (continuous_id.mul Real.continuous_exp).continuousOn ⟨hbot, htop⟩
  refine ⟨y, lt_of_le_of_ne hy.1 ?_, he⟩
  intro h
  subst y
  simp [f] at he
  linarith

lemma W_spec {x : ℝ} (hx : -Real.exp (-1) < x) :
    -1 < lambertW0 x ∧ f (lambertW0 x) = x := by
  exact Classical.epsilon_spec (exists_inverse hx)

lemma W_f {y : ℝ} (hy : -1 < y) : lambertW0 (f y) = y := by
  have hs : -1 < lambertW0 (f y) ∧ f (lambertW0 (f y)) = f y :=
    Classical.epsilon_spec (show ∃ z : ℝ, -1 < z ∧ z * Real.exp z = f y from ⟨y, hy, rfl⟩)
  exact f_mono.injOn hs.1.le hy.le hs.2

lemma W_deriv {x : ℝ} (hx : -Real.exp (-1) < x) :
    HasDerivAt lambertW0 (Real.exp (-(lambertW0 x)) / (1 + lambertW0 x)) x := by
  obtain ⟨hw, he⟩ := W_spec hx
  have hn : (1 + lambertW0 x) * Real.exp (lambertW0 x) ≠ 0 :=
    ne_of_gt (mul_pos (by linarith) (Real.exp_pos _))
  have hi : ∀ᶠ y in 𝓝 (lambertW0 x), lambertW0 (f y) = y := by
    filter_upwards [Ioi_mem_nhds hw] with y hy
    exact W_f hy
  have hd := ((f_strict (lambertW0 x)).to_local_left_inverse hn hi).hasDerivAt
  rw [he] at hd
  have hh : Real.exp (-lambertW0 x) / (1 + lambertW0 x) =
      ((1 + lambertW0 x) * Real.exp (lambertW0 x))⁻¹ := by
    rw [Real.exp_neg, mul_inv, div_eq_mul_inv]
    ring
  rw [hh]
  exact hd

noncomputable def q (x : ℝ) : ℝ := Real.exp (-lambertW0 x)

noncomputable def z (x : ℝ) : ℝ := (1 + lambertW0 x)⁻¹

lemma q_deriv {x : ℝ} (hx : -Real.exp (-1) < x) :
    HasDerivAt q (-(q x)^2 * z x) x := by
  have hd := (W_deriv hx).neg.exp
  convert! hd using 1
  dsimp [q, z]
  rw [div_eq_mul_inv]
  ring

lemma z_deriv {x : ℝ} (hx : -Real.exp (-1) < x) :
    HasDerivAt z (-q x * (z x)^3) x := by
  have hn : 1 + lambertW0 x ≠ 0 := by linarith [(W_spec hx).1]
  have hd := ((W_deriv hx).const_add 1).inv hn
  convert! hd using 1
  dsimp [q, z]
  simp only [div_eq_mul_inv, ← inv_pow]
  ring

noncomputable def basis (n k : ℕ) (x : ℝ) : ℝ := (q x)^(n+1) * (z x)^(k+1)

lemma basis_deriv (n k : ℕ) {x : ℝ} (hx : -Real.exp (-1) < x) :
    HasDerivAt (basis n k)
      (-((n+1 : ℕ) * basis (n+1) (k+1) x + (k+1 : ℕ) * basis (n+1) (k+2) x)) x := by
  have hd := ((q_deriv hx).pow (n+1)).mul ((z_deriv hx).pow (k+1))
  convert! hd using 1
  simp only [basis, pow_succ, Nat.add_sub_cancel, Pi.pow_apply]
  ring

noncomputable def R : ℕ → ℕ → ℕ → ℝ → ℝ
  | 0, n, k, x => basis n k x
  | m+1, n, k, x => (n+1 : ℕ) * R m (n+1) (k+1) x +
      (k+1 : ℕ) * R m (n+1) (k+2) x

lemma R_deriv (m n k : ℕ) {x : ℝ} (hx : -Real.exp (-1) < x) :
    HasDerivAt (R m n k) (-R (m+1) n k x) x := by
  induction m generalizing n k with
  | zero => exact basis_deriv n k hx
  | succ m ih =>
    have hd := ((ih (n+1) (k+1)).const_mul ((n+1 : ℕ) : ℝ)).add
      ((ih (n+1) (k+2)).const_mul ((k+1 : ℕ) : ℝ))
    convert! hd using 1
    simp only [R]
    ring

lemma R_pos (m n k : ℕ) {x : ℝ} (hx : -Real.exp (-1) < x) : 0 < R m n k x := by
  have hq : 0 < q x := Real.exp_pos _
  have hz : 0 < z x := inv_pos.mpr (by linarith [(W_spec hx).1])
  induction m generalizing n k with
  | zero => exact mul_pos (pow_pos hq _) (pow_pos hz _)
  | succ m ih =>
    exact add_pos (mul_pos (by exact_mod_cast Nat.succ_pos n) (ih _ _))
      (mul_pos (by exact_mod_cast Nat.succ_pos k) (ih _ _))

lemma W_iter (m : ℕ) {x : ℝ} (hx : -Real.exp (-1) < x) :
    iteratedDeriv (m+1) lambertW0 x = (-1 : ℝ)^m * R m 0 0 x := by
  induction m generalizing x with
  | zero =>
    simpa only [iteratedDeriv_one, pow_zero, one_mul, R, basis, zero_add, pow_one,
      q, z, div_eq_mul_inv] using (W_deriv hx).deriv
  | succ m ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv (m+1) lambertW0 =ᶠ[𝓝 x]
        (fun y => (-1 : ℝ)^m * R m 0 0 y) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact ih hy
    rw [he.deriv_eq, ((R_deriv m 0 0 hx).const_mul ((-1 : ℝ)^m)).deriv]
    rw [pow_succ]
    ring

end LambertProof

theorem OMA.solution : type_of% @OMA.S_oeis_a042977.main := by
  intro n hn x hx
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  rw [LambertProof.W_iter m hx]
  exact mul_ne_zero (pow_ne_zero m (by norm_num)) (ne_of_gt (LambertProof.R_pos m 0 0 hx))
