import OMAReductions.R_Green65_green_65_variants_prime_minus_one_R1

/-!
Proof of `OMA.R_Green65_green_65_variants_prime_minus_one_R1.H2`.

Write `e = ZMod.stdAddChar`, `t r = 𝓕 K r ≥ 0` and `S r = ∑_{x ∈ A} e (r x)`.
Fourier inversion (`ZMod.dft_dft`) gives `M K z = ∑_r e (r z) t r`, hence
`M ∑_{x, y ∈ A} K (x - y) = ∑_r t r |S r| ^ 2 ≥ t 0 |S 0| ^ 2 = |A| ^ 2`,
because `t 0 = ∑ K = 1` and `S 0 = |A|`.
-/

open Finset ComplexConjugate

theorem OMA.solution : OMA.R_Green65_green_65_variants_prime_minus_one_R1.H2 := by
  intro M _ A K hsum hpos
  classical
  choose t ht0 htK using hpos
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  -- Fourier inversion for `K`.
  have hinv : ∀ z : ZMod M,
      (M : ℂ) * (K z : ℂ) = ∑ r, ZMod.stdAddChar (r * z) * (t r : ℂ) := by
    intro z
    have h := congrFun (ZMod.dft_dft (fun x => (K x : ℂ))) (-z)
    rw [ZMod.dft_apply] at h
    simp only [htK, smul_eq_mul, neg_neg, mul_neg] at h
    rw [← h]
  -- The character splits along `x - y`.
  have hsplit : ∀ r x y : ZMod M, ZMod.stdAddChar (r * (x - y)) =
      ZMod.stdAddChar (r * x) * conj (ZMod.stdAddChar (r * y)) := by
    intro r x y
    rw [mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul,
      OMA.R_Green65_green_65_variants_prime_minus_one_R1.green_char_conj]
  set S : ZMod M → ℂ := fun r => ∑ x ∈ A, ZMod.stdAddChar (r * x) with hS
  have hkey : ((M : ℝ) * ∑ x ∈ A, ∑ y ∈ A, K (x - y) : ℝ) =
      ∑ r, t r * Complex.normSq (S r) := by
    apply Complex.ofReal_injective
    push_cast
    calc (M : ℂ) * ∑ x ∈ A, ∑ y ∈ A, (K (x - y) : ℂ)
        = ∑ x ∈ A, ∑ y ∈ A, (M : ℂ) * (K (x - y) : ℂ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ x ∈ A, ∑ y ∈ A, ∑ r, ZMod.stdAddChar (r * (x - y)) * (t r : ℂ) := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          exact hinv (x - y)
      _ = ∑ x ∈ A, ∑ y ∈ A, ∑ r,
            (t r : ℂ) * (ZMod.stdAddChar (r * x) * conj (ZMod.stdAddChar (r * y))) := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
            Finset.sum_congr rfl fun r _ => ?_
          rw [hsplit]
          ring
      _ = ∑ x ∈ A, ∑ r, ∑ y ∈ A,
            (t r : ℂ) * (ZMod.stdAddChar (r * x) * conj (ZMod.stdAddChar (r * y))) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = ∑ r, ∑ x ∈ A, ∑ y ∈ A,
            (t r : ℂ) * (ZMod.stdAddChar (r * x) * conj (ZMod.stdAddChar (r * y))) :=
          Finset.sum_comm
      _ = ∑ r, (t r : ℂ) * (S r * conj (S r)) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          simp only [hS, map_sum, Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_comm
      _ = ∑ r, (t r : ℂ) * (Complex.normSq (S r) : ℂ) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Complex.mul_conj]
  -- The zero frequency.
  have ht1 : t 0 = 1 := by
    have h := htK 0
    rw [ZMod.dft_apply_zero] at h
    have h' : ((∑ x, K x : ℝ) : ℂ) = (t 0 : ℂ) := by push_cast; exact h
    rw [hsum] at h'
    exact_mod_cast h'.symm
  have hS0 : S 0 = ((A.card : ℝ) : ℂ) := by
    simp [hS]
  have hle : t 0 * Complex.normSq (S 0) ≤ ∑ r, t r * Complex.normSq (S r) :=
    Finset.single_le_sum (f := fun r => t r * Complex.normSq (S r))
      (fun r _ => mul_nonneg (ht0 r) (Complex.normSq_nonneg _)) (Finset.mem_univ 0)
  rw [ht1, one_mul, hS0, Complex.normSq_ofReal] at hle
  rw [← hkey] at hle
  nlinarith [hle]
