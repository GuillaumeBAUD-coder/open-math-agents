import OMAStatements.S_oeis_a376499

-- Shorter proof of oeis-a376499 via M-th roots of unity in ℂ (M = 2n + 1).
namespace OMA.P

open Finset Complex
open OMA.S_oeis_a376499

noncomputable abbrev E := Complex.exp

noncomputable def th (M t : ℕ) : ℝ := 2 * t * Real.pi / M

noncomputable def tm (M k t : ℕ) : ℝ := 4 ^ k * Real.sin (th M t) ^ (2 * k)

lemma hsum2 (n k : ℕ) (hk : 1 ≤ k) :
    ∑ t ∈ range (2 * n + 1), tm (2 * n + 1) k t = 2 * entry n k := by
  let M := 2 * n + 1
  have hMne : (M : ℝ) ≠ 0 := (by dsimp [M]; positivity : (0 : ℝ) < M).ne'
  change ∑ t ∈ range M, tm M k t = 2 * entry n k
  rw [show range M = range (2 * n + 1) from rfl, sum_range_succ']
  have h0 : tm M k 0 = 0 := by simp [tm, th, zero_pow (by omega : 2 * k ≠ 0)]
  have hsp : ∑ i ∈ range (2 * n), tm M k (i + 1) =
      ∑ j ∈ range n, tm M k (j + 1) + ∑ j ∈ range n, tm M k (n + j + 1) := by
    rw [show range (2 * n) = range (n + n) by rw [Nat.two_mul], sum_range_add]
  have hL : ∑ j ∈ range n, tm M k (j + 1) = entry n k := by
    unfold entry; rw [mul_sum]; refine sum_congr rfl fun j _ => ?_
    unfold tm th angle; dsimp [M]; congr 3; push_cast; ring
  have hR : ∑ j ∈ range n, tm M k (n + j + 1) = entry n k := by
    rw [← sum_range_reflect]; unfold entry; rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have hjn : j < n := mem_range.mp hj
    rw [show n + (n - 1 - j) + 1 = 2 * n - j by omega]
    unfold tm; congr 1
    have hang : th M (2 * n - j) = -(angle n j) + 2 * Real.pi := by
      unfold th angle
      have hc : ((2 * n - j : ℕ) : ℝ) = 2 * (n : ℝ) - j := by
        rw [Nat.cast_sub (by omega : j ≤ 2 * n), Nat.cast_mul, Nat.cast_ofNat]
      dsimp [M] at hMne ⊢; push_cast at hMne ⊢; rw [hc]; field_simp [hMne]; ring
    rw [hang, Real.sin_add_two_pi, Real.sin_neg, pow_mul, pow_mul, neg_sq]
  rw [h0, add_zero, hsp, hL, hR]; ring

lemma hch (k : ℕ) (hk : 1 ≤ k) :
    (2 * k).choose k = 2 * (2 * k - 1).choose (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hs : (2 * m + 1).choose (m + 1) = (2 * m + 1).choose m := by
    rw [← Nat.choose_symm (by omega : m + 1 ≤ 2 * m + 1), show 2 * m + 1 - (m + 1) = m by omega]
  change ((2 * m + 1) + 1).choose (m + 1) = 2 * (2 * m + 1).choose m
  rw [Nat.choose_succ_succ, Nat.succ_eq_add_one, hs]; ring

lemma hgeo (ξ : ℂ) (M : ℕ) (hM : ξ ^ M = 1) :
    (∑ t ∈ range M, ξ ^ t) = if ξ = 1 then (M : ℂ) else 0 := by
  classical
  split_ifs with h1
  · subst h1; simp
  · have hm := geom_sum_mul ξ M
    rw [hM, sub_self] at hm
    exact (mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr h1)

end OMA.P

open Finset Complex
open OMA.P OMA.S_oeis_a376499

theorem OMA.solution : type_of% @OMA.S_oeis_a376499.main := by
  classical
  intro n k _ hk
  let M := 2 * n + 1
  have hMneC : (M : ℂ) ≠ 0 := by exact_mod_cast (show (0 : ℝ) < M by dsimp [M]; positivity).ne'
  let ζ : ℂ := E (2 * Real.pi * I / M)
  have hζM : ζ ^ M = 1 := by
    dsimp [ζ, E]; rw [← Complex.exp_nat_mul, mul_div_cancel₀ _ hMneC]
    simpa [mul_assoc] using Complex.exp_two_pi_mul_I
  have htermC (t : ℕ) : (tm M k t : ℂ) = (-1) ^ k * (ζ ^ t - (ζ ^ (M - 1)) ^ t) ^ (2 * k) := by
    have he1 : ζ ^ t = E (↑(th M t) * I) := by
      dsimp [ζ, E, th]; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    have he2 : (ζ ^ (M - 1)) ^ t = E (-(↑(th M t) * I)) := by
      have hp1 : ζ ^ t * (ζ ^ (M - 1)) ^ t = 1 := by
        rw [← mul_pow, ← pow_succ', show M - 1 + 1 = M by dsimp [M], hζM, one_pow]
      have hp2 : E (↑(th M t) * I) * E (-(↑(th M t) * I)) = 1 := by
        dsimp [E]; rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
      rw [he1] at hp1
      exact mul_left_cancel₀ (Complex.exp_ne_zero _) (hp1.trans hp2.symm)
    set s : ℂ := ↑(Real.sin (th M t))
    have hd : ζ ^ t - (ζ ^ (M - 1)) ^ t = 2 * s * I := by
      rw [he1, he2]; dsimp [E]
      have hn : -(↑(th M t) * I) = ((-th M t : ℝ) : ℂ) * I := by push_cast; ring
      rw [hn, Complex.exp_mul_I, Complex.exp_mul_I]; dsimp [s]; push_cast
      rw [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_sin]; ring
    have hp : (2 * s * I) ^ (2 * k) = (-1) ^ k * (4 ^ k * s ^ (2 * k)) := by
      rw [pow_mul, pow_mul]
      have hsq : (2 * s * I) ^ 2 = (-1) * (4 * s ^ 2) := by
        calc (2 * s * I) ^ 2 = 4 * s ^ 2 * I ^ 2 := by ring
          _ = (-1) * (4 * s ^ 2) := by rw [Complex.I_sq]; ring
      rw [hsq, mul_pow, mul_pow]
    rw [hd, hp, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
    unfold tm; dsimp [s]; push_cast; rfl
  let ξ (r : ℕ) : ℂ := ζ ^ (r + (M - 1) * (2 * k - r))
  have hξM (r : ℕ) : ξ r ^ M = 1 := by
    dsimp [ξ]; rw [← pow_mul, mul_comm _ M, pow_mul, hζM, one_pow]
  let F (r : ℕ) : ℂ := (-1) ^ (2 * k - r) * ((2 * k).choose r : ℂ) * if ξ r = 1 then (M : ℂ) else 0
  have hsumC : ((∑ t ∈ range M, tm M k t : ℝ) : ℂ) = (-1) ^ k * ∑ r ∈ range (2 * k + 1), F r := by
    rw [Complex.ofReal_sum]; simp_rw [htermC, ← mul_sum]; congr 1
    have hex (t : ℕ) : (ζ ^ t - (ζ ^ (M - 1)) ^ t) ^ (2 * k) =
        ∑ r ∈ range (2 * k + 1), (-1) ^ (2 * k - r) * ((2 * k).choose r : ℂ) * ξ r ^ t := by
      rw [sub_eq_add_neg, add_pow]
      refine sum_congr rfl fun r _ => ?_
      set w := (ζ ^ (M - 1)) ^ t
      have hn : (-w) ^ (2 * k - r) = (-1) ^ (2 * k - r) * w ^ (2 * k - r) := by
        rw [neg_eq_neg_one_mul, mul_pow]
      have hξt : (ζ ^ t) ^ r * w ^ (2 * k - r) = ξ r ^ t := by
        dsimp [ξ, w]; rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_mul]; congr 1; ring
      rw [hn]
      calc (ζ ^ t) ^ r * ((-1) ^ (2 * k - r) * w ^ (2 * k - r)) * ((2 * k).choose r : ℂ)
          = (-1) ^ (2 * k - r) * ((2 * k).choose r : ℂ) * ((ζ ^ t) ^ r * w ^ (2 * k - r)) := by ring
        _ = _ := by rw [hξt]
    simp_rw [hex]; rw [sum_comm]
    refine sum_congr rfl fun r _ => ?_
    rw [← mul_sum, hgeo (ξ r) M (hξM r)]
  have hsym (r : ℕ) (hr : r ∈ range k) : F (2 * k - r) = F r := by
    have hlt := mem_range.mp hr
    dsimp [F]
    have hsub : 2 * k - (2 * k - r) = r := by omega
    have hsgn : (-1 : ℂ) ^ r = (-1) ^ (2 * k - r) := by
      apply mul_left_cancel₀ (pow_ne_zero r (by norm_num : (-1 : ℂ) ≠ 0))
      rw [← pow_add, ← pow_add, show r + r = 2 * r by omega, show r + (2 * k - r) = 2 * k by omega,
        pow_mul, pow_mul, neg_one_sq, one_pow, one_pow]
    have hξi : ξ r * ξ (2 * k - r) = 1 := by
      dsimp [ξ]; rw [← pow_add]
      have hex : r + (M - 1) * (2 * k - r) + (2 * k - r + (M - 1) * (2 * k - (2 * k - r))) = M * (2 * k) := by
        rw [hsub, show M - 1 = 2 * n from rfl]
        calc r + 2 * n * (2 * k - r) + (2 * k - r + 2 * n * r) = (2 * n + 1) * (2 * k - r + r) := by ring
          _ = M * (2 * k) := by dsimp [M]; rw [show 2 * k - r + r = 2 * k by omega]
      rw [hex, pow_mul, hζM, one_pow]
    have hiff : (ξ (2 * k - r) = 1) ↔ (ξ r = 1) := ⟨fun h => by simpa [h] using hξi, fun h => by simpa [h] using hξi⟩
    rw [hsub, hsgn, Nat.choose_symm (by omega), if_congr hiff rfl rfl]
  have hsp : ∑ r ∈ range (2 * k + 1), F r = 2 * (∑ r ∈ range k, F r) + F k := by
    rw [show 2 * k + 1 = (k + 1) + k by omega, sum_range_add, sum_range_succ]
    have ht : ∑ j ∈ range k, F (k + 1 + j) = ∑ r ∈ range k, F r := by
      rw [← sum_range_reflect]; refine sum_congr rfl fun r hr => ?_
      have := mem_range.mp hr; rw [show k + 1 + (k - 1 - r) = 2 * k - r by omega, hsym r hr]
    rw [ht]; ring
  have hFk : F k = 2 * (M : ℂ) * ((-1) ^ k * ((2 * k - 1).choose (k - 1) : ℂ)) := by
    dsimp [F]
    have hξk : ξ k = 1 := by
      dsimp [ξ]
      have hex : k + (M - 1) * (2 * k - k) = M * k := by
        rw [show 2 * k - k = k by omega, show M - 1 = 2 * n from rfl]; dsimp [M]; ring
      rw [hex, pow_mul, hζM, one_pow]
    rw [if_pos hξk, show 2 * k - k = k by omega, hch k hk]; push_cast; ring
  let c (r : ℕ) : ℤ := if ξ r = 1 then (-1) ^ (2 * k - r) * (2 * k).choose r else 0
  let z : ℤ := (-1) ^ k * ((-1) ^ k * (2 * k - 1).choose (k - 1) + ∑ r ∈ range k, c r)
  have hFz : ∑ r ∈ range k, F r = M * ∑ r ∈ range k, (c r : ℂ) := by
    rw [mul_sum]; refine sum_congr rfl fun r _ => ?_; dsimp [F, c]; split_ifs <;> push_cast <;> ring
  have h2C : (2 : ℂ) * entry n k = 2 * (M : ℂ) * z := by
    have hC : ((∑ t ∈ range M, tm M k t : ℝ) : ℂ) = 2 * entry n k := by
      dsimp [M]; exact_mod_cast hsum2 n k hk
    rw [← hC, hsumC, hsp, hFk, hFz]; dsimp [z]; push_cast; ring
  have h1C : (entry n k : ℂ) = (((M : ℝ) * z : ℝ) : ℂ) :=
    mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) (by rw [h2C]; push_cast; ring)
  have hR : entry n k = (2 * (n : ℝ) + 1) * z := by
    simpa [M, Nat.cast_add, Nat.cast_mul] using Complex.ofReal_injective h1C
  exact ⟨z, by rw [div_eq_iff (by positivity : (2 * (n : ℝ) + 1) ≠ 0), hR, mul_comm]⟩
