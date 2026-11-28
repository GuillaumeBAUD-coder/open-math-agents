import OMAStatements.S_mo_302130

-- Problem: Does $n^2$ divide $\det[(i+j)^n]_{0\le i,j\le n-1}$ for each integer $n>2$?
-- Upstream: formal-conjectures statements/mo-302130.lean:0 (declaration OMA.S_mo_302130.main)
-- Credit: @oceancheol (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Status of the mathematics (literature check): the MathOverflow question 302130 has no posted
-- answer, but comments there by Darij Grinberg (2018) sketch a proof of n^2 | a(n) through the
-- Cauchy-Binet formula. So the divisibility itself is a known result; this file is a Lean
-- formalization, by a different and self-contained route (finite differences).
--
-- Proof. Let L be the lower unitriangular matrix L(r,i) = (-1)^(r-i) * C(r,i) and M(i,j) = (i+j)^n.
-- Then (L * M * L^T)(r,s) = h(r+s), where h(k) is the k-th forward difference of x^n at 0, and
-- det(L * M * L^T) = det M. Facts used about h: h(k) = 0 for k > n, h(n) = n!, and
-- 2 * h(n-1) = (n-1) * n! (from the reflection k -> n-1-k of the difference sum), so n divides
-- both h(n) and h(n-1) when n >= 3. In the Leibniz expansion of det[h(r+s)], a permutation sigma
-- with every r + sigma(r) <= n must have at least two rows with r + sigma(r) >= n-1, because the
-- numbers r + sigma(r) sum to n(n-1); hence every term is divisible by n^2.

namespace OMA.MO302130

open Finset

/-- `hk n k` is the `k`-th forward difference of `x ↦ x ^ n`, evaluated at `0`. -/
def hk (n k : ℕ) : ℤ := (fwdDiff (1 : ℤ))^[k] (fun x : ℤ => x ^ n) 0

lemma hk_zero_of_lt {n k : ℕ} (h : n < k) : hk n k = 0 := by
  unfold hk
  rw [fwdDiff_iter_pow_eq_zero_of_lt h]
  rfl

lemma hk_self (n : ℕ) : hk n n = (n.factorial : ℤ) := by
  unfold hk
  rw [fwdDiff_iter_eq_factorial]
  simp

lemma sum_fin (n r : ℕ) (hr : r < n) (f : ℤ → ℤ) :
    ∑ i : Fin n, ((-1 : ℤ) ^ (r - (i : ℕ)) * (r.choose (i : ℕ) : ℤ)) * f ((i : ℕ) : ℤ)
      = (fwdDiff (1 : ℤ))^[r] f 0 := by
  rw [fwdDiff_iter_eq_sum_shift]
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => ((-1 : ℤ) ^ (r - i) * (r.choose i : ℤ)) * f (i : ℤ)) n]
  rw [← Finset.sum_subset (Finset.range_mono (show r + 1 ≤ n by omega))]
  · apply Finset.sum_congr rfl
    intro k _
    simp
  · intro k _ hk
    have hlt : r < k := by
      have := Finset.mem_range.not.mp hk
      omega
    simp [Nat.choose_eq_zero_of_lt hlt]

def Lm (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun r i : Fin n => (-1 : ℤ) ^ ((r : ℕ) - (i : ℕ)) * ((r : ℕ).choose (i : ℕ) : ℤ)

def Mm (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j : Fin n => ((i : ℤ) + j) ^ n

lemma LML (n : ℕ) (r s : Fin n) :
    (Lm n * Mm n * (Lm n).transpose) r s = hk n ((r : ℕ) + (s : ℕ)) := by
  rw [Matrix.mul_apply]
  have inner : ∀ j : Fin n, (Lm n * Mm n) r j
      = (fwdDiff (1 : ℤ))^[(r : ℕ)] (fun x : ℤ => x ^ n) ((j : ℕ) : ℤ) := by
    intro j
    rw [Matrix.mul_apply]
    have h1 := sum_fin n r r.isLt (fun x : ℤ => (x + ((j : ℕ) : ℤ)) ^ n)
    have h2 : (fwdDiff (1 : ℤ))^[(r : ℕ)] (fun x : ℤ => (x + ((j : ℕ) : ℤ)) ^ n) 0
        = (fwdDiff (1 : ℤ))^[(r : ℕ)] (fun x : ℤ => x ^ n) (0 + ((j : ℕ) : ℤ)) :=
      fwdDiff_iter_comp_add (1 : ℤ) (fun x : ℤ => x ^ n) _ _ 0
    rw [h2, zero_add] at h1
    rw [← h1]
    apply Finset.sum_congr rfl
    intro i _
    simp [Lm, Mm]
  simp only [inner]
  have h3 := sum_fin n s s.isLt ((fwdDiff (1 : ℤ))^[(r : ℕ)] (fun x : ℤ => x ^ n))
  unfold hk
  rw [Nat.add_comm (r : ℕ) (s : ℕ), Function.iterate_add_apply, ← h3]
  apply Finset.sum_congr rfl
  intro j _
  simp [Lm, Matrix.transpose_apply]
  ring

lemma det_Lm (n : ℕ) : (Lm n).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_eq_one
    intro i _
    simp [Lm]
  · intro i j hij
    have h : (i : ℕ) < (j : ℕ) := Fin.lt_def.mp (OrderDual.toDual_lt_toDual.mp hij)
    simp [Lm, Nat.choose_eq_zero_of_lt h]

lemma two_mul_hk_pred (m : ℕ) :
    2 * hk (m + 1) m = (m : ℤ) * ((m + 1).factorial : ℤ) := by
  obtain ⟨g, hg⟩ : ∃ g : ℤ → ℤ, g = (fwdDiff (1 : ℤ))^[m] (fun x : ℤ => x ^ (m + 1)) :=
    ⟨_, rfl⟩
  have step : ∀ y : ℤ, g (y + 1) - g y = ((m + 1).factorial : ℤ) := by
    intro y
    have h1 : fwdDiff (1 : ℤ) g y = g (y + 1) - g y := rfl
    have h2 : fwdDiff (1 : ℤ) g = (fwdDiff (1 : ℤ))^[m + 1] (fun x : ℤ => x ^ (m + 1)) := by
      rw [hg]
      exact (Function.iterate_succ_apply' (fwdDiff (1 : ℤ)) m (fun x : ℤ => x ^ (m + 1))).symm
    rw [← h1, h2, fwdDiff_iter_eq_factorial]
    simp
  have down : ∀ k : ℕ, g (-(k : ℤ)) = g 0 - (k : ℤ) * ((m + 1).factorial : ℤ) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h := step (-((k + 1 : ℕ) : ℤ))
      have e : -((k + 1 : ℕ) : ℤ) + 1 = -(k : ℤ) := by push_cast; ring
      rw [e, ih] at h
      push_cast at h ⊢
      linarith
  have L1 : g (-(m : ℤ)) = ∑ k ∈ range (m + 1),
      ((-1 : ℤ) ^ (m - k) * (m.choose k : ℤ)) * (-(m : ℤ) + (k : ℤ)) ^ (m + 1) := by
    rw [hg, fwdDiff_iter_eq_sum_shift]
    apply Finset.sum_congr rfl
    intro k _
    simp
  have L2 : g 0 = ∑ k ∈ range (m + 1),
      ((-1 : ℤ) ^ (m - k) * (m.choose k : ℤ)) * (k : ℤ) ^ (m + 1) := by
    rw [hg, fwdDiff_iter_eq_sum_shift]
    apply Finset.sum_congr rfl
    intro k _
    simp
  have hrefl : g (-(m : ℤ)) = - g 0 := by
    rw [L1, L2]
    rw [← Finset.sum_range_reflect
      (fun k => ((-1 : ℤ) ^ (m - k) * (m.choose k : ℤ)) * (-(m : ℤ) + (k : ℤ)) ^ (m + 1)) (m + 1)]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ m := by
      have := Finset.mem_range.mp hj
      omega
    have e1 : m + 1 - 1 - j = m - j := by omega
    have e2 : m - (m - j) = j := by omega
    have e3 : ((m - j : ℕ) : ℤ) = (m : ℤ) - (j : ℤ) := by
      rw [Nat.cast_sub hj']
    simp only [e1, e2, e3, Nat.choose_symm hj']
    have e4 : (-(m : ℤ) + ((m : ℤ) - (j : ℤ))) = -(j : ℤ) := by ring
    rw [e4, neg_pow (j : ℤ) (m + 1)]
    have e5 : (-1 : ℤ) ^ (m + 1) = (-1) ^ (m - j) * (-1) ^ j * (-1) := by
      rw [← pow_add, Nat.sub_add_cancel hj', pow_succ]
    have e6 : ((-1 : ℤ) ^ j) * ((-1 : ℤ) ^ j) = 1 := by
      rw [← mul_pow]
      norm_num
    rw [e5]
    linear_combination (-((-1 : ℤ) ^ (m - j) * (m.choose j : ℤ) * (j : ℤ) ^ (m + 1))) * e6
  have hd := down m
  rw [hrefl] at hd
  have hh : hk (m + 1) m = g 0 := by
    rw [hg]
    rfl
  rw [hh]
  linarith

lemma dvd_hk_pred {n : ℕ} (hn : 3 ≤ n) : (n : ℤ) ∣ hk n (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨t, ht⟩ : 2 ∣ m.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have key := two_mul_hk_pred m
  rw [Nat.factorial_succ, ht] at key
  refine ⟨(m : ℤ) * (t : ℤ), ?_⟩
  simp only [Nat.add_sub_cancel]
  push_cast at key ⊢
  have h3 : 2 * hk (m + 1) m = 2 * (((m : ℤ) + 1) * ((m : ℤ) * (t : ℤ))) := by
    rw [key]
    ring
  linarith

lemma dvd_prod (n : ℕ) (hn : 3 ≤ n) (σ : Equiv.Perm (Fin n)) :
    (n : ℤ) ^ 2 ∣ ∏ i : Fin n, hk n (((σ i : Fin n) : ℕ) + (i : ℕ)) := by
  obtain ⟨c, hc⟩ : ∃ c : Fin n → ℕ, c = fun i => ((σ i : Fin n) : ℕ) + (i : ℕ) := ⟨_, rfl⟩
  have hcv : ∀ i : Fin n, c i = ((σ i : Fin n) : ℕ) + (i : ℕ) := by
    intro i
    rw [hc]
  have hprod : ∏ i : Fin n, hk n (((σ i : Fin n) : ℕ) + (i : ℕ)) = ∏ i : Fin n, hk n (c i) := by
    rw [hc]
  rw [hprod]
  by_cases hbig : ∃ i : Fin n, n < c i
  · obtain ⟨i, hi⟩ := hbig
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (hk_zero_of_lt hi)]
    exact dvd_zero _
  · push_neg at hbig
    have hdvd : ∀ i : Fin n, n - 1 ≤ c i → (n : ℤ) ∣ hk n (c i) := by
      intro i hi
      have hle := hbig i
      rcases Nat.lt_or_ge (c i) n with h | h
      · have e : c i = n - 1 := by omega
        rw [e]
        exact dvd_hk_pred hn
      · have e : c i = n := by omega
        rw [e, hk_self]
        exact_mod_cast Nat.dvd_factorial (by omega) le_rfl
    by_cases hpair : ∃ i j : Fin n, i ≠ j ∧ n - 1 ≤ c i ∧ n - 1 ≤ c j
    · obtain ⟨i, j, hij, hi, hj⟩ := hpair
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), pow_two]
      apply mul_dvd_mul (hdvd i hi)
      exact (hdvd j hj).trans
        (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩))
    · exfalso
      push_neg at hpair
      have s1 : ∑ i : Fin n, (((σ i : Fin n) : ℕ) : ℤ) = ∑ i : Fin n, ((i : ℕ) : ℤ) :=
        Equiv.sum_comp σ (fun i : Fin n => ((i : ℕ) : ℤ))
      have s2 : ∑ i : Fin n, (((Fin.rev i : Fin n) : ℕ) : ℤ) = ∑ i : Fin n, ((i : ℕ) : ℤ) :=
        Equiv.sum_comp Fin.revPerm (fun i : Fin n => ((i : ℕ) : ℤ))
      have s3 : ∀ i : Fin n, (((Fin.rev i : Fin n) : ℕ) : ℤ) = (n : ℤ) - 1 - ((i : ℕ) : ℤ) := by
        intro i
        rw [Fin.val_rev]
        have := i.isLt
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring
      have hsum : ∑ i : Fin n, ((n : ℤ) - 1 - (c i : ℤ)) = 0 := by
        have h : ∑ i : Fin n, ((n : ℤ) - 1 - (c i : ℤ))
            = ∑ i : Fin n, (((Fin.rev i : Fin n) : ℕ) : ℤ)
              - ∑ i : Fin n, (((σ i : Fin n) : ℕ) : ℤ) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [s3 i, hcv i]
          push_cast
          ring
        rw [h, s1, s2, sub_self]
      have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        simp
      by_cases hex : ∃ i0 : Fin n, n - 1 ≤ c i0
      · obtain ⟨i0, hi0⟩ := hex
        have hothers : ∀ j ∈ Finset.univ.erase i0, (1 : ℤ) ≤ (n : ℤ) - 1 - (c j : ℤ) := by
          intro j hj
          have hne : i0 ≠ j := (Finset.ne_of_mem_erase hj).symm
          have h := hpair i0 j hne hi0
          have h' : c j + 2 ≤ n := by omega
          have h'' : (c j : ℤ) + 2 ≤ (n : ℤ) := by exact_mod_cast h'
          linarith
        have hi0' : (-1 : ℤ) ≤ (n : ℤ) - 1 - (c i0 : ℤ) := by
          have h := hbig i0
          have h' : (c i0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast h
          linarith
        have hs := Finset.add_sum_erase Finset.univ (fun i : Fin n => (n : ℤ) - 1 - (c i : ℤ))
          (Finset.mem_univ i0)
        have hcard : (Finset.univ.erase i0).card = n - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
        have hlow := Finset.card_nsmul_le_sum (Finset.univ.erase i0)
          (fun i : Fin n => (n : ℤ) - 1 - (c i : ℤ)) 1 hothers
        rw [hcard, nsmul_eq_mul, mul_one, hn1] at hlow
        have hn' : (3 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
        linarith
      · push_neg at hex
        have hall : ∀ j ∈ (Finset.univ : Finset (Fin n)), (1 : ℤ) ≤ (n : ℤ) - 1 - (c j : ℤ) := by
          intro j _
          have h := hex j
          have h' : c j + 2 ≤ n := by omega
          have h'' : (c j : ℤ) + 2 ≤ (n : ℤ) := by exact_mod_cast h'
          linarith
        have hlow := Finset.card_nsmul_le_sum (Finset.univ : Finset (Fin n))
          (fun i : Fin n => (n : ℤ) - 1 - (c i : ℤ)) 1 hall
        rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hlow
        have hn' : (3 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
        linarith

theorem main' : ∀ n : ℕ, 3 ≤ n → (n : ℤ) ^ 2 ∣ (Mm n).det := by
  intro n hn
  have hdet : (Mm n).det = (Lm n * Mm n * (Lm n).transpose).det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_Lm]
    ring
  rw [hdet, Matrix.det_apply']
  apply Finset.dvd_sum
  intro σ _
  apply Dvd.dvd.mul_left
  have h : ∏ i : Fin n, (Lm n * Mm n * (Lm n).transpose) (σ i) i
      = ∏ i : Fin n, hk n (((σ i : Fin n) : ℕ) + (i : ℕ)) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [LML]
  rw [h]
  exact dvd_prod n hn σ

end OMA.MO302130

theorem OMA.solution : type_of% @OMA.S_mo_302130.main := by
  intro n hn
  exact OMA.MO302130.main' n hn
