import OMAStatements.S_oeis_a005726

-- Problem: A005726: Quadrinomial coefficients.
-- Upstream: formal-conjectures statements/oeis-a005726.lean:0 (declaration OMA.S_oeis_a005726.main)
-- Credit: @umarsxlim (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.S_oeis_a005726

private def F (n k : ℕ) : ℤ :=
  ((n.choose k * n.choose (2 * k + 1) : ℕ) : ℤ)

private def Q (m k : ℤ) : ℤ :=
  -28 - 80 * k - 56 * k ^ 2 - 16 * k ^ 3
  + 176 * m + 880 * m * k + 784 * m * k ^ 2 + 208 * m * k ^ 3
  - 945 * m ^ 2 - 1890 * m ^ 2 * k - 728 * m ^ 2 * k ^ 2
  + 1188 * m ^ 3 + 910 * m ^ 3 * k - 403 * m ^ 4

private def G (n k : ℕ) : ℤ :=
  if k = 0 then 0
  else Q (n : ℤ) (k : ℤ) * (((n - 1).choose (k - 1) : ℕ) : ℤ) * (((n - 2).choose (2 * k - 1) : ℕ) : ℤ)

private lemma nat_choose_absorb_bot : ∀ a b : ℕ,
    (b + 1) * (a + 1).choose (b + 1) = (a + 1) * a.choose b
  | 0, 0 => by simp
  | 0, b + 1 => by simp [Nat.choose_eq_zero_of_lt (by omega : 1 < b + 1 + 1)]
  | a + 1, 0 => by simp
  | a + 1, b + 1 => by
    have h1 := nat_choose_absorb_bot a b
    have h2 := nat_choose_absorb_bot a (b + 1)
    have h3 := Nat.choose_succ_succ a b
    have h4 := Nat.choose_succ_succ (a + 1) (b + 1)
    zify at h1 h2 h3 h4 ⊢
    rw [h4]
    linear_combination h1 + h2 - ((a : ℤ) + 1) * h3

private lemma choose_absorb_top (a b : ℕ) :
    ((a + 1 : ℕ) : ℤ) * (a.choose b : ℤ) =
      (((a + 1 : ℕ) : ℤ) - (b : ℤ)) * ((a + 1).choose b : ℤ) := by
  by_cases h : b ≤ a + 1
  · have hnat : (a + 1) * a.choose b = (a + 1 - b) * (a + 1).choose b := by
      by_cases hba : b ≤ a
      · have h3 : (a + 1 - b) * (a + 1).choose b = (a + 1) * a.choose b := by
          have hsym1 : (a + 1).choose b = (a + 1).choose (a + 1 - b) := (Nat.choose_symm h).symm
          have hsym2 : a.choose b = a.choose (a - b) := (Nat.choose_symm hba).symm
          rw [hsym1, hsym2]
          have hsub : a + 1 - b = (a - b) + 1 := by omega
          rw [hsub]
          exact nat_choose_absorb_bot a (a - b)
        exact h3.symm
      · have heq : b = a + 1 := by omega
        subst heq
        simp
    have hcast : (((a + 1) * a.choose b : ℕ) : ℤ) = (((a + 1 - b) * (a + 1).choose b : ℕ) : ℤ) :=
      by exact_mod_cast hnat
    push_cast [h] at hcast
    exact hcast
  · have h1 : a.choose b = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h2 : (a + 1).choose b = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h1, h2]

private lemma choose_absorb_bot (a b : ℕ) :
    ((b + 1 : ℕ) : ℤ) * ((a + 1).choose (b + 1) : ℤ) =
      ((a + 1 : ℕ) : ℤ) * (a.choose b : ℤ) := by
  exact_mod_cast nat_choose_absorb_bot a b

private lemma a_eq_sum_range {m n : ℕ} (hmn : m ≤ n) :
    a m = ∑ k ∈ Finset.range (n / 2 + 1), F m k := by
  unfold a F
  have hsub : Finset.range (m / 2 + 1) ⊆ Finset.range (n / 2 + 1) := by
    intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  rw [Finset.sum_subset hsub]
  intro k _ hkm
  simp only [Finset.mem_range] at hkm
  have h0 : m.choose (2 * k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp [h0]

private lemma wz_pointwise (r k : ℕ) :
    let n := r + 3
    let m : ℤ := (n : ℤ)
    G n (k + 1) - G n k =
      (m - 2) * (2 * (m - 1) * (2 * m + 1) * (13 * m - 14) * F n k +
        (-143 * m ^ 3 + 297 * m ^ 2 - 148 * m + 12) * F (n - 1) k -
        4 * (m - 1) * (26 * m ^ 2 - 41 * m + 9) * F (n - 2) k -
        16 * (m - 1) * (m - 2) * (13 * m - 1) * F (n - 3) k) := by
  dsimp only
  have hmul_ne : (((r + 3 : ℕ) : ℤ) ^ 2 * ((r + 2 : ℕ) : ℤ) ^ 2 * ((r + 1 : ℕ) : ℤ) ^ 2) ≠ 0 := by
    positivity
  apply mul_left_cancel₀ hmul_ne
  set rz : ℤ := (r : ℤ)
  set kz : ℤ := (k : ℤ)
  set c3k : ℤ := ((r + 3).choose k : ℤ)
  set c32 : ℤ := ((r + 3).choose (2 * k + 1) : ℤ)
  have h2k : ((r + 3 : ℕ) : ℤ) * ((r + 2).choose k : ℤ) = (rz + 3 - kz) * c3k := by
    have h := choose_absorb_top (r + 2) k
    rw [show r + 2 + 1 = r + 3 by omega] at h
    push_cast [rz, kz, c3k] at h ⊢
    linarith
  have h1k : ((r + 3 : ℕ) : ℤ) * ((r + 2 : ℕ) : ℤ) * ((r + 1).choose k : ℤ) =
      (rz + 3 - kz) * (rz + 2 - kz) * c3k := by
    have h := choose_absorb_top (r + 1) k
    rw [show r + 1 + 1 = r + 2 by omega] at h
    push_cast [rz, kz] at h ⊢
    have h' : (rz + 2) * ((r + 1).choose k : ℤ) = (rz + 2 - kz) * ((r + 2).choose k : ℤ) := by linarith
    calc (rz + 3) * (rz + 2) * ((r + 1).choose k : ℤ)
      _ = (rz + 3) * ((rz + 2) * ((r + 1).choose k : ℤ)) := by ring
      _ = (rz + 3) * ((rz + 2 - kz) * ((r + 2).choose k : ℤ)) := by rw [h']
      _ = (rz + 2 - kz) * ((rz + 3) * ((r + 2).choose k : ℤ)) := by ring
      _ = (rz + 2 - kz) * ((rz + 3 - kz) * c3k) := by rw [show (rz + 3) * ((r + 2).choose k : ℤ) = (rz + 3 - kz) * c3k from by push_cast [rz] at h2k; exact h2k]
      _ = (rz + 3 - kz) * (rz + 2 - kz) * c3k := by ring
  have h0k : ((r + 3 : ℕ) : ℤ) * ((r + 2 : ℕ) : ℤ) * ((r + 1 : ℕ) : ℤ) * (r.choose k : ℤ) =
      (rz + 3 - kz) * (rz + 2 - kz) * (rz + 1 - kz) * c3k := by
    have h := choose_absorb_top r k
    push_cast [rz, kz] at h ⊢
    have h' : (rz + 1) * (r.choose k : ℤ) = (rz + 1 - kz) * ((r + 1).choose k : ℤ) := by linarith
    calc (rz + 3) * (rz + 2) * (rz + 1) * (r.choose k : ℤ)
      _ = (rz + 3) * (rz + 2) * ((rz + 1) * (r.choose k : ℤ)) := by ring
      _ = (rz + 3) * (rz + 2) * ((rz + 1 - kz) * ((r + 1).choose k : ℤ)) := by rw [h']
      _ = (rz + 1 - kz) * ((rz + 3) * (rz + 2) * ((r + 1).choose k : ℤ)) := by ring
      _ = (rz + 1 - kz) * ((rz + 3 - kz) * (rz + 2 - kz) * c3k) := by
          rw [show (rz + 3) * (rz + 2) * ((r + 1).choose k : ℤ) = (rz + 3 - kz) * (rz + 2 - kz) * c3k from by push_cast [rz] at h1k; exact h1k]
      _ = (rz + 3 - kz) * (rz + 2 - kz) * (rz + 1 - kz) * c3k := by ring
  have h22 : ((r + 3 : ℕ) : ℤ) * ((r + 2).choose (2 * k + 1) : ℤ) = (rz + 2 - 2 * kz) * c32 := by
    have h := choose_absorb_top (r + 2) (2 * k + 1)
    rw [show r + 2 + 1 = r + 3 by omega] at h
    push_cast [rz, kz, c32] at h ⊢
    linarith
  have h12 : ((r + 3 : ℕ) : ℤ) * ((r + 2 : ℕ) : ℤ) * ((r + 1).choose (2 * k + 1) : ℤ) =
      (rz + 2 - 2 * kz) * (rz + 1 - 2 * kz) * c32 := by
    have h := choose_absorb_top (r + 1) (2 * k + 1)
    rw [show r + 1 + 1 = r + 2 by omega] at h
    push_cast [rz, kz] at h ⊢
    have h' : (rz + 2) * ((r + 1).choose (2 * k + 1) : ℤ) =
        (rz + 1 - 2 * kz) * ((r + 2).choose (2 * k + 1) : ℤ) := by linarith
    calc (rz + 3) * (rz + 2) * ((r + 1).choose (2 * k + 1) : ℤ)
      _ = (rz + 3) * ((rz + 2) * ((r + 1).choose (2 * k + 1) : ℤ)) := by ring
      _ = (rz + 3) * ((rz + 1 - 2 * kz) * ((r + 2).choose (2 * k + 1) : ℤ)) := by rw [h']
      _ = (rz + 1 - 2 * kz) * ((rz + 3) * ((r + 2).choose (2 * k + 1) : ℤ)) := by ring
      _ = (rz + 1 - 2 * kz) * ((rz + 2 - 2 * kz) * c32) := by
          rw [show (rz + 3) * ((r + 2).choose (2 * k + 1) : ℤ) = (rz + 2 - 2 * kz) * c32 from by push_cast [rz] at h22; exact h22]
      _ = (rz + 2 - 2 * kz) * (rz + 1 - 2 * kz) * c32 := by ring
  have h02 : ((r + 3 : ℕ) : ℤ) * ((r + 2 : ℕ) : ℤ) * ((r + 1 : ℕ) : ℤ) * (r.choose (2 * k + 1) : ℤ) =
      (rz + 2 - 2 * kz) * (rz + 1 - 2 * kz) * (rz - 2 * kz) * c32 := by
    have h := choose_absorb_top r (2 * k + 1)
    push_cast [rz, kz] at h ⊢
    have h' : (rz + 1) * (r.choose (2 * k + 1) : ℤ) =
        (rz - 2 * kz) * ((r + 1).choose (2 * k + 1) : ℤ) := by linarith
    calc (rz + 3) * (rz + 2) * (rz + 1) * (r.choose (2 * k + 1) : ℤ)
      _ = (rz + 3) * (rz + 2) * ((rz + 1) * (r.choose (2 * k + 1) : ℤ)) := by ring
      _ = (rz + 3) * (rz + 2) * ((rz - 2 * kz) * ((r + 1).choose (2 * k + 1) : ℤ)) := by rw [h']
      _ = (rz - 2 * kz) * ((rz + 3) * (rz + 2) * ((r + 1).choose (2 * k + 1) : ℤ)) := by ring
      _ = (rz - 2 * kz) * ((rz + 2 - 2 * kz) * (rz + 1 - 2 * kz) * c32) := by
          rw [show (rz + 3) * (rz + 2) * ((r + 1).choose (2 * k + 1) : ℤ) = (rz + 2 - 2 * kz) * (rz + 1 - 2 * kz) * c32 from by push_cast [rz] at h12; exact h12]
      _ = (rz + 2 - 2 * kz) * (rz + 1 - 2 * kz) * (rz - 2 * kz) * c32 := by ring
  have hF3 : F (r + 3) k = c3k * c32 := by unfold F; push_cast; rfl
  have hF2 : ((r + 3 : ℕ) : ℤ) ^ 2 * F (r + 2) k = (rz + 3 - kz) * (rz + 2 - 2 * kz) * c3k * c32 := by
    unfold F; push_cast
    calc ((r : ℤ) + 3) ^ 2 * (((r + 2).choose k : ℤ) * ((r + 2).choose (2 * k + 1) : ℤ))
      _ = (((r : ℤ) + 3) * ((r + 2).choose k : ℤ)) * (((r : ℤ) + 3) * ((r + 2).choose (2 * k + 1) : ℤ)) := by ring
      _ = ((rz + 3 - kz) * c3k) * ((rz + 2 - 2 * kz) * c32) := by
          rw [show ((r : ℤ) + 3) * ((r + 2).choose k : ℤ) = (rz + 3 - kz) * c3k from by push_cast at h2k; exact h2k,
              show ((r : ℤ) + 3) * ((r + 2).choose (2 * k + 1) : ℤ) = (rz + 2 - 2 * kz) * c32 from by push_cast at h22; exact h22]
      _ = (rz + 3 - kz) * (rz + 2 - 2 * kz) * c3k * c32 := by ring
  have hF1 : ((r + 3 : ℕ) : ℤ) ^ 2 * ((r + 2 : ℕ) : ℤ) ^ 2 * F (r + 1) k =
      (rz + 3 - kz) * (rz + 2 - kz) * (rz + 2 - 2 * kz) * (rz + 1 - 2 * kz) * c3k * c32 := by
    unfold F; push_cast
    calc ((r : ℤ) + 3) ^ 2 * ((r : ℤ) + 2) ^ 2 * (((r + 1).choose k : ℤ) * ((r + 1).choose (2 * k + 1) : ℤ))
      _ = (((r : ℤ) + 3) * ((r : ℤ) + 2) * ((r + 1).choose k : ℤ)) *
          (((r : ℤ) + 3) * ((r : ℤ) + 2) * ((r + 1).choose (2 * k + 1) : ℤ)) := by ring
      _ = ((rz + 3 - kz) * (rz + 2 - kz) * c3k) * ((rz + 2 - 2 * kz) * (rz + 1 - 2 * kz) * c32) := by
          rw [show ((r : ℤ) + 3) * ((r : ℤ) + 2) * ((r + 1).choose k : ℤ) = (rz + 3 - kz) * (rz + 2 - kz) * c3k from by push_cast at h1k; exact h1k,
              show ((r : ℤ) + 3) * ((r : ℤ) + 2) * ((r + 1).choose (2 * k + 1) : ℤ) = (rz + 2 - 2 * kz) * (rz + 1 - 2 * kz) * c32 from by push_cast at h12; exact h12]
      _ = (rz + 3 - kz) * (rz + 2 - kz) * (rz + 2 - 2 * kz) * (rz + 1 - 2 * kz) * c3k * c32 := by ring
  have hF0 : ((r + 3 : ℕ) : ℤ) ^ 2 * ((r + 2 : ℕ) : ℤ) ^ 2 * ((r + 1 : ℕ) : ℤ) ^ 2 * F r k =
      (rz + 3 - kz) * (rz + 2 - kz) * (rz + 1 - kz) * (rz + 2 - 2 * kz) * (rz + 1 - 2 * kz) * (rz - 2 * kz) * c3k * c32 := by
    unfold F; push_cast
    calc ((r : ℤ) + 3) ^ 2 * ((r : ℤ) + 2) ^ 2 * ((r : ℤ) + 1) ^ 2 * ((r.choose k : ℤ) * (r.choose (2 * k + 1) : ℤ))
      _ = (((r : ℤ) + 3) * ((r : ℤ) + 2) * ((r : ℤ) + 1) * (r.choose k : ℤ)) *
          (((r : ℤ) + 3) * ((r : ℤ) + 2) * ((r : ℤ) + 1) * (r.choose (2 * k + 1) : ℤ)) := by ring
      _ = ((rz + 3 - kz) * (rz + 2 - kz) * (rz + 1 - kz) * c3k) *
          ((rz + 2 - 2 * kz) * (rz + 1 - 2 * kz) * (rz - 2 * kz) * c32) := by
          rw [show ((r : ℤ) + 3) * ((r : ℤ) + 2) * ((r : ℤ) + 1) * (r.choose k : ℤ) = (rz + 3 - kz) * (rz + 2 - kz) * (rz + 1 - kz) * c3k from by push_cast at h0k; exact h0k,
              show ((r : ℤ) + 3) * ((r : ℤ) + 2) * ((r : ℤ) + 1) * (r.choose (2 * k + 1) : ℤ) = (rz + 2 - 2 * kz) * (rz + 1 - 2 * kz) * (rz - 2 * kz) * c32 from by push_cast at h02; exact h02]
      _ = (rz + 3 - kz) * (rz + 2 - kz) * (rz + 1 - kz) * (rz + 2 - 2 * kz) * (rz + 1 - 2 * kz) * (rz - 2 * kz) * c3k * c32 := by ring
  have hGp : ((r + 3 : ℕ) : ℤ) ^ 2 * ((r + 2 : ℕ) : ℤ) ^ 2 * ((r + 1 : ℕ) : ℤ) ^ 2 * G (r + 3) (k + 1) =
      Q (rz + 3) (kz + 1) * (rz + 2) * (rz + 1) ^ 2 * (rz + 3 - kz) * (rz + 2 - 2 * kz) * (rz + 1 - 2 * kz) * c3k * c32 := by
    unfold G
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
               show r + 3 - 1 = r + 2 by omega, show r + 3 - 2 = r + 1 by omega,
               show k + 1 - 1 = k by omega, show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
    push_cast
    calc ((r : ℤ) + 3) ^ 2 * ((r : ℤ) + 2) ^ 2 * ((r : ℤ) + 1) ^ 2 *
          (Q (rz + 3) (kz + 1) * ((r + 2).choose k : ℤ) * ((r + 1).choose (2 * k + 1) : ℤ))
      _ = Q (rz + 3) (kz + 1) * (rz + 2) * (rz + 1) ^ 2 *
          (((r : ℤ) + 3) * ((r + 2).choose k : ℤ)) *
          (((r : ℤ) + 3) * ((r : ℤ) + 2) * ((r + 1).choose (2 * k + 1) : ℤ)) := by ring
      _ = Q (rz + 3) (kz + 1) * (rz + 2) * (rz + 1) ^ 2 *
          ((rz + 3 - kz) * c3k) * ((rz + 2 - 2 * kz) * (rz + 1 - 2 * kz) * c32) := by
          rw [show ((r : ℤ) + 3) * ((r + 2).choose k : ℤ) = (rz + 3 - kz) * c3k from by push_cast at h2k; exact h2k,
              show ((r : ℤ) + 3) * ((r : ℤ) + 2) * ((r + 1).choose (2 * k + 1) : ℤ) = (rz + 2 - 2 * kz) * (rz + 1 - 2 * kz) * c32 from by push_cast at h12; exact h12]
      _ = Q (rz + 3) (kz + 1) * (rz + 2) * (rz + 1) ^ 2 * (rz + 3 - kz) * (rz + 2 - 2 * kz) * (rz + 1 - 2 * kz) * c3k * c32 := by ring
  have hGk : ((r + 3 : ℕ) : ℤ) ^ 2 * ((r + 2 : ℕ) : ℤ) ^ 2 * ((r + 1 : ℕ) : ℤ) ^ 2 * G (r + 3) k =
      Q (rz + 3) kz * (rz + 2) * (rz + 1) ^ 2 * kz * (2 * kz) * (2 * kz + 1) * c3k * c32 := by
    cases k with
    | zero =>
      simp [G, kz]
    | succ k' =>
      unfold G
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
                 show r + 3 - 1 = r + 2 by omega, show r + 3 - 2 = r + 1 by omega,
                 show k' + 1 - 1 = k' by omega, show 2 * (k' + 1) - 1 = 2 * k' + 1 by omega]
      have hb1 : ((r + 3 : ℕ) : ℤ) * ((r + 2).choose k' : ℤ) = kz * c3k := by
        have h := choose_absorb_bot (r + 2) k'
        rw [show r + 2 + 1 = r + 3 by omega] at h
        push_cast [kz, c3k] at h ⊢
        linarith
      have hb2 : ((r + 3 : ℕ) : ℤ) * ((r + 2 : ℕ) : ℤ) * ((r + 1).choose (2 * k' + 1) : ℤ) =
          (2 * kz) * (2 * kz + 1) * c32 := by
        have ha := choose_absorb_bot (r + 2) (2 * k' + 2)
        have hb := choose_absorb_bot (r + 1) (2 * k' + 1)
        rw [show r + 2 + 1 = r + 3 by omega, show 2 * k' + 2 + 1 = 2 * (k' + 1) + 1 by omega] at ha
        rw [show r + 1 + 1 = r + 2 by omega, show 2 * k' + 1 + 1 = 2 * k' + 2 by omega] at hb
        push_cast [kz, c32] at ha hb ⊢
        have ha' : ((r : ℤ) + 3) * ((r + 2).choose (2 * k' + 2) : ℤ) =
            (2 * (k' : ℤ) + 3) * ((r + 3).choose (2 * (k' + 1) + 1) : ℤ) := by linarith
        have hb' : ((r : ℤ) + 2) * ((r + 1).choose (2 * k' + 1) : ℤ) =
            (2 * (k' : ℤ) + 2) * ((r + 2).choose (2 * k' + 2) : ℤ) := by linarith
        calc ((r : ℤ) + 3) * ((r : ℤ) + 2) * ((r + 1).choose (2 * k' + 1) : ℤ)
          _ = ((r : ℤ) + 3) * (((r : ℤ) + 2) * ((r + 1).choose (2 * k' + 1) : ℤ)) := by ring
          _ = ((r : ℤ) + 3) * ((2 * (k' : ℤ) + 2) * ((r + 2).choose (2 * k' + 2) : ℤ)) := by rw [hb']
          _ = (2 * (k' : ℤ) + 2) * (((r : ℤ) + 3) * ((r + 2).choose (2 * k' + 2) : ℤ)) := by ring
          _ = (2 * (k' : ℤ) + 2) * ((2 * (k' : ℤ) + 3) * ((r + 3).choose (2 * (k' + 1) + 1) : ℤ)) := by rw [ha']
          _ = (2 * ((k' : ℤ) + 1)) * (2 * ((k' : ℤ) + 1) + 1) * ((r + 3).choose (2 * (k' + 1) + 1) : ℤ) := by ring
      push_cast at hb1 hb2 ⊢
      calc ((r : ℤ) + 3) ^ 2 * ((r : ℤ) + 2) ^ 2 * ((r : ℤ) + 1) ^ 2 *
            (Q (rz + 3) ((k' : ℤ) + 1) * ((r + 2).choose k' : ℤ) * ((r + 1).choose (2 * k' + 1) : ℤ))
        _ = Q (rz + 3) kz * (rz + 2) * (rz + 1) ^ 2 *
            (((r : ℤ) + 3) * ((r + 2).choose k' : ℤ)) *
            (((r : ℤ) + 3) * ((r : ℤ) + 2) * ((r + 1).choose (2 * k' + 1) : ℤ)) := by
            dsimp [rz, kz]; ring
        _ = Q (rz + 3) kz * (rz + 2) * (rz + 1) ^ 2 * (kz * c3k) * ((2 * kz) * (2 * kz + 1) * c32) := by
            rw [hb1, hb2]
        _ = Q (rz + 3) kz * (rz + 2) * (rz + 1) ^ 2 * kz * (2 * kz) * (2 * kz + 1) * c3k * c32 := by ring
  have hsub1 : r + 3 - 1 = r + 2 := by omega
  have hsub2 : r + 3 - 2 = r + 1 := by omega
  have hsub3 : r + 3 - 3 = r := by omega
  rw [hsub1, hsub2, hsub3, mul_sub, hGp, hGk]
  have hrhs :
      ((r + 3 : ℕ) : ℤ) ^ 2 * ((r + 2 : ℕ) : ℤ) ^ 2 * ((r + 1 : ℕ) : ℤ) ^ 2 *
        ((((r + 3 : ℕ) : ℤ) - 2) *
          (2 * (((r + 3 : ℕ) : ℤ) - 1) * (2 * ((r + 3 : ℕ) : ℤ) + 1) * (13 * ((r + 3 : ℕ) : ℤ) - 14) * F (r + 3) k +
            (-143 * ((r + 3 : ℕ) : ℤ) ^ 3 + 297 * ((r + 3 : ℕ) : ℤ) ^ 2 - 148 * ((r + 3 : ℕ) : ℤ) + 12) * F (r + 2) k -
            4 * (((r + 3 : ℕ) : ℤ) - 1) * (26 * ((r + 3 : ℕ) : ℤ) ^ 2 - 41 * ((r + 3 : ℕ) : ℤ) + 9) * F (r + 1) k -
            16 * (((r + 3 : ℕ) : ℤ) - 1) * (((r + 3 : ℕ) : ℤ) - 2) * (13 * ((r + 3 : ℕ) : ℤ) - 1) * F r k)) =
      (((rz + 3) - 2) *
        (2 * ((rz + 3) - 1) * (2 * (rz + 3) + 1) * (13 * (rz + 3) - 14) *
            ((rz + 3) ^ 2 * (rz + 2) ^ 2 * (rz + 1) ^ 2 * (c3k * c32)) +
          (-143 * (rz + 3) ^ 3 + 297 * (rz + 3) ^ 2 - 148 * (rz + 3) + 12) *
            ((rz + 2) ^ 2 * (rz + 1) ^ 2 * ((rz + 3 - kz) * (rz + 2 - 2 * kz) * c3k * c32)) -
          4 * ((rz + 3) - 1) * (26 * (rz + 3) ^ 2 - 41 * (rz + 3) + 9) *
            ((rz + 1) ^ 2 * ((rz + 3 - kz) * (rz + 2 - kz) * (rz + 2 - 2 * kz) * (rz + 1 - 2 * kz) * c3k * c32)) -
          16 * ((rz + 3) - 1) * ((rz + 3) - 2) * (13 * (rz + 3) - 1) *
            ((rz + 3 - kz) * (rz + 2 - kz) * (rz + 1 - kz) * (rz + 2 - 2 * kz) * (rz + 1 - 2 * kz) * (rz - 2 * kz) * c3k * c32))) := by
    rw [← hF3, ← hF2, ← hF1, ← hF0]
    push_cast [rz]
    ring
  rw [hrhs]
  unfold Q
  ring

private lemma main_proof : ∀ n : ℕ, 4 ≤ n →
    let m : ℤ := n
    2 * (m - 1) * (2 * m + 1) * (13 * m - 14) * a n +
      (-143 * m ^ 3 + 297 * m ^ 2 - 148 * m + 12) * a (n - 1) -
      4 * (m - 1) * (26 * m ^ 2 - 41 * m + 9) * a (n - 2) -
      16 * (m - 1) * (m - 2) * (13 * m - 1) * a (n - 3) = 0 := by
  intro n hn
  dsimp only
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 3 := ⟨n - 3, by omega⟩
  have hne : (((r + 3 : ℕ) : ℤ) - 2) ≠ 0 := by omega
  apply mul_left_cancel₀ hne
  rw [mul_zero]
  rw [a_eq_sum_range (n := r + 3) le_rfl,
      a_eq_sum_range (n := r + 3) (by omega : r + 3 - 1 ≤ r + 3),
      a_eq_sum_range (n := r + 3) (by omega : r + 3 - 2 ≤ r + 3),
      a_eq_sum_range (n := r + 3) (by omega : r + 3 - 3 ≤ r + 3)]
  have hsum :
      (((r + 3 : ℕ) : ℤ) - 2) *
        (2 * (((r + 3 : ℕ) : ℤ) - 1) * (2 * ((r + 3 : ℕ) : ℤ) + 1) * (13 * ((r + 3 : ℕ) : ℤ) - 14) *
            (∑ k ∈ Finset.range ((r + 3) / 2 + 1), F (r + 3) k) +
          (-143 * ((r + 3 : ℕ) : ℤ) ^ 3 + 297 * ((r + 3 : ℕ) : ℤ) ^ 2 - 148 * ((r + 3 : ℕ) : ℤ) + 12) *
            (∑ k ∈ Finset.range ((r + 3) / 2 + 1), F (r + 3 - 1) k) -
          4 * (((r + 3 : ℕ) : ℤ) - 1) * (26 * ((r + 3 : ℕ) : ℤ) ^ 2 - 41 * ((r + 3 : ℕ) : ℤ) + 9) *
            (∑ k ∈ Finset.range ((r + 3) / 2 + 1), F (r + 3 - 2) k) -
          16 * (((r + 3 : ℕ) : ℤ) - 1) * (((r + 3 : ℕ) : ℤ) - 2) * (13 * ((r + 3 : ℕ) : ℤ) - 1) *
            (∑ k ∈ Finset.range ((r + 3) / 2 + 1), F (r + 3 - 3) k)) =
      ∑ k ∈ Finset.range ((r + 3) / 2 + 1), (G (r + 3) (k + 1) - G (r + 3) k) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have hpt := wz_pointwise r k
    dsimp only at hpt
    linarith
  rw [hsum, Finset.sum_range_sub (fun k => G (r + 3) k)]
  have htop : G (r + 3) ((r + 3) / 2 + 1) = 0 := by
    unfold G
    have h0 : (r + 1).choose (2 * ((r + 3) / 2 + 1) - 1) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    simp [h0]
  have hbot : G (r + 3) 0 = 0 := by simp [G]
  rw [htop, hbot, sub_zero]

end OMA.S_oeis_a005726

theorem OMA.solution : type_of% @OMA.S_oeis_a005726.main :=
  OMA.S_oeis_a005726.main_proof
