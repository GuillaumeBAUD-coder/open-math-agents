import OMAStatements.S_oeis_a000247

-- Problem: A000247: a(n) = 2^n - n - 2.
-- Upstream: formal-conjectures statements/oeis-a000247.lean:0 (declaration OMA.S_oeis_a000247.main)
-- Credit: @datdzrgb
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a000247

open OMA.S_oeis_a000247
open scoped BigOperators Matrix

def vec (n t : ℕ) : Fin n → ℕ :=
  (unitPrimitiveMatrix n ^ t) *ᵥ (fun _ : Fin n => 1)

lemma vec_zero (n : ℕ) (i : Fin n) : vec n 0 i = 1 := by
  simp [vec]

lemma vec_succ (n t : ℕ) (i : Fin n) :
    vec n (t + 1) i = ∑ j : Fin n, unitPrimitiveMatrix n i j * vec n t j := by
  rw [vec, pow_succ', ← Matrix.mulVec_mulVec]
  rfl

lemma vec_succ_zero (n t : ℕ) (hn : 2 < n) :
    vec n (t + 1) ⟨0, by omega⟩ = vec n t ⟨1, by omega⟩ := by
  rw [vec_succ, Finset.sum_eq_single ⟨1, by omega⟩]
  · simp [unitPrimitiveMatrix]
  · intro j _ hj
    have hne : j.val ≠ 1 := fun h => hj (Fin.ext h)
    have hcond : ¬ (0 + 1 = j.val ∨ j.val + 1 = 0 ∨ ((⟨0, by omega⟩ : Fin n) = j ∧ 0 + 1 = n)) := by
      rintro (h | h | ⟨_, h⟩) <;> omega
    simp only [unitPrimitiveMatrix, Matrix.of_apply, if_neg hcond, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma vec_succ_mid (n t : ℕ) (i : Fin n) (h0 : 0 < i.val) (hhi : i.val + 1 < n) :
    vec n (t + 1) i = vec n t ⟨i.val - 1, by omega⟩ + vec n t ⟨i.val + 1, by omega⟩ := by
  rw [vec_succ]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨i.val - 1, by omega⟩)]
  have hfirst :
      unitPrimitiveMatrix n i ⟨i.val - 1, by omega⟩ * vec n t ⟨i.val - 1, by omega⟩ =
        vec n t ⟨i.val - 1, by omega⟩ := by
    have hcond : i.val + 1 = i.val - 1 ∨ i.val - 1 + 1 = i.val ∨
        (i = ⟨i.val - 1, by omega⟩ ∧ i.val + 1 = n) :=
      Or.inr (Or.inl (by omega))
    simp [unitPrimitiveMatrix, hcond]
  rw [hfirst]
  congr 1
  rw [Finset.sum_eq_single ⟨i.val + 1, by omega⟩]
  · simp [unitPrimitiveMatrix]
  · intro j hj hne2
    have hne1 : j ≠ ⟨i.val - 1, by omega⟩ := (Finset.mem_erase.mp hj).1
    have hval1 : j.val ≠ i.val - 1 := fun h => hne1 (Fin.ext h)
    have hval2 : j.val ≠ i.val + 1 := fun h => hne2 (Fin.ext h)
    have hcond : ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val ∨ (i = j ∧ i.val + 1 = n)) := by
      rintro (h | h | ⟨_, h⟩) <;> omega
    simp [unitPrimitiveMatrix, hcond]
  · intro h
    exfalso
    apply h
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro heq
    have := congrArg Fin.val heq
    dsimp at this
    omega

lemma vec_succ_last (n t : ℕ) (hn : 2 < n) :
    vec n (t + 1) ⟨n - 1, by omega⟩ =
      vec n t ⟨n - 2, by omega⟩ + vec n t ⟨n - 1, by omega⟩ := by
  rw [vec_succ]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨n - 2, by omega⟩)]
  have hfirst :
      unitPrimitiveMatrix n ⟨n - 1, by omega⟩ ⟨n - 2, by omega⟩ * vec n t ⟨n - 2, by omega⟩ =
        vec n t ⟨n - 2, by omega⟩ := by
    have hcond : n - 1 + 1 = n - 2 ∨ n - 2 + 1 = n - 1 ∨
        ((⟨n - 1, by omega⟩ : Fin n) = ⟨n - 2, by omega⟩ ∧ n - 1 + 1 = n) :=
      Or.inr (Or.inl (by omega))
    simp only [unitPrimitiveMatrix, Matrix.of_apply, if_pos hcond, one_mul]
  rw [hfirst]
  congr 1
  rw [Finset.sum_eq_single ⟨n - 1, by omega⟩]
  · have hcond : n - 1 + 1 = n - 1 ∨ n - 1 + 1 = n - 1 ∨
        ((⟨n - 1, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ ∧ n - 1 + 1 = n) :=
      Or.inr (Or.inr ⟨rfl, by omega⟩)
    rw [unitPrimitiveMatrix, Matrix.of_apply, if_pos hcond, one_mul]
  · intro j hj hne2
    have hne1 : j ≠ ⟨n - 2, by omega⟩ := (Finset.mem_erase.mp hj).1
    have hval1 : j.val ≠ n - 2 := fun h => hne1 (Fin.ext h)
    have hval2 : j.val ≠ n - 1 := fun h => hne2 (Fin.ext h)
    have hcond : ¬ (n - 1 + 1 = j.val ∨ j.val + 1 = n - 1 ∨
        ((⟨n - 1, by omega⟩ : Fin n) = j ∧ n - 1 + 1 = n)) := by
      rintro (h | h | ⟨heq, _⟩)
      · omega
      · omega
      · have := congrArg Fin.val heq
        dsimp at this
        omega
    simp [unitPrimitiveMatrix, hcond]
  · intro h
    exfalso
    apply h
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro heq
    have := congrArg Fin.val heq
    dsimp at this
    omega

lemma vec_eq_two_pow (n : ℕ) (hn : 2 < n) :
    ∀ t (i : Fin n), t ≤ i.val → vec n t i = 2 ^ t := by
  intro t
  induction t with
  | zero =>
    intro i _
    simp [vec_zero]
  | succ t ih =>
    intro i hti
    by_cases hlast : i.val + 1 = n
    · have hi : i = ⟨n - 1, by omega⟩ := Fin.ext (by change i.val = n - 1; omega)
      rw [hi, vec_succ_last n t hn]
      rw [ih ⟨n - 2, by omega⟩ (by change t ≤ n - 2; omega),
        ih ⟨n - 1, by omega⟩ (by change t ≤ n - 1; omega)]
      ring
    · rw [vec_succ_mid n t i (by omega) (by omega)]
      rw [ih ⟨i.val - 1, by omega⟩ (by change t ≤ i.val - 1; omega),
        ih ⟨i.val + 1, by omega⟩ (by change t ≤ i.val + 1; omega)]
      ring

lemma vec_diag_add_one (n : ℕ) (hn : 2 < n) :
    ∀ k (hk : k < n), vec n (k + 1) ⟨k, hk⟩ + 1 = 2 ^ (k + 1) := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [vec_succ_zero n 0 hn, vec_zero]
    norm_num
  | succ k ih =>
    intro hk
    by_cases hlast : k + 1 + 1 = n
    · have heq : (⟨k + 1, hk⟩ : Fin n) = ⟨n - 1, by omega⟩ :=
        Fin.ext (by change k + 1 = n - 1; omega)
      rw [heq, vec_succ_last n (k + 1) hn]
      have h1 : vec n (k + 1) ⟨n - 2, by omega⟩ + 1 = 2 ^ (k + 1) := by
        have hidx : (⟨n - 2, by omega⟩ : Fin n) = ⟨k, by omega⟩ :=
          Fin.ext (by change n - 2 = k; omega)
        rw [hidx]
        exact ih (by omega)
      have h2 : vec n (k + 1) ⟨n - 1, by omega⟩ = 2 ^ (k + 1) :=
        vec_eq_two_pow n hn (k + 1) ⟨n - 1, by omega⟩ (by change k + 1 ≤ n - 1; omega)
      have hpow : 2 ^ (k + 1 + 1) = 2 ^ (k + 1) + 2 ^ (k + 1) := by ring
      omega
    · rw [vec_succ_mid n (k + 1) ⟨k + 1, hk⟩ (Nat.zero_lt_succ k)
        (by change k + 1 + 1 < n; omega)]
      have h1 : vec n (k + 1) ⟨k + 1 - 1, by omega⟩ + 1 = 2 ^ (k + 1) := by
        have hidx : (⟨k + 1 - 1, by omega⟩ : Fin n) = ⟨k, by omega⟩ := Fin.ext rfl
        rw [hidx]
        exact ih (by omega)
      have h2 : vec n (k + 1) ⟨k + 1 + 1, by omega⟩ = 2 ^ (k + 1) :=
        vec_eq_two_pow n hn (k + 1) ⟨k + 1 + 1, by omega⟩ (by change k + 1 ≤ k + 1 + 1; omega)
      have hpow : 2 ^ (k + 1 + 1) = 2 ^ (k + 1) + 2 ^ (k + 1) := by ring
      change vec n (k + 1) ⟨k + 1 - 1, by omega⟩ + vec n (k + 1) ⟨k + 1 + 1, by omega⟩ + 1 = _
      omega

lemma vec_diag_add_three (n : ℕ) (hn : 2 < n) :
    ∀ k (hk : k + 3 ≤ n), vec n (k + 3) ⟨k, by omega⟩ + (k + 5) = 2 ^ (k + 3) := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [show (0 + 3 : ℕ) = 2 + 1 from rfl, vec_succ_zero n 2 hn]
    have h1 : vec n 2 ⟨1, by omega⟩ + 1 = 2 ^ 2 :=
      vec_diag_add_one n hn 1 (by omega)
    omega
  | succ k ih =>
    intro hk
    rw [show k + 1 + 3 = (k + 3) + 1 by omega]
    rw [vec_succ_mid n (k + 3) ⟨k + 1, by omega⟩ (Nat.zero_lt_succ k)
      (by change k + 1 + 1 < n; omega)]
    have h1 : vec n (k + 3) ⟨k + 1 - 1, by omega⟩ + (k + 5) = 2 ^ (k + 3) := by
      have hidx : (⟨k + 1 - 1, by omega⟩ : Fin n) = ⟨k, by omega⟩ := Fin.ext rfl
      rw [hidx]
      exact ih (by omega)
    have h2 : vec n (k + 3) ⟨k + 1 + 1, by omega⟩ + 1 = 2 ^ (k + 3) := by
      have hidx : (⟨k + 1 + 1, by omega⟩ : Fin n) = ⟨k + 2, by omega⟩ := Fin.ext rfl
      rw [hidx]
      exact vec_diag_add_one n hn (k + 2) (by omega)
    have hpow : 2 ^ ((k + 3) + 1) = 2 ^ (k + 3) + 2 ^ (k + 3) := by ring
    change vec n (k + 3) ⟨k + 1 - 1, by omega⟩ + vec n (k + 3) ⟨k + 1 + 1, by omega⟩ + _ = _
    omega

end OMA.P_oeis_a000247

theorem OMA.solution : type_of% @OMA.S_oeis_a000247.main := by
  refine ⟨by rfl, fun n hn => ?_⟩
  have h := OMA.P_oeis_a000247.vec_diag_add_three n hn (n - 3) (by omega)
  have hlen : n - 3 + 3 = n := by omega
  simp only [hlen] at h
  change OMA.P_oeis_a000247.vec n n ⟨n - 3, by omega⟩ = 2 ^ n - n - 2
  omega
