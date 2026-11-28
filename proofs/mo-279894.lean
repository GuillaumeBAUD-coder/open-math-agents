import OMAStatements.S_mo_279894
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Proof of MathOverflow 279894

We embed both sides into a two-parameter family `P n k` (staircase matrix permanents) and
`S n k = ∑' m, m^k * (m + 1)^(n - k) / 2^(m + 1)` for `k ≤ n`, satisfying the same initial value,
boundary doubling `F (n + 1) 0 = 2 * F (n + 1) (n + 1)`, and step difference
`F (n + 1) k - F (n + 1) (k + 1) = F n k`.
-/

namespace OMA.MO279894

open Equiv Finset Matrix

def M (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j : Fin n => if i.val = 0 ∨ j.val < i.val then 1 else 2

def C (n k : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j : Fin n => if j.val < i.val ∨ (i.val < k ∧ j.val = i.val) then 1 else 2

noncomputable def P (n k : ℕ) : ℝ := (C n k).permanent

noncomputable def S (n k : ℕ) : ℝ :=
  ∑' m : ℕ, (m : ℝ) ^ k * ((m : ℝ) + 1) ^ (n - k) / 2 ^ (m + 1)

private lemma P_diag (n : ℕ) : P n n = (M n).permanent := by
  rcases n with _ | m
  · simp [P, permanent_isEmpty]
  · rw [P, ← permanent_permute_cols (Equiv.addRight (1 : Fin (m + 1))) (M (m + 1))]
    congr 1; ext i j
    simp only [C, M, submatrix_apply, of_apply, id_eq, coe_addRight]
    by_cases h : i = Fin.last m
    · subst h
      have h1 : (Fin.last m + (1 : Fin (m + 1))).val = 0 := by rw [Fin.val_add_one]; simp
      have h2 : j.val < (Fin.last m).val ∨ (Fin.last m).val < m + 1 ∧ j.val = (Fin.last m).val := by
        simp only [Fin.val_last]; omega
      simp only [h1, h2, true_or, ↓reduceIte]
    · have h1 : (i + (1 : Fin (m + 1))).val = i.val + 1 := by rw [Fin.val_add_one]; simp [h]
      have h2 : (j.val < i.val ∨ i.val < m + 1 ∧ j.val = i.val) ↔ (i.val + 1 = 0 ∨ j.val < i.val + 1) := by
        omega
      simp only [h1, h2]

private lemma P_zero (n : ℕ) : P (n + 1) 0 = 2 * P (n + 1) (n + 1) := by
  rw [P_diag, P, ← updateRow_eq_self (M (n + 1)) 0, ← permanent_updateRow_smul]
  congr 1; ext i j
  by_cases h : i = 0
  · subst h; simp [C, M]
  · simp [C, M, h]

private lemma perm_sub {n : ℕ} (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (k : Fin (n + 1))
    (hkk : A k k - B k k = 1) (ho : ∀ i j, i ≠ k ∨ j ≠ k → A i j = B i j) :
    A.permanent - B.permanent = (A.submatrix k.succAbove k.succAbove).permanent := by
  unfold permanent; rw [← sum_sub_distrib]
  have ht : ∀ σ : Perm (Fin (n + 1)),
      (∏ j, A (σ j) j) - (∏ j, B (σ j) j) = if σ k = k then ∏ j ∈ univ.erase k, A (σ j) j else 0 := by
    intro σ; split_ifs with hσ
    · rw [← mul_prod_erase univ _ (mem_univ k), ← mul_prod_erase univ _ (mem_univ k),
        prod_congr rfl fun j hj => (ho _ _ (Or.inr (ne_of_mem_erase hj))).symm,
        hσ, ← sub_mul, hkk, one_mul]
    · rw [prod_congr rfl fun j _ => if hj : j = k then hj ▸ ho _ _ (Or.inl hσ) else ho _ _ (Or.inr hj),
        sub_self]
  simp_rw [ht, ← sum_filter]; symm
  let e : Fin n ≃ {x : Fin (n + 1) // x ≠ k} :=
    ofBijective (fun i => ⟨k.succAbove i, Fin.succAbove_ne k i⟩)
      ⟨fun _ _ h => Fin.succAbove_right_injective (congrArg Subtype.val h),
       fun ⟨_, hx⟩ => let ⟨i, hi⟩ := Fin.exists_succAbove_eq hx; ⟨i, Subtype.ext hi⟩⟩
  let L : Perm (Fin n) → Perm (Fin (n + 1)) := fun τ => Perm.ofSubtype (e.permCongr τ)
  have hLk : ∀ τ, L τ k = k := fun τ => Perm.ofSubtype_apply_of_not_mem _ (by simp)
  have hLs : ∀ τ i, L τ (k.succAbove i) = k.succAbove (τ i) := fun τ i => by
    change Perm.ofSubtype (e.permCongr τ) (e i : Fin (n + 1)) = (e (τ i)).val
    rw [Perm.ofSubtype_apply_coe, permCongr_apply, e.symm_apply_apply]
  refine sum_bij (fun τ _ => L τ) (fun τ _ => by simp [hLk])
    (fun _ _ _ _ h => Perm.ext fun i => by simpa [hLs] using congrArg (fun σ : Perm _ => σ (k.succAbove i)) h)
    (fun σ hσ => ?_) (fun τ _ => prod_bij (fun i _ => k.succAbove i)
      (fun i _ => mem_erase.mpr ⟨Fin.succAbove_ne k i, mem_univ _⟩)
      (fun _ _ _ _ h => Fin.succAbove_right_injective h)
      (fun _ hj => let ⟨i, hi⟩ := Fin.exists_succAbove_eq (ne_of_mem_erase hj); ⟨i, mem_univ _, hi⟩)
      (fun i _ => by simp [submatrix_apply, hLs]))
  simp only [mem_filter, mem_univ, true_and] at hσ
  have hi : ∀ x, σ x ≠ k ↔ x ≠ k := fun x =>
    ⟨fun h hx => h (hx ▸ hσ), fun h hx => h (σ.injective (hx.trans hσ.symm))⟩
  refine ⟨e.symm.permCongr (σ.subtypePerm hi), mem_univ _, Perm.ext fun x => ?_⟩
  by_cases hx : x = k
  · rw [hx, hLk, hσ]
  · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hx
    rw [hLs]
    exact congrArg Subtype.val (e.apply_symm_apply (σ.subtypePerm hi (e i)))

private lemma P_step (n k : ℕ) (hk : k ≤ n) : P (n + 1) k - P (n + 1) (k + 1) = P n k := by
  let k0 : Fin (n + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
  rw [P, P, perm_sub _ _ k0 (by simp [C, k0]; norm_num)]
  · unfold P; congr 1; ext i j
    simp only [C, submatrix_apply, of_apply]
    have h1 : (k0.succAbove j).val < (k0.succAbove i).val ↔ j.val < i.val :=
      Fin.succAbove_lt_succAbove_iff
    have h2 : (k0.succAbove j).val = (k0.succAbove i).val ↔ j.val = i.val :=
      ⟨fun h => congrArg Fin.val (Fin.succAbove_right_injective (Fin.ext h)), fun h => by rw [Fin.ext h]⟩
    have h3 : (k0.succAbove i).val < k ↔ i.val < k := by
      by_cases h : i.castSucc < k0
      · rw [Fin.succAbove_of_castSucc_lt k0 i h]; simp [Fin.lt_def, k0] at h ⊢
      · rw [Fin.succAbove_of_le_castSucc k0 i (not_lt.mp h)]
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ, k0] at h ⊢; omega
    simp only [h1, h2, h3]
  · intro i j hij
    have : i.val ≠ k ∨ j.val ≠ k := hij.imp (fun h e => h (Fin.ext e)) (fun h e => h (Fin.ext e))
    simp only [C, of_apply, show (j.val < i.val ∨ i.val < k ∧ j.val = i.val) ↔
      (j.val < i.val ∨ i.val < k + 1 ∧ j.val = i.val) by omega]

private lemma sm (a b : ℕ) :
    Summable fun m : ℕ => (m : ℝ) ^ a * ((m : ℝ) + 1) ^ b / 2 ^ (m + 1) := by
  have h : ∀ r, Summable fun m : ℕ => (m : ℝ) ^ r / 2 ^ (m + 1) := fun r =>
    ((summable_pow_mul_geometric_of_norm_lt_one r (by norm_num : ‖(2⁻¹ : ℝ)‖ < 1)).mul_left 2⁻¹).congr
      fun m => by rw [div_eq_mul_inv, pow_succ, mul_inv, inv_pow]; ring
  refine (summable_sum fun j (_ : j ∈ range (b + 1)) =>
    (h (a + j)).mul_left (b.choose j : ℝ)).congr fun m => ?_
  rw [add_pow, Finset.mul_sum, div_eq_mul_inv, Finset.sum_mul]
  exact sum_congr rfl fun j _ => by simp only [one_pow, mul_one, pow_add, div_eq_mul_inv]; ring

private lemma S_zero (n : ℕ) : S (n + 1) 0 = 2 * S (n + 1) (n + 1) := by
  simp only [S, pow_zero, one_mul, Nat.sub_zero, Nat.sub_self, mul_one]
  have hs : Summable fun m : ℕ => (m : ℝ) ^ (n + 1) / 2 ^ (m + 1) := by simpa using sm (n + 1) 0
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_pow (Nat.succ_ne_zero n), zero_div, zero_add, Nat.cast_add,
    Nat.cast_one, ← tsum_mul_left]
  exact tsum_congr fun m => by ring

private lemma S_step (n k : ℕ) (hk : k ≤ n) : S (n + 1) k - S (n + 1) (k + 1) = S n k := by
  rw [S, S, S, ← (sm k (n + 1 - k)).tsum_sub (sm (k + 1) (n + 1 - (k + 1)))]
  refine tsum_congr fun m => ?_
  rw [show n + 1 - k = (n - k) + 1 by omega, show n + 1 - (k + 1) = n - k by omega, pow_succ,
    pow_succ]
  ring

private lemma P_eq_S : ∀ n k, k ≤ n → P n k = S n k := by
  intro n; induction n with
  | zero =>
    intro k hk; obtain rfl : k = 0 := by omega
    rw [P, permanent_isEmpty, S]
    simp only [Nat.sub_zero, pow_zero, mul_one]
    rw [show (fun m : ℕ => (1 : ℝ) / 2 ^ (m + 1)) = fun m => 2⁻¹ * (2⁻¹ : ℝ) ^ m from
      funext fun m => by rw [div_eq_mul_inv, one_mul, pow_succ, mul_inv, inv_pow, mul_comm],
      tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num)]
    norm_num
  | succ n ih =>
    have hc : ∀ k ≤ n + 1, P (n + 1) k - S (n + 1) k = P (n + 1) 0 - S (n + 1) 0 := by
      intro k; induction k with
      | zero => intro _; rfl
      | succ k ihk =>
        intro hk
        have := P_step n k (by omega)
        have := S_step n k (by omega)
        have := ih k (by omega)
        have := ihk (by omega)
        linarith
    have h0 := hc (n + 1) le_rfl
    have := P_zero n
    have := S_zero n
    intro k hk; have := hc k hk; linarith

end OMA.MO279894

theorem OMA.solution : type_of% @OMA.S_mo_279894.main := by
  intro n _
  have h := OMA.MO279894.P_eq_S n n le_rfl
  rw [OMA.MO279894.P_diag] at h
  simpa only [OMA.MO279894.M, OMA.MO279894.S, Nat.sub_self, pow_zero, mul_one] using h
