import OMAStatements.S_oeis_a060521
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

namespace OMA.P_oeis_a060521

open OMA.S_oeis_a060521

/-- Valid single column of height 3 (not all equal). -/
private def validCol (c : Fin 3 → Bool) : Prop :=
  ¬ (c 0 = c 1 ∧ c 1 = c 2)

private instance (c : Fin 3 → Bool) : Decidable (validCol c) := by
  unfold validCol; infer_instance

/-- Three consecutive columns have no horizontal 3-in-a-row. -/
private def okTriple (u v w : Fin 3 → Bool) : Prop :=
  ∀ i : Fin 3, ¬ (u i = v i ∧ v i = w i)

private instance (u v w : Fin 3 → Bool) : Decidable (okTriple u v w) := by
  unfold okTriple; infer_instance

/-- Hamming distance between two columns of height 3, as an element of `Fin 4`. -/
private def colDist (u v : Fin 3 → Bool) : Fin 4 :=
  ⟨(if u 0 ≠ v 0 then 1 else 0) + (if u 1 ≠ v 1 then 1 else 0) + (if u 2 ≠ v 2 then 1 else 0), by
    split_ifs <;> omega⟩

/-- The `4 × 4` lumped transfer matrix `M` over `ℤ`. -/
private def transMat : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 0, 1;
     0, 0, 1, 1;
     0, 1, 1, 1;
     1, 2, 2, 1]

/-- Natural-number version of the `4 × 4` transfer matrix. -/
private def transNat : Fin 4 → Fin 4 → ℕ
  | 0, 3 => 1
  | 1, 2 => 1
  | 1, 3 => 1
  | 2, 1 => 1
  | 2, 2 => 1
  | 2, 3 => 1
  | 3, 0 => 1
  | 3, 1 => 2
  | 3, 2 => 2
  | 3, 3 => 1
  | _, _ => 0

private lemma transMat_eq_nat (d d' : Fin 4) : transMat d d' = (transNat d d' : ℤ) := by
  fin_cases d <;> fin_cases d' <;> decide

private lemma transMat_char :
    transMat ^ 4 + (1 : Matrix (Fin 4) (Fin 4) ℤ) = 2 • transMat ^ 3 + 5 • transMat ^ 2 := by
  decide

/-- Number of valid next columns `w` with `okTriple u v w` and `colDist v w = d'` depends
only on `colDist u v`. -/
private lemma card_next_col (u v : Fin 3 → Bool) (hu : validCol u) (hv : validCol v) (d' : Fin 4) :
    (Finset.univ.filter (fun w : Fin 3 → Bool => validCol w ∧ okTriple u v w ∧ colDist v w = d')).card =
      transNat (colDist u v) d' := by
  revert u v hu hv d'
  decide

private lemma card_init_dist (d : Fin 4) :
    (Finset.univ.filter (fun p : (Fin 3 → Bool) × (Fin 3 → Bool) =>
      validCol p.1 ∧ validCol p.2 ∧ colDist p.1 p.2 = d)).card =
      match d.1 with | 0 => 6 | 1 => 12 | 2 => 12 | _ => 6 := by
  revert d
  decide

private lemma card_validCol :
    (Finset.univ.filter (fun c : Fin 3 → Bool => validCol c)).card = 6 := by
  decide

/-- Count of valid `3 × (n + 2)` grids whose last two columns have Hamming distance `d`. -/
private noncomputable def distCount (n : ℕ) (d : Fin 4) : ℕ :=
  Nat.card {g : Fin 3 → Fin (n + 2) → Bool //
    ValidGrid (n + 2) g ∧ colDist (fun i => g i ⟨n, by omega⟩) (fun i => g i ⟨n + 1, by omega⟩) = d}

private lemma a060521_one : a060521 1 = 6 := by
  classical
  unfold a060521
  have heq : {g : Fin 3 → Fin 1 → Bool // ValidGrid 1 g} ≃
      {c : Fin 3 → Bool // validCol c} :=
    { toFun := fun ⟨g, hg⟩ => ⟨fun i => g i 0, hg.1 0⟩
      invFun := fun ⟨c, hc⟩ => ⟨fun i _ => c i, ⟨fun j => by fin_cases j; exact hc, fun _ j hj => by omega⟩⟩
      left_inv := fun ⟨g, _⟩ => by ext i j; fin_cases j; rfl
      right_inv := fun ⟨c, _⟩ => rfl }
  rw [Nat.card_congr heq, Nat.card_eq_fintype_card, Fintype.card_subtype, card_validCol]

private lemma a060521_add_two_eq_sum (n : ℕ) :
    a060521 (n + 2) = ∑ d : Fin 4, distCount n d := by
  classical
  unfold a060521 distCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hpart := Finset.card_eq_sum_card_fiberwise
    (f := fun g : Fin 3 → Fin (n + 2) → Bool =>
      colDist (fun i => g i ⟨n, by omega⟩) (fun i => g i ⟨n + 1, by omega⟩))
    (s := Finset.univ.filter (fun g : Fin 3 → Fin (n + 2) → Bool => ValidGrid (n + 2) g))
    (t := (Finset.univ : Finset (Fin 4)))
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
  rw [hpart]
  apply Finset.sum_congr rfl
  intro d _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1; ext g; simp

private lemma distCount_zero (d : Fin 4) :
    distCount 0 d = match d.1 with | 0 => 6 | 1 => 12 | 2 => 12 | _ => 6 := by
  classical
  unfold distCount
  have heq : {g : Fin 3 → Fin 2 → Bool //
        ValidGrid 2 g ∧ colDist (fun i => g i ⟨0, by omega⟩) (fun i => g i ⟨1, by omega⟩) = d} ≃
      {p : (Fin 3 → Bool) × (Fin 3 → Bool) // validCol p.1 ∧ validCol p.2 ∧ colDist p.1 p.2 = d} :=
    { toFun := fun ⟨g, hg, hd⟩ => ⟨(fun i => g i 0, fun i => g i 1), hg.1 0, hg.1 1, hd⟩
      invFun := fun ⟨p, h1, h2, hd⟩ =>
        ⟨fun i j => if j.1 = 0 then p.1 i else p.2 i,
         ⟨⟨fun j => by fin_cases j; exact h1; exact h2, fun _ j hj => by omega⟩, hd⟩⟩
      left_inv := fun ⟨g, _, _⟩ => by
        ext i j; fin_cases j <;> rfl
      right_inv := fun ⟨p, _, _, _⟩ => by
        ext1; rfl }
  rw [Nat.card_congr heq, Nat.card_eq_fintype_card, Fintype.card_subtype, card_init_dist d]

private lemma distCount_succ (n : ℕ) (d' : Fin 4) :
    distCount (n + 1) d' = ∑ d : Fin 4, distCount n d * transNat d d' := by
  classical
  unfold distCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- Prefix map dropping the last column
  let pref : (Fin 3 → Fin (n + 3) → Bool) → (Fin 3 → Fin (n + 2) → Bool) :=
    fun g i j => g i ⟨j.1, by omega⟩
  let S := Finset.univ.filter (fun g : Fin 3 → Fin (n + 3) → Bool =>
    ValidGrid (n + 3) g ∧ colDist (fun i => g i ⟨n + 1, by omega⟩) (fun i => g i ⟨n + 2, by omega⟩) = d')
  let T := Finset.univ.filter (fun g0 : Fin 3 → Fin (n + 2) → Bool => ValidGrid (n + 2) g0)
  have hpart := Finset.card_eq_sum_card_fiberwise (f := pref) (s := S) (t := T) (fun g hg => by
    simp only [Finset.mem_coe, S, T, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    refine ⟨fun j => hg.1.1 ⟨j.1, by omega⟩, fun i j hj => hg.1.2 i j (by omega)⟩)
  rw [hpart]
  -- For each valid g0 ∈ T, the fiber over g0 has size transNat (colDist last two cols of g0) d'
  have hfiber : ∀ g0 ∈ T,
      (S.filter (fun g => pref g = g0)).card =
        transNat (colDist (fun i => g0 i ⟨n, by omega⟩) (fun i => g0 i ⟨n + 1, by omega⟩)) d' := by
    intro g0 hg0
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hg0
    set u : Fin 3 → Bool := fun i => g0 i ⟨n, by omega⟩
    set v : Fin 3 → Bool := fun i => g0 i ⟨n + 1, by omega⟩
    rw [← card_next_col u v (hg0.1 ⟨n, by omega⟩) (hg0.1 ⟨n + 1, by omega⟩) d']
    apply Finset.card_bij (fun g _ i => g i ⟨n + 2, by omega⟩)
    · intro g hg
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      have hu : (fun i => g i ⟨n, by omega⟩) = u := by
        ext i; exact congrFun (congrFun hg.2 i) ⟨n, by omega⟩
      have hv : (fun i => g i ⟨n + 1, by omega⟩) = v := by
        ext i; exact congrFun (congrFun hg.2 i) ⟨n + 1, by omega⟩
      refine ⟨hg.1.1.1 ⟨n + 2, by omega⟩, fun i => ?_, ?_⟩
      · have h3 := hg.1.1.2 i n (by omega)
        rwa [show g i ⟨n, by omega⟩ = u i from congrFun hu i,
             show g i ⟨n + 1, by omega⟩ = v i from congrFun hv i] at h3
      · rw [← hv]; exact hg.1.2
    · intro g1 h1 g2 h2 heq
      simp only [Finset.mem_filter] at h1 h2
      ext i j
      by_cases hj : j.1 < n + 2
      · have h1j := congrFun (congrFun h1.2 i) ⟨j.1, hj⟩
        have h2j := congrFun (congrFun h2.2 i) ⟨j.1, hj⟩
        exact h1j.trans h2j.symm
      · have hjeq : j = ⟨n + 2, by omega⟩ := Fin.ext (by dsimp; have := j.2; omega)
        rw [hjeq]; exact congrFun heq i
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      let g : Fin 3 → Fin (n + 3) → Bool := fun i j =>
        if h : j.1 < n + 2 then g0 i ⟨j.1, h⟩ else w i
      refine ⟨g, ?_, ?_⟩
      · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨⟨⟨fun j => ?_, fun i j hj => ?_⟩, ?_⟩, ?_⟩
        · by_cases h : j.1 < n + 2
          · simp only [g, h, dite_true]; exact hg0.1 ⟨j.1, h⟩
          · simp only [g, h, dite_false]; exact hw.1
        · by_cases h2 : j + 2 < n + 2
          · simp only [g, show j < n + 2 by omega, show j + 1 < n + 2 by omega, h2, dite_true]
            exact hg0.2 i j h2
          · have hjeq : j = n := by omega
            subst j
            have h1 : g i ⟨n, by omega⟩ = u i := by simp [g, u]
            have h2' : g i ⟨n + 1, by omega⟩ = v i := by simp [g, v]
            have h3 : g i ⟨n + 2, by omega⟩ = w i := by simp [g]
            rw [h1, h2', h3]
            exact hw.2.1 i
        · have hv : (fun i => g i ⟨n + 1, by omega⟩) = v := by
            ext i; simp [g, v]
          have hw' : (fun i => g i ⟨n + 2, by omega⟩) = w := by
            ext i; simp [g]
          rw [hv, hw']; exact hw.2.2
        · ext i j; simp [pref, g, j.2]
      · ext i; simp [g]
  rw [Finset.sum_congr rfl hfiber]
  -- Group T by colDist of last two columns
  have hgroup := Finset.sum_fiberwise_of_maps_to
    (s := T) (t := (Finset.univ : Finset (Fin 4)))
    (g := fun g0 : Fin 3 → Fin (n + 2) → Bool =>
      colDist (fun i => g0 i ⟨n, by omega⟩) (fun i => g0 i ⟨n + 1, by omega⟩))
    (fun _ _ => Finset.mem_univ _)
    (fun g0 => transNat (colDist (fun i => g0 i ⟨n, by omega⟩) (fun i => g0 i ⟨n + 1, by omega⟩)) d')
  rw [← hgroup]
  apply Finset.sum_congr rfl
  intro d _
  have hconst : ∑ g0 ∈ T.filter (fun g0 =>
        colDist (fun i => g0 i ⟨n, by omega⟩) (fun i => g0 i ⟨n + 1, by omega⟩) = d),
        transNat (colDist (fun i => g0 i ⟨n, by omega⟩) (fun i => g0 i ⟨n + 1, by omega⟩)) d' =
      ∑ _g0 ∈ T.filter (fun g0 =>
        colDist (fun i => g0 i ⟨n, by omega⟩) (fun i => g0 i ⟨n + 1, by omega⟩) = d),
        transNat d d' := by
    apply Finset.sum_congr rfl
    intro g0 hg0
    rw [Finset.mem_filter] at hg0
    rw [hg0.2]
  rw [hconst, Finset.sum_const, smul_eq_mul, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1; congr 1; ext g0; simp [T]

private noncomputable def vecZ (n : ℕ) : Fin 4 → ℤ :=
  fun d => (distCount n d : ℤ)

private lemma vecZ_succ (n : ℕ) :
    vecZ (n + 1) = Matrix.vecMul (vecZ n) transMat := by
  ext d'
  simp only [vecZ, Matrix.vecMul, dotProduct, distCount_succ, transMat_eq_nat]
  push_cast
  rfl

private lemma vecZ_eq_pow (n : ℕ) :
    vecZ n = Matrix.vecMul (vecZ 0) (transMat ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [vecZ_succ, ih, pow_succ, Matrix.vecMul_vecMul]

private lemma vecZ_rec (n : ℕ) :
    vecZ (n + 4) + vecZ n = 2 • vecZ (n + 3) + 5 • vecZ (n + 2) := by
  rw [vecZ_eq_pow (n + 4), vecZ_eq_pow n, vecZ_eq_pow (n + 3), vecZ_eq_pow (n + 2)]
  have hmat : transMat ^ (n + 4) + transMat ^ n =
      2 • transMat ^ (n + 3) + 5 • transMat ^ (n + 2) := by
    calc transMat ^ (n + 4) + transMat ^ n
        = transMat ^ n * (transMat ^ 4 + 1) := by rw [pow_add, mul_add, mul_one]
      _ = transMat ^ n * (2 • transMat ^ 3 + 5 • transMat ^ 2) := by rw [transMat_char]
      _ = 2 • transMat ^ (n + 3) + 5 • transMat ^ (n + 2) := by
          rw [mul_add, Matrix.mul_smul, Matrix.mul_smul, ← pow_add, ← pow_add]
  calc Matrix.vecMul (vecZ 0) (transMat ^ (n + 4)) + Matrix.vecMul (vecZ 0) (transMat ^ n)
      = Matrix.vecMul (vecZ 0) (transMat ^ (n + 4) + transMat ^ n) := (Matrix.vecMul_add _ _ _).symm
    _ = Matrix.vecMul (vecZ 0) (2 • transMat ^ (n + 3) + 5 • transMat ^ (n + 2)) := by rw [hmat]
    _ = 2 • Matrix.vecMul (vecZ 0) (transMat ^ (n + 3)) + 5 • Matrix.vecMul (vecZ 0) (transMat ^ (n + 2)) := by
        rw [Matrix.vecMul_add, Matrix.vecMul_smul, Matrix.vecMul_smul]

private lemma prove_main :
    ∀ n : ℕ, 1 ≤ n →
      a060521 (n + 4) + a060521 n = 2 * a060521 (n + 3) + 5 * a060521 (n + 2) := by
  intro n hn
  by_cases hn1 : n = 1
  · subst hn1
    have hv0 : vecZ 0 = ![6, 12, 12, 6] := by
      ext d; fin_cases d <;> simp [vecZ, distCount_zero]
    have ha1 : (a060521 1 : ℤ) = 6 := by exact_mod_cast a060521_one
    have ha3 : (a060521 3 : ℤ) = ∑ d : Fin 4, vecZ 1 d := by
      rw [a060521_add_two_eq_sum 1]; simp [vecZ]
    have ha4 : (a060521 4 : ℤ) = ∑ d : Fin 4, vecZ 2 d := by
      rw [a060521_add_two_eq_sum 2]; simp [vecZ]
    have ha5 : (a060521 5 : ℤ) = ∑ d : Fin 4, vecZ 3 d := by
      rw [a060521_add_two_eq_sum 3]; simp [vecZ]
    have hv1 : vecZ 1 = Matrix.vecMul ![6, 12, 12, 6] transMat := by rw [vecZ_succ, hv0]
    have hv2 : vecZ 2 = Matrix.vecMul ![6, 12, 12, 6] (transMat ^ 2) := by rw [vecZ_eq_pow, hv0]
    have hv3 : vecZ 3 = Matrix.vecMul ![6, 12, 12, 6] (transMat ^ 3) := by rw [vecZ_eq_pow, hv0]
    have hsum1 : ∑ d : Fin 4, Matrix.vecMul ![6, 12, 12, 6] transMat d = 102 := by decide
    have hsum2 : ∑ d : Fin 4, Matrix.vecMul ![6, 12, 12, 6] (transMat ^ 2) d = 378 := by decide
    have hsum3 : ∑ d : Fin 4, Matrix.vecMul ![6, 12, 12, 6] (transMat ^ 3) d = 1260 := by decide
    rw [hv1, hsum1] at ha3
    rw [hv2, hsum2] at ha4
    rw [hv3, hsum3] at ha5
    have hz : (a060521 (1 + 4) : ℤ) + (a060521 1 : ℤ) =
        2 * (a060521 (1 + 3) : ℤ) + 5 * (a060521 (1 + 2) : ℤ) := by
      rw [show (1 + 4 : ℕ) = 5 by rfl, show (1 + 3 : ℕ) = 4 by rfl, show (1 + 2 : ℕ) = 3 by rfl]
      omega
    exact_mod_cast hz
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hrec := vecZ_rec m
    have hsum : ∑ d : Fin 4, (vecZ (m + 4) + vecZ m) d =
        ∑ d : Fin 4, (2 • vecZ (m + 3) + 5 • vecZ (m + 2)) d :=
      congrArg (fun v : Fin 4 → ℤ => ∑ d : Fin 4, v d) hrec
    simp only [Pi.add_apply, Pi.smul_apply] at hsum
    simp only [nsmul_eq_mul, Nat.cast_ofNat, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    have hcast : ∀ k : ℕ, (a060521 (k + 2) : ℤ) = ∑ d : Fin 4, vecZ k d := fun k => by
      rw [a060521_add_two_eq_sum k]; simp [vecZ]
    have hz : (a060521 (m + 2 + 4) : ℤ) + (a060521 (m + 2) : ℤ) =
        2 * (a060521 (m + 2 + 3) : ℤ) + 5 * (a060521 (m + 2 + 2) : ℤ) := by
      rw [show m + 2 + 4 = (m + 4) + 2 by omega, show m + 2 + 3 = (m + 3) + 2 by omega,
          show m + 2 + 2 = (m + 2) + 2 by omega, hcast, hcast, hcast, hcast]
      exact hsum
    exact_mod_cast hz

end OMA.P_oeis_a060521

theorem OMA.solution : type_of% @OMA.S_oeis_a060521.main :=
  OMA.P_oeis_a060521.prove_main
