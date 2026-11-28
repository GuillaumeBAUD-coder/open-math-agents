import FormalConjectures.ErdosProblems.«160»
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Log

/-!
# Improved Upper Bound $h(n) = O(n^{3/5})$ for Erdős Problem 160

We prove `Erdos160.erdos_160.better_upper` with the explicit bound `OMA.answer n = n ^ (3 / 5)`.
The construction colours every `x ∈ [1, n]` by applying an explicit 9-colouring `c41 : Fin 41 → Fin 9`
(whose every nondegenerate 4-term arithmetic progression modulo `41` uses at least `3` distinct
colours) independently to the first `m = Nat.log 41 n + 1` base-`41` digits of `x`. For any 4-term
arithmetic progression `a, a + d, a + 2d, a + 3d` in `[1, n]` (`d > 0`), letting `41 ^ j` be the
largest power of `41` dividing `d` (`d = u * 41 ^ j`, `u % 41 ≠ 0`), exact divisibility prevents any
base-`41` carry into digit `j`, so digit `j` traverses a nondegenerate 4-AP modulo `41` and already
exhibits at least `3` distinct colours. Since `9 ^ 5 = 59049 ≤ 68921 = 41 ^ 3`, this gives
`h(n) ≤ 9 ^ (Nat.log 41 n + 1) ≤ 9 * n ^ (3 / 5) = o(n ^ (2 / 3))`.
-/

noncomputable def OMA.answer : ℕ → ℝ := fun n => (n : ℝ) ^ ((3 : ℝ) / 5)

namespace OMA_Erdos160

open Asymptotics Filter Set
open scoped Topology

private def c41 : Fin 41 → Fin 9 :=
  ![2, 0, 0, 8, 3, 1, 8, 0, 7, 4, 1, 1, 6, 3, 6, 4, 0, 4, 8, 6, 7, 7, 2, 3, 0, 3, 4, 5, 5,
    1, 6, 7, 4, 7, 5, 5, 8, 1, 5, 8, 3]

private def mod41 (x : ℕ) : Fin 41 :=
  ⟨x % 41, Nat.mod_lt x (by decide)⟩

private def okPair41 (a d : Fin 41) : Bool :=
  d == 0 ||
  let x0 := c41 a
  let x1 := c41 (mod41 (a.val + d.val))
  let x2 := c41 (mod41 (a.val + 2 * d.val))
  let x3 := c41 (mod41 (a.val + 3 * d.val))
  decide (3 ≤ ({x0, x1, x2, x3} : Finset (Fin 9)).card)

private lemma c41_valid : ∀ a d : Fin 41, okPair41 a d = true := by decide

private lemma c41_ap_three (q u : ℕ) (hu : u % 41 ≠ 0) :
    3 ≤ ({c41 (mod41 (q + 0 * u)), c41 (mod41 (q + 1 * u)),
          c41 (mod41 (q + 2 * u)), c41 (mod41 (q + 3 * u))} : Finset (Fin 9)).card := by
  let a : Fin 41 := mod41 q
  let d : Fin 41 := mod41 u
  have hd0 : (d == 0) = false := by
    cases h : d == 0
    · rfl
    · exfalso
      have hd_eq : d = 0 := beq_iff_eq.mp h
      have hval : d.val = 0 := congrArg Fin.val hd_eq
      exact hu hval
  have hok := c41_valid a d
  unfold okPair41 at hok
  rw [hd0, Bool.false_or, decide_eq_true_eq] at hok
  have h0 : mod41 (q + 0 * u) = a := by rw [zero_mul, add_zero]
  have h1 : mod41 (q + 1 * u) = mod41 (a.val + d.val) := by
    apply Fin.ext
    simp [mod41, a, d, Nat.add_mod]
  have h2 : mod41 (q + 2 * u) = mod41 (a.val + 2 * d.val) := by
    apply Fin.ext
    simp [mod41, a, d, Nat.add_mod, Nat.mul_mod]
  have h3 : mod41 (q + 3 * u) = mod41 (a.val + 3 * d.val) := by
    apply Fin.ext
    simp [mod41, a, d, Nat.add_mod, Nat.mul_mod]
  rwa [h0, h1, h2, h3]

private lemma exists_div_pow_41 :
    ∀ (m d : ℕ), 0 < d → d < 41 ^ m → ∃ (j : Fin m) (u : ℕ), d = u * 41 ^ j.val ∧ u % 41 ≠ 0
  | 0, d, hd0, hdlt => absurd hdlt (by omega)
  | m + 1, d, hd0, hdlt => by
      by_cases hmod : d % 41 = 0
      · have hd_eq : d = (d / 41) * 41 := (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)).symm
        have hd'_pos : 0 < d / 41 := by omega
        have hd'_lt : d / 41 < 41 ^ m := by
          rw [pow_succ] at hdlt
          omega
        obtain ⟨j', u, hu_eq, hu_mod⟩ := exists_div_pow_41 m (d / 41) hd'_pos hd'_lt
        refine ⟨⟨j'.val + 1, Nat.succ_lt_succ j'.isLt⟩, u, ?_, hu_mod⟩
        rw [hd_eq, hu_eq, pow_succ, mul_assoc]
      · exact ⟨⟨0, Nat.succ_pos m⟩, d, by simp, hmod⟩

private def tupleCol (m : ℕ) (x : ℕ) : Fin m → Fin 9 :=
  fun j => c41 (mod41 (x / 41 ^ j.val))

private noncomputable def equivFin9Pow (m : ℕ) : (Fin m → Fin 9) ≃ Fin (9 ^ m) :=
  (Fintype.equivFin (Fin m → Fin 9)).trans (finCongr (by simp))

private noncomputable def colIcc (m n : ℕ) : Finset.Icc 1 n → Fin (9 ^ m) :=
  fun x => equivFin9Pow m (tupleCol m (x : ℕ))

private lemma h_le_nine_pow (m n : ℕ) (hn : n < 41 ^ m) :
    Erdos160.erdos_160.h n ≤ 9 ^ m := by
  unfold Erdos160.erdos_160.h
  refine Nat.sInf_le ⟨colIcc m n, ?_⟩
  rintro progression ⟨hsub, a, d, hcard, hset⟩
  have hmem_ap : ∀ t : ℕ, t < 4 → a + t * d ∈ progression := by
    intro t ht
    rw [hset]
    refine ⟨t, ?_, by simp⟩
    exact_mod_cast ht
  have hd_pos : 0 < d := by
    by_contra hd0
    have hd_zero : d = 0 := by omega
    subst hd_zero
    have heq_single : progression = {a} := by
      ext x
      rw [hset]
      constructor
      · rintro ⟨t, _, rfl⟩
        simp
      · rintro rfl
        exact ⟨0, by norm_num, by simp⟩
    rw [heq_single] at hcard
    simp at hcard
  have hx0 : a + 0 * d ∈ Finset.Icc 1 n := Finset.mem_coe.mp (hsub (hmem_ap 0 (by decide)))
  have hx1 : a + 1 * d ∈ Finset.Icc 1 n := Finset.mem_coe.mp (hsub (hmem_ap 1 (by decide)))
  have hx2 : a + 2 * d ∈ Finset.Icc 1 n := Finset.mem_coe.mp (hsub (hmem_ap 2 (by decide)))
  have hx3 : a + 3 * d ∈ Finset.Icc 1 n := Finset.mem_coe.mp (hsub (hmem_ap 3 (by decide)))
  have hd_lt : d < 41 ^ m := by
    have h3le : a + 3 * d ≤ n := (Finset.mem_Icc.mp hx3).2
    omega
  obtain ⟨j, u, hd_eq, hu_mod⟩ := exists_div_pow_41 m d hd_pos hd_lt
  let y0 : Finset.Icc 1 n := ⟨a + 0 * d, hx0⟩
  let y1 : Finset.Icc 1 n := ⟨a + 1 * d, hx1⟩
  let y2 : Finset.Icc 1 n := ⟨a + 2 * d, hx2⟩
  let y3 : Finset.Icc 1 n := ⟨a + 3 * d, hx3⟩
  let Scol : Finset (Fin (9 ^ m)) := {colIcc m n y0, colIcc m n y1, colIcc m n y2, colIcc m n y3}
  let proj : Fin (9 ^ m) → Fin 9 := fun z => ((equivFin9Pow m).symm z) j
  have hproj_y : ∀ (t : ℕ) (ht : a + t * d ∈ Finset.Icc 1 n),
      proj (colIcc m n ⟨a + t * d, ht⟩) = c41 (mod41 (a / 41 ^ j.val + t * u)) := by
    intro t ht
    simp only [proj, colIcc, Equiv.symm_apply_apply, tupleCol]
    have hdiv : (a + t * d) / 41 ^ j.val = a / 41 ^ j.val + t * u := by
      have hmul : a + t * d = a + (t * u) * 41 ^ j.val := by
        rw [hd_eq, mul_assoc]
      rw [hmul]
      exact Nat.add_mul_div_right a (t * u) (Nat.pow_pos (by decide : 0 < 41))
    rw [hdiv]
  have himg : Scol.image proj =
      {c41 (mod41 (a / 41 ^ j.val + 0 * u)), c41 (mod41 (a / 41 ^ j.val + 1 * u)),
       c41 (mod41 (a / 41 ^ j.val + 2 * u)), c41 (mod41 (a / 41 ^ j.val + 3 * u))} := by
    simp only [Scol, y0, y1, y2, y3, Finset.image_insert, Finset.image_singleton,
      hproj_y 0 hx0, hproj_y 1 hx1, hproj_y 2 hx2, hproj_y 3 hx3]
  have hScol_card : 3 ≤ Scol.card := by
    have h3 : 3 ≤ (Scol.image proj).card := by
      rw [himg]
      exact c41_ap_three (a / 41 ^ j.val) u hu_mod
    exact h3.trans Finset.card_image_le
  have hScol_sub : (Scol : Set (Fin (9 ^ m))) ⊆
      colIcc m n '' {k : Finset.Icc 1 n | (k : ℕ) ∈ progression} := by
    intro z hz
    simp only [Scol, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨y0, hmem_ap 0 (by decide), rfl⟩
    · exact ⟨y1, hmem_ap 1 (by decide), rfl⟩
    · exact ⟨y2, hmem_ap 2 (by decide), rfl⟩
    · exact ⟨y3, hmem_ap 3 (by decide), rfl⟩
  calc 3 ≤ Scol.card := hScol_card
    _ = (Scol : Set (Fin (9 ^ m))).ncard := (Set.ncard_coe_finset Scol).symm
    _ ≤ (colIcc m n '' {k : Finset.Icc 1 n | (k : ℕ) ∈ progression}).ncard :=
      Set.ncard_le_ncard hScol_sub (Set.toFinite _)

private lemma nine_pow_log_le_rpow (n : ℕ) (hn : 1 ≤ n) :
    ((9 ^ (Nat.log 41 n + 1) : ℕ) : ℝ) ≤ 9 * (n : ℝ) ^ ((3 : ℝ) / 5) := by
  set L := Nat.log 41 n
  have h41_le : 41 ^ L ≤ n := Nat.pow_log_le_self 41 (by omega)
  have hpow5 : ((9 : ℝ) ^ L) ^ 5 ≤ ((n : ℝ) ^ ((3 : ℝ) / 5)) ^ 5 := by
    have hlhs : ((9 : ℝ) ^ L) ^ 5 = ((59049 : ℝ) ^ L) := by
      rw [← pow_right_comm]
      norm_num
    have hmid1 : (59049 : ℝ) ^ L ≤ (68921 : ℝ) ^ L :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) L
    have hmid2 : (68921 : ℝ) ^ L = (((41 ^ L : ℕ) : ℝ) ^ 3) := by
      push_cast
      rw [← pow_right_comm]
      norm_num
    have hmid3 : (((41 ^ L : ℕ) : ℝ) ^ 3) ≤ (n : ℝ) ^ 3 := by
      have hcast : ((41 ^ L : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h41_le
      exact pow_le_pow_left₀ (by positivity) hcast 3
    have hrhs : (n : ℝ) ^ 3 = ((n : ℝ) ^ ((3 : ℝ) / 5)) ^ 5 := by
      rw [← Real.rpow_natCast ((n : ℝ) ^ ((3 : ℝ) / 5)) 5,
        ← Real.rpow_mul (Nat.cast_nonneg n)]
      norm_num
    linarith [hlhs, hmid1, hmid2, hmid3, hrhs]
  have h9L : (9 : ℝ) ^ L ≤ (n : ℝ) ^ ((3 : ℝ) / 5) :=
    le_of_pow_le_pow_left₀ (by norm_num : (5 : ℕ) ≠ 0) (by positivity) hpow5
  have hsplit : ((9 ^ (L + 1) : ℕ) : ℝ) = 9 * (9 : ℝ) ^ L := by
    rw [pow_succ']
    push_cast
    ring
  rw [hsplit]
  linarith

theorem main_proof :
    (fun n => (Erdos160.erdos_160.h n : ℝ)) =O[atTop] OMA.answer ∧
    OMA.answer =o[atTop] fun n => (n : ℝ) ^ ((2 : ℝ) / 3) := by
  refine ⟨?_, ?_⟩
  · refine IsBigO.of_bound 9 ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hlt : n < 41 ^ (Nat.log 41 n + 1) := Nat.lt_pow_succ_log_self (by decide : 1 < 41) n
    have hh : (Erdos160.erdos_160.h n : ℝ) ≤ ((9 ^ (Nat.log 41 n + 1) : ℕ) : ℝ) := by
      exact_mod_cast h_le_nine_pow (Nat.log 41 n + 1) n hlt
    have hbound := nine_pow_log_le_rpow n hn
    dsimp only [OMA.answer]
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    exact hh.trans hbound
  · rw [isLittleO_iff_tendsto']
    · have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (-((1 : ℝ) / 15))) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 15)).comp
          tendsto_natCast_atTop_atTop
      refine hlim.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
      dsimp only [OMA.answer]
      rw [← Real.rpow_sub hpos]
      congr 1
      norm_num
    · filter_upwards [eventually_ge_atTop 1] with n hn h0
      have hpos : (0 : ℝ) < (n : ℝ) ^ ((2 : ℝ) / 3) :=
        Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
      linarith

end OMA_Erdos160

theorem OMA.solution :
    Erdos160.erdos_160.better_upper.answer = OMA.answer →
    type_of% @Erdos160.erdos_160.better_upper := by
  intro h
  rw [h]
  exact OMA_Erdos160.main_proof
