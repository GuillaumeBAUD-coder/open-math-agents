import OMAReductions.R_Erdos1_erdos_1_variants_least_N_9_R2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds

/-!
Reduction of `Erdos1.erdos_1.variants.least_N_9.R2.H1` (9-element sum-distinct sets in
`[1..151]` with `max >= 103`, `sum x^2 >= 87381`, `sum x >= 511`) into 4 balanced cases `H1..H4`.

`main` eliminates all `max <= 140` directly and raises the second-moment lower bound `Q = sum x^2`
on all remaining maxima `141..151` via:
1. Middle-layer span bounds, five-layer second-moment inequalities, and exact equal-size
   subset-sum gaps `g(0..6) = [0, 1, 2, 4, 7, 13, 22]`.
2. 14 pure-`Nat` Elkies-Karamata-Jensen finite-frequency trigonometric certificates raising `Q`
   to `132151` (`max = 151`), `132501` (`max = 150`), `132801` (`max in [141..149]`), and
   `135501` (`max <= 138`), refuting `max <= 137`.
3. A verified pure-`Nat` Kronecker base-256 bitset branch-and-bound solver refuting
   `max in {138, 139, 140}` directly in the Lean kernel.
-/

namespace OMA.R_Erdos1_erdos_1_variants_least_N_9_R2_H1_R1
open Finset Real

private lemma strictMono_nat_gap {m : ℕ} {f : Fin m → ℕ} (hf : StrictMono f)
    (i j : Fin m) (hij : i ≤ j) : f i + (j.val - i.val) ≤ f j := by
  suffices h : ∀ (b : ℕ) (hb : b < m) (a : Fin m), a.val ≤ b → f a + (b - a.val) ≤ f ⟨b, hb⟩ from
    h j.val j.isLt i hij
  intro b
  induction b with
  | zero =>
    intro hb a ha
    have : a = ⟨0, hb⟩ := Fin.ext (Nat.eq_zero_of_le_zero ha)
    simp [this]
  | succ b ih =>
    intro hb a ha
    by_cases hEq : a.val = b + 1
    · have : a = ⟨b + 1, hb⟩ := Fin.ext hEq
      simp [this]
    · have hb' : b < m := by omega
      have h1 := ih hb' a (by omega)
      have h2 : f ⟨b, hb'⟩ < f ⟨b + 1, hb⟩ :=
        hf (show (⟨b, hb'⟩ : Fin m) < ⟨b + 1, hb⟩ from Nat.lt_succ_self b)
      omega

private lemma centered_square_bound_even {k : ℕ} (f : Fin (2 * k) → ℕ) (hf : StrictMono f) (c : ℝ) :
    (∑ i ∈ range k, 2 * ((2 * k - 1 - 2 * i : ℕ) : ℝ) ^ 2) ≤
      ∑ i : Fin (2 * k), (2 * (f i : ℝ) - c) ^ 2 := by
  let v (i : ℕ) : ℝ := if h : i < 2 * k then (2 * (f ⟨i, h⟩ : ℝ) - c) ^ 2 else 0
  have hsum : (∑ i : Fin (2 * k), (2 * (f i : ℝ) - c) ^ 2) = ∑ i ∈ range (2 * k), v i := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact sum_congr rfl fun i _ => by simp [v, i.isLt]
  rw [hsum, show 2 * k = k + k by omega, sum_range_add,
    ← sum_range_reflect (fun i => v (k + i)) k, ← sum_add_distrib]
  refine sum_le_sum fun i hi => ?_
  have hi' : i < k := mem_range.mp hi
  have hi2 : i < 2 * k := by omega
  have hj2 : 2 * k - 1 - i < 2 * k := by omega
  have hidx : k + (k - 1 - i) = 2 * k - 1 - i := by omega
  rw [hidx]
  simp only [v, dif_pos hi2, dif_pos hj2]
  have hgap := strictMono_nat_gap hf ⟨i, hi2⟩ ⟨2 * k - 1 - i, hj2⟩ (show i ≤ 2 * k - 1 - i by omega)
  dsimp only at hgap
  have hd : f ⟨i, hi2⟩ + (2 * k - 1 - 2 * i) ≤ f ⟨2 * k - 1 - i, hj2⟩ := by omega
  let x : ℝ := f ⟨i, hi2⟩
  let y : ℝ := f ⟨2 * k - 1 - i, hj2⟩
  let d : ℝ := ((2 * k - 1 - 2 * i : ℕ) : ℝ)
  have hdxy : x + d ≤ y := by dsimp [x, y, d]; exact_mod_cast hd
  have hsq : d ^ 2 ≤ (y - x) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) (2 * k - 1 - 2 * i)]
  have hgoal : 2 * d ^ 2 ≤ (2 * x - c) ^ 2 + (2 * y - c) ^ 2 := by nlinarith [sq_nonneg (x + y - c)]
  have h2k : k + k - 1 - 2 * i = 2 * k - 1 - 2 * i := by omega
  simpa only [x, y, d, h2k] using hgoal

private lemma even_sq_sum_eval (k : ℕ) :
    3 * (∑ i ∈ range k, 2 * (2 * k - 1 - 2 * i) ^ 2) = 2 * k * ((2 * k) ^ 2 - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hshift : ∑ i ∈ range (k + 1), 2 * (2 * (k + 1) - 1 - 2 * i) ^ 2 =
        2 * (2 * k + 1) ^ 2 + ∑ i ∈ range k, 2 * (2 * k - 1 - 2 * i) ^ 2 := by
      rw [sum_range_succ']
      have hsub : ∀ i ∈ range k, 2 * (2 * (k + 1) - 1 - 2 * (i + 1)) ^ 2 = 2 * (2 * k - 1 - 2 * i) ^ 2 := by
        intro i hi
        have := mem_range.mp hi
        congr 2; omega
      rw [sum_congr rfl hsub, add_comm]
      have h0 : 2 * (k + 1) - 1 - 2 * 0 = 2 * k + 1 := by omega
      rw [h0]
    rw [hshift, mul_add, ih]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · decide
    · have h1 : 1 ≤ (2 * k) ^ 2 := by nlinarith
      have h2 : 1 ≤ (2 * (k + 1)) ^ 2 := by nlinarith
      zify [h1, h2]; ring

private lemma centered_square_bound_finset {S : Finset ℕ} {k : ℕ} (hcard : S.card = 2 * k) (c : ℝ) :
    ((2 * k * ((2 * k) ^ 2 - 1) : ℕ) : ℝ) / 3 ≤ ∑ x ∈ S, (2 * (x : ℝ) - c) ^ 2 := by
  let e := S.orderIsoOfFin hcard
  have hbij : ∑ x ∈ S, (2 * (x : ℝ) - c) ^ 2 = ∑ i : Fin (2 * k), (2 * ((e i : ℕ) : ℝ) - c) ^ 2 := by
    refine sum_bij (fun x hx => e.symm ⟨x, hx⟩) (fun _ _ => mem_univ _) ?_ ?_ ?_
    · intro a ha b hb h
      have := congrArg (fun idx => (e idx : ℕ)) h
      simpa using this
    · intro i _
      exact ⟨(e i : ℕ), (e i).2, by simp⟩
    · intro a ha
      simp
  rw [hbij]
  have h1 := centered_square_bound_even (fun i => (e i : ℕ)) (fun i j hij => e.strictMono hij) c
  have h2 : (3 : ℝ) * (∑ i ∈ range k, 2 * ((2 * k - 1 - 2 * i : ℕ) : ℝ) ^ 2) =
      ((2 * k * ((2 * k) ^ 2 - 1) : ℕ) : ℝ) := by
    exact_mod_cast even_sq_sum_eval k
  linarith

/- Section 1B: Layer-band 2nd-moment inequalities -/

private lemma card_powersetCard_mem {n k : ℕ} (i : Fin n) (hk : 1 ≤ k) :
    ((univ : Finset (Fin n)).powersetCard k |>.filter (fun U => i ∈ U)).card =
      Nat.choose (n - 1) (k - 1) := by
  have hbij : ((univ : Finset (Fin n)).powersetCard k |>.filter (fun U => i ∈ U)).card =
      ((univ.erase i).powersetCard (k - 1)).card := by
    refine card_bij (fun U _ => U.erase i) ?_ ?_ ?_
    · intro U hU
      rw [mem_filter, mem_powersetCard] at hU
      rw [mem_powersetCard]
      exact ⟨subset_erase.mpr ⟨subset_univ _, notMem_erase i U⟩, by rw [card_erase_of_mem hU.2, hU.1.2]⟩
    · intro U hU V hV hEq
      rw [mem_filter] at hU hV
      rw [← insert_erase hU.2, ← insert_erase hV.2, hEq]
    · intro V hV
      rw [mem_powersetCard] at hV
      have hiV : i ∉ V := fun h => (mem_erase.mp (hV.1 h)).1 rfl
      refine ⟨insert i V, ?_, erase_insert hiV⟩
      rw [mem_filter, mem_powersetCard]
      exact ⟨⟨subset_univ _, by rw [card_insert_of_notMem hiV, hV.2]; omega⟩, mem_insert_self i V⟩
  rw [hbij, card_powersetCard, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]

private lemma card_powersetCard_mem_pair {n k : ℕ} {i j : Fin n} (hij : i ≠ j) (hk : 2 ≤ k) :
    ((univ : Finset (Fin n)).powersetCard k |>.filter (fun U => i ∈ U ∧ j ∈ U)).card =
      Nat.choose (n - 2) (k - 2) := by
  have hbij : ((univ : Finset (Fin n)).powersetCard k |>.filter (fun U => i ∈ U ∧ j ∈ U)).card =
      (((univ.erase i).erase j).powersetCard (k - 2)).card := by
    refine card_bij (fun U _ => (U.erase i).erase j) ?_ ?_ ?_
    · intro U hU
      rw [mem_filter, mem_powersetCard] at hU
      rw [mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [mem_erase, mem_erase] at hx ⊢
        exact ⟨hx.1, hx.2.1, mem_univ _⟩
      · have hj' : j ∈ U.erase i := mem_erase.mpr ⟨hij.symm, hU.2.2⟩
        rw [card_erase_of_mem hj', card_erase_of_mem hU.2.1, hU.1.2]
        omega
    · intro U hU V hV hEq
      rw [mem_filter] at hU hV
      have hjU : j ∈ U.erase i := mem_erase.mpr ⟨hij.symm, hU.2.2⟩
      have hjV : j ∈ V.erase i := mem_erase.mpr ⟨hij.symm, hV.2.2⟩
      have h1 : U.erase i = V.erase i := by rw [← insert_erase hjU, ← insert_erase hjV, hEq]
      rw [← insert_erase hU.2.1, ← insert_erase hV.2.1, h1]
    · intro V hV
      rw [mem_powersetCard] at hV
      have hjV : j ∉ V := fun h => (mem_erase.mp (hV.1 h)).1 rfl
      have hiV : i ∉ V := fun h => (mem_erase.mp (mem_erase.mp (hV.1 h)).2).1 rfl
      have hiJV : i ∉ insert j V := fun h => by
        rcases mem_insert.mp h with rfl | h'
        · exact hij rfl
        · exact hiV h'
      refine ⟨insert i (insert j V), ?_, ?_⟩
      · rw [mem_filter, mem_powersetCard]
        refine ⟨⟨subset_univ _, ?_⟩, mem_insert_self i _, mem_insert_of_mem (mem_insert_self j V)⟩
        rw [card_insert_of_notMem hiJV, card_insert_of_notMem hjV, hV.2]; omega
      · rw [erase_insert hiJV, erase_insert hjV]
  have hjmem : j ∈ (univ : Finset (Fin n)).erase i := mem_erase.mpr ⟨hij.symm, mem_univ j⟩
  rw [hbij, card_powersetCard, card_erase_of_mem hjmem, card_erase_of_mem (mem_univ i), card_univ,
    Fintype.card_fin]
  rfl

private lemma sum_powersetCard_sum (a : Fin 9 → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    ∑ U ∈ (univ : Finset (Fin 9)).powersetCard k, ∑ i ∈ U, a i =
      (Nat.choose 8 (k - 1) : ℝ) * ∑ i : Fin 9, a i := by
  have hswap : ∑ U ∈ (univ : Finset (Fin 9)).powersetCard k, ∑ i ∈ U, a i =
      ∑ i : Fin 9, ∑ U ∈ (univ : Finset (Fin 9)).powersetCard k |>.filter (fun U => i ∈ U), a i := by
    calc ∑ U ∈ (univ : Finset (Fin 9)).powersetCard k, ∑ i ∈ U, a i
        = ∑ U ∈ (univ : Finset (Fin 9)).powersetCard k, ∑ i : Fin 9, if i ∈ U then a i else 0 := by
          refine sum_congr rfl fun U _ => ?_
          rw [sum_ite_mem, univ_inter]
      _ = ∑ i : Fin 9, ∑ U ∈ (univ : Finset (Fin 9)).powersetCard k, if i ∈ U then a i else 0 :=
          sum_comm
      _ = _ := sum_congr rfl fun i _ => (sum_filter _ _).symm
  rw [hswap]
  simp_rw [sum_const, card_powersetCard_mem (n := 9) _ hk, nsmul_eq_mul, ← mul_sum]

private lemma sum_powersetCard_sq_sum (a : Fin 9 → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    ∑ U ∈ (univ : Finset (Fin 9)).powersetCard k, (∑ i ∈ U, a i) ^ 2 =
      (Nat.choose 7 (k - 1) : ℝ) * (∑ i : Fin 9, a i ^ 2) +
      (if k = 1 then (0 : ℝ) else (Nat.choose 7 (k - 2) : ℝ)) * (∑ i : Fin 9, a i) ^ 2 := by
  by_cases hk1 : k = 1
  · subst hk1
    simp only [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, one_mul, ite_true, zero_mul, add_zero]
    rw [powersetCard_one, sum_map]
    simp [Function.Embedding.coeFn_mk]
  · have hk2 : 2 ≤ k := by omega
    simp only [hk1, ite_false]
    have hsq : ∀ U : Finset (Fin 9), (∑ i ∈ U, a i) ^ 2 =
        ∑ i ∈ U, a i ^ 2 + ∑ i ∈ U, ∑ j ∈ U.erase i, a i * a j := by
      intro U
      rw [sq, sum_mul_sum]
      have hsplit : ∀ i ∈ U, ∑ j ∈ U, a i * a j = a i ^ 2 + ∑ j ∈ U.erase i, a i * a j := by
        intro i hi
        rw [← add_sum_erase _ _ hi, sq]
      rw [sum_congr rfl hsplit, sum_add_distrib]
    rw [sum_congr rfl fun U _ => hsq U, sum_add_distrib]
    have hdiag : ∑ U ∈ (univ : Finset (Fin 9)).powersetCard k, ∑ i ∈ U, a i ^ 2 =
        (Nat.choose 8 (k - 1) : ℝ) * ∑ i : Fin 9, a i ^ 2 :=
      sum_powersetCard_sum (fun i => a i ^ 2) k hk
    have hoff : ∑ U ∈ (univ : Finset (Fin 9)).powersetCard k, ∑ i ∈ U, ∑ j ∈ U.erase i, a i * a j =
        (Nat.choose 7 (k - 2) : ℝ) * ((∑ i : Fin 9, a i) ^ 2 - ∑ i : Fin 9, a i ^ 2) := by
      have hswap : ∑ U ∈ (univ : Finset (Fin 9)).powersetCard k, ∑ i ∈ U, ∑ j ∈ U.erase i, a i * a j =
          ∑ i : Fin 9, ∑ j ∈ (univ : Finset (Fin 9)).erase i,
            ∑ U ∈ (univ : Finset (Fin 9)).powersetCard k |>.filter (fun U => i ∈ U ∧ j ∈ U), a i * a j := by
        calc ∑ U ∈ (univ : Finset (Fin 9)).powersetCard k, ∑ i ∈ U, ∑ j ∈ U.erase i, a i * a j
            = ∑ U ∈ (univ : Finset (Fin 9)).powersetCard k, ∑ i : Fin 9, ∑ j ∈ (univ : Finset (Fin 9)).erase i,
                if i ∈ U ∧ j ∈ U then a i * a j else 0 := by
              refine sum_congr rfl fun U _ => ?_
              have h1 : ∑ i ∈ U, ∑ j ∈ U.erase i, a i * a j =
                  ∑ i : Fin 9, if i ∈ U then ∑ j ∈ U.erase i, a i * a j else 0 := by
                rw [sum_ite_mem, univ_inter]
              rw [h1]
              refine sum_congr rfl fun i _ => ?_
              by_cases hi : i ∈ U
              · simp only [hi, true_and, if_true]
                rw [sum_ite_mem]
                refine sum_congr ?_ fun _ _ => rfl
                ext j; simp
              · simp [hi]
          _ = ∑ i : Fin 9, ∑ U ∈ (univ : Finset (Fin 9)).powersetCard k, ∑ j ∈ (univ : Finset (Fin 9)).erase i,
                if i ∈ U ∧ j ∈ U then a i * a j else 0 := sum_comm
          _ = ∑ i : Fin 9, ∑ j ∈ (univ : Finset (Fin 9)).erase i, ∑ U ∈ (univ : Finset (Fin 9)).powersetCard k,
                if i ∈ U ∧ j ∈ U then a i * a j else 0 := sum_congr rfl fun i _ => sum_comm
          _ = _ := sum_congr rfl fun i _ => sum_congr rfl fun j _ => (sum_filter _ _).symm
      rw [hswap]
      have hinner : ∀ i : Fin 9, ∀ j ∈ (univ : Finset (Fin 9)).erase i,
          ∑ U ∈ (univ : Finset (Fin 9)).powersetCard k |>.filter (fun U => i ∈ U ∧ j ∈ U), a i * a j =
            (Nat.choose 7 (k - 2) : ℝ) * (a i * a j) := by
        intro i j hj
        have hij : i ≠ j := (mem_erase.mp hj).1.symm
        rw [sum_const, card_powersetCard_mem_pair (n := 9) hij hk2, nsmul_eq_mul]
      have hsum2 : ∑ i : Fin 9, ∑ j ∈ (univ : Finset (Fin 9)).erase i, a i * a j =
          (∑ i : Fin 9, a i) ^ 2 - ∑ i : Fin 9, a i ^ 2 := by
        have := hsq univ
        linarith
      calc ∑ i : Fin 9, ∑ j ∈ (univ : Finset (Fin 9)).erase i,
              ∑ U ∈ (univ : Finset (Fin 9)).powersetCard k |>.filter (fun U => i ∈ U ∧ j ∈ U), a i * a j
          = ∑ i : Fin 9, ∑ j ∈ (univ : Finset (Fin 9)).erase i, (Nat.choose 7 (k - 2) : ℝ) * (a i * a j) :=
            sum_congr rfl fun i _ => sum_congr rfl fun j hj => hinner i j hj
        _ = (Nat.choose 7 (k - 2) : ℝ) * ∑ i : Fin 9, ∑ j ∈ (univ : Finset (Fin 9)).erase i, a i * a j := by
            simp_rw [← mul_sum]
        _ = _ := by rw [hsum2]
    rw [hdiag, hoff]
    have hpas : Nat.choose 8 (k - 1) = Nat.choose 7 (k - 2) + Nat.choose 7 (k - 1) := by
      have hk' : k - 1 = (k - 2) + 1 := by omega
      rw [hk', Nat.choose_succ_succ]
    have hpasR : (Nat.choose 8 (k - 1) : ℝ) = (Nat.choose 7 (k - 2) : ℝ) + (Nat.choose 7 (k - 1) : ℝ) := by
      exact_mod_cast hpas
    rw [hpasR]; ring

private lemma sum_powersetCard_centered_sq (a : Fin 9 → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    ∑ U ∈ (univ : Finset (Fin 9)).powersetCard k, (2 * ∑ i ∈ U, a i - ∑ i : Fin 9, a i) ^ 2 =
      4 * (Nat.choose 7 (k - 1) : ℝ) * (∑ i : Fin 9, a i ^ 2) +
      (4 * (if k = 1 then (0 : ℝ) else (Nat.choose 7 (k - 2) : ℝ)) -
        4 * (Nat.choose 8 (k - 1) : ℝ) + (Nat.choose 9 k : ℝ)) * (∑ i : Fin 9, a i) ^ 2 := by
  let S := ∑ i : Fin 9, a i
  have hexp : ∀ U : Finset (Fin 9),
      (2 * ∑ i ∈ U, a i - S) ^ 2 = 4 * (∑ i ∈ U, a i) ^ 2 - 4 * S * (∑ i ∈ U, a i) + S ^ 2 := by
    intro U; ring
  rw [sum_congr rfl fun U _ => hexp U, sum_add_distrib, sum_sub_distrib,
    ← mul_sum, ← mul_sum, sum_powersetCard_sq_sum a k hk, sum_powersetCard_sum a k hk,
    sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]
  dsimp [S]; ring

private lemma sum_powersetCard4_centered (a : Fin 9 → ℝ) :
    ∑ U ∈ (univ : Finset (Fin 9)).powersetCard 4, (2 * ∑ i ∈ U, a i - (8 / 9 : ℝ) * ∑ i : Fin 9, a i) ^ 2 =
      (140 / 9 : ℝ) * (9 * ∑ i : Fin 9, a i ^ 2 - (∑ i : Fin 9, a i) ^ 2) := by
  let S := ∑ i : Fin 9, a i
  have hexp : ∀ U : Finset (Fin 9),
      (2 * ∑ i ∈ U, a i - (8 / 9 : ℝ) * S) ^ 2 =
        4 * (∑ i ∈ U, a i) ^ 2 - (32 / 9 : ℝ) * S * (∑ i ∈ U, a i) + (64 / 81 : ℝ) * S ^ 2 := by
    intro U; ring
  rw [sum_congr rfl fun U _ => hexp U, sum_add_distrib, sum_sub_distrib,
    ← mul_sum, ← mul_sum, sum_powersetCard_sq_sum a 4 (by omega), sum_powersetCard_sum a 4 (by omega),
    sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num [Nat.choose]
  dsimp [S]; ring

private lemma five_layer_moments {a : Fin 9 → ℕ}
    (hinj : Function.Injective (fun U : Finset (Fin 9) => ∑ i ∈ U, a i)) :
    let S := ∑ i : Fin 9, a i
    let Q := ∑ i : Fin 9, a i ^ 2
    22108415 + S ^ 2 ≤ 256 * Q ∧
    9924583 + 3 * S ^ 2 ≤ 126 * Q ∧
    881995 + S ^ 2 ≤ 16 * Q ∧
    190509 + S ^ 2 ≤ 10 * Q ∧
    42863 + S ^ 2 ≤ 9 * Q := by
  classical
  let f : Finset (Fin 9) → ℕ := fun U => ∑ i ∈ U, a i
  let S : ℕ := ∑ i : Fin 9, a i
  let Q : ℕ := ∑ i : Fin 9, a i ^ 2
  let aR : Fin 9 → ℝ := fun i => (a i : ℝ)
  have hSR : ∑ i : Fin 9, aR i = (S : ℝ) := by simp [aR, S]
  have hQR : ∑ i : Fin 9, aR i ^ 2 = (Q : ℝ) := by simp [aR, Q]
  have hband : ∀ (ks : Finset ℕ) (m : ℕ) (c : ℝ),
      (∑ k ∈ ks, Nat.choose 9 k) = 2 * m →
      ((2 * m * ((2 * m) ^ 2 - 1) : ℕ) : ℝ) / 3 ≤
        ∑ k ∈ ks, ∑ U ∈ (univ : Finset (Fin 9)).powersetCard k, (2 * ∑ i ∈ U, aR i - c) ^ 2 := by
    intro ks m c hcard_ks
    let F := ks.biUnion (fun k => (univ : Finset (Fin 9)).powersetCard k)
    have hdisj : Set.PairwiseDisjoint (ks : Set ℕ) (fun k => (univ : Finset (Fin 9)).powersetCard k) := by
      intro k1 _ k2 _ hne
      change Disjoint ((univ : Finset (Fin 9)).powersetCard k1) ((univ : Finset (Fin 9)).powersetCard k2)
      rw [Finset.disjoint_left]
      intro U h1 h2
      rw [mem_powersetCard] at h1 h2
      exact hne (h1.2.symm.trans h2.2)
    have hcardF : F.card = 2 * m := by
      rw [card_biUnion hdisj, ← hcard_ks]
      refine sum_congr rfl fun k _ => ?_
      rw [card_powersetCard, card_univ, Fintype.card_fin]
    have hcardImg : (F.image f).card = 2 * m := by
      rw [card_image_of_injective _ hinj, hcardF]
    have hlb := centered_square_bound_finset hcardImg c
    have hsumImg : ∑ x ∈ F.image f, (2 * (x : ℝ) - c) ^ 2 =
        ∑ k ∈ ks, ∑ U ∈ (univ : Finset (Fin 9)).powersetCard k, (2 * ∑ i ∈ U, aR i - c) ^ 2 := by
      rw [sum_image (fun _ _ _ _ h => hinj h), sum_biUnion hdisj]
      refine sum_congr rfl fun k _ => sum_congr rfl fun U _ => ?_
      simp [aR]
    linarith
  have h1 : (22108415 : ℝ) + (S : ℝ) ^ 2 ≤ 256 * (Q : ℝ) := by
    have h := hband (Icc 1 8) 255 (S : ℝ) (by decide)
    have hsum : ∀ g : ℕ → ℝ, ∑ k ∈ Icc 1 8, g k =
        g 1 + g 2 + g 3 + g 4 + g 5 + g 6 + g 7 + g 8 := fun g => by
      simp [Finset.sum_Icc_succ_top]
    rw [hsum] at h
    rw [← hSR] at h
    repeat rw [sum_powersetCard_centered_sq aR _ (by omega)] at h
    rw [hSR, hQR] at h
    norm_num [Nat.choose] at h
    linarith
  have h2 : (9924583 : ℝ) + 3 * (S : ℝ) ^ 2 ≤ 126 * (Q : ℝ) := by
    have h := hband (Icc 2 7) 246 (S : ℝ) (by decide)
    have hsum : ∀ g : ℕ → ℝ, ∑ k ∈ Icc 2 7, g k =
        g 2 + g 3 + g 4 + g 5 + g 6 + g 7 := fun g => by
      simp [Finset.sum_Icc_succ_top]
    rw [hsum] at h
    rw [← hSR] at h
    repeat rw [sum_powersetCard_centered_sq aR _ (by omega)] at h
    rw [hSR, hQR] at h
    norm_num [Nat.choose] at h
    linarith
  have h3 : (881995 : ℝ) + (S : ℝ) ^ 2 ≤ 16 * (Q : ℝ) := by
    have h := hband (Icc 3 6) 210 (S : ℝ) (by decide)
    have hsum : ∀ g : ℕ → ℝ, ∑ k ∈ Icc 3 6, g k =
        g 3 + g 4 + g 5 + g 6 := fun g => by
      simp [Finset.sum_Icc_succ_top]
    rw [hsum] at h
    rw [← hSR] at h
    repeat rw [sum_powersetCard_centered_sq aR _ (by omega)] at h
    rw [hSR, hQR] at h
    norm_num [Nat.choose] at h
    linarith
  have h4 : (190509 : ℝ) + (S : ℝ) ^ 2 ≤ 10 * (Q : ℝ) := by
    have h := hband (Icc 4 5) 126 (S : ℝ) (by decide)
    have hsum : ∀ g : ℕ → ℝ, ∑ k ∈ Icc 4 5, g k = g 4 + g 5 := fun g => by
      simp [Finset.sum_Icc_succ_top]
    rw [hsum] at h
    rw [← hSR] at h
    repeat rw [sum_powersetCard_centered_sq aR _ (by omega)] at h
    rw [hSR, hQR] at h
    norm_num [Nat.choose] at h
    linarith
  have h5 : (42862.5 : ℝ) + (S : ℝ) ^ 2 ≤ 9 * (Q : ℝ) := by
    have h := hband ({4} : Finset ℕ) 63 ((8 / 9 : ℝ) * (S : ℝ)) (by decide)
    simp only [sum_singleton] at h
    rw [← hSR, sum_powersetCard4_centered aR, hSR, hQR] at h
    norm_num at h
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast h1
  · exact_mod_cast h2
  · exact_mod_cast h3
  · exact_mod_cast h4
  · have h5lt : 42862 + S ^ 2 < 9 * Q := by
      have : ((42862 + S ^ 2 : ℕ) : ℝ) < ((9 * Q : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    dsimp only [S, Q] at h5lt
    omega

/- Section 1C: Middle-layer span bounds & fast 60-bit EXACT_G -/

private lemma sum_sdiff_add_inter (A B : Finset (Fin 9)) (a : Fin 9 → ℕ) :
    ∑ i ∈ A \ B, a i + ∑ i ∈ A ∩ B, a i = ∑ i ∈ A, a i := by
  have h := sum_sdiff (s₁ := A ∩ B) (s₂ := A) inter_subset_left (f := a)
  have heq : A \ (A ∩ B) = A \ B := by ext x; simp
  rwa [heq] at h

private lemma sum_card_ge_bot {a : Fin 9 → ℕ} (ha : StrictAnti a) {U : Finset (Fin 9)} {k : ℕ}
    (hcard : U.card = k) (hk : k ≤ 9) :
    (∑ i ∈ univ.filter (fun i : Fin 9 => 9 - k ≤ i.val), a i) ≤ ∑ i ∈ U, a i := by
  let B := univ.filter (fun i : Fin 9 => 9 - k ≤ i.val)
  have hBcard : B.card = k := by
    have : B = (Ico (9 - k) 9).attach.image (fun x => ⟨x.1, (mem_Ico.mp x.2).2⟩) := by
      ext i; simp only [B, mem_filter, mem_univ, true_and, mem_image, mem_attach, true_and, Subtype.exists]
      constructor
      · intro hi; exact ⟨i.val, mem_Ico.mpr ⟨hi, i.isLt⟩, rfl⟩
      · rintro ⟨x, hx, rfl⟩; exact (mem_Ico.mp hx).1
    rw [this, card_image_of_injective]
    · rw [card_attach, Nat.card_Ico]; omega
    · intro x y h; exact Subtype.ext (congrArg Fin.val h)
  have hdiff_card : (B \ U).card = (U \ B).card := by
    have h1 := card_sdiff_add_card_inter B U
    have h2 := card_sdiff_add_card_inter U B
    rw [inter_comm] at h2
    omega
  have hsplit1 := (sum_sdiff_add_inter B U a).symm
  have hsplit2 := (sum_sdiff_add_inter U B a).symm
  rw [hsplit1, hsplit2, inter_comm B U]
  have hle : ∑ i ∈ B \ U, a i ≤ ∑ i ∈ U \ B, a i := by
    by_cases h0 : (B \ U).card = 0
    · rw [card_eq_zero.mp h0, card_eq_zero.mp (hdiff_card.symm.trans h0)]
    · have hminU : ∀ j ∈ U \ B, ∀ i ∈ B \ U, a i ≤ a j := by
        intro j hj i hi
        have hiB := (mem_filter.mp (mem_sdiff.mp hi).1).2
        have hjB : ¬ (9 - k ≤ j.val) := by
          intro h; exact (mem_sdiff.mp hj).2 (mem_filter.mpr ⟨mem_univ j, h⟩)
        exact le_of_lt (ha (show j < i by omega))
      let M := (B \ U).sup' (card_pos.mp (by omega)) a
      calc ∑ i ∈ B \ U, a i ≤ ∑ _i ∈ B \ U, M := sum_le_sum fun i hi => le_sup' a hi
        _ = (B \ U).card * M := by rw [sum_const, smul_eq_mul]
        _ = (U \ B).card * M := by rw [hdiff_card]
        _ = ∑ _j ∈ U \ B, M := by rw [sum_const, smul_eq_mul]
        _ ≤ ∑ j ∈ U \ B, a j := sum_le_sum fun j hj => sup'_le _ _ fun i hi => hminU j hj i hi
  omega

private lemma sum_card_le_top {a : Fin 9 → ℕ} (ha : StrictAnti a) {U : Finset (Fin 9)} {k : ℕ}
    (hcard : U.card = k) (hk : k ≤ 9) :
    ∑ i ∈ U, a i ≤ ∑ i ∈ univ.filter (fun i : Fin 9 => i.val < k), a i := by
  let T := univ.filter (fun i : Fin 9 => i.val < k)
  have hTcard : T.card = k := by
    have : T = (range k).attach.image (fun x => ⟨x.1, by have := mem_range.mp x.2; omega⟩) := by
      ext i; simp only [T, mem_filter, mem_univ, true_and, mem_image, mem_attach, true_and, Subtype.exists]
      constructor
      · intro hi; exact ⟨i.val, mem_range.mpr hi, rfl⟩
      · rintro ⟨x, hx, rfl⟩; exact mem_range.mp hx
    rw [this, card_image_of_injective]
    · rw [card_attach, card_range]
    · intro x y h; exact Subtype.ext (congrArg Fin.val h)
  have hdiff_card : (U \ T).card = (T \ U).card := by
    have h1 := card_sdiff_add_card_inter U T
    have h2 := card_sdiff_add_card_inter T U
    rw [inter_comm] at h2
    omega
  have hsplit1 := (sum_sdiff_add_inter U T a).symm
  have hsplit2 := (sum_sdiff_add_inter T U a).symm
  rw [hsplit1, hsplit2, inter_comm U T]
  have hle : ∑ i ∈ U \ T, a i ≤ ∑ i ∈ T \ U, a i := by
    by_cases h0 : (U \ T).card = 0
    · rw [card_eq_zero.mp h0, card_eq_zero.mp (hdiff_card.symm.trans h0)]
    · have hcmp : ∀ i ∈ U \ T, ∀ j ∈ T \ U, a i ≤ a j := by
        intro i hi j hj
        have hjT := (mem_filter.mp (mem_sdiff.mp hj).1).2
        have hiT : ¬ (i.val < k) := fun h => (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ i, h⟩)
        exact le_of_lt (ha (show j < i by omega))
      let M := (U \ T).sup' (card_pos.mp (by omega)) a
      calc ∑ i ∈ U \ T, a i ≤ ∑ _i ∈ U \ T, M := sum_le_sum fun i hi => le_sup' a hi
        _ = (U \ T).card * M := by rw [sum_const, smul_eq_mul]
        _ = (T \ U).card * M := by rw [hdiff_card]
        _ = ∑ _j ∈ T \ U, M := by rw [sum_const, smul_eq_mul]
        _ ≤ ∑ j ∈ T \ U, a j := sum_le_sum fun j hj => sup'_le _ _ fun i hi => hcmp i hi j hj
  omega


private lemma sum_cos_powerset {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ) (t : ℝ) :
    ∑ U ∈ s.powerset, Real.cos (t * (2 * ∑ i ∈ U, a i - ∑ i ∈ s, a i)) =
      (2 : ℝ) ^ s.card * ∏ i ∈ s, Real.cos (t * a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    rw [sum_powerset_insert hx, card_insert_of_notMem hx, prod_insert hx, sum_insert hx, ← sum_add_distrib]
    have hterm : ∀ U ∈ s.powerset,
        Real.cos (t * (2 * ∑ i ∈ U, a i - (a x + ∑ i ∈ s, a i))) +
        Real.cos (t * (2 * ∑ i ∈ insert x U, a i - (a x + ∑ i ∈ s, a i))) =
        2 * Real.cos (t * a x) * Real.cos (t * (2 * ∑ i ∈ U, a i - ∑ i ∈ s, a i)) := by
      intro U hU
      have hxU : x ∉ U := fun h => hx (mem_powerset.mp hU h)
      rw [sum_insert hxU]
      set B : ℝ := t * (2 * ∑ i ∈ U, a i - ∑ i ∈ s, a i)
      set A : ℝ := t * a x
      have h1 : t * (2 * ∑ i ∈ U, a i - (a x + ∑ i ∈ s, a i)) = B - A := by dsimp [A, B]; ring
      have h2 : t * (2 * (a x + ∑ i ∈ U, a i) - (a x + ∑ i ∈ s, a i)) = B + A := by dsimp [A, B]; ring
      rw [h1, h2, Real.cos_sub, Real.cos_add]
      ring
    rw [sum_congr rfl hterm, ← mul_sum, ih, pow_succ]
    ring

private lemma sum_cos_pos_half {a : Fin 9 → ℕ}
    (hinj : Function.Injective (fun U : Finset (Fin 9) => ∑ i ∈ U, a i)) (t : ℝ) :
    let S := ∑ i : Fin 9, a i
    let P := (univ : Finset (Fin 9)).powerset.filter (fun U => S < 2 * ∑ i ∈ U, a i)
    P.card = 256 ∧
    (∀ U ∈ P, (2 * ∑ i ∈ U, a i - S) % 2 = S % 2 ∧ 1 ≤ 2 * ∑ i ∈ U, a i - S ∧ 2 * ∑ i ∈ U, a i - S ≤ S) ∧
    Set.InjOn (fun U : Finset (Fin 9) => 2 * ∑ i ∈ U, a i - S) (P : Set (Finset (Fin 9))) ∧
    ∑ U ∈ P, Real.cos (t * ((2 * ∑ i ∈ U, a i - S : ℕ) : ℝ)) =
      256 * ∏ i : Fin 9, Real.cos (t * (a i : ℝ)) := by
  classical
  let S := ∑ i : Fin 9, a i
  let P := (univ : Finset (Fin 9)).powerset.filter (fun U => S < 2 * ∑ i ∈ U, a i)
  let Q := (univ : Finset (Fin 9)).powerset.filter (fun U => ¬ (S < 2 * ∑ i ∈ U, a i))
  have hcomp_sum : ∀ U : Finset (Fin 9), ∑ i ∈ univ \ U, a i + ∑ i ∈ U, a i = S := fun U =>
    sum_sdiff (subset_univ U)
  have hne_half : ∀ U : Finset (Fin 9), 2 * ∑ i ∈ U, a i ≠ S := by
    intro U h
    have hcs := hcomp_sum U
    have hEq : ∑ i ∈ univ \ U, a i = ∑ i ∈ U, a i := by omega
    have hUeq : univ \ U = U := hinj hEq
    have hcard : (univ \ U).card + U.card = (univ : Finset (Fin 9)).card := card_sdiff_add_card_eq_card (subset_univ U)
    rw [hUeq, card_univ, Fintype.card_fin] at hcard
    omega
  have hbij : ∀ U ∈ P, univ \ U ∈ Q := by
    intro U hU
    rw [mem_filter] at hU ⊢
    refine ⟨mem_powerset.mpr (subset_univ _), ?_⟩
    have := hcomp_sum U; omega
  have hbij' : ∀ U ∈ Q, univ \ U ∈ P := by
    intro U hU
    rw [mem_filter] at hU ⊢
    refine ⟨mem_powerset.mpr (subset_univ _), ?_⟩
    have := hcomp_sum U
    have := hne_half U
    omega
  have hcardPQ : P.card = Q.card := by
    refine card_bij (fun U _ => univ \ U) hbij ?_ ?_
    · intro U _ V _ h
      have h1 : univ \ (univ \ U) = univ \ (univ \ V) := congrArg (univ \ ·) h
      simpa [Finset.sdiff_sdiff_eq_self (subset_univ U), Finset.sdiff_sdiff_eq_self (subset_univ V)] using h1
    · intro V hV
      exact ⟨univ \ V, hbij' V hV, Finset.sdiff_sdiff_eq_self (subset_univ V)⟩
  have hcard_tot : P.card + Q.card = 512 := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin 9)).powerset)
      (p := fun U => S < 2 * ∑ i ∈ U, a i)
    rw [card_powerset, card_univ, Fintype.card_fin] at this
    exact this
  have hcardP : P.card = 256 := by omega
  have hprops : ∀ U ∈ P, (2 * ∑ i ∈ U, a i - S) % 2 = S % 2 ∧
      1 ≤ 2 * ∑ i ∈ U, a i - S ∧ 2 * ∑ i ∈ U, a i - S ≤ S := by
    intro U hU
    have hlt := (mem_filter.mp hU).2
    have hle : ∑ i ∈ U, a i ≤ S := sum_le_sum_of_subset (subset_univ U)
    omega
  have hinjP : Set.InjOn (fun U : Finset (Fin 9) => 2 * ∑ i ∈ U, a i - S) (P : Set (Finset (Fin 9))) := by
    intro U hU V hV hEq
    have h1 := (mem_filter.mp hU).2
    have h2 := (mem_filter.mp hV).2
    dsimp only at hEq
    exact hinj (by dsimp only; omega)
  have hsumQ : ∑ U ∈ Q, Real.cos (t * (2 * ∑ i ∈ U, (a i : ℝ) - ∑ i : Fin 9, (a i : ℝ))) =
      ∑ U ∈ P, Real.cos (t * (2 * ∑ i ∈ U, (a i : ℝ) - ∑ i : Fin 9, (a i : ℝ))) := by
    refine sum_bij (fun U _ => univ \ U) hbij' ?_ ?_ ?_
    · intro U _ V _ h
      have h1 : univ \ (univ \ U) = univ \ (univ \ V) := congrArg (univ \ ·) h
      simpa [Finset.sdiff_sdiff_eq_self (subset_univ U), Finset.sdiff_sdiff_eq_self (subset_univ V)] using h1
    · intro V hV
      exact ⟨univ \ V, hbij V hV, Finset.sdiff_sdiff_eq_self (subset_univ V)⟩
    · intro U _
      have hcs : ∑ i ∈ univ \ U, (a i : ℝ) + ∑ i ∈ U, (a i : ℝ) = ∑ i : Fin 9, (a i : ℝ) := by
        exact_mod_cast hcomp_sum U
      have hneg : t * (2 * ∑ i ∈ univ \ U, (a i : ℝ) - ∑ i : Fin 9, (a i : ℝ)) =
          -(t * (2 * ∑ i ∈ U, (a i : ℝ) - ∑ i : Fin 9, (a i : ℝ))) := by
        rw [← hcs]; ring
      rw [hneg, Real.cos_neg]
  have hsplit : ∑ U ∈ P, Real.cos (t * (2 * ∑ i ∈ U, (a i : ℝ) - ∑ i : Fin 9, (a i : ℝ))) +
      ∑ U ∈ Q, Real.cos (t * (2 * ∑ i ∈ U, (a i : ℝ) - ∑ i : Fin 9, (a i : ℝ))) =
      ∑ U ∈ (univ : Finset (Fin 9)).powerset, Real.cos (t * (2 * ∑ i ∈ U, (a i : ℝ) - ∑ i : Fin 9, (a i : ℝ))) :=
    sum_filter_add_sum_filter_not (s := (univ : Finset (Fin 9)).powerset)
      (p := fun U => S < 2 * ∑ i ∈ U, a i)
      (f := fun U => Real.cos (t * (2 * ∑ i ∈ U, (a i : ℝ) - ∑ i : Fin 9, (a i : ℝ))))
  have htot := sum_cos_powerset (univ : Finset (Fin 9)) (fun i => (a i : ℝ)) t
  rw [card_univ, Fintype.card_fin] at htot
  have hsumP_eq : ∑ U ∈ P, Real.cos (t * ((2 * ∑ i ∈ U, a i - S : ℕ) : ℝ)) =
      ∑ U ∈ P, Real.cos (t * (2 * ∑ i ∈ U, (a i : ℝ) - ∑ i : Fin 9, (a i : ℝ))) := by
    refine sum_congr rfl fun U hU => ?_
    have hlt := (mem_filter.mp hU).2
    have hcast : ((2 * ∑ i ∈ U, a i - S : ℕ) : ℝ) = 2 * ∑ i ∈ U, (a i : ℝ) - ∑ i : Fin 9, (a i : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      simp [S]
    rw [hcast]
  refine ⟨hcardP, hprops, hinjP, ?_⟩
  rw [hsumP_eq]
  linarith [hsplit, hsumQ, htot]

/- 2. Elementary alternating Taylor bounds for cos & sin on [0, ∞) -/

private lemma nonneg_of_hasDerivAt_nonneg {f f' : ℝ → ℝ}
    (h0 : 0 ≤ f 0) (hd : ∀ x ≥ 0, HasDerivAt f (f' x) x) (hp : ∀ x ≥ 0, 0 ≤ f' x) :
    ∀ x ≥ 0, 0 ≤ f x := by
  intro x hx
  rcases eq_or_lt_of_le hx with rfl | hpos
  · exact h0
  · have hcont : ContinuousOn f (Set.Icc 0 x) := fun y hy => (hd y hy.1).continuousAt.continuousWithinAt
    have hdiff : ∀ y ∈ Set.Ioo 0 x, HasDerivAt f (f' y) y := fun y hy => hd y (le_of_lt hy.1)
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f f' hpos hcont hdiff
    have hc' : 0 ≤ f' c := hp c (le_of_lt hc.1)
    rw [sub_zero] at hslope
    have : 0 ≤ f x - f 0 := by nlinarith [div_mul_cancel₀ (f x - f 0) (ne_of_gt hpos)]
    linarith

private lemma taylor_cos_sin_bounds (u : ℝ) (hu : 0 ≤ u) :
    (1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 + u ^ 8 / 40320 - u ^ 10 / 3628800 ≤ Real.cos u ∧
     Real.cos u ≤ 1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 + u ^ 8 / 40320) ∧
    (u - u ^ 3 / 6 + u ^ 5 / 120 - u ^ 7 / 5040 ≤ Real.sin u ∧
     Real.sin u ≤ u - u ^ 3 / 6 + u ^ 5 / 120 - u ^ 7 / 5040 + u ^ 9 / 362880) := by
  have h0 : ∀ x ≥ 0, 0 ≤ 1 - Real.cos x := fun x _ => by linarith [Real.cos_le_one x]
  have h1 : ∀ x ≥ 0, 0 ≤ x - Real.sin x := nonneg_of_hasDerivAt_nonneg (by norm_num)
    (fun x _ => (hasDerivAt_id' x).sub (Real.hasDerivAt_sin x)) h0
  have h2 : ∀ x ≥ 0, 0 ≤ x ^ 2 / 2 - 1 + Real.cos x := nonneg_of_hasDerivAt_nonneg (by norm_num)
    (fun x _ => by
      have hd := (((hasDerivAt_pow 2 x).div_const 2).sub (hasDerivAt_const x (1 : ℝ))).add (Real.hasDerivAt_cos x)
      simp only [Nat.cast_ofNat] at hd
      have heq : 2 * x ^ (2 - 1) / 2 - 0 + -Real.sin x = x - Real.sin x := by ring
      rwa [heq] at hd) h1
  have h3 : ∀ x ≥ 0, 0 ≤ x ^ 3 / 6 - x + Real.sin x := nonneg_of_hasDerivAt_nonneg (by norm_num)
    (fun x _ => by
      have hd := (((hasDerivAt_pow 3 x).div_const 6).sub (hasDerivAt_id' x)).add (Real.hasDerivAt_sin x)
      simp only [Nat.cast_ofNat] at hd
      have heq : 3 * x ^ (3 - 1) / 6 - 1 + Real.cos x = x ^ 2 / 2 - 1 + Real.cos x := by ring
      rwa [heq] at hd) h2
  have h4 : ∀ x ≥ 0, 0 ≤ x ^ 4 / 24 - x ^ 2 / 2 + 1 - Real.cos x := nonneg_of_hasDerivAt_nonneg (by norm_num)
    (fun x _ => by
      have hd := ((((hasDerivAt_pow 4 x).div_const 24).sub ((hasDerivAt_pow 2 x).div_const 2)).add
        (hasDerivAt_const x (1 : ℝ))).sub (Real.hasDerivAt_cos x)
      simp only [Nat.cast_ofNat] at hd
      have heq : 4 * x ^ (4 - 1) / 24 - 2 * x ^ (2 - 1) / 2 + 0 - -Real.sin x = x ^ 3 / 6 - x + Real.sin x := by ring
      rwa [heq] at hd) h3
  have h5 : ∀ x ≥ 0, 0 ≤ x ^ 5 / 120 - x ^ 3 / 6 + x - Real.sin x := nonneg_of_hasDerivAt_nonneg (by norm_num)
    (fun x _ => by
      have hd := ((((hasDerivAt_pow 5 x).div_const 120).sub ((hasDerivAt_pow 3 x).div_const 6)).add
        (hasDerivAt_id' x)).sub (Real.hasDerivAt_sin x)
      simp only [Nat.cast_ofNat] at hd
      have heq : 5 * x ^ (5 - 1) / 120 - 3 * x ^ (3 - 1) / 6 + 1 - Real.cos x =
        x ^ 4 / 24 - x ^ 2 / 2 + 1 - Real.cos x := by ring
      rwa [heq] at hd) h4
  have h6 : ∀ x ≥ 0, 0 ≤ x ^ 6 / 720 - x ^ 4 / 24 + x ^ 2 / 2 - 1 + Real.cos x :=
    nonneg_of_hasDerivAt_nonneg (by norm_num)
    (fun x _ => by
      have hd := (((((hasDerivAt_pow 6 x).div_const 720).sub ((hasDerivAt_pow 4 x).div_const 24)).add
        ((hasDerivAt_pow 2 x).div_const 2)).sub (hasDerivAt_const x (1 : ℝ))).add (Real.hasDerivAt_cos x)
      simp only [Nat.cast_ofNat] at hd
      have heq : 6 * x ^ (6 - 1) / 720 - 4 * x ^ (4 - 1) / 24 + 2 * x ^ (2 - 1) / 2 - 0 + -Real.sin x =
        x ^ 5 / 120 - x ^ 3 / 6 + x - Real.sin x := by ring
      rwa [heq] at hd) h5
  have h7 : ∀ x ≥ 0, 0 ≤ x ^ 7 / 5040 - x ^ 5 / 120 + x ^ 3 / 6 - x + Real.sin x :=
    nonneg_of_hasDerivAt_nonneg (by norm_num)
    (fun x _ => by
      have hd := (((((hasDerivAt_pow 7 x).div_const 5040).sub ((hasDerivAt_pow 5 x).div_const 120)).add
        ((hasDerivAt_pow 3 x).div_const 6)).sub (hasDerivAt_id' x)).add (Real.hasDerivAt_sin x)
      simp only [Nat.cast_ofNat] at hd
      have heq : 7 * x ^ (7 - 1) / 5040 - 5 * x ^ (5 - 1) / 120 + 3 * x ^ (3 - 1) / 6 - 1 + Real.cos x =
        x ^ 6 / 720 - x ^ 4 / 24 + x ^ 2 / 2 - 1 + Real.cos x := by ring
      rwa [heq] at hd) h6
  have h8 : ∀ x ≥ 0, 0 ≤ x ^ 8 / 40320 - x ^ 6 / 720 + x ^ 4 / 24 - x ^ 2 / 2 + 1 - Real.cos x :=
    nonneg_of_hasDerivAt_nonneg (by norm_num)
    (fun x _ => by
      have hd := ((((((hasDerivAt_pow 8 x).div_const 40320).sub ((hasDerivAt_pow 6 x).div_const 720)).add
        ((hasDerivAt_pow 4 x).div_const 24)).sub ((hasDerivAt_pow 2 x).div_const 2)).add
        (hasDerivAt_const x (1 : ℝ))).sub (Real.hasDerivAt_cos x)
      simp only [Nat.cast_ofNat] at hd
      have heq : 8 * x ^ (8 - 1) / 40320 - 6 * x ^ (6 - 1) / 720 + 4 * x ^ (4 - 1) / 24 -
        2 * x ^ (2 - 1) / 2 + 0 - -Real.sin x = x ^ 7 / 5040 - x ^ 5 / 120 + x ^ 3 / 6 - x + Real.sin x := by ring
      rwa [heq] at hd) h7
  have h9 : ∀ x ≥ 0, 0 ≤ x ^ 9 / 362880 - x ^ 7 / 5040 + x ^ 5 / 120 - x ^ 3 / 6 + x - Real.sin x :=
    nonneg_of_hasDerivAt_nonneg (by norm_num)
    (fun x _ => by
      have hd := ((((((hasDerivAt_pow 9 x).div_const 362880).sub ((hasDerivAt_pow 7 x).div_const 5040)).add
        ((hasDerivAt_pow 5 x).div_const 120)).sub ((hasDerivAt_pow 3 x).div_const 6)).add
        (hasDerivAt_id' x)).sub (Real.hasDerivAt_sin x)
      simp only [Nat.cast_ofNat] at hd
      have heq : 9 * x ^ (9 - 1) / 362880 - 7 * x ^ (7 - 1) / 5040 + 5 * x ^ (5 - 1) / 120 -
        3 * x ^ (3 - 1) / 6 + 1 - Real.cos x =
        x ^ 8 / 40320 - x ^ 6 / 720 + x ^ 4 / 24 - x ^ 2 / 2 + 1 - Real.cos x := by ring
      rwa [heq] at hd) h8
  have h10 : ∀ x ≥ 0, 0 ≤ x ^ 10 / 3628800 - x ^ 8 / 40320 + x ^ 6 / 720 - x ^ 4 / 24 + x ^ 2 / 2 - 1 + Real.cos x :=
    nonneg_of_hasDerivAt_nonneg (by norm_num)
    (fun x _ => by
      have hd := (((((((hasDerivAt_pow 10 x).div_const 3628800).sub ((hasDerivAt_pow 8 x).div_const 40320)).add
        ((hasDerivAt_pow 6 x).div_const 720)).sub ((hasDerivAt_pow 4 x).div_const 24)).add
        ((hasDerivAt_pow 2 x).div_const 2)).sub (hasDerivAt_const x (1 : ℝ))).add (Real.hasDerivAt_cos x)
      simp only [Nat.cast_ofNat] at hd
      have heq : 10 * x ^ (10 - 1) / 3628800 - 8 * x ^ (8 - 1) / 40320 + 6 * x ^ (6 - 1) / 720 -
        4 * x ^ (4 - 1) / 24 + 2 * x ^ (2 - 1) / 2 - 0 + -Real.sin x =
        x ^ 9 / 362880 - x ^ 7 / 5040 + x ^ 5 / 120 - x ^ 3 / 6 + x - Real.sin x := by ring
      rwa [heq] at hd) h9
  exact ⟨⟨by linarith [h10 u hu], by linarith [h8 u hu]⟩,
         ⟨by linarith [h7 u hu], by linarith [h9 u hu]⟩⟩

/- 3. Elementary Karamata & Jensen inequalities for f(u) = log(cos(t * sqrt u)) -/

private lemma tan_div_self_strictMono_and_gt_one :
    (∀ v : ℝ, 0 < v → v < Real.pi / 2 → 1 < Real.tan v / v) ∧
    (∀ v w : ℝ, 0 < v → v < w → w < Real.pi / 2 → Real.tan v / v ≤ Real.tan w / w) := by
  have hgt : ∀ v : ℝ, 0 < v → v < Real.pi / 2 → 1 < Real.tan v / v := by
    intro v hv hvp
    have hcos : 0 < Real.cos v := Real.cos_pos_of_mem_Ioo ⟨by linarith, hvp⟩
    rw [Real.tan_eq_sin_div_cos, div_div, one_lt_div (mul_pos hcos hv)]
    let g := fun x => Real.sin x - x * Real.cos x
    have hg0 : g 0 = 0 := by simp [g]
    have hcont : ContinuousOn g (Set.Icc 0 v) :=
      (Real.continuous_sin.sub (continuous_id.mul Real.continuous_cos)).continuousOn
    have hdiff : ∀ x ∈ Set.Ioo 0 v, HasDerivAt g (x * Real.sin x) x := by
      intro x _
      have hd := (Real.hasDerivAt_sin x).sub ((hasDerivAt_id' x).mul (Real.hasDerivAt_cos x))
      have heq : Real.cos x - (1 * Real.cos x + x * -Real.sin x) = x * Real.sin x := by ring
      rwa [heq] at hd
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g (fun x => x * Real.sin x) hv hcont hdiff
    have hsin : 0 < Real.sin c := Real.sin_pos_of_pos_of_lt_pi hc.1 (by linarith [hc.2])
    have hpos : 0 < c * Real.sin c := mul_pos hc.1 hsin
    rw [hg0, sub_zero, sub_zero] at hslope
    have : 0 < g v := by nlinarith [div_mul_cancel₀ (g v) (ne_of_gt hv)]
    dsimp [g] at this; linarith
  have hmono : ∀ v w : ℝ, 0 < v → v < w → w < Real.pi / 2 → Real.tan v / v ≤ Real.tan w / w := by
    intro v w hv hvw hwp
    let h := fun x => Real.tan x / x
    have hdiff : ∀ x ∈ Set.Icc v w, HasDerivAt h ((x - Real.sin x * Real.cos x) / (x ^ 2 * Real.cos x ^ 2)) x := by
      intro x hx
      have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hv hx.1)
      have hcos : Real.cos x ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩)
      have hd := (Real.hasDerivAt_tan hcos).div (hasDerivAt_id' x) hx0
      have heq : (1 / Real.cos x ^ 2 * x - Real.tan x * 1) / x ^ 2 =
          (x - Real.sin x * Real.cos x) / (x ^ 2 * Real.cos x ^ 2) := by
        rw [Real.tan_eq_sin_div_cos]; field_simp [hx0, hcos]
      rwa [heq] at hd
    have hcont : ContinuousOn h (Set.Icc v w) := fun x hx => (hdiff x hx).continuousAt.continuousWithinAt
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope h _ hvw hcont
      (fun x hx => hdiff x ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
    have hcpos : 0 < c := lt_trans hv hc.1
    have h2c : Real.sin (2 * c) < 2 * c := Real.sin_lt (by linarith)
    have hnum : 0 < c - Real.sin c * Real.cos c := by
      have := Real.sin_two_mul c
      linarith
    have hden : 0 < c ^ 2 * Real.cos c ^ 2 := by
      have hcos : 0 < Real.cos c := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith [hc.2]⟩
      positivity
    have hderiv_pos : 0 ≤ (c - Real.sin c * Real.cos c) / (c ^ 2 * Real.cos c ^ 2) :=
      le_of_lt (div_pos hnum hden)
    have : 0 ≤ h w - h v := by
      have hsub : 0 < w - v := by linarith
      nlinarith [div_mul_cancel₀ (h w - h v) (ne_of_gt hsub)]
    dsimp [h] at this; linarith
  exact ⟨hgt, hmono⟩

private lemma log_cos_sqrt_deriv_antitone {t R : ℝ} (ht : 0 < t) (_hR : 0 < R)
    (hbound : t * Real.sqrt R < Real.pi / 2) :
    let f : ℝ → ℝ := fun u => Real.log (Real.cos (t * Real.sqrt u))
    let df : ℝ → ℝ := fun u => if u = 0 then -(t ^ 2 / 2) else -(t * Real.tan (t * Real.sqrt u) / (2 * Real.sqrt u))
    (∀ u ∈ Set.Icc 0 R, ContinuousAt f u) ∧
    (∀ u ∈ Set.Ioo 0 R, HasDerivAt f (df u) u) ∧
    (∀ u v, 0 ≤ u → u ≤ v → v ≤ R → df v ≤ df u) ∧
    (∀ u, 0 ≤ u → u ≤ R → df u ≤ 0) := by
  intro f df
  have hcos_pos : ∀ u ∈ Set.Icc 0 R, 0 < Real.cos (t * Real.sqrt u) := by
    intro u hu
    have h1 : 0 ≤ t * Real.sqrt u := mul_nonneg (le_of_lt ht) (Real.sqrt_nonneg u)
    have h2 : t * Real.sqrt u < Real.pi / 2 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hu.2) (le_of_lt ht)) hbound
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h2⟩
  have hcont : ∀ u ∈ Set.Icc 0 R, ContinuousAt f u := by
    intro u hu
    have h1 : ContinuousAt (fun x => Real.cos (t * Real.sqrt x)) u :=
      (Real.continuous_cos.comp (continuous_const.mul Real.continuous_sqrt)).continuousAt
    exact h1.log (ne_of_gt (hcos_pos u hu))
  have hdiff : ∀ u ∈ Set.Ioo 0 R, HasDerivAt f (df u) u := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt hu.1
    have hsq : Real.sqrt u ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hu.1)
    have hcos : Real.cos (t * Real.sqrt u) ≠ 0 := ne_of_gt (hcos_pos u ⟨le_of_lt hu.1, le_of_lt hu.2⟩)
    have h1 : HasDerivAt (fun x => t * Real.sqrt x) (t * (1 / (2 * Real.sqrt u))) u :=
      (Real.hasDerivAt_sqrt hu0).const_mul t
    have h2 := (Real.hasDerivAt_cos (t * Real.sqrt u)).comp u h1
    have h3 := h2.log hcos
    have h4 : HasDerivAt f (-Real.sin (t * Real.sqrt u) * (t * (1 / (2 * Real.sqrt u))) / Real.cos (t * Real.sqrt u)) u := h3
    have heq : -Real.sin (t * Real.sqrt u) * (t * (1 / (2 * Real.sqrt u))) / Real.cos (t * Real.sqrt u) = df u := by
      simp only [df, if_neg hu0, Real.tan_eq_sin_div_cos]
      field_simp [hcos, hsq]
    rwa [heq] at h4
  have hant : ∀ u v, 0 ≤ u → u ≤ v → v ≤ R → df v ≤ df u := by
    intro u v hu huv hvR
    rcases eq_or_lt_of_le huv with rfl | hlt
    · exact le_rfl
    · have hvpos : 0 < v := lt_of_le_of_lt hu hlt
      have htv_pos : 0 < t * Real.sqrt v := mul_pos ht (Real.sqrt_pos.mpr hvpos)
      have htv_lt : t * Real.sqrt v < Real.pi / 2 :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hvR) (le_of_lt ht)) hbound
      have hrewrite : ∀ x > 0, df x = -(t ^ 2 / 2) * (Real.tan (t * Real.sqrt x) / (t * Real.sqrt x)) := by
        intro x hx
        have hx0 : x ≠ 0 := ne_of_gt hx
        have hsq : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx)
        simp only [df, hx0, ite_false]
        field_simp [ne_of_gt ht, hsq]
      rcases eq_or_lt_of_le hu with rfl | hupos
      · rw [hrewrite v hvpos]
        simp only [df, ite_true]
        have hgt := tan_div_self_strictMono_and_gt_one.1 (t * Real.sqrt v) htv_pos htv_lt
        nlinarith [sq_pos_of_pos ht]
      · rw [hrewrite u hupos, hrewrite v hvpos]
        have htu_pos : 0 < t * Real.sqrt u := mul_pos ht (Real.sqrt_pos.mpr hupos)
        have htu_lt_v : t * Real.sqrt u < t * Real.sqrt v :=
          mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt hu hlt) ht
        have hmono := tan_div_self_strictMono_and_gt_one.2 _ _ htu_pos htu_lt_v htv_lt
        nlinarith [sq_pos_of_pos ht]
  have hnonpos : ∀ u, 0 ≤ u → u ≤ R → df u ≤ 0 := by
    intro u hu huR
    have hle := hant 0 u le_rfl hu huR
    have h0 : df 0 ≤ 0 := by simp only [df, ite_true]; nlinarith [sq_nonneg t]
    linarith
  exact ⟨hcont, hdiff, hant, hnonpos⟩

private lemma chord_slope_antitone {f df : ℝ → ℝ} {R : ℝ}
    (hcont : ∀ u ∈ Set.Icc 0 R, ContinuousAt f u)
    (hdiff : ∀ u ∈ Set.Ioo 0 R, HasDerivAt f (df u) u)
    (hant : ∀ u v, 0 ≤ u → u ≤ v → v ≤ R → df v ≤ df u)
    (hnonpos : ∀ u, 0 ≤ u → u ≤ R → df u ≤ 0) :
    let sl : ℝ → ℝ → ℝ := fun a b => if a = b then df a else (f b - f a) / (b - a)
    (∀ a b, 0 ≤ a → a ≤ R → 0 ≤ b → b ≤ R → f b - f a = sl a b * (b - a)) ∧
    (∀ a b, 0 ≤ a → a ≤ R → 0 ≤ b → b ≤ R → sl a b ≤ 0) ∧
    (∀ a a' b, 0 ≤ a → a ≤ a' → a' ≤ R → 0 ≤ b → b ≤ R → sl a' b ≤ sl a b) ∧
    (∀ a b, sl a b = sl b a) := by
  intro sl
  have hsymm : ∀ a b, sl a b = sl b a := by
    intro a b
    by_cases h : a = b
    · subst h; rfl
    · have h' : b ≠ a := Ne.symm h
      simp only [sl, h, h', ite_false]
      have hne : b - a ≠ 0 := sub_ne_zero.mpr h'
      have hne' : a - b ≠ 0 := sub_ne_zero.mpr h
      field_simp [hne, hne']; ring
  have hmul : ∀ a b, 0 ≤ a → a ≤ R → 0 ≤ b → b ≤ R → f b - f a = sl a b * (b - a) := by
    intro a b _ _ _ _
    by_cases h : a = b
    · subst h; simp [sl]
    · simp only [sl, h, ite_false]
      exact (div_mul_cancel₀ (f b - f a) (sub_ne_zero.mpr (Ne.symm h))).symm
  have hmvt : ∀ u v, 0 ≤ u → u < v → v ≤ R → df v ≤ sl u v ∧ sl u v ≤ df u := by
    intro u v hu huv hvR
    have hne : u ≠ v := ne_of_lt huv
    simp only [sl, hne, ite_false]
    have hc : ContinuousOn f (Set.Icc u v) := fun x hx =>
      (hcont x ⟨le_trans hu hx.1, le_trans hx.2 hvR⟩).continuousWithinAt
    have hd : ∀ x ∈ Set.Ioo u v, HasDerivAt f (df x) x := fun x hx =>
      hdiff x ⟨lt_of_le_of_lt hu hx.1, lt_of_lt_of_le hx.2 hvR⟩
    obtain ⟨c, hcI, hEq⟩ := exists_hasDerivAt_eq_slope f df huv hc hd
    rw [← hEq]
    exact ⟨hant c v (le_trans hu (le_of_lt hcI.1)) (le_of_lt hcI.2) hvR,
           hant u c hu (le_of_lt hcI.1) (le_trans (le_of_lt hcI.2) hvR)⟩
  have hle0 : ∀ a b, 0 ≤ a → a ≤ R → 0 ≤ b → b ≤ R → sl a b ≤ 0 := by
    intro a b ha haR hb hbR
    rcases lt_trichotomy a b with hlt | rfl | hgt
    · exact le_trans (hmvt a b ha hlt hbR).2 (hnonpos a ha haR)
    · simp only [sl, ite_true]; exact hnonpos a ha haR
    · rw [hsymm]; exact le_trans (hmvt b a hb hgt haR).2 (hnonpos b hb hbR)
  have htriple : ∀ u v w, 0 ≤ u → u < v → v < w → w ≤ R → sl v w ≤ sl u w ∧ sl u w ≤ sl u v := by
    intro u v w hu huv hvw hwR
    have h1 := hmvt u v hu huv (le_trans (le_of_lt hvw) hwR)
    have h2 := hmvt v w (le_trans hu (le_of_lt huv)) hvw hwR
    have hle : sl v w ≤ sl u v := le_trans h2.2 h1.1
    have hsum : sl u w * (w - u) = sl u v * (v - u) + sl v w * (w - v) := by
      have e1 := hmul u w hu (le_trans (le_of_lt (lt_trans huv hvw)) hwR) (le_trans hu (le_of_lt (lt_trans huv hvw))) hwR
      have e2 := hmul u v hu (le_trans (le_of_lt (lt_trans huv hvw)) hwR) (le_trans hu (le_of_lt huv)) (le_trans (le_of_lt hvw) hwR)
      have e3 := hmul v w (le_trans hu (le_of_lt huv)) (le_trans (le_of_lt hvw) hwR) (le_trans hu (le_of_lt (lt_trans huv hvw))) hwR
      linarith
    constructor <;> nlinarith
  have hdec : ∀ a a' b, 0 ≤ a → a ≤ a' → a' ≤ R → 0 ≤ b → b ≤ R → sl a' b ≤ sl a b := by
    intro a a' b ha haa' ha'R hb hbR
    rcases eq_or_lt_of_le haa' with rfl | hlt
    · exact le_rfl
    · rcases lt_trichotomy b a with hba | hba | hab
      · rw [hsymm a' b, hsymm a b]; exact (htriple b a a' hb hba hlt ha'R).2
      · subst hba
        rw [hsymm a' b]; simp only [sl, ite_true]; exact (hmvt b a' hb hlt ha'R).2
      · rcases lt_trichotomy b a' with hba' | hba' | ha'b
        · rw [hsymm a' b]
          exact le_trans (hmvt b a' hb hba' ha'R).2 (hmvt a b ha hab hbR).1
        · subst hba'
          simp only [sl, ite_true]; exact (hmvt a b ha hlt hbR).1
        · exact (htriple a a' b ha hlt ha'b hbR).1
  exact ⟨hmul, hle0, hdec, hsymm⟩

private lemma jensen_cos_prod {t : ℝ} (ht : 0 ≤ t) {a : Fin 9 → ℝ} {j M : ℝ}
    (ha0 : ∀ i, 0 ≤ a i) (haM : ∀ i, a i ≤ M) (hj0 : 0 ≤ j) (hjM : j ≤ M)
    (hbound : t * M < Real.pi / 2) (hQ : 9 * j ^ 2 ≤ ∑ i : Fin 9, a i ^ 2) :
    ∏ i : Fin 9, Real.cos (t * a i) ≤ (Real.cos (t * j)) ^ 9 := by
  rcases eq_or_lt_of_le ht with rfl | htpos
  · simp
  · have hMpos : 0 < M ∨ M = 0 := by
      by_cases hM : M = 0
      · right; exact hM
      · left; exact lt_of_le_of_ne (le_trans hj0 hjM) (Ne.symm hM)
    rcases hMpos with hMpos | rfl
    · set R := M ^ 2
      have hRpos : 0 < R := sq_pos_of_pos hMpos
      have hsqR : Real.sqrt R = M := Real.sqrt_sq (le_of_lt hMpos)
      have hbR : t * Real.sqrt R < Real.pi / 2 := by rw [hsqR]; exact hbound
      obtain ⟨hcont, hdiff, hant, hnonpos⟩ := log_cos_sqrt_deriv_antitone htpos hRpos hbR
      obtain ⟨hmul, _, hdec, _⟩ := chord_slope_antitone hcont hdiff hant hnonpos
      let f : ℝ → ℝ := fun u => Real.log (Real.cos (t * Real.sqrt u))
      let df : ℝ → ℝ := fun u => if u = 0 then -(t ^ 2 / 2) else -(t * Real.tan (t * Real.sqrt u) / (2 * Real.sqrt u))
      have htan : ∀ u, 0 ≤ u → u ≤ R → f u ≤ f (j ^ 2) + df (j ^ 2) * (u - j ^ 2) := by
        intro u hu huR
        have hj2R : j ^ 2 ≤ R := by dsimp [R]; nlinarith
        have hEq := hmul (j ^ 2) u (sq_nonneg j) hj2R hu huR
        rcases lt_trichotomy u (j ^ 2) with hlt | rfl | hgt
        · have hs := hdec u (j ^ 2) (j ^ 2) hu (le_of_lt hlt) hj2R (sq_nonneg j) hj2R
          have hsym : (if j ^ 2 = u then df (j ^ 2) else (f u - f (j ^ 2)) / (u - j ^ 2)) =
              (if u = j ^ 2 then df u else (f (j ^ 2) - f u) / (j ^ 2 - u)) := by
            have hne1 : j ^ 2 ≠ u := ne_of_gt hlt
            have hne2 : u ≠ j ^ 2 := ne_of_lt hlt
            simp only [hne1, hne2, ite_false]
            have : j ^ 2 - u ≠ 0 := sub_ne_zero.mpr hne1
            have : u - j ^ 2 ≠ 0 := sub_ne_zero.mpr hne2
            field_simp; ring
          simp only [ite_true] at hs
          nlinarith
        · linarith
        · have hs := hdec (j ^ 2) u (j ^ 2) (sq_nonneg j) (le_of_lt hgt) huR (sq_nonneg j) hj2R
          have hsym : (if u = j ^ 2 then df u else (f (j ^ 2) - f u) / (j ^ 2 - u)) =
              (if j ^ 2 = u then df (j ^ 2) else (f u - f (j ^ 2)) / (u - j ^ 2)) := by
            have hne1 : u ≠ j ^ 2 := ne_of_gt hgt
            have hne2 : j ^ 2 ≠ u := ne_of_lt hgt
            simp only [hne1, hne2, ite_false]
            have : u - j ^ 2 ≠ 0 := sub_ne_zero.mpr hne1
            have : j ^ 2 - u ≠ 0 := sub_ne_zero.mpr hne2
            field_simp; ring
          simp only [ite_true] at hs
          nlinarith
      have hsum_le : ∑ i : Fin 9, f (a i ^ 2) ≤ 9 * f (j ^ 2) := by
        have h1 : ∑ i : Fin 9, f (a i ^ 2) ≤ ∑ i : Fin 9, (f (j ^ 2) + df (j ^ 2) * (a i ^ 2 - j ^ 2)) :=
          sum_le_sum fun i _ => htan (a i ^ 2) (sq_nonneg _) (by dsimp [R]; nlinarith [ha0 i, haM i])
        have h2 : ∑ i : Fin 9, (f (j ^ 2) + df (j ^ 2) * (a i ^ 2 - j ^ 2)) =
            9 * f (j ^ 2) + df (j ^ 2) * ((∑ i : Fin 9, a i ^ 2) - 9 * j ^ 2) := by
          rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← mul_sum, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num
        have hdf : df (j ^ 2) ≤ 0 := hnonpos (j ^ 2) (sq_nonneg j) (by dsimp [R]; nlinarith)
        nlinarith
      have hcos_a : ∀ i : Fin 9, 0 < Real.cos (t * a i) := fun i =>
        Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, mul_nonneg (le_of_lt htpos) (ha0 i)],
          lt_of_le_of_lt (mul_le_mul_of_nonneg_left (haM i) (le_of_lt htpos)) hbound⟩
      have hcos_j : 0 < Real.cos (t * j) :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, mul_nonneg (le_of_lt htpos) hj0],
          lt_of_le_of_lt (mul_le_mul_of_nonneg_left hjM (le_of_lt htpos)) hbound⟩
      have hexp_lhs : Real.exp (∑ i : Fin 9, f (a i ^ 2)) = ∏ i : Fin 9, Real.cos (t * a i) := by
        rw [Real.exp_sum]
        refine prod_congr rfl fun i _ => ?_
        dsimp [f]; rw [Real.sqrt_sq (ha0 i), Real.exp_log (hcos_a i)]
      have hexp_rhs : Real.exp (9 * f (j ^ 2)) = (Real.cos (t * j)) ^ 9 := by
        dsimp [f]; rw [Real.sqrt_sq hj0, show (9 : ℝ) * Real.log (Real.cos (t * j)) =
          ((9 : ℕ) : ℝ) * Real.log (Real.cos (t * j)) by norm_num, Real.exp_nat_mul, Real.exp_log hcos_j]
      rw [← hexp_lhs, ← hexp_rhs]
      exact Real.exp_le_exp.mpr hsum_le
    · have hj : j = 0 := le_antisymm hjM hj0
      have ha : ∀ i, a i = 0 := fun i => le_antisymm (haM i) (ha0 i)
      simp [hj, ha]

private lemma abel_sum_range (s d : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range (n + 1), s i * d i =
      s n * (∑ i ∈ range (n + 1), d i) +
      ∑ k ∈ range n, (s k - s (k + 1)) * (∑ i ∈ range (k + 1), d i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ (f := fun k => (s k - s (k + 1)) * _),
      sum_range_succ (f := d) (n + 1)]
    ring

private lemma karamata_cos_prod {t : ℝ} (ht : 0 ≤ t) {a b : Fin 9 → ℝ} {M : ℝ}
    (ha0 : ∀ i, 0 ≤ a i) (haM : ∀ i, a i ≤ M) (hb0 : ∀ i, 0 ≤ b i) (hbM : ∀ i, b i ≤ M)
    (ha_anti : Antitone a) (hb_anti : Antitone b)
    (hbound : t * M < Real.pi / 2)
    (hmaj : ∀ k : Fin 9,
      ∑ i ∈ univ.filter (fun j : Fin 9 => j.val ≤ k.val), a i ^ 2 ≤
      ∑ i ∈ univ.filter (fun j : Fin 9 => j.val ≤ k.val), b i ^ 2) :
    ∏ i : Fin 9, Real.cos (t * b i) ≤ ∏ i : Fin 9, Real.cos (t * a i) := by
  rcases eq_or_lt_of_le ht with rfl | htpos
  · simp
  · have hMpos : 0 < M ∨ M = 0 := by
      by_cases hM : M = 0
      · right; exact hM
      · left; exact lt_of_le_of_ne (le_trans (ha0 0) (haM 0)) (Ne.symm hM)
    rcases hMpos with hMpos | rfl
    · set R := M ^ 2
      have hRpos : 0 < R := sq_pos_of_pos hMpos
      have hbR : t * Real.sqrt R < Real.pi / 2 := by rw [Real.sqrt_sq (le_of_lt hMpos)]; exact hbound
      obtain ⟨hcont, hdiff, hant, hnonpos⟩ := log_cos_sqrt_deriv_antitone htpos hRpos hbR
      obtain ⟨hmul, hle0, hdec, hsymm⟩ := chord_slope_antitone hcont hdiff hant hnonpos
      let f : ℝ → ℝ := fun u => Real.log (Real.cos (t * Real.sqrt u))
      let df : ℝ → ℝ := fun u => if u = 0 then -(t ^ 2 / 2) else -(t * Real.tan (t * Real.sqrt u) / (2 * Real.sqrt u))
      let sl : ℝ → ℝ → ℝ := fun x y => if x = y then df x else (f y - f x) / (y - x)
      let sN : ℕ → ℝ := fun i => if h : i < 9 then sl (a ⟨i, h⟩ ^ 2) (b ⟨i, h⟩ ^ 2) else 0
      let dN : ℕ → ℝ := fun i => if h : i < 9 then b ⟨i, h⟩ ^ 2 - a ⟨i, h⟩ ^ 2 else 0
      have haR : ∀ i, a i ^ 2 ≤ R := fun i => by dsimp [R]; nlinarith [ha0 i, haM i]
      have hbR' : ∀ i, b i ^ 2 ≤ R := fun i => by dsimp [R]; nlinarith [hb0 i, hbM i]
      have hdiff_eq : ∑ i : Fin 9, f (b i ^ 2) - ∑ i : Fin 9, f (a i ^ 2) = ∑ i ∈ range 9, sN i * dN i := by
        rw [← sum_sub_distrib, ← Fin.sum_univ_eq_sum_range]
        refine sum_congr rfl fun i _ => ?_
        simp only [sN, dN, i.isLt, dif_pos]
        exact hmul (a i ^ 2) (b i ^ 2) (sq_nonneg _) (haR i) (sq_nonneg _) (hbR' i)
      have hs_mono : ∀ k ∈ range 8, sN k ≤ sN (k + 1) := by
        intro k hk
        have hk8 : k < 8 := mem_range.mp hk
        have hk9 : k < 9 := by omega
        have hk19 : k + 1 < 9 := by omega
        simp only [sN, hk9, hk19, dif_pos]
        let i0 : Fin 9 := ⟨k, hk9⟩
        let i1 : Fin 9 := ⟨k + 1, hk19⟩
        have hle_i : i0 ≤ i1 := Fin.le_iff_val_le_val.mpr (Nat.le_succ k)
        have ha_le : a i1 ^ 2 ≤ a i0 ^ 2 := by have := ha_anti hle_i; nlinarith [ha0 i1, ha0 i0]
        have hb_le : b i1 ^ 2 ≤ b i0 ^ 2 := by have := hb_anti hle_i; nlinarith [hb0 i1, hb0 i0]
        have h1 : sl (a i0 ^ 2) (b i0 ^ 2) ≤ sl (a i1 ^ 2) (b i0 ^ 2) :=
          hdec _ _ _ (sq_nonneg _) ha_le (haR _) (sq_nonneg _) (hbR' _)
        have h2a : sl (b i0 ^ 2) (a i1 ^ 2) ≤ sl (b i1 ^ 2) (a i1 ^ 2) :=
          hdec _ _ _ (sq_nonneg _) hb_le (hbR' _) (sq_nonneg _) (haR _)
        have hsy1 : sl (a i1 ^ 2) (b i0 ^ 2) = sl (b i0 ^ 2) (a i1 ^ 2) := hsymm _ _
        have hsy2 : sl (a i1 ^ 2) (b i1 ^ 2) = sl (b i1 ^ 2) (a i1 ^ 2) := hsymm _ _
        linarith
      have hpart_nonneg : ∀ k : ℕ, k < 9 → 0 ≤ ∑ i ∈ range (k + 1), dN i := by
        intro k hk9
        have heq : ∑ i ∈ range (k + 1), dN i =
            ∑ i ∈ univ.filter (fun j : Fin 9 => j.val ≤ k), (b i ^ 2 - a i ^ 2) := by
          refine sum_bij (fun i hi => ⟨i, by have := mem_range.mp hi; omega⟩) ?_ ?_ ?_ ?_
          · intro i hi; rw [mem_filter]; exact ⟨mem_univ _, Nat.lt_succ_iff.mp (mem_range.mp hi)⟩
          · intro i1 _ i2 _ h; exact congrArg Fin.val h
          · intro j hj; exact ⟨j.val, mem_range.mpr (Nat.lt_succ_iff.mpr (mem_filter.mp hj).2), Fin.ext rfl⟩
          · intro i hi; have hi9 : i < 9 := by have := mem_range.mp hi; omega
            simp [dN, hi9]
        rw [heq, sum_sub_distrib]
        linarith [hmaj ⟨k, hk9⟩]
      have habel := abel_sum_range sN dN 8
      have hterm1 : sN 8 * (∑ i ∈ range 9, dN i) ≤ 0 := by
        have hs8 : sN 8 ≤ 0 := by
          simp only [sN, show (8 : ℕ) < 9 by omega, dif_pos]
          exact hle0 _ _ (sq_nonneg _) (haR _) (sq_nonneg _) (hbR' _)
        exact mul_nonpos_of_nonpos_of_nonneg hs8 (hpart_nonneg 8 (by omega))
      have hterm2 : ∑ k ∈ range 8, (sN k - sN (k + 1)) * (∑ i ∈ range (k + 1), dN i) ≤ 0 :=
        sum_nonpos fun k hk => mul_nonpos_of_nonpos_of_nonneg
          (by linarith [hs_mono k hk]) (hpart_nonneg k (by have := mem_range.mp hk; omega))
      have hsum_le : ∑ i : Fin 9, f (b i ^ 2) ≤ ∑ i : Fin 9, f (a i ^ 2) := by linarith
      have hcos_a : ∀ i : Fin 9, 0 < Real.cos (t * a i) := fun i =>
        Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, mul_nonneg (le_of_lt htpos) (ha0 i)],
          lt_of_le_of_lt (mul_le_mul_of_nonneg_left (haM i) (le_of_lt htpos)) hbound⟩
      have hcos_b : ∀ i : Fin 9, 0 < Real.cos (t * b i) := fun i =>
        Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, mul_nonneg (le_of_lt htpos) (hb0 i)],
          lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hbM i) (le_of_lt htpos)) hbound⟩
      have hexp_a : Real.exp (∑ i : Fin 9, f (a i ^ 2)) = ∏ i : Fin 9, Real.cos (t * a i) := by
        rw [Real.exp_sum]
        refine prod_congr rfl fun i _ => ?_
        dsimp [f]; rw [Real.sqrt_sq (ha0 i), Real.exp_log (hcos_a i)]
      have hexp_b : Real.exp (∑ i : Fin 9, f (b i ^ 2)) = ∏ i : Fin 9, Real.cos (t * b i) := by
        rw [Real.exp_sum]
        refine prod_congr rfl fun i _ => ?_
        dsimp [f]; rw [Real.sqrt_sq (hb0 i), Real.exp_log (hcos_b i)]
      rw [← hexp_a, ← hexp_b]
      exact Real.exp_le_exp.mpr hsum_le
    · have ha : ∀ i, a i = 0 := fun i => le_antisymm (haM i) (ha0 i)
      have hb : ∀ i, b i = 0 := fun i => le_antisymm (hbM i) (hb0 i)
      simp [ha, hb]

/- 4. Threshold pigeonhole bound & factored cosIntervalShift soundness -/

private lemma threshold_sum_le {S U : Finset ℕ} (hSU : S ⊆ U) (f : ℕ → ℝ) (tau : ℝ) :
    ∑ x ∈ S, f x ≤ (S.card : ℝ) * tau + ∑ x ∈ U, max 0 (f x - tau) := by
  have h1 : ∑ x ∈ S, f x = (S.card : ℝ) * tau + ∑ x ∈ S, (f x - tau) := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul]; ring
  rw [h1]
  have h2 : ∑ x ∈ S, (f x - tau) ≤ ∑ x ∈ S, max 0 (f x - tau) :=
    sum_le_sum fun x _ => le_max_right _ _
  have h3 : ∑ x ∈ S, max 0 (f x - tau) ≤ ∑ x ∈ U, max 0 (f x - tau) :=
    sum_le_sum_of_subset_of_nonneg hSU fun x _ _ => le_max_left _ _
  linarith

private lemma cos_add_nat_pi_div_two (z : ℝ) (k : ℕ) :
    Real.cos (z + (k : ℝ) * (Real.pi / 2)) =
      if k % 4 = 0 then Real.cos z
      else if k % 4 = 1 then -Real.sin z
      else if k % 4 = 2 then -Real.cos z
      else Real.sin z := by
  have hper : ∀ (y : ℝ) (m : ℕ), Real.cos (y + (m : ℝ) * (2 * Real.pi)) = Real.cos y := fun y m => by
    have := Real.cos_add_int_mul_two_pi y m
    rw [Int.cast_natCast] at this
    exact this
  have hdiv : (k : ℝ) = ((k / 4 : ℕ) : ℝ) * 4 + ((k % 4 : ℕ) : ℝ) := by
    exact_mod_cast (show k = k / 4 * 4 + k % 4 by omega)
  have hrew : z + (k : ℝ) * (Real.pi / 2) =
      (z + ((k % 4 : ℕ) : ℝ) * (Real.pi / 2)) + ((k / 4 : ℕ) : ℝ) * (2 * Real.pi) := by
    rw [hdiv]; ring
  rw [hrew, hper]
  have hmod : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases hmod with h | h | h | h <;> rw [h] <;> simp
  · rw [Real.cos_add_pi_div_two]
  · rw [show z + 2 * (Real.pi / 2) = z + Real.pi by ring, Real.cos_add_pi]
  · rw [show z + 3 * (Real.pi / 2) = (z + Real.pi) + Real.pi / 2 by ring,
        Real.cos_add_pi_div_two, Real.sin_add_pi, neg_neg]

private def SCALE : Nat := 100000000
private def PI2_LO : Nat := 157079632
private def PI2_HI : Nat := 157079633

private def mulS (a b : Nat) : Nat := Nat.div (Nat.mul a b) SCALE

private def cyApprox (u : Nat) : Nat :=
  let u2 := mulS u u
  let u4 := mulS u2 u2
  let u6 := mulS u4 u2
  let u8 := mulS u4 u4
  Nat.sub (Nat.add (Nat.sub (Nat.add SCALE (Nat.div u4 24)) (Nat.div u2 2)) (Nat.div u8 40320)) (Nat.div u6 720)

private def syApprox (u : Nat) : Nat :=
  let u2 := mulS u u
  let u3 := mulS u2 u
  let u5 := mulS u3 u2
  let u7 := mulS u5 u2
  Nat.sub (Nat.add (Nat.sub u (Nat.div u3 6)) (Nat.div u5 120)) (Nat.div u7 5040)

private def cosIntervalShift (X : Nat) : Nat × Nat :=
  let k := Nat.div (Nat.add X 78539816) PI2_LO
  let kLo := Nat.mul k PI2_LO
  let kHi := Nat.mul k PI2_HI
  let hw := Nat.div (Nat.add k 1) 2
  let twoX := Nat.mul 2 X
  let kSum := Nat.add kLo kHi
  let isNeg := Nat.blt twoX kSum
  let u := if isNeg then Nat.div (Nat.sub kSum twoX) 2 else Nat.div (Nat.sub twoX kSum) 2
  let q := Nat.mod k 4
  if Nat.beq q 0 then
    let val := Nat.add SCALE (cyApprox u)
    let err := Nat.add hw 40
    (Nat.sub val err, Nat.add val err)
  else if Nat.beq q 2 then
    let val := Nat.sub SCALE (cyApprox u)
    let err := Nat.add hw 40
    (Nat.sub val err, Nat.add val err)
  else
    let sy := syApprox u
    let err := Nat.add hw 45
    if Nat.beq q 1 then
      let val := if isNeg then Nat.add SCALE sy else Nat.sub SCALE sy
      (Nat.sub val err, Nat.add val err)
    else
      let val := if isNeg then Nat.sub SCALE sy else Nat.add SCALE sy
      (Nat.sub val err, Nat.add val err)

private lemma nat_div_bounds (n d : ℕ) (hd : 0 < d) :
    ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / (d : ℝ) ∧ (n : ℝ) / (d : ℝ) < ((n / d : ℕ) : ℝ) + 1 := by
  have hdR : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have h1 : (n / d) * d ≤ n := Nat.div_mul_le_self n d
  have h2 : n < (n / d + 1) * d := by
    have := Nat.div_add_mod n d
    have := Nat.mod_lt n hd
    nlinarith
  have h1R : ((n / d : ℕ) : ℝ) * (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
  have h2R : (n : ℝ) < (((n / d : ℕ) : ℝ) + 1) * (d : ℝ) := by exact_mod_cast h2
  exact ⟨(le_div_iff₀ hdR).mpr h1R, (div_lt_iff₀ hdR).mpr h2R⟩

private lemma mulS_err_scaled (a b : ℕ) :
    0 ≤ (a : ℝ) * (b : ℝ) / (SCALE : ℝ) - ((mulS a b : ℕ) : ℝ) ∧
    (a : ℝ) * (b : ℝ) / (SCALE : ℝ) - ((mulS a b : ℕ) : ℝ) < 1 := by
  have hd := nat_div_bounds (a * b) SCALE (by decide)
  change 0 ≤ _ - (((a * b) / SCALE : ℕ) : ℝ) ∧ _ - (((a * b) / SCALE : ℕ) : ℝ) < 1
  rw [Nat.cast_mul] at hd
  exact ⟨by linarith [hd.1], by linarith [hd.2]⟩

private lemma div_term_err (x d : ℕ) (hd : 0 < d) (val eps : ℝ)
    (hx0 : 0 ≤ val - (x : ℝ)) (hxe : val - (x : ℝ) < eps) (heps : eps ≤ (d : ℝ)) :
    |((x / d : ℕ) : ℝ) - val / (d : ℝ)| ≤ 2 := by
  have hdb := nat_div_bounds x d hd
  have hdR : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hdiv1 : (val - eps) / (d : ℝ) < (x : ℝ) / (d : ℝ) := (div_lt_div_iff_of_pos_right hdR).mpr (by linarith)
  have hdiv2 : (x : ℝ) / (d : ℝ) ≤ val / (d : ℝ) := (div_le_div_iff_of_pos_right hdR).mpr (by linarith)
  have heps_d : eps / (d : ℝ) ≤ 1 := (div_le_one hdR).mpr heps
  have hrw : (val - eps) / (d : ℝ) = val / (d : ℝ) - eps / (d : ℝ) := by ring
  rw [abs_le]; constructor <;> linarith

private lemma mulS_prod_err (a b : ℕ) (ra rb ea eb B : ℝ)
    (ha0 : 0 ≤ ra * (SCALE : ℝ) - (a : ℝ)) (hae : ra * (SCALE : ℝ) - (a : ℝ) < ea)
    (hb0 : 0 ≤ rb * (SCALE : ℝ) - (b : ℝ)) (hbe : rb * (SCALE : ℝ) - (b : ℝ) < eb)
    (hrb0 : 0 ≤ rb) (hbound : ea * rb + ((a : ℝ) / (SCALE : ℝ)) * eb + 1 ≤ B) :
    0 ≤ (ra * rb) * (SCALE : ℝ) - ((mulS a b : ℕ) : ℝ) ∧
    (ra * rb) * (SCALE : ℝ) - ((mulS a b : ℕ) : ℝ) < B := by
  have hSpos : (0 : ℝ) < (SCALE : ℝ) := by norm_num [SCALE]
  have hm := mulS_err_scaled a b
  have haS0 : 0 ≤ (a : ℝ) / (SCALE : ℝ) := by positivity
  have hdiff : (ra * rb) * (SCALE : ℝ) - (a : ℝ) * (b : ℝ) / (SCALE : ℝ) =
      (ra * (SCALE : ℝ) - (a : ℝ)) * rb + ((a : ℝ) / (SCALE : ℝ)) * (rb * (SCALE : ℝ) - (b : ℝ)) := by
    field_simp [ne_of_gt hSpos]; ring
  have h1 : 0 ≤ (ra * (SCALE : ℝ) - (a : ℝ)) * rb := mul_nonneg ha0 hrb0
  have h2 : 0 ≤ ((a : ℝ) / (SCALE : ℝ)) * (rb * (SCALE : ℝ) - (b : ℝ)) := mul_nonneg haS0 hb0
  have h3 : (ra * (SCALE : ℝ) - (a : ℝ)) * rb ≤ ea * rb := mul_le_mul_of_nonneg_right (le_of_lt hae) hrb0
  have h4 : ((a : ℝ) / (SCALE : ℝ)) * (rb * (SCALE : ℝ) - (b : ℝ)) ≤ ((a : ℝ) / (SCALE : ℝ)) * eb :=
    mul_le_mul_of_nonneg_left (le_of_lt hbe) haS0
  exact ⟨by linarith [hm.1], by linarith [hm.2]⟩

private lemma cyApprox_sound (u : ℕ) (hu : u ≤ 78600000) :
    |((cyApprox u : ℕ) : ℝ) - Real.cos ((u : ℝ) / (SCALE : ℝ)) * (SCALE : ℝ)| ≤ 38 ∧ cyApprox u ≤ SCALE := by
  set S : ℝ := (SCALE : ℝ)
  have hSpos : (0 : ℝ) < S := by norm_num [S, SCALE]
  set ur : ℝ := (u : ℝ) / S
  have huS : (u : ℝ) = ur * S := by dsimp [ur]; field_simp [ne_of_gt hSpos]
  have hur0 : 0 ≤ ur := div_nonneg (Nat.cast_nonneg u) (le_of_lt hSpos)
  have hur_le : ur ≤ 0.786 := by
    have : (u : ℝ) ≤ 78600000 := by exact_mod_cast hu
    dsimp [ur, S, SCALE]; linarith
  have hur2_le : ur ^ 2 ≤ 0.62 := by nlinarith
  have hur4_le : ur ^ 4 ≤ 0.39 := by have : ur ^ 4 = (ur ^ 2) ^ 2 := by ring
                                     nlinarith [sq_nonneg ur]
  have hur6_le : ur ^ 6 ≤ 0.25 := by have : ur ^ 6 = ur ^ 4 * ur ^ 2 := by ring
                                     nlinarith [pow_nonneg hur0 4, sq_nonneg ur]
  have hur8_le : ur ^ 8 ≤ 0.16 := by have : ur ^ 8 = (ur ^ 4) ^ 2 := by ring
                                     nlinarith [pow_nonneg hur0 4]
  have hur10_le : ur ^ 10 ≤ 0.1 := by have : ur ^ 10 = ur ^ 8 * ur ^ 2 := by ring
                                      nlinarith [pow_nonneg hur0 8, sq_nonneg ur]
  set u2 := mulS u u
  set u4 := mulS u2 u2
  set u6 := mulS u4 u2
  set u8 := mulS u4 u4
  have hu2_e : 0 ≤ ur ^ 2 * S - (u2 : ℝ) ∧ ur ^ 2 * S - (u2 : ℝ) < 1 := by
    have hm := mulS_err_scaled u u
    have heq : (u : ℝ) * (u : ℝ) / S = ur ^ 2 * S := by rw [huS]; field_simp [ne_of_gt hSpos]
    dsimp [S] at heq; rwa [heq] at hm
  have hu2_r : (u2 : ℝ) / S ≤ 0.62 := by rw [div_le_iff₀ hSpos]; nlinarith [hu2_e.1]
  have hu4_e : 0 ≤ ur ^ 4 * S - (u4 : ℝ) ∧ ur ^ 4 * S - (u4 : ℝ) < 3 := by
    have hm := mulS_prod_err u2 u2 (ur ^ 2) (ur ^ 2) 1 1 3 hu2_e.1 hu2_e.2 hu2_e.1 hu2_e.2 (sq_nonneg ur) (by linarith)
    simpa only [show ur ^ 2 * ur ^ 2 = ur ^ 4 by ring] using hm
  have hu4_r : (u4 : ℝ) / S ≤ 0.39 := by rw [div_le_iff₀ hSpos]; nlinarith [hu4_e.1]
  have hu6_e : 0 ≤ ur ^ 6 * S - (u6 : ℝ) ∧ ur ^ 6 * S - (u6 : ℝ) < 4 := by
    have hm := mulS_prod_err u4 u2 (ur ^ 4) (ur ^ 2) 3 1 4 hu4_e.1 hu4_e.2 hu2_e.1 hu2_e.2 (sq_nonneg ur) (by linarith)
    simpa only [show ur ^ 4 * ur ^ 2 = ur ^ 6 by ring] using hm
  have hu8_e : 0 ≤ ur ^ 8 * S - (u8 : ℝ) ∧ ur ^ 8 * S - (u8 : ℝ) < 5 := by
    have hm := mulS_prod_err u4 u4 (ur ^ 4) (ur ^ 4) 3 3 5 hu4_e.1 hu4_e.2 hu4_e.1 hu4_e.2 (pow_nonneg hur0 4) (by linarith)
    simpa only [show ur ^ 4 * ur ^ 4 = ur ^ 8 by ring] using hm
  have hle_u2 : u2 ≤ 62000000 := by
    have : (u2 : ℝ) ≤ 62000000 := by dsimp [S, SCALE] at *; nlinarith [hu2_e.1]
    exact_mod_cast this
  have hle_u6 : u6 ≤ 25000000 := by
    have : (u6 : ℝ) ≤ 25000000 := by dsimp [S, SCALE] at *; nlinarith [hu6_e.1]
    exact_mod_cast this
  have hle1 : u2 / 2 ≤ SCALE + u4 / 24 := by dsimp [SCALE]; omega
  have hle2 : u6 / 720 ≤ SCALE + u4 / 24 - u2 / 2 + u8 / 40320 := by dsimp [SCALE]; omega
  have hcast : ((cyApprox u : ℕ) : ℝ) =
      S + ((u4 / 24 : ℕ) : ℝ) - ((u2 / 2 : ℕ) : ℝ) + ((u8 / 40320 : ℕ) : ℝ) - ((u6 / 720 : ℕ) : ℝ) := by
    change ((SCALE + u4 / 24 - u2 / 2 + u8 / 40320 - u6 / 720 : ℕ) : ℝ) = _
    rw [Nat.cast_sub hle2, Nat.cast_add, Nat.cast_sub hle1, Nat.cast_add]
  have htay := (taylor_cos_sin_bounds ur hur0).1
  have h1 := abs_le.mp (div_term_err u2 2 (by decide) (ur ^ 2 * S) 1 hu2_e.1 hu2_e.2 (by norm_num))
  have h2 := abs_le.mp (div_term_err u4 24 (by decide) (ur ^ 4 * S) 3 hu4_e.1 hu4_e.2 (by norm_num))
  have h3 := abs_le.mp (div_term_err u6 720 (by decide) (ur ^ 6 * S) 4 hu6_e.1 hu6_e.2 (by norm_num))
  have h4 := abs_le.mp (div_term_err u8 40320 (by decide) (ur ^ 8 * S) 5 hu8_e.1 hu8_e.2 (by norm_num))
  have hu10 : ur ^ 10 * S / 3628800 ≤ 3 := by dsimp [S, SCALE]; linarith
  have hcos_hi : Real.cos ur * S ≤ S - ur ^ 2 * S / 2 + ur ^ 4 * S / 24 - ur ^ 6 * S / 720 + ur ^ 8 * S / 40320 := by
    have := mul_le_mul_of_nonneg_right htay.2 (le_of_lt hSpos); linarith
  have hcos_lo : S - ur ^ 2 * S / 2 + ur ^ 4 * S / 24 - ur ^ 6 * S / 720 + ur ^ 8 * S / 40320 - ur ^ 10 * S / 3628800 ≤
      Real.cos ur * S := by
    have := mul_le_mul_of_nonneg_right htay.1 (le_of_lt hSpos); linarith
  have habs : |((cyApprox u : ℕ) : ℝ) - Real.cos ur * S| ≤ 38 := by
    rw [hcast, abs_le]; constructor <;> linarith
  have hleS : cyApprox u ≤ SCALE := by
    have hlt4 : u4 ≤ u2 := by
      have hm := (mulS_err_scaled u2 u2).1
      have hmul : (u2 : ℝ) * ((u2 : ℝ) / S) ≤ (u2 : ℝ) :=
        mul_le_of_le_one_right (Nat.cast_nonneg u2) (by linarith [hu2_r])
      have heq : (u2 : ℝ) * (u2 : ℝ) / S = (u2 : ℝ) * ((u2 : ℝ) / S) := by ring
      have : (u4 : ℝ) ≤ (u2 : ℝ) := by dsimp [S] at heq hmul; linarith
      exact_mod_cast this
    have hlt8 : u8 ≤ u4 := by
      have hm := (mulS_err_scaled u4 u4).1
      have hmul : (u4 : ℝ) * ((u4 : ℝ) / S) ≤ (u4 : ℝ) :=
        mul_le_of_le_one_right (Nat.cast_nonneg u4) (by linarith [hu4_r])
      have heq : (u4 : ℝ) * (u4 : ℝ) / S = (u4 : ℝ) * ((u4 : ℝ) / S) := by ring
      have : (u8 : ℝ) ≤ (u4 : ℝ) := by dsimp [S] at heq hmul; linarith
      exact_mod_cast this
    change SCALE + u4 / 24 - u2 / 2 + u8 / 40320 - u6 / 720 ≤ SCALE
    omega
  exact ⟨habs, hleS⟩

private lemma syApprox_sound (u : ℕ) (hu : u ≤ 78600000) :
    |((syApprox u : ℕ) : ℝ) - Real.sin ((u : ℝ) / (SCALE : ℝ)) * (SCALE : ℝ)| ≤ 40 ∧ syApprox u ≤ 85000000 := by
  set S : ℝ := (SCALE : ℝ)
  have hSpos : (0 : ℝ) < S := by norm_num [S, SCALE]
  set ur : ℝ := (u : ℝ) / S
  have huS : (u : ℝ) = ur * S := by dsimp [ur]; field_simp [ne_of_gt hSpos]
  have hur0 : 0 ≤ ur := div_nonneg (Nat.cast_nonneg u) (le_of_lt hSpos)
  have hur_le : ur ≤ 0.786 := by
    have : (u : ℝ) ≤ 78600000 := by exact_mod_cast hu
    dsimp [ur, S, SCALE]; linarith
  have hur2_le : ur ^ 2 ≤ 0.618 := by nlinarith
  have hur3_le : ur ^ 3 ≤ 0.49 := by have : ur ^ 3 = ur ^ 2 * ur := by ring
                                     nlinarith [sq_nonneg ur]
  have hur4_le : ur ^ 4 ≤ 0.382 := by have : ur ^ 4 = (ur ^ 2) ^ 2 := by ring
                                      nlinarith [sq_nonneg ur]
  have hur5_le : ur ^ 5 ≤ 0.31 := by have : ur ^ 5 = ur ^ 4 * ur := by ring
                                     nlinarith [pow_nonneg hur0 4]
  have hur8_le : ur ^ 8 ≤ 0.146 := by have : ur ^ 8 = (ur ^ 4) ^ 2 := by ring
                                      nlinarith [pow_nonneg hur0 4]
  have hur9_le : ur ^ 9 ≤ 0.115 := by have : ur ^ 9 = ur ^ 8 * ur := by ring
                                      nlinarith [pow_nonneg hur0 8]
  set u2 := mulS u u
  set u3 := mulS u2 u
  set u5 := mulS u3 u2
  set u7 := mulS u5 u2
  have hu2_e : 0 ≤ ur ^ 2 * S - (u2 : ℝ) ∧ ur ^ 2 * S - (u2 : ℝ) < 1 := by
    have hm := mulS_err_scaled u u
    have heq : (u : ℝ) * (u : ℝ) / S = ur ^ 2 * S := by rw [huS]; field_simp [ne_of_gt hSpos]
    dsimp [S] at heq; rwa [heq] at hm
  have hu2_r : (u2 : ℝ) / (SCALE : ℝ) ≤ 0.618 := by rw [div_le_iff₀ hSpos]; dsimp [S] at *; nlinarith [hu2_e.1]
  have hu3_e : 0 ≤ ur ^ 3 * S - (u3 : ℝ) ∧ ur ^ 3 * S - (u3 : ℝ) < 2 := by
    have hu_ex : 0 ≤ ur * S - (u : ℝ) ∧ ur * S - (u : ℝ) < 0.1 := ⟨by linarith [huS], by linarith [huS]⟩
    have hm := mulS_prod_err u2 u (ur ^ 2) ur 1 0.1 2 hu2_e.1 hu2_e.2 hu_ex.1 hu_ex.2 hur0 (by linarith)
    simpa only [show ur ^ 2 * ur = ur ^ 3 by ring] using hm
  have hu3_r : (u3 : ℝ) / (SCALE : ℝ) ≤ 0.49 := by rw [div_le_iff₀ hSpos]; dsimp [S] at *; nlinarith [hu3_e.1]
  have hu5_e : 0 ≤ ur ^ 5 * S - (u5 : ℝ) ∧ ur ^ 5 * S - (u5 : ℝ) < 3 := by
    have hm := mulS_prod_err u3 u2 (ur ^ 3) (ur ^ 2) 2 1 3 hu3_e.1 hu3_e.2 hu2_e.1 hu2_e.2 (sq_nonneg ur) (by linarith)
    simpa only [show ur ^ 3 * ur ^ 2 = ur ^ 5 by ring] using hm
  have hu5_r : (u5 : ℝ) / (SCALE : ℝ) ≤ 0.31 := by rw [div_le_iff₀ hSpos]; dsimp [S] at *; nlinarith [hu5_e.1]
  have hu7_e : 0 ≤ ur ^ 7 * S - (u7 : ℝ) ∧ ur ^ 7 * S - (u7 : ℝ) < 4 := by
    have hm := mulS_prod_err u5 u2 (ur ^ 5) (ur ^ 2) 3 1 4 hu5_e.1 hu5_e.2 hu2_e.1 hu2_e.2 (sq_nonneg ur) (by linarith)
    simpa only [show ur ^ 5 * ur ^ 2 = ur ^ 7 by ring] using hm
  have hu3_le_u : u3 ≤ u := by
    have : (u3 : ℝ) ≤ (u : ℝ) := by
      have : ur ^ 3 ≤ ur := by have : ur ^ 3 = ur ^ 2 * ur := by ring
                               nlinarith
      rw [huS]; nlinarith [hu3_e.1]
    exact_mod_cast this
  have hu7_le_u : u7 ≤ u := by
    have : (u7 : ℝ) ≤ (u : ℝ) := by
      have h7 : ur ^ 7 ≤ ur := by have : ur ^ 7 = ur ^ 5 * ur ^ 2 := by ring
                                  nlinarith [pow_nonneg hur0 5, sq_nonneg ur]
      rw [huS]; nlinarith [hu7_e.1]
    exact_mod_cast this
  have hle1 : u3 / 6 ≤ u := by omega
  have hle2 : u7 / 5040 ≤ u - u3 / 6 + u5 / 120 := by omega
  have hcast : ((syApprox u : ℕ) : ℝ) =
      (u : ℝ) - ((u3 / 6 : ℕ) : ℝ) + ((u5 / 120 : ℕ) : ℝ) - ((u7 / 5040 : ℕ) : ℝ) := by
    change ((u - u3 / 6 + u5 / 120 - u7 / 5040 : ℕ) : ℝ) = _
    rw [Nat.cast_sub hle2, Nat.cast_add, Nat.cast_sub hle1]
  have htay := (taylor_cos_sin_bounds ur hur0).2
  have h3 := abs_le.mp (div_term_err u3 6 (by decide) (ur ^ 3 * S) 2 hu3_e.1 hu3_e.2 (by norm_num))
  have h5 := abs_le.mp (div_term_err u5 120 (by decide) (ur ^ 5 * S) 3 hu5_e.1 hu5_e.2 (by norm_num))
  have h7 := abs_le.mp (div_term_err u7 5040 (by decide) (ur ^ 7 * S) 4 hu7_e.1 hu7_e.2 (by norm_num))
  have hu9 : ur ^ 9 * S / 362880 ≤ 32 := by dsimp [S, SCALE]; linarith
  have hsin_lo : (u : ℝ) - ur ^ 3 * S / 6 + ur ^ 5 * S / 120 - ur ^ 7 * S / 5040 ≤ Real.sin ur * S := by
    have := mul_le_mul_of_nonneg_right htay.1 (le_of_lt hSpos); rw [huS]; linarith
  have hsin_hi : Real.sin ur * S ≤ (u : ℝ) - ur ^ 3 * S / 6 + ur ^ 5 * S / 120 - ur ^ 7 * S / 5040 + ur ^ 9 * S / 362880 := by
    have := mul_le_mul_of_nonneg_right htay.2 (le_of_lt hSpos); rw [huS]; linarith
  have habs : |((syApprox u : ℕ) : ℝ) - Real.sin ur * S| ≤ 40 := by
    rw [hcast, abs_le]; constructor <;> linarith
  have hle85 : syApprox u ≤ 85000000 := by
    rw [abs_le] at habs
    have hsin : Real.sin ur ≤ ur := Real.sin_le hur0
    have : ((syApprox u : ℕ) : ℝ) ≤ 85000000 := by dsimp [S, SCALE] at *; linarith
    exact_mod_cast this
  exact ⟨habs, hle85⟩

private lemma cosIntervalShift_eq (X : ℕ) :
    let k := (X + 78539816) / PI2_LO
    let hw := (k + 1) / 2
    let twoX := 2 * X
    let kSum := k * PI2_LO + k * PI2_HI
    let isNeg := decide (twoX < kSum)
    let u := if isNeg then (kSum - twoX) / 2 else (twoX - kSum) / 2
    cosIntervalShift X =
      if k % 4 = 0 then (SCALE + cyApprox u - (hw + 40), SCALE + cyApprox u + (hw + 40))
      else if k % 4 = 2 then (SCALE - cyApprox u - (hw + 40), SCALE - cyApprox u + (hw + 40))
      else if k % 4 = 1 then
        let val := if isNeg then SCALE + syApprox u else SCALE - syApprox u
        (val - (hw + 45), val + (hw + 45))
      else
        let val := if isNeg then SCALE - syApprox u else SCALE + syApprox u
        (val - (hw + 45), val + (hw + 45)) := by
  intro k hw twoX kSum isNeg u
  have hblt : Nat.blt twoX kSum = isNeg := by
    dsimp [isNeg]
    cases h : Nat.blt twoX kSum
    · have : ¬ (twoX < kSum) := by intro hlt; rw [Nat.blt_eq.mpr hlt] at h; cases h
      simp [this]
    · simp [Nat.blt_eq.mp h]
  have hbeq : ∀ a b : ℕ, Nat.beq a b = decide (a = b) := fun a b => by
    cases h : Nat.beq a b
    · have : a ≠ b := by intro heq; subst heq; simp at h
      simp [this]
    · simp [Nat.eq_of_beq_eq_true h]
  unfold cosIntervalShift
  change (let isN := Nat.blt twoX kSum
    let uu := if isN then (kSum - twoX) / 2 else (twoX - kSum) / 2
    if Nat.beq (k % 4) 0 then (SCALE + cyApprox uu - (hw + 40), SCALE + cyApprox uu + (hw + 40))
    else if Nat.beq (k % 4) 2 then (SCALE - cyApprox uu - (hw + 40), SCALE - cyApprox uu + (hw + 40))
    else if Nat.beq (k % 4) 1 then
      let val := if isN then SCALE + syApprox uu else SCALE - syApprox uu
      (val - (hw + 45), val + (hw + 45))
    else
      let val := if isN then SCALE - syApprox uu else SCALE + syApprox uu
      (val - (hw + 45), val + (hw + 45))) = _
  simp only [hblt, hbeq, decide_eq_true_eq]
  rfl

private lemma shift_cos_bounds {S c z hw : ℝ} {cy : ℕ}
    (h1 : -((hw + 1 : ℝ)) ≤ (c - z) * S) (h2 : (c - z) * S ≤ hw + 1)
    (h3 : -38 ≤ (cy : ℝ) - z * S) (h4 : (cy : ℝ) - z * S ≤ 38) :
    (S + (cy : ℝ) - (hw + 40)) ≤ (c + 1) * S ∧ (c + 1) * S ≤ (S + (cy : ℝ) + (hw + 40)) := by
  constructor <;> linarith

private lemma shift_neg_cos_bounds {S c z hw : ℝ} {cy : ℕ}
    (h1 : -((hw + 1 : ℝ)) ≤ (c - z) * S) (h2 : (c - z) * S ≤ hw + 1)
    (h3 : -38 ≤ (cy : ℝ) - z * S) (h4 : (cy : ℝ) - z * S ≤ 38) :
    (S - (cy : ℝ) - (hw + 40)) ≤ (-c + 1) * S ∧ (-c + 1) * S ≤ (S - (cy : ℝ) + (hw + 40)) := by
  constructor <;> linarith

private lemma shift_sin_plus_bounds {S s z hw : ℝ} {sy : ℕ}
    (h1 : -((hw + 1 : ℝ)) ≤ (s - z) * S) (h2 : (s - z) * S ≤ hw + 1)
    (h3 : -40 ≤ (sy : ℝ) - z * S) (h4 : (sy : ℝ) - z * S ≤ 40) :
    (S + (sy : ℝ) - (hw + 45)) ≤ (s + 1) * S ∧ (s + 1) * S ≤ (S + (sy : ℝ) + (hw + 45)) := by
  constructor <;> linarith

private lemma shift_sin_minus_bounds {S s z hw : ℝ} {sy : ℕ}
    (h1 : -((hw + 1 : ℝ)) ≤ (s - z) * S) (h2 : (s - z) * S ≤ hw + 1)
    (h3 : -40 ≤ (sy : ℝ) - z * S) (h4 : (sy : ℝ) - z * S ≤ 40) :
    (S - (sy : ℝ) - (hw + 45)) ≤ (-s + 1) * S ∧ (-s + 1) * S ≤ (S - (sy : ℝ) + (hw + 45)) := by
  constructor <;> linarith

private lemma cosIntervalShift_u_le (X : ℕ) (hX : X ≤ 1350000000) :
    let k := (X + 78539816) / PI2_LO
    let twoX := 2 * X
    let kSum := k * PI2_LO + k * PI2_HI
    (if decide (twoX < kSum) then (kSum - twoX) / 2 else (twoX - kSum) / 2) ≤ 78600000 := by
  intro k twoX kSum
  have hk_le : k ≤ 9 := by dsimp [k, PI2_LO]; omega
  have hrem1 : k * 157079632 ≤ X + 78539816 := Nat.div_mul_le_self _ _
  have hrem2 : X + 78539816 < (k + 1) * 157079632 := by
    have h1 := Nat.div_add_mod (X + 78539816) 157079632
    have h2 := Nat.mod_lt (X + 78539816) (by decide : 0 < 157079632)
    have h3 : 157079632 * k + (X + 78539816) % 157079632 = X + 78539816 := h1
    omega
  change (if decide (2 * X < k * 157079632 + k * 157079633) then
      (k * 157079632 + k * 157079633 - 2 * X) / 2
    else (2 * X - (k * 157079632 + k * 157079633)) / 2) ≤ 78600000
  split_ifs with hlt
  · have hlt' : 2 * X < k * 157079632 + k * 157079633 := of_decide_eq_true hlt
    omega
  · have hge' : k * 157079632 + k * 157079633 ≤ 2 * X :=
      Nat.le_of_not_lt (of_decide_eq_false (Bool.eq_false_iff.mpr hlt))
    omega

private lemma cosIntervalShift_dist (X : ℕ) :
    let k := (X + 78539816) / PI2_LO
    let hw := (k + 1) / 2
    let twoX := 2 * X
    let kSum := k * PI2_LO + k * PI2_HI
    let isNeg := decide (twoX < kSum)
    let u := if isNeg then (kSum - twoX) / 2 else (twoX - kSum) / 2
    let S : ℝ := (SCALE : ℝ)
    let z : ℝ := (X : ℝ) / S - (k : ℝ) * (Real.pi / 2)
    let su : ℝ := if isNeg then -((u : ℝ) / S) else (u : ℝ) / S
    |z - su| * S ≤ (hw : ℝ) + 1 := by
  intro k hw twoX kSum isNeg u S z su
  have hSpos : (0 : ℝ) < S := by norm_num [S, SCALE]
  have hpi_lo : (PI2_LO : ℝ) / S < Real.pi / 2 := by
    have := Real.pi_gt_d20; norm_num [S, PI2_LO, SCALE]; linarith
  have hpi_hi : Real.pi / 2 < (PI2_HI : ℝ) / S := by
    have := Real.pi_lt_d20; norm_num [S, PI2_HI, SCALE]; linarith
  have hk_pi : |((k : ℝ) * (PI2_LO : ℝ) + (k : ℝ) * (PI2_HI : ℝ)) - 2 * (k : ℝ) * (Real.pi / 2) * S| ≤ (k : ℝ) := by
    have h1 : (PI2_LO : ℝ) < (Real.pi / 2) * S := (div_lt_iff₀ hSpos).mp hpi_lo
    have h2 : (Real.pi / 2) * S < (PI2_HI : ℝ) := (lt_div_iff₀ hSpos).mp hpi_hi
    have h3 : (PI2_HI : ℝ) - (PI2_LO : ℝ) = 1 := by norm_num [PI2_HI, PI2_LO]
    have h4 : |((PI2_LO : ℝ) + (PI2_HI : ℝ)) - 2 * ((Real.pi / 2) * S)| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have heq : ((k : ℝ) * (PI2_LO : ℝ) + (k : ℝ) * (PI2_HI : ℝ)) - 2 * (k : ℝ) * (Real.pi / 2) * S =
        (k : ℝ) * (((PI2_LO : ℝ) + (PI2_HI : ℝ)) - 2 * ((Real.pi / 2) * S)) := by ring
    rw [heq, abs_mul, abs_of_nonneg hk0]; nlinarith
  have hsu_err : |((2 * (X : ℝ) - ((k : ℝ) * (PI2_LO : ℝ) + (k : ℝ) * (PI2_HI : ℝ))) - 2 * su * S)| ≤ 1 := by
    have hmulS : su * S = if isNeg then -(u : ℝ) else (u : ℝ) := by
      dsimp [su]; split_ifs <;> field_simp [ne_of_gt hSpos]
    rw [show 2 * su * S = 2 * (su * S) by ring, hmulS]
    by_cases hlt : twoX < kSum
    · have his : isNeg = true := decide_eq_true hlt
      have huEq : u = (kSum - twoX) / 2 := by simp [u, his]
      simp only [his, ite_true]
      have hsub : ((kSum - twoX : ℕ) : ℝ) = ((k : ℝ) * (PI2_LO : ℝ) + (k : ℝ) * (PI2_HI : ℝ)) - 2 * (X : ℝ) := by
        rw [Nat.cast_sub (le_of_lt hlt)]; simp [kSum, twoX]
      have hdiv2 : 2 * (u : ℝ) ≤ ((kSum - twoX : ℕ) : ℝ) ∧ ((kSum - twoX : ℕ) : ℝ) ≤ 2 * (u : ℝ) + 1 := by
        rw [huEq]; exact ⟨by exact_mod_cast Nat.mul_div_le (kSum - twoX) 2,
          by exact_mod_cast (show kSum - twoX ≤ 2 * ((kSum - twoX) / 2) + 1 by omega)⟩
      rw [abs_le]; constructor <;> linarith
    · have his : isNeg = false := decide_eq_false hlt
      have huEq : u = (twoX - kSum) / 2 := by simp [u, his]
      simp only [his, Bool.false_eq_true, ite_false]
      have hsub : ((twoX - kSum : ℕ) : ℝ) = 2 * (X : ℝ) - ((k : ℝ) * (PI2_LO : ℝ) + (k : ℝ) * (PI2_HI : ℝ)) := by
        rw [Nat.cast_sub (not_lt.mp hlt)]; simp [kSum, twoX]
      have hdiv2 : 2 * (u : ℝ) ≤ ((twoX - kSum : ℕ) : ℝ) ∧ ((twoX - kSum : ℕ) : ℝ) ≤ 2 * (u : ℝ) + 1 := by
        rw [huEq]; exact ⟨by exact_mod_cast Nat.mul_div_le (twoX - kSum) 2,
          by exact_mod_cast (show twoX - kSum ≤ 2 * ((twoX - kSum) / 2) + 1 by omega)⟩
      rw [abs_le]; constructor <;> linarith
  have h2z : 2 * (z - su) * S =
      ((2 * (X : ℝ) - ((k : ℝ) * (PI2_LO : ℝ) + (k : ℝ) * (PI2_HI : ℝ))) - 2 * su * S) +
      (((k : ℝ) * (PI2_LO : ℝ) + (k : ℝ) * (PI2_HI : ℝ)) - 2 * (k : ℝ) * (Real.pi / 2) * S) := by
    dsimp [z]; field_simp [ne_of_gt hSpos]; ring
  have htri : |2 * (z - su) * S| ≤ (k : ℝ) + 1 := by
    rw [h2z]; exact le_trans (abs_add_le _ _) (by linarith)
  have h2hw : (k : ℝ) + 1 ≤ 2 * ((hw : ℝ) + 1) := by
    exact_mod_cast (show k + 1 ≤ 2 * (hw + 1) by dsimp [hw]; omega)
  have habs2 : |2 * (z - su) * S| = 2 * (|z - su| * S) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hSpos]; ring
  linarith

private lemma cosIntervalShift_sound_core (X k hw u : ℕ) (isNeg : Bool)
    (hhw : hw ≤ 5) (hu_le : u ≤ 78600000)
    (hdist : |((X : ℝ) / (SCALE : ℝ) - (k : ℝ) * (Real.pi / 2)) -
      (if isNeg then -((u : ℝ) / (SCALE : ℝ)) else (u : ℝ) / (SCALE : ℝ))| * (SCALE : ℝ) ≤ (hw : ℝ) + 1)
    (hshift : cosIntervalShift X =
      if k % 4 = 0 then (SCALE + cyApprox u - (hw + 40), SCALE + cyApprox u + (hw + 40))
      else if k % 4 = 2 then (SCALE - cyApprox u - (hw + 40), SCALE - cyApprox u + (hw + 40))
      else if k % 4 = 1 then
        let val := if isNeg then SCALE + syApprox u else SCALE - syApprox u
        (val - (hw + 45), val + (hw + 45))
      else
        let val := if isNeg then SCALE - syApprox u else SCALE + syApprox u
        (val - (hw + 45), val + (hw + 45))) :
    ((cosIntervalShift X).1 : ℝ) ≤ (Real.cos ((X : ℝ) / (SCALE : ℝ)) + 1) * (SCALE : ℝ) ∧
    (Real.cos ((X : ℝ) / (SCALE : ℝ)) + 1) * (SCALE : ℝ) ≤ ((cosIntervalShift X).2 : ℝ) := by
  have hSpos : (0 : ℝ) < (SCALE : ℝ) := by norm_num [SCALE]
  set z : ℝ := (X : ℝ) / (SCALE : ℝ) - (k : ℝ) * (Real.pi / 2)
  set ur : ℝ := (u : ℝ) / (SCALE : ℝ)
  set su : ℝ := if isNeg then -ur else ur
  have hcos_eq : Real.cos ((X : ℝ) / (SCALE : ℝ)) =
      if k % 4 = 0 then Real.cos z
      else if k % 4 = 1 then -Real.sin z
      else if k % 4 = 2 then -Real.cos z
      else Real.sin z := by
    rw [show (X : ℝ) / (SCALE : ℝ) = z + (k : ℝ) * (Real.pi / 2) by dsimp [z]; ring, cos_add_nat_pi_div_two]
  have hcos_su : Real.cos su = Real.cos ur := by dsimp [su]; split_ifs <;> simp [Real.cos_neg]
  have hsin_su : Real.sin su = if isNeg then -Real.sin ur else Real.sin ur := by
    dsimp [su]; split_ifs <;> simp [Real.sin_neg]
  have hcd : -((hw : ℝ) + 1) ≤ (Real.cos z - Real.cos ur) * (SCALE : ℝ) ∧
      (Real.cos z - Real.cos ur) * (SCALE : ℝ) ≤ (hw : ℝ) + 1 := by
    apply abs_le.mp
    rw [abs_mul, abs_of_pos hSpos, ← hcos_su]
    exact le_trans (mul_le_mul_of_nonneg_right (Real.abs_cos_sub_cos_le z su) (le_of_lt hSpos)) hdist
  have hsd : -((hw : ℝ) + 1) ≤ (Real.sin z - Real.sin su) * (SCALE : ℝ) ∧
      (Real.sin z - Real.sin su) * (SCALE : ℝ) ≤ (hw : ℝ) + 1 := by
    apply abs_le.mp
    rw [abs_mul, abs_of_pos hSpos]
    exact le_trans (mul_le_mul_of_nonneg_right (Real.abs_sin_sub_sin_le z su) (le_of_lt hSpos)) hdist
  have hcy := cyApprox_sound u hu_le
  have hsy := syApprox_sound u hu_le
  have hcy_e := abs_le.mp hcy.1
  have hsy_e := abs_le.mp hsy.1
  have hmod : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases hmod with hq | hq | hq | hq
  · have hcos0 : Real.cos ((X : ℝ) / (SCALE : ℝ)) = Real.cos z := by rw [hcos_eq]; simp [hq]
    have hshift0 : cosIntervalShift X = (SCALE + cyApprox u - (hw + 40), SCALE + cyApprox u + (hw + 40)) := by
      rw [hshift]; simp [hq]
    rw [hshift0, hcos0]
    have hno : hw + 40 ≤ SCALE + cyApprox u := by dsimp [SCALE]; omega
    have hb := shift_cos_bounds hcd.1 hcd.2 hcy_e.1 hcy_e.2
    simp only [Nat.cast_sub hno, Nat.cast_add, Nat.cast_ofNat]
    exact hb
  · have hcos1 : Real.cos ((X : ℝ) / (SCALE : ℝ)) = -Real.sin z := by rw [hcos_eq]; simp [hq]
    have hshift1 : cosIntervalShift X =
        let val := if isNeg then SCALE + syApprox u else SCALE - syApprox u
        (val - (hw + 45), val + (hw + 45)) := by
      rw [hshift]; simp [hq]
    rw [hshift1, hcos1]
    cases his : isNeg
    · simp only [his, Bool.false_eq_true, ite_false] at hsin_su ⊢
      rw [hsin_su] at hsd
      have h1 : syApprox u ≤ SCALE := by have := hsy.2; dsimp [SCALE]; omega
      have h2 : hw + 45 ≤ SCALE - syApprox u := by have := hsy.2; dsimp [SCALE]; omega
      have hb := shift_sin_minus_bounds hsd.1 hsd.2 hsy_e.1 hsy_e.2
      simp only [Nat.cast_sub h2, Nat.cast_sub h1, Nat.cast_add, Nat.cast_ofNat]
      exact hb
    · simp only [his, ite_true] at hsin_su ⊢
      rw [hsin_su] at hsd
      have h2 : hw + 45 ≤ SCALE + syApprox u := by dsimp [SCALE]; omega
      have hsd' : -((hw : ℝ) + 1) ≤ (-Real.sin z - Real.sin ur) * (SCALE : ℝ) ∧
          (-Real.sin z - Real.sin ur) * (SCALE : ℝ) ≤ (hw : ℝ) + 1 := by
        constructor <;> linarith [hsd.1, hsd.2]
      have hb := shift_sin_plus_bounds hsd'.1 hsd'.2 hsy_e.1 hsy_e.2
      simp only [Nat.cast_sub h2, Nat.cast_add, Nat.cast_ofNat]
      exact hb
  · have hcos2 : Real.cos ((X : ℝ) / (SCALE : ℝ)) = -Real.cos z := by rw [hcos_eq]; simp [hq]
    have hshift2 : cosIntervalShift X = (SCALE - cyApprox u - (hw + 40), SCALE - cyApprox u + (hw + 40)) := by
      rw [hshift]; simp [hq]
    rw [hshift2, hcos2]
    have hb := shift_neg_cos_bounds hcd.1 hcd.2 hcy_e.1 hcy_e.2
    constructor
    · by_cases huf : hw + 40 ≤ SCALE - cyApprox u
      · simp only [Nat.cast_sub huf, Nat.cast_sub hcy.2, Nat.cast_add, Nat.cast_ofNat]; exact hb.1
      · simp only [Nat.sub_eq_zero_of_le (le_of_not_ge huf), Nat.cast_zero]
        have : -Real.cos z + 1 ≥ 0 := by linarith [Real.cos_le_one z]
        nlinarith
    · simp only [Nat.cast_add, Nat.cast_sub hcy.2, Nat.cast_ofNat]; exact hb.2
  · have hcos3 : Real.cos ((X : ℝ) / (SCALE : ℝ)) = Real.sin z := by rw [hcos_eq]; simp [hq]
    have hshift3 : cosIntervalShift X =
        let val := if isNeg then SCALE - syApprox u else SCALE + syApprox u
        (val - (hw + 45), val + (hw + 45)) := by
      rw [hshift]; simp [hq]
    rw [hshift3, hcos3]
    cases his : isNeg
    · simp only [his, Bool.false_eq_true, ite_false] at hsin_su ⊢
      rw [hsin_su] at hsd
      have h2 : hw + 45 ≤ SCALE + syApprox u := by dsimp [SCALE]; omega
      have hb := shift_sin_plus_bounds hsd.1 hsd.2 hsy_e.1 hsy_e.2
      simp only [Nat.cast_sub h2, Nat.cast_add, Nat.cast_ofNat]
      exact hb
    · simp only [his, ite_true] at hsin_su ⊢
      rw [hsin_su] at hsd
      have h1 : syApprox u ≤ SCALE := by have := hsy.2; dsimp [SCALE]; omega
      have h2 : hw + 45 ≤ SCALE - syApprox u := by have := hsy.2; dsimp [SCALE]; omega
      have hsd' : -((hw : ℝ) + 1) ≤ (-Real.sin z - Real.sin ur) * (SCALE : ℝ) ∧
          (-Real.sin z - Real.sin ur) * (SCALE : ℝ) ≤ (hw : ℝ) + 1 := by
        constructor <;> linarith [hsd.1, hsd.2]
      have hb := shift_sin_minus_bounds hsd'.1 hsd'.2 hsy_e.1 hsy_e.2
      simp only [Nat.cast_sub h2, Nat.cast_sub h1, Nat.cast_add, Nat.cast_ofNat]
      simpa [neg_neg] using hb

private lemma cosIntervalShift_sound (X : ℕ) (hX : X ≤ 1350000000) :
    let res := cosIntervalShift X
    (res.1 : ℝ) ≤ (Real.cos ((X : ℝ) / (SCALE : ℝ)) + 1) * (SCALE : ℝ) ∧
    (Real.cos ((X : ℝ) / (SCALE : ℝ)) + 1) * (SCALE : ℝ) ≤ (res.2 : ℝ) := by
  let k : ℕ := (X + 78539816) / PI2_LO
  let hw : ℕ := (k + 1) / 2
  let twoX : ℕ := 2 * X
  let kSum : ℕ := k * PI2_LO + k * PI2_HI
  let isNeg : Bool := decide (twoX < kSum)
  let u : ℕ := if isNeg then (kSum - twoX) / 2 else (twoX - kSum) / 2
  exact cosIntervalShift_sound_core X k hw u isNeg
    (by dsimp [hw, k, PI2_LO]; omega)
    (cosIntervalShift_u_le X hX)
    (cosIntervalShift_dist X)
    (cosIntervalShift_eq X)


-- Part 1 glue (zero-error, zero-warning, zero-sorry):
-- (1) extract_sorted_tuple
-- (2) layer_span_bound + 5 middle-layer span corollaries
-- (3) Sorted-list O(n) mergeDisj g(0..6) = [0,1,2,4,7,13,22] soundness + a_gap_g6 + sum_le_9a0_sub_146
-- (4) Pure-Nat Elkies verifier + checkCertMeta + elkies_cert_sound
-- (5) a0_ge_138 (fast 2-variable nlinarith killing a 0 <= 137)

private lemma nat_add_eq (a b : ℕ) : Nat.add a b = a + b := rfl
private lemma nat_sub_eq (a b : ℕ) : Nat.sub a b = a - b := rfl
private lemma nat_mul_eq (a b : ℕ) : Nat.mul a b = a * b := rfl
private lemma nat_div_eq (a b : ℕ) : Nat.div a b = a / b := rfl

private lemma blt_false_of_le {a b : Nat} (h : b ≤ a) : Nat.blt a b = false := by
  cases hc : Nat.blt a b
  · rfl
  · exfalso; have := Nat.blt_eq.mp hc; omega

private lemma beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hc : Nat.beq a b
  · rfl
  · exfalso; exact h (Nat.eq_of_beq_eq_true hc)

-- 1. Extract sorted descending tuple a : Fin 9 -> Nat
private lemma extract_sorted_tuple {A : Finset ℕ} (hA : A ⊆ Icc 1 151) (h103 : ∃ x ∈ A, 103 ≤ x)
    (hcard : A.card = 9) (hQ : 87381 ≤ ∑ x ∈ A, x ^ 2) (hS : 511 ≤ A.sum id)
    (hno : ¬ ∃ S ⊆ A, ∃ T ⊆ A, S ≠ T ∧ S.sum id = T.sum id) :
    ∃ a : Fin 9 → ℕ, StrictAnti a ∧ (∀ i, a i ∈ A) ∧ (∀ i, 1 ≤ a i ∧ a i ≤ 151) ∧
      103 ≤ a 0 ∧ 87381 ≤ (∑ i : Fin 9, a i ^ 2) ∧ 511 ≤ (∑ i : Fin 9, a i) ∧
      (∑ i : Fin 9, a i = A.sum id) ∧ (∑ i : Fin 9, a i ^ 2 = ∑ x ∈ A, x ^ 2) ∧
      Function.Injective (fun S : Finset (Fin 9) => ∑ i ∈ S, a i) := by
  let e := A.orderIsoOfFin hcard
  let a : Fin 9 → ℕ := fun i => (e ⟨8 - i.val, by omega⟩ : ℕ)
  have ha_anti : StrictAnti a := by
    intro i j hij
    have hlt : (⟨8 - j.val, by omega⟩ : Fin 9) < ⟨8 - i.val, by omega⟩ := by
      simp only [Fin.lt_def]; omega
    exact e.strictMono hlt
  have ha_mem : ∀ i, a i ∈ A := fun i => (e ⟨8 - i.val, by omega⟩).2
  have ha_bnd : ∀ i, 1 ≤ a i ∧ a i ≤ 151 := fun i => mem_Icc.mp (hA (ha_mem i))
  have ha_bij : ∀ (f : ℕ → ℕ), ∑ i : Fin 9, f (a i) = ∑ x ∈ A, f x := by
    intro f
    refine sum_bij (fun i _ => a i) (fun i _ => ha_mem i) ?_ ?_ (fun _ _ => rfl)
    · intro i _ j _ h; exact ha_anti.injective h
    · intro x hx
      let k := e.symm ⟨x, hx⟩
      have hklt : k.val < 9 := k.isLt
      refine ⟨⟨8 - k.val, by omega⟩, mem_univ _, ?_⟩
      dsimp [a]
      have hk : (⟨8 - (8 - k.val), by omega⟩ : Fin 9) = k := Fin.ext (by dsimp; omega)
      rw [hk]; simp [k]
  have ha0 : 103 ≤ a 0 := by
    rcases h103 with ⟨x, hxA, hx103⟩
    let k := e.symm ⟨x, hxA⟩
    have hklt : k.val < 9 := k.isLt
    have hle : k ≤ ⟨8, by omega⟩ := Fin.le_iff_val_le_val.mpr (by dsimp; omega)
    have hval : x ≤ a 0 := by
      have : (e k : ℕ) ≤ (e ⟨8, by omega⟩ : ℕ) := e.monotone hle
      simpa [a, k] using this
    omega
  have hsum_eq : ∑ i : Fin 9, a i = A.sum id := ha_bij id
  have hsq_eq : ∑ i : Fin 9, a i ^ 2 = ∑ x ∈ A, x ^ 2 := ha_bij (fun x => x ^ 2)
  have hinj : Function.Injective (fun S : Finset (Fin 9) => ∑ i ∈ S, a i) := by
    intro S T hST
    by_contra hne
    apply hno
    refine ⟨S.image a, image_subset_iff.mpr fun i _ => ha_mem i,
            T.image a, image_subset_iff.mpr fun i _ => ha_mem i, ?_, ?_⟩
    · intro himg
      apply hne
      ext i
      constructor
      · intro hi
        have : a i ∈ T.image a := himg ▸ mem_image_of_mem a hi
        rcases mem_image.mp this with ⟨j, hj, hji⟩
        exact ha_anti.injective hji ▸ hj
      · intro hi
        have : a i ∈ S.image a := himg.symm ▸ mem_image_of_mem a hi
        rcases mem_image.mp this with ⟨j, hj, hji⟩
        exact ha_anti.injective hji ▸ hj
    · rw [sum_image (fun x _ y _ h => ha_anti.injective h),
          sum_image (fun x _ y _ h => ha_anti.injective h)]
      exact hST
  exact ⟨a, ha_anti, ha_mem, ha_bnd, ha0, hsq_eq ▸ hQ, hsum_eq ▸ hS, hsum_eq, hsq_eq, hinj⟩

-- 2. Generic middle-layer span bound + 5 explicit corollaries
private lemma layer_span_bound {a : Fin 9 → ℕ} (ha : StrictAnti a)
    (hinj : Function.Injective (fun U : Finset (Fin 9) => ∑ i ∈ U, a i))
    (k1 k2 : ℕ) (hk12 : k1 ≤ k2) (hk2 : k2 ≤ 9) :
    (∑ i ∈ univ.filter (fun i : Fin 9 => 9 - k1 ≤ i.val), a i) +
      ((∑ k ∈ Icc k1 k2, Nat.choose 9 k) - 1) ≤
      ∑ i ∈ univ.filter (fun i : Fin 9 => i.val < k2), a i := by
  classical
  let ks := Icc k1 k2
  let F := ks.biUnion (fun k => (univ : Finset (Fin 9)).powersetCard k)
  let bot := ∑ i ∈ univ.filter (fun i : Fin 9 => 9 - k1 ≤ i.val), a i
  let top := ∑ i ∈ univ.filter (fun i : Fin 9 => i.val < k2), a i
  have hdisj : Set.PairwiseDisjoint (ks : Set ℕ) (fun k => (univ : Finset (Fin 9)).powersetCard k) := by
    intro a1 _ a2 _ hne
    change Disjoint ((univ : Finset (Fin 9)).powersetCard a1) ((univ : Finset (Fin 9)).powersetCard a2)
    rw [Finset.disjoint_left]
    intro U h1 h2
    exact hne ((mem_powersetCard.mp h1).2.symm.trans (mem_powersetCard.mp h2).2)
  have hcardF : F.card = ∑ k ∈ ks, Nat.choose 9 k := by
    rw [card_biUnion hdisj]
    refine sum_congr rfl fun k _ => ?_
    rw [card_powersetCard, card_univ, Fintype.card_fin]
  have hsub : F.image (fun U => ∑ i ∈ U, a i) ⊆ Icc bot top := by
    intro s hs
    rcases mem_image.mp hs with ⟨U, hUF, rfl⟩
    rcases mem_biUnion.mp hUF with ⟨k, hk, hUk⟩
    have hkI := mem_Icc.mp hk
    have hUc := (mem_powersetCard.mp hUk).2
    rw [mem_Icc]
    constructor
    · have h1 : (∑ i ∈ univ.filter (fun i : Fin 9 => 9 - k1 ≤ i.val), a i) ≤
          ∑ i ∈ univ.filter (fun i : Fin 9 => 9 - k ≤ i.val), a i :=
        sum_le_sum_of_subset (fun i hi => by
          rw [mem_filter] at hi ⊢; exact ⟨mem_univ _, by omega⟩)
      exact le_trans h1 (sum_card_ge_bot ha hUc (by omega))
    · have h2 : (∑ i ∈ univ.filter (fun i : Fin 9 => i.val < k), a i) ≤
          ∑ i ∈ univ.filter (fun i : Fin 9 => i.val < k2), a i :=
        sum_le_sum_of_subset (fun i hi => by
          rw [mem_filter] at hi ⊢; exact ⟨mem_univ _, by omega⟩)
      exact le_trans (sum_card_le_top ha hUc (by omega)) h2
  have hle_card : F.card ≤ (Icc bot top).card := by
    rw [← card_image_of_injective F hinj]
    exact card_le_card hsub
  have hpos : 1 ≤ F.card := by
    rw [hcardF]
    have hmem : k1 ∈ ks := mem_Icc.mpr ⟨le_rfl, hk12⟩
    have hch : 1 ≤ Nat.choose 9 k1 := Nat.choose_pos (by omega)
    exact le_trans hch (single_le_sum (fun _ _ => Nat.zero_le _) hmem)
  rw [Nat.card_Icc] at hle_card
  rw [hcardF] at hle_card hpos
  change bot + ((∑ k ∈ ks, Nat.choose 9 k) - 1) ≤ top
  omega

private lemma five_layer_spans {a : Fin 9 → ℕ} (ha : StrictAnti a)
    (hinj : Function.Injective (fun U : Finset (Fin 9) => ∑ i ∈ U, a i)) :
    (a 5 + a 6 + a 7 + a 8 + 125 ≤ a 0 + a 1 + a 2 + a 3) ∧
    (a 5 + a 6 + a 7 + a 8 + 251 ≤ a 0 + a 1 + a 2 + a 3 + a 4) ∧
    (a 6 + a 7 + a 8 + 83 ≤ a 0 + a 1 + a 2) ∧
    (a 6 + a 7 + a 8 + 335 ≤ a 0 + a 1 + a 2 + a 3 + a 4) ∧
    (a 6 + a 7 + a 8 + 419 ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5) := by
  have hb3 : ∑ i ∈ univ.filter (fun i : Fin 9 => 9 - 3 ≤ i.val), a i = a 6 + a 7 + a 8 := by
    have : univ.filter (fun i : Fin 9 => 9 - 3 ≤ i.val) = {6, 7, 8} := by decide
    rw [this]; simp [add_assoc]
  have hb4 : ∑ i ∈ univ.filter (fun i : Fin 9 => 9 - 4 ≤ i.val), a i = a 5 + a 6 + a 7 + a 8 := by
    have : univ.filter (fun i : Fin 9 => 9 - 4 ≤ i.val) = {5, 6, 7, 8} := by decide
    rw [this]; simp [add_assoc]
  have ht3 : ∑ i ∈ univ.filter (fun i : Fin 9 => i.val < 3), a i = a 0 + a 1 + a 2 := by
    have : univ.filter (fun i : Fin 9 => i.val < 3) = {0, 1, 2} := by decide
    rw [this]; simp [add_assoc]
  have ht4 : ∑ i ∈ univ.filter (fun i : Fin 9 => i.val < 4), a i = a 0 + a 1 + a 2 + a 3 := by
    have : univ.filter (fun i : Fin 9 => i.val < 4) = {0, 1, 2, 3} := by decide
    rw [this]; simp [add_assoc]
  have ht5 : ∑ i ∈ univ.filter (fun i : Fin 9 => i.val < 5), a i = a 0 + a 1 + a 2 + a 3 + a 4 := by
    have : univ.filter (fun i : Fin 9 => i.val < 5) = {0, 1, 2, 3, 4} := by decide
    rw [this]; simp [add_assoc]
  have ht6 : ∑ i ∈ univ.filter (fun i : Fin 9 => i.val < 6), a i = a 0 + a 1 + a 2 + a 3 + a 4 + a 5 := by
    have : univ.filter (fun i : Fin 9 => i.val < 6) = {0, 1, 2, 3, 4, 5} := by decide
    rw [this]; simp [add_assoc]
  have h1 := layer_span_bound ha hinj 4 4 (by omega) (by omega)
  have h2 := layer_span_bound ha hinj 4 5 (by omega) (by omega)
  have h3 := layer_span_bound ha hinj 3 3 (by omega) (by omega)
  have h4 := layer_span_bound ha hinj 3 5 (by omega) (by omega)
  have h5 := layer_span_bound ha hinj 3 6 (by omega) (by omega)
  have c1 : (∑ k ∈ Icc 4 4, Nat.choose 9 k) - 1 = 125 := by decide
  have c2 : (∑ k ∈ Icc 4 5, Nat.choose 9 k) - 1 = 251 := by decide
  have c3 : (∑ k ∈ Icc 3 3, Nat.choose 9 k) - 1 = 83 := by decide
  have c4 : (∑ k ∈ Icc 3 5, Nat.choose 9 k) - 1 = 335 := by decide
  have c5 : (∑ k ∈ Icc 3 6, Nat.choose 9 k) - 1 = 419 := by decide
  rw [hb4, ht4, c1] at h1
  rw [hb4, ht5, c2] at h2
  rw [hb3, ht3, c3] at h3
  rw [hb3, ht5, c4] at h4
  rw [hb3, ht6, c5] at h5
  exact ⟨h1, h2, h3, h4, h5⟩

-- 3. Pure-Nat bitmask g(0..6) = [0,1,2,4,7,13,22] checker & soundness (<0.1s in decide +kernel!)
private def stepLayersAux (v : Nat) (prev : Nat) : List Nat → Option (List Nat)
  | [] => some [Nat.shiftLeft prev v]
  | cur :: rest =>
    let sh := Nat.shiftLeft prev v
    if Nat.beq (Nat.land sh cur) 0 then
      match stepLayersAux v cur rest with
      | none => none
      | some tl => some (Nat.lor sh cur :: tl)
    else none

private def stepLayers (v : Nat) : List Nat → Option (List Nat)
  | [] => some [1, Nat.shiftLeft 1 v]
  | c0 :: rest =>
    match stepLayersAux v c0 rest with
    | none => none
    | some tl => some (c0 :: tl)

private def gBound : Nat → Nat
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 7 | 5 => 13 | _ => 22

private def minNextVal (limGap gap acc : Nat) : List Nat → Nat
  | [] => acc
  | p :: ps =>
    if Nat.blt gap limGap then
      let req := Nat.add p (gBound gap)
      minNextVal limGap (Nat.add gap 1) (if Nat.blt acc req then req else acc) ps
    else acc

private def gSearchLoop (sub : Nat → List Nat → Bool)
    (layers : List Nat) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, v =>
    let okV := match stepLayers v layers with
      | none => true
      | some nl => sub v nl
    if okV then gSearchLoop sub layers fuel (Nat.add v 1) else false

private def gSearchRec (lim limGap d1 : Nat) : Nat → List Nat → List Nat → Bool
  | 0, _, _ => false
  | rem + 1, prevs, layers =>
    let lo := minNextVal limGap 1 0 prevs
    let need := gBound rem
    if Nat.blt lim (Nat.add lo need) then true
    else
      let hi0 := Nat.sub lim need
      let hi := if and (Nat.beq rem 1) (Nat.blt 0 d1) then
                  let symHi := Nat.sub lim d1
                  if Nat.blt symHi hi0 then symHi else hi0
                else hi0
      if Nat.blt hi lo then true
      else
        let span := Nat.add (Nat.sub hi lo) 1
        gSearchLoop (fun v nl =>
          let nd1 := if Nat.beq d1 0 then v else d1
          gSearchRec lim limGap nd1 rem (v :: prevs) nl) layers span lo

private lemma ok_g4 : gSearchRec 6 4 0 4 [0] [1, 1] = true := by decide +kernel
private lemma ok_g5 : gSearchRec 12 5 0 5 [0] [1, 1] = true := by decide +kernel
private lemma ok_g6 : gSearchRec 21 6 0 6 [0] [1, 1] = true := by decide +kernel

private lemma testBit_shiftLeft_iff (m v s : Nat) :
    (Nat.shiftLeft m v).testBit s = true ↔ ∃ x, m.testBit x = true ∧ x + v = s := by
  change (m <<< v).testBit s = true ↔ _
  rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hvs, hx⟩; exact ⟨s - v, hx, by omega⟩
  · rintro ⟨x, hx, rfl⟩
    have hsub : x + v - v = x := by omega
    exact ⟨by omega, by rwa [hsub]⟩

private lemma land_eq_zero_of_disj {a b : Nat}
    (h : ∀ s, a.testBit s = true → b.testBit s = false) : Nat.land a b = 0 := by
  change a &&& b = 0
  apply Nat.eq_of_testBit_eq
  intro s
  rw [Nat.testBit_and, Nat.zero_testBit]
  cases ha : a.testBit s
  · rfl
  · rw [h s ha]; rfl

private lemma testBit_lor_iff (a b s : Nat) :
    (Nat.lor a b).testBit s = true ↔ a.testBit s = true ∨ b.testBit s = true := by
  change (a ||| b).testBit s = true ↔ _
  rw [Nat.testBit_or, Bool.or_eq_true]

private lemma testBit_one_iff (s : Nat) : (1 : Nat).testBit s = true ↔ s = 0 := by
  cases s with
  | zero => decide
  | succ s' => simp [Nat.testBit_succ]

private def LayersCorrect (k : Nat) (f : Fin k → Nat) (layers : List Nat) : Prop :=
  layers.length = k + 1 ∧
  ∀ c (hc : c < layers.length) (s : Nat),
    (layers[c]'hc).testBit s = true ↔ ∃ S : Finset (Fin k), S.card = c ∧ ∑ i ∈ S, f i = s

private lemma stepLayersAux_sound {v : Nat} {prev : Nat} {rest : List Nat}
    (hdisj : ∀ (c : Nat) (hc : c < rest.length) (x : Nat),
      ((prev :: rest)[c]'(by simp; omega)).testBit x = true → (rest[c]'hc).testBit (x + v) = false) :
    ∃ tl, stepLayersAux v prev rest = some tl ∧ tl.length = rest.length + 1 ∧
      (∀ c (hc : c < rest.length) (htl : c < tl.length) (s : Nat),
        (tl[c]'htl).testBit s = true ↔
          (∃ x, ((prev :: rest)[c]'(by simp; omega)).testBit x = true ∧ x + v = s) ∨ (rest[c]'hc).testBit s = true) ∧
      (∀ (htl : rest.length < tl.length) (s : Nat),
        (tl[rest.length]'htl).testBit s = true ↔
          ∃ x, ((prev :: rest)[rest.length]'(by simp)).testBit x = true ∧ x + v = s) := by
  induction rest generalizing prev with
  | nil =>
    refine ⟨[Nat.shiftLeft prev v], rfl, by simp, ?_, ?_⟩
    · intro c hc; simp at hc
    · intro _ s; simp only [List.length_nil, List.getElem_cons_zero]; exact testBit_shiftLeft_iff prev v s
  | cons cur rs ih =>
    have hzero : Nat.land (Nat.shiftLeft prev v) cur = 0 := by
      apply land_eq_zero_of_disj
      intro s hs
      rcases (testBit_shiftLeft_iff prev v s).mp hs with ⟨x, hx, rfl⟩
      exact hdisj 0 (by simp) x (by simpa using hx)
    have hbeq : Nat.beq (Nat.land (Nat.shiftLeft prev v) cur) 0 = true := by rw [hzero]; rfl
    have hdisj' : ∀ c (hc : c < rs.length) x,
        ((cur :: rs)[c]'(by simp; omega)).testBit x = true → (rs[c]'hc).testBit (x + v) = false :=
      fun c hc x hx => hdisj (c + 1) (by simp; omega) x hx
    obtain ⟨tl', hstep', hlen_tl, hmid', hlast'⟩ := ih hdisj'
    refine ⟨Nat.lor (Nat.shiftLeft prev v) cur :: tl', by simp only [stepLayersAux, hbeq, ite_true, hstep'],
      by simp [hlen_tl], ?_, ?_⟩
    · intro c hc htl s
      cases c with
      | zero =>
        simp only [List.getElem_cons_zero, testBit_lor_iff, testBit_shiftLeft_iff]
      | succ c' => exact hmid' c' (by simp at hc; omega) (by simp at htl; omega) s
    · intro htl s; simpa using hlast' (by simp at htl; omega) s

private lemma layers_init_correct (f : Fin 1 → Nat) (hf0 : f 0 = 0) :
    LayersCorrect 1 f [1, 1] := by
  refine ⟨rfl, ?_⟩
  intro c hc s
  simp only [List.length_cons, List.length_nil] at hc
  have hc2 : c = 0 ∨ c = 1 := by omega
  rcases hc2 with rfl | rfl
  · simp only [List.getElem_cons_zero, testBit_one_iff]
    constructor
    · rintro rfl; exact ⟨∅, rfl, rfl⟩
    · rintro ⟨S, hSc, rfl⟩; rw [card_eq_zero.mp hSc]; simp
  · simp only [List.getElem_cons_succ, List.getElem_cons_zero, testBit_one_iff]
    constructor
    · rintro rfl; exact ⟨{0}, rfl, by simp [hf0]⟩
    · rintro ⟨S, hSc, rfl⟩
      have hS : S = {0} := by
        rcases card_eq_one.mp hSc with ⟨i, rfl⟩
        have : i = 0 := Fin.ext (by omega)
        subst this; rfl
      simp [hS, hf0]

private lemma layers_step_correct {k : Nat} {f : Fin (k + 1) → Nat} {layers : List Nat}
    (_hk : 0 < k) (_hk6 : k ≤ 6)
    (hcur : LayersCorrect k (fun i => f ⟨i.val, by omega⟩) layers)
    (heq_inj : ∀ S T : Finset (Fin (k + 1)), S.card = T.card → ∑ i ∈ S, f i = ∑ i ∈ T, f i → S = T) :
    ∃ nl, stepLayers (f ⟨k, by omega⟩) layers = some nl ∧ LayersCorrect (k + 1) f nl := by
  rcases layers with _ | ⟨c0, rest⟩
  · have := hcur.1; simp at this
  have hlen_lay : (c0 :: rest).length = k + 1 := hcur.1
  have hrest_len : rest.length = k := by simp at hlen_lay; omega
  have hdisj : ∀ (c : Nat) (hc : c < rest.length) (x : Nat),
      ((c0 :: rest)[c]'(by simp; omega)).testBit x = true → (rest[c]'hc).testBit (x + f ⟨k, by omega⟩) = false := by
    intro c hc x hx
    cases hx' : (rest[c]'hc).testBit (x + f ⟨k, by omega⟩)
    · rfl
    · exfalso
      have hx_sub := (hcur.2 c (by simp; omega) x).mp hx
      have hx'_sub := (hcur.2 (c + 1) (by simp; omega) (x + f ⟨k, by omega⟩)).mp hx'
      rcases hx_sub with ⟨S1, hS1c, hS1s⟩
      rcases hx'_sub with ⟨S2, hS2c, hS2s⟩
      dsimp only at hS1s hS2s
      let emb : Fin k ↪ Fin (k + 1) := ⟨fun i => ⟨i.val, by omega⟩, fun i j h => Fin.ext (by simpa [Fin.ext_iff] using h)⟩
      let S1' : Finset (Fin (k + 1)) := insert ⟨k, by omega⟩ (S1.map emb)
      let S2' : Finset (Fin (k + 1)) := S2.map emb
      have hnot1 : (⟨k, by omega⟩ : Fin (k + 1)) ∉ S1.map emb := by
        intro hm; rcases mem_map.mp hm with ⟨i, _, hi⟩
        have hiLt : i.val < k := i.isLt
        have hval := congrArg Fin.val hi; change i.val = k at hval; omega
      have hnot2 : (⟨k, by omega⟩ : Fin (k + 1)) ∉ S2' := by
        intro hm; rcases mem_map.mp hm with ⟨i, _, hi⟩
        have hiLt : i.val < k := i.isLt
        have hval := congrArg Fin.val hi; change i.val = k at hval; omega
      have hcEq : S1'.card = S2'.card := by
        dsimp [S1', S2']; rw [card_insert_of_notMem hnot1, card_map, card_map, hS1c, hS2c]
      have hsEq : ∑ i ∈ S1', f i = ∑ i ∈ S2', f i := by
        dsimp [S1', S2']; rw [sum_insert hnot1, sum_map, sum_map]
        change f ⟨k, by omega⟩ + ∑ i ∈ S1, f ⟨i.val, by omega⟩ = ∑ i ∈ S2, f ⟨i.val, by omega⟩
        omega
      have hEq := heq_inj S1' S2' hcEq hsEq
      exact hnot2 (hEq ▸ mem_insert_self _ _)
  obtain ⟨tl, hstep, hlen, hmid, hlast⟩ :=
    stepLayersAux_sound (v := f ⟨k, by omega⟩) hdisj
  refine ⟨c0 :: tl, by simp only [stepLayers, hstep], by simp [hlen, hrest_len], ?_⟩
  intro c hc s
  let emb : Fin k ↪ Fin (k + 1) := ⟨fun i => ⟨i.val, by omega⟩, fun i j h => Fin.ext (by simpa [Fin.ext_iff] using h)⟩
  let lastIdx : Fin (k + 1) := ⟨k, by omega⟩
  have hnot_emb : ∀ S : Finset (Fin k), lastIdx ∉ S.map emb := by
    intro S hm; rcases mem_map.mp hm with ⟨i, _, hi⟩
    have hiLt : i.val < k := i.isLt
    have hval := congrArg Fin.val hi; change i.val = k at hval; omega
  cases c with
  | zero =>
    simp only [List.getElem_cons_zero]
    rw [show c0 = (c0 :: rest)[0]'(by simp) from rfl, hcur.2 0 (by simp) s]
    constructor
    · rintro ⟨S, hSc, rfl⟩; rw [card_eq_zero.mp hSc]; exact ⟨∅, rfl, rfl⟩
    · rintro ⟨S, hSc, rfl⟩; rw [card_eq_zero.mp hSc]; exact ⟨∅, rfl, rfl⟩
  | succ c' =>
    simp only [List.getElem_cons_succ]
    have htlc : c' < tl.length := by simp at hc; omega
    by_cases hck : c' < rest.length
    · rw [hmid c' hck htlc s]
      simp_rw [hcur.2 c' (by simp; omega),
        show rest[c']'hck = (c0 :: rest)[c' + 1]'(by simp; omega) from rfl,
        hcur.2 (c' + 1) (by simp; omega)]
      constructor
      · rintro (⟨x, ⟨S, hSc, rfl⟩, rfl⟩ | ⟨S, hSc, rfl⟩)
        · refine ⟨insert lastIdx (S.map emb), ?_, ?_⟩
          · rw [card_insert_of_notMem (hnot_emb S), card_map, hSc]
          · rw [sum_insert (hnot_emb S), sum_map]
            change f ⟨k, by omega⟩ + ∑ i ∈ S, f ⟨i.val, by omega⟩ = (∑ i ∈ S, f ⟨i.val, by omega⟩) + f ⟨k, by omega⟩
            omega
        · exact ⟨S.map emb, by rw [card_map, hSc], by rw [sum_map]; rfl⟩
      · rintro ⟨S, hSc, rfl⟩
        by_cases hm : lastIdx ∈ S
        · left
          let S0 : Finset (Fin k) := (S.erase lastIdx).preimage emb (fun x _ y _ h => emb.injective h)
          have hmap : S0.map emb = S.erase lastIdx := by
            ext j; rw [mem_map, mem_erase]
            constructor
            · rintro ⟨i, hi, rfl⟩; exact mem_erase.mp (Finset.mem_preimage.mp hi)
            · rintro ⟨hne, hjS⟩
              have hjlt : j.val < k := by have := j.isLt; have : j.val ≠ k := fun h => hne (Fin.ext (by dsimp [lastIdx]; exact h)); omega
              refine ⟨⟨j.val, hjlt⟩, Finset.mem_preimage.mpr (mem_erase.mpr ?_), Fin.ext rfl⟩
              have hemb : emb ⟨j.val, hjlt⟩ = j := Fin.ext rfl
              rw [hemb]; exact ⟨hne, hjS⟩
          refine ⟨∑ i ∈ S0, f ⟨i.val, by omega⟩, ⟨S0, ?_, rfl⟩, ?_⟩
          · have h1 := card_erase_of_mem hm
            have h2 : S0.card = (S.erase lastIdx).card := by rw [← card_map, hmap]
            omega
          · have hsum := add_sum_erase S f hm
            rw [← hmap, sum_map] at hsum
            change f ⟨k, by omega⟩ + ∑ i ∈ S0, f ⟨i.val, by omega⟩ = ∑ i ∈ S, f i at hsum
            omega
        · right
          let S0 : Finset (Fin k) := S.preimage emb (fun x _ y _ h => emb.injective h)
          have hmap : S0.map emb = S := by
            ext j; rw [mem_map]
            constructor
            · rintro ⟨i, hi, rfl⟩; exact Finset.mem_preimage.mp hi
            · intro hjS
              have hjlt : j.val < k := by have := j.isLt; have : j.val ≠ k := fun h => hm ((show j = lastIdx from Fin.ext h) ▸ hjS); omega
              refine ⟨⟨j.val, hjlt⟩, Finset.mem_preimage.mpr ?_, Fin.ext rfl⟩
              have hemb : emb ⟨j.val, hjlt⟩ = j := Fin.ext rfl
              rwa [hemb]
          exact ⟨S0, by rw [← card_map, hmap, hSc], by rw [← hmap, sum_map]; rfl⟩
    · have hc'Eq : c' = rest.length := by omega
      subst hc'Eq
      rw [hlast htlc s]
      simp_rw [hcur.2 rest.length (by simp)]
      constructor
      · rintro ⟨x, ⟨S, hSc, rfl⟩, rfl⟩
        refine ⟨insert lastIdx (S.map emb), ?_, ?_⟩
        · rw [card_insert_of_notMem (hnot_emb S), card_map, hSc]
        · rw [sum_insert (hnot_emb S), sum_map]
          change f ⟨k, by omega⟩ + ∑ i ∈ S, f ⟨i.val, by omega⟩ = (∑ i ∈ S, f ⟨i.val, by omega⟩) + f ⟨k, by omega⟩
          omega
      · rintro ⟨S, hSc, rfl⟩
        have hSuniv : S = univ := eq_univ_of_card S (by simp; omega)
        subst hSuniv
        refine ⟨∑ i : Fin k, f ⟨i.val, by omega⟩, ⟨univ, by simp [hrest_len], rfl⟩, ?_⟩
        rw [Fin.sum_univ_castSucc]; rfl

private lemma gSearchLoop_false {sub : Nat → List Nat → Bool} {layers : List Nat}
    {fuel v0 v : Nat} {nl : List Nat}
    (hv_ge : v0 ≤ v) (hv_lt : v < v0 + fuel)
    (hstep : stepLayers v layers = some nl) (hsub : sub v nl = false) :
    gSearchLoop sub layers fuel v0 = false := by
  induction fuel generalizing v0 with
  | zero => omega
  | succ fuel ih =>
    unfold gSearchLoop
    by_cases heq : v = v0
    · subst heq; simp [hstep, hsub]
    · have hrec := ih (v0 := Nat.add v0 1) (by change v0 + 1 ≤ v; omega) (by change v < v0 + 1 + fuel; omega)
      dsimp only
      split_ifs
      · exact hrec
      · rfl

private lemma minNextVal_le {limGap gap acc : Nat} {ps : List Nat} {x : Nat}
    (hacc : acc ≤ x) (hps : ∀ i (hi : i < ps.length), gap + i < limGap → ps[i]'hi + gBound (gap + i) ≤ x) :
    minNextVal limGap gap acc ps ≤ x := by
  induction ps generalizing gap acc with
  | nil => exact hacc
  | cons p ps ih =>
    unfold minNextVal
    by_cases hlt : gap < limGap
    · simp only [Nat.blt_eq.mpr hlt, ite_true]
      have hp : p + gBound gap ≤ x := hps 0 (by simp) (by omega)
      apply ih
      · split_ifs
        · exact hp
        · exact hacc
      · intro i hi hglt
        have h1 := hps (i + 1) (by simp; omega) (by change gap + 1 + i < limGap at hglt; omega)
        change ps[i]'hi + gBound (gap + 1 + i) ≤ x
        have heq : gap + 1 + i = gap + (i + 1) := by omega
        rw [heq]; exact h1
    · simp only [blt_false_of_le (by omega : limGap ≤ gap), Bool.false_eq_true, ite_false]
      exact hacc

private lemma gSearchRec_sound {lim limGap : Nat} :
    ∀ (rem k d1 : Nat) (f : Fin (k + rem) → Nat) (prevs : List Nat) (layers : List Nat),
      0 < k → k + rem ≤ 7 → limGap = k + rem - 1 →
      StrictMono f →
      ((k = 1 ∧ d1 = 0) ∨ (1 < k ∧ 0 < d1 ∧ ∀ h1 : 1 < k + rem, d1 = f ⟨1, h1⟩)) →
      (∀ (hk2 : 2 ≤ k + rem), f ⟨1, by omega⟩ + f ⟨k + rem - 2, by omega⟩ ≤ lim) →
      prevs.length = k →
      (∀ i (hi : i < k), prevs.getD i 0 = f ⟨k - 1 - i, by omega⟩) →
      LayersCorrect k (fun i => f ⟨i.val, by omega⟩) layers →
      (∀ S T : Finset (Fin (k + rem)), S.card = T.card → ∑ i ∈ S, f i = ∑ i ∈ T, f i → S = T) →
      (∀ i j : Fin (k + rem), i ≤ j → j.val - i.val < limGap → f i + gBound (j.val - i.val) ≤ f j) →
      (∀ i : Fin (k + rem), f i ≤ lim) →
      gSearchRec lim limGap d1 rem prevs layers = false := by
  intro rem
  induction rem with
  | zero =>
    intro k d1 f prevs layers _ _ _ _ _ _ _ _ _ _ _ _
    rfl
  | succ rem ih =>
    intro k d1 f prevs layers hk hk7 hlg hf_mono hd1 hsym hplen hprev hlay heq hgap hlim
    unfold gSearchRec
    let v := f ⟨k, by omega⟩
    have hv_lo : minNextVal limGap 1 0 prevs ≤ v := by
      apply minNextVal_le (Nat.zero_le _)
      intro i hi hglt
      have hik : i < k := by omega
      have hge : prevs[i]'hi = prevs.getD i 0 := (List.getD_eq_getElem prevs 0 hi).symm
      rw [hge, hprev i hik]
      have h1 := hgap ⟨k - 1 - i, by omega⟩ ⟨k, by omega⟩ (Fin.le_iff_val_le_val.mpr (by dsimp; omega)) (by dsimp; omega)
      have hsub : k - (k - 1 - i) = 1 + i := by omega
      simpa [v, hsub] using h1
    have hv_hi0 : v + gBound rem ≤ lim := by
      rcases Nat.eq_zero_or_pos rem with rfl | hrem
      · have := hlim ⟨k, by omega⟩; simp [gBound, v] at *; omega
      · have h1 := hgap ⟨k, by omega⟩ ⟨k + rem, by omega⟩ (Fin.le_iff_val_le_val.mpr (by dsimp; omega)) (by dsimp; omega)
        have h2 := hlim ⟨k + rem, by omega⟩
        have hsub : k + rem - k = rem := by omega
        simpa [v, hsub] using le_trans h1 h2
    have hnot_lt : Nat.blt lim (Nat.add (minNextVal limGap 1 0 prevs) (gBound rem)) = false :=
      blt_false_of_le (by change minNextVal limGap 1 0 prevs + gBound rem ≤ lim; omega)
    simp only [hnot_lt, Bool.false_eq_true, ite_false]
    have hv_hi : v ≤ if and (Nat.beq rem 1) (Nat.blt 0 d1) then
        let symHi := Nat.sub lim d1
        if Nat.blt symHi (Nat.sub lim (gBound rem)) then symHi else Nat.sub lim (gBound rem)
      else Nat.sub lim (gBound rem) := by
      dsimp only
      split_ifs with h1 _
      · have hr1 : rem = 1 := by
          cases h : Nat.beq rem 1
          · simp [h] at h1
          · exact Nat.eq_of_beq_eq_true h
        have hdpos : 0 < d1 := by
          cases h : Nat.blt 0 d1
          · simp [h] at h1
          · exact Nat.blt_eq.mp h
        rcases hd1 with ⟨_, rfl⟩ | ⟨hk1, _, hd1eq⟩
        · omega
        · have hs := hsym (by omega)
          have hkEq : k + (rem + 1) - 2 = k := by omega
          have hfk : f ⟨k + (rem + 1) - 2, by omega⟩ = v := by
            dsimp [v]; congr 1; exact Fin.ext hkEq
          rw [hfk, ← hd1eq (by omega)] at hs
          change v ≤ lim - d1; omega
      · change v ≤ lim - gBound rem; omega
      · change v ≤ lim - gBound rem; omega
    have hnot_hi_lo : Nat.blt (if and (Nat.beq rem 1) (Nat.blt 0 d1) then
        let symHi := Nat.sub lim d1
        if Nat.blt symHi (Nat.sub lim (gBound rem)) then symHi else Nat.sub lim (gBound rem)
      else Nat.sub lim (gBound rem)) (minNextVal limGap 1 0 prevs) = false :=
      blt_false_of_le (le_trans hv_lo hv_hi)
    simp only [hnot_hi_lo, Bool.false_eq_true, ite_false]
    let f1 : Fin (k + 1) → Nat := fun i => f ⟨i.val, by omega⟩
    have heq1 : ∀ S T : Finset (Fin (k + 1)), S.card = T.card → ∑ i ∈ S, f1 i = ∑ i ∈ T, f1 i → S = T := by
      intro S T hc hs
      let emb : Fin (k + 1) ↪ Fin (k + (rem + 1)) :=
        ⟨fun i => ⟨i.val, by omega⟩, fun i j h => Fin.ext (by simpa [Fin.ext_iff] using h)⟩
      have hEq := heq (S.map emb) (T.map emb) (by rw [card_map, card_map, hc])
        (by rw [sum_map, sum_map]; exact hs)
      ext i
      have : emb i ∈ S.map emb ↔ emb i ∈ T.map emb := by rw [hEq]
      simpa [mem_map] using this
    obtain ⟨nl, hstep, hlay'⟩ := layers_step_correct (f := f1) hk (by omega) hlay heq1
    refine gSearchLoop_false hv_lo (by
      let hi := if and (Nat.beq rem 1) (Nat.blt 0 d1) then
          let symHi := Nat.sub lim d1
          if Nat.blt symHi (Nat.sub lim (gBound rem)) then symHi else Nat.sub lim (gBound rem)
        else Nat.sub lim (gBound rem)
      change v < minNextVal limGap 1 0 prevs + (hi - minNextVal limGap 1 0 prevs + 1)
      have : v ≤ hi := hv_hi
      omega) hstep ?_
    let f' : Fin ((k + 1) + rem) → Nat := fun i => f ⟨i.val, by omega⟩
    have hnd1 : ((k + 1 = 1 ∧ (if Nat.beq d1 0 then v else d1) = 0) ∨
        (1 < k + 1 ∧ 0 < (if Nat.beq d1 0 then v else d1) ∧
          ∀ h1 : 1 < (k + 1) + rem, (if Nat.beq d1 0 then v else d1) = f' ⟨1, h1⟩)) := by
      rcases hd1 with ⟨rfl, rfl⟩ | ⟨hk1, hdpos, hd1eq⟩
      · right
        have hlt01 : f ⟨0, by omega⟩ < f ⟨1, by omega⟩ := hf_mono (by simp [Fin.lt_def])
        exact ⟨by omega, by dsimp [v]; omega, fun h1 => rfl⟩
      · right
        have hne : Nat.beq d1 0 = false := beq_false_of_ne (by omega)
        simp only [hne, Bool.false_eq_true, ite_false]
        exact ⟨by omega, hdpos, fun h1 => hd1eq (by omega)⟩
    refine ih (k + 1) (if Nat.beq d1 0 then v else d1) f' (v :: prevs) nl (by omega) (by omega) (by omega)
      (fun i j hij => hf_mono (show (⟨i.val, by omega⟩ : Fin (k + (rem + 1))) < ⟨j.val, by omega⟩ from hij))
      hnd1 ?_ (by simp [hplen]) ?_ hlay' ?_ ?_ ?_
    · intro hk2
      have h1 := hsym (by omega)
      have heqIdx : (⟨(k + 1) + rem - 2, by omega⟩ : Fin (k + (rem + 1))) = ⟨k + (rem + 1) - 2, by omega⟩ :=
        Fin.ext (by dsimp; omega)
      dsimp [f']; rw [heqIdx]; exact h1
    · intro i hi
      cases i with
      | zero => simp [f', v]
      | succ i' =>
        simp only [List.getD_cons_succ]
        rw [hprev i' (by omega)]
        congr 1; apply Fin.ext; dsimp; omega
    · intro S T hc hs
      let e : Fin ((k + 1) + rem) ≃ Fin (k + (rem + 1)) :=
        { toFun := fun i => ⟨i.val, by omega⟩, invFun := fun i => ⟨i.val, by omega⟩,
          left_inv := fun i => Fin.ext rfl, right_inv := fun i => Fin.ext rfl }
      have hEq := heq (S.map e.toEmbedding) (T.map e.toEmbedding) (by rw [card_map, card_map, hc])
        (by rw [sum_map, sum_map]; exact hs)
      ext i
      have : e i ∈ S.map e.toEmbedding ↔ e i ∈ T.map e.toEmbedding := by rw [hEq]
      simpa [mem_map] using this
    · intro i j hij hlt
      have hilt := i.isLt; have hjlt := j.isLt
      exact hgap ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ (Fin.le_iff_val_le_val.mpr hij) (by dsimp; omega)
    · intro i; exact hlim ⟨i.val, by omega⟩

private lemma a_gap_g6 {a : Fin 9 → ℕ} (ha : StrictAnti a)
    (hinj : Function.Injective (fun U : Finset (Fin 9) => ∑ i ∈ U, a i)) :
    ∀ i j : Fin 9, i ≤ j → j.val - i.val ≤ 6 → a j + gBound (j.val - i.val) ≤ a i := by
  have hstep : ∀ d : ℕ, d ≤ 6 → ∀ i j : Fin 9, i ≤ j → j.val - i.val = d → a j + gBound d ≤ a i := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro hd6 i j hij hdiff
      have hilt : i.val < 9 := i.isLt
      have hjlt : j.val < 9 := j.isLt
      have hle_val : i.val ≤ j.val := hij
      by_cases hd0 : d = 0
      · subst hd0; have : i = j := Fin.ext (by omega); subst this; simp [gBound]
      · by_cases hd1 : d = 1
        · subst hd1
          have hlt : a j < a i := ha (Fin.lt_def.mpr (by omega))
          simp [gBound]; omega
        · by_cases hd2 : d = 2
          · subst hd2
            let m : Fin 9 := ⟨i.val + 1, by omega⟩
            have h1 : a m < a i := ha (Fin.lt_def.mpr (by dsimp [m]; omega))
            have h2 : a j < a m := ha (Fin.lt_def.mpr (by dsimp [m]; omega))
            simp [gBound]; omega
          · by_cases hd3 : d = 3
            · subst hd3
              let m1 : Fin 9 := ⟨i.val + 1, by omega⟩
              let m2 : Fin 9 := ⟨i.val + 2, by omega⟩
              have h1 : a m1 < a i := ha (Fin.lt_def.mpr (by dsimp [m1]; omega))
              have h2 : a m2 < a m1 := ha (Fin.lt_def.mpr (by dsimp [m1, m2]; omega))
              have h3 : a j < a m2 := ha (Fin.lt_def.mpr (by dsimp [m2]; omega))
              by_contra hlt
              simp only [gBound] at hlt
              have heq_sum : a i + a j = a m1 + a m2 := by omega
              have hne1 : i ≠ j := fun h => by have := congrArg Fin.val h; omega
              have hne2 : m1 ≠ m2 := fun h => by have := congrArg Fin.val h; dsimp [m1, m2] at this; omega
              have hS : ∑ x ∈ ({i, j} : Finset (Fin 9)), a x = ∑ x ∈ ({m1, m2} : Finset (Fin 9)), a x := by
                rw [sum_pair hne1, sum_pair hne2]; exact heq_sum
              have hEq := hinj hS
              have hm1 : m1 ∈ ({i, j} : Finset (Fin 9)) := hEq ▸ mem_insert_self m1 {m2}
              rcases mem_insert.mp hm1 with h | h
              · have := congrArg Fin.val h; dsimp [m1] at this; omega
              · have := congrArg Fin.val (mem_singleton.mp h); dsimp [m1] at this; omega
            · have hd46 : d = 4 ∨ d = 5 ∨ d = 6 := by omega
              have hok : gSearchRec (gBound d - 1) d 0 d [0] [1, 1] = true := by
                rcases hd46 with rfl | rfl | rfl
                · exact ok_g4
                · exact ok_g5
                · exact ok_g6
              by_contra hlt
              let lim := gBound d - 1
              have hai_le : a i - a j ≤ lim := by
                have : 1 ≤ gBound d := by rcases hd46 with rfl | rfl | rfl <;> decide
                dsimp [lim]; omega
              let f1 : Fin (1 + d) → ℕ := fun t => a ⟨j.val - t.val, by omega⟩ - a j
              let f2 : Fin (1 + d) → ℕ := fun t => a i - a ⟨i.val + t.val, by omega⟩
              have hsum_sym : (f1 ⟨1, by omega⟩ + f1 ⟨1 + d - 2, by omega⟩) +
                  (f2 ⟨1, by omega⟩ + f2 ⟨1 + d - 2, by omega⟩) ≤ 2 * lim := by
                have hjm1 : a j ≤ a ⟨j.val - 1, by omega⟩ := le_of_lt (ha (Fin.lt_def.mpr (by dsimp; omega)))
                have hip1 : a j ≤ a ⟨i.val + 1, by omega⟩ := le_of_lt (ha (Fin.lt_def.mpr (by dsimp; omega)))
                have htop1 : a ⟨i.val + 1, by omega⟩ ≤ a i := le_of_lt (ha (Fin.lt_def.mpr (by dsimp; omega)))
                have htop2 : a ⟨j.val - 1, by omega⟩ ≤ a i := le_of_lt (ha (Fin.lt_def.mpr (by dsimp; omega)))
                have heq1 : (⟨j.val - (1 + d - 2), by omega⟩ : Fin 9) = ⟨i.val + 1, by omega⟩ := Fin.ext (by dsimp; omega)
                have heq2 : (⟨i.val + (1 + d - 2), by omega⟩ : Fin 9) = ⟨j.val - 1, by omega⟩ := Fin.ext (by dsimp; omega)
                dsimp [f1, f2]
                rw [heq1, heq2]
                omega
              have hrun : ∀ (f : Fin (1 + d) → ℕ),
                  f ⟨0, by omega⟩ = 0 → StrictMono f →
                  (f ⟨1, by omega⟩ + f ⟨1 + d - 2, by omega⟩ ≤ lim) →
                  (∀ S T : Finset (Fin (1 + d)), S.card = T.card → ∑ t ∈ S, f t = ∑ t ∈ T, f t → S = T) →
                  (∀ x y : Fin (1 + d), x ≤ y → y.val - x.val < d → f x + gBound (y.val - x.val) ≤ f y) →
                  (∀ x : Fin (1 + d), f x ≤ lim) → False := by
                intro f hf0 hfmono hsym heq_f hgap_f hlim_f
                have hfalse := gSearchRec_sound (lim := lim) (limGap := d) d 1 0 f [0] [1, 1] (by omega) (by omega) (by omega)
                  hfmono (Or.inl ⟨rfl, rfl⟩) (fun _ => hsym) rfl
                  (fun t ht => by rcases Nat.lt_one_iff.mp ht with rfl; exact hf0.symm)
                  (layers_init_correct (fun t => f ⟨t.val, by omega⟩) hf0) heq_f hgap_f hlim_f
                rw [hok] at hfalse; cases hfalse
              by_cases hcase : f1 ⟨1, by omega⟩ + f1 ⟨1 + d - 2, by omega⟩ ≤ lim
              · refine hrun f1 (by simp [f1]) ?_ hcase ?_ ?_ ?_
                · intro x y hxy
                  have hx := x.isLt; have hy := y.isLt; have hltv : x.val < y.val := hxy
                  have hlt1 : a ⟨j.val - x.val, by omega⟩ < a ⟨j.val - y.val, by omega⟩ :=
                    ha (Fin.lt_def.mpr (by dsimp; omega))
                  have hge : a j ≤ a ⟨j.val - x.val, by omega⟩ :=
                    ha.antitone (Fin.le_iff_val_le_val.mpr (by dsimp; omega))
                  dsimp [f1]; omega
                · intro S T hSc hSs
                  let emb : Fin (1 + d) ↪ Fin 9 :=
                    ⟨fun t => ⟨j.val - t.val, by omega⟩, fun x y h => Fin.ext (by
                      have := congrArg Fin.val h; dsimp at this; have := x.isLt; have := y.isLt; omega)⟩
                  have hsum_add : ∀ U : Finset (Fin (1 + d)),
                      (∑ t ∈ U, f1 t) + U.card * a j = ∑ t ∈ U, a (emb t) := by
                    intro U
                    rw [← smul_eq_mul, ← sum_const, ← sum_add_distrib]
                    refine sum_congr rfl fun t _ => ?_
                    have ht := t.isLt
                    have hge : a j ≤ a ⟨j.val - t.val, by omega⟩ :=
                      ha.antitone (Fin.le_iff_val_le_val.mpr (by dsimp; omega))
                    change (a ⟨j.val - t.val, by omega⟩ - a j) + a j = a ⟨j.val - t.val, by omega⟩
                    omega
                  have hEqA : ∑ x ∈ S.map emb, a x = ∑ x ∈ T.map emb, a x := by
                    rw [sum_map, sum_map, ← hsum_add S, ← hsum_add T, hSc, hSs]
                  have hEq := hinj hEqA
                  ext t
                  have : emb t ∈ S.map emb ↔ emb t ∈ T.map emb := by rw [hEq]
                  simpa [mem_map] using this
                · intro x y hxy hlt_d
                  have hx := x.isLt; have hy := y.isLt; have hlev : x.val ≤ y.val := hxy
                  have h1 := ih (y.val - x.val) (by omega) (by omega)
                    ⟨j.val - y.val, by omega⟩ ⟨j.val - x.val, by omega⟩
                    (Fin.le_iff_val_le_val.mpr (by dsimp; omega)) (by dsimp; omega)
                  have hge : a j ≤ a ⟨j.val - x.val, by omega⟩ :=
                    ha.antitone (Fin.le_iff_val_le_val.mpr (by dsimp; omega))
                  dsimp [f1]; omega
                · intro x
                  have hx := x.isLt
                  have hle : a ⟨j.val - x.val, by omega⟩ ≤ a i :=
                    ha.antitone (Fin.le_iff_val_le_val.mpr (by dsimp; omega))
                  dsimp [f1]; omega
              · have hcase2 : f2 ⟨1, by omega⟩ + f2 ⟨1 + d - 2, by omega⟩ ≤ lim := by omega
                refine hrun f2 (by simp [f2]) ?_ hcase2 ?_ ?_ ?_
                · intro x y hxy
                  have hx := x.isLt; have hy := y.isLt; have hltv : x.val < y.val := hxy
                  have hlt1 : a ⟨i.val + y.val, by omega⟩ < a ⟨i.val + x.val, by omega⟩ :=
                    ha (Fin.lt_def.mpr (by dsimp; omega))
                  have hle : a ⟨i.val + x.val, by omega⟩ ≤ a i :=
                    ha.antitone (Fin.le_iff_val_le_val.mpr (by dsimp; omega))
                  dsimp [f2]; omega
                · intro S T hSc hSs
                  let emb : Fin (1 + d) ↪ Fin 9 :=
                    ⟨fun t => ⟨i.val + t.val, by omega⟩, fun x y h => Fin.ext (by
                      have := congrArg Fin.val h; dsimp at this; omega)⟩
                  have hsum_sub : ∀ U : Finset (Fin (1 + d)),
                      (∑ t ∈ U, f2 t) + (∑ t ∈ U, a (emb t)) = U.card * a i := by
                    intro U
                    rw [← smul_eq_mul, ← sum_const, ← sum_add_distrib]
                    refine sum_congr rfl fun t _ => ?_
                    have ht := t.isLt
                    have hle : a ⟨i.val + t.val, by omega⟩ ≤ a i :=
                      ha.antitone (Fin.le_iff_val_le_val.mpr (by dsimp; omega))
                    change (a i - a ⟨i.val + t.val, by omega⟩) + a ⟨i.val + t.val, by omega⟩ = a i
                    omega
                  have hEqA : ∑ x ∈ S.map emb, a x = ∑ x ∈ T.map emb, a x := by
                    rw [sum_map, sum_map]
                    have h1 := hsum_sub S; have h2 := hsum_sub T; rw [hSc] at h1; omega
                  have hEq := hinj hEqA
                  ext t
                  have : emb t ∈ S.map emb ↔ emb t ∈ T.map emb := by rw [hEq]
                  simpa [mem_map] using this
                · intro x y hxy hlt_d
                  have hx := x.isLt; have hy := y.isLt; have hlev : x.val ≤ y.val := hxy
                  have h1 := ih (y.val - x.val) (by omega) (by omega)
                    ⟨i.val + x.val, by omega⟩ ⟨i.val + y.val, by omega⟩
                    (Fin.le_iff_val_le_val.mpr (by dsimp; omega)) (by dsimp; omega)
                  have hle : a ⟨i.val + x.val, by omega⟩ ≤ a i :=
                    ha.antitone (Fin.le_iff_val_le_val.mpr (by dsimp; omega))
                  dsimp [f2]; omega
                · intro x
                  have hx := x.isLt
                  have hge : a j ≤ a ⟨i.val + x.val, by omega⟩ :=
                    ha.antitone (Fin.le_iff_val_le_val.mpr (by dsimp; omega))
                  dsimp [f2]; omega
  intro i j hij hd
  exact hstep (j.val - i.val) hd i j hij rfl

private lemma a_upper_bounds {a : Fin 9 → ℕ} (ha : StrictAnti a)
    (hinj : Function.Injective (fun U : Finset (Fin 9) => ∑ i ∈ U, a i)) :
    a 1 + 1 ≤ a 0 ∧ a 2 + 2 ≤ a 0 ∧ a 3 + 4 ≤ a 0 ∧ a 4 + 7 ≤ a 0 ∧
    a 5 + 13 ≤ a 0 ∧ a 6 + 22 ≤ a 0 ∧ a 7 + 23 ≤ a 0 ∧ a 8 + 24 ≤ a 0 := by
  have hgap := a_gap_g6 ha hinj
  have h1 := hgap 0 1 (by decide) (by decide)
  have h2 := hgap 0 2 (by decide) (by decide)
  have h3 := hgap 0 3 (by decide) (by decide)
  have h4 := hgap 0 4 (by decide) (by decide)
  have h5 := hgap 0 5 (by decide) (by decide)
  have h6 := hgap 0 6 (by decide) (by decide)
  have h7 : a 7 < a 6 := ha (by decide)
  have h8 : a 8 < a 7 := ha (by decide)
  norm_num [gBound] at h1 h2 h3 h4 h5 h6
  omega

private lemma sum_le_9a0_sub_146 {a : Fin 9 → ℕ} (ha : StrictAnti a)
    (hinj : Function.Injective (fun U : Finset (Fin 9) => ∑ i ∈ U, a i)) :
    (∑ i : Fin 9, a i) + 146 ≤ 9 * a 0 := by
  have hsp := (five_layer_spans ha hinj).1
  have hub := a_upper_bounds ha hinj
  have hsum : ∑ i : Fin 9, a i = a 0 + a 1 + a 2 + a 3 + a 4 + a 5 + a 6 + a 7 + a 8 := by
    simp [Fin.sum_univ_succ, add_assoc]
  omega

-- 4. Pure-Nat Elkies verifier + checkCertMeta + complete elkies_cert_sound
private def karamataProdAux (p prod : Nat) : List Nat → Nat
  | [] => prod
  | b :: bs =>
    if Nat.beq b 0 then karamataProdAux p prod bs
    else
      let xHi := Nat.div (Nat.add (Nat.mul p b) 99) 100
      let loS := (cosIntervalShift xHi).1
      let lo := Nat.sub loS SCALE
      karamataProdAux p (Nat.div (Nat.mul prod lo) SCALE) bs

private def jensenPowAux (hi : Nat) : Nat → Nat → Nat
  | 0, prod => prod
  | n + 1, prod => jensenPowAux hi n (Nat.div (Nat.add (Nat.mul prod hi) 99999999) SCALE)

private def jensenChi (p j100 : Nat) : Nat :=
  let xLo := Nat.div (Nat.mul p j100) 100
  let hiS := (cosIntervalShift xLo).2
  let hi := Nat.sub hiS SCALE
  let hi' := if Nat.blt SCALE hi then SCALE else hi
  jensenPowAux hi' 9 SCALE

private def calcLhsShift (b100 : List Nat) (j100 : Nat) : List (Nat × Nat × Nat) → Nat → Nat
  | [], acc => Nat.mul 256 acc
  | (p, wp, wn) :: rest, acc =>
    if Nat.blt 0 wp then
      let clo := if Nat.beq p 0 then SCALE else karamataProdAux p SCALE b100
      calcLhsShift b100 j100 rest (Nat.add acc (Nat.mul wp (Nat.add clo SCALE)))
    else if Nat.blt 0 wn then
      let chi := jensenChi p j100
      calcLhsShift b100 j100 rest (Nat.add acc (Nat.mul wn (Nat.sub SCALE chi)))
    else calcLhsShift b100 j100 rest acc

private def evalKHiShift (x : Nat) : List (Nat × Nat × Nat) → Nat → Nat
  | [], acc => acc
  | (p, wp, wn) :: rest, acc =>
    if Nat.beq p 0 then
      let term := if Nat.blt 0 wp then Nat.mul wp (Nat.mul 2 SCALE) else 0
      evalKHiShift x rest (Nat.add acc term)
    else
      let ci := cosIntervalShift (Nat.mul p x)
      let term := if Nat.blt 0 wp then Nat.mul wp ci.2
                  else Nat.mul wn (Nat.sub (Nat.mul 2 SCALE) ci.1)
      evalKHiShift x rest (Nat.add acc term)

private def sumExcessShift (pw : List (Nat × Nat × Nat)) (tauO tauE : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, so, se => (so, se)
  | x + 1, so, se =>
    let kh := evalKHiShift (Nat.add x 1) pw 0
    if Nat.beq (Nat.mod (Nat.add x 1) 2) 1 then
      let so' := if Nat.blt tauO kh then Nat.add so (Nat.sub kh tauO) else so
      sumExcessShift pw tauO tauE x so' se
    else
      let se' := if Nat.blt tauE kh then Nat.add se (Nat.sub kh tauE) else se
      sumExcessShift pw tauO tauE x so se'

private structure ElkiesCertNat where
  M : Nat
  Smax : Nat
  Qprev : Nat
  Qtgt : Nat
  b100 : List Nat
  j100 : Nat
  pw : List (Nat × Nat × Nat)
  tauOS : Nat
  tauES : Nat

private def checkCertNat (c : ElkiesCertNat) : Bool :=
  let lhs := calcLhsShift c.b100 c.j100 c.pw 0
  let (so, se) := sumExcessShift c.pw c.tauOS c.tauES c.Smax (Nat.mul 256 c.tauOS) (Nat.mul 256 c.tauES)
  and (Nat.blt so lhs) (Nat.blt se lhs)

private def listAnti : List Nat → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => and (Nat.ble y x) (listAnti (y :: rest))

private def checkMajAux (Qtgt : Nat) : List Nat → List Nat → Nat → Nat → Bool
  | [], [], _, _ => true
  | u :: us, b :: bs, su, sb =>
    let su' := Nat.add su (Nat.mul (Nat.mul 100 u) (Nat.mul 100 u))
    let sb' := Nat.add sb (Nat.mul b b)
    if or (Nat.ble su' sb') (Nat.ble (Nat.mul 10000 Qtgt) sb') then
      checkMajAux Qtgt us bs su' sb'
    else false
  | _, _, _, _ => false

private def checkPwMeta (M Smax : Nat) : List (Nat × Nat × Nat) → Bool
  | [] => true
  | (p, wp, wn) :: rest =>
    and (or (Nat.beq wp 0) (Nat.beq wn 0))
    (and (or (not (Nat.beq p 0)) (Nat.beq wn 0))
    (and (Nat.ble (Nat.mul p Smax) 1350000000)
    (and (Nat.blt (Nat.mul p M) PI2_LO)
         (checkPwMeta M Smax rest))))

private def checkCertMeta (c : ElkiesCertNat) : Bool :=
  let uList := [c.M, c.M - 1, c.M - 2, c.M - 4, c.M - 7, c.M - 13, c.M - 22, c.M - 23, c.M - 24]
  and (Nat.beq c.b100.length 9)
  (and (Nat.ble 24 c.M)
  (and (Nat.ble (Nat.sub (Nat.mul 9 c.M) 146) c.Smax)
  (and (Nat.ble c.j100 (Nat.mul 100 c.M))
  (and (Nat.ble (Nat.mul 9 (Nat.mul c.j100 c.j100)) (Nat.mul 10000 c.Qprev))
  (and (listAnti c.b100)
  (and (Nat.ble (c.b100.getD 0 0) (Nat.mul 100 c.M))
  (and (checkMajAux c.Qtgt uList c.b100 0 0)
       (checkPwMeta c.M c.Smax c.pw))))))))

private lemma list_prod_fin9 (l : List ℕ) (hl : l.length = 9) (f : ℕ → ℝ) :
    (l.map f).prod = ∏ i : Fin 9, f (l.getD i.val 0) := by
  rcases l with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, _ | ⟨x7, _ | ⟨x8, rest⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at hl; done)
  cases rest with
  | cons _ _ => simp at hl
  | nil => simp [Fin.prod_univ_succ]

private lemma listAnti_getD :
    ∀ (l : List ℕ), listAnti l = true → ∀ (i j : ℕ), i ≤ j → j < l.length → l.getD j 0 ≤ l.getD i 0 := by
  intro l
  induction l with
  | nil => intro _ _ j _ hj; simp at hj
  | cons x xs ih =>
    cases xs with
    | nil =>
      intro _ i j hij hj
      simp only [List.length_singleton] at hj
      have : i = 0 := by omega
      have : j = 0 := by omega
      subst_vars; exact le_rfl
    | cons y ys =>
      intro hla i j hij hj
      simp only [listAnti, Bool.and_eq_true] at hla
      have hyx : y ≤ x := Nat.le_of_ble_eq_true hla.1
      cases i with
      | zero =>
        cases j with
        | zero => exact le_rfl
        | succ j' =>
          have hj' : j' < (y :: ys).length := by simp only [List.length_cons] at hj ⊢; omega
          have h1 := ih hla.2 0 j' (Nat.zero_le _) hj'
          simp only [List.getD_cons_zero, List.getD_cons_succ] at h1 ⊢
          exact le_trans h1 hyx
      | succ i' =>
        cases j with
        | zero => omega
        | succ j' =>
          have hj' : j' < (y :: ys).length := by simp only [List.length_cons] at hj ⊢; omega
          exact ih hla.2 i' j' (by omega) hj'

private lemma karamataProdAux_sound {p M : ℕ} (hpM : p * M < PI2_LO) :
    ∀ (bs : List ℕ) (prod : ℕ),
      (∀ b ∈ bs, b ≤ 100 * M) →
      ((karamataProdAux p prod bs : ℕ) : ℝ) ≤
        (prod : ℝ) * (bs.map fun (b : ℕ) => Real.cos (((p : ℝ) / (SCALE : ℝ)) * ((b : ℝ) / 100))).prod := by
  intro bs
  induction bs with
  | nil => intro prod _; simp [karamataProdAux]
  | cons b bs ih =>
    intro prod hle
    have hbM : b ≤ 100 * M := hle b List.mem_cons_self
    have hbsM : ∀ x ∈ bs, x ≤ 100 * M := fun x hx => hle x (List.mem_cons_of_mem b hx)
    unfold karamataProdAux
    by_cases hb0 : b = 0
    · subst hb0
      simp only [Nat.beq_refl, ite_true, List.map_cons, List.prod_cons, Nat.cast_zero, zero_div, mul_zero, Real.cos_zero, one_mul]
      exact ih prod hbsM
    · have hbeq : Nat.beq b 0 = false := beq_false_of_ne hb0
      simp only [hbeq, Bool.false_eq_true, ite_false, List.map_cons, List.prod_cons]
      let xHi := (p * b + 99) / 100
      let loS := (cosIntervalShift xHi).1
      let lo := loS - SCALE
      have hxHi_lt : xHi < PI2_LO := by
        dsimp [xHi, PI2_LO] at hpM ⊢
        have h1 : p * b ≤ p * (100 * M) := Nat.mul_le_mul_left p hbM
        have h2 : p * (100 * M) = 100 * (p * M) := by ring
        omega
      have hxHi_le : xHi ≤ 1350000000 := by dsimp [PI2_LO] at hxHi_lt; omega
      have hSpos : (0 : ℝ) < (SCALE : ℝ) := by norm_num [SCALE]
      have hpi2 : (PI2_LO : ℝ) / (SCALE : ℝ) < Real.pi / 2 := by
        have := Real.pi_gt_d20; norm_num [PI2_LO, SCALE]; linarith
      have hx_le_xHi : ((p : ℝ) / (SCALE : ℝ)) * ((b : ℝ) / 100) ≤ (xHi : ℝ) / (SCALE : ℝ) := by
        have hnat : p * b ≤ xHi * 100 := by dsimp [xHi]; omega
        have hR : (p : ℝ) * (b : ℝ) ≤ (xHi : ℝ) * 100 := by exact_mod_cast hnat
        rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hSpos]
        nlinarith
      have hxHi_pi : (xHi : ℝ) / (SCALE : ℝ) < Real.pi / 2 := by
        have hlt : (xHi : ℝ) < (PI2_LO : ℝ) := by exact_mod_cast hxHi_lt
        have : (xHi : ℝ) / (SCALE : ℝ) < (PI2_LO : ℝ) / (SCALE : ℝ) := div_lt_div_of_pos_right hlt hSpos
        linarith
      have hcos_pos : 0 < Real.cos ((xHi : ℝ) / (SCALE : ℝ)) :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, div_nonneg (Nat.cast_nonneg xHi) (le_of_lt hSpos)], hxHi_pi⟩
      have hcos_mono : Real.cos ((xHi : ℝ) / (SCALE : ℝ)) ≤ Real.cos (((p : ℝ) / (SCALE : ℝ)) * ((b : ℝ) / 100)) :=
        Real.strictAntiOn_cos.antitoneOn
          ⟨by positivity, by linarith [Real.pi_pos]⟩
          ⟨div_nonneg (Nat.cast_nonneg xHi) (le_of_lt hSpos), by linarith [Real.pi_pos]⟩
          hx_le_xHi
      have hci := (cosIntervalShift_sound xHi hxHi_le).1
      have hlo_le : (lo : ℝ) ≤ Real.cos (((p : ℝ) / (SCALE : ℝ)) * ((b : ℝ) / 100)) * (SCALE : ℝ) := by
        dsimp [lo, loS]
        by_cases hge : SCALE ≤ (cosIntervalShift xHi).1
        · rw [Nat.cast_sub hge]; nlinarith
        · rw [Nat.sub_eq_zero_of_le (le_of_not_ge hge), Nat.cast_zero]; nlinarith
      have hstep : (((prod * lo) / SCALE : ℕ) : ℝ) ≤
          (prod : ℝ) * Real.cos (((p : ℝ) / (SCALE : ℝ)) * ((b : ℝ) / 100)) := by
        have hdiv : (((prod * lo) / SCALE : ℕ) : ℝ) * (SCALE : ℝ) ≤ (prod : ℝ) * (lo : ℝ) := by
          exact_mod_cast Nat.div_mul_le_self (prod * lo) SCALE
        nlinarith [Nat.cast_nonneg (α := ℝ) prod]
      have hprod_nonneg : 0 ≤ (bs.map fun (x : ℕ) => Real.cos (((p : ℝ) / (SCALE : ℝ)) * ((x : ℝ) / 100))).prod := by
        apply List.prod_nonneg
        intro y hy
        rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
        have hxM : x ≤ 100 * M := hbsM x hx
        have harg0 : (0 : ℝ) ≤ ((p : ℝ) / (SCALE : ℝ)) * ((x : ℝ) / 100) := by positivity
        have hxlt : ((p : ℝ) / (SCALE : ℝ)) * ((x : ℝ) / 100) < Real.pi / 2 := by
          have h1 : p * x ≤ 100 * (p * M) := by
            have := Nat.mul_le_mul_left p hxM; linarith
          have h1R : (p : ℝ) * (x : ℝ) ≤ 100 * ((p * M : ℕ) : ℝ) := by exact_mod_cast h1
          have h2 : ((p * M : ℕ) : ℝ) < (PI2_LO : ℝ) := by exact_mod_cast hpM
          have h3 : ((p : ℝ) / (SCALE : ℝ)) * ((x : ℝ) / 100) ≤ ((p * M : ℕ) : ℝ) / (SCALE : ℝ) := by
            rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hSpos]; nlinarith
          have h4 : ((p * M : ℕ) : ℝ) / (SCALE : ℝ) < (PI2_LO : ℝ) / (SCALE : ℝ) :=
            div_lt_div_of_pos_right h2 hSpos
          linarith
        exact le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hxlt⟩)
      have hih := ih ((prod * lo) / SCALE) hbsM
      change ((karamataProdAux p ((prod * lo) / SCALE) bs : ℕ) : ℝ) ≤ _
      calc ((karamataProdAux p ((prod * lo) / SCALE) bs : ℕ) : ℝ)
          ≤ (((prod * lo) / SCALE : ℕ) : ℝ) *
              (bs.map fun (x : ℕ) => Real.cos (((p : ℝ) / (SCALE : ℝ)) * ((x : ℝ) / 100))).prod := hih
        _ ≤ ((prod : ℝ) * Real.cos (((p : ℝ) / (SCALE : ℝ)) * ((b : ℝ) / 100))) *
              (bs.map fun (x : ℕ) => Real.cos (((p : ℝ) / (SCALE : ℝ)) * ((x : ℝ) / 100))).prod :=
            mul_le_mul_of_nonneg_right hstep hprod_nonneg
        _ = _ := by ring

private lemma jensenPowAux_sound {hi : ℕ} (hhi : hi ≤ SCALE) {c : ℝ} (hc0 : 0 ≤ c) (hc : c * (SCALE : ℝ) ≤ (hi : ℝ)) :
    ∀ (n prod : ℕ) (p0 : ℝ), 0 ≤ p0 → p0 ≤ (prod : ℝ) → prod ≤ SCALE →
      p0 * c ^ n ≤ (jensenPowAux hi n prod : ℝ) ∧ jensenPowAux hi n prod ≤ SCALE := by
  intro n
  induction n with
  | zero => intro prod p0 _ hp hS; change p0 * c ^ 0 ≤ (prod : ℝ) ∧ prod ≤ SCALE; rw [pow_zero, mul_one]; exact ⟨hp, hS⟩
  | succ n ih =>
    intro prod p0 hp0 hp hS
    unfold jensenPowAux
    let prod' := Nat.div (Nat.add (Nat.mul prod hi) 99999999) SCALE
    have hprod'_eq : prod' = (prod * hi + 99999999) / SCALE := by
      dsimp only [prod']; rw [nat_div_eq, nat_add_eq, nat_mul_eq]
    have hprod'_le : prod' ≤ SCALE := by
      have hlt : prod' < SCALE + 1 := by
        rw [hprod'_eq]
        refine Nat.div_lt_of_lt_mul ?_
        have h1 : prod * hi ≤ SCALE * SCALE := Nat.mul_le_mul hS hhi
        have h2 : SCALE * (SCALE + 1) = SCALE * SCALE + SCALE := by ring
        have h3 : 99999999 < SCALE := by norm_num [SCALE]
        omega
      omega
    have hprod'_ge : p0 * c ≤ (prod' : ℝ) := by
      have hSpos : (0 : ℝ) < (SCALE : ℝ) := by norm_num [SCALE]
      have hceil : prod * hi ≤ prod' * SCALE := by
        rw [hprod'_eq]
        have hdm := Nat.div_add_mod (prod * hi + 99999999) SCALE
        have hml := Nat.mod_lt (prod * hi + 99999999) (by norm_num [SCALE] : 0 < SCALE)
        dsimp [SCALE] at hdm hml ⊢; linarith
      have hceilR : (prod : ℝ) * (hi : ℝ) ≤ (prod' : ℝ) * (SCALE : ℝ) := by exact_mod_cast hceil
      have h1 : p0 * (c * (SCALE : ℝ)) ≤ (prod : ℝ) * (hi : ℝ) :=
        mul_le_mul hp hc (mul_nonneg hc0 (le_of_lt hSpos)) (Nat.cast_nonneg prod)
      nlinarith
    have hrec := ih prod' (p0 * c) (mul_nonneg hp0 hc0) hprod'_ge hprod'_le
    rw [pow_succ, ← mul_assoc, mul_comm (p0 * c ^ n) c]
    have heq : c * (p0 * c ^ n) = (p0 * c) * c ^ n := by ring
    rw [heq]; exact hrec

private lemma jensenChi_sound {p M j100 : ℕ} (hpM : p * M < PI2_LO) (hjM : j100 ≤ 100 * M) :
    (Real.cos (((p : ℝ) / (SCALE : ℝ)) * ((j100 : ℝ) / 100))) ^ 9 * (SCALE : ℝ) ≤ (jensenChi p j100 : ℝ) ∧
    jensenChi p j100 ≤ SCALE := by
  unfold jensenChi
  let xLo := (p * j100) / 100
  let hiS := (cosIntervalShift xLo).2
  let hi := hiS - SCALE
  let hi' := if Nat.blt SCALE hi then SCALE else hi
  have hxLo_lt : xLo < PI2_LO := by
    dsimp [xLo, PI2_LO] at hpM ⊢
    have h1 : p * j100 ≤ p * (100 * M) := Nat.mul_le_mul_left p hjM
    have h2 : p * (100 * M) = 100 * (p * M) := by ring
    omega
  have hxLo_le : xLo ≤ 1350000000 := by dsimp [PI2_LO] at hxLo_lt; omega
  have hSpos : (0 : ℝ) < (SCALE : ℝ) := by norm_num [SCALE]
  have hpi2 : (PI2_LO : ℝ) / (SCALE : ℝ) < Real.pi / 2 := by
    have := Real.pi_gt_d20; norm_num [PI2_LO, SCALE]; linarith
  have hx_lt_pi : ((p : ℝ) / (SCALE : ℝ)) * ((j100 : ℝ) / 100) < Real.pi / 2 := by
    have h1 : p * j100 ≤ 100 * (p * M) := by have := Nat.mul_le_mul_left p hjM; linarith
    have h1R : (p : ℝ) * (j100 : ℝ) ≤ 100 * ((p * M : ℕ) : ℝ) := by exact_mod_cast h1
    have h2 : ((p * M : ℕ) : ℝ) < (PI2_LO : ℝ) := by exact_mod_cast hpM
    have h3 : ((p : ℝ) / (SCALE : ℝ)) * ((j100 : ℝ) / 100) ≤ ((p * M : ℕ) : ℝ) / (SCALE : ℝ) := by
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hSpos]; nlinarith
    have h4 : ((p * M : ℕ) : ℝ) / (SCALE : ℝ) < (PI2_LO : ℝ) / (SCALE : ℝ) :=
      div_lt_div_of_pos_right h2 hSpos
    linarith
  have hxLo_le_x : (xLo : ℝ) / (SCALE : ℝ) ≤ ((p : ℝ) / (SCALE : ℝ)) * ((j100 : ℝ) / 100) := by
    have hnat : xLo * 100 ≤ p * j100 := Nat.div_mul_le_self _ _
    have hR : (xLo : ℝ) * 100 ≤ (p : ℝ) * (j100 : ℝ) := by exact_mod_cast hnat
    rw [div_mul_div_comm, div_le_div_iff₀ hSpos (by positivity)]
    nlinarith
  have hcos_pos : 0 < Real.cos (((p : ℝ) / (SCALE : ℝ)) * ((j100 : ℝ) / 100)) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, show (0 : ℝ) ≤ ((p : ℝ) / (SCALE : ℝ)) * ((j100 : ℝ) / 100) by positivity], hx_lt_pi⟩
  have hcos_le : Real.cos (((p : ℝ) / (SCALE : ℝ)) * ((j100 : ℝ) / 100)) ≤ Real.cos ((xLo : ℝ) / (SCALE : ℝ)) :=
    Real.strictAntiOn_cos.antitoneOn
      ⟨div_nonneg (Nat.cast_nonneg xLo) (le_of_lt hSpos), by linarith [Real.pi_pos]⟩
      ⟨by positivity, by linarith [Real.pi_pos]⟩
      hxLo_le_x
  have hci := (cosIntervalShift_sound xLo hxLo_le).2
  have hhi'_le : hi' ≤ SCALE := by
    dsimp [hi']; split_ifs with h
    · exact le_rfl
    · exact Nat.le_of_not_lt (fun hgt => h (Nat.blt_eq.mpr hgt))
  have hcos_le_hi' : Real.cos (((p : ℝ) / (SCALE : ℝ)) * ((j100 : ℝ) / 100)) * (SCALE : ℝ) ≤ (hi' : ℝ) := by
    dsimp [hi']
    split_ifs with h
    · have h1 := Real.cos_le_one (((p : ℝ) / (SCALE : ℝ)) * ((j100 : ℝ) / 100))
      have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hSpos)
      linarith
    · have hS_le_hiS : SCALE ≤ hiS := by
        have h1 : (Real.cos ((xLo : ℝ) / (SCALE : ℝ)) + 1) * (SCALE : ℝ) ≤ (hiS : ℝ) := hci
        have h0c : 0 ≤ Real.cos ((xLo : ℝ) / (SCALE : ℝ)) := le_trans (le_of_lt hcos_pos) hcos_le
        have h2 : (1 : ℝ) * (SCALE : ℝ) ≤ (Real.cos ((xLo : ℝ) / (SCALE : ℝ)) + 1) * (SCALE : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hSpos)
        have h3 : (SCALE : ℝ) ≤ (hiS : ℝ) := by linarith
        exact_mod_cast h3
      have hsub : (hi : ℝ) = (hiS : ℝ) - (SCALE : ℝ) := by dsimp [hi]; exact Nat.cast_sub hS_le_hiS
      rw [hsub]
      have h1 : (Real.cos ((xLo : ℝ) / (SCALE : ℝ)) + 1) * (SCALE : ℝ) ≤ (hiS : ℝ) := hci
      have h2 : Real.cos (((p : ℝ) / (SCALE : ℝ)) * ((j100 : ℝ) / 100)) * (SCALE : ℝ) ≤
          Real.cos ((xLo : ℝ) / (SCALE : ℝ)) * (SCALE : ℝ) :=
        mul_le_mul_of_nonneg_right hcos_le (le_of_lt hSpos)
      linarith
  have hres := jensenPowAux_sound hhi'_le (le_of_lt hcos_pos) hcos_le_hi' 9 SCALE (SCALE : ℝ) (le_of_lt hSpos) le_rfl le_rfl
  change _ ≤ (jensenPowAux hi' 9 SCALE : ℝ) ∧ jensenPowAux hi' 9 SCALE ≤ SCALE
  simpa [mul_comm (SCALE : ℝ)] using hres

private noncomputable def evalKReal (pw : List (Nat × Nat × Nat)) (x : ℝ) : ℝ :=
  (pw.map fun e =>
    let t := (e.1 : ℝ) / (SCALE : ℝ)
    (e.2.1 : ℝ) * (Real.cos (t * x) + 1) + (e.2.2 : ℝ) * (1 - Real.cos (t * x))).sum

private noncomputable def evalProdReal (pw : List (Nat × Nat × Nat)) (a : Fin 9 → ℕ) : ℝ :=
  (pw.map fun e =>
    let t := (e.1 : ℝ) / (SCALE : ℝ)
    let pr := ∏ i : Fin 9, Real.cos (t * (a i : ℝ))
    (e.2.1 : ℝ) * (pr + 1) + (e.2.2 : ℝ) * (1 - pr)).sum

private lemma evalKHiTerm_pos_le {p wp wn x : ℕ} {ci : ℕ × ℕ}
    (hdisj : wp = 0 ∨ wn = 0)
    (hci1 : (ci.1 : ℝ) ≤ (Real.cos (((p : ℝ) / (SCALE : ℝ)) * (x : ℝ)) + 1) * (SCALE : ℝ))
    (hci2 : (Real.cos (((p : ℝ) / (SCALE : ℝ)) * (x : ℝ)) + 1) * (SCALE : ℝ) ≤ (ci.2 : ℝ)) :
    ((wp : ℝ) * (Real.cos (((p : ℝ) / (SCALE : ℝ)) * (x : ℝ)) + 1) +
      (wn : ℝ) * (1 - Real.cos (((p : ℝ) / (SCALE : ℝ)) * (x : ℝ)))) * (SCALE : ℝ) ≤
      ((if Nat.blt 0 wp then Nat.mul wp ci.2
        else Nat.mul wn (Nat.sub (Nat.mul 2 SCALE) ci.1) : ℕ) : ℝ) := by
  by_cases hwp : 0 < wp
  · have hwn0 : wn = 0 := by rcases hdisj with h | h <;> omega
    subst hwn0
    simp only [Nat.blt_eq.mpr hwp, ite_true, Nat.cast_zero, zero_mul, add_zero]
    rw [nat_mul_eq, Nat.cast_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hci2 (Nat.cast_nonneg wp)
  · have hwp0 : wp = 0 := by omega
    subst hwp0
    simp only [show Nat.blt 0 0 = false from rfl, Bool.false_eq_true, ite_false, Nat.cast_zero, zero_mul, zero_add]
    have hsub : (2 : ℝ) * (SCALE : ℝ) - (ci.1 : ℝ) ≤ ((2 * SCALE - ci.1 : ℕ) : ℝ) := by
      by_cases hle : ci.1 ≤ 2 * SCALE
      · rw [Nat.cast_sub hle, Nat.cast_mul, Nat.cast_ofNat]
      · have hlt : (2 : ℝ) * (SCALE : ℝ) < (ci.1 : ℝ) := by
          have : 2 * SCALE < ci.1 := by omega
          have hR : ((2 * SCALE : ℕ) : ℝ) < (ci.1 : ℝ) := Nat.cast_lt.mpr this
          rwa [Nat.cast_mul, Nat.cast_ofNat] at hR
        linarith only [hlt, Nat.cast_nonneg (α := ℝ) (2 * SCALE - ci.1)]
    have h1 : (1 - Real.cos (((p : ℝ) / (SCALE : ℝ)) * (x : ℝ))) * (SCALE : ℝ) ≤
        ((2 * SCALE - ci.1 : ℕ) : ℝ) := by
      linarith only [hci1, hsub]
    rw [nat_mul_eq, nat_sub_eq, nat_mul_eq, Nat.cast_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg wn)

private lemma evalKHiShift_sound {M Smax x : ℕ} (hx : x ≤ Smax) :
    ∀ (pw : List (Nat × Nat × Nat)) (acc : ℕ),
      checkPwMeta M Smax pw = true →
      (acc : ℝ) + evalKReal pw (x : ℝ) * (SCALE : ℝ) ≤ (evalKHiShift x pw acc : ℝ) := by
  intro pw
  induction pw with
  | nil => intro acc _; simp [evalKReal, evalKHiShift]
  | cons e rest ih =>
    rcases e with ⟨p, wp, wn⟩
    intro acc hmeta
    simp only [checkPwMeta, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hmeta
    rcases hmeta with ⟨hdisj, h0wn, hpS, hpM, hrest⟩
    have hpSx : p * x ≤ 1350000000 :=
      le_trans (Nat.mul_le_mul_left p hx) (Nat.le_of_ble_eq_true hpS)
    have hdisj' : wp = 0 ∨ wn = 0 := by
      rcases hdisj with h | h
      · left; exact Nat.eq_of_beq_eq_true h
      · right; exact Nat.eq_of_beq_eq_true h
    unfold evalKHiShift evalKReal
    simp only [List.map_cons, List.sum_cons, add_mul]
    by_cases hp0 : p = 0
    · subst hp0
      have hwn0 : wn = 0 := by
        rcases h0wn with h | h
        · simp at h
        · exact Nat.eq_of_beq_eq_true h
      subst hwn0
      simp only [Nat.beq_refl, ite_true, Nat.cast_zero, zero_div, zero_mul, Real.cos_zero]
      set term := if Nat.blt 0 wp then Nat.mul wp (Nat.mul 2 SCALE) else 0
      have hterm : ((wp : ℝ) * (1 + 1)) * (SCALE : ℝ) ≤ (term : ℝ) := by
        dsimp only [term]
        by_cases hwp : 0 < wp
        · simp only [Nat.blt_eq.mpr hwp, ite_true]
          rw [nat_mul_eq, nat_mul_eq]
          push_cast; linarith
        · have : wp = 0 := by omega
          subst this; simp
      clear_value term
      have hih := ih (Nat.add acc term) hrest
      unfold evalKReal at hih
      have hcast : ((Nat.add acc term : ℕ) : ℝ) = (acc : ℝ) + (term : ℝ) := by rw [nat_add_eq]; push_cast; rfl
      rw [hcast] at hih
      exact le_trans (by linarith only [hterm]) hih
    · have hpbeq : Nat.beq p 0 = false := beq_false_of_ne hp0
      simp only [hpbeq, Bool.false_eq_true, ite_false]
      have hci := cosIntervalShift_sound (Nat.mul p x) (by rw [nat_mul_eq]; exact hpSx)
      have harg : ((Nat.mul p x : ℕ) : ℝ) / (SCALE : ℝ) = ((p : ℝ) / (SCALE : ℝ)) * (x : ℝ) := by
        rw [nat_mul_eq]; push_cast; ring
      rw [harg] at hci
      generalize cosIntervalShift (Nat.mul p x) = ci at hci ⊢
      set term := if Nat.blt 0 wp then Nat.mul wp ci.2
                  else Nat.mul wn (Nat.sub (Nat.mul 2 SCALE) ci.1)
      have hterm : ((wp : ℝ) * (Real.cos (((p : ℝ) / (SCALE : ℝ)) * (x : ℝ)) + 1) +
          (wn : ℝ) * (1 - Real.cos (((p : ℝ) / (SCALE : ℝ)) * (x : ℝ)))) * (SCALE : ℝ) ≤ (term : ℝ) :=
        evalKHiTerm_pos_le hdisj' hci.1 hci.2
      clear_value term
      have hih := ih (Nat.add acc term) hrest
      unfold evalKReal at hih
      have hcast : ((Nat.add acc term : ℕ) : ℝ) = (acc : ℝ) + (term : ℝ) := by rw [nat_add_eq]; push_cast; rfl
      rw [hcast] at hih
      exact le_trans (by linarith only [hterm]) hih

private lemma sumExcessShift_eq (pw : List (Nat × Nat × Nat)) (tauO tauE : ℕ) :
    ∀ (n so se : ℕ),
      (sumExcessShift pw tauO tauE n so se).1 =
        so + ∑ x ∈ (Icc 1 n).filter (fun x => x % 2 = 1), (evalKHiShift x pw 0 - tauO) ∧
      (sumExcessShift pw tauO tauE n so se).2 =
        se + ∑ x ∈ (Icc 1 n).filter (fun x => x % 2 = 0), (evalKHiShift x pw 0 - tauE) := by
  intro n
  induction n with
  | zero => intro so se; simp [sumExcessShift]
  | succ n ih =>
    intro so se
    unfold sumExcessShift
    have hsplit : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    have hnot : n + 1 ∉ Icc 1 n := by simp [mem_Icc]
    have hsub_if : ∀ a b : ℕ, (if Nat.blt b a then Nat.add so (Nat.sub a b) else so) = so + (a - b) := by
      intro a b
      by_cases h : b < a
      · simp [Nat.blt_eq.mpr h]
      · simp [blt_false_of_le (by omega : a ≤ b), Nat.sub_eq_zero_of_le (by omega : a ≤ b)]
    have hsub_if2 : ∀ a b : ℕ, (if Nat.blt b a then Nat.add se (Nat.sub a b) else se) = se + (a - b) := by
      intro a b
      by_cases h : b < a
      · simp [Nat.blt_eq.mpr h]
      · simp [blt_false_of_le (by omega : a ≤ b), Nat.sub_eq_zero_of_le (by omega : a ≤ b)]
    have hn1 : Nat.add n 1 = n + 1 := rfl
    by_cases hpar : (n + 1) % 2 = 1
    · have hbeq : Nat.beq (Nat.mod (Nat.add n 1) 2) 1 = true := by
        rw [hn1]; change Nat.beq ((n + 1) % 2) 1 = true; rw [hpar]; rfl
      simp only [hbeq, ite_true]
      obtain ⟨h1, h2⟩ := ih (if Nat.blt tauO (evalKHiShift (Nat.add n 1) pw 0) then Nat.add so (Nat.sub (evalKHiShift (Nat.add n 1) pw 0) tauO) else so) se
      rw [hsplit, filter_insert, filter_insert, if_pos hpar, if_neg (by omega : ¬ ((n + 1) % 2 = 0)),
          sum_insert (fun hm => hnot (mem_filter.mp hm).1)]
      rw [h1, h2, hsub_if, hn1]
      exact ⟨by omega, rfl⟩
    · have hpar0 : (n + 1) % 2 = 0 := by omega
      have hbeq : Nat.beq (Nat.mod (Nat.add n 1) 2) 1 = false := by
        rw [hn1]; change Nat.beq ((n + 1) % 2) 1 = false; rw [hpar0]; rfl
      simp only [hbeq, Bool.false_eq_true, ite_false]
      obtain ⟨h1, h2⟩ := ih so (if Nat.blt tauE (evalKHiShift (Nat.add n 1) pw 0) then Nat.add se (Nat.sub (evalKHiShift (Nat.add n 1) pw 0) tauE) else se)
      rw [hsplit, filter_insert, filter_insert, if_neg hpar, if_pos hpar0,
          sum_insert (fun hm => hnot (mem_filter.mp hm).1)]
      rw [h1, h2, hsub_if2, hn1]
      exact ⟨rfl, by omega⟩

private lemma elkies_cert_sound (c : ElkiesCertNat) (hmeta : checkCertMeta c = true) (hcert : checkCertNat c = true)
    {a : Fin 9 → ℕ} (ha : StrictAnti a)
    (hinj : Function.Injective (fun U : Finset (Fin 9) => ∑ i ∈ U, a i))
    (ha0 : a 0 ≤ c.M) (hQprev : c.Qprev ≤ ∑ i : Fin 9, a i ^ 2) :
    c.Qtgt < ∑ i : Fin 9, a i ^ 2 := by
  by_contra hQle
  push Not at hQle
  simp only [checkCertMeta, Bool.and_eq_true] at hmeta
  rcases hmeta with ⟨hblen, hM24, hSmax, hjM, hjQ, hbanti, hb0, hmaj, hpw⟩
  have hblen' : c.b100.length = 9 := Nat.eq_of_beq_eq_true hblen
  have hM24' : 24 ≤ c.M := Nat.le_of_ble_eq_true hM24
  have hSmax' : 9 * c.M - 146 ≤ c.Smax := Nat.le_of_ble_eq_true hSmax
  have hjM' : c.j100 ≤ 100 * c.M := Nat.le_of_ble_eq_true hjM
  have hjQ' : 9 * (c.j100 * c.j100) ≤ 10000 * c.Qprev := Nat.le_of_ble_eq_true hjQ
  have hb0' : c.b100.getD 0 0 ≤ 100 * c.M := Nat.le_of_ble_eq_true hb0
  have hS_le : ∑ i : Fin 9, a i ≤ c.Smax := by
    have := sum_le_9a0_sub_146 ha hinj; omega
  let b : Fin 9 → ℝ := fun i => ((c.b100.getD i.val 0 : ℕ) : ℝ) / 100
  have hb_anti_nat : ∀ i j : Fin 9, i ≤ j → c.b100.getD j.val 0 ≤ c.b100.getD i.val 0 := fun i j hij =>
    listAnti_getD c.b100 hbanti i.val j.val hij (by omega)
  have hb_le_M : ∀ x ∈ c.b100, x ≤ 100 * c.M := by
    intro x hx
    rcases List.getElem_of_mem hx with ⟨k, hk, rfl⟩
    have h1 : c.b100[k]'hk = c.b100.getD k 0 := (List.getD_eq_getElem c.b100 0 hk).symm
    rw [h1]
    exact le_trans (listAnti_getD c.b100 hbanti 0 k (Nat.zero_le k) hk) hb0'
  have hb_anti : Antitone b := fun i j hij => by
    dsimp [b]; exact div_le_div_of_nonneg_right (by exact_mod_cast hb_anti_nat i j hij) (by norm_num)
  have hbM : ∀ i : Fin 9, b i ≤ (c.M : ℝ) := fun i => by
    dsimp [b]
    have h1 : c.b100.getD i.val 0 ≤ 100 * c.M :=
      le_trans (listAnti_getD c.b100 hbanti 0 i.val (Nat.zero_le _) (by omega)) hb0'
    have h2 : ((c.b100.getD i.val 0 : ℕ) : ℝ) ≤ 100 * (c.M : ℝ) := by exact_mod_cast h1
    linarith
  have hmaj_R : ∀ k : Fin 9,
      ∑ i ∈ univ.filter (fun j : Fin 9 => j.val ≤ k.val), (a i : ℝ) ^ 2 ≤
      ∑ i ∈ univ.filter (fun j : Fin 9 => j.val ≤ k.val), (b i) ^ 2 := by
    let uL : List ℕ := [c.M, c.M - 1, c.M - 2, c.M - 4, c.M - 7, c.M - 13, c.M - 22, c.M - 23, c.M - 24]
    have ha_le_u : ∀ i : Fin 9, a i ≤ uL.getD i.val 0 := by
      have hub := a_upper_bounds ha hinj
      intro i; fin_cases i <;> (simp [uL]; omega)
    have hmaj_extract : ∀ (us bs : List ℕ) (su sb : ℕ),
        us.length = bs.length → checkMajAux c.Qtgt us bs su sb = true →
        ∀ (m : ℕ), m < us.length →
          su + (∑ i ∈ range (m + 1), (100 * us.getD i 0) ^ 2) ≤ sb + (∑ i ∈ range (m + 1), (bs.getD i 0) ^ 2) ∨
          10000 * c.Qtgt ≤ sb + (∑ i ∈ range (m + 1), (bs.getD i 0) ^ 2) := by
      intro us
      induction us with
      | nil => intro bs _ _ _ _ m hm; simp at hm
      | cons u us ih =>
        intro bs su sb hlen hchk m hm
        cases bs with
        | nil => simp at hlen
        | cons bv bs =>
          unfold checkMajAux at hchk
          dsimp only at hchk
          split_ifs at hchk with hor
          simp only [Bool.or_eq_true] at hor
          have hsq_u : (100 * u) * (100 * u) = (100 * u) ^ 2 := (sq _).symm
          have hsq_b : bv * bv = bv ^ 2 := (sq _).symm
          cases m with
          | zero =>
            rw [range_one, sum_singleton, sum_singleton]
            simp only [List.getD_cons_zero]
            rcases hor with h1 | h2
            · left; have h1' := Nat.le_of_ble_eq_true h1
              change su + (100 * u) * (100 * u) ≤ sb + bv * bv at h1'
              rw [hsq_u, hsq_b] at h1'; exact h1'
            · right; have h2' := Nat.le_of_ble_eq_true h2
              change 10000 * c.Qtgt ≤ sb + bv * bv at h2'
              rw [hsq_b] at h2'; exact h2'
          | succ m' =>
            have hrec := ih bs (Nat.add su (Nat.mul (Nat.mul 100 u) (Nat.mul 100 u))) (Nat.add sb (Nat.mul bv bv))
              (by simp at hlen; omega) hchk m' (by simp at hm; omega)
            have hs1 : ∑ i ∈ range (m' + 1 + 1), (100 * (u :: us).getD i 0) ^ 2 =
                (100 * u) ^ 2 + ∑ i ∈ range (m' + 1), (100 * us.getD i 0) ^ 2 := by
              rw [sum_range_succ']; simp [add_comm]
            have hs2 : ∑ i ∈ range (m' + 1 + 1), ((bv :: bs).getD i 0) ^ 2 =
                bv ^ 2 + ∑ i ∈ range (m' + 1), (bs.getD i 0) ^ 2 := by
              rw [sum_range_succ']; simp [add_comm]
            rw [hs1, hs2]
            rcases hrec with h1 | h2
            · left; change su + (100 * u) * (100 * u) + _ ≤ sb + bv * bv + _ at h1
              rw [hsq_u, hsq_b] at h1; omega
            · right; change 10000 * c.Qtgt ≤ sb + bv * bv + _ at h2
              rw [hsq_b] at h2; omega
    intro k
    have hm := hmaj_extract uL c.b100 0 0 (by simp [uL, hblen']) hmaj k.val (by simp [uL])
    have hsum_b : ∑ i ∈ range (k.val + 1), (c.b100.getD i 0) ^ 2 =
        ∑ i ∈ univ.filter (fun j : Fin 9 => j.val ≤ k.val), (c.b100.getD i.val 0) ^ 2 := by
      refine sum_bij (fun i hi => ⟨i, by have := mem_range.mp hi; omega⟩) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro i hi; rw [mem_filter]; exact ⟨mem_univ _, Nat.lt_succ_iff.mp (mem_range.mp hi)⟩
      · intro _ _ _ _ h; exact congrArg Fin.val h
      · intro j hj; exact ⟨j.val, mem_range.mpr (Nat.lt_succ_iff.mpr (mem_filter.mp hj).2), Fin.ext rfl⟩
    have hsum_u : ∑ i ∈ range (k.val + 1), (100 * uL.getD i 0) ^ 2 =
        ∑ i ∈ univ.filter (fun j : Fin 9 => j.val ≤ k.val), (100 * uL.getD i.val 0) ^ 2 := by
      refine sum_bij (fun i hi => ⟨i, by have := mem_range.mp hi; omega⟩) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro i hi; rw [mem_filter]; exact ⟨mem_univ _, Nat.lt_succ_iff.mp (mem_range.mp hi)⟩
      · intro _ _ _ _ h; exact congrArg Fin.val h
      · intro j hj; exact ⟨j.val, mem_range.mpr (Nat.lt_succ_iff.mpr (mem_filter.mp hj).2), Fin.ext rfl⟩
    rw [zero_add, zero_add, hsum_b, hsum_u] at hm
    have hnat_ineq : 10000 * (∑ i ∈ univ.filter (fun j : Fin 9 => j.val ≤ k.val), a i ^ 2) ≤
        ∑ i ∈ univ.filter (fun j : Fin 9 => j.val ≤ k.val), (c.b100.getD i.val 0) ^ 2 := by
      rcases hm with h1 | h2
      · have hle_au : 10000 * (∑ i ∈ univ.filter (fun j : Fin 9 => j.val ≤ k.val), a i ^ 2) ≤
            ∑ i ∈ univ.filter (fun j : Fin 9 => j.val ≤ k.val), (100 * uL.getD i.val 0) ^ 2 := by
          rw [mul_sum]
          refine sum_le_sum fun i _ => ?_
          have hle := ha_le_u i
          have hsq : a i ^ 2 ≤ (uL.getD i.val 0) ^ 2 := Nat.pow_le_pow_left hle 2
          calc 10000 * a i ^ 2 ≤ 10000 * (uL.getD i.val 0) ^ 2 := Nat.mul_le_mul_left 10000 hsq
            _ = (100 * uL.getD i.val 0) ^ 2 := by ring
        exact le_trans hle_au h1
      · have hsub : ∑ i ∈ univ.filter (fun j : Fin 9 => j.val ≤ k.val), a i ^ 2 ≤ ∑ i : Fin 9, a i ^ 2 :=
          sum_le_sum_of_subset (subset_univ _)
        exact le_trans (Nat.mul_le_mul_left 10000 (le_trans hsub hQle)) h2
    have hR : (10000 : ℝ) * (∑ i ∈ univ.filter (fun j : Fin 9 => j.val ≤ k.val), (a i : ℝ) ^ 2) ≤
        ∑ i ∈ univ.filter (fun j : Fin 9 => j.val ≤ k.val), ((c.b100.getD i.val 0 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast hnat_ineq
    have hdiv : ∑ i ∈ univ.filter (fun j : Fin 9 => j.val ≤ k.val), (b i) ^ 2 =
        (∑ i ∈ univ.filter (fun j : Fin 9 => j.val ≤ k.val), ((c.b100.getD i.val 0 : ℕ) : ℝ) ^ 2) / 10000 := by
      rw [sum_div]; refine sum_congr rfl fun i _ => ?_; dsimp [b]; ring
    rw [hdiv]; linarith
  have hlhs_le : ∀ (pw : List (Nat × Nat × Nat)) (acc : ℕ),
      checkPwMeta c.M c.Smax pw = true →
      (calcLhsShift c.b100 c.j100 pw acc : ℝ) ≤
        256 * ((acc : ℝ) + evalProdReal pw a * (SCALE : ℝ)) := by
    intro pw
    induction pw with
    | nil =>
      intro acc _
      unfold calcLhsShift evalProdReal
      simp only [List.map_nil, List.sum_nil, zero_mul, add_zero]
      rw [nat_mul_eq, Nat.cast_mul, Nat.cast_ofNat]
    | cons e rest ih =>
      rcases e with ⟨p, wp, wn⟩
      intro acc hpm
      simp only [checkPwMeta, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hpm
      rcases hpm with ⟨hdisj, h0wn, hpS, hpM, hrest⟩
      have hpM' : p * c.M < PI2_LO := Nat.blt_eq.mp hpM
      have hSpos : (0 : ℝ) < (SCALE : ℝ) := by norm_num [SCALE]
      have hpi2 : (PI2_LO : ℝ) / (SCALE : ℝ) < Real.pi / 2 := by
        have := Real.pi_gt_d20; norm_num [PI2_LO, SCALE]; linarith
      have htM : ((p : ℝ) / (SCALE : ℝ)) * (c.M : ℝ) < Real.pi / 2 := by
        have h1 : ((p * c.M : ℕ) : ℝ) < (PI2_LO : ℝ) := by exact_mod_cast hpM'
        have h2 : ((p : ℝ) / (SCALE : ℝ)) * (c.M : ℝ) = ((p * c.M : ℕ) : ℝ) / (SCALE : ℝ) := by push_cast; ring
        rw [h2]; linarith only [div_lt_div_of_pos_right h1 hSpos, hpi2]
      have hdisj' : wp = 0 ∨ wn = 0 := by
        rcases hdisj with h | h
        · left; exact Nat.eq_of_beq_eq_true h
        · right; exact Nat.eq_of_beq_eq_true h
      unfold calcLhsShift evalProdReal
      simp only [List.map_cons, List.sum_cons, add_mul]
      by_cases hwp : 0 < wp
      · have hwn0 : wn = 0 := by rcases hdisj' with h | h <;> omega
        subst hwn0
        simp only [Nat.blt_eq.mpr hwp, ite_true, Nat.cast_zero, zero_mul, add_zero]
        have hclo : ((if Nat.beq p 0 then SCALE else karamataProdAux p SCALE c.b100 : ℕ) : ℝ) ≤
            (∏ i : Fin 9, Real.cos (((p : ℝ) / (SCALE : ℝ)) * (a i : ℝ))) * (SCALE : ℝ) := by
          by_cases hp0 : p = 0
          · subst hp0
            simp only [Nat.beq_refl, ite_true, Nat.cast_zero, zero_div, zero_mul, Real.cos_zero, prod_const_one, one_mul, le_refl]
          · have hpbeq : Nat.beq p 0 = false := beq_false_of_ne hp0
            simp only [hpbeq, Bool.false_eq_true, ite_false]
            have hkar1 := karamataProdAux_sound hpM' c.b100 SCALE hb_le_M
            have hlist_prod := list_prod_fin9 c.b100 hblen' (fun (x : ℕ) => Real.cos (((p : ℝ) / (SCALE : ℝ)) * ((x : ℝ) / 100)))
            have hkar2 : ∏ i : Fin 9, Real.cos (((p : ℝ) / (SCALE : ℝ)) * b i) ≤
                ∏ i : Fin 9, Real.cos (((p : ℝ) / (SCALE : ℝ)) * (a i : ℝ)) :=
              karamata_cos_prod (by positivity) (fun i => Nat.cast_nonneg _)
                (fun i => by exact_mod_cast le_trans (ha.antitone (Fin.zero_le i)) ha0)
                (fun i => by dsimp [b]; positivity) hbM
                (fun i j hij => by exact_mod_cast ha.antitone hij) hb_anti htM hmaj_R
            rw [hlist_prod] at hkar1
            have hkar1' : (karamataProdAux p SCALE c.b100 : ℝ) ≤ (SCALE : ℝ) * ∏ i : Fin 9, Real.cos (((p : ℝ) / (SCALE : ℝ)) * b i) := hkar1
            have hmul := mul_le_mul_of_nonneg_left hkar2 (le_of_lt hSpos)
            linarith only [hkar1', hmul]
        generalize (if Nat.beq p 0 then SCALE else karamataProdAux p SCALE c.b100) = clo at hclo ⊢
        have hih := ih (Nat.add acc (Nat.mul wp (Nat.add clo SCALE))) hrest
        unfold evalProdReal at hih
        have hcast : ((Nat.add acc (Nat.mul wp (Nat.add clo SCALE)) : ℕ) : ℝ) =
            (acc : ℝ) + (wp : ℝ) * ((clo : ℝ) + (SCALE : ℝ)) := by
          rw [nat_add_eq, nat_mul_eq, nat_add_eq, Nat.cast_add, Nat.cast_mul, Nat.cast_add]
        rw [hcast] at hih
        have hwp_mul : (wp : ℝ) * ((clo : ℝ) + (SCALE : ℝ)) ≤
            (wp : ℝ) * ((∏ i : Fin 9, Real.cos (((p : ℝ) / (SCALE : ℝ)) * (a i : ℝ))) + 1) * (SCALE : ℝ) := by
          have := mul_le_mul_of_nonneg_left (show (clo : ℝ) + (SCALE : ℝ) ≤ ((∏ i : Fin 9, Real.cos (((p : ℝ) / (SCALE : ℝ)) * (a i : ℝ))) + 1) * (SCALE : ℝ) by linarith only [hclo]) (Nat.cast_nonneg wp)
          rw [mul_assoc]; exact this
        exact le_trans hih (by linarith only [hwp_mul])
      · have hwp0 : wp = 0 := by omega
        subst hwp0
        simp only [show Nat.blt 0 0 = false from rfl, Bool.false_eq_true, ite_false, Nat.cast_zero, zero_mul, zero_add]
        by_cases hwn : 0 < wn
        · simp only [Nat.blt_eq.mpr hwn, ite_true]
          obtain ⟨hj1, hj2⟩ := jensenChi_sound hpM' hjM'
          generalize jensenChi p c.j100 = chi at hj1 hj2 ⊢
          have hjQ_R : 9 * ((c.j100 : ℝ) / 100) ^ 2 ≤ ∑ i : Fin 9, (a i : ℝ) ^ 2 := by
            have h1 : (9 : ℝ) * ((c.j100 : ℝ) * (c.j100 : ℝ)) ≤ 10000 * (c.Qprev : ℝ) := by exact_mod_cast hjQ'
            have h2 : (c.Qprev : ℝ) ≤ ∑ i : Fin 9, (a i : ℝ) ^ 2 := by exact_mod_cast hQprev
            have h3 : 9 * ((c.j100 : ℝ) / 100) ^ 2 = (9 * ((c.j100 : ℝ) * (c.j100 : ℝ))) / 10000 := by ring
            rw [h3]; linarith only [h1, h2]
          have hjM_R : (c.j100 : ℝ) / 100 ≤ (c.M : ℝ) := by
            have h1 : (c.j100 : ℝ) ≤ 100 * (c.M : ℝ) := by exact_mod_cast hjM'
            linarith only [h1]
          have hjen := jensen_cos_prod (by positivity) (fun i => Nat.cast_nonneg _)
            (fun i => by exact_mod_cast le_trans (ha.antitone (Fin.zero_le i)) ha0)
            (by positivity) hjM_R htM hjQ_R
          have hchi_le : ((SCALE - chi : ℕ) : ℝ) ≤
              (1 - ∏ i : Fin 9, Real.cos (((p : ℝ) / (SCALE : ℝ)) * (a i : ℝ))) * (SCALE : ℝ) := by
            rw [Nat.cast_sub hj2, sub_mul, one_mul]
            exact sub_le_sub_left (le_trans (mul_le_mul_of_nonneg_right hjen (le_of_lt hSpos)) hj1) (SCALE : ℝ)
          have hih := ih (Nat.add acc (Nat.mul wn (Nat.sub SCALE chi))) hrest
          unfold evalProdReal at hih
          have hcast : ((Nat.add acc (Nat.mul wn (Nat.sub SCALE chi)) : ℕ) : ℝ) =
              (acc : ℝ) + (wn : ℝ) * ((SCALE - chi : ℕ) : ℝ) := by
            rw [nat_add_eq, nat_mul_eq, nat_sub_eq, Nat.cast_add, Nat.cast_mul]
          rw [hcast] at hih
          have hwn_mul : (wn : ℝ) * ((SCALE - chi : ℕ) : ℝ) ≤
              (wn : ℝ) * (1 - ∏ i : Fin 9, Real.cos (((p : ℝ) / (SCALE : ℝ)) * (a i : ℝ))) * (SCALE : ℝ) := by
            have := mul_le_mul_of_nonneg_left hchi_le (Nat.cast_nonneg wn)
            rw [mul_assoc]; exact this
          exact le_trans hih (by linarith only [hwn_mul])
        · have hwn0 : wn = 0 := by omega
          subst hwn0
          simp only [show Nat.blt 0 0 = false from rfl, Bool.false_eq_true, ite_false, Nat.cast_zero, zero_mul, zero_add]
          exact ih acc hrest
  let S := ∑ i : Fin 9, a i
  let P := (univ : Finset (Fin 9)).powerset.filter (fun U => S < 2 * ∑ i ∈ U, a i)
  have hP0 := sum_cos_pos_half hinj 0
  have hPcard : P.card = 256 := hP0.1
  have hPprops := hP0.2.1
  have hPinj := hP0.2.2.1
  have hsumK_eq : ∑ U ∈ P, evalKReal c.pw ((2 * ∑ i ∈ U, a i - S : ℕ) : ℝ) = 256 * evalProdReal c.pw a := by
    have haux : ∀ (pw : List (Nat × Nat × Nat)),
        ∑ U ∈ P, evalKReal pw ((2 * ∑ i ∈ U, a i - S : ℕ) : ℝ) = 256 * evalProdReal pw a := by
      intro pw
      induction pw with
      | nil => simp [evalKReal, evalProdReal]
      | cons e rest ih =>
        rcases e with ⟨p, wp, wn⟩
        unfold evalKReal evalProdReal
        unfold evalKReal evalProdReal at ih
        simp only [List.map_cons, List.sum_cons]
        rw [sum_add_distrib, ih, sum_add_distrib, ← mul_sum, ← mul_sum]
        have hcos := (sum_cos_pos_half hinj ((p : ℝ) / (SCALE : ℝ))).2.2.2
        have h1 : ∑ U ∈ P, (Real.cos (((p : ℝ) / (SCALE : ℝ)) * ((2 * ∑ i ∈ U, a i - S : ℕ) : ℝ)) + 1) =
            256 * ((∏ i : Fin 9, Real.cos (((p : ℝ) / (SCALE : ℝ)) * (a i : ℝ))) + 1) := by
          rw [sum_add_distrib, sum_const, hPcard, nsmul_eq_mul, hcos]; ring
        have h2 : ∑ U ∈ P, (1 - Real.cos (((p : ℝ) / (SCALE : ℝ)) * ((2 * ∑ i ∈ U, a i - S : ℕ) : ℝ))) =
            256 * (1 - ∏ i : Fin 9, Real.cos (((p : ℝ) / (SCALE : ℝ)) * (a i : ℝ))) := by
          rw [sum_sub_distrib, sum_const, hPcard, nsmul_eq_mul, hcos]; ring
        rw [h1, h2]; ring
    exact haux c.pw
  let xFn : Finset (Fin 9) → ℕ := fun U => 2 * ∑ i ∈ U, a i - S
  let Simg : Finset ℕ := P.image xFn
  have hSimg_card : Simg.card = 256 := by rw [card_image_of_injOn hPinj, hPcard]
  have hSimg_le : ∑ U ∈ P, evalKReal c.pw ((xFn U : ℕ) : ℝ) * (SCALE : ℝ) ≤
      ∑ x ∈ Simg, (evalKHiShift x c.pw 0 : ℝ) := by
    rw [sum_image (fun U hU V hV h => hPinj hU hV h)]
    refine sum_le_sum fun U hU => ?_
    have hxS : xFn U ≤ c.Smax := le_trans (hPprops U hU).2.2 hS_le
    have := evalKHiShift_sound hxS c.pw 0 hpw
    simpa using this
  have hlhs_R : (calcLhsShift c.b100 c.j100 c.pw 0 : ℝ) ≤ ∑ x ∈ Simg, (evalKHiShift x c.pw 0 : ℝ) := by
    have h1 := hlhs_le c.pw 0 hpw
    rw [Nat.cast_zero, zero_add] at h1
    have h2 : ∑ U ∈ P, evalKReal c.pw ((xFn U : ℕ) : ℝ) * (SCALE : ℝ) = 256 * (evalProdReal c.pw a * (SCALE : ℝ)) := by
      rw [← sum_mul, hsumK_eq]; ring
    linarith only [h1, h2, hSimg_le]
  unfold checkCertNat at hcert
  dsimp only at hcert
  simp only [Bool.and_eq_true] at hcert
  have hso_lt : (sumExcessShift c.pw c.tauOS c.tauES c.Smax (Nat.mul 256 c.tauOS) (Nat.mul 256 c.tauES)).1 <
      calcLhsShift c.b100 c.j100 c.pw 0 := Nat.blt_eq.mp hcert.1
  have hse_lt : (sumExcessShift c.pw c.tauOS c.tauES c.Smax (Nat.mul 256 c.tauOS) (Nat.mul 256 c.tauES)).2 <
      calcLhsShift c.b100 c.j100 c.pw 0 := Nat.blt_eq.mp hcert.2
  obtain ⟨hso_eq, hse_eq⟩ := sumExcessShift_eq c.pw c.tauOS c.tauES c.Smax (Nat.mul 256 c.tauOS) (Nat.mul 256 c.tauES)
  have hmax_nat : ∀ x y : ℕ, max (0 : ℝ) ((x : ℝ) - (y : ℝ)) = ((x - y : ℕ) : ℝ) := fun x y => by
    by_cases h : y ≤ x
    · have hR : (y : ℝ) ≤ (x : ℝ) := by exact_mod_cast h
      rw [Nat.cast_sub h, max_eq_right (by linarith)]
    · have hR : (x : ℝ) < (y : ℝ) := by exact_mod_cast (show x < y by omega)
      rw [Nat.sub_eq_zero_of_le (by omega), Nat.cast_zero, max_eq_left (by linarith)]
  by_cases hpar : S % 2 = 1
  · have hsub : Simg ⊆ (Icc 1 c.Smax).filter (fun x => x % 2 = 1) := by
      intro x hx
      rcases mem_image.mp hx with ⟨U, hU, rfl⟩
      have hp := hPprops U hU
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.2.1, le_trans hp.2.2 hS_le⟩, hp.1.trans hpar⟩
    have hthr := threshold_sum_le hsub (fun x => (evalKHiShift x c.pw 0 : ℝ)) (c.tauOS : ℝ)
    rw [hSimg_card] at hthr
    simp_rw [hmax_nat] at hthr
    have hso_R : ((256 : ℕ) : ℝ) * (c.tauOS : ℝ) + ∑ x ∈ (Icc 1 c.Smax).filter (fun x => x % 2 = 1), ((evalKHiShift x c.pw 0 - c.tauOS : ℕ) : ℝ) =
        ((sumExcessShift c.pw c.tauOS c.tauES c.Smax (Nat.mul 256 c.tauOS) (Nat.mul 256 c.tauES)).1 : ℝ) := by
      rw [hso_eq]; change ((256 : ℕ) : ℝ) * (c.tauOS : ℝ) + _ = ((256 * c.tauOS + _ : ℕ) : ℝ); push_cast; rfl
    have hlt_R : ((sumExcessShift c.pw c.tauOS c.tauES c.Smax (Nat.mul 256 c.tauOS) (Nat.mul 256 c.tauES)).1 : ℝ) <
        (calcLhsShift c.b100 c.j100 c.pw 0 : ℝ) := by exact_mod_cast hso_lt
    linarith only [hlhs_R, hthr, hso_R, hlt_R]
  · have hpar0 : S % 2 = 0 := by omega
    have hsub : Simg ⊆ (Icc 1 c.Smax).filter (fun x => x % 2 = 0) := by
      intro x hx
      rcases mem_image.mp hx with ⟨U, hU, rfl⟩
      have hp := hPprops U hU
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.2.1, le_trans hp.2.2 hS_le⟩, hp.1.trans hpar0⟩
    have hthr := threshold_sum_le hsub (fun x => (evalKHiShift x c.pw 0 : ℝ)) (c.tauES : ℝ)
    rw [hSimg_card] at hthr
    simp_rw [hmax_nat] at hthr
    have hse_R : ((256 : ℕ) : ℝ) * (c.tauES : ℝ) + ∑ x ∈ (Icc 1 c.Smax).filter (fun x => x % 2 = 0), ((evalKHiShift x c.pw 0 - c.tauES : ℕ) : ℝ) =
        ((sumExcessShift c.pw c.tauOS c.tauES c.Smax (Nat.mul 256 c.tauOS) (Nat.mul 256 c.tauES)).2 : ℝ) := by
      rw [hse_eq]; change ((256 : ℕ) : ℝ) * (c.tauES : ℝ) + _ = ((256 * c.tauES + _ : ℕ) : ℝ); push_cast; rfl
    have hlt_R : ((sumExcessShift c.pw c.tauOS c.tauES c.Smax (Nat.mul 256 c.tauOS) (Nat.mul 256 c.tauES)).2 : ℝ) <
        (calcLhsShift c.b100 c.j100 c.pw 0 : ℝ) := by exact_mod_cast hse_lt
    linarith only [hlhs_R, hthr, hse_R, hlt_R]

-- 5. Fast 2-variable nlinarith refutation of a 0 <= 137 given Q >= 135501!
private lemma a0_ge_138 {a : Fin 9 → ℕ} (ha : StrictAnti a)
    (hinj : Function.Injective (fun U : Finset (Fin 9) => ∑ i ∈ U, a i))
    (hQ : 135501 ≤ ∑ i : Fin 9, a i ^ 2) : 138 ≤ a 0 := by
  by_contra hlt
  have ha0 : a 0 ≤ 137 := by omega
  have hub := a_upper_bounds ha hinj
  have hmom := (five_layer_moments hinj).2.2.2.2
  have hS_eq : ∑ i : Fin 9, a i = a 0 + a 1 + a 2 + a 3 + a 4 + a 5 + a 6 + a 7 + a 8 := by
    simp [Fin.sum_univ_succ, add_assoc]
  have hQ_eq : ∑ i : Fin 9, a i ^ 2 = a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2 + a 4 ^ 2 + a 5 ^ 2 + a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2 := by
    simp [Fin.sum_univ_succ, add_assoc]
  have hu0 : a 0 ≤ 137 := by omega
  have hu1 : a 1 ≤ 136 := by omega
  have hu2 : a 2 ≤ 135 := by omega
  have hu3 : a 3 ≤ 133 := by omega
  have hu4 : a 4 ≤ 130 := by omega
  have hu5 : a 5 ≤ 124 := by omega
  have hu6 : a 6 ≤ 115 := by omega
  have hu7 : a 7 ≤ 114 := by omega
  have ha8_ge : 62 ≤ a 8 := by
    have hsq : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2 + a 4 ^ 2 + a 5 ^ 2 + a 6 ^ 2 + a 7 ^ 2 ≤ 131676 := by
      have s0 : a 0 ^ 2 ≤ 137 ^ 2 := Nat.pow_le_pow_left hu0 2
      have s1 : a 1 ^ 2 ≤ 136 ^ 2 := Nat.pow_le_pow_left hu1 2
      have s2 : a 2 ^ 2 ≤ 135 ^ 2 := Nat.pow_le_pow_left hu2 2
      have s3 : a 3 ^ 2 ≤ 133 ^ 2 := Nat.pow_le_pow_left hu3 2
      have s4 : a 4 ^ 2 ≤ 130 ^ 2 := Nat.pow_le_pow_left hu4 2
      have s5 : a 5 ^ 2 ≤ 124 ^ 2 := Nat.pow_le_pow_left hu5 2
      have s6 : a 6 ^ 2 ≤ 115 ^ 2 := Nat.pow_le_pow_left hu6 2
      have s7 : a 7 ^ 2 ≤ 114 ^ 2 := Nat.pow_le_pow_left hu7 2
      omega
    rw [hQ_eq] at hQ
    have : 3825 ≤ a 8 ^ 2 := by omega
    by_contra h8lt
    have : a 8 ≤ 61 := by omega
    have : a 8 ^ 2 ≤ 61 ^ 2 := Nat.pow_le_pow_left this 2
    omega
  have hge62 : ∀ i : Fin 9, 62 ≤ a i := fun i => le_trans ha8_ge (ha.antitone (Fin.le_last i))
  have hl0 := hge62 0; have hl1 := hge62 1; have hl2 := hge62 2; have hl3 := hge62 3
  have hl4 := hge62 4; have hl5 := hge62 5; have hl6 := hge62 6; have hl7 := hge62 7
  have hlin : ∀ (x u : ℤ), 62 ≤ x → x ≤ u → 115 ≤ u → 177 * u - u ^ 2 ≤ 177 * x - x ^ 2 := by
    intro x u hx hxu hu; nlinarith only [hx, hxu, hu]
  have hlin2 : ∀ (x : ℤ), 62 ≤ x → x ≤ 115 → 7130 ≤ 177 * x - x ^ 2 := by
    intro x h1 h2; nlinarith only [h1, h2]
  set SZ : ℤ := ((∑ i : Fin 9, a i : ℕ) : ℤ)
  set QZ : ℤ := ((∑ i : Fin 9, a i ^ 2 : ℕ) : ℤ)
  have hSZ_eq : SZ = (a 0 : ℤ) + (a 1 : ℤ) + (a 2 : ℤ) + (a 3 : ℤ) + (a 4 : ℤ) + (a 5 : ℤ) + (a 6 : ℤ) + (a 7 : ℤ) + (a 8 : ℤ) := by
    dsimp [SZ]; rw [hS_eq]; push_cast; rfl
  have hQZ_eq : QZ = (a 0 : ℤ) ^ 2 + (a 1 : ℤ) ^ 2 + (a 2 : ℤ) ^ 2 + (a 3 : ℤ) ^ 2 + (a 4 : ℤ) ^ 2 + (a 5 : ℤ) ^ 2 + (a 6 : ℤ) ^ 2 + (a 7 : ℤ) ^ 2 + (a 8 : ℤ) ^ 2 := by
    dsimp [QZ]; rw [hQ_eq]; push_cast; rfl
  have c0 := hlin (a 0) 137 (by exact_mod_cast hl0) (by exact_mod_cast hu0) (by omega)
  have c1 := hlin (a 1) 136 (by exact_mod_cast hl1) (by exact_mod_cast hu1) (by omega)
  have c2 := hlin (a 2) 135 (by exact_mod_cast hl2) (by exact_mod_cast hu2) (by omega)
  have c3 := hlin (a 3) 133 (by exact_mod_cast hl3) (by exact_mod_cast hu3) (by omega)
  have c4 := hlin (a 4) 130 (by exact_mod_cast hl4) (by exact_mod_cast hu4) (by omega)
  have c5 := hlin (a 5) 124 (by exact_mod_cast hl5) (by exact_mod_cast hu5) (by omega)
  have c6 := hlin (a 6) 115 (by exact_mod_cast hl6) (by exact_mod_cast hu6) (by omega)
  have c7 := hlin2 (a 7) (by exact_mod_cast hl7) (by exact_mod_cast (show a 7 ≤ 115 by omega))
  have c8 := hlin2 (a 8) (by exact_mod_cast ha8_ge) (by exact_mod_cast (show a 8 ≤ 115 by omega))
  have h177 : QZ + 56650 ≤ 177 * SZ := by linarith only [hSZ_eq, hQZ_eq, c0, c1, c2, c3, c4, c5, c6, c7, c8]
  have hmomZ : (42863 : ℤ) + SZ ^ 2 ≤ 9 * QZ := by dsimp [SZ, QZ]; exact_mod_cast hmom
  have hQZ_ge : (135501 : ℤ) ≤ QZ := by dsimp [QZ]; exact_mod_cast hQ
  nlinarith only [h177, hmomZ, hQZ_ge]

private def cert151a : ElkiesCertNat := {
  M := 151, Smax := 1213, Qprev := 87381, Qtgt := 129000,
  b100 := [15100, 15000, 14900, 14700, 14400, 13800, 1045, 0, 0], j100 := 9853,
  pw := [(0, 92905, 0), (78706, 231996, 0), (157412, 476580, 0), (236118, 478281, 0), (314824, 98245, 0), (393530, 2369, 0), (472236, 4113, 0), (550942, 5331, 0), (629648, 502750, 0), (708355, 150675, 0), (787061, 539, 0), (865767, 0, 441), (944473, 0, 199994), (1023179, 395605, 0)],
  tauOS := 300035888755968, tauES := 300035094390570 }

private def cert151b : ElkiesCertNat := {
  M := 151, Smax := 1213, Qprev := 129001, Qtgt := 132150,
  b100 := [15100, 15000, 14900, 14700, 14400, 13800, 5709, 0, 0], j100 := 11972,
  pw := [(0, 329050, 0), (78706, 368081, 0), (157412, 381174, 0), (236118, 153381, 0), (314824, 192, 0), (393530, 439, 0), (472236, 1637, 0), (550942, 2109, 0), (629648, 1915, 0), (708355, 115794, 0), (787061, 299563, 0), (865767, 28226, 0), (944473, 0, 550822), (1023179, 424341, 0)],
  tauOS := 348785438536262, tauES := 348778156778371 }

private def cert150b : ElkiesCertNat := {
  M := 150, Smax := 1204, Qprev := 132151, Qtgt := 132500,
  b100 := [15000, 14900, 14800, 14600, 14300, 13700, 7322, 0, 0], j100 := 12117,
  pw := [(0, 319662, 0), (79231, 356766, 0), (158462, 373645, 0), (237692, 173296, 0), (316923, 62, 0), (396154, 385, 0), (475385, 1120, 0), (554615, 2031, 0), (633846, 1928, 0), (713077, 126997, 0), (792308, 297644, 0), (871538, 27883, 0), (950769, 0, 556131), (1030000, 431398, 0)],
  tauOS := 347708767340165, tauES := 347697915761755 }

private def cert149b : ElkiesCertNat := {
  M := 149, Smax := 1195, Qprev := 132501, Qtgt := 132800,
  b100 := [14900, 14800, 14700, 14500, 14200, 13600, 8603, 0, 0], j100 := 12133,
  pw := [(0, 315666, 0), (79763, 350329, 0), (159525, 369390, 0), (239288, 193942, 0), (319050, 0, 4), (398813, 412, 0), (478575, 1353, 0), (558338, 1762, 0), (638100, 1945, 0), (717863, 147472, 0), (797625, 288291, 0), (877388, 24200, 0), (957150, 0, 554246), (1036913, 436943, 0)],
  tauOS := 348096123168374, tauES := 348085081498924 }

private def cert147b : ElkiesCertNat := {
  M := 147, Smax := 1177, Qprev := 132801, Qtgt := 133300,
  b100 := [14700, 14600, 14500, 14300, 14000, 13400, 10652, 0, 0], j100 := 12147,
  pw := [(0, 297960, 0), (80848, 330504, 0), (161695, 360612, 0), (242543, 242005, 0), (323391, 146, 0), (404239, 0, 0), (485086, 1053, 0), (565934, 1891, 0), (646782, 2486, 0), (727630, 193660, 0), (808477, 268178, 0), (889325, 14649, 0), (970173, 0, 549041), (1051020, 449760, 0)],
  tauOS := 346461956014817, tauES := 346459701622785 }

private def cert146b : ElkiesCertNat := {
  M := 146, Smax := 1168, Qprev := 133301, Qtgt := 133500,
  b100 := [14600, 14500, 14400, 14200, 13900, 13300, 11511, 0, 0], j100 := 12170,
  pw := [(0, 294183, 0), (81401, 323923, 0), (162803, 355925, 0), (244204, 264324, 0), (325606, 4062, 0), (407007, 199, 0), (488409, 1189, 0), (569810, 2163, 0), (651212, 2370, 0), (732613, 222391, 0), (814015, 253953, 0), (895416, 6694, 0), (976818, 0, 540157), (1058219, 454079, 0)],
  tauOS := 346222317902406, tauES := 346219225173798 }

private def cert145b : ElkiesCertNat := {
  M := 145, Smax := 1159, Qprev := 133501, Qtgt := 133750,
  b100 := [14500, 14400, 14300, 14100, 13800, 13200, 12300, 788, 0], j100 := 12179,
  pw := [(0, 305422, 0), (81963, 326933, 0), (163926, 346185, 0), (245889, 259868, 0), (327851, 17936, 0), (409814, 5359, 0), (491777, 1182, 0), (573740, 2099, 0), (655703, 2603, 0), (737666, 232099, 0), (819629, 249257, 0), (901592, 6400, 0), (983554, 0, 536733), (1065517, 456038, 0)],
  tauOS := 348409094524453, tauES := 348402511546999 }

private def cert144b : ElkiesCertNat := {
  M := 144, Smax := 1150, Qprev := 133751, Qtgt := 133950,
  b100 := [14400, 14300, 14200, 14000, 13700, 13100, 12200, 4677, 0], j100 := 12190,
  pw := [(0, 283993, 0), (82532, 299529, 0), (165064, 314907, 0), (247596, 252625, 0), (330128, 68475, 0), (412660, 28461, 0), (495192, 1262, 0), (577724, 2138, 0), (660256, 2332, 0), (742788, 251770, 0), (825321, 261356, 0), (907853, 3703, 0), (990385, 0, 548775), (1072917, 477777, 0)],
  tauOS := 343668673729238, tauES := 343677682292715 }

private def cert143b : ElkiesCertNat := {
  M := 143, Smax := 1141, Qprev := 133951, Qtgt := 134200,
  b100 := [14300, 14200, 14100, 13900, 13600, 13000, 12100, 6594, 0], j100 := 12199,
  pw := [(0, 277127, 0), (83109, 286396, 0), (166218, 294558, 0), (249328, 245602, 0), (332437, 100623, 0), (415546, 41258, 0), (498655, 15922, 0), (581764, 2055, 0), (664874, 2464, 0), (747983, 258440, 0), (831092, 273819, 0), (914201, 0, 136), (997310, 0, 549085), (1080420, 488609, 0)],
  tauOS := 341733268371032, tauES := 341714557960387 }

private def cert142b : ElkiesCertNat := {
  M := 142, Smax := 1132, Qprev := 134201, Qtgt := 134450,
  b100 := [14200, 14100, 14000, 13800, 13500, 12900, 12000, 8060, 0], j100 := 12211,
  pw := [(0, 270422, 0), (83694, 274003, 0), (167389, 275801, 0), (251083, 239561, 0), (334778, 130582, 0), (418472, 54950, 0), (502167, 29880, 0), (585861, 2211, 0), (669556, 2406, 0), (753250, 263355, 0), (836945, 288880, 0), (920639, 0, 7281), (1004334, 0, 545522), (1088028, 496900, 0)],
  tauOS := 340656590303485, tauES := 340664364668491 }

private def cert141b : ElkiesCertNat := {
  M := 141, Smax := 1123, Qprev := 134451, Qtgt := 134700,
  b100 := [14100, 14000, 13900, 13700, 13400, 12800, 11900, 9289, 0], j100 := 12222,
  pw := [(0, 271247, 0), (84288, 262923, 0), (168576, 247225, 0), (252864, 220772, 0), (337152, 156796, 0), (421440, 74579, 0), (505728, 41950, 0), (590016, 2132, 0), (674304, 2343, 0), (758592, 246443, 0), (842881, 306956, 0), (927169, 4488, 0), (1011457, 0, 554600), (1095745, 502953, 0)],
  tauOS := 336853250626518, tauES := 336864440082479 }

private def cert140b : ElkiesCertNat := {
  M := 140, Smax := 1114, Qprev := 134701, Qtgt := 135000,
  b100 := [14000, 13900, 13800, 13600, 13300, 12700, 11800, 10391, 0], j100 := 12233,
  pw := [(0, 295319, 0), (84890, 274200, 0), (169780, 235257, 0), (254670, 204446, 0), (339560, 166649, 0), (424451, 84955, 0), (509341, 56363, 0), (594231, 2219, 0), (679121, 2276, 0), (764011, 235392, 0), (848901, 314297, 0), (933791, 6935, 0), (1018681, 0, 547039), (1103571, 498787, 0)],
  tauOS := 340634003903596, tauES := 340643262311033 }

private def cert139b : ElkiesCertNat := {
  M := 139, Smax := 1105, Qprev := 135001, Qtgt := 135300,
  b100 := [13900, 13800, 13700, 13500, 13200, 12600, 11700, 11381, 0], j100 := 12247,
  pw := [(0, 321078, 0), (85501, 277861, 0), (171002, 199879, 0), (256502, 162469, 0), (342003, 164525, 0), (427504, 117140, 0), (513005, 65527, 0), (598506, 2192, 0), (684007, 3, 0), (769507, 176397, 0), (855008, 337832, 0), (940509, 42495, 0), (1026010, 0, 566063), (1111511, 490700, 0)],
  tauOS := 339818094129357, tauES := 339822284998938 }

private def cert138b : ElkiesCertNat := {
  M := 138, Smax := 1096, Qprev := 135301, Qtgt := 135500,
  b100 := [13800, 13700, 13600, 13400, 13100, 12500, 11600, 11500, 4205], j100 := 12261,
  pw := [(0, 296054, 0), (86120, 252082, 0), (172241, 178084, 0), (258361, 158539, 0), (344482, 188798, 0), (430602, 162395, 0), (516722, 65590, 0), (602843, 2307, 0), (688963, 81, 0), (775084, 188897, 0), (861204, 353378, 0), (947324, 35028, 0), (1033445, 0, 560666), (1119565, 499502, 0)],
  tauOS := 331866907093998, tauES := 331876084696475 }


private lemma certMeta_151a : checkCertMeta cert151a = true := by decide +kernel
private lemma ok_151a : checkCertNat cert151a = true := by decide +kernel
private lemma certMeta_151b : checkCertMeta cert151b = true := by decide +kernel
private lemma ok_151b : checkCertNat cert151b = true := by decide +kernel
private lemma certMeta_150b : checkCertMeta cert150b = true := by decide +kernel
private lemma ok_150b : checkCertNat cert150b = true := by decide +kernel
private lemma certMeta_149b : checkCertMeta cert149b = true := by decide +kernel
private lemma ok_149b : checkCertNat cert149b = true := by decide +kernel
private lemma certMeta_147b : checkCertMeta cert147b = true := by decide +kernel
private lemma ok_147b : checkCertNat cert147b = true := by decide +kernel
private lemma certMeta_146b : checkCertMeta cert146b = true := by decide +kernel
private lemma ok_146b : checkCertNat cert146b = true := by decide +kernel
private lemma certMeta_145b : checkCertMeta cert145b = true := by decide +kernel
private lemma ok_145b : checkCertNat cert145b = true := by decide +kernel
private lemma certMeta_144b : checkCertMeta cert144b = true := by decide +kernel
private lemma ok_144b : checkCertNat cert144b = true := by decide +kernel
private lemma certMeta_143b : checkCertMeta cert143b = true := by decide +kernel
private lemma ok_143b : checkCertNat cert143b = true := by decide +kernel
private lemma certMeta_142b : checkCertMeta cert142b = true := by decide +kernel
private lemma ok_142b : checkCertNat cert142b = true := by decide +kernel
private lemma certMeta_141b : checkCertMeta cert141b = true := by decide +kernel
private lemma ok_141b : checkCertNat cert141b = true := by decide +kernel
private lemma certMeta_140b : checkCertMeta cert140b = true := by decide +kernel
private lemma ok_140b : checkCertNat cert140b = true := by decide +kernel
private lemma certMeta_139b : checkCertMeta cert139b = true := by decide +kernel
private lemma ok_139b : checkCertNat cert139b = true := by decide +kernel
private lemma certMeta_138b : checkCertMeta cert138b = true := by decide +kernel
private lemma ok_138b : checkCertNat cert138b = true := by decide +kernel

private lemma ble_false_of_lt {a b : Nat} (h : b < a) : Nat.ble a b = false := by
  cases hc : Nat.ble a b
  · rfl
  · exfalso; have := Nat.le_of_ble_eq_true hc; omega


private def nmax (a b : Nat) : Nat := if Nat.blt a b then b else a
private def nmin (a b : Nat) : Nat := if Nat.blt a b then a else b

private lemma nmax_eq (a b : Nat) : nmax a b = max a b := by
  unfold nmax
  cases h : Nat.blt a b
  · have : b ≤ a := by by_contra hlt; rw [Nat.blt_eq.mpr (by omega)] at h; cases h
    simp [max_eq_left this]
  · have : a < b := Nat.blt_eq.mp h
    simp [max_eq_right (le_of_lt this)]

private lemma nmin_eq (a b : Nat) : nmin a b = min a b := by
  unfold nmin
  cases h : Nat.blt a b
  · have : b ≤ a := by by_contra hlt; rw [Nat.blt_eq.mpr (by omega)] at h; cases h
    simp [min_eq_right this]
  · have : a < b := Nat.blt_eq.mp h
    simp [min_eq_left (le_of_lt this)]

-- Kronecker R_k = (prod_{i < k} (1 + 256^{a_i}))^2
private def updR (R v : Nat) : Nat :=
  let p := Nat.pow 256 v
  let t := Nat.add R (Nat.mul R p)
  Nat.add t (Nat.mul t p)

private def testPos (Rpos d : Nat) : Bool :=
  Nat.blt 0 (Nat.mod (Nat.div Rpos (Nat.pow 256 d)) 256)

private def findGAux : Nat → Nat → Nat → Nat
  | 0, _, g => g
  | fuel + 1, W, g =>
    if Nat.blt 0 (Nat.mod W 256) then findGAux fuel (Nat.div W 256) (Nat.add g 1)
    else g

private def findG (Rpos g : Nat) : Nat :=
  findGAux 64 (Nat.div Rpos (Nat.pow 256 g)) g

private def skipLoAux : Nat → Nat → Nat → Nat
  | 0, _, l => l
  | fuel + 1, W, l =>
    if Nat.blt 0 (Nat.mod W 256) then skipLoAux fuel (Nat.div W 256) (Nat.add l 1)
    else l

private def skipLo (Rpos l hi : Nat) : Nat :=
  if Nat.blt hi l then l
  else skipLoAux (Nat.add (Nat.sub hi l) 1) (Nat.div Rpos (Nat.pow 256 l)) l

private def skipHiAux : Nat → Nat → Nat → Nat
  | 0, _, h => h
  | fuel + 1, Rpos, h =>
    if testPos Rpos h then
      if Nat.beq h 0 then 0 else skipHiAux fuel Rpos (Nat.sub h 1)
    else h

private def skipHi (Rpos lo h : Nat) : Nat :=
  if Nat.blt h lo then h
  else skipHiAux (Nat.add (Nat.sub h lo) 1) Rpos h

private def collectAliveAux : Nat → Nat → Nat → List Nat → List Nat
  | 0, _, _, acc => acc
  | fuel + 1, W, v, acc =>
    let acc' := if Nat.beq (Nat.mod W 256) 0 then v :: acc else acc
    collectAliveAux fuel (Nat.div W 256) (Nat.add v 1) acc'

private def collectAliveDesc (Rpos lo hi : Nat) : List Nat :=
  if Nat.blt hi lo then []
  else
    let span := Nat.add (Nat.sub hi lo) 1
    let slice := Nat.mod (Nat.div Rpos (Nat.pow 256 lo)) (Nat.pow 256 span)
    collectAliveAux span slice lo []

private def okSQ (qlb S Q : Nat) : Bool :=
  if Nat.blt Q qlb then false
  else
    let s2 := Nat.mul S S
    if Nat.blt (Nat.mul 9 Q) (Nat.add 42863 s2) then false
    else if Nat.blt (Nat.mul 10 Q) (Nat.add 190509 s2) then false
    else if Nat.blt (Nat.mul 16 Q) (Nat.add 881995 s2) then false
    else if Nat.blt (Nat.mul 126 Q) (Nat.add 9924583 (Nat.mul 3 s2)) then false
    else if Nat.blt (Nat.mul 256 Q) (Nat.add 22108415 s2) then false
    else true

private def checkSegLoop (qlb curS curQ QRmin bS bQ0 lv : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, T =>
    let mv := Nat.add lv (Nat.sub T bS)
    let qR := Nat.add bQ0 (Nat.mul mv mv)
    if and (Nat.ble QRmin qR) (okSQ qlb (Nat.add curS T) (Nat.add curQ qR)) then true
    else checkSegLoop qlb curS curQ QRmin bS bQ0 lv fuel (Nat.add T 1)

private def checkSeg (qlb curS curQ QRmin bS bQ lv nL nR segR : Nat) : Bool :=
  let L := nmax nL bS
  let R := nmin nR segR
  if Nat.blt R L then false
  else
    let bQ0 := Nat.sub bQ (Nat.mul lv lv)
    let mL := Nat.add lv (Nat.sub L bS)
    let mR := Nat.add lv (Nat.sub R bS)
    let qLr := Nat.add bQ0 (Nat.mul mL mL)
    let qRr := Nat.add bQ0 (Nat.mul mR mR)
    if and (Nat.blt qLr QRmin) (Nat.blt qRr QRmin) then false
    else
      let qL := Nat.add curQ qLr
      let qR := Nat.add curQ qRr
      if and (Nat.blt qL qlb) (Nat.blt qR qlb) then false
      else
        let sL := Nat.add curS L
        let sR := Nat.add curS R
        if and (Nat.ble QRmin qRr) (okSQ qlb sR qR) then true
        else if and (Nat.ble QRmin qLr) (okSQ qlb sL qL) then true
        else if Nat.ble R (Nat.add L 1) then false
        else
          let sL2 := Nat.mul sL sL
          let sR2 := Nat.mul sR sR
          if and (Nat.blt (Nat.mul 9 qL) (Nat.add 42863 sL2)) (Nat.blt (Nat.mul 9 qR) (Nat.add 42863 sR2)) then false
          else if and (Nat.blt (Nat.mul 10 qL) (Nat.add 190509 sL2)) (Nat.blt (Nat.mul 10 qR) (Nat.add 190509 sR2)) then false
          else if and (Nat.blt (Nat.mul 16 qL) (Nat.add 881995 sL2)) (Nat.blt (Nat.mul 16 qR) (Nat.add 881995 sR2)) then false
          else if and (Nat.blt (Nat.mul 126 qL) (Nat.add 9924583 (Nat.mul 3 sL2))) (Nat.blt (Nat.mul 126 qR) (Nat.add 9924583 (Nat.mul 3 sR2))) then false
          else if and (Nat.blt (Nat.mul 256 qL) (Nat.add 22108415 sL2)) (Nat.blt (Nat.mul 256 qR) (Nat.add 22108415 sR2)) then false
          else checkSegLoop qlb curS curQ QRmin bS bQ0 lv (Nat.sub R (Nat.add L 1)) (Nat.add L 1)

private def checkBox2 (qlb curS curQ Tlo Thi QRmin l0 h0 l1 h1 : Nat) : Bool :=
  let bS0 := Nat.add l0 l1
  let bS1 := Nat.add h0 l1
  let bS2 := Nat.add h0 h1
  let nL := nmax Tlo bS0
  let nR := nmin Thi bS2
  if Nat.blt nR nL then false
  else
    let bQ0 := Nat.add (Nat.mul l0 l0) (Nat.mul l1 l1)
    if checkSeg qlb curS curQ QRmin bS0 bQ0 l0 nL nR bS1 then true
    else
      let bQ1 := Nat.add (Nat.mul h0 h0) (Nat.mul l1 l1)
      checkSeg qlb curS curQ QRmin bS1 bQ1 l1 nL nR bS2

private def checkBox3 (qlb curS curQ Tlo Thi QRmin l0 h0 l1 h1 l2 h2 : Nat) : Bool :=
  let bS0 := Nat.add l0 (Nat.add l1 l2)
  let bS1 := Nat.add h0 (Nat.add l1 l2)
  let bS2 := Nat.add h0 (Nat.add h1 l2)
  let bS3 := Nat.add h0 (Nat.add h1 h2)
  let nL := nmax Tlo bS0
  let nR := nmin Thi bS3
  if Nat.blt nR nL then false
  else
    let bQ0 := Nat.add (Nat.mul l0 l0) (Nat.add (Nat.mul l1 l1) (Nat.mul l2 l2))
    if checkSeg qlb curS curQ QRmin bS0 bQ0 l0 nL nR bS1 then true
    else
      let bQ1 := Nat.add (Nat.mul h0 h0) (Nat.add (Nat.mul l1 l1) (Nat.mul l2 l2))
      if checkSeg qlb curS curQ QRmin bS1 bQ1 l1 nL nR bS2 then true
      else
        let bQ2 := Nat.add (Nat.mul h0 h0) (Nat.add (Nat.mul h1 h1) (Nat.mul l2 l2))
        checkSeg qlb curS curQ QRmin bS2 bQ2 l2 nL nR bS3

private def checkBox4 (qlb curS curQ Tlo Thi QRmin l0 h0 l1 h1 l2 h2 l3 h3 : Nat) : Bool :=
  let bS0 := Nat.add l0 (Nat.add l1 (Nat.add l2 l3))
  let bS1 := Nat.add h0 (Nat.add l1 (Nat.add l2 l3))
  let bS2 := Nat.add h0 (Nat.add h1 (Nat.add l2 l3))
  let bS3 := Nat.add h0 (Nat.add h1 (Nat.add h2 l3))
  let bS4 := Nat.add h0 (Nat.add h1 (Nat.add h2 h3))
  let nL := nmax Tlo bS0
  let nR := nmin Thi bS4
  if Nat.blt nR nL then false
  else
    let q23 := Nat.add (Nat.mul l2 l2) (Nat.mul l3 l3)
    let bQ0 := Nat.add (Nat.mul l0 l0) (Nat.add (Nat.mul l1 l1) q23)
    if checkSeg qlb curS curQ QRmin bS0 bQ0 l0 nL nR bS1 then true
    else
      let bQ1 := Nat.add (Nat.mul h0 h0) (Nat.add (Nat.mul l1 l1) q23)
      if checkSeg qlb curS curQ QRmin bS1 bQ1 l1 nL nR bS2 then true
      else
        let q01 := Nat.add (Nat.mul h0 h0) (Nat.mul h1 h1)
        let bQ2 := Nat.add q01 q23
        if checkSeg qlb curS curQ QRmin bS2 bQ2 l2 nL nR bS3 then true
        else
          let bQ3 := Nat.add q01 (Nat.add (Nat.mul h2 h2) (Nat.mul l3 l3))
          checkSeg qlb curS curQ QRmin bS3 bQ3 l3 nL nR bS4

private def checkBox5 (qlb curS curQ Tlo Thi QRmin l0 h0 l1 h1 l2 h2 l3 h3 l4 h4 : Nat) : Bool :=
  let s34 := Nat.add l3 l4
  let bS0 := Nat.add l0 (Nat.add l1 (Nat.add l2 s34))
  let bS1 := Nat.add h0 (Nat.add l1 (Nat.add l2 s34))
  let bS2 := Nat.add h0 (Nat.add h1 (Nat.add l2 s34))
  let bS3 := Nat.add h0 (Nat.add h1 (Nat.add h2 s34))
  let bS4 := Nat.add h0 (Nat.add h1 (Nat.add h2 (Nat.add h3 l4)))
  let bS5 := Nat.add h0 (Nat.add h1 (Nat.add h2 (Nat.add h3 h4)))
  let nL := nmax Tlo bS0
  let nR := nmin Thi bS5
  if Nat.blt nR nL then false
  else
    let q34 := Nat.add (Nat.mul l3 l3) (Nat.mul l4 l4)
    let q234 := Nat.add (Nat.mul l2 l2) q34
    let bQ0 := Nat.add (Nat.mul l0 l0) (Nat.add (Nat.mul l1 l1) q234)
    if checkSeg qlb curS curQ QRmin bS0 bQ0 l0 nL nR bS1 then true
    else
      let bQ1 := Nat.add (Nat.mul h0 h0) (Nat.add (Nat.mul l1 l1) q234)
      if checkSeg qlb curS curQ QRmin bS1 bQ1 l1 nL nR bS2 then true
      else
        let q01 := Nat.add (Nat.mul h0 h0) (Nat.mul h1 h1)
        let bQ2 := Nat.add q01 q234
        if checkSeg qlb curS curQ QRmin bS2 bQ2 l2 nL nR bS3 then true
        else
          let q012 := Nat.add q01 (Nat.mul h2 h2)
          let bQ3 := Nat.add q012 q34
          if checkSeg qlb curS curQ QRmin bS3 bQ3 l3 nL nR bS4 then true
          else
            let bQ4 := Nat.add q012 (Nat.add (Nat.mul h3 h3) (Nat.mul l4 l4))
            checkSeg qlb curS curQ QRmin bS4 bQ4 l4 nL nR bS5

private def filterPartners (R6pos x6 hi7 : Nat) : List Nat → List Nat
  | [] => []
  | y :: ys =>
    if Nat.blt hi7 y then filterPartners R6pos x6 hi7 ys
    else if or (testPos R6pos (Nat.sub x6 y)) (testPos R6pos (Nat.add x6 y)) then
      filterPartners R6pos x6 hi7 ys
    else y :: filterPartners R6pos x6 hi7 ys

private def checkX8 (qlb sum7 sq7 R6pos G x6 x7 hi8 Tlo7 Thi7 : Nat) : List Nat → Bool
  | [] => true
  | x8 :: rest =>
    if Nat.blt hi8 x8 then checkX8 qlb sum7 sq7 R6pos G x6 x7 hi8 Tlo7 Thi7 rest
    else
      let s78 := Nat.add x7 x8
      if Nat.blt s78 Tlo7 then true
      else if Nat.blt Thi7 s78 then checkX8 qlb sum7 sq7 R6pos G x6 x7 hi8 Tlo7 Thi7 rest
      else if Nat.blt (Nat.sub x7 x8) G then checkX8 qlb sum7 sq7 R6pos G x6 x7 hi8 Tlo7 Thi7 rest
      else
        let okQ := okSQ qlb (Nat.add sum7 s78) (Nat.add sq7 (Nat.add (Nat.mul x7 x7) (Nat.mul x8 x8)))
        if okQ then
          if or (testPos R6pos (Nat.sub x7 x8)) (testPos R6pos (Nat.add x7 x8)) then
            checkX8 qlb sum7 sq7 R6pos G x6 x7 hi8 Tlo7 Thi7 rest
          else
            let sum3 := Nat.add x6 s78
            let d1 := Nat.sub (Nat.add x6 x7) x8
            let d2 := Nat.sub (Nat.add x6 x8) x7
            let d3 := if Nat.blt x6 s78 then Nat.sub s78 x6 else Nat.sub x6 s78
            if and (not (Nat.beq x6 s78))
               (and (not (testPos R6pos sum3))
               (and (not (testPos R6pos d1))
               (and (not (testPos R6pos d2))
                    (not (testPos R6pos d3))))) then false
            else checkX8 qlb sum7 sq7 R6pos G x6 x7 hi8 Tlo7 Thi7 rest
        else checkX8 qlb sum7 sq7 R6pos G x6 x7 hi8 Tlo7 Thi7 rest

private def checkX7 (qlb sum7 sq7 R6pos G x6 lo7 hi8 Tlo7 Thi7 : Nat) : List Nat → Bool
  | [] => true
  | x7 :: rest =>
    if Nat.blt x7 lo7 then true
    else
      match rest with
      | [] => true
      | nxt :: _ =>
        if Nat.blt (Nat.add x7 nxt) Tlo7 then true
        else if checkX8 qlb sum7 sq7 R6pos G x6 x7 hi8 Tlo7 Thi7 rest then
          checkX7 qlb sum7 sq7 R6pos G x6 lo7 hi8 Tlo7 Thi7 rest
        else false

private def checkX6 (qlb sum6 sq6 R6pos G lo6 hi6 lo7 hi7 lo8 hi8 Tlo6 Thi6 : Nat) : List Nat → Bool
  | [] => true
  | x6 :: rest =>
    if Nat.blt x6 lo6 then true
    else
      let h7 := nmin hi7 (Nat.sub x6 G)
      let h8 := nmin hi8 (Nat.sub h7 G)
      if or (Nat.blt h7 lo7) (Nat.blt h8 lo8) then
        checkX6 qlb sum6 sq6 R6pos G lo6 hi6 lo7 hi7 lo8 hi8 Tlo6 Thi6 rest
      else
        let sum7 := Nat.add sum6 x6
        let sq7 := Nat.add sq6 (Nat.mul x6 x6)
        let Tlo7 := nmax (Nat.sub Tlo6 x6) (nmax (Nat.sub 511 sum7) (Nat.mul 3 G))
        let Thi7 := nmin (Nat.sub Thi6 x6) (Nat.add h7 h8)
        if Nat.blt Thi7 Tlo7 then
          checkX6 qlb sum6 sq6 R6pos G lo6 hi6 lo7 hi7 lo8 hi8 Tlo6 Thi6 rest
        else
          let maxQ := Nat.add sq7 (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8))
          if Nat.blt maxQ qlb then true
          else
            let minS := Nat.add sum7 Tlo7
            if Nat.blt (Nat.mul 9 maxQ) (Nat.add 42863 (Nat.mul minS minS)) then
              checkX6 qlb sum6 sq6 R6pos G lo6 hi6 lo7 hi7 lo8 hi8 Tlo6 Thi6 rest
            else if not (checkBox2 qlb sum7 sq7 Tlo7 Thi7 (Nat.mul 5 (Nat.mul G G)) lo7 h7 lo8 h8) then
              checkX6 qlb sum6 sq6 R6pos G lo6 hi6 lo7 hi7 lo8 hi8 Tlo6 Thi6 rest
            else
              let sub := filterPartners R6pos x6 h7 rest
              match sub with
              | [] => checkX6 qlb sum6 sq6 R6pos G lo6 hi6 lo7 hi7 lo8 hi8 Tlo6 Thi6 rest
              | [_] => checkX6 qlb sum6 sq6 R6pos G lo6 hi6 lo7 hi7 lo8 hi8 Tlo6 Thi6 rest
              | top7 :: top8 :: _ =>
                if or (Nat.blt top7 lo7) (or (Nat.blt (Nat.add top7 top8) Tlo7) (Nat.blt (Nat.add sq7 (Nat.add (Nat.mul top7 top7) (Nat.mul top8 top8))) qlb)) then
                  checkX6 qlb sum6 sq6 R6pos G lo6 hi6 lo7 hi7 lo8 hi8 Tlo6 Thi6 rest
                else if checkX7 qlb sum7 sq7 R6pos G x6 lo7 h8 Tlo7 Thi7 sub then
                  checkX6 qlb sum6 sq6 R6pos G lo6 hi6 lo7 hi7 lo8 hi8 Tlo6 Thi6 rest
                else false

-- Sound fixed version: uses Gin (from P_{k-1}) for a_{k-1} - a_k, G (from P_k) for a_k..a_8,
-- underflow-free Thi, and g(0..6)-proven lower bounds l5=5, l4=8, l3=14, l2=23, l1=24!
private def solveK6 (qlb a0 a1 a2 a3 a4 a5 sum6 sq6 R6 Gin : Nat) : Bool :=
  let R6pos := Nat.div R6 (Nat.pow 256 sum6)
  if not (Nat.beq (Nat.mod R6pos 256) 64) then true
  else
    let G := findG R6pos Gin
    let s3 := Nat.add a0 (Nat.add a1 a2)
    let s4 := Nat.add s3 a3
    let s5 := Nat.add s4 a4
    let s6 := Nat.add s5 a5
    let h6 := nmin (Nat.sub a5 (nmax 1 Gin)) (nmin (Nat.sub a4 2) (nmin (Nat.sub a3 4) (nmin (Nat.sub a2 7) (nmin (Nat.sub a1 13) (Nat.sub a0 22)))))
    let h7 := nmin (Nat.sub h6 (nmax 1 G)) (nmin (Nat.sub a5 2) (nmin (Nat.sub a4 4) (nmin (Nat.sub a3 7) (nmin (Nat.sub a2 13) (Nat.sub a1 22)))))
    let h8 := nmin (Nat.sub h7 (nmax 1 G)) (nmin (Nat.sub a5 4) (nmin (Nat.sub a4 7) (nmin (Nat.sub a3 13) (Nat.sub a2 22))))
    let l8 := nmax 1 G
    let l7 := nmax (nmax 2 (Nat.mul 2 G)) (Nat.add l8 (nmax 1 G))
    let l6 := nmax (nmax 4 (Nat.mul 4 G)) (Nat.add l7 (nmax 1 G))
    if or (Nat.blt h6 l6) (or (Nat.blt h7 l7) (Nat.blt h8 l8)) then true
    else
      let h6 := skipHi R6pos l6 h6
      let l8 := skipLo R6pos l8 h8
      let h7 := skipHi R6pos l7 (nmin h7 (Nat.sub h6 (nmax 1 G)))
      let l7 := skipLo R6pos (nmax l7 (Nat.add l8 (nmax 1 G))) h7
      let h8 := skipHi R6pos l8 (nmin h8 (Nat.sub h7 (nmax 1 G)))
      let l6 := skipLo R6pos (nmax l6 (Nat.add l7 (nmax 1 G))) h6
      if or (Nat.blt h6 l6) (or (Nat.blt h7 l7) (Nat.blt h8 l8)) then true
      else
        let Tlo := nmax (Nat.sub 511 sum6) (Nat.mul 7 G)
        let Thi := nmin (Nat.add h6 (Nat.add h7 h8))
                   (nmin (Nat.sub s3 83)
                   (nmin (Nat.sub (Nat.sub s4 125) a5)
                   (nmin (Nat.sub (Nat.sub s5 251) a5)
                   (nmin (Nat.sub s5 335) (Nat.sub s6 419)))))
        if Nat.blt Thi Tlo then true
        else
          let maxQ := Nat.add sq6 (Nat.add (Nat.mul h6 h6) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8)))
          if Nat.blt maxQ qlb then true
          else if Nat.blt (Nat.mul 9 maxQ) (Nat.add 42863 (Nat.mul (Nat.add sum6 Tlo) (Nat.add sum6 Tlo))) then true
          else if not (checkBox3 qlb sum6 sq6 Tlo Thi (Nat.mul 21 (Nat.mul G G)) l6 h6 l7 h7 l8 h8) then true
          else
            let cand := collectAliveDesc R6pos l8 h6
            checkX6 qlb sum6 sq6 R6pos G l6 h6 l7 h7 l8 h8 Tlo Thi cand

private def loopK5 (qlb a0 a1 a2 a3 a4 sum5 sq5 R5 R5pos G l6 h6 l7 h7 l8 h8 : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, a5 =>
    let nh6 := nmin h6 (Nat.sub a5 (nmax 1 G))
    let nh7 := nmin h7 (Nat.sub nh6 (nmax 1 G))
    let nh8 := nmin h8 (Nat.sub nh7 (nmax 1 G))
    if or (Nat.blt nh6 l6) (or (Nat.blt nh7 l7) (Nat.blt nh8 l8)) then true
    else
      let sum6 := Nat.add sum5 a5
      let sq6 := Nat.add sq5 (Nat.mul a5 a5)
      let maxQ := Nat.add sq6 (Nat.add (Nat.mul nh6 nh6) (Nat.add (Nat.mul nh7 nh7) (Nat.mul nh8 nh8)))
      if Nat.blt maxQ qlb then true
      else
        let s3 := Nat.add a0 (Nat.add a1 a2)
        let s4 := Nat.add s3 a3
        let s5 := Nat.add s4 a4
        let Thi6 := nmin (Nat.add nh6 (Nat.add nh7 nh8))
                    (nmin (Nat.sub s3 83)
                    (nmin (Nat.sub (Nat.sub s4 125) a5)
                    (nmin (Nat.sub (Nat.sub s5 251) a5)
                    (nmin (Nat.sub s5 335) (Nat.sub (Nat.add s5 a5) 419)))))
        let Tlo6 := nmax (Nat.sub 511 sum6) (Nat.mul 7 G)
        let okCur :=
          if Nat.blt Thi6 Tlo6 then true
          else if not (okSQ qlb (Nat.add sum6 Tlo6) maxQ) then true
          else if not (checkBox3 qlb sum6 sq6 Tlo6 Thi6 (Nat.mul 21 (Nat.mul G G)) l6 nh6 l7 nh7 l8 nh8) then true
          else if testPos R5pos a5 then true
          else solveK6 qlb a0 a1 a2 a3 a4 a5 sum6 sq6 (updR R5 a5) G
        if okCur then loopK5 qlb a0 a1 a2 a3 a4 sum5 sq5 R5 R5pos G l6 h6 l7 h7 l8 h8 fuel (Nat.sub a5 1)
        else false

private def solveK5 (qlb a0 a1 a2 a3 a4 sum5 sq5 R5 Gin : Nat) : Bool :=
  let R5pos := Nat.div R5 (Nat.pow 256 sum5)
  if not (Nat.beq (Nat.mod R5pos 256) 32) then true
  else
    let G := findG R5pos Gin
    let s3 := Nat.add a0 (Nat.add a1 a2)
    let s4 := Nat.add s3 a3
    let s5 := Nat.add s4 a4
    let h5 := nmin (Nat.sub a4 (nmax 1 Gin)) (nmin (Nat.sub a3 2) (nmin (Nat.sub a2 4) (nmin (Nat.sub a1 7) (Nat.sub a0 13))))
    let h6 := nmin (Nat.sub h5 (nmax 1 G)) (nmin (Nat.sub a4 2) (nmin (Nat.sub a3 4) (nmin (Nat.sub a2 7) (nmin (Nat.sub a1 13) (Nat.sub a0 22)))))
    let h7 := nmin (Nat.sub h6 (nmax 1 G)) (nmin (Nat.sub a4 4) (nmin (Nat.sub a3 7) (nmin (Nat.sub a2 13) (Nat.sub a1 22))))
    let h8 := nmin (Nat.sub h7 (nmax 1 G)) (nmin (Nat.sub a4 7) (nmin (Nat.sub a3 13) (Nat.sub a2 22)))
    let l8 := nmax 1 G
    let l7 := nmax (nmax 2 (Nat.mul 2 G)) (Nat.add l8 (nmax 1 G))
    let l6 := nmax (nmax 4 (Nat.mul 4 G)) (Nat.add l7 (nmax 1 G))
    let l5 := nmax 5 (Nat.add l6 (nmax 1 G))
    if or (Nat.blt h5 l5) (or (Nat.blt h6 l6) (or (Nat.blt h7 l7) (Nat.blt h8 l8))) then true
    else
      let h5 := skipHi R5pos l5 h5
      let l8 := skipLo R5pos l8 h8
      let h6 := skipHi R5pos l6 (nmin h6 (Nat.sub h5 (nmax 1 G)))
      let h7 := skipHi R5pos l7 (nmin h7 (Nat.sub h6 (nmax 1 G)))
      let h8 := skipHi R5pos l8 (nmin h8 (Nat.sub h7 (nmax 1 G)))
      let l7 := skipLo R5pos (nmax l7 (Nat.add l8 (nmax 1 G))) h7
      let l6 := skipLo R5pos (nmax l6 (Nat.add l7 (nmax 1 G))) h6
      let l5 := skipLo R5pos (nmax l5 (Nat.add l6 (nmax 1 G))) h5
      if or (Nat.blt h5 l5) (or (Nat.blt h6 l6) (or (Nat.blt h7 l7) (Nat.blt h8 l8))) then true
      else
        let Tlo := nmax (Nat.sub 511 sum5) (Nat.mul 15 G)
        let Thi := nmin (Nat.add h5 (Nat.add h6 (Nat.add h7 h8)))
                   (nmin (Nat.sub s4 125)
                   (nmin (Nat.sub s5 251)
                   (nmin (Nat.sub (Nat.add s3 h5) 83)
                   (nmin (Nat.sub (Nat.add s5 h5) 335) (Nat.sub (Nat.add s5 (Nat.mul 2 h5)) 419)))))
        if Nat.blt Thi Tlo then true
        else
          let maxQ := Nat.add sq5 (Nat.add (Nat.mul h5 h5) (Nat.add (Nat.mul h6 h6) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8))))
          if Nat.blt maxQ qlb then true
          else if Nat.blt (Nat.mul 9 maxQ) (Nat.add 42863 (Nat.mul (Nat.add sum5 Tlo) (Nat.add sum5 Tlo))) then true
          else if not (checkBox4 qlb sum5 sq5 Tlo Thi (Nat.mul 85 (Nat.mul G G)) l5 h5 l6 h6 l7 h7 l8 h8) then true
          else loopK5 qlb a0 a1 a2 a3 a4 sum5 sq5 R5 R5pos G l6 h6 l7 h7 l8 h8 (Nat.add (Nat.sub h5 l5) 1) h5

private def loopK4 (qlb a0 a1 a2 a3 sum4 sq4 R4 R4pos G l5 h5 l6 h6 l7 h7 l8 h8 : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, a4 =>
    let nh5 := nmin h5 (Nat.sub a4 (nmax 1 G))
    let nh6 := nmin h6 (Nat.sub nh5 (nmax 1 G))
    let nh7 := nmin h7 (Nat.sub nh6 (nmax 1 G))
    let nh8 := nmin h8 (Nat.sub nh7 (nmax 1 G))
    if or (Nat.blt nh5 l5) (or (Nat.blt nh6 l6) (or (Nat.blt nh7 l7) (Nat.blt nh8 l8))) then true
    else
      let sum5 := Nat.add sum4 a4
      let sq5 := Nat.add sq4 (Nat.mul a4 a4)
      let maxQ := Nat.add sq5 (Nat.add (Nat.mul nh5 nh5) (Nat.add (Nat.mul nh6 nh6) (Nat.add (Nat.mul nh7 nh7) (Nat.mul nh8 nh8))))
      if Nat.blt maxQ qlb then true
      else
        let s3 := Nat.add a0 (Nat.add a1 a2)
        let s4 := Nat.add s3 a3
        let s5 := Nat.add s4 a4
        let Thi5 := nmin (Nat.add nh5 (Nat.add nh6 (Nat.add nh7 nh8)))
                    (nmin (Nat.sub s4 125)
                    (nmin (Nat.sub s5 251)
                    (nmin (Nat.sub (Nat.add s3 nh5) 83)
                    (nmin (Nat.sub (Nat.add s5 nh5) 335) (Nat.sub (Nat.add s5 (Nat.mul 2 nh5)) 419)))))
        let Tlo5 := nmax (Nat.sub 511 sum5) (Nat.mul 15 G)
        let okCur :=
          if Nat.blt Thi5 Tlo5 then true
          else if not (okSQ qlb (Nat.add sum5 Tlo5) maxQ) then true
          else if not (checkBox4 qlb sum5 sq5 Tlo5 Thi5 (Nat.mul 85 (Nat.mul G G)) l5 nh5 l6 nh6 l7 nh7 l8 nh8) then true
          else if testPos R4pos a4 then true
          else solveK5 qlb a0 a1 a2 a3 a4 sum5 sq5 (updR R4 a4) G
        if okCur then loopK4 qlb a0 a1 a2 a3 sum4 sq4 R4 R4pos G l5 h5 l6 h6 l7 h7 l8 h8 fuel (Nat.sub a4 1)
        else false

private def solveK4 (qlb a0 a1 a2 a3 sum4 sq4 R4 Gin : Nat) : Bool :=
  let R4pos := Nat.div R4 (Nat.pow 256 sum4)
  if not (Nat.beq (Nat.mod R4pos 256) 16) then true
  else
    let G := findG R4pos Gin
    let s3 := Nat.add a0 (Nat.add a1 a2)
    let s4 := Nat.add s3 a3
    let h4 := nmin (Nat.sub a3 (nmax 1 Gin)) (nmin (Nat.sub a2 2) (nmin (Nat.sub a1 4) (Nat.sub a0 7)))
    let h5 := nmin (Nat.sub h4 (nmax 1 G)) (nmin (Nat.sub a3 2) (nmin (Nat.sub a2 4) (nmin (Nat.sub a1 7) (Nat.sub a0 13))))
    let h6 := nmin (Nat.sub h5 (nmax 1 G)) (nmin (Nat.sub a3 4) (nmin (Nat.sub a2 7) (nmin (Nat.sub a1 13) (Nat.sub a0 22))))
    let h7 := nmin (Nat.sub h6 (nmax 1 G)) (nmin (Nat.sub a3 7) (nmin (Nat.sub a2 13) (Nat.sub a1 22)))
    let h8 := nmin (Nat.sub h7 (nmax 1 G)) (nmin (Nat.sub a3 13) (Nat.sub a2 22))
    let l8 := nmax 1 G
    let l7 := nmax (nmax 2 (Nat.mul 2 G)) (Nat.add l8 (nmax 1 G))
    let l6 := nmax (nmax 4 (Nat.mul 4 G)) (Nat.add l7 (nmax 1 G))
    let l5 := nmax 5 (Nat.add l6 (nmax 1 G))
    let l4 := nmax 8 (Nat.add l5 (nmax 1 G))
    if or (Nat.blt h4 l4) (or (Nat.blt h5 l5) (or (Nat.blt h6 l6) (or (Nat.blt h7 l7) (Nat.blt h8 l8)))) then true
    else
      let h4 := skipHi R4pos l4 h4
      let l8 := skipLo R4pos l8 h8
      let h5 := skipHi R4pos l5 (nmin h5 (Nat.sub h4 (nmax 1 G)))
      let h6 := skipHi R4pos l6 (nmin h6 (Nat.sub h5 (nmax 1 G)))
      let h7 := skipHi R4pos l7 (nmin h7 (Nat.sub h6 (nmax 1 G)))
      let h8 := skipHi R4pos l8 (nmin h8 (Nat.sub h7 (nmax 1 G)))
      let l7 := skipLo R4pos (nmax l7 (Nat.add l8 (nmax 1 G))) h7
      let l6 := skipLo R4pos (nmax l6 (Nat.add l7 (nmax 1 G))) h6
      let l5 := skipLo R4pos (nmax l5 (Nat.add l6 (nmax 1 G))) h5
      let l4 := skipLo R4pos (nmax l4 (Nat.add l5 (nmax 1 G))) h4
      if or (Nat.blt h4 l4) (or (Nat.blt h5 l5) (or (Nat.blt h6 l6) (or (Nat.blt h7 l7) (Nat.blt h8 l8)))) then true
      else
        let Tlo := nmax (Nat.sub 511 sum4) (Nat.mul 31 G)
        let Thi := nmin (Nat.add h4 (Nat.add h5 (Nat.add h6 (Nat.add h7 h8))))
                   (nmin (Nat.sub (Nat.add s4 h4) 125)
                   (nmin (Nat.sub (Nat.add s4 (Nat.mul 2 h4)) 251)
                   (nmin (Nat.sub (Nat.add s3 (Nat.add h4 h5)) 83)
                   (nmin (Nat.sub (Nat.add s4 (Nat.add (Nat.mul 2 h4) h5)) 335)
                         (Nat.sub (Nat.add s4 (Nat.add (Nat.mul 2 h4) (Nat.mul 2 h5))) 419)))))
        if Nat.blt Thi Tlo then true
        else
          let maxQ := Nat.add sq4 (Nat.add (Nat.mul h4 h4) (Nat.add (Nat.mul h5 h5) (Nat.add (Nat.mul h6 h6) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8)))))
          if Nat.blt maxQ qlb then true
          else if not (checkBox5 qlb sum4 sq4 Tlo Thi (Nat.mul 341 (Nat.mul G G)) l4 h4 l5 h5 l6 h6 l7 h7 l8 h8) then true
          else loopK4 qlb a0 a1 a2 a3 sum4 sq4 R4 R4pos G l5 h5 l6 h6 l7 h7 l8 h8 (Nat.add (Nat.sub h4 l4) 1) h4

private def loopK3 (qlb a0 a1 a2 sum3 sq3 R3 R3pos G : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, a3 =>
    let h4 := nmin (Nat.sub a3 (nmax 1 G)) (nmin (Nat.sub a2 2) (nmin (Nat.sub a1 4) (Nat.sub a0 7)))
    let h5 := nmin (Nat.sub h4 (nmax 1 G)) (nmin (Nat.sub a2 4) (nmin (Nat.sub a1 7) (Nat.sub a0 13)))
    let h6 := nmin (Nat.sub h5 (nmax 1 G)) (nmin (Nat.sub a2 7) (nmin (Nat.sub a1 13) (Nat.sub a0 22)))
    let h7 := nmin (Nat.sub h6 (nmax 1 G)) (nmin (Nat.sub a2 13) (Nat.sub a1 22))
    let h8 := nmin (Nat.sub h7 (nmax 1 G)) (Nat.sub a2 22)
    let sum4 := Nat.add sum3 a3
    let sq4 := Nat.add sq3 (Nat.mul a3 a3)
    let maxQ := Nat.add sq4 (Nat.add (Nat.mul h4 h4) (Nat.add (Nat.mul h5 h5) (Nat.add (Nat.mul h6 h6) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8)))))
    if Nat.blt maxQ qlb then true
    else
      let Tlo := nmax (Nat.sub 511 sum4) (Nat.mul 31 G)
      let Thi := nmin (Nat.add h4 (Nat.add h5 (Nat.add h6 (Nat.add h7 h8))))
                 (nmin (Nat.sub (Nat.add sum4 h4) 125)
                 (nmin (Nat.sub (Nat.add sum4 (Nat.mul 2 h4)) 251)
                 (nmin (Nat.sub (Nat.add sum3 (Nat.add h4 h5)) 83)
                 (nmin (Nat.sub (Nat.add sum4 (Nat.add (Nat.mul 2 h4) h5)) 335)
                       (Nat.sub (Nat.add sum4 (Nat.add (Nat.mul 2 h4) (Nat.mul 2 h5))) 419)))))
      let okCur :=
        if Nat.blt Thi Tlo then true
        else if not (okSQ qlb (Nat.add sum4 Tlo) maxQ) then true
        else if testPos R3pos a3 then true
        else solveK4 qlb a0 a1 a2 a3 sum4 sq4 (updR R3 a3) G
      if okCur then loopK3 qlb a0 a1 a2 sum3 sq3 R3 R3pos G fuel (Nat.sub a3 1)
      else false

private def solveK3 (qlb a0 a1 a2 sum3 sq3 R3 Gin : Nat) : Bool :=
  let R3pos := Nat.div R3 (Nat.pow 256 sum3)
  if not (Nat.beq (Nat.mod R3pos 256) 8) then true
  else
    let G := findG R3pos Gin
    let h3 := nmin (Nat.sub a2 (nmax 1 Gin)) (nmin (Nat.sub a1 2) (Nat.sub a0 4))
    let h4 := nmin (Nat.sub h3 (nmax 1 G)) (nmin (Nat.sub a2 2) (nmin (Nat.sub a1 4) (Nat.sub a0 7)))
    let h5 := nmin (Nat.sub h4 (nmax 1 G)) (nmin (Nat.sub a2 4) (nmin (Nat.sub a1 7) (Nat.sub a0 13)))
    let h6 := nmin (Nat.sub h5 (nmax 1 G)) (nmin (Nat.sub a2 7) (nmin (Nat.sub a1 13) (Nat.sub a0 22)))
    let h7 := nmin (Nat.sub h6 (nmax 1 G)) (nmin (Nat.sub a2 13) (Nat.sub a1 22))
    let h8 := nmin (Nat.sub h7 (nmax 1 G)) (Nat.sub a2 22)
    let l8 := nmax 1 G
    let l7 := nmax (nmax 2 (Nat.mul 2 G)) (Nat.add l8 (nmax 1 G))
    let l6 := nmax (nmax 4 (Nat.mul 4 G)) (Nat.add l7 (nmax 1 G))
    let l5 := nmax 5 (Nat.add l6 (nmax 1 G))
    let l4 := nmax 8 (Nat.add l5 (nmax 1 G))
    let l3 := nmax 14 (Nat.add l4 (nmax 1 G))
    if Nat.blt h3 l3 then true
    else
      let Tlo := nmax (Nat.sub 511 sum3) (Nat.mul 63 G)
      let Thi := nmin (Nat.add h3 (Nat.add h4 (Nat.add h5 (Nat.add h6 (Nat.add h7 h8)))))
                      (Nat.sub (Nat.add sum3 (Nat.add h3 (Nat.add h4 h5))) 83)
      if Nat.blt Thi Tlo then true
      else
        let maxQ := Nat.add sq3 (Nat.add (Nat.mul h3 h3) (Nat.add (Nat.mul h4 h4) (Nat.add (Nat.mul h5 h5) (Nat.add (Nat.mul h6 h6) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8))))))
        if not (okSQ qlb (Nat.add sum3 Tlo) maxQ) then true
        else loopK3 qlb a0 a1 a2 sum3 sq3 R3 R3pos G (Nat.add (Nat.sub h3 l3) 1) h3

private def loopK2 (qlb a0 a1 sum2 sq2 R2 R2pos G : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, a2 =>
    let h3 := nmin (Nat.sub a2 1) (nmin (Nat.sub a1 2) (Nat.sub a0 4))
    let h4 := nmin (Nat.sub h3 1) (nmin (Nat.sub a1 4) (Nat.sub a0 7))
    let h5 := nmin (Nat.sub h4 1) (nmin (Nat.sub a1 7) (Nat.sub a0 13))
    let h6 := nmin (Nat.sub h5 1) (nmin (Nat.sub a1 13) (Nat.sub a0 22))
    let h7 := nmin (Nat.sub h6 1) (Nat.sub a1 22)
    let h8 := nmin (Nat.sub h7 1) (Nat.sub a2 22)
    let maxQ := Nat.add (Nat.add sq2 (Nat.mul a2 a2)) (Nat.add (Nat.mul h3 h3) (Nat.add (Nat.mul h4 h4) (Nat.add (Nat.mul h5 h5) (Nat.add (Nat.mul h6 h6) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8))))))
    if Nat.blt maxQ qlb then true
    else
      let okCur :=
        if testPos R2pos a2 then true
        else solveK3 qlb a0 a1 a2 (Nat.add sum2 a2) (Nat.add sq2 (Nat.mul a2 a2)) (updR R2 a2) G
      if okCur then loopK2 qlb a0 a1 sum2 sq2 R2 R2pos G fuel (Nat.sub a2 1)
      else false

private def loopK1 (qlb a0 R1 : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, a1 =>
    let h2 := nmin (Nat.sub a1 1) (Nat.sub a0 2)
    let h3 := nmin (Nat.sub h2 1) (Nat.sub a0 4)
    let h4 := nmin (Nat.sub h3 1) (Nat.sub a0 7)
    let h5 := nmin (Nat.sub h4 1) (Nat.sub a0 13)
    let h6 := nmin (Nat.sub h5 1) (Nat.sub a0 22)
    let h7 := nmin (Nat.sub h6 1) (Nat.sub a1 22)
    let h8 := Nat.sub h7 1
    let maxQ := Nat.add (Nat.add (Nat.mul a0 a0) (Nat.mul a1 a1)) (Nat.add (Nat.mul h2 h2) (Nat.add (Nat.mul h3 h3) (Nat.add (Nat.mul h4 h4) (Nat.add (Nat.mul h5 h5) (Nat.add (Nat.mul h6 h6) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8)))))))
    if Nat.blt maxQ qlb then true
    else
      let R2 := updR R1 a1
      let sum2 := Nat.add a0 a1
      let R2pos := Nat.div R2 (Nat.pow 256 sum2)
      let G := findG R2pos 1
      let l2 := 23
      let okCur := if Nat.blt h2 l2 then true else loopK2 qlb a0 a1 sum2 (Nat.add (Nat.mul a0 a0) (Nat.mul a1 a1)) R2 R2pos G (Nat.add (Nat.sub h2 l2) 1) h2
      if okCur then loopK1 qlb a0 R1 fuel (Nat.sub a1 1)
      else false

private def solveA0 (a0 qlb : Nat) : Bool :=
  let R1 := updR 1 a0
  let h1 := Nat.sub a0 1
  let l1 := 24
  if Nat.blt h1 l1 then true
  else loopK1 qlb a0 R1 (Nat.add (Nat.sub h1 l1) 1) h1


-- Soundness proof section for Part2KronSound (to be appended to /tmp/part2_kron_sound.lean
-- once the fixed solver timing is verified, and merged into R2.H1.R1.lean).

-- 2A. Kronecker R_k polynomial identity & base-256 unique digit extraction

private def kronS (k : ℕ) (hk : k ≤ 9) (a : Fin 9 → ℕ) : ℕ :=
  ∑ U : Finset (Fin k), 256 ^ (∑ i ∈ U, a ⟨i.val, by omega⟩)

private def kronR (k : ℕ) (hk : k ≤ 9) (a : Fin 9 → ℕ) : ℕ :=
  (kronS k hk a) ^ 2

private lemma updR_eq (R v : ℕ) : updR R v = R * (1 + 256 ^ v) ^ 2 := by
  unfold updR
  change (R + R * 256 ^ v) + (R + R * 256 ^ v) * 256 ^ v = R * (1 + 256 ^ v) ^ 2
  ring

private lemma kronR_zero (a : Fin 9 → ℕ) : kronR 0 (by omega) a = 1 := by
  simp [kronR, kronS]

private lemma sq_le_mul_of_le {x y : ℕ} (h : x ≤ y) : x ^ 2 ≤ y * y := by
  rw [sq]; exact Nat.mul_le_mul h h

private lemma kronR_succ {k : ℕ} (hk : k < 9) (a : Fin 9 → ℕ) :
    kronR (k + 1) (by omega) a = updR (kronR k (by omega) a) (a ⟨k, hk⟩) := by
  rw [updR_eq, kronR, kronR, ← mul_pow]
  congr 1
  unfold kronS
  let lastIdx : Fin (k + 1) := ⟨k, by omega⟩
  let emb : Fin k ↪ Fin (k + 1) :=
    ⟨fun i => ⟨i.val, by omega⟩, fun i j h => Fin.ext (by simpa [Fin.ext_iff] using h)⟩
  have hsplit := (sum_filter_add_sum_filter_not (s := (univ : Finset (Finset (Fin (k + 1)))))
    (p := fun U => lastIdx ∈ U) (f := fun U => 256 ^ (∑ i ∈ U, a ⟨i.val, by omega⟩))).symm
  rw [hsplit]
  have hnot_mem : ∀ U : Finset (Fin k), lastIdx ∉ U.map emb := by
    intro U hm; rcases mem_map.mp hm with ⟨i, _, hi⟩
    have hiLt := i.isLt
    have hval := congrArg Fin.val hi; change i.val = k at hval; omega
  have h0 : ∑ U ∈ (univ : Finset (Finset (Fin (k + 1)))).filter (fun U => lastIdx ∉ U),
      256 ^ (∑ i ∈ U, a ⟨i.val, by omega⟩) = ∑ U : Finset (Fin k), 256 ^ (∑ i ∈ U, a ⟨i.val, by omega⟩) := by
    refine sum_bij (fun U _ => U.preimage emb (fun x _ y _ h => emb.injective h)) (fun _ _ => mem_univ _) ?_ ?_ ?_
    · intro U hU V hV hEq
      have hUn := (mem_filter.mp hU).2
      have hVn := (mem_filter.mp hV).2
      ext j
      by_cases hjk : j = lastIdx
      · subst hjk; simp [hUn, hVn]
      · have hjlt : j.val < k := by have := j.isLt; have : j.val ≠ k := fun h => hjk (Fin.ext (by dsimp [lastIdx]; exact h)); omega
        have hemb : emb ⟨j.val, hjlt⟩ = j := Fin.ext rfl
        constructor
        · intro hjU
          have h1 : (⟨j.val, hjlt⟩ : Fin k) ∈ U.preimage emb (fun x _ y _ h => emb.injective h) :=
            Finset.mem_preimage.mpr (hemb.symm ▸ hjU)
          have h2 : (⟨j.val, hjlt⟩ : Fin k) ∈ V.preimage emb (fun x _ y _ h => emb.injective h) := hEq ▸ h1
          exact hemb ▸ Finset.mem_preimage.mp h2
        · intro hjV
          have h1 : (⟨j.val, hjlt⟩ : Fin k) ∈ V.preimage emb (fun x _ y _ h => emb.injective h) :=
            Finset.mem_preimage.mpr (hemb.symm ▸ hjV)
          have h2 : (⟨j.val, hjlt⟩ : Fin k) ∈ U.preimage emb (fun x _ y _ h => emb.injective h) := hEq.symm ▸ h1
          exact hemb ▸ Finset.mem_preimage.mp h2
    · intro S _
      refine ⟨S.map emb, mem_filter.mpr ⟨mem_univ _, hnot_mem S⟩, ?_⟩
      ext i
      constructor
      · intro hi
        rcases mem_map.mp (Finset.mem_preimage.mp hi) with ⟨j, hj, hji⟩
        exact emb.injective hji ▸ hj
      · intro hi
        exact Finset.mem_preimage.mpr (mem_map.mpr ⟨i, hi, rfl⟩)
    · intro U hU
      have hUn := (mem_filter.mp hU).2
      have hmap : (U.preimage emb (fun x _ y _ h => emb.injective h)).map emb = U := by
        ext j; rw [mem_map]
        constructor
        · rintro ⟨i, hi, rfl⟩; exact Finset.mem_preimage.mp hi
        · intro hj
          have hjlt : j.val < k := by
            have := j.isLt
            have hne : j.val ≠ k := fun h => hUn ((show j = lastIdx from Fin.ext h) ▸ hj)
            omega
          refine ⟨⟨j.val, hjlt⟩, Finset.mem_preimage.mpr ?_, Fin.ext rfl⟩
          have hemb : emb ⟨j.val, hjlt⟩ = j := Fin.ext rfl
          rwa [hemb]
      conv_lhs => rw [← hmap]
      rw [sum_map]; rfl
  have h1 : ∑ U ∈ (univ : Finset (Finset (Fin (k + 1)))).filter (fun U => lastIdx ∈ U),
      256 ^ (∑ i ∈ U, a ⟨i.val, by omega⟩) =
      (∑ U : Finset (Fin k), 256 ^ (∑ i ∈ U, a ⟨i.val, by omega⟩)) * 256 ^ (a ⟨k, hk⟩) := by
    rw [sum_mul]
    refine sum_bij (fun U _ => (U.erase lastIdx).preimage emb (fun x _ y _ h => emb.injective h))
      (fun _ _ => mem_univ _) ?_ ?_ ?_
    · intro U hU V hV hEq
      have hUm := (mem_filter.mp hU).2
      have hVm := (mem_filter.mp hV).2
      ext j
      by_cases hjk : j = lastIdx
      · subst hjk; simp [hUm, hVm]
      · have hjlt : j.val < k := by have := j.isLt; have : j.val ≠ k := fun h => hjk (Fin.ext (by dsimp [lastIdx]; exact h)); omega
        have hemb : emb ⟨j.val, hjlt⟩ = j := Fin.ext rfl
        constructor
        · intro hjU
          have h1 : (⟨j.val, hjlt⟩ : Fin k) ∈ (U.erase lastIdx).preimage emb (fun x _ y _ h => emb.injective h) :=
            Finset.mem_preimage.mpr (hemb.symm ▸ mem_erase.mpr ⟨hjk, hjU⟩)
          have h2 : (⟨j.val, hjlt⟩ : Fin k) ∈ (V.erase lastIdx).preimage emb (fun x _ y _ h => emb.injective h) := hEq ▸ h1
          exact (mem_erase.mp (hemb ▸ Finset.mem_preimage.mp h2)).2
        · intro hjV
          have h1 : (⟨j.val, hjlt⟩ : Fin k) ∈ (V.erase lastIdx).preimage emb (fun x _ y _ h => emb.injective h) :=
            Finset.mem_preimage.mpr (hemb.symm ▸ mem_erase.mpr ⟨hjk, hjV⟩)
          have h2 : (⟨j.val, hjlt⟩ : Fin k) ∈ (U.erase lastIdx).preimage emb (fun x _ y _ h => emb.injective h) := hEq.symm ▸ h1
          exact (mem_erase.mp (hemb ▸ Finset.mem_preimage.mp h2)).2
    · intro S _
      refine ⟨insert lastIdx (S.map emb), mem_filter.mpr ⟨mem_univ _, mem_insert_self _ _⟩, ?_⟩
      ext i
      constructor
      · intro hi
        have h1 := Finset.mem_preimage.mp hi
        rw [erase_insert (hnot_mem S)] at h1
        rcases mem_map.mp h1 with ⟨j, hj, hji⟩
        exact emb.injective hji ▸ hj
      · intro hi
        refine Finset.mem_preimage.mpr ?_
        rw [erase_insert (hnot_mem S)]
        exact mem_map.mpr ⟨i, hi, rfl⟩
    · intro U hU
      have hUm := (mem_filter.mp hU).2
      have hmap : ((U.erase lastIdx).preimage emb (fun x _ y _ h => emb.injective h)).map emb = U.erase lastIdx := by
        ext j; rw [mem_map, mem_erase]
        constructor
        · rintro ⟨i, hi, rfl⟩; exact mem_erase.mp (Finset.mem_preimage.mp hi)
        · rintro ⟨hne, hj⟩
          have hjlt : j.val < k := by have := j.isLt; have : j.val ≠ k := fun h => hne (Fin.ext (by dsimp [lastIdx]; exact h)); omega
          refine ⟨⟨j.val, hjlt⟩, Finset.mem_preimage.mpr (mem_erase.mpr ?_), Fin.ext rfl⟩
          have hemb : emb ⟨j.val, hjlt⟩ = j := Fin.ext rfl
          rw [hemb]; exact ⟨hne, hj⟩
      have hsum : ∑ i ∈ U, a ⟨i.val, by omega⟩ =
          (∑ i ∈ (U.erase lastIdx).preimage emb (fun x _ y _ h => emb.injective h), a ⟨i.val, by omega⟩) + a ⟨k, hk⟩ := by
        have h2 := add_sum_erase U (fun i : Fin (k + 1) => a ⟨i.val, by omega⟩) hUm
        rw [← hmap, sum_map] at h2
        change a ⟨k, hk⟩ + (∑ i ∈ (U.erase lastIdx).preimage emb (fun x _ y _ h => emb.injective h), a ⟨i.val, by omega⟩) =
          ∑ i ∈ U, a ⟨i.val, by omega⟩ at h2
        omega
      rw [hsum, pow_add]
  rw [h0, h1]; ring

private lemma base256_digit :
    ∀ (d N : ℕ) (c : ℕ → ℕ), (∀ m < N, c m < 256) →
      ((∑ m ∈ range N, c m * 256 ^ m) / 256 ^ d) % 256 = if d < N then c d else 0 := by
  intro d
  induction d with
  | zero =>
    intro N c hc
    cases N with
    | zero => simp
    | succ N' =>
      rw [pow_zero, Nat.div_one, sum_range_succ']
      have htail : ∑ m ∈ range N', c (m + 1) * 256 ^ (m + 1) = (∑ m ∈ range N', c (m + 1) * 256 ^ m) * 256 := by
        rw [sum_mul]; refine sum_congr rfl fun m _ => ?_; rw [pow_succ]; ring
      rw [htail, pow_zero, mul_one, add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (hc 0 (by omega))]
      simp
  | succ d ih =>
    intro N c hc
    cases N with
    | zero => simp
    | succ N' =>
      rw [pow_succ', ← Nat.div_div_eq_div_mul, sum_range_succ']
      have htail : ∑ m ∈ range N', c (m + 1) * 256 ^ (m + 1) = (∑ m ∈ range N', c (m + 1) * 256 ^ m) * 256 := by
        rw [sum_mul]; refine sum_congr rfl fun m _ => ?_; rw [pow_succ]; ring
      rw [htail, pow_zero, mul_one, add_comm, Nat.add_mul_div_right _ _ (by decide : 0 < 256),
          Nat.div_eq_of_lt (hc 0 (by omega)), zero_add]
      have hrec := ih N' (fun m => c (m + 1)) (fun m hm => hc (m + 1) (by omega))
      rw [hrec]
      by_cases hlt : d < N'
      · simp [hlt, show d + 1 < N' + 1 by omega]
      · simp [hlt, show ¬ (d + 1 < N' + 1) by omega]

private lemma kronR_digit {k : ℕ} (hk6 : k ≤ 6) {a : Fin 9 → ℕ}
    (hinj : Function.Injective (fun U : Finset (Fin 9) => ∑ i ∈ U, a i)) :
    let sumk := ∑ i : Fin k, a ⟨i.val, by omega⟩
    let Rpos := kronR k (by omega) a / 256 ^ sumk
    Rpos % 256 = 2 ^ k ∧
    ∀ d : ℕ, testPos Rpos d = true ↔
      ∃ S T : Finset (Fin k), ∑ i ∈ S, a ⟨i.val, by omega⟩ = (∑ i ∈ T, a ⟨i.val, by omega⟩) + d := by
  classical
  intro sumk Rpos
  let f : Finset (Fin k) → ℕ := fun U => ∑ i ∈ U, a ⟨i.val, by omega⟩
  have hfinj : Function.Injective f := by
    intro S T hEq
    let emb : Fin k ↪ Fin 9 := ⟨fun i => ⟨i.val, by omega⟩, fun x y h => Fin.ext (by simpa [Fin.ext_iff] using h)⟩
    have h1 : ∑ i ∈ S.map emb, a i = ∑ i ∈ T.map emb, a i := by rw [sum_map, sum_map]; exact hEq
    have h2 := hinj h1
    ext i
    have : emb i ∈ S.map emb ↔ emb i ∈ T.map emb := by rw [h2]
    simpa [mem_map] using this
  have hfle : ∀ U : Finset (Fin k), f U ≤ sumk := fun U => sum_le_sum_of_subset (subset_univ U)
  have hcomp : ∀ U : Finset (Fin k), f (univ \ U) = sumk - f U := fun U => by
    have := sum_sdiff (subset_univ U) (f := fun i : Fin k => a ⟨i.val, by omega⟩)
    dsimp [f, sumk] at *; omega
  have hS_comp : kronS k (by omega) a = ∑ T : Finset (Fin k), 256 ^ (sumk - f T) := by
    unfold kronS
    refine sum_bij (fun U _ => univ \ U) (fun _ _ => mem_univ _) ?_ ?_ ?_
    · intro U _ V _ h
      have h1 : univ \ (univ \ U) = univ \ (univ \ V) := congrArg (univ \ ·) h
      simpa [Finset.sdiff_sdiff_eq_self (subset_univ U), Finset.sdiff_sdiff_eq_self (subset_univ V)] using h1
    · intro V _; exact ⟨univ \ V, mem_univ _, Finset.sdiff_sdiff_eq_self (subset_univ V)⟩
    · intro U _
      have hc := hcomp (univ \ U)
      rw [Finset.sdiff_sdiff_eq_self (subset_univ U)] at hc
      change 256 ^ f U = 256 ^ (sumk - f (univ \ U))
      rw [hc]
  let idx : Finset (Fin k) × Finset (Fin k) → ℕ := fun p => sumk + f p.1 - f p.2
  have hR_prod : kronR k (by omega) a = ∑ p ∈ (univ : Finset (Finset (Fin k))) ×ˢ (univ : Finset (Finset (Fin k))),
      256 ^ idx p := by
    rw [kronR, sq]
    conv_lhs => arg 2; rw [hS_comp]
    rw [kronS, sum_mul_sum, ← sum_product']
    refine sum_congr rfl fun p _ => ?_
    rw [← pow_add]
    have h2 : f p.2 ≤ sumk := hfle p.2
    congr 1; change f p.1 + (sumk - f p.2) = sumk + f p.1 - f p.2; omega
  let N := 2 * sumk + 1
  let cnt : ℕ → ℕ := fun m => (((univ : Finset (Finset (Fin k))) ×ˢ (univ : Finset (Finset (Fin k)))).filter (fun p => idx p = m)).card
  have hR_sum : kronR k (by omega) a = ∑ m ∈ range N, cnt m * 256 ^ m := by
    rw [hR_prod]
    rw [← sum_fiberwise_of_maps_to (g := idx) (t := range N) (fun p _ => by
      rw [mem_range]; have h1 := hfle p.1; dsimp [idx, N]; omega)]
    refine sum_congr rfl fun m _ => ?_
    have hconst : ∀ p ∈ ((univ : Finset (Finset (Fin k))) ×ˢ (univ : Finset (Finset (Fin k)))).filter (fun p => idx p = m),
        256 ^ idx p = 256 ^ m := fun p hp => by rw [(mem_filter.mp hp).2]
    rw [sum_congr rfl hconst, sum_const, smul_eq_mul]
  have hcnt_lt : ∀ m < N, cnt m < 256 := by
    intro m _
    let F := ((univ : Finset (Finset (Fin k))) ×ˢ (univ : Finset (Finset (Fin k)))).filter (fun p => idx p = m)
    have hinj_fst : Set.InjOn Prod.fst (F : Set (Finset (Fin k) × Finset (Fin k))) := by
      intro p1 hp1 p2 hp2 hEq
      have hm1 := (mem_filter.mp hp1).2
      have hm2 := (mem_filter.mp hp2).2
      have hf1 := hfle p1.2; have hf2 := hfle p2.2
      have heq_f2 : f p1.2 = f p2.2 := by dsimp [idx] at hm1 hm2; rw [hEq] at hm1; omega
      exact Prod.ext hEq (hfinj heq_f2)
    have hle : F.card ≤ (univ : Finset (Finset (Fin k))).card := by
      rw [← card_image_of_injOn hinj_fst]
      exact card_le_card (subset_univ _)
    have hcard_u : (univ : Finset (Finset (Fin k))).card = 2 ^ k := by simp
    have h2k : 2 ^ k < 256 := by
      have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hcnt_eq : cnt m = F.card := rfl
    rw [hcnt_eq]; rw [hcard_u] at hle; omega
  have hdig : ∀ d : ℕ, (Rpos / 256 ^ d) % 256 = if sumk + d < N then cnt (sumk + d) else 0 := by
    intro d
    dsimp [Rpos]
    rw [Nat.div_div_eq_div_mul, ← pow_add, hR_sum]
    exact base256_digit (sumk + d) N cnt hcnt_lt
  constructor
  · have h0 := hdig 0
    rw [pow_zero, Nat.div_one, add_zero, if_pos (by dsimp [N]; omega)] at h0
    rw [h0]
    have hcard_eq : cnt sumk = (univ : Finset (Finset (Fin k))).card := by
      refine card_bij (fun p _ => p.1) (fun _ _ => mem_univ _) ?_ ?_
      · intro p1 hp1 p2 hp2 hEq
        have hm1 := (mem_filter.mp hp1).2
        have hm2 := (mem_filter.mp hp2).2
        have hf1 := hfle p1.2; have hf2 := hfle p2.2
        have hp1e : p1.1 = p1.2 := hfinj (by dsimp [idx] at hm1; omega)
        have hp2e : p2.1 = p2.2 := hfinj (by dsimp [idx] at hm2; omega)
        exact Prod.ext hEq (hp1e.symm.trans (hEq.trans hp2e))
      · intro S _
        refine ⟨(S, S), mem_filter.mpr ⟨mem_product.mpr ⟨mem_univ _, mem_univ _⟩, ?_⟩, rfl⟩
        have := hfle S; dsimp [idx]; omega
    rw [hcard_eq]; simp
  · intro d
    unfold testPos
    change Nat.blt 0 ((Rpos / 256 ^ d) % 256) = true ↔ _
    rw [Nat.blt_eq, hdig d]
    by_cases hlt : sumk + d < N
    · rw [if_pos hlt]
      dsimp [cnt]
      rw [card_pos]
      constructor
      · rintro ⟨⟨S, T⟩, hST⟩
        have hm := (mem_filter.mp hST).2
        have hT := hfle T
        exact ⟨S, T, by dsimp [idx, f] at hm hT ⊢; omega⟩
      · rintro ⟨S, T, hEq⟩
        refine ⟨(S, T), mem_filter.mpr ⟨mem_product.mpr ⟨mem_univ _, mem_univ _⟩, ?_⟩⟩
        have hT := hfle T; dsimp [idx, f] at *; omega
    · rw [if_neg hlt]
      constructor
      · intro h; omega
      · rintro ⟨S, T, hEq⟩
        have hS := hfle S; dsimp [N, f] at hlt hS; omega

private lemma tail_diff_not_testPos {k : ℕ} (hk6 : k ≤ 6) {a : Fin 9 → ℕ}
    (hinj : Function.Injective (fun U : Finset (Fin 9) => ∑ i ∈ U, a i))
    {U V : Finset (Fin 9)} (hne : U ≠ V)
    (hU : ∀ i ∈ U, k ≤ i.val) (hV : ∀ i ∈ V, k ≤ i.val)
    (hle : ∑ i ∈ V, a i ≤ ∑ i ∈ U, a i) :
    testPos (kronR k (by omega) a / 256 ^ (∑ i : Fin k, a ⟨i.val, by omega⟩))
      (∑ i ∈ U, a i - ∑ i ∈ V, a i) = false := by
  cases h : testPos (kronR k (by omega) a / 256 ^ (∑ i : Fin k, a ⟨i.val, by omega⟩))
      (∑ i ∈ U, a i - ∑ i ∈ V, a i)
  · rfl
  · exfalso
    obtain ⟨S, T, hST⟩ := ((kronR_digit hk6 hinj).2 _).mp h
    let emb : Fin k ↪ Fin 9 := ⟨fun i => ⟨i.val, by omega⟩, fun x y h => Fin.ext (by simpa [Fin.ext_iff] using h)⟩
    let S' := S.map emb
    let T' := T.map emb
    have hUT : Disjoint U T' := disjoint_left.mpr fun i hiU hiT => by
      rcases mem_map.mp hiT with ⟨j, _, rfl⟩
      have h1 := hU _ hiU; change k ≤ j.val at h1; have := j.isLt; omega
    have hVS : Disjoint V S' := disjoint_left.mpr fun i hiV hiS => by
      rcases mem_map.mp hiS with ⟨j, _, rfl⟩
      have h1 := hV _ hiV; change k ≤ j.val at h1; have := j.isLt; omega
    have hsumEq : ∑ i ∈ U ∪ T', a i = ∑ i ∈ V ∪ S', a i := by
      rw [sum_union hUT, sum_union hVS, sum_map, sum_map]
      change ∑ i ∈ U, a i + ∑ j ∈ T, a ⟨j.val, by omega⟩ = ∑ i ∈ V, a i + ∑ j ∈ S, a ⟨j.val, by omega⟩
      omega
    have hEq := hinj hsumEq
    apply hne
    ext i
    constructor
    · intro hiU
      have hi1 : i ∈ V ∪ S' := hEq ▸ mem_union_left T' hiU
      rcases mem_union.mp hi1 with hiV | hiS
      · exact hiV
      · rcases mem_map.mp hiS with ⟨j, _, rfl⟩
        have h1 := hU _ hiU; change k ≤ j.val at h1; have := j.isLt; omega
    · intro hiV
      have hi1 : i ∈ U ∪ T' := hEq.symm ▸ mem_union_left S' hiV
      rcases mem_union.mp hi1 with hiU | hiT
      · exact hiU
      · rcases mem_map.mp hiT with ⟨j, _, rfl⟩
        have h1 := hV _ hiV; change k ≤ j.val at h1; have := j.isLt; omega

-- 2B. TailGap, findG, skipLo, skipHi, collectAliveDesc, and G-spaced moment bounds

private def TailGap (k G : ℕ) (a : Fin 9 → ℕ) : Prop :=
  1 ≤ G ∧ ∀ U V : Finset (Fin 9), U ≠ V →
    (∀ i ∈ U, k ≤ i.val) → (∀ i ∈ V, k ≤ i.val) →
    ∑ i ∈ V, a i + G ≤ ∑ i ∈ U, a i ∨ ∑ i ∈ U, a i + G ≤ ∑ i ∈ V, a i

private lemma tailGap_of_inj {k : ℕ} {a : Fin 9 → ℕ}
    (hinj : Function.Injective (fun U : Finset (Fin 9) => ∑ i ∈ U, a i)) :
    TailGap k 1 a :=
  ⟨le_rfl, fun U V hne _ _ => by have : ∑ i ∈ U, a i ≠ ∑ i ∈ V, a i := fun h => hne (hinj h); omega⟩

private lemma tailGap_mono_k {k k' G : ℕ} {a : Fin 9 → ℕ} (hkk' : k ≤ k') (h : TailGap k G a) :
    TailGap k' G a :=
  ⟨h.1, fun U V hne hU hV => h.2 U V hne (fun i hi => le_trans hkk' (hU i hi)) (fun i hi => le_trans hkk' (hV i hi))⟩

private lemma findGAux_spec :
    ∀ (fuel W g : ℕ),
      g ≤ findGAux fuel W g ∧
      ∀ d, g ≤ d → d < findGAux fuel W g → 0 < (W / 256 ^ (d - g)) % 256 := by
  intro fuel
  induction fuel with
  | zero => intro W g; exact ⟨le_rfl, fun d h1 h2 => by dsimp [findGAux] at h2; omega⟩
  | succ fuel ih =>
    intro W g
    unfold findGAux
    by_cases hpos : 0 < W % 256
    · have hblt : Nat.blt 0 (Nat.mod W 256) = true := Nat.blt_eq.mpr hpos
      simp only [hblt, ite_true]
      obtain ⟨hge, hspec⟩ := ih (Nat.div W 256) (Nat.add g 1)
      have hge' : g + 1 ≤ findGAux fuel (Nat.div W 256) (Nat.add g 1) := hge
      refine ⟨by omega, fun d h1 h2 => ?_⟩
      by_cases hdg : d = g
      · subst hdg; simpa using hpos
      · have h3 := hspec d (by change g + 1 ≤ d; omega) h2
        have hsub : d - g = 1 + (d - (g + 1)) := by omega
        rw [hsub, pow_add, pow_one, ← Nat.div_div_eq_div_mul]
        exact h3
    · have hblt : Nat.blt 0 (Nat.mod W 256) = false := blt_false_of_le (by change W % 256 ≤ 0; omega)
      simp only [hblt, Bool.false_eq_true, ite_false]
      exact ⟨le_rfl, fun d h1 h2 => by omega⟩

private lemma findG_tailGap {k Gin : ℕ} (hk6 : k ≤ 6) {a : Fin 9 → ℕ}
    (hinj : Function.Injective (fun U : Finset (Fin 9) => ∑ i ∈ U, a i))
    (hGin : TailGap k Gin a) :
    let Rpos := kronR k (by omega) a / 256 ^ (∑ i : Fin k, a ⟨i.val, by omega⟩)
    TailGap k (findG Rpos Gin) a := by
  intro Rpos
  obtain ⟨hge, hspec⟩ := findGAux_spec 64 (Nat.div Rpos (Nat.pow 256 Gin)) Gin
  refine ⟨le_trans hGin.1 hge, fun U V hne hU hV => ?_⟩
  rcases hGin.2 U V hne hU hV with h1 | h2
  · left
    by_contra hlt
    have hd1 : Gin ≤ ∑ i ∈ U, a i - ∑ i ∈ V, a i := by omega
    have hd2 : ∑ i ∈ U, a i - ∑ i ∈ V, a i < findG Rpos Gin := by omega
    have hpos := hspec _ hd1 hd2
    have htp : testPos Rpos (∑ i ∈ U, a i - ∑ i ∈ V, a i) = true := by
      unfold testPos
      change Nat.blt 0 ((Rpos / 256 ^ (∑ i ∈ U, a i - ∑ i ∈ V, a i)) % 256) = true
      rw [Nat.blt_eq]
      change 0 < ((Rpos / 256 ^ Gin) / 256 ^ (∑ i ∈ U, a i - ∑ i ∈ V, a i - Gin)) % 256 at hpos
      rwa [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_sub_cancel' hd1] at hpos
    have hfalse := tail_diff_not_testPos hk6 hinj hne hU hV (by omega)
    rw [htp] at hfalse; cases hfalse
  · right
    by_contra hlt
    have hd1 : Gin ≤ ∑ i ∈ V, a i - ∑ i ∈ U, a i := by omega
    have hd2 : ∑ i ∈ V, a i - ∑ i ∈ U, a i < findG Rpos Gin := by omega
    have hpos := hspec _ hd1 hd2
    have htp : testPos Rpos (∑ i ∈ V, a i - ∑ i ∈ U, a i) = true := by
      unfold testPos
      change Nat.blt 0 ((Rpos / 256 ^ (∑ i ∈ V, a i - ∑ i ∈ U, a i)) % 256) = true
      rw [Nat.blt_eq]
      change 0 < ((Rpos / 256 ^ Gin) / 256 ^ (∑ i ∈ V, a i - ∑ i ∈ U, a i - Gin)) % 256 at hpos
      rwa [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_sub_cancel' hd1] at hpos
    have hfalse := tail_diff_not_testPos hk6 hinj hne.symm hV hU (by omega)
    rw [htp] at hfalse; cases hfalse

private lemma tailGap_elem_ge {k G : ℕ} {a : Fin 9 → ℕ} (h : TailGap k G a) {i : Fin 9} (hi : k ≤ i.val) :
    G ≤ a i := by
  have h1 := h.2 {i} ∅ (by simp) (by simp [hi]) (by simp)
  simp at h1; omega

private lemma tailGap_diff_ge {k G : ℕ} {a : Fin 9 → ℕ} (ha : StrictAnti a) (h : TailGap k G a)
    {i j : Fin 9} (hi : k ≤ i.val) (hij : i < j) :
    a j + G ≤ a i := by
  have hne : ({i} : Finset (Fin 9)) ≠ {j} := by
    intro heq; have : i ∈ ({j} : Finset (Fin 9)) := heq ▸ mem_singleton_self i
    exact ne_of_lt hij (mem_singleton.mp this)
  have h1 := h.2 {i} {j} hne (by simp [hi]) (by simp; have : i.val < j.val := hij; omega)
  have hlt := ha hij
  simp at h1; omega

private lemma tailGap_a6_ge_4G {k G : ℕ} (hk6 : k ≤ 6) {a : Fin 9 → ℕ} (ha : StrictAnti a) (h : TailGap k G a) :
    4 * G ≤ a 6 := by
  have h8 : G ≤ a 8 := tailGap_elem_ge h (by omega)
  have h78 : a 8 + G ≤ a 7 := tailGap_diff_ge ha h (by omega) (by decide)
  have h67 : a 7 + G ≤ a 6 := tailGap_diff_ge ha h (by omega) (by decide)
  have hne : ({6} : Finset (Fin 9)) ≠ {7, 8} := by decide
  have h678 := h.2 {6} {7, 8} hne (by intro i hi; simp at hi; subst hi; omega)
    (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
  rw [sum_singleton, sum_pair (by decide : (7 : Fin 9) ≠ 8)] at h678
  omega

private lemma powerset_centered_sq_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ) :
    ∑ U ∈ s.powerset, (2 * ∑ i ∈ U, a i - ∑ i ∈ s, a i) ^ 2 = (2 : ℝ) ^ s.card * ∑ i ∈ s, a i ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    rw [sum_powerset_insert hx, card_insert_of_notMem hx, sum_insert hx, sum_insert hx, ← sum_add_distrib]
    have hterm : ∀ U ∈ s.powerset,
        (2 * ∑ i ∈ U, a i - (a x + ∑ i ∈ s, a i)) ^ 2 +
        (2 * ∑ i ∈ insert x U, a i - (a x + ∑ i ∈ s, a i)) ^ 2 =
        2 * a x ^ 2 + 2 * (2 * ∑ i ∈ U, a i - ∑ i ∈ s, a i) ^ 2 := by
      intro U hU
      have hxU : x ∉ U := fun h => hx (mem_powerset.mp hU h)
      rw [sum_insert hxU]; ring
    rw [sum_congr rfl hterm, sum_add_distrib, sum_const, card_powerset, nsmul_eq_mul, ← mul_sum, ih, pow_succ]
    push_cast; ring

private lemma even_sq_sum_eval2 (m : ℕ) :
    3 * (∑ i ∈ range m, 2 * (2 * m - 1 - 2 * i) ^ 2) = 2 * m * ((2 * m) ^ 2 - 1) := by
  induction m with
  | zero => simp
  | succ k ih =>
    have hshift : ∑ i ∈ range (k + 1), 2 * (2 * (k + 1) - 1 - 2 * i) ^ 2 =
        2 * (2 * k + 1) ^ 2 + ∑ i ∈ range k, 2 * (2 * k - 1 - 2 * i) ^ 2 := by
      rw [sum_range_succ']
      have hsub : ∀ i ∈ range k, 2 * (2 * (k + 1) - 1 - 2 * (i + 1)) ^ 2 = 2 * (2 * k - 1 - 2 * i) ^ 2 := by
        intro i hi; have := mem_range.mp hi; congr 2; omega
      rw [sum_congr rfl hsub, add_comm]
      have h0 : 2 * (k + 1) - 1 - 2 * 0 = 2 * k + 1 := by omega
      rw [h0]
    rw [hshift, mul_add, ih]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · decide
    · have h1 : 1 ≤ (2 * k) ^ 2 := by nlinarith
      have h2 : 1 ≤ (2 * (k + 1)) ^ 2 := by nlinarith
      zify [h1, h2]; ring

private lemma strictMono_gap_G {m G : ℕ} {f : Fin m → ℕ}
    (hstep : ∀ i j : Fin m, i < j → f i + G ≤ f j) (i j : Fin m) (hij : i ≤ j) :
    f i + (j.val - i.val) * G ≤ f j := by
  suffices h : ∀ (b : ℕ) (hb : b < m) (x : Fin m), x.val ≤ b → f x + (b - x.val) * G ≤ f ⟨b, hb⟩ from
    h j.val j.isLt i hij
  intro b
  induction b with
  | zero =>
    intro hb x hx
    have : x = ⟨0, hb⟩ := Fin.ext (Nat.eq_zero_of_le_zero hx)
    simp [this]
  | succ b ih =>
    intro hb x hx
    by_cases hEq : x.val = b + 1
    · have : x = ⟨b + 1, hb⟩ := Fin.ext hEq; simp [this]
    · have hb' : b < m := by omega
      have h1 := ih hb' x (by omega)
      have h2 := hstep ⟨b, hb'⟩ ⟨b + 1, hb⟩ (Nat.lt_succ_self b)
      have hsub : b + 1 - x.val = (b - x.val) + 1 := by omega
      rw [hsub, add_mul, one_mul]; omega

private lemma tailGap_sum_and_sq {k G : ℕ} (hk8 : k ≤ 8) {a : Fin 9 → ℕ}
    (h : TailGap k G a) :
    let T := (univ : Finset (Fin 9)).filter (fun i => k ≤ i.val)
    let r := 9 - k
    (2 ^ r - 1) * G ≤ ∑ i ∈ T, a i ∧
    G ^ 2 * (4 ^ r - 1) ≤ 3 * ∑ i ∈ T, a i ^ 2 := by
  classical
  intro T r
  have hTcard : T.card = r := by
    have : T = (Ico k 9).attach.image (fun x => ⟨x.1, (mem_Ico.mp x.2).2⟩) := by
      ext i; simp only [T, mem_filter, mem_univ, true_and, mem_image, mem_attach, true_and, Subtype.exists]
      constructor
      · intro hi; exact ⟨i.val, mem_Ico.mpr ⟨hi, i.isLt⟩, rfl⟩
      · rintro ⟨x, hx, rfl⟩; exact (mem_Ico.mp hx).1
    rw [this, card_image_of_injective]
    · rw [card_attach, Nat.card_Ico]
    · intro x y h; exact Subtype.ext (congrArg Fin.val h)
  let fn : Finset (Fin 9) → ℕ := fun U => ∑ i ∈ U, a i
  have hinjT : Set.InjOn fn (T.powerset : Set (Finset (Fin 9))) := by
    intro U hU V hV hEq
    by_contra hne
    have hU' : ∀ i ∈ U, k ≤ i.val := fun i hi => (mem_filter.mp (mem_powerset.mp hU hi)).2
    have hV' : ∀ i ∈ V, k ≤ i.val := fun i hi => (mem_filter.mp (mem_powerset.mp hV hi)).2
    have hG := h.2 U V hne hU' hV'
    have hG1 := h.1
    dsimp [fn] at hEq; omega
  let S := T.powerset.image fn
  have hScard : S.card = 2 * 2 ^ (r - 1) := by
    rw [card_image_of_injOn hinjT, card_powerset, hTcard]
    have hr1 : r = (r - 1) + 1 := by omega
    conv_lhs => rw [hr1, pow_succ']
  let e := S.orderIsoOfFin hScard
  let f : Fin (2 * 2 ^ (r - 1)) → ℕ := fun i => (e i : ℕ)
  have hf_gap : ∀ i j : Fin (2 * 2 ^ (r - 1)), i < j → f i + G ≤ f j := by
    intro i j hij
    have hlt : f i < f j := e.strictMono hij
    rcases mem_image.mp (e i).2 with ⟨U, hU, hUi⟩
    rcases mem_image.mp (e j).2 with ⟨V, hV, hVj⟩
    have hne : U ≠ V := fun heq => by subst heq; dsimp [f] at hlt; rw [← hUi, ← hVj] at hlt; exact lt_irrefl _ hlt
    have hU' : ∀ x ∈ U, k ≤ x.val := fun x hx => (mem_filter.mp (mem_powerset.mp hU hx)).2
    have hV' : ∀ x ∈ V, k ≤ x.val := fun x hx => (mem_filter.mp (mem_powerset.mp hV hx)).2
    have hG := h.2 U V hne hU' hV'
    dsimp [f, fn] at hlt hUi hVj ⊢
    omega
  have hrpos : 1 ≤ 2 * 2 ^ (r - 1) := by
    have : 1 ≤ 2 ^ (r - 1) := Nat.one_le_pow _ _ (by decide)
    omega
  have hsum_bd : (2 ^ r - 1) * G ≤ ∑ i ∈ T, a i := by
    let last : Fin (2 * 2 ^ (r - 1)) := ⟨2 * 2 ^ (r - 1) - 1, by omega⟩
    let fst : Fin (2 * 2 ^ (r - 1)) := ⟨0, by omega⟩
    have h1 := strictMono_gap_G hf_gap fst last (Fin.zero_le _)
    have hlast_le : f last ≤ ∑ i ∈ T, a i := by
      rcases mem_image.mp (e last).2 with ⟨U, hU, hUeq⟩
      have : f last = ∑ i ∈ U, a i := hUeq.symm
      rw [this]; exact sum_le_sum_of_subset (mem_powerset.mp hU)
    have h2r : 2 * 2 ^ (r - 1) = 2 ^ r := by
      have hr1 : r = (r - 1) + 1 := by omega
      conv_rhs => rw [hr1, pow_succ']
    dsimp [fst, last] at h1 hlast_le
    have h1' : (2 * 2 ^ (r - 1) - 1) * G ≤ ∑ i ∈ T, a i := le_trans (by omega) hlast_le
    rwa [h2r] at h1'
  have hsq_bd : G ^ 2 * (4 ^ r - 1) ≤ 3 * ∑ i ∈ T, a i ^ 2 := by
    let m := 2 ^ (r - 1)
    let c : ℝ := ∑ i ∈ T, (a i : ℝ)
    have hpow : ∑ U ∈ T.powerset, (2 * ∑ i ∈ U, (a i : ℝ) - c) ^ 2 = (2 : ℝ) ^ r * ∑ i ∈ T, (a i : ℝ) ^ 2 := by
      have := powerset_centered_sq_sum T (fun i => (a i : ℝ))
      rwa [hTcard] at this
    have hbij : ∑ x ∈ S, (2 * (x : ℝ) - c) ^ 2 = ∑ U ∈ T.powerset, (2 * ∑ i ∈ U, (a i : ℝ) - c) ^ 2 := by
      rw [sum_image (fun U hU V hV h => hinjT hU hV h)]
      refine sum_congr rfl fun U _ => ?_
      simp [fn]
    have hbij2 : ∑ x ∈ S, (2 * (x : ℝ) - c) ^ 2 = ∑ i : Fin (2 * m), (2 * (f i : ℝ) - c) ^ 2 := by
      refine sum_bij (fun x hx => e.symm ⟨x, hx⟩) (fun _ _ => mem_univ _) ?_ ?_ ?_
      · intro x _ y _ hEq; have := congrArg (fun idx => (e idx : ℕ)) hEq; simpa using this
      · intro i _; exact ⟨(e i : ℕ), (e i).2, by simp⟩
      · intro x hx; simp [f]
    -- Paired centered square bound with step G:
    have hpair : (G : ℝ) ^ 2 * (∑ i ∈ range m, 2 * ((2 * m - 1 - 2 * i : ℕ) : ℝ) ^ 2) ≤
        ∑ i : Fin (2 * m), (2 * (f i : ℝ) - c) ^ 2 := by
      rw [mul_sum]
      let v (i : ℕ) : ℝ := if h : i < 2 * m then (2 * (f ⟨i, h⟩ : ℝ) - c) ^ 2 else 0
      have hsum : (∑ i : Fin (2 * m), (2 * (f i : ℝ) - c) ^ 2) = ∑ i ∈ range (2 * m), v i := by
        rw [← Fin.sum_univ_eq_sum_range]; exact sum_congr rfl fun i _ => by simp [v, i.isLt]
      rw [hsum, show 2 * m = m + m by omega, sum_range_add,
        ← sum_range_reflect (fun i => v (m + i)) m, ← sum_add_distrib]
      refine sum_le_sum fun i hi => ?_
      have hi' : i < m := mem_range.mp hi
      have hi2 : i < 2 * m := by omega
      have hj2 : 2 * m - 1 - i < 2 * m := by omega
      have hidx : m + (m - 1 - i) = 2 * m - 1 - i := by omega
      rw [hidx]; simp only [v, dif_pos hi2, dif_pos hj2]
      have hgap := strictMono_gap_G hf_gap ⟨i, hi2⟩ ⟨2 * m - 1 - i, hj2⟩ (show i ≤ 2 * m - 1 - i by omega)
      dsimp only at hgap
      have hd : f ⟨i, hi2⟩ + (2 * m - 1 - 2 * i) * G ≤ f ⟨2 * m - 1 - i, hj2⟩ := by
        have : 2 * m - 1 - i - i = 2 * m - 1 - 2 * i := by omega
        rwa [this] at hgap
      have hdR : (f ⟨i, hi2⟩ : ℝ) + ((2 * m - 1 - 2 * i : ℕ) : ℝ) * (G : ℝ) ≤ (f ⟨2 * m - 1 - i, hj2⟩ : ℝ) := by
        exact_mod_cast hd
      have h2m : m + m - 1 - 2 * i = 2 * m - 1 - 2 * i := by omega
      rw [h2m]
      nlinarith [sq_nonneg ((f ⟨i, hi2⟩ : ℝ) + (f ⟨2 * m - 1 - i, hj2⟩ : ℝ) - c),
                 sq_nonneg (((f ⟨2 * m - 1 - i, hj2⟩ : ℝ) - (f ⟨i, hi2⟩ : ℝ)) - ((2 * m - 1 - 2 * i : ℕ) : ℝ) * (G : ℝ)),
                 mul_nonneg (Nat.cast_nonneg (α := ℝ) (2 * m - 1 - 2 * i)) (Nat.cast_nonneg (α := ℝ) G)]
    have heval : (3 : ℝ) * (∑ i ∈ range m, 2 * ((2 * m - 1 - 2 * i : ℕ) : ℝ) ^ 2) =
        ((2 * m * ((2 * m) ^ 2 - 1) : ℕ) : ℝ) := by
      exact_mod_cast even_sq_sum_eval2 m
    have h2m_eq : 2 * m = 2 ^ r := by
      have hr1 : r = (r - 1) + 1 := by omega
      dsimp [m]; conv_rhs => rw [hr1, pow_succ']
    have h2r_sq : (2 ^ r) ^ 2 = 4 ^ r := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h2m_eq, h2r_sq] at heval
    have hsum_eq : ∑ i ∈ range m, 2 * ((2 * m - 1 - 2 * i : ℕ) : ℝ) ^ 2 =
        ∑ i ∈ range m, 2 * ((2 ^ r - 1 - 2 * i : ℕ) : ℝ) ^ 2 :=
      sum_congr rfl fun i _ => by rw [h2m_eq]
    rw [hsum_eq] at hpair
    have hcomb : ((2 ^ r : ℕ) : ℝ) * ((G : ℝ) ^ 2 * ((4 ^ r - 1 : ℕ) : ℝ)) ≤
        ((2 ^ r : ℕ) : ℝ) * (3 * ∑ i ∈ T, (a i : ℝ) ^ 2) := by
      have h1 : (G : ℝ) ^ 2 * (((2 ^ r * (4 ^ r - 1) : ℕ) : ℝ)) ≤ 3 * ((2 : ℝ) ^ r * ∑ i ∈ T, (a i : ℝ) ^ 2) := by
        rw [← heval]; linarith
      push_cast at h1 ⊢; linarith
    have h2r_pos : (0 : ℝ) < ((2 ^ r : ℕ) : ℝ) := by positivity
    have hR : (G : ℝ) ^ 2 * ((4 ^ r - 1 : ℕ) : ℝ) ≤ 3 * ∑ i ∈ T, (a i : ℝ) ^ 2 :=
      le_of_mul_le_mul_left hcomb h2r_pos
    exact_mod_cast hR
  exact ⟨hsum_bd, hsq_bd⟩

private lemma skipLoAux_le :
    ∀ (fuel W l x : ℕ), l ≤ x → (W / 256 ^ (x - l)) % 256 = 0 → skipLoAux fuel W l ≤ x := by
  intro fuel
  induction fuel with
  | zero => intro W l x hlx _; exact hlx
  | succ fuel ih =>
    intro W l x hlx hzero
    unfold skipLoAux
    by_cases hpos : 0 < W % 256
    · have hblt : Nat.blt 0 (Nat.mod W 256) = true := Nat.blt_eq.mpr hpos
      simp only [hblt, ite_true]
      have hne : x ≠ l := by intro h; subst h; simp at hzero; omega
      have h1 : l + 1 ≤ x := by omega
      have hsub : x - l = 1 + (x - (l + 1)) := by omega
      rw [hsub, pow_add, pow_one, ← Nat.div_div_eq_div_mul] at hzero
      exact ih (Nat.div W 256) (Nat.add l 1) x h1 hzero
    · have hblt : Nat.blt 0 (Nat.mod W 256) = false := blt_false_of_le (by change W % 256 ≤ 0; omega)
      simp only [hblt, Bool.false_eq_true, ite_false]
      exact hlx

private lemma skipLo_le {Rpos l hi x : ℕ} (hlx : l ≤ x) (htp : testPos Rpos x = false) :
    skipLo Rpos l hi ≤ x := by
  unfold skipLo
  split_ifs
  · exact hlx
  · apply skipLoAux_le _ _ _ x hlx
    change ((Rpos / 256 ^ l) / 256 ^ (x - l)) % 256 = 0
    rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_sub_cancel' hlx]
    unfold testPos at htp
    change Nat.blt 0 ((Rpos / 256 ^ x) % 256) = false at htp
    by_contra hne
    rw [Nat.blt_eq.mpr (Nat.pos_of_ne_zero hne)] at htp; cases htp

private lemma skipHiAux_ge {Rpos x : ℕ} (hx1 : 1 ≤ x) (htp : testPos Rpos x = false) :
    ∀ (fuel h : ℕ), x ≤ h → x ≤ skipHiAux fuel Rpos h := by
  intro fuel
  induction fuel with
  | zero => intro h hxh; exact hxh
  | succ fuel ih =>
    intro h hxh
    unfold skipHiAux
    cases htest : testPos Rpos h
    · simp only [Bool.false_eq_true, ite_false]; exact hxh
    · simp only [ite_true]
      have hne : x ≠ h := by intro heq; subst heq; rw [htp] at htest; cases htest
      have hh0 : h ≠ 0 := by omega
      simp only [beq_false_of_ne hh0, Bool.false_eq_true, ite_false]
      exact ih (Nat.sub h 1) (by change x ≤ h - 1; omega)

private lemma skipHi_ge {Rpos lo h x : ℕ} (hx1 : 1 ≤ x) (hxh : x ≤ h) (htp : testPos Rpos x = false) :
    x ≤ skipHi Rpos lo h := by
  unfold skipHi
  split_ifs
  · exact hxh
  · exact skipHiAux_ge hx1 htp _ h hxh

private lemma mod_pow256_div_mod {X span i : ℕ} (hi : i < span) :
    ((X % 256 ^ span) / 256 ^ i) % 256 = (X / 256 ^ i) % 256 := by
  have h1 : X = (X / 256 ^ span) * 256 ^ span + X % 256 ^ span := by
    have := Nat.div_add_mod X (256 ^ span); linarith
  have hpow : 256 ^ span = 256 ^ i * 256 ^ (span - i) := by
    rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hi)]
  have hpos256 : 0 < 256 ^ i := Nat.pow_pos (by decide)
  have hdiv : X / 256 ^ i = (X / 256 ^ span) * 256 ^ (span - i) + (X % 256 ^ span) / 256 ^ i := by
    have hrew : X = 256 ^ i * ((X / 256 ^ span) * 256 ^ (span - i)) + X % 256 ^ span := by
      conv_lhs => rw [h1]
      nth_rw 2 [hpow]; ring
    conv_lhs => rw [hrew]
    rw [Nat.mul_add_div hpos256]
  have h256 : 256 ^ (span - i) = 256 ^ (span - i - 1) * 256 := by
    have : span - i = (span - i - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ]
  rw [hdiv, h256, ← mul_assoc, Nat.mul_add_mod_self_right]

private lemma collectAliveAux_spec :
    ∀ (fuel W v : ℕ) (acc : List ℕ),
      acc.Pairwise (· > ·) →
      (∀ y ∈ acc, y < v) →
      (collectAliveAux fuel W v acc).Pairwise (· > ·) ∧
      ∀ x, x ∈ collectAliveAux fuel W v acc ↔
        x ∈ acc ∨ (v ≤ x ∧ x < v + fuel ∧ (W / 256 ^ (x - v)) % 256 = 0) := by
  intro fuel
  induction fuel with
  | zero => intro W v acc hpw _; exact ⟨hpw, fun x => by simp [collectAliveAux]; omega⟩
  | succ fuel ih =>
    intro W v acc hpw hlt
    unfold collectAliveAux
    let acc' := if Nat.beq (Nat.mod W 256) 0 then v :: acc else acc
    have hpw' : acc'.Pairwise (· > ·) := by
      dsimp [acc']; split_ifs
      · exact List.pairwise_cons.mpr ⟨fun y hy => hlt y hy, hpw⟩
      · exact hpw
    have hlt' : ∀ y ∈ acc', y < Nat.add v 1 := by
      intro y hy; dsimp [acc'] at hy; split_ifs at hy
      · rcases List.mem_cons.mp hy with rfl | hy'
        · change y < y + 1; omega
        · have := hlt y hy'; change y < v + 1; omega
      · have := hlt y hy; change y < v + 1; omega
    obtain ⟨hpw_res, hmem_res⟩ := ih (Nat.div W 256) (Nat.add v 1) acc' hpw' hlt'
    refine ⟨hpw_res, fun x => ?_⟩
    rw [hmem_res x]
    by_cases hxv : x = v
    · subst hxv
      have hnot_right : ¬ (Nat.add x 1 ≤ x ∧ x < Nat.add x 1 + fuel ∧ ((Nat.div W 256) / 256 ^ (x - Nat.add x 1)) % 256 = 0) := by
        intro h; have := h.1; change x + 1 ≤ x at this; omega
      simp only [hnot_right, or_false]
      dsimp [acc']
      by_cases hw0 : W % 256 = 0
      · have hbeq : Nat.beq (Nat.mod W 256) 0 = true := by change Nat.beq (W % 256) 0 = true; rw [hw0]; rfl
        simp [hbeq, hw0]
      · have hbeq : Nat.beq (Nat.mod W 256) 0 = false := beq_false_of_ne hw0
        simp only [hbeq, Bool.false_eq_true, ite_false]
        constructor
        · intro hx; exact Or.inl hx
        · rintro (hx | ⟨_, _, hz⟩)
          · exact hx
          · simp at hz; exact absurd hz hw0
    · have hmem_acc' : x ∈ acc' ↔ x ∈ acc := by
        dsimp [acc']; split_ifs
        · simp [hxv]
        · rfl
      rw [hmem_acc']
      by_cases hgt : v < x
      · have hsub : x - v = 1 + (x - (v + 1)) := by omega
        have hdiv : (Nat.div W 256) / 256 ^ (x - Nat.add v 1) = W / 256 ^ (x - v) := by
          change (W / 256) / 256 ^ (x - (v + 1)) = W / 256 ^ (x - v)
          rw [hsub, pow_add, pow_one, Nat.div_div_eq_div_mul]
        rw [hdiv]
        constructor
        · rintro (h | ⟨h1, h2, h3⟩)
          · exact Or.inl h
          · exact Or.inr ⟨by omega, by change x < v + 1 + fuel at h2; omega, h3⟩
        · rintro (h | ⟨h1, h2, h3⟩)
          · exact Or.inl h
          · exact Or.inr ⟨by change v + 1 ≤ x; omega, by change x < v + 1 + fuel; omega, h3⟩
      · have hno1 : ¬ (Nat.add v 1 ≤ x ∧ x < Nat.add v 1 + fuel ∧ ((Nat.div W 256) / 256 ^ (x - Nat.add v 1)) % 256 = 0) := by
          intro h; have := h.1; change v + 1 ≤ x at this; omega
        have hno2 : ¬ (v ≤ x ∧ x < v + (fuel + 1) ∧ (W / 256 ^ (x - v)) % 256 = 0) := by
          intro h; omega
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact absurd h hno1
        · rintro (h | h)
          · exact Or.inl h
          · exact absurd h hno2

private lemma collectAliveDesc_spec (Rpos lo hi : ℕ) :
    (collectAliveDesc Rpos lo hi).Pairwise (· > ·) ∧
    ∀ x, x ∈ collectAliveDesc Rpos lo hi ↔ lo ≤ x ∧ x ≤ hi ∧ testPos Rpos x = false := by
  unfold collectAliveDesc
  by_cases hlt : hi < lo
  · simp only [Nat.blt_eq.mpr hlt, ite_true]
    exact ⟨List.Pairwise.nil, fun x => by simp; omega⟩
  · simp only [blt_false_of_le (by omega : lo ≤ hi), Bool.false_eq_true, ite_false]
    let span := Nat.add (Nat.sub hi lo) 1
    let slice := Nat.mod (Nat.div Rpos (Nat.pow 256 lo)) (Nat.pow 256 span)
    obtain ⟨hpw, hmem⟩ := collectAliveAux_spec span slice lo [] List.Pairwise.nil (fun _ h => by simp at h)
    refine ⟨hpw, fun x => ?_⟩
    rw [hmem x]
    simp only [List.not_mem_nil, false_or]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have hi_lt : x - lo < span := by dsimp [span] at h2 ⊢; omega
      have hmod := mod_pow256_div_mod (X := Rpos / 256 ^ lo) hi_lt
      rw [show (slice / 256 ^ (x - lo)) % 256 = ((Rpos / 256 ^ lo) / 256 ^ (x - lo)) % 256 from hmod,
          Nat.div_div_eq_div_mul, ← pow_add, Nat.add_sub_cancel' h1] at h3
      refine ⟨h1, by dsimp [span] at h2; omega, ?_⟩
      unfold testPos; change Nat.blt 0 ((Rpos / 256 ^ x) % 256) = false
      rw [h3]; rfl
    · rintro ⟨h1, h2, h3⟩
      have hi_lt : x - lo < span := by dsimp [span]; omega
      refine ⟨h1, by dsimp [span]; omega, ?_⟩
      have hmod := mod_pow256_div_mod (X := Rpos / 256 ^ lo) hi_lt
      rw [show (slice / 256 ^ (x - lo)) % 256 = ((Rpos / 256 ^ lo) / 256 ^ (x - lo)) % 256 from hmod,
          Nat.div_div_eq_div_mul, ← pow_add, Nat.add_sub_cancel' h1]
      unfold testPos at h3
      change Nat.blt 0 ((Rpos / 256 ^ x) % 256) = false at h3
      by_contra hne
      rw [Nat.blt_eq.mpr (Nat.pos_of_ne_zero hne)] at h3; cases h3

-- 2C. okSQ, checkSeg, checkBox2..5 soundness

private lemma okSQ_iff {qlb S Q : ℕ} :
    okSQ qlb S Q = true ↔
      qlb ≤ Q ∧
      42863 + S ^ 2 ≤ 9 * Q ∧
      190509 + S ^ 2 ≤ 10 * Q ∧
      881995 + S ^ 2 ≤ 16 * Q ∧
      9924583 + 3 * S ^ 2 ≤ 126 * Q ∧
      22108415 + S ^ 2 ≤ 256 * Q := by
  unfold okSQ
  dsimp only
  have hS2 : S * S = S ^ 2 := (sq S).symm
  constructor
  · intro h
    by_cases c0 : Q < qlb
    · have : Nat.blt Q qlb = true := Nat.blt_eq.mpr c0
      rw [this] at h; cases h
    rw [blt_false_of_le (by omega : qlb ≤ Q)] at h; simp only [Bool.false_eq_true, ite_false] at h
    by_cases c1 : 9 * Q < 42863 + S * S
    · have : Nat.blt (Nat.mul 9 Q) (Nat.add 42863 (Nat.mul S S)) = true := Nat.blt_eq.mpr c1
      rw [this] at h; cases h
    rw [blt_false_of_le (by change 42863 + S * S ≤ 9 * Q; omega)] at h; simp only [Bool.false_eq_true, ite_false] at h
    by_cases c2 : 10 * Q < 190509 + S * S
    · have : Nat.blt (Nat.mul 10 Q) (Nat.add 190509 (Nat.mul S S)) = true := Nat.blt_eq.mpr c2
      rw [this] at h; cases h
    rw [blt_false_of_le (by change 190509 + S * S ≤ 10 * Q; omega)] at h; simp only [Bool.false_eq_true, ite_false] at h
    by_cases c3 : 16 * Q < 881995 + S * S
    · have : Nat.blt (Nat.mul 16 Q) (Nat.add 881995 (Nat.mul S S)) = true := Nat.blt_eq.mpr c3
      rw [this] at h; cases h
    rw [blt_false_of_le (by change 881995 + S * S ≤ 16 * Q; omega)] at h; simp only [Bool.false_eq_true, ite_false] at h
    by_cases c4 : 126 * Q < 9924583 + 3 * (S * S)
    · have : Nat.blt (Nat.mul 126 Q) (Nat.add 9924583 (Nat.mul 3 (Nat.mul S S))) = true := Nat.blt_eq.mpr c4
      rw [this] at h; cases h
    rw [blt_false_of_le (by change 9924583 + 3 * (S * S) ≤ 126 * Q; omega)] at h; simp only [Bool.false_eq_true, ite_false] at h
    by_cases c5 : 256 * Q < 22108415 + S * S
    · have : Nat.blt (Nat.mul 256 Q) (Nat.add 22108415 (Nat.mul S S)) = true := Nat.blt_eq.mpr c5
      rw [this] at h; cases h
    rw [← hS2]
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩
    rw [← hS2] at h1 h2 h3 h4 h5
    rw [blt_false_of_le h0,
        blt_false_of_le (show Nat.add 42863 (Nat.mul S S) ≤ Nat.mul 9 Q from h1),
        blt_false_of_le (show Nat.add 190509 (Nat.mul S S) ≤ Nat.mul 10 Q from h2),
        blt_false_of_le (show Nat.add 881995 (Nat.mul S S) ≤ Nat.mul 16 Q from h3),
        blt_false_of_le (show Nat.add 9924583 (Nat.mul 3 (Nat.mul S S)) ≤ Nat.mul 126 Q from h4),
        blt_false_of_le (show Nat.add 22108415 (Nat.mul S S) ≤ Nat.mul 256 Q from h5)]
    rfl

private lemma okSQ_mono {qlb S S' Q Q' : ℕ} (hS : S' ≤ S) (hQ : Q ≤ Q') (h : okSQ qlb S Q = true) :
    okSQ qlb S' Q' = true := by
  rw [okSQ_iff] at h ⊢
  have hSsq : S' ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hS 2
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

private lemma convex_seg_quad {C D K curS curQ bQ0 lv bS L T R : ℕ}
    (hCD : D ≤ C) (hbL : bS ≤ L) (hLT : L ≤ T) (hTR : T ≤ R)
    (hT : K + D * (curS + T) ^ 2 ≤ C * (curQ + (bQ0 + (lv + (T - bS)) ^ 2)))
    (hL : C * (curQ + (bQ0 + (lv + (L - bS)) ^ 2)) < K + D * (curS + L) ^ 2)
    (hR : C * (curQ + (bQ0 + (lv + (R - bS)) ^ 2)) < K + D * (curS + R) ^ 2) : False := by
  have hTZ : (K : ℤ) + (D : ℤ) * ((curS : ℤ) + (T : ℤ)) ^ 2 ≤
      (C : ℤ) * ((curQ : ℤ) + ((bQ0 : ℤ) + ((lv : ℤ) + ((T : ℤ) - (bS : ℤ))) ^ 2)) := by
    have : ((T - bS : ℕ) : ℤ) = (T : ℤ) - (bS : ℤ) := Nat.cast_sub (by omega)
    rw [← this]; exact_mod_cast hT
  have hLZ : (C : ℤ) * ((curQ : ℤ) + ((bQ0 : ℤ) + ((lv : ℤ) + ((L : ℤ) - (bS : ℤ))) ^ 2)) <
      (K : ℤ) + (D : ℤ) * ((curS : ℤ) + (L : ℤ)) ^ 2 := by
    have : ((L - bS : ℕ) : ℤ) = (L : ℤ) - (bS : ℤ) := Nat.cast_sub hbL
    rw [← this]; exact_mod_cast hL
  have hRZ : (C : ℤ) * ((curQ : ℤ) + ((bQ0 : ℤ) + ((lv : ℤ) + ((R : ℤ) - (bS : ℤ))) ^ 2)) <
      (K : ℤ) + (D : ℤ) * ((curS : ℤ) + (R : ℤ)) ^ 2 := by
    have : ((R - bS : ℕ) : ℤ) = (R : ℤ) - (bS : ℤ) := Nat.cast_sub (by omega)
    rw [← this]; exact_mod_cast hR
  have hCDZ : (0 : ℤ) ≤ (C : ℤ) - (D : ℤ) := by
    have h1 : (D : ℤ) ≤ (C : ℤ) := by exact_mod_cast hCD
    linarith
  have hLTZ : (0 : ℤ) ≤ (T : ℤ) - (L : ℤ) := by
    have h1 : (L : ℤ) ≤ (T : ℤ) := by exact_mod_cast hLT
    linarith
  have hTRZ : (0 : ℤ) ≤ (R : ℤ) - (T : ℤ) := by
    have h1 : (T : ℤ) ≤ (R : ℤ) := by exact_mod_cast hTR
    linarith
  have hLRZ : (0 : ℤ) ≤ (R : ℤ) - (L : ℤ) := by linarith
  let f : ℤ → ℤ := fun x => (C : ℤ) * ((curQ : ℤ) + ((bQ0 : ℤ) + ((lv : ℤ) + (x - (bS : ℤ))) ^ 2)) - (D : ℤ) * ((curS : ℤ) + x) ^ 2
  have hid : ((R : ℤ) - (T : ℤ)) * f (L : ℤ) + ((T : ℤ) - (L : ℤ)) * f (R : ℤ) - ((R : ℤ) - (L : ℤ)) * f (T : ℤ) =
      ((C : ℤ) - (D : ℤ)) * ((R : ℤ) - (L : ℤ)) * ((T : ℤ) - (L : ℤ)) * ((R : ℤ) - (T : ℤ)) := by
    dsimp [f]; ring
  have hpos : 0 ≤ ((C : ℤ) - (D : ℤ)) * ((R : ℤ) - (L : ℤ)) * ((T : ℤ) - (L : ℤ)) * ((R : ℤ) - (T : ℤ)) := by positivity
  by_cases hEqL : L = T
  · subst hEqL; linarith
  · by_cases hEqR : T = R
    · subst hEqR; linarith
    · have hLT' : (0 : ℤ) < (T : ℤ) - (L : ℤ) := by
        have h1 : (L : ℤ) < (T : ℤ) := by exact_mod_cast (show L < T by omega)
        linarith
      have hTR' : (0 : ℤ) < (R : ℤ) - (T : ℤ) := by
        have h1 : (T : ℤ) < (R : ℤ) := by exact_mod_cast (show T < R by omega)
        linarith
      have hfT : (K : ℤ) ≤ f (T : ℤ) := by dsimp [f]; linarith
      have hfL : f (L : ℤ) < (K : ℤ) := by dsimp [f]; linarith
      have hfR : f (R : ℤ) < (K : ℤ) := by dsimp [f]; linarith
      nlinarith only [hid, hpos, hLT', hTR', hfT, hfL, hfR]

private lemma checkSegLoop_true {qlb curS curQ QRmin bS bQ0 lv T : ℕ}
    (hQR : QRmin ≤ bQ0 + (lv + (T - bS)) * (lv + (T - bS)))
    (hok : okSQ qlb (curS + T) (curQ + (bQ0 + (lv + (T - bS)) * (lv + (T - bS)))) = true) :
    ∀ (fuel T0 : ℕ), T0 ≤ T → T < T0 + fuel → checkSegLoop qlb curS curQ QRmin bS bQ0 lv fuel T0 = true := by
  intro fuel
  induction fuel with
  | zero => intro T0 h1 h2; omega
  | succ fuel ih =>
    intro T0 h1 h2
    unfold checkSegLoop
    dsimp only
    by_cases hEq : T = T0
    · subst hEq
      have hble : Nat.ble QRmin (Nat.add bQ0 (Nat.mul (Nat.add lv (Nat.sub T bS)) (Nat.add lv (Nat.sub T bS)))) = true :=
        Nat.ble_eq.mpr hQR
      simp only [hble, Bool.true_and]
      change (if okSQ qlb (curS + T) (curQ + (bQ0 + (lv + (T - bS)) * (lv + (T - bS)))) = true then true else _) = true
      rw [hok]; rfl
    · split_ifs
      · rfl
      · exact ih (Nat.add T0 1) (by change T0 + 1 ≤ T; omega) (by change T < T0 + 1 + fuel; omega)

private lemma checkSeg_sound {qlb curS curQ QRmin bS bQ lv nL nR segR T : ℕ}
    (hT_n : nL ≤ T ∧ T ≤ nR) (hT_s : bS ≤ T ∧ T ≤ segR)
    (hQR : QRmin ≤ (bQ - lv * lv) + (lv + (T - bS)) ^ 2)
    (hok : okSQ qlb (curS + T) (curQ + ((bQ - lv * lv) + (lv + (T - bS)) ^ 2)) = true) :
    checkSeg qlb curS curQ QRmin bS bQ lv nL nR segR = true := by
  unfold checkSeg
  dsimp only
  let L := nmax nL bS
  let R := nmin nR segR
  have hLT : L ≤ T := by dsimp [L]; rw [nmax_eq]; exact max_le hT_n.1 hT_s.1
  have hTR : T ≤ R := by dsimp [R]; rw [nmin_eq]; exact le_min hT_n.2 hT_s.2
  have hbL : bS ≤ L := by dsimp [L]; rw [nmax_eq]; exact le_max_right _ _
  have hLR : L ≤ R := le_trans hLT hTR
  change (if Nat.blt R L = true then false else _) = true
  simp only [blt_false_of_le hLR, Bool.false_eq_true, ite_false]
  let bQ0 := Nat.sub bQ (Nat.mul lv lv)
  let mL := Nat.add lv (Nat.sub L bS)
  let mR := Nat.add lv (Nat.sub R bS)
  let qLr := Nat.add bQ0 (Nat.mul mL mL)
  let qRr := Nat.add bQ0 (Nat.mul mR mR)
  have hqT_le_qR : bQ0 + (lv + (T - bS)) ^ 2 ≤ qRr := by
    dsimp [qRr, mR]; have h1 : lv + (T - bS) ≤ lv + (R - bS) := by omega
    have h2 := sq_le_mul_of_le h1; change bQ0 + (lv + (T - bS)) ^ 2 ≤ bQ0 + (lv + (R - bS)) * (lv + (R - bS)); omega
  have hok_u := okSQ_iff.mp hok
  have hnot_qR : Nat.blt qRr QRmin = false := blt_false_of_le (le_trans hQR hqT_le_qR)
  have hnot_qlb : Nat.blt (Nat.add curQ qRr) qlb = false :=
    blt_false_of_le (le_trans hok_u.1 (by change curQ + (bQ0 + (lv + (T - bS)) ^ 2) ≤ curQ + qRr; omega))
  change (if and (Nat.blt qLr QRmin) (Nat.blt qRr QRmin) = true then false
    else if and (Nat.blt (Nat.add curQ qLr) qlb) (Nat.blt (Nat.add curQ qRr) qlb) = true then false else _) = true
  simp only [hnot_qR, hnot_qlb, Bool.and_false, Bool.false_eq_true, ite_false]
  change (if and (Nat.ble QRmin qRr) (okSQ qlb (Nat.add curS R) (Nat.add curQ qRr)) = true then true
    else if and (Nat.ble QRmin qLr) (okSQ qlb (Nat.add curS L) (Nat.add curQ qLr)) = true then true
    else if Nat.ble R (Nat.add L 1) = true then false
    else if and (Nat.blt (Nat.mul 9 (Nat.add curQ qLr)) (Nat.add 42863 (Nat.mul (Nat.add curS L) (Nat.add curS L))))
                (Nat.blt (Nat.mul 9 (Nat.add curQ qRr)) (Nat.add 42863 (Nat.mul (Nat.add curS R) (Nat.add curS R)))) = true then false
    else if and (Nat.blt (Nat.mul 10 (Nat.add curQ qLr)) (Nat.add 190509 (Nat.mul (Nat.add curS L) (Nat.add curS L))))
                (Nat.blt (Nat.mul 10 (Nat.add curQ qRr)) (Nat.add 190509 (Nat.mul (Nat.add curS R) (Nat.add curS R)))) = true then false
    else if and (Nat.blt (Nat.mul 16 (Nat.add curQ qLr)) (Nat.add 881995 (Nat.mul (Nat.add curS L) (Nat.add curS L))))
                (Nat.blt (Nat.mul 16 (Nat.add curQ qRr)) (Nat.add 881995 (Nat.mul (Nat.add curS R) (Nat.add curS R)))) = true then false
    else if and (Nat.blt (Nat.mul 126 (Nat.add curQ qLr)) (Nat.add 9924583 (Nat.mul 3 (Nat.mul (Nat.add curS L) (Nat.add curS L)))))
                (Nat.blt (Nat.mul 126 (Nat.add curQ qRr)) (Nat.add 9924583 (Nat.mul 3 (Nat.mul (Nat.add curS R) (Nat.add curS R))))) = true then false
    else if and (Nat.blt (Nat.mul 256 (Nat.add curQ qLr)) (Nat.add 22108415 (Nat.mul (Nat.add curS L) (Nat.add curS L))))
                (Nat.blt (Nat.mul 256 (Nat.add curQ qRr)) (Nat.add 22108415 (Nat.mul (Nat.add curS R) (Nat.add curS R)))) = true then false
    else checkSegLoop qlb curS curQ QRmin bS bQ0 lv (Nat.sub R (Nat.add L 1)) (Nat.add L 1)) = true
  by_cases hhitR : and (Nat.ble QRmin qRr) (okSQ qlb (Nat.add curS R) (Nat.add curQ qRr)) = true
  · rw [if_pos hhitR]
  rw [if_neg hhitR]
  by_cases hhitL : and (Nat.ble QRmin qLr) (okSQ qlb (Nat.add curS L) (Nat.add curQ qLr)) = true
  · rw [if_pos hhitL]
  rw [if_neg hhitL]
  have hT_ne_R : T ≠ R := by
    intro hEq; subst hEq
    have h1 : Nat.ble QRmin qRr = true := Nat.ble_eq.mpr (by dsimp [qRr, mR, bQ0]; change QRmin ≤ bQ - lv * lv + (lv + (R - bS)) * (lv + (R - bS)); rw [← sq (lv + (R - bS))]; exact hQR)
    have h2 : okSQ qlb (Nat.add curS R) (Nat.add curQ qRr) = true := by
      dsimp [qRr, mR, bQ0]; change okSQ qlb (curS + R) (curQ + (bQ - lv * lv + (lv + (R - bS)) * (lv + (R - bS)))) = true; rw [← sq (lv + (R - bS))]; exact hok
    exact hhitR (by rw [h1, h2]; rfl)
  have hT_ne_L : T ≠ L := by
    intro hEq; subst hEq
    have h1 : Nat.ble QRmin qLr = true := Nat.ble_eq.mpr (by dsimp [qLr, mL, bQ0]; change QRmin ≤ bQ - lv * lv + (lv + (L - bS)) * (lv + (L - bS)); rw [← sq (lv + (L - bS))]; exact hQR)
    have h2 : okSQ qlb (Nat.add curS L) (Nat.add curQ qLr) = true := by
      dsimp [qLr, mL, bQ0]; change okSQ qlb (curS + L) (curQ + (bQ - lv * lv + (lv + (L - bS)) * (lv + (L - bS)))) = true; rw [← sq (lv + (L - bS))]; exact hok
    exact hhitL (by rw [h1, h2]; rfl)
  have hL1_lt_R : L + 1 < R := by omega
  simp only [ble_false_of_lt (show Nat.add L 1 < R from hL1_lt_R), Bool.false_eq_true, ite_false]
  have hsqL : mL * mL = (lv + (L - bS)) ^ 2 := (sq _).symm
  have hsqR : mR * mR = (lv + (R - bS)) ^ 2 := (sq _).symm
  have hsqSL : (curS + L) * (curS + L) = (curS + L) ^ 2 := (sq _).symm
  have hsqSR : (curS + R) * (curS + R) = (curS + R) ^ 2 := (sq _).symm
  have hno1 : and (Nat.blt (Nat.mul 9 (Nat.add curQ qLr)) (Nat.add 42863 (Nat.mul (Nat.add curS L) (Nat.add curS L))))
                  (Nat.blt (Nat.mul 9 (Nat.add curQ qRr)) (Nat.add 42863 (Nat.mul (Nat.add curS R) (Nat.add curS R)))) = false := by
    cases h : and (Nat.blt (Nat.mul 9 (Nat.add curQ qLr)) (Nat.add 42863 (Nat.mul (Nat.add curS L) (Nat.add curS L))))
                  (Nat.blt (Nat.mul 9 (Nat.add curQ qRr)) (Nat.add 42863 (Nat.mul (Nat.add curS R) (Nat.add curS R))))
    · rfl
    · exfalso; simp only [Bool.and_eq_true, Nat.blt_eq] at h
      exact convex_seg_quad (C := 9) (D := 1) (K := 42863) (curS := curS) (curQ := curQ) (bQ0 := bQ0) (lv := lv) (by omega) hbL hLT hTR
        (by have := hok_u.2.1; dsimp [bQ0]; omega)
        (by have h1 := h.1; change 9 * (curQ + (bQ0 + mL * mL)) < 42863 + (curS + L) * (curS + L) at h1; rw [hsqL, hsqSL] at h1; omega)
        (by have h2 := h.2; change 9 * (curQ + (bQ0 + mR * mR)) < 42863 + (curS + R) * (curS + R) at h2; rw [hsqR, hsqSR] at h2; omega)
  have hno2 : and (Nat.blt (Nat.mul 10 (Nat.add curQ qLr)) (Nat.add 190509 (Nat.mul (Nat.add curS L) (Nat.add curS L))))
                  (Nat.blt (Nat.mul 10 (Nat.add curQ qRr)) (Nat.add 190509 (Nat.mul (Nat.add curS R) (Nat.add curS R)))) = false := by
    cases h : and (Nat.blt (Nat.mul 10 (Nat.add curQ qLr)) (Nat.add 190509 (Nat.mul (Nat.add curS L) (Nat.add curS L))))
                  (Nat.blt (Nat.mul 10 (Nat.add curQ qRr)) (Nat.add 190509 (Nat.mul (Nat.add curS R) (Nat.add curS R))))
    · rfl
    · exfalso; simp only [Bool.and_eq_true, Nat.blt_eq] at h
      exact convex_seg_quad (C := 10) (D := 1) (K := 190509) (curS := curS) (curQ := curQ) (bQ0 := bQ0) (lv := lv) (by omega) hbL hLT hTR
        (by have := hok_u.2.2.1; dsimp [bQ0]; omega)
        (by have h1 := h.1; change 10 * (curQ + (bQ0 + mL * mL)) < 190509 + (curS + L) * (curS + L) at h1; rw [hsqL, hsqSL] at h1; omega)
        (by have h2 := h.2; change 10 * (curQ + (bQ0 + mR * mR)) < 190509 + (curS + R) * (curS + R) at h2; rw [hsqR, hsqSR] at h2; omega)
  have hno3 : and (Nat.blt (Nat.mul 16 (Nat.add curQ qLr)) (Nat.add 881995 (Nat.mul (Nat.add curS L) (Nat.add curS L))))
                  (Nat.blt (Nat.mul 16 (Nat.add curQ qRr)) (Nat.add 881995 (Nat.mul (Nat.add curS R) (Nat.add curS R)))) = false := by
    cases h : and (Nat.blt (Nat.mul 16 (Nat.add curQ qLr)) (Nat.add 881995 (Nat.mul (Nat.add curS L) (Nat.add curS L))))
                  (Nat.blt (Nat.mul 16 (Nat.add curQ qRr)) (Nat.add 881995 (Nat.mul (Nat.add curS R) (Nat.add curS R))))
    · rfl
    · exfalso; simp only [Bool.and_eq_true, Nat.blt_eq] at h
      exact convex_seg_quad (C := 16) (D := 1) (K := 881995) (curS := curS) (curQ := curQ) (bQ0 := bQ0) (lv := lv) (by omega) hbL hLT hTR
        (by have := hok_u.2.2.2.1; dsimp [bQ0]; omega)
        (by have h1 := h.1; change 16 * (curQ + (bQ0 + mL * mL)) < 881995 + (curS + L) * (curS + L) at h1; rw [hsqL, hsqSL] at h1; omega)
        (by have h2 := h.2; change 16 * (curQ + (bQ0 + mR * mR)) < 881995 + (curS + R) * (curS + R) at h2; rw [hsqR, hsqSR] at h2; omega)
  have hno4 : and (Nat.blt (Nat.mul 126 (Nat.add curQ qLr)) (Nat.add 9924583 (Nat.mul 3 (Nat.mul (Nat.add curS L) (Nat.add curS L)))))
                  (Nat.blt (Nat.mul 126 (Nat.add curQ qRr)) (Nat.add 9924583 (Nat.mul 3 (Nat.mul (Nat.add curS R) (Nat.add curS R))))) = false := by
    cases h : and (Nat.blt (Nat.mul 126 (Nat.add curQ qLr)) (Nat.add 9924583 (Nat.mul 3 (Nat.mul (Nat.add curS L) (Nat.add curS L)))))
                  (Nat.blt (Nat.mul 126 (Nat.add curQ qRr)) (Nat.add 9924583 (Nat.mul 3 (Nat.mul (Nat.add curS R) (Nat.add curS R)))))
    · rfl
    · exfalso; simp only [Bool.and_eq_true, Nat.blt_eq] at h
      exact convex_seg_quad (C := 126) (D := 3) (K := 9924583) (curS := curS) (curQ := curQ) (bQ0 := bQ0) (lv := lv) (by omega) hbL hLT hTR
        (by have := hok_u.2.2.2.2.1; dsimp [bQ0]; omega)
        (by have h1 := h.1; change 126 * (curQ + (bQ0 + mL * mL)) < 9924583 + 3 * ((curS + L) * (curS + L)) at h1; rw [hsqL, hsqSL] at h1; omega)
        (by have h2 := h.2; change 126 * (curQ + (bQ0 + mR * mR)) < 9924583 + 3 * ((curS + R) * (curS + R)) at h2; rw [hsqR, hsqSR] at h2; omega)
  have hno5 : and (Nat.blt (Nat.mul 256 (Nat.add curQ qLr)) (Nat.add 22108415 (Nat.mul (Nat.add curS L) (Nat.add curS L))))
                  (Nat.blt (Nat.mul 256 (Nat.add curQ qRr)) (Nat.add 22108415 (Nat.mul (Nat.add curS R) (Nat.add curS R)))) = false := by
    cases h : and (Nat.blt (Nat.mul 256 (Nat.add curQ qLr)) (Nat.add 22108415 (Nat.mul (Nat.add curS L) (Nat.add curS L))))
                  (Nat.blt (Nat.mul 256 (Nat.add curQ qRr)) (Nat.add 22108415 (Nat.mul (Nat.add curS R) (Nat.add curS R))))
    · rfl
    · exfalso; simp only [Bool.and_eq_true, Nat.blt_eq] at h
      exact convex_seg_quad (C := 256) (D := 1) (K := 22108415) (curS := curS) (curQ := curQ) (bQ0 := bQ0) (lv := lv) (by omega) hbL hLT hTR
        (by have := hok_u.2.2.2.2.2; dsimp [bQ0]; omega)
        (by have h1 := h.1; change 256 * (curQ + (bQ0 + mL * mL)) < 22108415 + (curS + L) * (curS + L) at h1; rw [hsqL, hsqSL] at h1; omega)
        (by have h2 := h.2; change 256 * (curQ + (bQ0 + mR * mR)) < 22108415 + (curS + R) * (curS + R) at h2; rw [hsqR, hsqSR] at h2; omega)
  simp only [hno1, hno2, hno3, hno4, hno5, Bool.false_eq_true, ite_false]
  exact checkSegLoop_true (T := T)
    (by dsimp [bQ0]; change QRmin ≤ bQ - lv * lv + (lv + (T - bS)) * (lv + (T - bS)); rw [← sq (lv + (T - bS))]; exact hQR)
    (by dsimp [bQ0]; change okSQ qlb (curS + T) (curQ + (bQ - lv * lv + (lv + (T - bS)) * (lv + (T - bS)))) = true; rw [← sq (lv + (T - bS))]; exact hok)
    (Nat.sub R (Nat.add L 1)) (Nat.add L 1) (by change L + 1 ≤ T; omega) (by change T < L + 1 + (R - (L + 1)); omega)

private lemma sq_sub_ge_linear (x y c : ℤ) (h : (y - x) * (y + x - 2 * c) ≥ 0) :
    y ^ 2 - x ^ 2 ≥ 2 * c * (y - x) := by nlinarith only [h]

private lemma box_seg_ineq_2 {x0 x1 y0 y1 c : ℤ}
    (hsum : y0 + y1 = x0 + x1)
    (h0 : (y0 - x0) * (y0 + x0 - 2 * c) ≥ 0)
    (h1 : (y1 - x1) * (y1 + x1 - 2 * c) ≥ 0) :
    x0 ^ 2 + x1 ^ 2 ≤ y0 ^ 2 + y1 ^ 2 := by
  have i0 := sq_sub_ge_linear x0 y0 c h0
  have i1 := sq_sub_ge_linear x1 y1 c h1
  have hc : 2 * c * (y0 - x0) + 2 * c * (y1 - x1) = 0 := by
    have : 2 * c * (y0 - x0) + 2 * c * (y1 - x1) = 2 * c * ((y0 + y1) - (x0 + x1)) := by ring
    rw [this, hsum, sub_self, mul_zero]
  linarith only [i0, i1, hc]

private lemma box_seg_ineq_3 {x0 x1 x2 y0 y1 y2 c : ℤ}
    (hsum : y0 + y1 + y2 = x0 + x1 + x2)
    (h0 : (y0 - x0) * (y0 + x0 - 2 * c) ≥ 0)
    (h1 : (y1 - x1) * (y1 + x1 - 2 * c) ≥ 0)
    (h2 : (y2 - x2) * (y2 + x2 - 2 * c) ≥ 0) :
    x0 ^ 2 + x1 ^ 2 + x2 ^ 2 ≤ y0 ^ 2 + y1 ^ 2 + y2 ^ 2 := by
  have i0 := sq_sub_ge_linear x0 y0 c h0
  have i1 := sq_sub_ge_linear x1 y1 c h1
  have i2 := sq_sub_ge_linear x2 y2 c h2
  have hc : 2 * c * (y0 - x0) + 2 * c * (y1 - x1) + 2 * c * (y2 - x2) = 0 := by
    have : 2 * c * (y0 - x0) + 2 * c * (y1 - x1) + 2 * c * (y2 - x2) = 2 * c * ((y0 + y1 + y2) - (x0 + x1 + x2)) := by ring
    rw [this, hsum, sub_self, mul_zero]
  linarith only [i0, i1, i2, hc]

private lemma box_seg_ineq_4 {x0 x1 x2 x3 y0 y1 y2 y3 c : ℤ}
    (hsum : y0 + y1 + y2 + y3 = x0 + x1 + x2 + x3)
    (h0 : (y0 - x0) * (y0 + x0 - 2 * c) ≥ 0)
    (h1 : (y1 - x1) * (y1 + x1 - 2 * c) ≥ 0)
    (h2 : (y2 - x2) * (y2 + x2 - 2 * c) ≥ 0)
    (h3 : (y3 - x3) * (y3 + x3 - 2 * c) ≥ 0) :
    x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 ≤ y0 ^ 2 + y1 ^ 2 + y2 ^ 2 + y3 ^ 2 := by
  have i0 := sq_sub_ge_linear x0 y0 c h0
  have i1 := sq_sub_ge_linear x1 y1 c h1
  have i2 := sq_sub_ge_linear x2 y2 c h2
  have i3 := sq_sub_ge_linear x3 y3 c h3
  have hc : 2 * c * (y0 - x0) + 2 * c * (y1 - x1) + 2 * c * (y2 - x2) + 2 * c * (y3 - x3) = 0 := by
    have : 2 * c * (y0 - x0) + 2 * c * (y1 - x1) + 2 * c * (y2 - x2) + 2 * c * (y3 - x3) =
        2 * c * ((y0 + y1 + y2 + y3) - (x0 + x1 + x2 + x3)) := by ring
    rw [this, hsum, sub_self, mul_zero]
  linarith only [i0, i1, i2, i3, hc]

private lemma box_seg_ineq_5 {x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 c : ℤ}
    (hsum : y0 + y1 + y2 + y3 + y4 = x0 + x1 + x2 + x3 + x4)
    (h0 : (y0 - x0) * (y0 + x0 - 2 * c) ≥ 0)
    (h1 : (y1 - x1) * (y1 + x1 - 2 * c) ≥ 0)
    (h2 : (y2 - x2) * (y2 + x2 - 2 * c) ≥ 0)
    (h3 : (y3 - x3) * (y3 + x3 - 2 * c) ≥ 0)
    (h4 : (y4 - x4) * (y4 + x4 - 2 * c) ≥ 0) :
    x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 ≤ y0 ^ 2 + y1 ^ 2 + y2 ^ 2 + y3 ^ 2 + y4 ^ 2 := by
  have i0 := sq_sub_ge_linear x0 y0 c h0
  have i1 := sq_sub_ge_linear x1 y1 c h1
  have i2 := sq_sub_ge_linear x2 y2 c h2
  have i3 := sq_sub_ge_linear x3 y3 c h3
  have i4 := sq_sub_ge_linear x4 y4 c h4
  have hc : 2 * c * (y0 - x0) + 2 * c * (y1 - x1) + 2 * c * (y2 - x2) + 2 * c * (y3 - x3) + 2 * c * (y4 - x4) = 0 := by
    have : 2 * c * (y0 - x0) + 2 * c * (y1 - x1) + 2 * c * (y2 - x2) + 2 * c * (y3 - x3) + 2 * c * (y4 - x4) =
        2 * c * ((y0 + y1 + y2 + y3 + y4) - (x0 + x1 + x2 + x3 + x4)) := by ring
    rw [this, hsum, sub_self, mul_zero]
  linarith only [i0, i1, i2, i3, i4, hc]

private lemma checkBox2_sound {qlb curS curQ Tlo Thi QRmin l0 h0 l1 h1 x0 x1 : ℕ}
    (hb0 : l0 ≤ x0 ∧ x0 ≤ h0) (hb1 : l1 ≤ x1 ∧ x1 ≤ h1) (hord : x1 ≤ x0)
    (hT : Tlo ≤ x0 + x1 ∧ x0 + x1 ≤ Thi) (hQR : QRmin ≤ x0 ^ 2 + x1 ^ 2)
    (hok : okSQ qlb (curS + (x0 + x1)) (curQ + (x0 ^ 2 + x1 ^ 2)) = true) :
    checkBox2 qlb curS curQ Tlo Thi QRmin l0 h0 l1 h1 = true := by
  unfold checkBox2; dsimp only
  let T := x0 + x1
  have hnL : nmax Tlo (Nat.add l0 l1) ≤ T := by rw [nmax_eq]; exact max_le hT.1 (by dsimp [T]; omega)
  have hnR : T ≤ nmin Thi (Nat.add h0 h1) := by rw [nmin_eq]; exact le_min hT.2 (by dsimp [T]; omega)
  change (if Nat.blt (nmin Thi (Nat.add h0 h1)) (nmax Tlo (Nat.add l0 l1)) = true then false else _) = true
  simp only [blt_false_of_le (le_trans hnL hnR), Bool.false_eq_true, ite_false]
  by_cases hs : T ≤ h0 + l1
  · have hq : x0 ^ 2 + x1 ^ 2 ≤ (l0 * l0 + l1 * l1 - l0 * l0) + (l0 + (T - (l0 + l1))) ^ 2 := by
      have hsub : l0 * l0 + l1 * l1 - l0 * l0 = l1 * l1 := by omega
      rw [hsub, ← sq l1]
      have hge : l0 + l1 ≤ T := by dsimp [T]; omega
      zify [hge]; rw [add_comm ((l1 : ℤ) ^ 2)]
      refine box_seg_ineq_2 (c := (x0 : ℤ)) (by dsimp [T]; omega) ?_ ?_
      · have hsq : ((l0 : ℤ) + ((T : ℤ) - ((l0 : ℤ) + (l1 : ℤ))) - (x0 : ℤ)) *
            ((l0 : ℤ) + ((T : ℤ) - ((l0 : ℤ) + (l1 : ℤ))) + (x0 : ℤ) - 2 * (x0 : ℤ)) =
            ((l0 : ℤ) + ((T : ℤ) - ((l0 : ℤ) + (l1 : ℤ))) - (x0 : ℤ)) ^ 2 := by ring
        rw [hsq]; exact sq_nonneg _
      · have : (l1 : ℤ) ≤ (x1 : ℤ) := by exact_mod_cast hb1.1
        have : (x1 : ℤ) ≤ (x0 : ℤ) := by exact_mod_cast hord
        nlinarith only [‹(l1 : ℤ) ≤ (x1 : ℤ)›, ‹(x1 : ℤ) ≤ (x0 : ℤ)›]
    have hseg := checkSeg_sound (bS := l0 + l1) (bQ := l0 * l0 + l1 * l1) (lv := l0) (segR := h0 + l1) (T := T)
      ⟨hnL, hnR⟩ ⟨by dsimp [T]; omega, hs⟩ (le_trans hQR hq) (okSQ_mono le_rfl (Nat.add_le_add_left hq curQ) hok)
    change (if checkSeg qlb curS curQ QRmin (l0 + l1) (l0 * l0 + l1 * l1) l0 _ _ (h0 + l1) = true then true else _) = true
    rw [hseg]; rfl
  · have hq : x0 ^ 2 + x1 ^ 2 ≤ (h0 * h0 + l1 * l1 - l1 * l1) + (l1 + (T - (h0 + l1))) ^ 2 := by
      have hsub : h0 * h0 + l1 * l1 - l1 * l1 = h0 * h0 := by omega
      rw [hsub, ← sq h0]
      have hge : h0 + l1 ≤ T := by omega
      zify [hge]
      refine box_seg_ineq_2 (c := (x1 : ℤ)) (by dsimp [T]; omega) ?_ ?_
      · have : (x0 : ℤ) ≤ (h0 : ℤ) := by exact_mod_cast hb0.2
        have : (x1 : ℤ) ≤ (x0 : ℤ) := by exact_mod_cast hord
        nlinarith only [‹(x0 : ℤ) ≤ (h0 : ℤ)›, ‹(x1 : ℤ) ≤ (x0 : ℤ)›]
      · have hsq : ((l1 : ℤ) + ((T : ℤ) - ((h0 : ℤ) + (l1 : ℤ))) - (x1 : ℤ)) *
            ((l1 : ℤ) + ((T : ℤ) - ((h0 : ℤ) + (l1 : ℤ))) + (x1 : ℤ) - 2 * (x1 : ℤ)) =
            ((l1 : ℤ) + ((T : ℤ) - ((h0 : ℤ) + (l1 : ℤ))) - (x1 : ℤ)) ^ 2 := by ring
        rw [hsq]; exact sq_nonneg _
    have hseg := checkSeg_sound (bS := h0 + l1) (bQ := h0 * h0 + l1 * l1) (lv := l1) (segR := h0 + h1) (T := T)
      ⟨hnL, hnR⟩ ⟨by omega, by dsimp [T]; omega⟩ (le_trans hQR hq) (okSQ_mono le_rfl (Nat.add_le_add_left hq curQ) hok)
    change (if _ then true else checkSeg qlb curS curQ QRmin (h0 + l1) (h0 * h0 + l1 * l1) l1 _ _ (h0 + h1)) = true
    split_ifs <;> first | rfl | exact hseg

private lemma checkBox3_sound {qlb curS curQ Tlo Thi QRmin l0 h0 l1 h1 l2 h2 x0 x1 x2 : ℕ}
    (hb0 : l0 ≤ x0 ∧ x0 ≤ h0) (hb1 : l1 ≤ x1 ∧ x1 ≤ h1) (hb2 : l2 ≤ x2 ∧ x2 ≤ h2)
    (hord : x2 ≤ x1 ∧ x1 ≤ x0)
    (hT : Tlo ≤ x0 + x1 + x2 ∧ x0 + x1 + x2 ≤ Thi) (hQR : QRmin ≤ x0 ^ 2 + x1 ^ 2 + x2 ^ 2)
    (hok : okSQ qlb (curS + (x0 + x1 + x2)) (curQ + (x0 ^ 2 + x1 ^ 2 + x2 ^ 2)) = true) :
    checkBox3 qlb curS curQ Tlo Thi QRmin l0 h0 l1 h1 l2 h2 = true := by
  unfold checkBox3; dsimp only
  let T := x0 + x1 + x2
  have hnL : nmax Tlo (Nat.add l0 (Nat.add l1 l2)) ≤ T := by rw [nmax_eq]; exact max_le hT.1 (by dsimp [T]; omega)
  have hnR : T ≤ nmin Thi (Nat.add h0 (Nat.add h1 h2)) := by rw [nmin_eq]; exact le_min hT.2 (by dsimp [T]; omega)
  change (if Nat.blt (nmin Thi (Nat.add h0 (Nat.add h1 h2))) (nmax Tlo (Nat.add l0 (Nat.add l1 l2))) = true then false else _) = true
  simp only [blt_false_of_le (le_trans hnL hnR), Bool.false_eq_true, ite_false]
  have hle_hi : ∀ a b c : ℤ, a ≤ b → c ≤ a → (b - a) * (b + a - 2 * c) ≥ 0 := fun a b c h1 h2 => by nlinarith only [h1, h2]
  have hle_lo : ∀ a b c : ℤ, b ≤ a → a ≤ c → (b - a) * (b + a - 2 * c) ≥ 0 := fun a b c h1 h2 => by nlinarith only [h1, h2]
  have hself : ∀ a b : ℤ, (b - a) * (b + a - 2 * a) ≥ 0 := fun a b => by
    have : (b - a) * (b + a - 2 * a) = (b - a) ^ 2 := by ring
    rw [this]; exact sq_nonneg _
  by_cases hs1 : T ≤ h0 + (l1 + l2)
  · have hq : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 ≤
        (l0 * l0 + (l1 * l1 + l2 * l2) - l0 * l0) + (l0 + (T - (l0 + (l1 + l2)))) ^ 2 := by
      have hsub : l0 * l0 + (l1 * l1 + l2 * l2) - l0 * l0 = l1 ^ 2 + l2 ^ 2 := by rw [sq, sq]; omega
      rw [hsub]; zify [show l0 + (l1 + l2) ≤ T by dsimp [T]; omega]
      have := box_seg_ineq_3 (x0 := (x0 : ℤ)) (x1 := (x1 : ℤ)) (x2 := (x2 : ℤ))
        (y0 := (l0 : ℤ) + ((T : ℤ) - ((l0 : ℤ) + ((l1 : ℤ) + (l2 : ℤ))))) (y1 := (l1 : ℤ)) (y2 := (l2 : ℤ)) (c := (x0 : ℤ))
        (by dsimp [T]; omega) (hself _ _) (hle_lo _ _ _ (by exact_mod_cast hb1.1) (by exact_mod_cast hord.2))
        (hle_lo _ _ _ (by exact_mod_cast hb2.1) (by exact_mod_cast le_trans hord.1 hord.2))
      linarith only [this]
    have hseg := checkSeg_sound (bS := l0 + (l1 + l2)) (bQ := l0 * l0 + (l1 * l1 + l2 * l2)) (lv := l0) (segR := h0 + (l1 + l2)) (T := T)
      ⟨hnL, hnR⟩ ⟨by dsimp [T]; omega, hs1⟩ (le_trans hQR hq) (okSQ_mono le_rfl (Nat.add_le_add_left hq curQ) hok)
    change (if checkSeg qlb curS curQ QRmin (l0 + (l1 + l2)) (l0 * l0 + (l1 * l1 + l2 * l2)) l0 _ _ (h0 + (l1 + l2)) = true then true else _) = true
    rw [hseg]; rfl
  · by_cases hs2 : T ≤ h0 + (h1 + l2)
    · have hq : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 ≤
          (h0 * h0 + (l1 * l1 + l2 * l2) - l1 * l1) + (l1 + (T - (h0 + (l1 + l2)))) ^ 2 := by
        have hsub : h0 * h0 + (l1 * l1 + l2 * l2) - l1 * l1 = h0 ^ 2 + l2 ^ 2 := by rw [sq, sq]; omega
        rw [hsub]; zify [show h0 + (l1 + l2) ≤ T by omega]
        have := box_seg_ineq_3 (x0 := (x0 : ℤ)) (x1 := (x1 : ℤ)) (x2 := (x2 : ℤ))
          (y0 := (h0 : ℤ)) (y1 := (l1 : ℤ) + ((T : ℤ) - ((h0 : ℤ) + ((l1 : ℤ) + (l2 : ℤ))))) (y2 := (l2 : ℤ)) (c := (x1 : ℤ))
          (by dsimp [T]; omega) (hle_hi _ _ _ (by exact_mod_cast hb0.2) (by exact_mod_cast hord.2))
          (hself _ _) (hle_lo _ _ _ (by exact_mod_cast hb2.1) (by exact_mod_cast hord.1))
        linarith only [this]
      have hseg := checkSeg_sound (bS := h0 + (l1 + l2)) (bQ := h0 * h0 + (l1 * l1 + l2 * l2)) (lv := l1) (segR := h0 + (h1 + l2)) (T := T)
        ⟨hnL, hnR⟩ ⟨by omega, hs2⟩ (le_trans hQR hq) (okSQ_mono le_rfl (Nat.add_le_add_left hq curQ) hok)
      change (if _ then true else if checkSeg qlb curS curQ QRmin (h0 + (l1 + l2)) (h0 * h0 + (l1 * l1 + l2 * l2)) l1 _ _ (h0 + (h1 + l2)) = true then true else _) = true
      split_ifs <;> rfl
    · have hq : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 ≤
          (h0 * h0 + (h1 * h1 + l2 * l2) - l2 * l2) + (l2 + (T - (h0 + (h1 + l2)))) ^ 2 := by
        have hsub : h0 * h0 + (h1 * h1 + l2 * l2) - l2 * l2 = h0 ^ 2 + h1 ^ 2 := by rw [sq, sq]; omega
        rw [hsub]; zify [show h0 + (h1 + l2) ≤ T by omega]
        have := box_seg_ineq_3 (x0 := (x0 : ℤ)) (x1 := (x1 : ℤ)) (x2 := (x2 : ℤ))
          (y0 := (h0 : ℤ)) (y1 := (h1 : ℤ)) (y2 := (l2 : ℤ) + ((T : ℤ) - ((h0 : ℤ) + ((h1 : ℤ) + (l2 : ℤ))))) (c := (x2 : ℤ))
          (by dsimp [T]; omega) (hle_hi _ _ _ (by exact_mod_cast hb0.2) (by exact_mod_cast le_trans hord.1 hord.2))
          (hle_hi _ _ _ (by exact_mod_cast hb1.2) (by exact_mod_cast hord.1)) (hself _ _)
        linarith only [this]
      have hseg := checkSeg_sound (bS := h0 + (h1 + l2)) (bQ := h0 * h0 + (h1 * h1 + l2 * l2)) (lv := l2) (segR := h0 + (h1 + h2)) (T := T)
        ⟨hnL, hnR⟩ ⟨by omega, by dsimp [T]; omega⟩ (le_trans hQR hq) (okSQ_mono le_rfl (Nat.add_le_add_left hq curQ) hok)
      change (if _ then true else if _ then true else checkSeg qlb curS curQ QRmin (h0 + (h1 + l2)) (h0 * h0 + (h1 * h1 + l2 * l2)) l2 _ _ (h0 + (h1 + h2))) = true
      split_ifs <;> first | rfl | exact hseg

private lemma checkBox4_sound {qlb curS curQ Tlo Thi QRmin l0 h0 l1 h1 l2 h2 l3 h3 x0 x1 x2 x3 : ℕ}
    (hb0 : l0 ≤ x0 ∧ x0 ≤ h0) (hb1 : l1 ≤ x1 ∧ x1 ≤ h1) (hb2 : l2 ≤ x2 ∧ x2 ≤ h2) (hb3 : l3 ≤ x3 ∧ x3 ≤ h3)
    (hord : x3 ≤ x2 ∧ x2 ≤ x1 ∧ x1 ≤ x0)
    (hT : Tlo ≤ x0 + x1 + x2 + x3 ∧ x0 + x1 + x2 + x3 ≤ Thi)
    (hQR : QRmin ≤ x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2)
    (hok : okSQ qlb (curS + (x0 + x1 + x2 + x3)) (curQ + (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2)) = true) :
    checkBox4 qlb curS curQ Tlo Thi QRmin l0 h0 l1 h1 l2 h2 l3 h3 = true := by
  unfold checkBox4; dsimp only
  let T := x0 + x1 + x2 + x3
  have hnL : nmax Tlo (Nat.add l0 (Nat.add l1 (Nat.add l2 l3))) ≤ T := by rw [nmax_eq]; exact max_le hT.1 (by dsimp [T]; omega)
  have hnR : T ≤ nmin Thi (Nat.add h0 (Nat.add h1 (Nat.add h2 h3))) := by rw [nmin_eq]; exact le_min hT.2 (by dsimp [T]; omega)
  change (if Nat.blt (nmin Thi (Nat.add h0 (Nat.add h1 (Nat.add h2 h3)))) (nmax Tlo (Nat.add l0 (Nat.add l1 (Nat.add l2 l3)))) = true then false else _) = true
  simp only [blt_false_of_le (le_trans hnL hnR), Bool.false_eq_true, ite_false]
  have hle_hi : ∀ a b c : ℤ, a ≤ b → c ≤ a → (b - a) * (b + a - 2 * c) ≥ 0 := fun a b c h1 h2 => by nlinarith only [h1, h2]
  have hle_lo : ∀ a b c : ℤ, b ≤ a → a ≤ c → (b - a) * (b + a - 2 * c) ≥ 0 := fun a b c h1 h2 => by nlinarith only [h1, h2]
  have hself : ∀ a b : ℤ, (b - a) * (b + a - 2 * a) ≥ 0 := fun a b => by
    have : (b - a) * (b + a - 2 * a) = (b - a) ^ 2 := by ring
    rw [this]; exact sq_nonneg _
  by_cases hs1 : T ≤ h0 + (l1 + (l2 + l3))
  · have hq : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 ≤
        (l0 * l0 + (l1 * l1 + (l2 * l2 + l3 * l3)) - l0 * l0) + (l0 + (T - (l0 + (l1 + (l2 + l3))))) ^ 2 := by
      have hsub : l0 * l0 + (l1 * l1 + (l2 * l2 + l3 * l3)) - l0 * l0 = l1 ^ 2 + l2 ^ 2 + l3 ^ 2 := by rw [sq, sq, sq]; omega
      rw [hsub]; zify [show l0 + (l1 + (l2 + l3)) ≤ T by dsimp [T]; omega]
      have := box_seg_ineq_4 (x0 := (x0 : ℤ)) (x1 := (x1 : ℤ)) (x2 := (x2 : ℤ)) (x3 := (x3 : ℤ))
        (y0 := (l0 : ℤ) + ((T : ℤ) - ((l0 : ℤ) + ((l1 : ℤ) + ((l2 : ℤ) + (l3 : ℤ)))))) (y1 := (l1 : ℤ)) (y2 := (l2 : ℤ)) (y3 := (l3 : ℤ)) (c := (x0 : ℤ))
        (by dsimp [T]; omega) (hself _ _) (hle_lo _ _ _ (by exact_mod_cast hb1.1) (by exact_mod_cast hord.2.2))
        (hle_lo _ _ _ (by exact_mod_cast hb2.1) (by exact_mod_cast le_trans hord.2.1 hord.2.2))
        (hle_lo _ _ _ (by exact_mod_cast hb3.1) (by exact_mod_cast le_trans hord.1 (le_trans hord.2.1 hord.2.2)))
      linarith only [this]
    have hseg := checkSeg_sound (bS := l0 + (l1 + (l2 + l3))) (bQ := l0 * l0 + (l1 * l1 + (l2 * l2 + l3 * l3))) (lv := l0) (segR := h0 + (l1 + (l2 + l3))) (T := T)
      ⟨hnL, hnR⟩ ⟨by dsimp [T]; omega, hs1⟩ (le_trans hQR hq) (okSQ_mono le_rfl (Nat.add_le_add_left hq curQ) hok)
    change (if checkSeg qlb curS curQ QRmin (l0 + (l1 + (l2 + l3))) (l0 * l0 + (l1 * l1 + (l2 * l2 + l3 * l3))) l0 _ _ (h0 + (l1 + (l2 + l3))) = true then true else _) = true
    rw [hseg]; rfl
  · by_cases hs2 : T ≤ h0 + (h1 + (l2 + l3))
    · have hq : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 ≤
          (h0 * h0 + (l1 * l1 + (l2 * l2 + l3 * l3)) - l1 * l1) + (l1 + (T - (h0 + (l1 + (l2 + l3))))) ^ 2 := by
        have hsub : h0 * h0 + (l1 * l1 + (l2 * l2 + l3 * l3)) - l1 * l1 = h0 ^ 2 + l2 ^ 2 + l3 ^ 2 := by rw [sq, sq, sq]; omega
        rw [hsub]; zify [show h0 + (l1 + (l2 + l3)) ≤ T by omega]
        have := box_seg_ineq_4 (x0 := (x0 : ℤ)) (x1 := (x1 : ℤ)) (x2 := (x2 : ℤ)) (x3 := (x3 : ℤ))
          (y0 := (h0 : ℤ)) (y1 := (l1 : ℤ) + ((T : ℤ) - ((h0 : ℤ) + ((l1 : ℤ) + ((l2 : ℤ) + (l3 : ℤ)))))) (y2 := (l2 : ℤ)) (y3 := (l3 : ℤ)) (c := (x1 : ℤ))
          (by dsimp [T]; omega) (hle_hi _ _ _ (by exact_mod_cast hb0.2) (by exact_mod_cast hord.2.2))
          (hself _ _) (hle_lo _ _ _ (by exact_mod_cast hb2.1) (by exact_mod_cast hord.2.1))
          (hle_lo _ _ _ (by exact_mod_cast hb3.1) (by exact_mod_cast le_trans hord.1 hord.2.1))
        linarith only [this]
      have hseg := checkSeg_sound (bS := h0 + (l1 + (l2 + l3))) (bQ := h0 * h0 + (l1 * l1 + (l2 * l2 + l3 * l3))) (lv := l1) (segR := h0 + (h1 + (l2 + l3))) (T := T)
        ⟨hnL, hnR⟩ ⟨by omega, hs2⟩ (le_trans hQR hq) (okSQ_mono le_rfl (Nat.add_le_add_left hq curQ) hok)
      change (if _ then true else if checkSeg qlb curS curQ QRmin (h0 + (l1 + (l2 + l3))) (h0 * h0 + (l1 * l1 + (l2 * l2 + l3 * l3))) l1 _ _ (h0 + (h1 + (l2 + l3))) = true then true else _) = true
      split_ifs <;> rfl
    · by_cases hs3 : T ≤ h0 + (h1 + (h2 + l3))
      · have hq : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 ≤
            ((h0 * h0 + h1 * h1) + (l2 * l2 + l3 * l3) - l2 * l2) + (l2 + (T - (h0 + (h1 + (l2 + l3))))) ^ 2 := by
          have hsub : (h0 * h0 + h1 * h1) + (l2 * l2 + l3 * l3) - l2 * l2 = h0 ^ 2 + h1 ^ 2 + l3 ^ 2 := by rw [sq, sq, sq]; omega
          rw [hsub]; zify [show h0 + (h1 + (l2 + l3)) ≤ T by omega]
          have := box_seg_ineq_4 (x0 := (x0 : ℤ)) (x1 := (x1 : ℤ)) (x2 := (x2 : ℤ)) (x3 := (x3 : ℤ))
            (y0 := (h0 : ℤ)) (y1 := (h1 : ℤ)) (y2 := (l2 : ℤ) + ((T : ℤ) - ((h0 : ℤ) + ((h1 : ℤ) + ((l2 : ℤ) + (l3 : ℤ)))))) (y3 := (l3 : ℤ)) (c := (x2 : ℤ))
            (by dsimp [T]; omega) (hle_hi _ _ _ (by exact_mod_cast hb0.2) (by exact_mod_cast le_trans hord.2.1 hord.2.2))
            (hle_hi _ _ _ (by exact_mod_cast hb1.2) (by exact_mod_cast hord.2.1))
            (hself _ _) (hle_lo _ _ _ (by exact_mod_cast hb3.1) (by exact_mod_cast hord.1))
          linarith only [this]
        have hseg := checkSeg_sound (bS := h0 + (h1 + (l2 + l3))) (bQ := (h0 * h0 + h1 * h1) + (l2 * l2 + l3 * l3)) (lv := l2) (segR := h0 + (h1 + (h2 + l3))) (T := T)
          ⟨hnL, hnR⟩ ⟨by omega, hs3⟩ (le_trans hQR hq) (okSQ_mono le_rfl (Nat.add_le_add_left hq curQ) hok)
        change (if _ then true else if _ then true else if checkSeg qlb curS curQ QRmin (h0 + (h1 + (l2 + l3))) ((h0 * h0 + h1 * h1) + (l2 * l2 + l3 * l3)) l2 _ _ (h0 + (h1 + (h2 + l3))) = true then true else _) = true
        split_ifs <;> rfl
      · have hq : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 ≤
            ((h0 * h0 + h1 * h1) + (h2 * h2 + l3 * l3) - l3 * l3) + (l3 + (T - (h0 + (h1 + (h2 + l3))))) ^ 2 := by
          have hsub : (h0 * h0 + h1 * h1) + (h2 * h2 + l3 * l3) - l3 * l3 = h0 ^ 2 + h1 ^ 2 + h2 ^ 2 := by rw [sq, sq, sq]; omega
          rw [hsub]; zify [show h0 + (h1 + (h2 + l3)) ≤ T by omega]
          have := box_seg_ineq_4 (x0 := (x0 : ℤ)) (x1 := (x1 : ℤ)) (x2 := (x2 : ℤ)) (x3 := (x3 : ℤ))
            (y0 := (h0 : ℤ)) (y1 := (h1 : ℤ)) (y2 := (h2 : ℤ)) (y3 := (l3 : ℤ) + ((T : ℤ) - ((h0 : ℤ) + ((h1 : ℤ) + ((h2 : ℤ) + (l3 : ℤ)))))) (c := (x3 : ℤ))
            (by dsimp [T]; omega) (hle_hi _ _ _ (by exact_mod_cast hb0.2) (by exact_mod_cast le_trans hord.1 (le_trans hord.2.1 hord.2.2)))
            (hle_hi _ _ _ (by exact_mod_cast hb1.2) (by exact_mod_cast le_trans hord.1 hord.2.1))
            (hle_hi _ _ _ (by exact_mod_cast hb2.2) (by exact_mod_cast hord.1)) (hself _ _)
          linarith only [this]
        have hseg := checkSeg_sound (bS := h0 + (h1 + (h2 + l3))) (bQ := (h0 * h0 + h1 * h1) + (h2 * h2 + l3 * l3)) (lv := l3) (segR := h0 + (h1 + (h2 + h3))) (T := T)
          ⟨hnL, hnR⟩ ⟨by omega, by dsimp [T]; omega⟩ (le_trans hQR hq) (okSQ_mono le_rfl (Nat.add_le_add_left hq curQ) hok)
        change (if _ then true else if _ then true else if _ then true else checkSeg qlb curS curQ QRmin (h0 + (h1 + (h2 + l3))) ((h0 * h0 + h1 * h1) + (h2 * h2 + l3 * l3)) l3 _ _ (h0 + (h1 + (h2 + h3)))) = true
        split_ifs <;> first | rfl | exact hseg

private lemma checkBox5_sound {qlb curS curQ Tlo Thi QRmin l0 h0 l1 h1 l2 h2 l3 h3 l4 h4 x0 x1 x2 x3 x4 : ℕ}
    (hb0 : l0 ≤ x0 ∧ x0 ≤ h0) (hb1 : l1 ≤ x1 ∧ x1 ≤ h1) (hb2 : l2 ≤ x2 ∧ x2 ≤ h2)
    (hb3 : l3 ≤ x3 ∧ x3 ≤ h3) (hb4 : l4 ≤ x4 ∧ x4 ≤ h4)
    (hord : x4 ≤ x3 ∧ x3 ≤ x2 ∧ x2 ≤ x1 ∧ x1 ≤ x0)
    (hT : Tlo ≤ x0 + x1 + x2 + x3 + x4 ∧ x0 + x1 + x2 + x3 + x4 ≤ Thi)
    (hQR : QRmin ≤ x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2)
    (hok : okSQ qlb (curS + (x0 + x1 + x2 + x3 + x4)) (curQ + (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2)) = true) :
    checkBox5 qlb curS curQ Tlo Thi QRmin l0 h0 l1 h1 l2 h2 l3 h3 l4 h4 = true := by
  unfold checkBox5; dsimp only
  let T := x0 + x1 + x2 + x3 + x4
  have hnL : nmax Tlo (Nat.add l0 (Nat.add l1 (Nat.add l2 (Nat.add l3 l4)))) ≤ T := by rw [nmax_eq]; exact max_le hT.1 (by dsimp [T]; omega)
  have hnR : T ≤ nmin Thi (Nat.add h0 (Nat.add h1 (Nat.add h2 (Nat.add h3 h4)))) := by rw [nmin_eq]; exact le_min hT.2 (by dsimp [T]; omega)
  change (if Nat.blt (nmin Thi (Nat.add h0 (Nat.add h1 (Nat.add h2 (Nat.add h3 h4))))) (nmax Tlo (Nat.add l0 (Nat.add l1 (Nat.add l2 (Nat.add l3 l4))))) = true then false else _) = true
  simp only [blt_false_of_le (le_trans hnL hnR), Bool.false_eq_true, ite_false]
  have hle_hi : ∀ a b c : ℤ, a ≤ b → c ≤ a → (b - a) * (b + a - 2 * c) ≥ 0 := fun a b c h1 h2 => by nlinarith only [h1, h2]
  have hle_lo : ∀ a b c : ℤ, b ≤ a → a ≤ c → (b - a) * (b + a - 2 * c) ≥ 0 := fun a b c h1 h2 => by nlinarith only [h1, h2]
  have hself : ∀ a b : ℤ, (b - a) * (b + a - 2 * a) ≥ 0 := fun a b => by
    have : (b - a) * (b + a - 2 * a) = (b - a) ^ 2 := by ring
    rw [this]; exact sq_nonneg _
  by_cases hs1 : T ≤ h0 + (l1 + (l2 + (l3 + l4)))
  · have hq : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 ≤
        (l0 * l0 + (l1 * l1 + (l2 * l2 + (l3 * l3 + l4 * l4))) - l0 * l0) + (l0 + (T - (l0 + (l1 + (l2 + (l3 + l4)))))) ^ 2 := by
      have hsub : l0 * l0 + (l1 * l1 + (l2 * l2 + (l3 * l3 + l4 * l4))) - l0 * l0 = l1 ^ 2 + l2 ^ 2 + l3 ^ 2 + l4 ^ 2 := by rw [sq, sq, sq, sq]; omega
      rw [hsub]; zify [show l0 + (l1 + (l2 + (l3 + l4))) ≤ T by dsimp [T]; omega]
      have := box_seg_ineq_5 (x0 := (x0 : ℤ)) (x1 := (x1 : ℤ)) (x2 := (x2 : ℤ)) (x3 := (x3 : ℤ)) (x4 := (x4 : ℤ))
        (y0 := (l0 : ℤ) + ((T : ℤ) - ((l0 : ℤ) + ((l1 : ℤ) + ((l2 : ℤ) + ((l3 : ℤ) + (l4 : ℤ))))))) (y1 := (l1 : ℤ)) (y2 := (l2 : ℤ)) (y3 := (l3 : ℤ)) (y4 := (l4 : ℤ)) (c := (x0 : ℤ))
        (by dsimp [T]; omega) (hself _ _) (hle_lo _ _ _ (by exact_mod_cast hb1.1) (by exact_mod_cast hord.2.2.2))
        (hle_lo _ _ _ (by exact_mod_cast hb2.1) (by exact_mod_cast le_trans hord.2.2.1 hord.2.2.2))
        (hle_lo _ _ _ (by exact_mod_cast hb3.1) (by exact_mod_cast le_trans hord.2.1 (le_trans hord.2.2.1 hord.2.2.2)))
        (hle_lo _ _ _ (by exact_mod_cast hb4.1) (by exact_mod_cast le_trans hord.1 (le_trans hord.2.1 (le_trans hord.2.2.1 hord.2.2.2))))
      linarith only [this]
    have hseg := checkSeg_sound (bS := l0 + (l1 + (l2 + (l3 + l4)))) (bQ := l0 * l0 + (l1 * l1 + (l2 * l2 + (l3 * l3 + l4 * l4)))) (lv := l0) (segR := h0 + (l1 + (l2 + (l3 + l4)))) (T := T)
      ⟨hnL, hnR⟩ ⟨by dsimp [T]; omega, hs1⟩ (le_trans hQR hq) (okSQ_mono le_rfl (Nat.add_le_add_left hq curQ) hok)
    change (if checkSeg qlb curS curQ QRmin (l0 + (l1 + (l2 + (l3 + l4)))) (l0 * l0 + (l1 * l1 + (l2 * l2 + (l3 * l3 + l4 * l4)))) l0 _ _ (h0 + (l1 + (l2 + (l3 + l4)))) = true then true else _) = true
    rw [hseg]; rfl
  · by_cases hs2 : T ≤ h0 + (h1 + (l2 + (l3 + l4)))
    · have hq : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 ≤
          (h0 * h0 + (l1 * l1 + (l2 * l2 + (l3 * l3 + l4 * l4))) - l1 * l1) + (l1 + (T - (h0 + (l1 + (l2 + (l3 + l4)))))) ^ 2 := by
        have hsub : h0 * h0 + (l1 * l1 + (l2 * l2 + (l3 * l3 + l4 * l4))) - l1 * l1 = h0 ^ 2 + l2 ^ 2 + l3 ^ 2 + l4 ^ 2 := by rw [sq, sq, sq, sq]; omega
        rw [hsub]; zify [show h0 + (l1 + (l2 + (l3 + l4))) ≤ T by omega]
        have := box_seg_ineq_5 (x0 := (x0 : ℤ)) (x1 := (x1 : ℤ)) (x2 := (x2 : ℤ)) (x3 := (x3 : ℤ)) (x4 := (x4 : ℤ))
          (y0 := (h0 : ℤ)) (y1 := (l1 : ℤ) + ((T : ℤ) - ((h0 : ℤ) + ((l1 : ℤ) + ((l2 : ℤ) + ((l3 : ℤ) + (l4 : ℤ))))))) (y2 := (l2 : ℤ)) (y3 := (l3 : ℤ)) (y4 := (l4 : ℤ)) (c := (x1 : ℤ))
          (by dsimp [T]; omega) (hle_hi _ _ _ (by exact_mod_cast hb0.2) (by exact_mod_cast hord.2.2.2))
          (hself _ _) (hle_lo _ _ _ (by exact_mod_cast hb2.1) (by exact_mod_cast hord.2.2.1))
          (hle_lo _ _ _ (by exact_mod_cast hb3.1) (by exact_mod_cast le_trans hord.2.1 hord.2.2.1))
          (hle_lo _ _ _ (by exact_mod_cast hb4.1) (by exact_mod_cast le_trans hord.1 (le_trans hord.2.1 hord.2.2.1)))
        linarith only [this]
      have hseg := checkSeg_sound (bS := h0 + (l1 + (l2 + (l3 + l4)))) (bQ := h0 * h0 + (l1 * l1 + (l2 * l2 + (l3 * l3 + l4 * l4)))) (lv := l1) (segR := h0 + (h1 + (l2 + (l3 + l4)))) (T := T)
        ⟨hnL, hnR⟩ ⟨by omega, hs2⟩ (le_trans hQR hq) (okSQ_mono le_rfl (Nat.add_le_add_left hq curQ) hok)
      change (if _ then true else if checkSeg qlb curS curQ QRmin (h0 + (l1 + (l2 + (l3 + l4)))) (h0 * h0 + (l1 * l1 + (l2 * l2 + (l3 * l3 + l4 * l4)))) l1 _ _ (h0 + (h1 + (l2 + (l3 + l4)))) = true then true else _) = true
      split_ifs <;> rfl
    · by_cases hs3 : T ≤ h0 + (h1 + (h2 + (l3 + l4)))
      · have hq : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 ≤
            ((h0 * h0 + h1 * h1) + (l2 * l2 + (l3 * l3 + l4 * l4)) - l2 * l2) + (l2 + (T - (h0 + (h1 + (l2 + (l3 + l4)))))) ^ 2 := by
          have hsub : (h0 * h0 + h1 * h1) + (l2 * l2 + (l3 * l3 + l4 * l4)) - l2 * l2 = h0 ^ 2 + h1 ^ 2 + l3 ^ 2 + l4 ^ 2 := by rw [sq, sq, sq, sq]; omega
          rw [hsub]; zify [show h0 + (h1 + (l2 + (l3 + l4))) ≤ T by omega]
          have := box_seg_ineq_5 (x0 := (x0 : ℤ)) (x1 := (x1 : ℤ)) (x2 := (x2 : ℤ)) (x3 := (x3 : ℤ)) (x4 := (x4 : ℤ))
            (y0 := (h0 : ℤ)) (y1 := (h1 : ℤ)) (y2 := (l2 : ℤ) + ((T : ℤ) - ((h0 : ℤ) + ((h1 : ℤ) + ((l2 : ℤ) + ((l3 : ℤ) + (l4 : ℤ))))))) (y3 := (l3 : ℤ)) (y4 := (l4 : ℤ)) (c := (x2 : ℤ))
            (by dsimp [T]; omega) (hle_hi _ _ _ (by exact_mod_cast hb0.2) (by exact_mod_cast le_trans hord.2.2.1 hord.2.2.2))
            (hle_hi _ _ _ (by exact_mod_cast hb1.2) (by exact_mod_cast hord.2.2.1))
            (hself _ _) (hle_lo _ _ _ (by exact_mod_cast hb3.1) (by exact_mod_cast hord.2.1))
            (hle_lo _ _ _ (by exact_mod_cast hb4.1) (by exact_mod_cast le_trans hord.1 hord.2.1))
          linarith only [this]
        have hseg := checkSeg_sound (bS := h0 + (h1 + (l2 + (l3 + l4)))) (bQ := (h0 * h0 + h1 * h1) + (l2 * l2 + (l3 * l3 + l4 * l4))) (lv := l2) (segR := h0 + (h1 + (h2 + (l3 + l4)))) (T := T)
          ⟨hnL, hnR⟩ ⟨by omega, hs3⟩ (le_trans hQR hq) (okSQ_mono le_rfl (Nat.add_le_add_left hq curQ) hok)
        change (if _ then true else if _ then true else if checkSeg qlb curS curQ QRmin (h0 + (h1 + (l2 + (l3 + l4)))) ((h0 * h0 + h1 * h1) + (l2 * l2 + (l3 * l3 + l4 * l4))) l2 _ _ (h0 + (h1 + (h2 + (l3 + l4)))) = true then true else _) = true
        split_ifs <;> rfl
      · by_cases hs4 : T ≤ h0 + (h1 + (h2 + (h3 + l4)))
        · have hq : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 ≤
              (((h0 * h0 + h1 * h1) + h2 * h2) + (l3 * l3 + l4 * l4) - l3 * l3) + (l3 + (T - (h0 + (h1 + (h2 + (l3 + l4)))))) ^ 2 := by
            have hsub : ((h0 * h0 + h1 * h1) + h2 * h2) + (l3 * l3 + l4 * l4) - l3 * l3 = h0 ^ 2 + h1 ^ 2 + h2 ^ 2 + l4 ^ 2 := by rw [sq, sq, sq, sq]; omega
            rw [hsub]; zify [show h0 + (h1 + (h2 + (l3 + l4))) ≤ T by omega]
            have := box_seg_ineq_5 (x0 := (x0 : ℤ)) (x1 := (x1 : ℤ)) (x2 := (x2 : ℤ)) (x3 := (x3 : ℤ)) (x4 := (x4 : ℤ))
              (y0 := (h0 : ℤ)) (y1 := (h1 : ℤ)) (y2 := (h2 : ℤ)) (y3 := (l3 : ℤ) + ((T : ℤ) - ((h0 : ℤ) + ((h1 : ℤ) + ((h2 : ℤ) + ((l3 : ℤ) + (l4 : ℤ))))))) (y4 := (l4 : ℤ)) (c := (x3 : ℤ))
              (by dsimp [T]; omega) (hle_hi _ _ _ (by exact_mod_cast hb0.2) (by exact_mod_cast le_trans hord.2.1 (le_trans hord.2.2.1 hord.2.2.2)))
              (hle_hi _ _ _ (by exact_mod_cast hb1.2) (by exact_mod_cast le_trans hord.2.1 hord.2.2.1))
              (hle_hi _ _ _ (by exact_mod_cast hb2.2) (by exact_mod_cast hord.2.1))
              (hself _ _) (hle_lo _ _ _ (by exact_mod_cast hb4.1) (by exact_mod_cast hord.1))
            linarith only [this]
          have hseg := checkSeg_sound (bS := h0 + (h1 + (h2 + (l3 + l4)))) (bQ := ((h0 * h0 + h1 * h1) + h2 * h2) + (l3 * l3 + l4 * l4)) (lv := l3) (segR := h0 + (h1 + (h2 + (h3 + l4)))) (T := T)
            ⟨hnL, hnR⟩ ⟨by omega, hs4⟩ (le_trans hQR hq) (okSQ_mono le_rfl (Nat.add_le_add_left hq curQ) hok)
          change (if _ then true else if _ then true else if _ then true else if checkSeg qlb curS curQ QRmin (h0 + (h1 + (h2 + (l3 + l4)))) (((h0 * h0 + h1 * h1) + h2 * h2) + (l3 * l3 + l4 * l4)) l3 _ _ (h0 + (h1 + (h2 + (h3 + l4)))) = true then true else _) = true
          split_ifs <;> rfl
        · have hq : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 ≤
              (((h0 * h0 + h1 * h1) + h2 * h2) + (h3 * h3 + l4 * l4) - l4 * l4) + (l4 + (T - (h0 + (h1 + (h2 + (h3 + l4)))))) ^ 2 := by
            have hsub : ((h0 * h0 + h1 * h1) + h2 * h2) + (h3 * h3 + l4 * l4) - l4 * l4 = h0 ^ 2 + h1 ^ 2 + h2 ^ 2 + h3 ^ 2 := by rw [sq, sq, sq, sq]; omega
            rw [hsub]; zify [show h0 + (h1 + (h2 + (h3 + l4))) ≤ T by omega]
            have := box_seg_ineq_5 (x0 := (x0 : ℤ)) (x1 := (x1 : ℤ)) (x2 := (x2 : ℤ)) (x3 := (x3 : ℤ)) (x4 := (x4 : ℤ))
              (y0 := (h0 : ℤ)) (y1 := (h1 : ℤ)) (y2 := (h2 : ℤ)) (y3 := (h3 : ℤ)) (y4 := (l4 : ℤ) + ((T : ℤ) - ((h0 : ℤ) + ((h1 : ℤ) + ((h2 : ℤ) + ((h3 : ℤ) + (l4 : ℤ))))))) (c := (x4 : ℤ))
              (by dsimp [T]; omega) (hle_hi _ _ _ (by exact_mod_cast hb0.2) (by exact_mod_cast le_trans hord.1 (le_trans hord.2.1 (le_trans hord.2.2.1 hord.2.2.2))))
              (hle_hi _ _ _ (by exact_mod_cast hb1.2) (by exact_mod_cast le_trans hord.1 (le_trans hord.2.1 hord.2.2.1)))
              (hle_hi _ _ _ (by exact_mod_cast hb2.2) (by exact_mod_cast le_trans hord.1 hord.2.1))
              (hle_hi _ _ _ (by exact_mod_cast hb3.2) (by exact_mod_cast hord.1)) (hself _ _)
            linarith only [this]
          have hseg := checkSeg_sound (bS := h0 + (h1 + (h2 + (h3 + l4)))) (bQ := ((h0 * h0 + h1 * h1) + h2 * h2) + (h3 * h3 + l4 * l4)) (lv := l4) (segR := h0 + (h1 + (h2 + (h3 + h4)))) (T := T)
            ⟨hnL, hnR⟩ ⟨by omega, by dsimp [T]; omega⟩ (le_trans hQR hq) (okSQ_mono le_rfl (Nat.add_le_add_left hq curQ) hok)
          change (if _ then true else if _ then true else if _ then true else if _ then true else checkSeg qlb curS curQ QRmin (h0 + (h1 + (h2 + (h3 + l4)))) (((h0 * h0 + h1 * h1) + h2 * h2) + (h3 * h3 + l4 * l4)) l4 _ _ (h0 + (h1 + (h2 + (h3 + h4))))) = true
          split_ifs <;> first | rfl | exact hseg

-- 2D. Backward induction: filterPartners, checkX8, checkX7, checkX6, solveK6..solveA0_sound

private lemma filterPartners_spec {R6pos x6 hi7 : ℕ} :
    ∀ (xs : List ℕ), xs.Pairwise (· > ·) →
      (filterPartners R6pos x6 hi7 xs).Pairwise (· > ·) ∧
      ∀ y, y ∈ filterPartners R6pos x6 hi7 xs ↔
        y ∈ xs ∧ y ≤ hi7 ∧ testPos R6pos (x6 - y) = false ∧ testPos R6pos (x6 + y) = false := by
  intro xs
  induction xs with
  | nil => intro _; exact ⟨List.Pairwise.nil, fun y => by simp [filterPartners]⟩
  | cons z zs ih =>
    intro hpw
    rcases List.pairwise_cons.mp hpw with ⟨hz_gt, hzs⟩
    obtain ⟨hpw', hmem'⟩ := ih hzs
    unfold filterPartners
    by_cases hhi : hi7 < z
    · simp only [Nat.blt_eq.mpr hhi, ite_true]
      refine ⟨hpw', fun y => ?_⟩
      rw [hmem' y]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩; exact ⟨List.mem_cons_of_mem z h1, h2, h3, h4⟩
      · rintro ⟨h1, h2, h3, h4⟩
        rcases List.mem_cons.mp h1 with rfl | h1'
        · omega
        · exact ⟨h1', h2, h3, h4⟩
    · simp only [blt_false_of_le (by omega : z ≤ hi7), Bool.false_eq_true, ite_false]
      by_cases hbad : or (testPos R6pos (Nat.sub x6 z)) (testPos R6pos (Nat.add x6 z)) = true
      · simp only [hbad, ite_true]
        refine ⟨hpw', fun y => ?_⟩
        rw [hmem' y]
        constructor
        · rintro ⟨h1, h2, h3, h4⟩; exact ⟨List.mem_cons_of_mem z h1, h2, h3, h4⟩
        · rintro ⟨h1, h2, h3, h4⟩
          rcases List.mem_cons.mp h1 with rfl | h1'
          · simp only [Bool.or_eq_true] at hbad
            rcases hbad with hb | hb
            · change testPos R6pos (x6 - y) = true at hb; rw [h3] at hb; cases hb
            · change testPos R6pos (x6 + y) = true at hb; rw [h4] at hb; cases hb
          · exact ⟨h1', h2, h3, h4⟩
      · have hbad' : or (testPos R6pos (Nat.sub x6 z)) (testPos R6pos (Nat.add x6 z)) = false :=
          Bool.eq_false_iff.mpr hbad
        simp only [hbad', Bool.false_eq_true, ite_false]
        simp only [Bool.or_eq_false_iff] at hbad'
        refine ⟨List.pairwise_cons.mpr ⟨fun y hy => hz_gt y ((hmem' y).mp hy).1, hpw'⟩, fun y => ?_⟩
        simp only [List.mem_cons, hmem' y]
        constructor
        · rintro (rfl | ⟨h1, h2, h3, h4⟩)
          · exact ⟨Or.inl rfl, by omega, hbad'.1, hbad'.2⟩
          · exact ⟨Or.inr h1, h2, h3, h4⟩
        · rintro ⟨rfl | h1, h2, h3, h4⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨h1, h2, h3, h4⟩

private lemma pairwise_gt_top2 {l : List ℕ} (hpw : l.Pairwise (· > ·)) {x y : ℕ}
    (hx : x ∈ l) (hy : y ∈ l) (hyx : y < x) :
    ∃ t1 t2 tl, l = t1 :: t2 :: tl ∧ x ≤ t1 ∧ y ≤ t2 := by
  rcases l with _ | ⟨t1, rest⟩
  · simp at hx
  rcases List.pairwise_cons.mp hpw with ⟨ht1, hrest⟩
  have hx1 : x ≤ t1 := by
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact le_rfl
    · exact le_of_lt (ht1 x hx')
  have hy_rest : y ∈ rest := by
    rcases List.mem_cons.mp hy with rfl | hy'
    · omega
    · exact hy'
  rcases rest with _ | ⟨t2, tl⟩
  · simp at hy_rest
  rcases List.pairwise_cons.mp hrest with ⟨ht2, _⟩
  have hy2 : y ≤ t2 := by
    rcases List.mem_cons.mp hy_rest with rfl | hy'
    · exact le_rfl
    · exact le_of_lt (ht2 y hy')
  exact ⟨t1, t2, tl, rfl, hx1, hy2⟩

private lemma checkX8_false {qlb sum7 sq7 R6pos G x6 x7 hi8 Tlo7 Thi7 x8 : ℕ}
    (h8_hi : x8 ≤ hi8) (h78_lo : Tlo7 ≤ x7 + x8) (h78_hi : x7 + x8 ≤ Thi7)
    (hgap : G ≤ x7 - x8) (_hord : x8 < x7 ∧ x7 < x6)
    (hok : okSQ qlb (sum7 + (x7 + x8)) (sq7 + (x7 * x7 + x8 * x8)) = true)
    (hne6 : x6 ≠ x7 + x8)
    (ht1 : testPos R6pos (x7 - x8) = false) (ht2 : testPos R6pos (x7 + x8) = false)
    (ht3 : testPos R6pos (x6 + (x7 + x8)) = false)
    (ht4 : testPos R6pos (x6 + x7 - x8) = false)
    (ht5 : testPos R6pos (x6 + x8 - x7) = false)
    (ht6 : testPos R6pos (if x6 < x7 + x8 then x7 + x8 - x6 else x6 - (x7 + x8)) = false) :
    ∀ (xs : List ℕ), xs.Pairwise (· > ·) → x8 ∈ xs →
      checkX8 qlb sum7 sq7 R6pos G x6 x7 hi8 Tlo7 Thi7 xs = false := by
  intro xs
  induction xs with
  | nil => intro _ hm; simp at hm
  | cons z rest ih =>
    intro hpw hm
    rcases List.pairwise_cons.mp hpw with ⟨hz_gt, hrest⟩
    unfold checkX8
    rcases List.mem_cons.mp hm with rfl | hmem
    · dsimp only
      simp only [blt_false_of_le h8_hi, blt_false_of_le (show Tlo7 ≤ Nat.add x7 x8 from h78_lo),
        blt_false_of_le (show Nat.add x7 x8 ≤ Thi7 from h78_hi),
        blt_false_of_le (show G ≤ Nat.sub x7 x8 from hgap),
        Bool.false_eq_true, ite_false]
      have hok' : okSQ qlb (Nat.add sum7 (Nat.add x7 x8)) (Nat.add sq7 (Nat.add (Nat.mul x7 x7) (Nat.mul x8 x8))) = true := hok
      simp only [hok', ite_true]
      have hor : or (testPos R6pos (Nat.sub x7 x8)) (testPos R6pos (Nat.add x7 x8)) = false := by
        change or (testPos R6pos (x7 - x8)) (testPos R6pos (x7 + x8)) = false; simp [ht1, ht2]
      simp only [hor, Bool.false_eq_true, ite_false]
      simp [hne6, ht3, ht4, ht5, ht6]
    · have hrec := ih hrest hmem
      have hz_gt8 : x8 < z := hz_gt x8 hmem
      have hnot_lo : Nat.blt (Nat.add x7 z) Tlo7 = false :=
        blt_false_of_le (by change Tlo7 ≤ x7 + z; omega)
      dsimp only
      split_ifs with c1 c2
      · exact hrec
      · rw [hnot_lo] at c2; cases c2
      all_goals try exact hrec
      all_goals rfl

private lemma checkX7_false {qlb sum7 sq7 R6pos G x6 lo7 hi8 Tlo7 Thi7 x7 x8 : ℕ}
    (h7_lo : lo7 ≤ x7) (h8_hi : x8 ≤ hi8) (h78_lo : Tlo7 ≤ x7 + x8) (h78_hi : x7 + x8 ≤ Thi7)
    (hgap : G ≤ x7 - x8) (hord : x8 < x7 ∧ x7 < x6)
    (hok : okSQ qlb (sum7 + (x7 + x8)) (sq7 + (x7 * x7 + x8 * x8)) = true)
    (hne6 : x6 ≠ x7 + x8)
    (ht1 : testPos R6pos (x7 - x8) = false) (ht2 : testPos R6pos (x7 + x8) = false)
    (ht3 : testPos R6pos (x6 + (x7 + x8)) = false)
    (ht4 : testPos R6pos (x6 + x7 - x8) = false)
    (ht5 : testPos R6pos (x6 + x8 - x7) = false)
    (ht6 : testPos R6pos (if x6 < x7 + x8 then x7 + x8 - x6 else x6 - (x7 + x8)) = false) :
    ∀ (sub : List ℕ), sub.Pairwise (· > ·) → x7 ∈ sub → x8 ∈ sub →
      checkX7 qlb sum7 sq7 R6pos G x6 lo7 hi8 Tlo7 Thi7 sub = false := by
  intro sub
  induction sub with
  | nil => intro _ hm _; simp at hm
  | cons z rest ih =>
    intro hpw hm7 hm8
    rcases List.pairwise_cons.mp hpw with ⟨hz_gt, hrest⟩
    unfold checkX7
    have hz_ge7 : x7 ≤ z := by
      rcases List.mem_cons.mp hm7 with rfl | hm7'
      · exact le_rfl
      · exact le_of_lt (hz_gt x7 hm7')
    have hnot_lo : Nat.blt z lo7 = false := blt_false_of_le (le_trans h7_lo hz_ge7)
    simp only [hnot_lo, Bool.false_eq_true, ite_false]
    have hm8_rest : x8 ∈ rest := by
      rcases List.mem_cons.mp hm8 with rfl | hm8'
      · omega
      · exact hm8'
    rcases rest with _ | ⟨nxt, rest'⟩
    · simp at hm8_rest
    rcases List.pairwise_cons.mp hrest with ⟨hnxt_gt, _⟩
    have hnxt_ge8 : x8 ≤ nxt := by
      rcases List.mem_cons.mp hm8_rest with rfl | hm8''
      · exact le_rfl
      · exact le_of_lt (hnxt_gt x8 hm8'')
    have hnot_s : Nat.blt (Nat.add z nxt) Tlo7 = false :=
      blt_false_of_le (by change Tlo7 ≤ z + nxt; omega)
    simp only [hnot_s, Bool.false_eq_true, ite_false]
    rcases List.mem_cons.mp hm7 with rfl | hm7'
    · have h8f := checkX8_false h8_hi h78_lo h78_hi hgap hord hok hne6 ht1 ht2 ht3 ht4 ht5 ht6
        (nxt :: rest') hrest hm8_rest
      simp [h8f]
    · have hrec := ih hrest hm7' hm8_rest
      split_ifs <;> simp [hrec]

private lemma checkX6_false {qlb sum6 sq6 G lo6 hi6 lo7 hi7 lo8 hi8 Tlo6 Thi6 : ℕ}
    {a : Fin 9 → ℕ} (ha : StrictAnti a)
    (hinj : Function.Injective (fun U : Finset (Fin 9) => ∑ i ∈ U, a i))
    (hG : TailGap 6 G a)
    (hsum6 : sum6 = a 0 + a 1 + a 2 + a 3 + a 4 + a 5)
    (hsq6 : sq6 = a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2 + a 4 ^ 2 + a 5 ^ 2)
    (hS511 : 511 ≤ ∑ i : Fin 9, a i)
    (hok_full : okSQ qlb (∑ i : Fin 9, a i) (∑ i : Fin 9, a i ^ 2) = true)
    (hb6 : lo6 ≤ a 6 ∧ a 6 ≤ hi6) (hb7 : lo7 ≤ a 7 ∧ a 7 ≤ hi7) (hb8 : lo8 ≤ a 8 ∧ a 8 ≤ hi8)
    (hT6 : Tlo6 ≤ a 6 + a 7 + a 8 ∧ a 6 + a 7 + a 8 ≤ Thi6) :
    let R6pos := kronR 6 (by omega) a / 256 ^ (∑ i : Fin 6, a ⟨i.val, by omega⟩)
    ∀ (cand : List ℕ), cand.Pairwise (· > ·) → a 6 ∈ cand → a 7 ∈ cand → a 8 ∈ cand →
      checkX6 qlb sum6 sq6 R6pos G lo6 hi6 lo7 hi7 lo8 hi8 Tlo6 Thi6 cand = false := by
  intro R6pos cand
  have hS_split : ∑ i : Fin 9, a i = sum6 + (a 6 + a 7 + a 8) := by
    rw [hsum6]; simp [Fin.sum_univ_succ, add_assoc]
  have hQ_split : ∑ i : Fin 9, a i ^ 2 = sq6 + (a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2) := by
    rw [hsq6]; simp [Fin.sum_univ_succ, add_assoc]
  have h67 : a 7 + G ≤ a 6 := tailGap_diff_ge ha hG (by omega) (by decide)
  have h78 : a 8 + G ≤ a 7 := tailGap_diff_ge ha hG (by omega) (by decide)
  have hord76 : a 7 < a 6 := ha (by decide)
  have hord87 : a 8 < a 7 := ha (by decide)
  have hG7 : TailGap 7 G a := tailGap_mono_k (by omega) hG
  have h78_mom := tailGap_sum_and_sq (by omega) hG7
  have hT7_eq : (univ : Finset (Fin 9)).filter (fun i => 7 ≤ i.val) = {7, 8} := by decide
  have h78_sum : 3 * G ≤ a 7 + a 8 := by
    have h1 := h78_mom.1; rw [hT7_eq, sum_pair (by decide : (7 : Fin 9) ≠ 8)] at h1; norm_num at h1; exact h1
  have h78_sq : 5 * G ^ 2 ≤ a 7 ^ 2 + a 8 ^ 2 := by
    have h1 := h78_mom.2; rw [hT7_eq, sum_pair (by decide : (7 : Fin 9) ≠ 8)] at h1; norm_num at h1; omega
  have hok_u := okSQ_iff.mp hok_full
  induction cand with
  | nil => intro _ hm _ _; simp at hm
  | cons z rest ih =>
    intro hpw hm6 hm7 hm8
    rcases List.pairwise_cons.mp hpw with ⟨hz_gt, hrest⟩
    unfold checkX6; dsimp only
    have hz_ge6 : a 6 ≤ z := by
      rcases List.mem_cons.mp hm6 with rfl | hm6'
      · exact le_rfl
      · exact le_of_lt (hz_gt (a 6) hm6')
    have hnot_lo6 : Nat.blt z lo6 = false := blt_false_of_le (le_trans hb6.1 hz_ge6)
    simp only [hnot_lo6, Bool.false_eq_true, ite_false]
    let h7 := nmin hi7 (Nat.sub z G)
    let h8 := nmin hi8 (Nat.sub h7 G)
    have ha7_le : a 7 ≤ h7 := by dsimp [h7]; rw [nmin_eq]; exact le_min hb7.2 (by omega)
    have ha8_le : a 8 ≤ h8 := by dsimp [h8]; rw [nmin_eq]; exact le_min hb8.2 (by omega)
    have hmaxQ_ge : qlb ≤ Nat.add (Nat.add sq6 (Nat.mul z z)) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8)) := by
      have h1 : qlb ≤ sq6 + (a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2) := by rw [← hQ_split]; exact hok_u.1
      change qlb ≤ sq6 + z * z + (h7 * h7 + h8 * h8)
      have s6 := sq_le_mul_of_le hz_ge6; have s7 := sq_le_mul_of_le ha7_le; have s8 := sq_le_mul_of_le ha8_le
      omega
    rcases List.mem_cons.mp hm6 with rfl | hm6'
    · have hnot_lh : or (Nat.blt h7 lo7) (Nat.blt h8 lo8) = false := by
        simp [blt_false_of_le (le_trans hb7.1 ha7_le), blt_false_of_le (le_trans hb8.1 ha8_le)]
      dsimp only [h7, h8] at hnot_lh
      simp only [hnot_lh, Bool.false_eq_true, ite_false]
      let sum7 := Nat.add sum6 (a 6)
      let sq7 := Nat.add sq6 (Nat.mul (a 6) (a 6))
      let Tlo7 := nmax (Nat.sub Tlo6 (a 6)) (nmax (Nat.sub 511 sum7) (Nat.mul 3 G))
      let Thi7 := nmin (Nat.sub Thi6 (a 6)) (Nat.add h7 h8)
      have hT7_lo : Tlo7 ≤ a 7 + a 8 := by
        dsimp [Tlo7, sum7]; rw [nmax_eq, nmax_eq]
        exact max_le (by omega) (max_le (by omega) h78_sum)
      have hT7_hi : a 7 + a 8 ≤ Thi7 := by
        dsimp [Thi7]; rw [nmin_eq]; exact le_min (by omega) (by omega)
      have hnot_T7 : Nat.blt Thi7 Tlo7 = false := blt_false_of_le (le_trans hT7_lo hT7_hi)
      have hnot_mQ : Nat.blt (Nat.add sq7 (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8))) qlb = false :=
        blt_false_of_le hmaxQ_ge
      have hnot_9mQ : Nat.blt (Nat.mul 9 (Nat.add sq7 (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8))))
          (Nat.add 42863 (Nat.mul (Nat.add sum7 Tlo7) (Nat.add sum7 Tlo7))) = false := by
        apply blt_false_of_le
        have h9 := hok_u.2.1; rw [hS_split, hQ_split] at h9
        change 42863 + (sum6 + a 6 + Tlo7) * (sum6 + a 6 + Tlo7) ≤ 9 * (sq6 + a 6 * a 6 + (h7 * h7 + h8 * h8))
        have hs : (sum6 + a 6 + Tlo7) * (sum6 + a 6 + Tlo7) ≤ (sum6 + (a 6 + a 7 + a 8)) ^ 2 := by
          rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
        have s6 : a 6 ^ 2 = a 6 * a 6 := sq _
        have s7 := sq_le_mul_of_le ha7_le; have s8 := sq_le_mul_of_le ha8_le
        omega
      have hok7 : okSQ qlb (sum7 + (a 7 + a 8)) (sq7 + (a 7 ^ 2 + a 8 ^ 2)) = true := by
        rw [show sum7 + (a 7 + a 8) = ∑ i : Fin 9, a i by dsimp [sum7]; rw [hS_split]; ring,
            show sq7 + (a 7 ^ 2 + a 8 ^ 2) = ∑ i : Fin 9, a i ^ 2 by dsimp [sq7]; rw [hQ_split]; ring]
        exact hok_full
      have hbox2 : checkBox2 qlb sum7 sq7 Tlo7 Thi7 (Nat.mul 5 (Nat.mul G G)) lo7 h7 lo8 h8 = true :=
        checkBox2_sound ⟨hb7.1, ha7_le⟩ ⟨hb8.1, ha8_le⟩ (le_of_lt hord87) ⟨hT7_lo, hT7_hi⟩
          (by change 5 * (G * G) ≤ a 7 ^ 2 + a 8 ^ 2; rw [← sq]; exact h78_sq) hok7
      change (if Nat.blt Thi7 Tlo7 = true then _
        else if Nat.blt (Nat.add sq7 (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8))) qlb = true then true
        else if Nat.blt (Nat.mul 9 (Nat.add sq7 (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8))))
            (Nat.add 42863 (Nat.mul (Nat.add sum7 Tlo7) (Nat.add sum7 Tlo7))) = true then _
        else if not (checkBox2 qlb sum7 sq7 Tlo7 Thi7 (Nat.mul 5 (Nat.mul G G)) lo7 h7 lo8 h8) = true then _
        else _) = false
      simp only [hnot_T7, hnot_mQ, hnot_9mQ, hbox2, Bool.not_true, Bool.false_eq_true, ite_false]
      -- Now filterPartners R6pos (a 6) h7 rest contains both a 7 and a 8!
      have hm7_rest : a 7 ∈ rest := by
        rcases List.mem_cons.mp hm7 with h | h
        · omega
        · exact h
      have hm8_rest : a 8 ∈ rest := by
        rcases List.mem_cons.mp hm8 with h | h
        · omega
        · exact h
      have htp_sub67 : testPos R6pos (a 6 - a 7) = false := by
        have := tail_diff_not_testPos (k := 6) (by omega) hinj (U := {6}) (V := {7}) (by decide)
          (by intro i hi; simp at hi; subst hi; omega) (by intro i hi; simp at hi; subst hi; omega) (by simp; omega)
        simpa [R6pos] using this
      have htp_add67 : testPos R6pos (a 6 + a 7) = false := by
        have := tail_diff_not_testPos (k := 6) (by omega) hinj (U := {6, 7}) (V := ∅) (by decide)
          (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega) (by simp) (by simp)
        simpa [R6pos, sum_pair (by decide : (6 : Fin 9) ≠ 7)] using this
      have htp_sub68 : testPos R6pos (a 6 - a 8) = false := by
        have := tail_diff_not_testPos (k := 6) (by omega) hinj (U := {6}) (V := {8}) (by decide)
          (by intro i hi; simp at hi; subst hi; omega) (by intro i hi; simp at hi; subst hi; omega) (by simp; omega)
        simpa [R6pos] using this
      have htp_add68 : testPos R6pos (a 6 + a 8) = false := by
        have := tail_diff_not_testPos (k := 6) (by omega) hinj (U := {6, 8}) (V := ∅) (by decide)
          (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega) (by simp) (by simp)
        simpa [R6pos, sum_pair (by decide : (6 : Fin 9) ≠ 8)] using this
      obtain ⟨hsub_pw, hsub_mem⟩ := filterPartners_spec (R6pos := R6pos) (x6 := a 6) (hi7 := h7) rest hrest
      have h7_sub : a 7 ∈ filterPartners R6pos (a 6) h7 rest := (hsub_mem (a 7)).mpr ⟨hm7_rest, ha7_le, htp_sub67, htp_add67⟩
      have h8_sub : a 8 ∈ filterPartners R6pos (a 6) h7 rest := (hsub_mem (a 8)).mpr ⟨hm8_rest, le_trans (le_of_lt hord87) ha7_le, htp_sub68, htp_add68⟩
      obtain ⟨top7, top8, tl, hsub_eq, htop7, htop8⟩ := pairwise_gt_top2 hsub_pw h7_sub h8_sub hord87
      change (match filterPartners R6pos (a 6) h7 rest with
        | [] => _ | [_] => _
        | top7 :: top8 :: _ =>
          if or (Nat.blt top7 lo7) (or (Nat.blt (Nat.add top7 top8) Tlo7)
              (Nat.blt (Nat.add sq7 (Nat.add (Nat.mul top7 top7) (Nat.mul top8 top8))) qlb)) = true then _
          else if checkX7 qlb sum7 sq7 R6pos G (a 6) lo7 h8 Tlo7 Thi7 (filterPartners R6pos (a 6) h7 rest) = true then _
          else false) = false
      rw [hsub_eq]
      dsimp only
      have hnot_top : or (Nat.blt top7 lo7) (or (Nat.blt (Nat.add top7 top8) Tlo7)
          (Nat.blt (Nat.add sq7 (Nat.add (Nat.mul top7 top7) (Nat.mul top8 top8))) qlb)) = false := by
        have hq_top : qlb ≤ sq7 + (top7 * top7 + top8 * top8) := by
          have h1 := hok_u.1; rw [hQ_split] at h1; dsimp [sq7]
          have s6 : a 6 ^ 2 = a 6 * a 6 := sq _
          have s7 := sq_le_mul_of_le htop7; have s8 := sq_le_mul_of_le htop8
          change qlb ≤ sq6 + a 6 * a 6 + (top7 * top7 + top8 * top8); omega
        have htop_sum : Tlo7 ≤ top7 + top8 := by omega
        simp [blt_false_of_le (le_trans hb7.1 htop7),
              blt_false_of_le htop_sum,
              blt_false_of_le hq_top]
      simp only [hnot_top, Bool.false_eq_true, ite_false]
      have hne6 : a 6 ≠ a 7 + a 8 := by
        intro hEq
        have hS : ∑ i ∈ ({6} : Finset (Fin 9)), a i = ∑ i ∈ ({7, 8} : Finset (Fin 9)), a i := by
          rw [sum_singleton, sum_pair (by decide : (7 : Fin 9) ≠ 8)]; exact hEq
        have := hinj hS; exact absurd this (by decide)
      have ht1 : testPos R6pos (a 7 - a 8) = false := by
        have := tail_diff_not_testPos (k := 6) (by omega) hinj (U := {7}) (V := {8}) (by decide)
          (by intro i hi; simp at hi; subst hi; omega) (by intro i hi; simp at hi; subst hi; omega) (by simp; omega)
        simpa [R6pos] using this
      have ht2 : testPos R6pos (a 7 + a 8) = false := by
        have := tail_diff_not_testPos (k := 6) (by omega) hinj (U := {7, 8}) (V := ∅) (by decide)
          (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega) (by simp) (by simp)
        simpa [R6pos, sum_pair (by decide : (7 : Fin 9) ≠ 8)] using this
      have ht3 : testPos R6pos (a 6 + (a 7 + a 8)) = false := by
        have := tail_diff_not_testPos (k := 6) (by omega) hinj (U := {6, 7, 8}) (V := ∅) (by decide)
          (by intro i hi; simp at hi; rcases hi with rfl | rfl | rfl <;> omega) (by simp) (by simp)
        simpa [R6pos, add_assoc] using this
      have ht4 : testPos R6pos (a 6 + a 7 - a 8) = false := by
        have := tail_diff_not_testPos (k := 6) (by omega) hinj (U := {6, 7}) (V := {8}) (by decide)
          (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
          (by intro i hi; simp at hi; subst hi; omega) (by rw [sum_pair (by decide : (6 : Fin 9) ≠ 7), sum_singleton]; omega)
        simpa [R6pos, sum_pair (by decide : (6 : Fin 9) ≠ 7)] using this
      have ht5 : testPos R6pos (a 6 + a 8 - a 7) = false := by
        have := tail_diff_not_testPos (k := 6) (by omega) hinj (U := {6, 8}) (V := {7}) (by decide)
          (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
          (by intro i hi; simp at hi; subst hi; omega) (by rw [sum_pair (by decide : (6 : Fin 9) ≠ 8), sum_singleton]; omega)
        simpa [R6pos, sum_pair (by decide : (6 : Fin 9) ≠ 8)] using this
      have ht6 : testPos R6pos (if a 6 < a 7 + a 8 then a 7 + a 8 - a 6 else a 6 - (a 7 + a 8)) = false := by
        split_ifs with hlt
        · have := tail_diff_not_testPos (k := 6) (by omega) hinj (U := {7, 8}) (V := {6}) (by decide)
            (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
            (by intro i hi; simp at hi; subst hi; omega) (by rw [sum_pair (by decide : (7 : Fin 9) ≠ 8), sum_singleton]; omega)
          simpa [R6pos, sum_pair (by decide : (7 : Fin 9) ≠ 8)] using this
        · have := tail_diff_not_testPos (k := 6) (by omega) hinj (U := {6}) (V := {7, 8}) (by decide)
            (by intro i hi; simp at hi; subst hi; omega)
            (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega) (by rw [sum_pair (by decide : (7 : Fin 9) ≠ 8), sum_singleton]; omega)
          simpa [R6pos, sum_pair (by decide : (7 : Fin 9) ≠ 8)] using this
      have h7f := checkX7_false hb7.1 ha8_le hT7_lo hT7_hi (Nat.le_sub_of_add_le' h78) ⟨hord87, hord76⟩
        (by rw [← sq, ← sq]; exact hok7) hne6 ht1 ht2 ht3 ht4 ht5 ht6
        (top7 :: top8 :: tl) (hsub_eq ▸ hsub_pw) (hsub_eq ▸ h7_sub) (hsub_eq ▸ h8_sub)
      simp only [h7f, Bool.false_eq_true, ite_false]
    · have hm7_rest : a 7 ∈ rest := by
        rcases List.mem_cons.mp hm7 with h | h
        · omega
        · exact h
      have hm8_rest : a 8 ∈ rest := by
        rcases List.mem_cons.mp hm8 with h | h
        · omega
        · exact h
      have hrec := ih hrest hm6' hm7_rest hm8_rest
      have hnot_mQ : Nat.blt (Nat.add (Nat.add sq6 (Nat.mul z z)) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8))) qlb = false :=
        blt_false_of_le hmaxQ_ge
      dsimp only [h7, h8] at hnot_mQ
      split_ifs with c1 c2 c3
      · exact hrec
      · exact hrec
      · rw [hnot_mQ] at c3; cases c3
      · exact hrec
      · exact hrec
      all_goals
        cases hsub : filterPartners R6pos z (nmin hi7 (Nat.sub z G)) rest with
        | nil => exact hrec
        | cons t1 tl1 =>
          cases tl1 with
          | nil => exact hrec
          | cons t2 tl2 =>
            dsimp only
            split_ifs <;> first | exact hrec | rfl

private lemma solveK6_false {qlb sum6 sq6 Gin : ℕ} {a : Fin 9 → ℕ}
    (ha : StrictAnti a) (ha1 : ∀ i, 1 ≤ a i)
    (hinj : Function.Injective (fun U : Finset (Fin 9) => ∑ i ∈ U, a i))
    (hgap : ∀ i j : Fin 9, i ≤ j → j.val - i.val ≤ 6 → a j + gBound (j.val - i.val) ≤ a i)
    (hspan : (a 5 + a 6 + a 7 + a 8 + 125 ≤ a 0 + a 1 + a 2 + a 3) ∧
             (a 5 + a 6 + a 7 + a 8 + 251 ≤ a 0 + a 1 + a 2 + a 3 + a 4) ∧
             (a 6 + a 7 + a 8 + 83 ≤ a 0 + a 1 + a 2) ∧
             (a 6 + a 7 + a 8 + 335 ≤ a 0 + a 1 + a 2 + a 3 + a 4) ∧
             (a 6 + a 7 + a 8 + 419 ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5))
    (hS511 : 511 ≤ ∑ i : Fin 9, a i)
    (hok_full : okSQ qlb (∑ i : Fin 9, a i) (∑ i : Fin 9, a i ^ 2) = true)
    (hGin : TailGap 5 Gin a)
    (hsum6 : sum6 = a 0 + a 1 + a 2 + a 3 + a 4 + a 5)
    (hsq6 : sq6 = a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2 + a 4 ^ 2 + a 5 ^ 2) :
    solveK6 qlb (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) sum6 sq6 (kronR 6 (by omega) a) Gin = false := by
  unfold solveK6; dsimp only
  have hsum6_fin : ∑ i : Fin 6, a ⟨i.val, by omega⟩ = sum6 := by
    rw [hsum6]; simp [Fin.sum_univ_succ, add_assoc]
  let R6pos := Nat.div (kronR 6 (by omega) a) (Nat.pow 256 sum6)
  have hR6pos_eq : R6pos = kronR 6 (by omega) a / 256 ^ (∑ i : Fin 6, a ⟨i.val, by omega⟩) := by
    dsimp [R6pos]; rw [hsum6_fin]; rfl
  have hdig := kronR_digit (k := 6) (by omega) hinj
  have hmod64 : Nat.beq (Nat.mod R6pos 256) 64 = true := by
    have : R6pos % 256 = 64 := by rw [hR6pos_eq]; simpa using hdig.1
    change Nat.beq (R6pos % 256) 64 = true; rw [this]; rfl
  dsimp only [R6pos] at hmod64
  simp only [hmod64, Bool.not_true, Bool.false_eq_true, ite_false]
  let G := findG R6pos Gin
  have hG : TailGap 6 G a := by
    dsimp [G]; rw [hR6pos_eq]; exact findG_tailGap (k := 6) (by omega) hinj (tailGap_mono_k (by omega) hGin)
  have hG1 : 1 ≤ G := hG.1
  have hGin1 : 1 ≤ Gin := hGin.1
  have ha56 : a 6 + max 1 Gin ≤ a 5 := by
    have := tailGap_diff_ge ha hGin (by omega) (by decide : (5 : Fin 9) < 6); omega
  have ha67 : a 7 + max 1 G ≤ a 6 := by
    have := tailGap_diff_ge ha hG (by omega) (by decide : (6 : Fin 9) < 7); omega
  have ha78 : a 8 + max 1 G ≤ a 7 := by
    have := tailGap_diff_ge ha hG (by omega) (by decide : (7 : Fin 9) < 8); omega
  have h8_ge : max 1 G ≤ a 8 := by have := tailGap_elem_ge hG (i := 8) (by omega); have := ha1 8; omega
  have h6_ge4 : 4 * G ≤ a 6 := tailGap_a6_ge_4G (by omega) ha hG
  have htp6 : testPos R6pos (a 6) = false := by
    rw [hR6pos_eq]
    have := tail_diff_not_testPos (k := 6) (by omega) hinj (U := {6}) (V := ∅) (by decide)
      (by intro i hi; simp at hi; subst hi; omega) (by simp) (by simp)
    simpa using this
  have htp7 : testPos R6pos (a 7) = false := by
    rw [hR6pos_eq]
    have := tail_diff_not_testPos (k := 6) (by omega) hinj (U := {7}) (V := ∅) (by decide)
      (by intro i hi; simp at hi; subst hi; omega) (by simp) (by simp)
    simpa using this
  have htp8 : testPos R6pos (a 8) = false := by
    rw [hR6pos_eq]
    have := tail_diff_not_testPos (k := 6) (by omega) hinj (U := {8}) (V := ∅) (by decide)
      (by intro i hi; simp at hi; subst hi; omega) (by simp) (by simp)
    simpa using this
  -- Initial bounds on h6, h7, h8, l8, l7, l6
  have hg46 := hgap 4 6 (by decide) (by decide); have hg36 := hgap 3 6 (by decide) (by decide)
  have hg26 := hgap 2 6 (by decide) (by decide); have hg16 := hgap 1 6 (by decide) (by decide)
  have hg06 := hgap 0 6 (by decide) (by decide)
  have hg57 := hgap 5 7 (by decide) (by decide); have hg47 := hgap 4 7 (by decide) (by decide)
  have hg37 := hgap 3 7 (by decide) (by decide); have hg27 := hgap 2 7 (by decide) (by decide)
  have hg17 := hgap 1 7 (by decide) (by decide)
  have hg58 := hgap 5 8 (by decide) (by decide); have hg48 := hgap 4 8 (by decide) (by decide)
  have hg38 := hgap 3 8 (by decide) (by decide); have hg28 := hgap 2 8 (by decide) (by decide)
  norm_num [gBound] at hg46 hg36 hg26 hg16 hg06 hg57 hg47 hg37 hg27 hg17 hg58 hg48 hg38 hg28
  let h6_0 := nmin (Nat.sub (a 5) (nmax 1 Gin)) (nmin (Nat.sub (a 4) 2) (nmin (Nat.sub (a 3) 4) (nmin (Nat.sub (a 2) 7) (nmin (Nat.sub (a 1) 13) (Nat.sub (a 0) 22)))))
  let h7_0 := nmin (Nat.sub h6_0 (nmax 1 G)) (nmin (Nat.sub (a 5) 2) (nmin (Nat.sub (a 4) 4) (nmin (Nat.sub (a 3) 7) (nmin (Nat.sub (a 2) 13) (Nat.sub (a 1) 22)))))
  let h8_0 := nmin (Nat.sub h7_0 (nmax 1 G)) (nmin (Nat.sub (a 5) 4) (nmin (Nat.sub (a 4) 7) (nmin (Nat.sub (a 3) 13) (Nat.sub (a 2) 22))))
  let l8_0 := nmax 1 G
  let l7_0 := nmax (nmax 2 (Nat.mul 2 G)) (Nat.add l8_0 (nmax 1 G))
  let l6_0 := nmax (nmax 4 (Nat.mul 4 G)) (Nat.add l7_0 (nmax 1 G))
  have ha6_h0 : a 6 ≤ h6_0 := by dsimp [h6_0]; simp only [nmin_eq, nmax_eq]; omega
  have ha7_h0 : a 7 ≤ h7_0 := by dsimp [h7_0]; simp only [nmin_eq, nmax_eq]; omega
  have ha8_h0 : a 8 ≤ h8_0 := by dsimp [h8_0]; simp only [nmin_eq, nmax_eq]; omega
  have ha8_l0 : l8_0 ≤ a 8 := by dsimp [l8_0]; simp only [nmax_eq]; omega
  have ha7_l0 : l7_0 ≤ a 7 := by dsimp [l7_0]; simp only [nmax_eq]; omega
  have ha6_l0 : l6_0 ≤ a 6 := by dsimp [l6_0]; simp only [nmax_eq]; omega
  have hnot_b0 : or (Nat.blt h6_0 l6_0) (or (Nat.blt h7_0 l7_0) (Nat.blt h8_0 l8_0)) = false := by
    simp [blt_false_of_le (le_trans ha6_l0 ha6_h0), blt_false_of_le (le_trans ha7_l0 ha7_h0),
          blt_false_of_le (le_trans ha8_l0 ha8_h0)]
  change (if or (Nat.blt h6_0 l6_0) (or (Nat.blt h7_0 l7_0) (Nat.blt h8_0 l8_0)) = true then true else _) = false
  simp only [hnot_b0, Bool.false_eq_true, ite_false]
  let h6 := skipHi R6pos l6_0 h6_0
  let l8 := skipLo R6pos l8_0 h8_0
  let h7 := skipHi R6pos l7_0 (nmin h7_0 (Nat.sub h6 (nmax 1 G)))
  let l7 := skipLo R6pos (nmax l7_0 (Nat.add l8 (nmax 1 G))) h7
  let h8 := skipHi R6pos l8 (nmin h8_0 (Nat.sub h7 (nmax 1 G)))
  let l6 := skipLo R6pos (nmax l6_0 (Nat.add l7 (nmax 1 G))) h6
  have ha6_h : a 6 ≤ h6 := skipHi_ge (ha1 6) ha6_h0 htp6
  have ha8_l : l8 ≤ a 8 := skipLo_le ha8_l0 htp8
  have ha7_h : a 7 ≤ h7 := skipHi_ge (ha1 7) (by rw [nmin_eq, nmax_eq]; exact le_min ha7_h0 (by change a 7 ≤ h6 - max 1 G; omega)) htp7
  have ha7_l : l7 ≤ a 7 := skipLo_le (by rw [nmax_eq, nmax_eq]; exact max_le ha7_l0 (by change l8 + max 1 G ≤ a 7; omega)) htp7
  have ha8_h : a 8 ≤ h8 := skipHi_ge (ha1 8) (by rw [nmin_eq, nmax_eq]; exact le_min ha8_h0 (by change a 8 ≤ h7 - max 1 G; omega)) htp8
  have ha6_l : l6 ≤ a 6 := skipLo_le (by rw [nmax_eq, nmax_eq]; exact max_le ha6_l0 (by change l7 + max 1 G ≤ a 6; omega)) htp6
  have hnot_b1 : or (Nat.blt h6 l6) (or (Nat.blt h7 l7) (Nat.blt h8 l8)) = false := by
    simp [blt_false_of_le (le_trans ha6_l ha6_h), blt_false_of_le (le_trans ha7_l ha7_h),
          blt_false_of_le (le_trans ha8_l ha8_h)]
  change (if or (Nat.blt h6 l6) (or (Nat.blt h7 l7) (Nat.blt h8 l8)) = true then true else _) = false
  simp only [hnot_b1, Bool.false_eq_true, ite_false]
  -- Tlo, Thi, maxQ, checkBox3
  have hmom6 := tailGap_sum_and_sq (by omega) hG
  have hT6_eq : (univ : Finset (Fin 9)).filter (fun i => 6 ≤ i.val) = {6, 7, 8} := by decide
  have h678_sum : 7 * G ≤ a 6 + a 7 + a 8 := by
    have h1 := hmom6.1; rw [hT6_eq] at h1; simp at h1; omega
  have h678_sq : 21 * G ^ 2 ≤ a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2 := by
    have h1 := hmom6.2; rw [hT6_eq] at h1; simp at h1; omega
  have hS_split : ∑ i : Fin 9, a i = sum6 + (a 6 + a 7 + a 8) := by
    rw [hsum6]; simp [Fin.sum_univ_succ, add_assoc]
  have hQ_split : ∑ i : Fin 9, a i ^ 2 = sq6 + (a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2) := by
    rw [hsq6]; simp [Fin.sum_univ_succ, add_assoc]
  let s3 := Nat.add (a 0) (Nat.add (a 1) (a 2))
  let s4 := Nat.add s3 (a 3)
  let s5 := Nat.add s4 (a 4)
  let s6 := Nat.add s5 (a 5)
  let Tlo := nmax (Nat.sub 511 sum6) (Nat.mul 7 G)
  let Thi := nmin (Nat.add h6 (Nat.add h7 h8))
             (nmin (Nat.sub s3 83)
             (nmin (Nat.sub (Nat.sub s4 125) (a 5))
             (nmin (Nat.sub (Nat.sub s5 251) (a 5))
             (nmin (Nat.sub s5 335) (Nat.sub s6 419)))))
  have hTlo : Tlo ≤ a 6 + a 7 + a 8 := by dsimp [Tlo]; rw [nmax_eq]; omega
  have hThi : a 6 + a 7 + a 8 ≤ Thi := by dsimp [Thi, s6, s5, s4, s3]; simp only [nmin_eq]; omega
  have hok_u := okSQ_iff.mp hok_full
  have hmaxQ_ge : qlb ≤ Nat.add sq6 (Nat.add (Nat.mul h6 h6) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8))) := by
    have h1 := hok_u.1; rw [hQ_split] at h1; change qlb ≤ sq6 + (h6 * h6 + (h7 * h7 + h8 * h8))
    have s6 := sq_le_mul_of_le ha6_h; have s7 := sq_le_mul_of_le ha7_h; have s8 := sq_le_mul_of_le ha8_h; omega
  have h9mQ : Nat.add 42863 (Nat.mul (Nat.add sum6 Tlo) (Nat.add sum6 Tlo)) ≤
      Nat.mul 9 (Nat.add sq6 (Nat.add (Nat.mul h6 h6) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8)))) := by
    have h9 := hok_u.2.1; rw [hS_split, hQ_split] at h9
    change 42863 + (sum6 + Tlo) * (sum6 + Tlo) ≤ 9 * (sq6 + (h6 * h6 + (h7 * h7 + h8 * h8)))
    have hs : (sum6 + Tlo) * (sum6 + Tlo) ≤ (sum6 + (a 6 + a 7 + a 8)) ^ 2 := by
      rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
    have s6 := sq_le_mul_of_le ha6_h; have s7 := sq_le_mul_of_le ha7_h; have s8 := sq_le_mul_of_le ha8_h; omega
  have hok6 : okSQ qlb (sum6 + (a 6 + a 7 + a 8)) (sq6 + (a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2)) = true := by
    rw [← hS_split, ← hQ_split]; exact hok_full
  have hbox3 : checkBox3 qlb sum6 sq6 Tlo Thi (Nat.mul 21 (Nat.mul G G)) l6 h6 l7 h7 l8 h8 = true :=
    checkBox3_sound ⟨ha6_l, ha6_h⟩ ⟨ha7_l, ha7_h⟩ ⟨ha8_l, ha8_h⟩ ⟨le_of_lt (ha (by decide)), le_of_lt (ha (by decide))⟩
      ⟨hTlo, hThi⟩ (by change 21 * (G * G) ≤ _; rw [← sq]; exact h678_sq) hok6
  change (if Nat.blt Thi Tlo = true then true else
    if Nat.blt (Nat.add sq6 (Nat.add (Nat.mul h6 h6) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8)))) qlb = true then true else
    if Nat.blt (Nat.mul 9 (Nat.add sq6 (Nat.add (Nat.mul h6 h6) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8)))))
        (Nat.add 42863 (Nat.mul (Nat.add sum6 Tlo) (Nat.add sum6 Tlo))) = true then true else
    if not (checkBox3 qlb sum6 sq6 Tlo Thi (Nat.mul 21 (Nat.mul G G)) l6 h6 l7 h7 l8 h8) = true then true else
    checkX6 qlb sum6 sq6 R6pos G l6 h6 l7 h7 l8 h8 Tlo Thi (collectAliveDesc R6pos l8 h6)) = false
  simp only [blt_false_of_le (le_trans hTlo hThi), blt_false_of_le hmaxQ_ge, blt_false_of_le h9mQ,
    hbox3, Bool.not_true, Bool.false_eq_true, ite_false]
  obtain ⟨hc_pw, hc_mem⟩ := collectAliveDesc_spec R6pos l8 h6
  have h6_in : a 6 ∈ collectAliveDesc R6pos l8 h6 := (hc_mem (a 6)).mpr ⟨by omega, ha6_h, htp6⟩
  have h7_in : a 7 ∈ collectAliveDesc R6pos l8 h6 := (hc_mem (a 7)).mpr ⟨by omega, le_trans (le_of_lt (ha (by decide))) ha6_h, htp7⟩
  have h8_in : a 8 ∈ collectAliveDesc R6pos l8 h6 := (hc_mem (a 8)).mpr ⟨ha8_l, le_trans (le_of_lt (ha (by decide))) ha6_h, htp8⟩
  have hx6 := checkX6_false ha hinj hG hsum6 hsq6 hS511 hok_full ⟨ha6_l, ha6_h⟩ ⟨ha7_l, ha7_h⟩ ⟨ha8_l, ha8_h⟩
    ⟨hTlo, hThi⟩ (collectAliveDesc R6pos l8 h6) hc_pw h6_in h7_in h8_in
  rw [← hR6pos_eq] at hx6
  exact hx6

private lemma loopK5_false {qlb sum5 sq5 G l6 h6 l7 h7 l8 h8 : ℕ} {a : Fin 9 → ℕ}
    (ha : StrictAnti a) (ha1 : ∀ i, 1 ≤ a i)
    (hinj : Function.Injective (fun U : Finset (Fin 9) => ∑ i ∈ U, a i))
    (hgap : ∀ i j : Fin 9, i ≤ j → j.val - i.val ≤ 6 → a j + gBound (j.val - i.val) ≤ a i)
    (hspan : (a 5 + a 6 + a 7 + a 8 + 125 ≤ a 0 + a 1 + a 2 + a 3) ∧
             (a 5 + a 6 + a 7 + a 8 + 251 ≤ a 0 + a 1 + a 2 + a 3 + a 4) ∧
             (a 6 + a 7 + a 8 + 83 ≤ a 0 + a 1 + a 2) ∧
             (a 6 + a 7 + a 8 + 335 ≤ a 0 + a 1 + a 2 + a 3 + a 4) ∧
             (a 6 + a 7 + a 8 + 419 ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5))
    (hS511 : 511 ≤ ∑ i : Fin 9, a i)
    (hok_full : okSQ qlb (∑ i : Fin 9, a i) (∑ i : Fin 9, a i ^ 2) = true)
    (hG : TailGap 5 G a)
    (hsum5 : sum5 = a 0 + a 1 + a 2 + a 3 + a 4)
    (hsq5 : sq5 = a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2 + a 4 ^ 2)
    (hb6 : l6 ≤ a 6 ∧ a 6 ≤ h6) (hb7 : l7 ≤ a 7 ∧ a 7 ≤ h7) (hb8 : l8 ≤ a 8 ∧ a 8 ≤ h8) :
    let R5 := kronR 5 (by omega) a
    let R5pos := Nat.div R5 (Nat.pow 256 sum5)
    ∀ (fuel cur : ℕ), a 5 ≤ cur → cur < a 5 + fuel →
      loopK5 qlb (a 0) (a 1) (a 2) (a 3) (a 4) sum5 sq5 R5 R5pos G l6 h6 l7 h7 l8 h8 fuel cur = false := by
  intro R5 R5pos fuel
  have hsum5_fin : ∑ i : Fin 5, a ⟨i.val, by omega⟩ = sum5 := by
    rw [hsum5]; simp [Fin.sum_univ_succ, add_assoc]
  have hR5pos_eq : R5pos = kronR 5 (by omega) a / 256 ^ (∑ i : Fin 5, a ⟨i.val, by omega⟩) := by
    dsimp [R5pos, R5]; rw [hsum5_fin]; rfl
  have hG1 : 1 ≤ G := hG.1
  have ha56 : a 6 + max 1 G ≤ a 5 := by have := tailGap_diff_ge ha hG (by omega) (by decide : (5 : Fin 9) < 6); omega
  have ha67 : a 7 + max 1 G ≤ a 6 := by have := tailGap_diff_ge ha hG (by omega) (by decide : (6 : Fin 9) < 7); omega
  have ha78 : a 8 + max 1 G ≤ a 7 := by have := tailGap_diff_ge ha hG (by omega) (by decide : (7 : Fin 9) < 8); omega
  have hG6 : TailGap 6 G a := tailGap_mono_k (by omega) hG
  have hmom6 := tailGap_sum_and_sq (by omega) hG6
  have hT6_eq : (univ : Finset (Fin 9)).filter (fun i => 6 ≤ i.val) = {6, 7, 8} := by decide
  have h678_sum : 7 * G ≤ a 6 + a 7 + a 8 := by
    have h1 := hmom6.1; rw [hT6_eq] at h1; simp at h1; omega
  have h678_sq : 21 * G ^ 2 ≤ a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2 := by
    have h1 := hmom6.2; rw [hT6_eq] at h1; simp at h1; omega
  have hS_split : ∑ i : Fin 9, a i = sum5 + a 5 + (a 6 + a 7 + a 8) := by
    rw [hsum5]; simp [Fin.sum_univ_succ, add_assoc]
  have hQ_split : ∑ i : Fin 9, a i ^ 2 = sq5 + a 5 ^ 2 + (a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2) := by
    rw [hsq5]; simp [Fin.sum_univ_succ, add_assoc]
  have hok_u := okSQ_iff.mp hok_full
  induction fuel with
  | zero => intro cur h1 h2; omega
  | succ fuel ih =>
    intro cur hle hlt
    unfold loopK5; dsimp only
    let nh6 := nmin h6 (Nat.sub cur (nmax 1 G))
    let nh7 := nmin h7 (Nat.sub nh6 (nmax 1 G))
    let nh8 := nmin h8 (Nat.sub nh7 (nmax 1 G))
    have ha6_nh : a 6 ≤ nh6 := by dsimp [nh6]; rw [nmin_eq, nmax_eq]; omega
    have ha7_nh : a 7 ≤ nh7 := by dsimp [nh7]; rw [nmin_eq, nmax_eq]; omega
    have ha8_nh : a 8 ≤ nh8 := by dsimp [nh8]; rw [nmin_eq, nmax_eq]; omega
    have hnot_b : or (Nat.blt nh6 l6) (or (Nat.blt nh7 l7) (Nat.blt nh8 l8)) = false := by
      simp [blt_false_of_le (le_trans hb6.1 ha6_nh), blt_false_of_le (le_trans hb7.1 ha7_nh),
            blt_false_of_le (le_trans hb8.1 ha8_nh)]
    have hmaxQ_ge : qlb ≤ Nat.add (Nat.add sq5 (Nat.mul cur cur)) (Nat.add (Nat.mul nh6 nh6) (Nat.add (Nat.mul nh7 nh7) (Nat.mul nh8 nh8))) := by
      have h1 := hok_u.1; rw [hQ_split] at h1
      change qlb ≤ sq5 + cur * cur + (nh6 * nh6 + (nh7 * nh7 + nh8 * nh8))
      have s5 := sq_le_mul_of_le hle; have s6 := sq_le_mul_of_le ha6_nh; have s7 := sq_le_mul_of_le ha7_nh; have s8 := sq_le_mul_of_le ha8_nh; omega
    have hnot_mQ : Nat.blt (Nat.add (Nat.add sq5 (Nat.mul cur cur)) (Nat.add (Nat.mul nh6 nh6) (Nat.add (Nat.mul nh7 nh7) (Nat.mul nh8 nh8)))) qlb = false :=
      blt_false_of_le hmaxQ_ge
    dsimp only [nh6, nh7, nh8] at hnot_b hnot_mQ
    simp only [hnot_b, hnot_mQ, Bool.false_eq_true, ite_false]
    by_cases hEq : cur = a 5
    · subst hEq
      let sum6 := Nat.add sum5 (a 5)
      let sq6 := Nat.add sq5 (Nat.mul (a 5) (a 5))
      let s3 := Nat.add (a 0) (Nat.add (a 1) (a 2))
      let s4 := Nat.add s3 (a 3)
      let s5 := Nat.add s4 (a 4)
      let Thi6 := nmin (Nat.add nh6 (Nat.add nh7 nh8))
                  (nmin (Nat.sub s3 83)
                  (nmin (Nat.sub (Nat.sub s4 125) (a 5))
                  (nmin (Nat.sub (Nat.sub s5 251) (a 5))
                  (nmin (Nat.sub s5 335) (Nat.sub (Nat.add s5 (a 5)) 419)))))
      let Tlo6 := nmax (Nat.sub 511 sum6) (Nat.mul 7 G)
      have hTlo : Tlo6 ≤ a 6 + a 7 + a 8 := by dsimp [Tlo6, sum6]; rw [nmax_eq]; omega
      have hThi : a 6 + a 7 + a 8 ≤ Thi6 := by dsimp [Thi6, s5, s4, s3]; simp only [nmin_eq]; omega
      have hok_cur : okSQ qlb (Nat.add sum6 Tlo6) (Nat.add sq6 (Nat.add (Nat.mul nh6 nh6) (Nat.add (Nat.mul nh7 nh7) (Nat.mul nh8 nh8)))) = true :=
        okSQ_mono (by rw [hS_split]; dsimp [sum6]; omega)
          (by rw [hQ_split]; dsimp [sq6]; change sq5 + a 5 ^ 2 + (a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2) ≤ sq5 + a 5 * a 5 + (nh6 * nh6 + (nh7 * nh7 + nh8 * nh8))
              have s5 : a 5 ^ 2 = a 5 * a 5 := sq _; have s6 := sq_le_mul_of_le ha6_nh; have s7 := sq_le_mul_of_le ha7_nh; have s8 := sq_le_mul_of_le ha8_nh; omega)
          hok_full
      have hok6 : okSQ qlb (sum6 + (a 6 + a 7 + a 8)) (sq6 + (a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2)) = true := by
        rw [show sum6 + (a 6 + a 7 + a 8) = ∑ i : Fin 9, a i by dsimp [sum6]; exact hS_split.symm,
            show sq6 + (a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2) = ∑ i : Fin 9, a i ^ 2 by dsimp [sq6]; rw [hQ_split]; ring]
        exact hok_full
      have hbox3 : checkBox3 qlb sum6 sq6 Tlo6 Thi6 (Nat.mul 21 (Nat.mul G G)) l6 nh6 l7 nh7 l8 nh8 = true :=
        checkBox3_sound ⟨hb6.1, ha6_nh⟩ ⟨hb7.1, ha7_nh⟩ ⟨hb8.1, ha8_nh⟩ ⟨le_of_lt (ha (by decide)), le_of_lt (ha (by decide))⟩
          ⟨hTlo, hThi⟩ (by change 21 * (G * G) ≤ _; rw [← sq]; exact h678_sq) hok6
      have htp5 : testPos R5pos (a 5) = false := by
        rw [hR5pos_eq]
        have := tail_diff_not_testPos (k := 5) (by omega) hinj (U := {5}) (V := ∅) (by decide)
          (by intro i hi; simp at hi; subst hi; omega) (by simp) (by simp)
        simpa using this
      have hk6 := solveK6_false ha ha1 hinj hgap hspan hS511 hok_full hG
        (show sum6 = a 0 + a 1 + a 2 + a 3 + a 4 + a 5 by dsimp [sum6]; omega)
        (show sq6 = a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2 + a 4 ^ 2 + a 5 ^ 2 by dsimp [sq6]; rw [hsq5]; ring)
      have hR6 : updR R5 (a 5) = kronR 6 (by omega) a := (kronR_succ (k := 5) (by omega) a).symm
      rw [← hR6] at hk6
      change (if (if Nat.blt Thi6 Tlo6 = true then true
        else if not (okSQ qlb (Nat.add sum6 Tlo6) (Nat.add sq6 (Nat.add (Nat.mul nh6 nh6) (Nat.add (Nat.mul nh7 nh7) (Nat.mul nh8 nh8))))) = true then true
        else if not (checkBox3 qlb sum6 sq6 Tlo6 Thi6 (Nat.mul 21 (Nat.mul G G)) l6 nh6 l7 nh7 l8 nh8) = true then true
        else if testPos R5pos (a 5) = true then true
        else solveK6 qlb (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) sum6 sq6 (updR R5 (a 5)) G) = true then _ else false) = false
      simp only [blt_false_of_le (le_trans hTlo hThi), hok_cur, hbox3, htp5, Bool.not_true, Bool.false_eq_true, ite_false, hk6]
    · have hrec := ih (Nat.sub cur 1) (by change a 5 ≤ cur - 1; omega) (by change cur - 1 < a 5 + fuel; omega)
      split_ifs <;> try exact hrec
      all_goals rfl

private lemma solveK5_false {qlb sum5 sq5 Gin : ℕ} {a : Fin 9 → ℕ}
    (ha : StrictAnti a) (ha1 : ∀ i, 1 ≤ a i)
    (hinj : Function.Injective (fun U : Finset (Fin 9) => ∑ i ∈ U, a i))
    (hgap : ∀ i j : Fin 9, i ≤ j → j.val - i.val ≤ 6 → a j + gBound (j.val - i.val) ≤ a i)
    (hspan : (a 5 + a 6 + a 7 + a 8 + 125 ≤ a 0 + a 1 + a 2 + a 3) ∧
             (a 5 + a 6 + a 7 + a 8 + 251 ≤ a 0 + a 1 + a 2 + a 3 + a 4) ∧
             (a 6 + a 7 + a 8 + 83 ≤ a 0 + a 1 + a 2) ∧
             (a 6 + a 7 + a 8 + 335 ≤ a 0 + a 1 + a 2 + a 3 + a 4) ∧
             (a 6 + a 7 + a 8 + 419 ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5))
    (hS511 : 511 ≤ ∑ i : Fin 9, a i)
    (hok_full : okSQ qlb (∑ i : Fin 9, a i) (∑ i : Fin 9, a i ^ 2) = true)
    (hGin : TailGap 4 Gin a)
    (hsum5 : sum5 = a 0 + a 1 + a 2 + a 3 + a 4)
    (hsq5 : sq5 = a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2 + a 4 ^ 2) :
    solveK5 qlb (a 0) (a 1) (a 2) (a 3) (a 4) sum5 sq5 (kronR 5 (by omega) a) Gin = false := by
  unfold solveK5; dsimp only
  have hsum5_fin : ∑ i : Fin 5, a ⟨i.val, by omega⟩ = sum5 := by
    rw [hsum5]; simp [Fin.sum_univ_succ, add_assoc]
  let R5pos := Nat.div (kronR 5 (by omega) a) (Nat.pow 256 sum5)
  have hR5pos_eq : R5pos = kronR 5 (by omega) a / 256 ^ (∑ i : Fin 5, a ⟨i.val, by omega⟩) := by
    dsimp [R5pos]; rw [hsum5_fin]; rfl
  have hdig := kronR_digit (k := 5) (by omega) hinj
  have hmod32 : Nat.beq (Nat.mod R5pos 256) 32 = true := by
    have : R5pos % 256 = 32 := by rw [hR5pos_eq]; simpa using hdig.1
    change Nat.beq (R5pos % 256) 32 = true; rw [this]; rfl
  dsimp only [R5pos] at hmod32
  simp only [hmod32, Bool.not_true, Bool.false_eq_true, ite_false]
  let G := findG R5pos Gin
  have hG : TailGap 5 G a := by
    dsimp [G]; rw [hR5pos_eq]; exact findG_tailGap (k := 5) (by omega) hinj (tailGap_mono_k (by omega) hGin)
  have hG1 : 1 ≤ G := hG.1; have hGin1 : 1 ≤ Gin := hGin.1
  have ha45 : a 5 + max 1 Gin ≤ a 4 := by have := tailGap_diff_ge ha hGin (by omega) (by decide : (4 : Fin 9) < 5); omega
  have ha56 : a 6 + max 1 G ≤ a 5 := by have := tailGap_diff_ge ha hG (by omega) (by decide : (5 : Fin 9) < 6); omega
  have ha67 : a 7 + max 1 G ≤ a 6 := by have := tailGap_diff_ge ha hG (by omega) (by decide : (6 : Fin 9) < 7); omega
  have ha78 : a 8 + max 1 G ≤ a 7 := by have := tailGap_diff_ge ha hG (by omega) (by decide : (7 : Fin 9) < 8); omega
  have h8_ge : max 1 G ≤ a 8 := by have := tailGap_elem_ge hG (i := 8) (by omega); have := ha1 8; omega
  have h6_ge4 : 4 * G ≤ a 6 := tailGap_a6_ge_4G (by omega) ha hG
  have hg35 := hgap 3 5 (by decide) (by decide); have hg25 := hgap 2 5 (by decide) (by decide)
  have hg15 := hgap 1 5 (by decide) (by decide); have hg05 := hgap 0 5 (by decide) (by decide)
  have hg46 := hgap 4 6 (by decide) (by decide); have hg36 := hgap 3 6 (by decide) (by decide)
  have hg26 := hgap 2 6 (by decide) (by decide); have hg16 := hgap 1 6 (by decide) (by decide)
  have hg06 := hgap 0 6 (by decide) (by decide)
  have hg47 := hgap 4 7 (by decide) (by decide); have hg37 := hgap 3 7 (by decide) (by decide)
  have hg27 := hgap 2 7 (by decide) (by decide); have hg17 := hgap 1 7 (by decide) (by decide)
  have hg48 := hgap 4 8 (by decide) (by decide); have hg38 := hgap 3 8 (by decide) (by decide)
  have hg28 := hgap 2 8 (by decide) (by decide); have hg58 := hgap 5 8 (by decide) (by decide)
  norm_num [gBound] at hg35 hg25 hg15 hg05 hg46 hg36 hg26 hg16 hg06 hg47 hg37 hg27 hg17 hg48 hg38 hg28 hg58
  have htp5 : testPos R5pos (a 5) = false := by
    rw [hR5pos_eq]; simpa using tail_diff_not_testPos (k := 5) (by omega) hinj (U := {5}) (V := ∅) (by decide)
      (by intro i hi; simp at hi; subst hi; omega) (by simp) (by simp)
  have htp6 : testPos R5pos (a 6) = false := by
    rw [hR5pos_eq]; simpa using tail_diff_not_testPos (k := 5) (by omega) hinj (U := {6}) (V := ∅) (by decide)
      (by intro i hi; simp at hi; subst hi; omega) (by simp) (by simp)
  have htp7 : testPos R5pos (a 7) = false := by
    rw [hR5pos_eq]; simpa using tail_diff_not_testPos (k := 5) (by omega) hinj (U := {7}) (V := ∅) (by decide)
      (by intro i hi; simp at hi; subst hi; omega) (by simp) (by simp)
  have htp8 : testPos R5pos (a 8) = false := by
    rw [hR5pos_eq]; simpa using tail_diff_not_testPos (k := 5) (by omega) hinj (U := {8}) (V := ∅) (by decide)
      (by intro i hi; simp at hi; subst hi; omega) (by simp) (by simp)
  let h5_0 := nmin (Nat.sub (a 4) (nmax 1 Gin)) (nmin (Nat.sub (a 3) 2) (nmin (Nat.sub (a 2) 4) (nmin (Nat.sub (a 1) 7) (Nat.sub (a 0) 13))))
  let h6_0 := nmin (Nat.sub h5_0 (nmax 1 G)) (nmin (Nat.sub (a 4) 2) (nmin (Nat.sub (a 3) 4) (nmin (Nat.sub (a 2) 7) (nmin (Nat.sub (a 1) 13) (Nat.sub (a 0) 22)))))
  let h7_0 := nmin (Nat.sub h6_0 (nmax 1 G)) (nmin (Nat.sub (a 4) 4) (nmin (Nat.sub (a 3) 7) (nmin (Nat.sub (a 2) 13) (Nat.sub (a 1) 22))))
  let h8_0 := nmin (Nat.sub h7_0 (nmax 1 G)) (nmin (Nat.sub (a 4) 7) (nmin (Nat.sub (a 3) 13) (Nat.sub (a 2) 22)))
  let l8_0 := nmax 1 G
  let l7_0 := nmax (nmax 2 (Nat.mul 2 G)) (Nat.add l8_0 (nmax 1 G))
  let l6_0 := nmax (nmax 4 (Nat.mul 4 G)) (Nat.add l7_0 (nmax 1 G))
  let l5_0 := nmax 5 (Nat.add l6_0 (nmax 1 G))
  have ha5_h0 : a 5 ≤ h5_0 := by dsimp [h5_0]; simp only [nmin_eq, nmax_eq]; omega
  have ha6_h0 : a 6 ≤ h6_0 := by dsimp [h6_0]; simp only [nmin_eq, nmax_eq]; omega
  have ha7_h0 : a 7 ≤ h7_0 := by dsimp [h7_0]; simp only [nmin_eq, nmax_eq]; omega
  have ha8_h0 : a 8 ≤ h8_0 := by dsimp [h8_0]; simp only [nmin_eq, nmax_eq]; omega
  have ha8_l0 : l8_0 ≤ a 8 := by dsimp [l8_0]; simp only [nmax_eq]; omega
  have ha7_l0 : l7_0 ≤ a 7 := by dsimp [l7_0]; simp only [nmax_eq]; omega
  have ha6_l0 : l6_0 ≤ a 6 := by dsimp [l6_0]; simp only [nmax_eq]; omega
  have ha5_l0 : l5_0 ≤ a 5 := by dsimp [l5_0]; simp only [nmax_eq]; omega
  have hnot_b0 : or (Nat.blt h5_0 l5_0) (or (Nat.blt h6_0 l6_0) (or (Nat.blt h7_0 l7_0) (Nat.blt h8_0 l8_0))) = false := by
    simp [blt_false_of_le (le_trans ha5_l0 ha5_h0), blt_false_of_le (le_trans ha6_l0 ha6_h0),
          blt_false_of_le (le_trans ha7_l0 ha7_h0), blt_false_of_le (le_trans ha8_l0 ha8_h0)]
  change (if or (Nat.blt h5_0 l5_0) (or (Nat.blt h6_0 l6_0) (or (Nat.blt h7_0 l7_0) (Nat.blt h8_0 l8_0))) = true then true else _) = false
  simp only [hnot_b0, Bool.false_eq_true, ite_false]
  let h5 := skipHi R5pos l5_0 h5_0
  let l8 := skipLo R5pos l8_0 h8_0
  let h6 := skipHi R5pos l6_0 (nmin h6_0 (Nat.sub h5 (nmax 1 G)))
  let h7 := skipHi R5pos l7_0 (nmin h7_0 (Nat.sub h6 (nmax 1 G)))
  let h8 := skipHi R5pos l8 (nmin h8_0 (Nat.sub h7 (nmax 1 G)))
  let l7 := skipLo R5pos (nmax l7_0 (Nat.add l8 (nmax 1 G))) h7
  let l6 := skipLo R5pos (nmax l6_0 (Nat.add l7 (nmax 1 G))) h6
  let l5 := skipLo R5pos (nmax l5_0 (Nat.add l6 (nmax 1 G))) h5
  have ha5_h : a 5 ≤ h5 := skipHi_ge (ha1 5) ha5_h0 htp5
  have ha8_l : l8 ≤ a 8 := skipLo_le ha8_l0 htp8
  have ha6_h : a 6 ≤ h6 := skipHi_ge (ha1 6) (by rw [nmin_eq, nmax_eq]; exact le_min ha6_h0 (by change a 6 ≤ h5 - max 1 G; omega)) htp6
  have ha7_h : a 7 ≤ h7 := skipHi_ge (ha1 7) (by rw [nmin_eq, nmax_eq]; exact le_min ha7_h0 (by change a 7 ≤ h6 - max 1 G; omega)) htp7
  have ha8_h : a 8 ≤ h8 := skipHi_ge (ha1 8) (by rw [nmin_eq, nmax_eq]; exact le_min ha8_h0 (by change a 8 ≤ h7 - max 1 G; omega)) htp8
  have ha7_l : l7 ≤ a 7 := skipLo_le (by rw [nmax_eq, nmax_eq]; exact max_le ha7_l0 (by change l8 + max 1 G ≤ a 7; omega)) htp7
  have ha6_l : l6 ≤ a 6 := skipLo_le (by rw [nmax_eq, nmax_eq]; exact max_le ha6_l0 (by change l7 + max 1 G ≤ a 6; omega)) htp6
  have ha5_l : l5 ≤ a 5 := skipLo_le (by rw [nmax_eq, nmax_eq]; exact max_le ha5_l0 (by change l6 + max 1 G ≤ a 5; omega)) htp5
  have hnot_b1 : or (Nat.blt h5 l5) (or (Nat.blt h6 l6) (or (Nat.blt h7 l7) (Nat.blt h8 l8))) = false := by
    simp [blt_false_of_le (le_trans ha5_l ha5_h), blt_false_of_le (le_trans ha6_l ha6_h),
          blt_false_of_le (le_trans ha7_l ha7_h), blt_false_of_le (le_trans ha8_l ha8_h)]
  change (if or (Nat.blt h5 l5) (or (Nat.blt h6 l6) (or (Nat.blt h7 l7) (Nat.blt h8 l8))) = true then true else _) = false
  simp only [hnot_b1, Bool.false_eq_true, ite_false]
  have hmom5 := tailGap_sum_and_sq (by omega) hG
  have hT5_eq : (univ : Finset (Fin 9)).filter (fun i => 5 ≤ i.val) = {5, 6, 7, 8} := by decide
  have h58_sum : 15 * G ≤ a 5 + a 6 + a 7 + a 8 := by
    have h1 := hmom5.1; rw [hT5_eq] at h1; simp at h1; omega
  have h58_sq : 85 * G ^ 2 ≤ a 5 ^ 2 + a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2 := by
    have h1 := hmom5.2; rw [hT5_eq] at h1; simp at h1; omega
  have hS_split : ∑ i : Fin 9, a i = sum5 + (a 5 + a 6 + a 7 + a 8) := by
    rw [hsum5]; simp [Fin.sum_univ_succ, add_assoc]
  have hQ_split : ∑ i : Fin 9, a i ^ 2 = sq5 + (a 5 ^ 2 + a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2) := by
    rw [hsq5]; simp [Fin.sum_univ_succ, add_assoc]
  let s3 := Nat.add (a 0) (Nat.add (a 1) (a 2))
  let s4 := Nat.add s3 (a 3)
  let s5 := Nat.add s4 (a 4)
  let Tlo := nmax (Nat.sub 511 sum5) (Nat.mul 15 G)
  let Thi := nmin (Nat.add h5 (Nat.add h6 (Nat.add h7 h8)))
             (nmin (Nat.sub s4 125)
             (nmin (Nat.sub s5 251)
             (nmin (Nat.sub (Nat.add s3 h5) 83)
             (nmin (Nat.sub (Nat.add s5 h5) 335) (Nat.sub (Nat.add s5 (Nat.mul 2 h5)) 419)))))
  have hTlo : Tlo ≤ a 5 + a 6 + a 7 + a 8 := by dsimp [Tlo]; rw [nmax_eq]; omega
  have hThi : a 5 + a 6 + a 7 + a 8 ≤ Thi := by dsimp [Thi, s5, s4, s3]; simp only [nmin_eq]; omega
  have hok_u := okSQ_iff.mp hok_full
  have hmaxQ_ge : qlb ≤ Nat.add sq5 (Nat.add (Nat.mul h5 h5) (Nat.add (Nat.mul h6 h6) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8)))) := by
    have h1 := hok_u.1; rw [hQ_split] at h1; change qlb ≤ sq5 + (h5 * h5 + (h6 * h6 + (h7 * h7 + h8 * h8)))
    have s5 := sq_le_mul_of_le ha5_h; have s6 := sq_le_mul_of_le ha6_h; have s7 := sq_le_mul_of_le ha7_h; have s8 := sq_le_mul_of_le ha8_h; omega
  have h9mQ : Nat.add 42863 (Nat.mul (Nat.add sum5 Tlo) (Nat.add sum5 Tlo)) ≤
      Nat.mul 9 (Nat.add sq5 (Nat.add (Nat.mul h5 h5) (Nat.add (Nat.mul h6 h6) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8))))) := by
    have h9 := hok_u.2.1; rw [hS_split, hQ_split] at h9
    change 42863 + (sum5 + Tlo) * (sum5 + Tlo) ≤ 9 * (sq5 + (h5 * h5 + (h6 * h6 + (h7 * h7 + h8 * h8))))
    have hs : (sum5 + Tlo) * (sum5 + Tlo) ≤ (sum5 + (a 5 + a 6 + a 7 + a 8)) ^ 2 := by
      rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
    have s5 := sq_le_mul_of_le ha5_h; have s6 := sq_le_mul_of_le ha6_h; have s7 := sq_le_mul_of_le ha7_h; have s8 := sq_le_mul_of_le ha8_h; omega
  have hok5 : okSQ qlb (sum5 + (a 5 + a 6 + a 7 + a 8)) (sq5 + (a 5 ^ 2 + a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2)) = true := by
    rw [← hS_split, ← hQ_split]; exact hok_full
  have hbox4 : checkBox4 qlb sum5 sq5 Tlo Thi (Nat.mul 85 (Nat.mul G G)) l5 h5 l6 h6 l7 h7 l8 h8 = true :=
    checkBox4_sound ⟨ha5_l, ha5_h⟩ ⟨ha6_l, ha6_h⟩ ⟨ha7_l, ha7_h⟩ ⟨ha8_l, ha8_h⟩
      ⟨le_of_lt (ha (by decide)), le_of_lt (ha (by decide)), le_of_lt (ha (by decide))⟩
      ⟨hTlo, hThi⟩ (by change 85 * (G * G) ≤ _; rw [← sq]; exact h58_sq) hok5
  change (if Nat.blt Thi Tlo = true then true else
    if Nat.blt (Nat.add sq5 (Nat.add (Nat.mul h5 h5) (Nat.add (Nat.mul h6 h6) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8))))) qlb = true then true else
    if Nat.blt (Nat.mul 9 (Nat.add sq5 (Nat.add (Nat.mul h5 h5) (Nat.add (Nat.mul h6 h6) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8))))))
        (Nat.add 42863 (Nat.mul (Nat.add sum5 Tlo) (Nat.add sum5 Tlo))) = true then true else
    if not (checkBox4 qlb sum5 sq5 Tlo Thi (Nat.mul 85 (Nat.mul G G)) l5 h5 l6 h6 l7 h7 l8 h8) = true then true else
    loopK5 qlb (a 0) (a 1) (a 2) (a 3) (a 4) sum5 sq5 (kronR 5 (by omega) a) R5pos G l6 h6 l7 h7 l8 h8 (Nat.add (Nat.sub h5 l5) 1) h5) = false
  simp only [blt_false_of_le (le_trans hTlo hThi), blt_false_of_le hmaxQ_ge, blt_false_of_le h9mQ,
    hbox4, Bool.not_true, Bool.false_eq_true, ite_false]
  exact loopK5_false ha ha1 hinj hgap hspan hS511 hok_full hG hsum5 hsq5 ⟨ha6_l, ha6_h⟩ ⟨ha7_l, ha7_h⟩ ⟨ha8_l, ha8_h⟩
    (Nat.add (Nat.sub h5 l5) 1) h5 ha5_h (by change h5 < a 5 + (h5 - l5 + 1); omega)

private lemma loopK4_false {qlb sum4 sq4 G l5 h5 l6 h6 l7 h7 l8 h8 : ℕ} {a : Fin 9 → ℕ}
    (ha : StrictAnti a) (ha1 : ∀ i, 1 ≤ a i)
    (hinj : Function.Injective (fun U : Finset (Fin 9) => ∑ i ∈ U, a i))
    (hgap : ∀ i j : Fin 9, i ≤ j → j.val - i.val ≤ 6 → a j + gBound (j.val - i.val) ≤ a i)
    (hspan : (a 5 + a 6 + a 7 + a 8 + 125 ≤ a 0 + a 1 + a 2 + a 3) ∧
             (a 5 + a 6 + a 7 + a 8 + 251 ≤ a 0 + a 1 + a 2 + a 3 + a 4) ∧
             (a 6 + a 7 + a 8 + 83 ≤ a 0 + a 1 + a 2) ∧
             (a 6 + a 7 + a 8 + 335 ≤ a 0 + a 1 + a 2 + a 3 + a 4) ∧
             (a 6 + a 7 + a 8 + 419 ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5))
    (hS511 : 511 ≤ ∑ i : Fin 9, a i)
    (hok_full : okSQ qlb (∑ i : Fin 9, a i) (∑ i : Fin 9, a i ^ 2) = true)
    (hG : TailGap 4 G a)
    (hsum4 : sum4 = a 0 + a 1 + a 2 + a 3)
    (hsq4 : sq4 = a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2)
    (hb5 : l5 ≤ a 5 ∧ a 5 ≤ h5) (hb6 : l6 ≤ a 6 ∧ a 6 ≤ h6)
    (hb7 : l7 ≤ a 7 ∧ a 7 ≤ h7) (hb8 : l8 ≤ a 8 ∧ a 8 ≤ h8) :
    let R4 := kronR 4 (by omega) a
    let R4pos := Nat.div R4 (Nat.pow 256 sum4)
    ∀ (fuel cur : ℕ), a 4 ≤ cur → cur < a 4 + fuel →
      loopK4 qlb (a 0) (a 1) (a 2) (a 3) sum4 sq4 R4 R4pos G l5 h5 l6 h6 l7 h7 l8 h8 fuel cur = false := by
  intro R4 R4pos fuel
  have hsum4_fin : ∑ i : Fin 4, a ⟨i.val, by omega⟩ = sum4 := by
    rw [hsum4]; simp [Fin.sum_univ_succ, add_assoc]
  have hR4pos_eq : R4pos = kronR 4 (by omega) a / 256 ^ (∑ i : Fin 4, a ⟨i.val, by omega⟩) := by
    dsimp [R4pos, R4]; rw [hsum4_fin]; rfl
  have hG1 : 1 ≤ G := hG.1
  have ha45 : a 5 + max 1 G ≤ a 4 := by have := tailGap_diff_ge ha hG (by omega) (by decide : (4 : Fin 9) < 5); omega
  have ha56 : a 6 + max 1 G ≤ a 5 := by have := tailGap_diff_ge ha hG (by omega) (by decide : (5 : Fin 9) < 6); omega
  have ha67 : a 7 + max 1 G ≤ a 6 := by have := tailGap_diff_ge ha hG (by omega) (by decide : (6 : Fin 9) < 7); omega
  have ha78 : a 8 + max 1 G ≤ a 7 := by have := tailGap_diff_ge ha hG (by omega) (by decide : (7 : Fin 9) < 8); omega
  have hG5 : TailGap 5 G a := tailGap_mono_k (by omega) hG
  have hmom5 := tailGap_sum_and_sq (by omega) hG5
  have hT5_eq : (univ : Finset (Fin 9)).filter (fun i => 5 ≤ i.val) = {5, 6, 7, 8} := by decide
  have h58_sum : 15 * G ≤ a 5 + a 6 + a 7 + a 8 := by
    have h1 := hmom5.1; rw [hT5_eq] at h1; simp at h1; omega
  have h58_sq : 85 * G ^ 2 ≤ a 5 ^ 2 + a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2 := by
    have h1 := hmom5.2; rw [hT5_eq] at h1; simp at h1; omega
  have hS_split : ∑ i : Fin 9, a i = sum4 + a 4 + (a 5 + a 6 + a 7 + a 8) := by
    rw [hsum4]; simp [Fin.sum_univ_succ, add_assoc]
  have hQ_split : ∑ i : Fin 9, a i ^ 2 = sq4 + a 4 ^ 2 + (a 5 ^ 2 + a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2) := by
    rw [hsq4]; simp [Fin.sum_univ_succ, add_assoc]
  have hok_u := okSQ_iff.mp hok_full
  induction fuel with
  | zero => intro cur h1 h2; omega
  | succ fuel ih =>
    intro cur hle hlt
    unfold loopK4; dsimp only
    let nh5 := nmin h5 (Nat.sub cur (nmax 1 G))
    let nh6 := nmin h6 (Nat.sub nh5 (nmax 1 G))
    let nh7 := nmin h7 (Nat.sub nh6 (nmax 1 G))
    let nh8 := nmin h8 (Nat.sub nh7 (nmax 1 G))
    have ha5_nh : a 5 ≤ nh5 := by dsimp [nh5]; rw [nmin_eq, nmax_eq]; omega
    have ha6_nh : a 6 ≤ nh6 := by dsimp [nh6]; rw [nmin_eq, nmax_eq]; omega
    have ha7_nh : a 7 ≤ nh7 := by dsimp [nh7]; rw [nmin_eq, nmax_eq]; omega
    have ha8_nh : a 8 ≤ nh8 := by dsimp [nh8]; rw [nmin_eq, nmax_eq]; omega
    have hnot_b : or (Nat.blt nh5 l5) (or (Nat.blt nh6 l6) (or (Nat.blt nh7 l7) (Nat.blt nh8 l8))) = false := by
      simp [blt_false_of_le (le_trans hb5.1 ha5_nh), blt_false_of_le (le_trans hb6.1 ha6_nh),
            blt_false_of_le (le_trans hb7.1 ha7_nh), blt_false_of_le (le_trans hb8.1 ha8_nh)]
    have hmaxQ_ge : qlb ≤ Nat.add (Nat.add sq4 (Nat.mul cur cur)) (Nat.add (Nat.mul nh5 nh5) (Nat.add (Nat.mul nh6 nh6) (Nat.add (Nat.mul nh7 nh7) (Nat.mul nh8 nh8)))) := by
      have h1 := hok_u.1; rw [hQ_split] at h1
      change qlb ≤ sq4 + cur * cur + (nh5 * nh5 + (nh6 * nh6 + (nh7 * nh7 + nh8 * nh8)))
      have s4 := sq_le_mul_of_le hle; have s5 := sq_le_mul_of_le ha5_nh; have s6 := sq_le_mul_of_le ha6_nh
      have s7 := sq_le_mul_of_le ha7_nh; have s8 := sq_le_mul_of_le ha8_nh; omega
    have hnot_mQ : Nat.blt (Nat.add (Nat.add sq4 (Nat.mul cur cur)) (Nat.add (Nat.mul nh5 nh5) (Nat.add (Nat.mul nh6 nh6) (Nat.add (Nat.mul nh7 nh7) (Nat.mul nh8 nh8))))) qlb = false :=
      blt_false_of_le hmaxQ_ge
    dsimp only [nh5, nh6, nh7, nh8] at hnot_b hnot_mQ
    simp only [hnot_b, hnot_mQ, Bool.false_eq_true, ite_false]
    by_cases hEq : cur = a 4
    · subst hEq
      let sum5 := Nat.add sum4 (a 4)
      let sq5 := Nat.add sq4 (Nat.mul (a 4) (a 4))
      let s3 := Nat.add (a 0) (Nat.add (a 1) (a 2))
      let s4 := Nat.add s3 (a 3)
      let s5 := Nat.add s4 (a 4)
      let Thi5 := nmin (Nat.add nh5 (Nat.add nh6 (Nat.add nh7 nh8)))
                  (nmin (Nat.sub s4 125)
                  (nmin (Nat.sub s5 251)
                  (nmin (Nat.sub (Nat.add s3 nh5) 83)
                  (nmin (Nat.sub (Nat.add s5 nh5) 335) (Nat.sub (Nat.add s5 (Nat.mul 2 nh5)) 419)))))
      let Tlo5 := nmax (Nat.sub 511 sum5) (Nat.mul 15 G)
      have hTlo : Tlo5 ≤ a 5 + a 6 + a 7 + a 8 := by dsimp [Tlo5, sum5]; rw [nmax_eq]; omega
      have hThi : a 5 + a 6 + a 7 + a 8 ≤ Thi5 := by dsimp [Thi5, s5, s4, s3]; simp only [nmin_eq]; omega
      have hok_cur : okSQ qlb (Nat.add sum5 Tlo5) (Nat.add sq5 (Nat.add (Nat.mul nh5 nh5) (Nat.add (Nat.mul nh6 nh6) (Nat.add (Nat.mul nh7 nh7) (Nat.mul nh8 nh8))))) = true :=
        okSQ_mono (by rw [hS_split]; dsimp [sum5]; omega)
          (by rw [hQ_split]; dsimp [sq5]; change sq4 + a 4 ^ 2 + (a 5 ^ 2 + a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2) ≤ sq4 + a 4 * a 4 + (nh5 * nh5 + (nh6 * nh6 + (nh7 * nh7 + nh8 * nh8)))
              have s4 : a 4 ^ 2 = a 4 * a 4 := sq _; have s5 := sq_le_mul_of_le ha5_nh; have s6 := sq_le_mul_of_le ha6_nh
              have s7 := sq_le_mul_of_le ha7_nh; have s8 := sq_le_mul_of_le ha8_nh; omega)
          hok_full
      have hok5 : okSQ qlb (sum5 + (a 5 + a 6 + a 7 + a 8)) (sq5 + (a 5 ^ 2 + a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2)) = true := by
        rw [show sum5 + (a 5 + a 6 + a 7 + a 8) = ∑ i : Fin 9, a i by dsimp [sum5]; exact hS_split.symm,
            show sq5 + (a 5 ^ 2 + a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2) = ∑ i : Fin 9, a i ^ 2 by dsimp [sq5]; rw [hQ_split]; ring]
        exact hok_full
      have hbox4 : checkBox4 qlb sum5 sq5 Tlo5 Thi5 (Nat.mul 85 (Nat.mul G G)) l5 nh5 l6 nh6 l7 nh7 l8 nh8 = true :=
        checkBox4_sound ⟨hb5.1, ha5_nh⟩ ⟨hb6.1, ha6_nh⟩ ⟨hb7.1, ha7_nh⟩ ⟨hb8.1, ha8_nh⟩
          ⟨le_of_lt (ha (by decide)), le_of_lt (ha (by decide)), le_of_lt (ha (by decide))⟩
          ⟨hTlo, hThi⟩ (by change 85 * (G * G) ≤ _; rw [← sq]; exact h58_sq) hok5
      have htp4 : testPos R4pos (a 4) = false := by
        rw [hR4pos_eq]; simpa using tail_diff_not_testPos (k := 4) (by omega) hinj (U := {4}) (V := ∅) (by decide)
          (by intro i hi; simp at hi; subst hi; omega) (by simp) (by simp)
      have hk5 := solveK5_false ha ha1 hinj hgap hspan hS511 hok_full hG
        (show sum5 = a 0 + a 1 + a 2 + a 3 + a 4 by dsimp [sum5]; omega)
        (show sq5 = a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2 + a 4 ^ 2 by dsimp [sq5]; rw [hsq4]; ring)
      have hR5 : updR R4 (a 4) = kronR 5 (by omega) a := (kronR_succ (k := 4) (by omega) a).symm
      rw [← hR5] at hk5
      change (if (if Nat.blt Thi5 Tlo5 = true then true
        else if not (okSQ qlb (Nat.add sum5 Tlo5) (Nat.add sq5 (Nat.add (Nat.mul nh5 nh5) (Nat.add (Nat.mul nh6 nh6) (Nat.add (Nat.mul nh7 nh7) (Nat.mul nh8 nh8)))))) = true then true
        else if not (checkBox4 qlb sum5 sq5 Tlo5 Thi5 (Nat.mul 85 (Nat.mul G G)) l5 nh5 l6 nh6 l7 nh7 l8 nh8) = true then true
        else if testPos R4pos (a 4) = true then true
        else solveK5 qlb (a 0) (a 1) (a 2) (a 3) (a 4) sum5 sq5 (updR R4 (a 4)) G) = true then _ else false) = false
      simp only [blt_false_of_le (le_trans hTlo hThi), hok_cur, hbox4, htp4, Bool.not_true, Bool.false_eq_true, ite_false, hk5]
    · have hrec := ih (Nat.sub cur 1) (by change a 4 ≤ cur - 1; omega) (by change cur - 1 < a 4 + fuel; omega)
      split_ifs <;> try exact hrec
      all_goals rfl

private lemma solveK4_false {qlb sum4 sq4 Gin : ℕ} {a : Fin 9 → ℕ}
    (ha : StrictAnti a) (ha1 : ∀ i, 1 ≤ a i)
    (hinj : Function.Injective (fun U : Finset (Fin 9) => ∑ i ∈ U, a i))
    (hgap : ∀ i j : Fin 9, i ≤ j → j.val - i.val ≤ 6 → a j + gBound (j.val - i.val) ≤ a i)
    (hspan : (a 5 + a 6 + a 7 + a 8 + 125 ≤ a 0 + a 1 + a 2 + a 3) ∧
             (a 5 + a 6 + a 7 + a 8 + 251 ≤ a 0 + a 1 + a 2 + a 3 + a 4) ∧
             (a 6 + a 7 + a 8 + 83 ≤ a 0 + a 1 + a 2) ∧
             (a 6 + a 7 + a 8 + 335 ≤ a 0 + a 1 + a 2 + a 3 + a 4) ∧
             (a 6 + a 7 + a 8 + 419 ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5))
    (hS511 : 511 ≤ ∑ i : Fin 9, a i)
    (hok_full : okSQ qlb (∑ i : Fin 9, a i) (∑ i : Fin 9, a i ^ 2) = true)
    (hGin : TailGap 3 Gin a)
    (hsum4 : sum4 = a 0 + a 1 + a 2 + a 3)
    (hsq4 : sq4 = a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2) :
    solveK4 qlb (a 0) (a 1) (a 2) (a 3) sum4 sq4 (kronR 4 (by omega) a) Gin = false := by
  unfold solveK4; dsimp only
  have hsum4_fin : ∑ i : Fin 4, a ⟨i.val, by omega⟩ = sum4 := by
    rw [hsum4]; simp [Fin.sum_univ_succ, add_assoc]
  let R4pos := Nat.div (kronR 4 (by omega) a) (Nat.pow 256 sum4)
  have hR4pos_eq : R4pos = kronR 4 (by omega) a / 256 ^ (∑ i : Fin 4, a ⟨i.val, by omega⟩) := by
    dsimp [R4pos]; rw [hsum4_fin]; rfl
  have hdig := kronR_digit (k := 4) (by omega) hinj
  have hmod16 : Nat.beq (Nat.mod R4pos 256) 16 = true := by
    have : R4pos % 256 = 16 := by rw [hR4pos_eq]; simpa using hdig.1
    change Nat.beq (R4pos % 256) 16 = true; rw [this]; rfl
  dsimp only [R4pos] at hmod16
  simp only [hmod16, Bool.not_true, Bool.false_eq_true, ite_false]
  let G := findG R4pos Gin
  have hG : TailGap 4 G a := by
    dsimp [G]; rw [hR4pos_eq]; exact findG_tailGap (k := 4) (by omega) hinj (tailGap_mono_k (by omega) hGin)
  have hG1 : 1 ≤ G := hG.1; have hGin1 : 1 ≤ Gin := hGin.1
  have ha34 : a 4 + max 1 Gin ≤ a 3 := by have := tailGap_diff_ge ha hGin (by omega) (by decide : (3 : Fin 9) < 4); omega
  have ha45 : a 5 + max 1 G ≤ a 4 := by have := tailGap_diff_ge ha hG (by omega) (by decide : (4 : Fin 9) < 5); omega
  have ha56 : a 6 + max 1 G ≤ a 5 := by have := tailGap_diff_ge ha hG (by omega) (by decide : (5 : Fin 9) < 6); omega
  have ha67 : a 7 + max 1 G ≤ a 6 := by have := tailGap_diff_ge ha hG (by omega) (by decide : (6 : Fin 9) < 7); omega
  have ha78 : a 8 + max 1 G ≤ a 7 := by have := tailGap_diff_ge ha hG (by omega) (by decide : (7 : Fin 9) < 8); omega
  have h8_ge : max 1 G ≤ a 8 := by have := tailGap_elem_ge hG (i := 8) (by omega); have := ha1 8; omega
  have h6_ge4 : 4 * G ≤ a 6 := tailGap_a6_ge_4G (by omega) ha hG
  have hg24 := hgap 2 4 (by decide) (by decide); have hg14 := hgap 1 4 (by decide) (by decide); have hg04 := hgap 0 4 (by decide) (by decide)
  have hg35 := hgap 3 5 (by decide) (by decide); have hg25 := hgap 2 5 (by decide) (by decide)
  have hg15 := hgap 1 5 (by decide) (by decide); have hg05 := hgap 0 5 (by decide) (by decide)
  have hg36 := hgap 3 6 (by decide) (by decide); have hg26 := hgap 2 6 (by decide) (by decide)
  have hg16 := hgap 1 6 (by decide) (by decide); have hg06 := hgap 0 6 (by decide) (by decide)
  have hg37 := hgap 3 7 (by decide) (by decide); have hg27 := hgap 2 7 (by decide) (by decide); have hg17 := hgap 1 7 (by decide) (by decide)
  have hg38 := hgap 3 8 (by decide) (by decide); have hg28 := hgap 2 8 (by decide) (by decide)
  have hg58 := hgap 5 8 (by decide) (by decide); have hg48 := hgap 4 8 (by decide) (by decide)
  norm_num [gBound] at hg24 hg14 hg04 hg35 hg25 hg15 hg05 hg36 hg26 hg16 hg06 hg37 hg27 hg17 hg38 hg28 hg58 hg48
  have htp4 : testPos R4pos (a 4) = false := by
    rw [hR4pos_eq]; simpa using tail_diff_not_testPos (k := 4) (by omega) hinj (U := {4}) (V := ∅) (by decide)
      (by intro i hi; simp at hi; subst hi; omega) (by simp) (by simp)
  have htp5 : testPos R4pos (a 5) = false := by
    rw [hR4pos_eq]; simpa using tail_diff_not_testPos (k := 4) (by omega) hinj (U := {5}) (V := ∅) (by decide)
      (by intro i hi; simp at hi; subst hi; omega) (by simp) (by simp)
  have htp6 : testPos R4pos (a 6) = false := by
    rw [hR4pos_eq]; simpa using tail_diff_not_testPos (k := 4) (by omega) hinj (U := {6}) (V := ∅) (by decide)
      (by intro i hi; simp at hi; subst hi; omega) (by simp) (by simp)
  have htp7 : testPos R4pos (a 7) = false := by
    rw [hR4pos_eq]; simpa using tail_diff_not_testPos (k := 4) (by omega) hinj (U := {7}) (V := ∅) (by decide)
      (by intro i hi; simp at hi; subst hi; omega) (by simp) (by simp)
  have htp8 : testPos R4pos (a 8) = false := by
    rw [hR4pos_eq]; simpa using tail_diff_not_testPos (k := 4) (by omega) hinj (U := {8}) (V := ∅) (by decide)
      (by intro i hi; simp at hi; subst hi; omega) (by simp) (by simp)
  let h4_0 := nmin (Nat.sub (a 3) (nmax 1 Gin)) (nmin (Nat.sub (a 2) 2) (nmin (Nat.sub (a 1) 4) (Nat.sub (a 0) 7)))
  let h5_0 := nmin (Nat.sub h4_0 (nmax 1 G)) (nmin (Nat.sub (a 3) 2) (nmin (Nat.sub (a 2) 4) (nmin (Nat.sub (a 1) 7) (Nat.sub (a 0) 13))))
  let h6_0 := nmin (Nat.sub h5_0 (nmax 1 G)) (nmin (Nat.sub (a 3) 4) (nmin (Nat.sub (a 2) 7) (nmin (Nat.sub (a 1) 13) (Nat.sub (a 0) 22))))
  let h7_0 := nmin (Nat.sub h6_0 (nmax 1 G)) (nmin (Nat.sub (a 3) 7) (nmin (Nat.sub (a 2) 13) (Nat.sub (a 1) 22)))
  let h8_0 := nmin (Nat.sub h7_0 (nmax 1 G)) (nmin (Nat.sub (a 3) 13) (Nat.sub (a 2) 22))
  let l8_0 := nmax 1 G
  let l7_0 := nmax (nmax 2 (Nat.mul 2 G)) (Nat.add l8_0 (nmax 1 G))
  let l6_0 := nmax (nmax 4 (Nat.mul 4 G)) (Nat.add l7_0 (nmax 1 G))
  let l5_0 := nmax 5 (Nat.add l6_0 (nmax 1 G))
  let l4_0 := nmax 8 (Nat.add l5_0 (nmax 1 G))
  have ha4_h0 : a 4 ≤ h4_0 := by dsimp [h4_0]; simp only [nmin_eq, nmax_eq]; omega
  have ha5_h0 : a 5 ≤ h5_0 := by dsimp [h5_0]; simp only [nmin_eq, nmax_eq]; omega
  have ha6_h0 : a 6 ≤ h6_0 := by dsimp [h6_0]; simp only [nmin_eq, nmax_eq]; omega
  have ha7_h0 : a 7 ≤ h7_0 := by dsimp [h7_0]; simp only [nmin_eq, nmax_eq]; omega
  have ha8_h0 : a 8 ≤ h8_0 := by dsimp [h8_0]; simp only [nmin_eq, nmax_eq]; omega
  have ha8_l0 : l8_0 ≤ a 8 := by dsimp [l8_0]; simp only [nmax_eq]; omega
  have ha7_l0 : l7_0 ≤ a 7 := by dsimp [l7_0]; simp only [nmax_eq]; omega
  have ha6_l0 : l6_0 ≤ a 6 := by dsimp [l6_0]; simp only [nmax_eq]; omega
  have ha5_l0 : l5_0 ≤ a 5 := by dsimp [l5_0]; simp only [nmax_eq]; omega
  have ha4_l0 : l4_0 ≤ a 4 := by dsimp [l4_0]; simp only [nmax_eq]; omega
  have hnot_b0 : or (Nat.blt h4_0 l4_0) (or (Nat.blt h5_0 l5_0) (or (Nat.blt h6_0 l6_0) (or (Nat.blt h7_0 l7_0) (Nat.blt h8_0 l8_0)))) = false := by
    simp [blt_false_of_le (le_trans ha4_l0 ha4_h0), blt_false_of_le (le_trans ha5_l0 ha5_h0),
          blt_false_of_le (le_trans ha6_l0 ha6_h0), blt_false_of_le (le_trans ha7_l0 ha7_h0),
          blt_false_of_le (le_trans ha8_l0 ha8_h0)]
  change (if or (Nat.blt h4_0 l4_0) (or (Nat.blt h5_0 l5_0) (or (Nat.blt h6_0 l6_0) (or (Nat.blt h7_0 l7_0) (Nat.blt h8_0 l8_0)))) = true then true else _) = false
  simp only [hnot_b0, Bool.false_eq_true, ite_false]
  let h4 := skipHi R4pos l4_0 h4_0
  let l8 := skipLo R4pos l8_0 h8_0
  let h5 := skipHi R4pos l5_0 (nmin h5_0 (Nat.sub h4 (nmax 1 G)))
  let h6 := skipHi R4pos l6_0 (nmin h6_0 (Nat.sub h5 (nmax 1 G)))
  let h7 := skipHi R4pos l7_0 (nmin h7_0 (Nat.sub h6 (nmax 1 G)))
  let h8 := skipHi R4pos l8 (nmin h8_0 (Nat.sub h7 (nmax 1 G)))
  let l7 := skipLo R4pos (nmax l7_0 (Nat.add l8 (nmax 1 G))) h7
  let l6 := skipLo R4pos (nmax l6_0 (Nat.add l7 (nmax 1 G))) h6
  let l5 := skipLo R4pos (nmax l5_0 (Nat.add l6 (nmax 1 G))) h5
  let l4 := skipLo R4pos (nmax l4_0 (Nat.add l5 (nmax 1 G))) h4
  have ha4_h : a 4 ≤ h4 := skipHi_ge (ha1 4) ha4_h0 htp4
  have ha8_l : l8 ≤ a 8 := skipLo_le ha8_l0 htp8
  have ha5_h : a 5 ≤ h5 := skipHi_ge (ha1 5) (by rw [nmin_eq, nmax_eq]; exact le_min ha5_h0 (by change a 5 ≤ h4 - max 1 G; omega)) htp5
  have ha6_h : a 6 ≤ h6 := skipHi_ge (ha1 6) (by rw [nmin_eq, nmax_eq]; exact le_min ha6_h0 (by change a 6 ≤ h5 - max 1 G; omega)) htp6
  have ha7_h : a 7 ≤ h7 := skipHi_ge (ha1 7) (by rw [nmin_eq, nmax_eq]; exact le_min ha7_h0 (by change a 7 ≤ h6 - max 1 G; omega)) htp7
  have ha8_h : a 8 ≤ h8 := skipHi_ge (ha1 8) (by rw [nmin_eq, nmax_eq]; exact le_min ha8_h0 (by change a 8 ≤ h7 - max 1 G; omega)) htp8
  have ha7_l : l7 ≤ a 7 := skipLo_le (by rw [nmax_eq, nmax_eq]; exact max_le ha7_l0 (by change l8 + max 1 G ≤ a 7; omega)) htp7
  have ha6_l : l6 ≤ a 6 := skipLo_le (by rw [nmax_eq, nmax_eq]; exact max_le ha6_l0 (by change l7 + max 1 G ≤ a 6; omega)) htp6
  have ha5_l : l5 ≤ a 5 := skipLo_le (by rw [nmax_eq, nmax_eq]; exact max_le ha5_l0 (by change l6 + max 1 G ≤ a 5; omega)) htp5
  have ha4_l : l4 ≤ a 4 := skipLo_le (by rw [nmax_eq, nmax_eq]; exact max_le ha4_l0 (by change l5 + max 1 G ≤ a 4; omega)) htp4
  have hnot_b1 : or (Nat.blt h4 l4) (or (Nat.blt h5 l5) (or (Nat.blt h6 l6) (or (Nat.blt h7 l7) (Nat.blt h8 l8)))) = false := by
    simp [blt_false_of_le (le_trans ha4_l ha4_h), blt_false_of_le (le_trans ha5_l ha5_h),
          blt_false_of_le (le_trans ha6_l ha6_h), blt_false_of_le (le_trans ha7_l ha7_h),
          blt_false_of_le (le_trans ha8_l ha8_h)]
  change (if or (Nat.blt h4 l4) (or (Nat.blt h5 l5) (or (Nat.blt h6 l6) (or (Nat.blt h7 l7) (Nat.blt h8 l8)))) = true then true else _) = false
  simp only [hnot_b1, Bool.false_eq_true, ite_false]
  have hmom4 := tailGap_sum_and_sq (by omega) hG
  have hT4_eq : (univ : Finset (Fin 9)).filter (fun i => 4 ≤ i.val) = {4, 5, 6, 7, 8} := by decide
  have h48_sum : 31 * G ≤ a 4 + a 5 + a 6 + a 7 + a 8 := by
    have h1 := hmom4.1; rw [hT4_eq] at h1; simp at h1; omega
  have h48_sq : 341 * G ^ 2 ≤ a 4 ^ 2 + a 5 ^ 2 + a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2 := by
    have h1 := hmom4.2; rw [hT4_eq] at h1; simp at h1; omega
  have hS_split : ∑ i : Fin 9, a i = sum4 + (a 4 + a 5 + a 6 + a 7 + a 8) := by
    rw [hsum4]; simp [Fin.sum_univ_succ, add_assoc]
  have hQ_split : ∑ i : Fin 9, a i ^ 2 = sq4 + (a 4 ^ 2 + a 5 ^ 2 + a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2) := by
    rw [hsq4]; simp [Fin.sum_univ_succ, add_assoc]
  let s3 := Nat.add (a 0) (Nat.add (a 1) (a 2))
  let s4 := Nat.add s3 (a 3)
  let Tlo := nmax (Nat.sub 511 sum4) (Nat.mul 31 G)
  let Thi := nmin (Nat.add h4 (Nat.add h5 (Nat.add h6 (Nat.add h7 h8))))
             (nmin (Nat.sub (Nat.add s4 h4) 125)
             (nmin (Nat.sub (Nat.add s4 (Nat.mul 2 h4)) 251)
             (nmin (Nat.sub (Nat.add s3 (Nat.add h4 h5)) 83)
             (nmin (Nat.sub (Nat.add s4 (Nat.add (Nat.mul 2 h4) h5)) 335)
                   (Nat.sub (Nat.add s4 (Nat.add (Nat.mul 2 h4) (Nat.mul 2 h5))) 419)))))
  have hTlo : Tlo ≤ a 4 + a 5 + a 6 + a 7 + a 8 := by dsimp [Tlo]; rw [nmax_eq]; omega
  have hThi : a 4 + a 5 + a 6 + a 7 + a 8 ≤ Thi := by dsimp [Thi, s4, s3]; simp only [nmin_eq]; omega
  have hok_u := okSQ_iff.mp hok_full
  have hmaxQ_ge : qlb ≤ Nat.add sq4 (Nat.add (Nat.mul h4 h4) (Nat.add (Nat.mul h5 h5) (Nat.add (Nat.mul h6 h6) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8))))) := by
    have h1 := hok_u.1; rw [hQ_split] at h1; change qlb ≤ sq4 + (h4 * h4 + (h5 * h5 + (h6 * h6 + (h7 * h7 + h8 * h8))))
    have s4 := sq_le_mul_of_le ha4_h; have s5 := sq_le_mul_of_le ha5_h; have s6 := sq_le_mul_of_le ha6_h
    have s7 := sq_le_mul_of_le ha7_h; have s8 := sq_le_mul_of_le ha8_h; omega
  have hok4 : okSQ qlb (sum4 + (a 4 + a 5 + a 6 + a 7 + a 8)) (sq4 + (a 4 ^ 2 + a 5 ^ 2 + a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2)) = true := by
    rw [← hS_split, ← hQ_split]; exact hok_full
  have hbox5 : checkBox5 qlb sum4 sq4 Tlo Thi (Nat.mul 341 (Nat.mul G G)) l4 h4 l5 h5 l6 h6 l7 h7 l8 h8 = true :=
    checkBox5_sound ⟨ha4_l, ha4_h⟩ ⟨ha5_l, ha5_h⟩ ⟨ha6_l, ha6_h⟩ ⟨ha7_l, ha7_h⟩ ⟨ha8_l, ha8_h⟩
      ⟨le_of_lt (ha (by decide)), le_of_lt (ha (by decide)), le_of_lt (ha (by decide)), le_of_lt (ha (by decide))⟩
      ⟨hTlo, hThi⟩ (by change 341 * (G * G) ≤ _; rw [← sq]; exact h48_sq) hok4
  change (if Nat.blt Thi Tlo = true then true else
    if Nat.blt (Nat.add sq4 (Nat.add (Nat.mul h4 h4) (Nat.add (Nat.mul h5 h5) (Nat.add (Nat.mul h6 h6) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8)))))) qlb = true then true else
    if not (checkBox5 qlb sum4 sq4 Tlo Thi (Nat.mul 341 (Nat.mul G G)) l4 h4 l5 h5 l6 h6 l7 h7 l8 h8) = true then true else
    loopK4 qlb (a 0) (a 1) (a 2) (a 3) sum4 sq4 (kronR 4 (by omega) a) R4pos G l5 h5 l6 h6 l7 h7 l8 h8 (Nat.add (Nat.sub h4 l4) 1) h4) = false
  simp only [blt_false_of_le (le_trans hTlo hThi), blt_false_of_le hmaxQ_ge, hbox5, Bool.not_true, Bool.false_eq_true, ite_false]
  exact loopK4_false ha ha1 hinj hgap hspan hS511 hok_full hG hsum4 hsq4 ⟨ha5_l, ha5_h⟩ ⟨ha6_l, ha6_h⟩ ⟨ha7_l, ha7_h⟩ ⟨ha8_l, ha8_h⟩
    (Nat.add (Nat.sub h4 l4) 1) h4 ha4_h (by change h4 < a 4 + (h4 - l4 + 1); omega)

private lemma loopK3_false {qlb sum3 sq3 G : ℕ} {a : Fin 9 → ℕ}
    (ha : StrictAnti a) (ha1 : ∀ i, 1 ≤ a i)
    (hinj : Function.Injective (fun U : Finset (Fin 9) => ∑ i ∈ U, a i))
    (hgap : ∀ i j : Fin 9, i ≤ j → j.val - i.val ≤ 6 → a j + gBound (j.val - i.val) ≤ a i)
    (hspan : (a 5 + a 6 + a 7 + a 8 + 125 ≤ a 0 + a 1 + a 2 + a 3) ∧
             (a 5 + a 6 + a 7 + a 8 + 251 ≤ a 0 + a 1 + a 2 + a 3 + a 4) ∧
             (a 6 + a 7 + a 8 + 83 ≤ a 0 + a 1 + a 2) ∧
             (a 6 + a 7 + a 8 + 335 ≤ a 0 + a 1 + a 2 + a 3 + a 4) ∧
             (a 6 + a 7 + a 8 + 419 ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5))
    (hS511 : 511 ≤ ∑ i : Fin 9, a i)
    (hok_full : okSQ qlb (∑ i : Fin 9, a i) (∑ i : Fin 9, a i ^ 2) = true)
    (hG : TailGap 3 G a)
    (hsum3 : sum3 = a 0 + a 1 + a 2)
    (hsq3 : sq3 = a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2) :
    let R3 := kronR 3 (by omega) a
    let R3pos := Nat.div R3 (Nat.pow 256 sum3)
    ∀ (fuel cur : ℕ), a 3 ≤ cur → cur < a 3 + fuel →
      loopK3 qlb (a 0) (a 1) (a 2) sum3 sq3 R3 R3pos G fuel cur = false := by
  intro R3 R3pos fuel
  have hsum3_fin : ∑ i : Fin 3, a ⟨i.val, by omega⟩ = sum3 := by
    rw [hsum3]; simp [Fin.sum_univ_succ, add_assoc]
  have hR3pos_eq : R3pos = kronR 3 (by omega) a / 256 ^ (∑ i : Fin 3, a ⟨i.val, by omega⟩) := by
    dsimp [R3pos, R3]; rw [hsum3_fin]; rfl
  have hG1 : 1 ≤ G := hG.1
  have ha34 : a 4 + max 1 G ≤ a 3 := by have := tailGap_diff_ge ha hG (by omega) (by decide : (3 : Fin 9) < 4); omega
  have ha45 : a 5 + max 1 G ≤ a 4 := by have := tailGap_diff_ge ha hG (by omega) (by decide : (4 : Fin 9) < 5); omega
  have ha56 : a 6 + max 1 G ≤ a 5 := by have := tailGap_diff_ge ha hG (by omega) (by decide : (5 : Fin 9) < 6); omega
  have ha67 : a 7 + max 1 G ≤ a 6 := by have := tailGap_diff_ge ha hG (by omega) (by decide : (6 : Fin 9) < 7); omega
  have ha78 : a 8 + max 1 G ≤ a 7 := by have := tailGap_diff_ge ha hG (by omega) (by decide : (7 : Fin 9) < 8); omega
  have hg24 := hgap 2 4 (by decide) (by decide); have hg14 := hgap 1 4 (by decide) (by decide); have hg04 := hgap 0 4 (by decide) (by decide)
  have hg25 := hgap 2 5 (by decide) (by decide); have hg15 := hgap 1 5 (by decide) (by decide); have hg05 := hgap 0 5 (by decide) (by decide)
  have hg26 := hgap 2 6 (by decide) (by decide); have hg16 := hgap 1 6 (by decide) (by decide); have hg06 := hgap 0 6 (by decide) (by decide)
  have hg27 := hgap 2 7 (by decide) (by decide); have hg17 := hgap 1 7 (by decide) (by decide); have hg28 := hgap 2 8 (by decide) (by decide)
  norm_num [gBound] at hg24 hg14 hg04 hg25 hg15 hg05 hg26 hg16 hg06 hg27 hg17 hg28
  have hG4 : TailGap 4 G a := tailGap_mono_k (by omega) hG
  have hmom4 := tailGap_sum_and_sq (by omega) hG4
  have hT4_eq : (univ : Finset (Fin 9)).filter (fun i => 4 ≤ i.val) = {4, 5, 6, 7, 8} := by decide
  have h48_sum : 31 * G ≤ a 4 + a 5 + a 6 + a 7 + a 8 := by
    have h1 := hmom4.1; rw [hT4_eq] at h1; simp at h1; omega
  have hS_split : ∑ i : Fin 9, a i = sum3 + a 3 + (a 4 + a 5 + a 6 + a 7 + a 8) := by
    rw [hsum3]; simp [Fin.sum_univ_succ, add_assoc]
  have hQ_split : ∑ i : Fin 9, a i ^ 2 = sq3 + a 3 ^ 2 + (a 4 ^ 2 + a 5 ^ 2 + a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2) := by
    rw [hsq3]; simp [Fin.sum_univ_succ, add_assoc]
  have hok_u := okSQ_iff.mp hok_full
  induction fuel with
  | zero => intro cur h1 h2; omega
  | succ fuel ih =>
    intro cur hle hlt
    unfold loopK3; dsimp only
    let h4 := nmin (Nat.sub cur (nmax 1 G)) (nmin (Nat.sub (a 2) 2) (nmin (Nat.sub (a 1) 4) (Nat.sub (a 0) 7)))
    let h5 := nmin (Nat.sub h4 (nmax 1 G)) (nmin (Nat.sub (a 2) 4) (nmin (Nat.sub (a 1) 7) (Nat.sub (a 0) 13)))
    let h6 := nmin (Nat.sub h5 (nmax 1 G)) (nmin (Nat.sub (a 2) 7) (nmin (Nat.sub (a 1) 13) (Nat.sub (a 0) 22)))
    let h7 := nmin (Nat.sub h6 (nmax 1 G)) (nmin (Nat.sub (a 2) 13) (Nat.sub (a 1) 22))
    let h8 := nmin (Nat.sub h7 (nmax 1 G)) (Nat.sub (a 2) 22)
    have ha4_h : a 4 ≤ h4 := by dsimp [h4]; simp only [nmin_eq, nmax_eq]; omega
    have ha5_h : a 5 ≤ h5 := by dsimp [h5]; simp only [nmin_eq, nmax_eq]; omega
    have ha6_h : a 6 ≤ h6 := by dsimp [h6]; simp only [nmin_eq, nmax_eq]; omega
    have ha7_h : a 7 ≤ h7 := by dsimp [h7]; simp only [nmin_eq, nmax_eq]; omega
    have ha8_h : a 8 ≤ h8 := by dsimp [h8]; simp only [nmin_eq, nmax_eq]; omega
    have hmaxQ_ge : qlb ≤ Nat.add (Nat.add sq3 (Nat.mul cur cur)) (Nat.add (Nat.mul h4 h4) (Nat.add (Nat.mul h5 h5) (Nat.add (Nat.mul h6 h6) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8))))) := by
      have h1 := hok_u.1; rw [hQ_split] at h1
      change qlb ≤ sq3 + cur * cur + (h4 * h4 + (h5 * h5 + (h6 * h6 + (h7 * h7 + h8 * h8))))
      have s3 := sq_le_mul_of_le hle; have s4 := sq_le_mul_of_le ha4_h; have s5 := sq_le_mul_of_le ha5_h
      have s6 := sq_le_mul_of_le ha6_h; have s7 := sq_le_mul_of_le ha7_h; have s8 := sq_le_mul_of_le ha8_h; omega
    have hnot_mQ : Nat.blt (Nat.add (Nat.add sq3 (Nat.mul cur cur)) (Nat.add (Nat.mul h4 h4) (Nat.add (Nat.mul h5 h5) (Nat.add (Nat.mul h6 h6) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8)))))) qlb = false :=
      blt_false_of_le hmaxQ_ge
    dsimp only [h4, h5, h6, h7, h8] at hnot_mQ
    simp only [hnot_mQ, Bool.false_eq_true, ite_false]
    by_cases hEq : cur = a 3
    · subst hEq
      let sum4 := Nat.add sum3 (a 3)
      let sq4 := Nat.add sq3 (Nat.mul (a 3) (a 3))
      let Tlo := nmax (Nat.sub 511 sum4) (Nat.mul 31 G)
      let Thi := nmin (Nat.add h4 (Nat.add h5 (Nat.add h6 (Nat.add h7 h8))))
                 (nmin (Nat.sub (Nat.add sum4 h4) 125)
                 (nmin (Nat.sub (Nat.add sum4 (Nat.mul 2 h4)) 251)
                 (nmin (Nat.sub (Nat.add sum3 (Nat.add h4 h5)) 83)
                 (nmin (Nat.sub (Nat.add sum4 (Nat.add (Nat.mul 2 h4) h5)) 335)
                       (Nat.sub (Nat.add sum4 (Nat.add (Nat.mul 2 h4) (Nat.mul 2 h5))) 419)))))
      have hTlo : Tlo ≤ a 4 + a 5 + a 6 + a 7 + a 8 := by dsimp [Tlo, sum4]; rw [nmax_eq]; omega
      have hThi : a 4 + a 5 + a 6 + a 7 + a 8 ≤ Thi := by dsimp [Thi, sum4]; simp only [nmin_eq]; omega
      have hok_cur : okSQ qlb (Nat.add sum4 Tlo) (Nat.add sq4 (Nat.add (Nat.mul h4 h4) (Nat.add (Nat.mul h5 h5) (Nat.add (Nat.mul h6 h6) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8)))))) = true :=
        okSQ_mono (by rw [hS_split]; dsimp [sum4]; omega)
          (by rw [hQ_split]; dsimp [sq4]; change sq3 + a 3 ^ 2 + (a 4 ^ 2 + a 5 ^ 2 + a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2) ≤ sq3 + a 3 * a 3 + (h4 * h4 + (h5 * h5 + (h6 * h6 + (h7 * h7 + h8 * h8))))
              have s3 : a 3 ^ 2 = a 3 * a 3 := sq _; have s4 := sq_le_mul_of_le ha4_h; have s5 := sq_le_mul_of_le ha5_h
              have s6 := sq_le_mul_of_le ha6_h; have s7 := sq_le_mul_of_le ha7_h; have s8 := sq_le_mul_of_le ha8_h; omega)
          hok_full
      have htp3 : testPos R3pos (a 3) = false := by
        rw [hR3pos_eq]; simpa using tail_diff_not_testPos (k := 3) (by omega) hinj (U := {3}) (V := ∅) (by decide)
          (by intro i hi; simp at hi; subst hi; omega) (by simp) (by simp)
      have hk4 := solveK4_false ha ha1 hinj hgap hspan hS511 hok_full hG
        (show sum4 = a 0 + a 1 + a 2 + a 3 by dsimp [sum4]; omega)
        (show sq4 = a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2 by dsimp [sq4]; rw [hsq3]; ring)
      have hR4 : updR R3 (a 3) = kronR 4 (by omega) a := (kronR_succ (k := 3) (by omega) a).symm
      rw [← hR4] at hk4
      change (if (if Nat.blt Thi Tlo = true then true
        else if not (okSQ qlb (Nat.add sum4 Tlo) (Nat.add sq4 (Nat.add (Nat.mul h4 h4) (Nat.add (Nat.mul h5 h5) (Nat.add (Nat.mul h6 h6) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8))))))) = true then true
        else if testPos R3pos (a 3) = true then true
        else solveK4 qlb (a 0) (a 1) (a 2) (a 3) sum4 sq4 (updR R3 (a 3)) G) = true then _ else false) = false
      simp only [blt_false_of_le (le_trans hTlo hThi), hok_cur, htp3, Bool.not_true, Bool.false_eq_true, ite_false, hk4]
    · have hrec := ih (Nat.sub cur 1) (by change a 3 ≤ cur - 1; omega) (by change cur - 1 < a 3 + fuel; omega)
      split_ifs <;> try exact hrec
      all_goals rfl

private lemma solveK3_false {qlb sum3 sq3 Gin : ℕ} {a : Fin 9 → ℕ}
    (ha : StrictAnti a) (ha1 : ∀ i, 1 ≤ a i)
    (hinj : Function.Injective (fun U : Finset (Fin 9) => ∑ i ∈ U, a i))
    (hgap : ∀ i j : Fin 9, i ≤ j → j.val - i.val ≤ 6 → a j + gBound (j.val - i.val) ≤ a i)
    (hspan : (a 5 + a 6 + a 7 + a 8 + 125 ≤ a 0 + a 1 + a 2 + a 3) ∧
             (a 5 + a 6 + a 7 + a 8 + 251 ≤ a 0 + a 1 + a 2 + a 3 + a 4) ∧
             (a 6 + a 7 + a 8 + 83 ≤ a 0 + a 1 + a 2) ∧
             (a 6 + a 7 + a 8 + 335 ≤ a 0 + a 1 + a 2 + a 3 + a 4) ∧
             (a 6 + a 7 + a 8 + 419 ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5))
    (hS511 : 511 ≤ ∑ i : Fin 9, a i)
    (hok_full : okSQ qlb (∑ i : Fin 9, a i) (∑ i : Fin 9, a i ^ 2) = true)
    (hGin : TailGap 2 Gin a)
    (hsum3 : sum3 = a 0 + a 1 + a 2)
    (hsq3 : sq3 = a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2) :
    solveK3 qlb (a 0) (a 1) (a 2) sum3 sq3 (kronR 3 (by omega) a) Gin = false := by
  unfold solveK3; dsimp only
  have hsum3_fin : ∑ i : Fin 3, a ⟨i.val, by omega⟩ = sum3 := by
    rw [hsum3]; simp [Fin.sum_univ_succ, add_assoc]
  let R3pos := Nat.div (kronR 3 (by omega) a) (Nat.pow 256 sum3)
  have hR3pos_eq : R3pos = kronR 3 (by omega) a / 256 ^ (∑ i : Fin 3, a ⟨i.val, by omega⟩) := by
    dsimp [R3pos]; rw [hsum3_fin]; rfl
  have hdig := kronR_digit (k := 3) (by omega) hinj
  have hmod8 : Nat.beq (Nat.mod R3pos 256) 8 = true := by
    have : R3pos % 256 = 8 := by rw [hR3pos_eq]; simpa using hdig.1
    change Nat.beq (R3pos % 256) 8 = true; rw [this]; rfl
  dsimp only [R3pos] at hmod8
  simp only [hmod8, Bool.not_true, Bool.false_eq_true, ite_false]
  let G := findG R3pos Gin
  have hG : TailGap 3 G a := by
    dsimp [G]; rw [hR3pos_eq]; exact findG_tailGap (k := 3) (by omega) hinj (tailGap_mono_k (by omega) hGin)
  have hG1 : 1 ≤ G := hG.1; have hGin1 : 1 ≤ Gin := hGin.1
  have ha23 : a 3 + max 1 Gin ≤ a 2 := by have := tailGap_diff_ge ha hGin (by omega) (by decide : (2 : Fin 9) < 3); omega
  have ha34 : a 4 + max 1 G ≤ a 3 := by have := tailGap_diff_ge ha hG (by omega) (by decide : (3 : Fin 9) < 4); omega
  have ha45 : a 5 + max 1 G ≤ a 4 := by have := tailGap_diff_ge ha hG (by omega) (by decide : (4 : Fin 9) < 5); omega
  have ha56 : a 6 + max 1 G ≤ a 5 := by have := tailGap_diff_ge ha hG (by omega) (by decide : (5 : Fin 9) < 6); omega
  have ha67 : a 7 + max 1 G ≤ a 6 := by have := tailGap_diff_ge ha hG (by omega) (by decide : (6 : Fin 9) < 7); omega
  have ha78 : a 8 + max 1 G ≤ a 7 := by have := tailGap_diff_ge ha hG (by omega) (by decide : (7 : Fin 9) < 8); omega
  have h8_ge : max 1 G ≤ a 8 := by have := tailGap_elem_ge hG (i := 8) (by omega); have := ha1 8; omega
  have h6_ge4 : 4 * G ≤ a 6 := tailGap_a6_ge_4G (by omega) ha hG
  have hg13 := hgap 1 3 (by decide) (by decide); have hg03 := hgap 0 3 (by decide) (by decide)
  have hg24 := hgap 2 4 (by decide) (by decide); have hg14 := hgap 1 4 (by decide) (by decide); have hg04 := hgap 0 4 (by decide) (by decide)
  have hg25 := hgap 2 5 (by decide) (by decide); have hg15 := hgap 1 5 (by decide) (by decide); have hg05 := hgap 0 5 (by decide) (by decide)
  have hg26 := hgap 2 6 (by decide) (by decide); have hg16 := hgap 1 6 (by decide) (by decide); have hg06 := hgap 0 6 (by decide) (by decide)
  have hg27 := hgap 2 7 (by decide) (by decide); have hg17 := hgap 1 7 (by decide) (by decide); have hg28 := hgap 2 8 (by decide) (by decide)
  have hg58 := hgap 5 8 (by decide) (by decide); have hg48 := hgap 4 8 (by decide) (by decide); have hg38 := hgap 3 8 (by decide) (by decide)
  norm_num [gBound] at hg13 hg03 hg24 hg14 hg04 hg25 hg15 hg05 hg26 hg16 hg06 hg27 hg17 hg28 hg58 hg48 hg38
  let h3 := nmin (Nat.sub (a 2) (nmax 1 Gin)) (nmin (Nat.sub (a 1) 2) (Nat.sub (a 0) 4))
  let h4 := nmin (Nat.sub h3 (nmax 1 G)) (nmin (Nat.sub (a 2) 2) (nmin (Nat.sub (a 1) 4) (Nat.sub (a 0) 7)))
  let h5 := nmin (Nat.sub h4 (nmax 1 G)) (nmin (Nat.sub (a 2) 4) (nmin (Nat.sub (a 1) 7) (Nat.sub (a 0) 13)))
  let h6 := nmin (Nat.sub h5 (nmax 1 G)) (nmin (Nat.sub (a 2) 7) (nmin (Nat.sub (a 1) 13) (Nat.sub (a 0) 22)))
  let h7 := nmin (Nat.sub h6 (nmax 1 G)) (nmin (Nat.sub (a 2) 13) (Nat.sub (a 1) 22))
  let h8 := nmin (Nat.sub h7 (nmax 1 G)) (Nat.sub (a 2) 22)
  let l8 := nmax 1 G
  let l7 := nmax (nmax 2 (Nat.mul 2 G)) (Nat.add l8 (nmax 1 G))
  let l6 := nmax (nmax 4 (Nat.mul 4 G)) (Nat.add l7 (nmax 1 G))
  let l5 := nmax 5 (Nat.add l6 (nmax 1 G))
  let l4 := nmax 8 (Nat.add l5 (nmax 1 G))
  let l3 := nmax 14 (Nat.add l4 (nmax 1 G))
  have ha3_h : a 3 ≤ h3 := by dsimp [h3]; simp only [nmin_eq, nmax_eq]; omega
  have ha4_h : a 4 ≤ h4 := by dsimp [h4]; simp only [nmin_eq, nmax_eq]; omega
  have ha5_h : a 5 ≤ h5 := by dsimp [h5]; simp only [nmin_eq, nmax_eq]; omega
  have ha6_h : a 6 ≤ h6 := by dsimp [h6]; simp only [nmin_eq, nmax_eq]; omega
  have ha7_h : a 7 ≤ h7 := by dsimp [h7]; simp only [nmin_eq, nmax_eq]; omega
  have ha8_h : a 8 ≤ h8 := by dsimp [h8]; simp only [nmin_eq, nmax_eq]; omega
  have ha8_l : l8 ≤ a 8 := by dsimp [l8]; simp only [nmax_eq]; omega
  have ha7_l : l7 ≤ a 7 := by dsimp [l7]; simp only [nmax_eq]; omega
  have ha6_l : l6 ≤ a 6 := by dsimp [l6]; simp only [nmax_eq]; omega
  have ha5_l : l5 ≤ a 5 := by dsimp [l5]; simp only [nmax_eq]; omega
  have ha4_l : l4 ≤ a 4 := by dsimp [l4]; simp only [nmax_eq]; omega
  have ha3_l : l3 ≤ a 3 := by dsimp [l3]; simp only [nmax_eq]; omega
  have hmom3 := tailGap_sum_and_sq (by omega) hG
  have hT3_eq : (univ : Finset (Fin 9)).filter (fun i => 3 ≤ i.val) = {3, 4, 5, 6, 7, 8} := by decide
  have h38_sum : 63 * G ≤ a 3 + a 4 + a 5 + a 6 + a 7 + a 8 := by
    have h1 := hmom3.1; rw [hT3_eq] at h1; simp at h1; omega
  have hS_split : ∑ i : Fin 9, a i = sum3 + (a 3 + a 4 + a 5 + a 6 + a 7 + a 8) := by
    rw [hsum3]; simp [Fin.sum_univ_succ, add_assoc]
  have hQ_split : ∑ i : Fin 9, a i ^ 2 = sq3 + (a 3 ^ 2 + a 4 ^ 2 + a 5 ^ 2 + a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2) := by
    rw [hsq3]; simp [Fin.sum_univ_succ, add_assoc]
  let Tlo := nmax (Nat.sub 511 sum3) (Nat.mul 63 G)
  let Thi := nmin (Nat.add h3 (Nat.add h4 (Nat.add h5 (Nat.add h6 (Nat.add h7 h8)))))
                  (Nat.sub (Nat.add sum3 (Nat.add h3 (Nat.add h4 h5))) 83)
  have hTlo : Tlo ≤ a 3 + a 4 + a 5 + a 6 + a 7 + a 8 := by dsimp [Tlo]; rw [nmax_eq]; omega
  have hThi : a 3 + a 4 + a 5 + a 6 + a 7 + a 8 ≤ Thi := by dsimp [Thi]; rw [nmin_eq]; omega
  have hok_cur : okSQ qlb (Nat.add sum3 Tlo)
      (Nat.add sq3 (Nat.add (Nat.mul h3 h3) (Nat.add (Nat.mul h4 h4) (Nat.add (Nat.mul h5 h5) (Nat.add (Nat.mul h6 h6) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8))))))) = true :=
    okSQ_mono (by change sum3 + Tlo ≤ _; rw [hS_split]; omega)
      (by rw [hQ_split]; change sq3 + (a 3 ^ 2 + a 4 ^ 2 + a 5 ^ 2 + a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2) ≤ sq3 + (h3 * h3 + (h4 * h4 + (h5 * h5 + (h6 * h6 + (h7 * h7 + h8 * h8)))))
          have s3 := sq_le_mul_of_le ha3_h; have s4 := sq_le_mul_of_le ha4_h; have s5 := sq_le_mul_of_le ha5_h
          have s6 := sq_le_mul_of_le ha6_h; have s7 := sq_le_mul_of_le ha7_h; have s8 := sq_le_mul_of_le ha8_h; omega)
      hok_full
  change (if Nat.blt h3 l3 = true then true else
    if Nat.blt Thi Tlo = true then true else
    if not (okSQ qlb (Nat.add sum3 Tlo) (Nat.add sq3 (Nat.add (Nat.mul h3 h3) (Nat.add (Nat.mul h4 h4) (Nat.add (Nat.mul h5 h5) (Nat.add (Nat.mul h6 h6) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8)))))))) = true then true else
    loopK3 qlb (a 0) (a 1) (a 2) sum3 sq3 (kronR 3 (by omega) a) R3pos G (Nat.add (Nat.sub h3 l3) 1) h3) = false
  simp only [blt_false_of_le (le_trans ha3_l ha3_h), blt_false_of_le (le_trans hTlo hThi), hok_cur, Bool.not_true, Bool.false_eq_true, ite_false]
  exact loopK3_false ha ha1 hinj hgap hspan hS511 hok_full hG hsum3 hsq3
    (Nat.add (Nat.sub h3 l3) 1) h3 ha3_h (by change h3 < a 3 + (h3 - l3 + 1); omega)

private lemma loopK2_false {qlb sum2 sq2 G : ℕ} {a : Fin 9 → ℕ}
    (ha : StrictAnti a) (ha1 : ∀ i, 1 ≤ a i)
    (hinj : Function.Injective (fun U : Finset (Fin 9) => ∑ i ∈ U, a i))
    (hgap : ∀ i j : Fin 9, i ≤ j → j.val - i.val ≤ 6 → a j + gBound (j.val - i.val) ≤ a i)
    (hspan : (a 5 + a 6 + a 7 + a 8 + 125 ≤ a 0 + a 1 + a 2 + a 3) ∧
             (a 5 + a 6 + a 7 + a 8 + 251 ≤ a 0 + a 1 + a 2 + a 3 + a 4) ∧
             (a 6 + a 7 + a 8 + 83 ≤ a 0 + a 1 + a 2) ∧
             (a 6 + a 7 + a 8 + 335 ≤ a 0 + a 1 + a 2 + a 3 + a 4) ∧
             (a 6 + a 7 + a 8 + 419 ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5))
    (hS511 : 511 ≤ ∑ i : Fin 9, a i)
    (hok_full : okSQ qlb (∑ i : Fin 9, a i) (∑ i : Fin 9, a i ^ 2) = true)
    (hG : TailGap 2 G a)
    (hsum2 : sum2 = a 0 + a 1) (hsq2 : sq2 = a 0 ^ 2 + a 1 ^ 2) :
    let R2 := kronR 2 (by omega) a
    let R2pos := Nat.div R2 (Nat.pow 256 sum2)
    ∀ (fuel cur : ℕ), a 2 ≤ cur → cur < a 2 + fuel →
      loopK2 qlb (a 0) (a 1) sum2 sq2 R2 R2pos G fuel cur = false := by
  intro R2 R2pos fuel
  have hsum2_fin : ∑ i : Fin 2, a ⟨i.val, by omega⟩ = sum2 := by rw [hsum2]; simp [Fin.sum_univ_succ]
  have hR2pos_eq : R2pos = kronR 2 (by omega) a / 256 ^ (∑ i : Fin 2, a ⟨i.val, by omega⟩) := by
    dsimp [R2pos, R2]; rw [hsum2_fin]; rfl
  have hg13 := hgap 1 3 (by decide) (by decide); have hg03 := hgap 0 3 (by decide) (by decide)
  have hg14 := hgap 1 4 (by decide) (by decide); have hg04 := hgap 0 4 (by decide) (by decide)
  have hg15 := hgap 1 5 (by decide) (by decide); have hg05 := hgap 0 5 (by decide) (by decide)
  have hg16 := hgap 1 6 (by decide) (by decide); have hg06 := hgap 0 6 (by decide) (by decide)
  have hg17 := hgap 1 7 (by decide) (by decide); have hg28 := hgap 2 8 (by decide) (by decide)
  norm_num [gBound] at hg13 hg03 hg14 hg04 hg15 hg05 hg16 hg06 hg17 hg28
  have ha23 : a 3 < a 2 := ha (by decide); have ha34 : a 4 < a 3 := ha (by decide)
  have ha45 : a 5 < a 4 := ha (by decide); have ha56 : a 6 < a 5 := ha (by decide)
  have ha67 : a 7 < a 6 := ha (by decide); have ha78 : a 8 < a 7 := ha (by decide)
  have hQ_split : ∑ i : Fin 9, a i ^ 2 = sq2 + a 2 ^ 2 + (a 3 ^ 2 + a 4 ^ 2 + a 5 ^ 2 + a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2) := by
    rw [hsq2]; simp [Fin.sum_univ_succ, add_assoc]
  have hok_u := okSQ_iff.mp hok_full
  induction fuel with
  | zero => intro cur h1 h2; omega
  | succ fuel ih =>
    intro cur hle hlt
    unfold loopK2; dsimp only
    let h3 := nmin (Nat.sub cur 1) (nmin (Nat.sub (a 1) 2) (Nat.sub (a 0) 4))
    let h4 := nmin (Nat.sub h3 1) (nmin (Nat.sub (a 1) 4) (Nat.sub (a 0) 7))
    let h5 := nmin (Nat.sub h4 1) (nmin (Nat.sub (a 1) 7) (Nat.sub (a 0) 13))
    let h6 := nmin (Nat.sub h5 1) (nmin (Nat.sub (a 1) 13) (Nat.sub (a 0) 22))
    let h7 := nmin (Nat.sub h6 1) (Nat.sub (a 1) 22)
    let h8 := nmin (Nat.sub h7 1) (Nat.sub cur 22)
    have ha3_h : a 3 ≤ h3 := by dsimp [h3]; simp only [nmin_eq]; omega
    have ha4_h : a 4 ≤ h4 := by dsimp [h4]; simp only [nmin_eq]; omega
    have ha5_h : a 5 ≤ h5 := by dsimp [h5]; simp only [nmin_eq]; omega
    have ha6_h : a 6 ≤ h6 := by dsimp [h6]; simp only [nmin_eq]; omega
    have ha7_h : a 7 ≤ h7 := by dsimp [h7]; simp only [nmin_eq]; omega
    have ha8_h : a 8 ≤ h8 := by dsimp [h8]; simp only [nmin_eq]; omega
    have hmaxQ_ge : qlb ≤ Nat.add (Nat.add sq2 (Nat.mul cur cur)) (Nat.add (Nat.mul h3 h3) (Nat.add (Nat.mul h4 h4) (Nat.add (Nat.mul h5 h5) (Nat.add (Nat.mul h6 h6) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8)))))) := by
      have h1 := hok_u.1; rw [hQ_split] at h1
      change qlb ≤ sq2 + cur * cur + (h3 * h3 + (h4 * h4 + (h5 * h5 + (h6 * h6 + (h7 * h7 + h8 * h8)))))
      have s2 := sq_le_mul_of_le hle; have s3 := sq_le_mul_of_le ha3_h; have s4 := sq_le_mul_of_le ha4_h
      have s5 := sq_le_mul_of_le ha5_h; have s6 := sq_le_mul_of_le ha6_h; have s7 := sq_le_mul_of_le ha7_h
      have s8 := sq_le_mul_of_le ha8_h; omega
    have hnot_mQ : Nat.blt (Nat.add (Nat.add sq2 (Nat.mul cur cur)) (Nat.add (Nat.mul h3 h3) (Nat.add (Nat.mul h4 h4) (Nat.add (Nat.mul h5 h5) (Nat.add (Nat.mul h6 h6) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8))))))) qlb = false :=
      blt_false_of_le hmaxQ_ge
    dsimp only [h3, h4, h5, h6, h7, h8] at hnot_mQ
    simp only [hnot_mQ, Bool.false_eq_true, ite_false]
    by_cases hEq : cur = a 2
    · subst hEq
      have htp2 : testPos R2pos (a 2) = false := by
        rw [hR2pos_eq]; simpa using tail_diff_not_testPos (k := 2) (by omega) hinj (U := {2}) (V := ∅) (by decide)
          (by intro i hi; simp at hi; subst hi; omega) (by simp) (by simp)
      have hk3 := solveK3_false ha ha1 hinj hgap hspan hS511 hok_full hG
        (show Nat.add sum2 (a 2) = a 0 + a 1 + a 2 by rw [hsum2]; rfl)
        (show Nat.add sq2 (Nat.mul (a 2) (a 2)) = a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 by change sq2 + a 2 * a 2 = _; rw [hsq2]; ring)
      have hR3 : updR R2 (a 2) = kronR 3 (by omega) a := (kronR_succ (k := 2) (by omega) a).symm
      rw [← hR3] at hk3
      simp only [htp2, Bool.false_eq_true, ite_false, hk3]
    · have hrec := ih (Nat.sub cur 1) (by change a 2 ≤ cur - 1; omega) (by change cur - 1 < a 2 + fuel; omega)
      split_ifs <;> try exact hrec
      all_goals rfl

private lemma loopK1_false {qlb : ℕ} {a : Fin 9 → ℕ}
    (ha : StrictAnti a) (ha1 : ∀ i, 1 ≤ a i)
    (hinj : Function.Injective (fun U : Finset (Fin 9) => ∑ i ∈ U, a i))
    (hgap : ∀ i j : Fin 9, i ≤ j → j.val - i.val ≤ 6 → a j + gBound (j.val - i.val) ≤ a i)
    (hspan : (a 5 + a 6 + a 7 + a 8 + 125 ≤ a 0 + a 1 + a 2 + a 3) ∧
             (a 5 + a 6 + a 7 + a 8 + 251 ≤ a 0 + a 1 + a 2 + a 3 + a 4) ∧
             (a 6 + a 7 + a 8 + 83 ≤ a 0 + a 1 + a 2) ∧
             (a 6 + a 7 + a 8 + 335 ≤ a 0 + a 1 + a 2 + a 3 + a 4) ∧
             (a 6 + a 7 + a 8 + 419 ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5))
    (hS511 : 511 ≤ ∑ i : Fin 9, a i)
    (hok_full : okSQ qlb (∑ i : Fin 9, a i) (∑ i : Fin 9, a i ^ 2) = true) :
    ∀ (fuel cur : ℕ), a 1 ≤ cur → cur < a 1 + fuel →
      loopK1 qlb (a 0) (kronR 1 (by omega) a) fuel cur = false := by
  intro fuel
  have hg02 := hgap 0 2 (by decide) (by decide); have hg03 := hgap 0 3 (by decide) (by decide)
  have hg04 := hgap 0 4 (by decide) (by decide); have hg05 := hgap 0 5 (by decide) (by decide)
  have hg06 := hgap 0 6 (by decide) (by decide); have hg17 := hgap 1 7 (by decide) (by decide)
  have hg28 := hgap 2 8 (by decide) (by decide)
  norm_num [gBound] at hg02 hg03 hg04 hg05 hg06 hg17 hg28
  have ha12 : a 2 < a 1 := ha (by decide); have ha23 : a 3 < a 2 := ha (by decide)
  have ha34 : a 4 < a 3 := ha (by decide); have ha45 : a 5 < a 4 := ha (by decide)
  have ha56 : a 6 < a 5 := ha (by decide); have ha67 : a 7 < a 6 := ha (by decide)
  have ha78 : a 8 < a 7 := ha (by decide); have h8ge : 1 ≤ a 8 := ha1 8
  have hQ_split : ∑ i : Fin 9, a i ^ 2 = a 0 ^ 2 + a 1 ^ 2 + (a 2 ^ 2 + a 3 ^ 2 + a 4 ^ 2 + a 5 ^ 2 + a 6 ^ 2 + a 7 ^ 2 + a 8 ^ 2) := by
    simp [Fin.sum_univ_succ, add_assoc]
  have hok_u := okSQ_iff.mp hok_full
  induction fuel with
  | zero => intro cur h1 h2; omega
  | succ fuel ih =>
    intro cur hle hlt
    unfold loopK1; dsimp only
    let h2 := nmin (Nat.sub cur 1) (Nat.sub (a 0) 2)
    let h3 := nmin (Nat.sub h2 1) (Nat.sub (a 0) 4)
    let h4 := nmin (Nat.sub h3 1) (Nat.sub (a 0) 7)
    let h5 := nmin (Nat.sub h4 1) (Nat.sub (a 0) 13)
    let h6 := nmin (Nat.sub h5 1) (Nat.sub (a 0) 22)
    let h7 := nmin (Nat.sub h6 1) (Nat.sub cur 22)
    let h8 := Nat.sub h7 1
    have ha2_h : a 2 ≤ h2 := by dsimp [h2]; simp only [nmin_eq]; omega
    have ha3_h : a 3 ≤ h3 := by dsimp [h3]; simp only [nmin_eq]; omega
    have ha4_h : a 4 ≤ h4 := by dsimp [h4]; simp only [nmin_eq]; omega
    have ha5_h : a 5 ≤ h5 := by dsimp [h5]; simp only [nmin_eq]; omega
    have ha6_h : a 6 ≤ h6 := by dsimp [h6]; simp only [nmin_eq]; omega
    have ha7_h : a 7 ≤ h7 := by dsimp [h7]; simp only [nmin_eq]; omega
    have ha8_h : a 8 ≤ h8 := by dsimp [h8]; omega
    have hmaxQ_ge : qlb ≤ Nat.add (Nat.add (Nat.mul (a 0) (a 0)) (Nat.mul cur cur)) (Nat.add (Nat.mul h2 h2) (Nat.add (Nat.mul h3 h3) (Nat.add (Nat.mul h4 h4) (Nat.add (Nat.mul h5 h5) (Nat.add (Nat.mul h6 h6) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8))))))) := by
      have h1 := hok_u.1; rw [hQ_split] at h1
      change qlb ≤ a 0 * a 0 + cur * cur + (h2 * h2 + (h3 * h3 + (h4 * h4 + (h5 * h5 + (h6 * h6 + (h7 * h7 + h8 * h8))))))
      have s0 : a 0 ^ 2 = a 0 * a 0 := sq _; have s1 := sq_le_mul_of_le hle; have s2 := sq_le_mul_of_le ha2_h
      have s3 := sq_le_mul_of_le ha3_h; have s4 := sq_le_mul_of_le ha4_h; have s5 := sq_le_mul_of_le ha5_h
      have s6 := sq_le_mul_of_le ha6_h; have s7 := sq_le_mul_of_le ha7_h; have s8 := sq_le_mul_of_le ha8_h; omega
    have hnot_mQ : Nat.blt (Nat.add (Nat.add (Nat.mul (a 0) (a 0)) (Nat.mul cur cur)) (Nat.add (Nat.mul h2 h2) (Nat.add (Nat.mul h3 h3) (Nat.add (Nat.mul h4 h4) (Nat.add (Nat.mul h5 h5) (Nat.add (Nat.mul h6 h6) (Nat.add (Nat.mul h7 h7) (Nat.mul h8 h8)))))))) qlb = false :=
      blt_false_of_le hmaxQ_ge
    dsimp only [h2, h3, h4, h5, h6, h7, h8] at hnot_mQ
    simp only [hnot_mQ, Bool.false_eq_true, ite_false]
    by_cases hEq : cur = a 1
    · subst hEq
      have ha2_l : 23 ≤ a 2 := by omega
      have hnot_h2 : Nat.blt h2 23 = false := blt_false_of_le (le_trans ha2_l ha2_h)
      let R2 := updR (kronR 1 (by omega) a) (a 1)
      have hR2 : R2 = kronR 2 (by omega) a := (kronR_succ (k := 1) (by omega) a).symm
      let sum2 := Nat.add (a 0) (a 1)
      let R2pos := Nat.div R2 (Nat.pow 256 sum2)
      have hsum2_fin : ∑ i : Fin 2, a ⟨i.val, by omega⟩ = sum2 := by dsimp [sum2]; simp [Fin.sum_univ_succ]
      have hG2 : TailGap 2 (findG R2pos 1) a := by
        have hEqPos : R2pos = kronR 2 (by omega) a / 256 ^ (∑ i : Fin 2, a ⟨i.val, by omega⟩) := by
          dsimp [R2pos]; rw [hR2, hsum2_fin]; rfl
        rw [hEqPos]; exact findG_tailGap (k := 2) (by omega) hinj (tailGap_of_inj hinj)
      have hk2 := loopK2_false ha ha1 hinj hgap hspan hS511 hok_full hG2
        (show sum2 = a 0 + a 1 from rfl)
        (show Nat.add (Nat.mul (a 0) (a 0)) (Nat.mul (a 1) (a 1)) = a 0 ^ 2 + a 1 ^ 2 by change a 0 * a 0 + a 1 * a 1 = _; ring)
        (Nat.add (Nat.sub h2 23) 1) h2 ha2_h (by change h2 < a 2 + (h2 - 23 + 1); omega)
      rw [← hR2] at hk2
      change (if (if Nat.blt h2 23 = true then true else loopK2 qlb (a 0) (a 1) sum2 (Nat.add (Nat.mul (a 0) (a 0)) (Nat.mul (a 1) (a 1))) R2 (Nat.div R2 (Nat.pow 256 sum2)) (findG R2pos 1) (Nat.add (Nat.sub h2 23) 1) h2) = true then _ else false) = false
      simp only [hnot_h2, Bool.false_eq_true, ite_false, hk2]
    · have hrec := ih (Nat.sub cur 1) (by change a 1 ≤ cur - 1; omega) (by change cur - 1 < a 1 + fuel; omega)
      split_ifs <;> try exact hrec
      all_goals rfl

private lemma solveA0_sound {a0 qlb : ℕ} (hsolve : solveA0 a0 qlb = true)
    {a : Fin 9 → ℕ} (ha : StrictAnti a) (ha1 : ∀ i, 1 ≤ a i)
    (hinj : Function.Injective (fun U : Finset (Fin 9) => ∑ i ∈ U, a i))
    (hgap : ∀ i j : Fin 9, i ≤ j → j.val - i.val ≤ 6 → a j + gBound (j.val - i.val) ≤ a i)
    (hspan : (a 5 + a 6 + a 7 + a 8 + 125 ≤ a 0 + a 1 + a 2 + a 3) ∧
             (a 5 + a 6 + a 7 + a 8 + 251 ≤ a 0 + a 1 + a 2 + a 3 + a 4) ∧
             (a 6 + a 7 + a 8 + 83 ≤ a 0 + a 1 + a 2) ∧
             (a 6 + a 7 + a 8 + 335 ≤ a 0 + a 1 + a 2 + a 3 + a 4) ∧
             (a 6 + a 7 + a 8 + 419 ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5))
    (hmom : 22108415 + (∑ i : Fin 9, a i) ^ 2 ≤ 256 * (∑ i : Fin 9, a i ^ 2) ∧
            9924583 + 3 * (∑ i : Fin 9, a i) ^ 2 ≤ 126 * (∑ i : Fin 9, a i ^ 2) ∧
            881995 + (∑ i : Fin 9, a i) ^ 2 ≤ 16 * (∑ i : Fin 9, a i ^ 2) ∧
            190509 + (∑ i : Fin 9, a i) ^ 2 ≤ 10 * (∑ i : Fin 9, a i ^ 2) ∧
            42863 + (∑ i : Fin 9, a i) ^ 2 ≤ 9 * (∑ i : Fin 9, a i ^ 2))
    (hS511 : 511 ≤ ∑ i : Fin 9, a i) (hQlb : qlb ≤ ∑ i : Fin 9, a i ^ 2)
    (ha0 : a 0 = a0) : False := by
  subst ha0
  have hok_full : okSQ qlb (∑ i : Fin 9, a i) (∑ i : Fin 9, a i ^ 2) = true :=
    okSQ_iff.mpr ⟨hQlb, hmom.2.2.2.2, hmom.2.2.2.1, hmom.2.2.1, hmom.2.1, hmom.1⟩
  have hg28 := hgap 2 8 (by decide) (by decide); norm_num [gBound] at hg28
  have ha01 : a 1 < a 0 := ha (by decide); have ha12 : a 2 < a 1 := ha (by decide); have h8ge := ha1 8
  have ha1_l : 24 ≤ a 1 := by omega
  have ha1_h : a 1 ≤ a 0 - 1 := by omega
  have hR1 : updR 1 (a 0) = kronR 1 (by omega) a := by
    have h1 := kronR_succ (k := 0) (by omega) a
    rw [kronR_zero] at h1
    exact h1.symm
  have hfalse : solveA0 (a 0) qlb = false := by
    unfold solveA0; dsimp only
    simp only [blt_false_of_le (show 24 ≤ Nat.sub (a 0) 1 from le_trans ha1_l ha1_h), Bool.false_eq_true, ite_false]
    rw [hR1]
    exact loopK1_false ha ha1 hinj hgap hspan hS511 hok_full (Nat.add (Nat.sub (Nat.sub (a 0) 1) 24) 1)
      (Nat.sub (a 0) 1) ha1_h (by change a 0 - 1 < a 1 + (a 0 - 1 - 24 + 1); omega)
  rw [hsolve] at hfalse; cases hfalse


private lemma ok_138 : solveA0 138 135501 = true := by decide +kernel
private lemma ok_139 : solveA0 139 135301 = true := by decide +kernel
private lemma ok_140 : solveA0 140 135001 = true := by decide +kernel

/-- Maxima in `[141..149]` with raised second-moment bound `sum x^2 >= 132801`. -/
def H1 : Prop :=
  ∀ A : Finset ℕ, A ⊆ Icc 1 149 → (∃ x ∈ A, 141 ≤ x) → A.card = 9 →
    132801 ≤ (∑ x ∈ A, x ^ 2) → 511 ≤ A.sum id →
      ∃ S ⊆ A, ∃ T ⊆ A, S ≠ T ∧ S.sum id = T.sum id

/-- Maximum equal to `150` with raised second-moment bound `sum x^2 >= 132501`. -/
def H2 : Prop :=
  ∀ A : Finset ℕ, A ⊆ Icc 1 150 → 150 ∈ A → A.card = 9 →
    132501 ≤ (∑ x ∈ A, x ^ 2) → 511 ≤ A.sum id →
      ∃ S ⊆ A, ∃ T ⊆ A, S ≠ T ∧ S.sum id = T.sum id

/-- Maximum equal to `151` with `149` or `150` also present and `sum x^2 >= 132151`. -/
def H3 : Prop :=
  ∀ A : Finset ℕ, A ⊆ Icc 1 151 → 151 ∈ A → (149 ∈ A ∨ 150 ∈ A) → A.card = 9 →
    132151 ≤ (∑ x ∈ A, x ^ 2) → 511 ≤ A.sum id →
      ∃ S ⊆ A, ∃ T ⊆ A, S ≠ T ∧ S.sum id = T.sum id

/-- Maximum equal to `151` with neither `149` nor `150` present and `sum x^2 >= 132151`. -/
def H4 : Prop :=
  ∀ A : Finset ℕ, A ⊆ Icc 1 151 → 151 ∈ A → 149 ∉ A → 150 ∉ A → A.card = 9 →
    132151 ≤ (∑ x ∈ A, x ^ 2) → 511 ≤ A.sum id →
      ∃ S ⊆ A, ∃ T ⊆ A, S ≠ T ∧ S.sum id = T.sum id

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos1_erdos_1_variants_least_N_9_R2.H1 := by
  intro h1 h2 h3 h4 A hA h103 hcard hQ hS
  by_contra hno
  obtain ⟨a, ha, ha_mem, ha_bnd, _, hQa, hSa, _, hQ_eq, hinj⟩ :=
    extract_sorted_tuple hA h103 hcard hQ hS hno
  have hImg_eq : (univ : Finset (Fin 9)).image a = A := by
    apply eq_of_subset_of_card_le
    · intro x hx
      rcases mem_image.mp hx with ⟨i, _, rfl⟩
      exact ha_mem i
    · rw [card_image_of_injective _ ha.injective, card_univ, Fintype.card_fin, hcard]
  have hA_le_a0 : ∀ x ∈ A, x ≤ a 0 := by
    intro x hx
    rw [← hImg_eq] at hx
    rcases mem_image.mp hx with ⟨i, _, rfl⟩
    exact ha.antitone (Fin.zero_le i)
  have hA_sub_of : ∀ M : ℕ, a 0 ≤ M → A ⊆ Icc 1 M := fun M hM x hx =>
    mem_Icc.mpr ⟨(mem_Icc.mp (hA hx)).1, le_trans (hA_le_a0 x hx) hM⟩
  have ha0_151 : a 0 ≤ 151 := (ha_bnd 0).2
  have hQ129 : 129001 ≤ ∑ i : Fin 9, a i ^ 2 :=
    elkies_cert_sound cert151a certMeta_151a ok_151a ha hinj ha0_151 hQa
  have hQ151 : 132151 ≤ ∑ i : Fin 9, a i ^ 2 :=
    elkies_cert_sound cert151b certMeta_151b ok_151b ha hinj ha0_151 hQ129
  by_cases ha151 : a 0 = 151
  · have h151_mem : 151 ∈ A := ha151 ▸ ha_mem 0
    by_cases h149_150 : 149 ∈ A ∨ 150 ∈ A
    · exact hno (h3 A hA h151_mem h149_150 hcard (hQ_eq ▸ hQ151) hS)
    · push Not at h149_150
      exact hno (h4 A hA h151_mem h149_150.1 h149_150.2 hcard (hQ_eq ▸ hQ151) hS)
  · have ha0_150 : a 0 ≤ 150 := by omega
    have hQ150 : 132501 ≤ ∑ i : Fin 9, a i ^ 2 :=
      elkies_cert_sound cert150b certMeta_150b ok_150b ha hinj ha0_150 hQ151
    by_cases ha150 : a 0 = 150
    · exact hno (h2 A (hA_sub_of 150 ha0_150) (ha150 ▸ ha_mem 0) hcard (hQ_eq ▸ hQ150) hS)
    · have ha0_149 : a 0 ≤ 149 := by omega
      have hQ149 : 132801 ≤ ∑ i : Fin 9, a i ^ 2 :=
        elkies_cert_sound cert149b certMeta_149b ok_149b ha hinj ha0_149 hQ150
      by_cases ha141 : 141 ≤ a 0
      · exact hno (h1 A (hA_sub_of 149 ha0_149) ⟨a 0, ha_mem 0, ha141⟩ hcard (hQ_eq ▸ hQ149) hS)
      · have ha0_140 : a 0 ≤ 140 := by omega
        have hQ147 : 133301 ≤ ∑ i : Fin 9, a i ^ 2 :=
          elkies_cert_sound cert147b certMeta_147b ok_147b ha hinj (le_trans ha0_140 (by decide)) hQ149
        have hQ146 : 133501 ≤ ∑ i : Fin 9, a i ^ 2 :=
          elkies_cert_sound cert146b certMeta_146b ok_146b ha hinj (le_trans ha0_140 (by decide)) hQ147
        have hQ145 : 133751 ≤ ∑ i : Fin 9, a i ^ 2 :=
          elkies_cert_sound cert145b certMeta_145b ok_145b ha hinj (le_trans ha0_140 (by decide)) hQ146
        have hQ144 : 133951 ≤ ∑ i : Fin 9, a i ^ 2 :=
          elkies_cert_sound cert144b certMeta_144b ok_144b ha hinj (le_trans ha0_140 (by decide)) hQ145
        have hQ143 : 134201 ≤ ∑ i : Fin 9, a i ^ 2 :=
          elkies_cert_sound cert143b certMeta_143b ok_143b ha hinj (le_trans ha0_140 (by decide)) hQ144
        have hQ142 : 134451 ≤ ∑ i : Fin 9, a i ^ 2 :=
          elkies_cert_sound cert142b certMeta_142b ok_142b ha hinj (le_trans ha0_140 (by decide)) hQ143
        have hQ141 : 134701 ≤ ∑ i : Fin 9, a i ^ 2 :=
          elkies_cert_sound cert141b certMeta_141b ok_141b ha hinj (le_trans ha0_140 (by decide)) hQ142
        have hQ140 : 135001 ≤ ∑ i : Fin 9, a i ^ 2 :=
          elkies_cert_sound cert140b certMeta_140b ok_140b ha hinj ha0_140 hQ141
        have ha1 : ∀ i : Fin 9, 1 ≤ a i := fun i => (ha_bnd i).1
        have hgap := a_gap_g6 ha hinj
        have hspan := five_layer_spans ha hinj
        have hmom := five_layer_moments hinj
        by_cases ha140 : a 0 = 140
        · exact solveA0_sound ok_140 ha ha1 hinj hgap hspan hmom hSa hQ140 ha140
        · have ha0_139 : a 0 ≤ 139 := by omega
          have hQ139 : 135301 ≤ ∑ i : Fin 9, a i ^ 2 :=
            elkies_cert_sound cert139b certMeta_139b ok_139b ha hinj ha0_139 hQ140
          by_cases ha139 : a 0 = 139
          · exact solveA0_sound ok_139 ha ha1 hinj hgap hspan hmom hSa hQ139 ha139
          · have ha0_138 : a 0 ≤ 138 := by omega
            have hQ138 : 135501 ≤ ∑ i : Fin 9, a i ^ 2 :=
              elkies_cert_sound cert138b certMeta_138b ok_138b ha hinj ha0_138 hQ139
            by_cases ha138 : a 0 = 138
            · exact solveA0_sound ok_138 ha ha1 hinj hgap hspan hmom hSa hQ138 ha138
            · have hge := a0_ge_138 ha hinj hQ138
              omega

end OMA.R_Erdos1_erdos_1_variants_least_N_9_R2_H1_R1
