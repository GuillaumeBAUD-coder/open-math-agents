import OMAStatements.S_oeis_a183905
import Mathlib

/-! Proof for OEIS A183905: a nondecreasing arrangement s of N = n + 2 numbers in 0..2 is
determined by u = the number of zeros and w = the number of entries at most 1, via
s x = 0 for x < u, 1 for u <= x < w, 2 otherwise; this gives a bijection with the pairs
u <= w <= N. With block sizes c0 = u, c1 = w - u, c2 = N - w, the arrangement is good iff
(c0 >= 1 implies c0 >= 3 or c1, c2 >= 1), (c1 >= 1 implies c0 >= 1 and c1 >= 2, or c2 >= 2),
(c2 >= 1 implies c0 >= 1 and c2 >= 2, or c1 >= 2), proved with explicit witness positions.
For N >= 4 exactly 11 pairs fail this, so a(n) = (n + 3)(n + 4)/2 - 11 for n >= 2; the
recurrence follows by algebra and the cleared generating function by comparing coefficients.
Credit: Sudharsan Rajendiran -/

namespace OMA.P183905
open OMA.S_oeis_a183905 PowerSeries Finset

def g (u w x : ℕ) : ℕ := if x < u then 0 else if x < w then 1 else 2

lemma g_lt (u w x : ℕ) : g u w x < 3 := by unfold g; split_ifs <;> omega

def f (N u w : ℕ) : Fin N → Fin 3 := fun x => ⟨g u w x, g_lt u w x⟩

lemma f_val (N u w : ℕ) (x : Fin N) : ((f N u w x : Fin 3) : ℕ) = g u w x := rfl

abbrev Cond (u w N : ℕ) : Prop :=
  (1 ≤ u → 3 ≤ u ∨ (u + 1 ≤ w ∧ w + 1 ≤ N)) ∧
  (u + 1 ≤ w → (1 ≤ u ∧ u + 2 ≤ w) ∨ w + 2 ≤ N) ∧
  (w + 1 ≤ N → (1 ≤ u ∧ w + 2 ≤ N) ∨ u + 2 ≤ w)

lemma good_iff {N u w : ℕ} (huw : u ≤ w) (hwN : w ≤ N) : Good (f N u w) ↔ Cond u w N := by
  constructor
  · rintro ⟨-, h⟩
    refine ⟨fun hu => ?_, fun hu => ?_, fun hu => ?_⟩
    · obtain ⟨j, k, hj, hk, hjk, e⟩ := h ⟨0, by omega⟩
      have := j.isLt
      have := k.isLt
      have hj' : (j : ℕ) ≠ 0 := fun h' => hj (Fin.ext h')
      have hk' : (k : ℕ) ≠ 0 := fun h' => hk (Fin.ext h')
      have hjk' : (j : ℕ) ≠ k := fun h' => hjk (Fin.ext h')
      simp only [f_val, g] at e
      split_ifs at e <;> omega
    · obtain ⟨j, k, hj, hk, hjk, e⟩ := h ⟨u, by omega⟩
      have := j.isLt
      have := k.isLt
      have hj' : (j : ℕ) ≠ u := fun h' => hj (Fin.ext h')
      have hk' : (k : ℕ) ≠ u := fun h' => hk (Fin.ext h')
      have hjk' : (j : ℕ) ≠ k := fun h' => hjk (Fin.ext h')
      simp only [f_val, g] at e
      split_ifs at e <;> omega
    · obtain ⟨j, k, hj, hk, hjk, e⟩ := h ⟨w, by omega⟩
      have := j.isLt
      have := k.isLt
      have hj' : (j : ℕ) ≠ w := fun h' => hj (Fin.ext h')
      have hk' : (k : ℕ) ≠ w := fun h' => hk (Fin.ext h')
      have hjk' : (j : ℕ) ≠ k := fun h' => hjk (Fin.ext h')
      simp only [f_val, g] at e
      split_ifs at e <;> omega
  · intro hC
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [Fin.le_iff_val_le_val] at hij ⊢
      simp only [f_val, g]
      split_ifs <;> omega
    · have hi := i.isLt
      obtain ⟨h1, h2, h3⟩ := hC
      by_cases a0 : (i : ℕ) < u
      · rcases h1 (by omega) with b | b
        · refine ⟨(⟨if (i : ℕ) = 0 then 1 else 0, by split_ifs <;> omega⟩ : Fin N),
            (⟨if (i : ℕ) = 2 then 1 else 2, by split_ifs <;> omega⟩ : Fin N), ?_, ?_, ?_, ?_⟩ <;>
          simp only [ne_eq, Fin.ext_iff, f_val, g] <;> (try split_ifs) <;> first | omega | trivial
        · refine ⟨⟨u, by omega⟩, ⟨w, by omega⟩, ?_, ?_, ?_, ?_⟩ <;>
          simp only [ne_eq, Fin.ext_iff, f_val, g] <;> (try split_ifs) <;> first | omega | trivial
      by_cases a1 : (i : ℕ) < w
      · rcases h2 (by omega) with b | b
        · refine ⟨⟨0, by omega⟩, (⟨if (i : ℕ) = u then u + 1 else u, by split_ifs <;> omega⟩ : Fin N),
            ?_, ?_, ?_, ?_⟩ <;>
          simp only [ne_eq, Fin.ext_iff, f_val, g] <;> (try split_ifs) <;> first | omega | trivial
        · refine ⟨⟨w, by omega⟩, ⟨w + 1, by omega⟩, ?_, ?_, ?_, ?_⟩ <;>
          simp only [ne_eq, Fin.ext_iff, f_val, g] <;> (try split_ifs) <;> first | omega | trivial
      · rcases h3 (by omega) with b | b
        · refine ⟨⟨0, by omega⟩, (⟨if (i : ℕ) = w then w + 1 else w, by split_ifs <;> omega⟩ : Fin N),
            ?_, ?_, ?_, ?_⟩ <;>
          simp only [ne_eq, Fin.ext_iff, f_val, g] <;> (try split_ifs) <;> first | omega | trivial
        · refine ⟨⟨u, by omega⟩, ⟨u + 1, by omega⟩, ?_, ?_, ?_, ?_⟩ <;>
          simp only [ne_eq, Fin.ext_iff, f_val, g] <;> (try split_ifs) <;> first | omega | trivial

lemma down {N : ℕ} (P : Fin N → Prop) [DecidablePred P] (hP : ∀ x y, y ≤ x → P x → P y)
    (x : Fin N) : P x ↔ (x : ℕ) < #(univ.filter P) := by
  constructor
  · intro hx
    have hs : Finset.Iic x ⊆ univ.filter P := by
      intro y hy
      rw [Finset.mem_Iic] at hy
      simp [hP x y hy hx]
    have := Finset.card_le_card hs
    rw [Fin.card_Iic] at this
    omega
  · intro hx
    by_contra hn
    have hs : univ.filter P ⊆ Finset.Iio x := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      rw [Finset.mem_Iio]
      by_contra h'
      exact hn (hP y x (not_lt.mp h') hy)
    have := Finset.card_le_card hs
    rw [Fin.card_Iio] at this
    omega

lemma card_lt {N u : ℕ} (h : u ≤ N) : #(univ.filter (fun x : Fin N => (x : ℕ) < u)) = u := by
  have e : (univ.filter (fun x : Fin N => (x : ℕ) < u)).map Fin.valEmbedding = range u := by
    ext y
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, by omega⟩, hy, rfl⟩
  calc _ = #((univ.filter (fun x : Fin N => (x : ℕ) < u)).map Fin.valEmbedding) :=
        (Finset.card_map _).symm
    _ = u := by rw [e, card_range]

def A (N : ℕ) : Finset (ℕ × ℕ) :=
  ((range (N + 1)) ×ˢ (range (N + 1))).filter (fun p => p.1 ≤ p.2)

def T (N : ℕ) : Finset (ℕ × ℕ) := (A N).filter (fun p => Cond p.1 p.2 N)

lemma mono_eq {N : ℕ} (s : Fin N → Fin 3) (hs : ∀ i j, i ≤ j → s i ≤ s j) :
    f N #(univ.filter fun x => ((s x : Fin 3) : ℕ) = 0)
      #(univ.filter fun x => ((s x : Fin 3) : ℕ) ≤ 1) = s := by
  funext x
  apply Fin.ext
  rw [f_val]
  have e0 := down (fun x => ((s x : Fin 3) : ℕ) = 0) (fun x y hxy hx => by
    have := hs y x hxy
    rw [Fin.le_iff_val_le_val] at this
    omega) x
  have e1 := down (fun x => ((s x : Fin 3) : ℕ) ≤ 1) (fun x y hxy hx => by
    have := hs y x hxy
    rw [Fin.le_iff_val_le_val] at this
    omega) x
  have := (s x).isLt
  unfold g
  split_ifs with h1 h2
  · exact (e0.mpr h1).symm
  · have := e0.not.mpr h1
    have := e1.mpr h2
    omega
  · have := e0.not.mpr (by omega)
    have := e1.not.mpr h2
    omega

lemma f_counts {N u w : ℕ} (huw : u ≤ w) (hwN : w ≤ N) :
    (#(univ.filter fun x => ((f N u w x : Fin 3) : ℕ) = 0),
      #(univ.filter fun x => ((f N u w x : Fin 3) : ℕ) ≤ 1)) = (u, w) := by
  have e0 : (univ.filter fun x => ((f N u w x : Fin 3) : ℕ) = 0) =
      univ.filter (fun x : Fin N => (x : ℕ) < u) := by
    apply Finset.filter_congr
    intro x _
    rw [f_val]
    unfold g
    split_ifs <;> (try simp) <;> omega
  have e1 : (univ.filter fun x => ((f N u w x : Fin 3) : ℕ) ≤ 1) =
      univ.filter (fun x : Fin N => (x : ℕ) < w) := by
    apply Finset.filter_congr
    intro x _
    rw [f_val]
    unfold g
    split_ifs <;> (try simp) <;> omega
  rw [e0, e1, card_lt (by omega), card_lt hwN]

lemma a_eq (n : ℕ) : a n = #(T (n + 2)) := by
  unfold a
  apply Finset.card_nbij'
    (fun s => (#(univ.filter fun x => ((s x : Fin 3) : ℕ) = 0),
      #(univ.filter fun x => ((s x : Fin 3) : ℕ) ≤ 1)))
    (fun p => f (n + 2) p.1 p.2)
  · intro s hs
    rw [Finset.mem_coe] at hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    have hu : #(univ.filter fun x => ((s x : Fin 3) : ℕ) = 0) ≤
        #(univ.filter fun x => ((s x : Fin 3) : ℕ) ≤ 1) := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      omega
    have hw : #(univ.filter fun x => ((s x : Fin 3) : ℕ) ≤ 1) ≤ n + 2 := by
      have := Finset.card_filter_le (univ : Finset (Fin (n + 2)))
        (fun x => ((s x : Fin 3) : ℕ) ≤ 1)
      rw [Finset.card_univ, Fintype.card_fin] at this
      exact this
    have hg := hs
    rw [← mono_eq s hs.1] at hg
    have hC := (good_iff hu hw).mp hg
    rw [Finset.mem_coe]
    simp only [T, A, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨⟨by omega, by omega⟩, hu⟩, hC⟩
  · intro p hp
    rw [Finset.mem_coe] at hp
    simp only [T, A, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    rw [Finset.mem_coe]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (good_iff hp.1.2 (by omega)).mpr hp.2
  · intro s hs
    rw [Finset.mem_coe] at hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    exact mono_eq s hs.1
  · intro p hp
    rw [Finset.mem_coe] at hp
    simp only [T, A, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    exact f_counts hp.1.2 (by omega)

def B (M : ℕ) : Finset (ℕ × ℕ) :=
  {(0, 0), (0, 1), (0, M + 3), (0, M + 4), (1, 1), (1, M + 4), (2, 2), (2, M + 4),
    (M + 2, M + 3), (M + 3, M + 3), (M + 3, M + 4)}

lemma B_card (M : ℕ) : #(B M) = 11 := by
  unfold B
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem, Finset.card_singleton]
  all_goals simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, true_and, and_true]
  all_goals omega

lemma bad_eq (M : ℕ) : (A (M + 4)).filter (fun p => ¬ Cond p.1 p.2 (M + 4)) = B M := by
  ext ⟨u, w⟩
  simp only [A, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨⟨hu, hw⟩, huw⟩, hC⟩
    by_cases c1 : (1 ≤ u → 3 ≤ u ∨ (u + 1 ≤ w ∧ w + 1 ≤ M + 4))
    · by_cases c2 : (u + 1 ≤ w → (1 ≤ u ∧ u + 2 ≤ w) ∨ w + 2 ≤ M + 4)
      · have c3 : ¬ (w + 1 ≤ M + 4 → (1 ≤ u ∧ w + 2 ≤ M + 4) ∨ u + 2 ≤ w) :=
          fun c3 => hC ⟨c1, c2, c3⟩
        have key : (u = 0 ∧ w = 0) ∨ (u = 0 ∧ w = 1) ∨ (u = M + 3 ∧ w = M + 3) ∨
            (u = M + 2 ∧ w = M + 3) := by omega
        rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [B]
      · have key : (u = 0 ∧ w = M + 4) ∨ (u = 0 ∧ w = M + 3) ∨ (u = M + 3 ∧ w = M + 4) ∨
            (u = M + 2 ∧ w = M + 3) := by omega
        rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [B]
    · have key : (u = 1 ∧ w = 1) ∨ (u = 1 ∧ w = M + 4) ∨ (u = 2 ∧ w = 2) ∨
          (u = 2 ∧ w = M + 4) := by omega
      rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [B]
  · intro h
    simp only [B, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact ⟨⟨⟨by omega, by omega⟩, by omega⟩, fun ⟨c1, c2, c3⟩ => by omega⟩

lemma sum_succ (N : ℕ) : 2 * ∑ w ∈ range (N + 1), (w + 1) = (N + 1) * (N + 2) := by
  induction N with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, mul_add, ih]; ring

lemma A_card (N : ℕ) : 2 * #(A N) = (N + 1) * (N + 2) := by
  rw [← sum_succ N]
  congr 1
  rw [A, Finset.card_filter, Finset.sum_product_right]
  apply Finset.sum_congr rfl
  intro w hw
  rw [← Finset.card_filter]
  have : (range (N + 1)).filter (fun u => u ≤ w) = range (w + 1) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_filter] at hw ⊢
    omega
  rw [this, card_range]

lemma closed (n : ℕ) (hn : 2 ≤ n) : 2 * a n + 22 = (n + 3) * (n + 4) := by
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 2 := ⟨n - 2, by omega⟩
  rw [a_eq]
  have h1 := Finset.card_filter_add_card_filter_not (s := A (M + 4))
    (fun p => Cond p.1 p.2 (M + 4))
  rw [bad_eq, B_card] at h1
  have h2 := A_card (M + 4)
  have e : T (M + 2 + 2) = (A (M + 4)).filter (fun p => Cond p.1 p.2 (M + 4)) := rfl
  rw [e]
  nlinarith

lemma a0 : a 0 = 0 := by rw [a_eq]; decide

lemma a1 : a 1 = 1 := by rw [a_eq]; decide

lemma recur (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have e1 : m + 5 - 1 = m + 4 := by omega
  have e2 : m + 5 - 2 = m + 3 := by omega
  have e3 : m + 5 - 3 = m + 2 := by omega
  rw [e1, e2, e3]
  have h0 : (2 * a (m + 5) + 22 : ℤ) = (m + 5 + 3) * (m + 5 + 4) := by
    exact_mod_cast closed (m + 5) (by omega)
  have h1 : (2 * a (m + 4) + 22 : ℤ) = (m + 4 + 3) * (m + 4 + 4) := by
    exact_mod_cast closed (m + 4) (by omega)
  have h2 : (2 * a (m + 3) + 22 : ℤ) = (m + 3 + 3) * (m + 3 + 4) := by
    exact_mod_cast closed (m + 3) (by omega)
  have h3 : (2 * a (m + 2) + 22 : ℤ) = (m + 2 + 3) * (m + 2 + 4) := by
    exact_mod_cast closed (m + 2) (by omega)
  linarith

lemma gf : PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 : PowerSeries ℤ) =
    X * (1 + X + X ^ 2 - 2 * X ^ 3) := by
  have hD : ((1 - X) ^ 3 : PowerSeries ℤ) =
      C (1 : ℤ) * X ^ 0 + C (-3 : ℤ) * X ^ 1 + C (3 : ℤ) * X ^ 2 + C (-1 : ℤ) * X ^ 3 := by
    simp only [map_neg, map_one, map_ofNat]; ring
  have hN : (X * (1 + X + X ^ 2 - 2 * X ^ 3) : PowerSeries ℤ) =
      C (1 : ℤ) * X ^ 1 + C (1 : ℤ) * X ^ 2 + C (1 : ℤ) * X ^ 3 + C (-2 : ℤ) * X ^ 4 := by
    simp only [map_neg, map_one, map_ofNat]; ring
  rw [hD, hN]
  ext n
  simp only [mul_add, map_add, mul_left_comm _ (C _), coeff_C_mul, coeff_mul_X_pow',
    coeff_C, coeff_mk]
  have b0 := a0
  have b1 := a1
  have b2 := closed 2 le_rfl
  have b3 := closed 3 (by norm_num)
  have b4 := closed 4 (by norm_num)
  have c2 : a 2 = 4 := by omega
  have c3 : a 3 = 10 := by omega
  have c4 : a 4 = 17 := by omega
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with h | h | h | h | h | h
  · subst h; simp [b0]
  · subst h; simp [b0, b1]
  · subst h; simp [b0, b1, c2]
  · subst h; simp [b0, b1, c2, c3]
  · subst h; simp [b0, b1, c2, c3, c4]
  · have hr := recur n (by omega)
    simp only [show 0 ≤ n from Nat.zero_le _, show 1 ≤ n by omega, show 2 ≤ n by omega,
      show 3 ≤ n by omega, if_true, Nat.sub_zero, if_false, show n - 1 ≠ 0 by omega,
      show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega,
      show 4 ≤ n by omega, show n - 4 ≠ 0 by omega]
    linarith

end OMA.P183905

theorem OMA.solution : type_of% @OMA.S_oeis_a183905.main :=
  ⟨OMA.P183905.gf, OMA.P183905.recur⟩
