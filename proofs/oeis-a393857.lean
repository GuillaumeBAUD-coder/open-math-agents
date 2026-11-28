import OMAStatements.S_oeis_a393857
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a393857

open OMA.S_oeis_a393857

/-- Geometric series `x / (1 - c * x) = ∑_{n ≥ 1} c^(n - 1) * x^n`. -/
private def geom {R : Type*} [CommRing R] (c : R) (n : ℕ) : R :=
  if n = 0 then 0 else c ^ (n - 1)

private lemma powSeq_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (g : ℕ → R) :
    ∀ k n : ℕ, φ (powSeq g k n) = powSeq (fun i => φ (g i)) k n := by
  intro k
  induction k with
  | zero => intro n; dsimp [powSeq]; split_ifs <;> simp
  | succ k ih => intro n; simp only [powSeq, map_sum, map_mul, ih]

private lemma comp_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f g : ℕ → R) (n : ℕ) :
    φ (comp f g n) = comp (fun i => φ (f i)) (fun i => φ (g i)) n := by
  simp only [comp, map_sum, map_mul, powSeq_map]

private lemma powSeq_zero_of_lt {R : Type*} [CommRing R] {g : ℕ → R} (hg0 : g 0 = 0) :
    ∀ k n : ℕ, n < k → powSeq g k n = 0 := by
  intro k
  induction k with
  | zero => intro n hn; omega
  | succ k ih =>
    intro n hn
    simp only [powSeq]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases hi0 : i = 0
    · subst hi0; simp [hg0]
    · rw [ih (n - i) (by omega), mul_zero]

private lemma powSeq_diag {R : Type*} [CommRing R] {g : ℕ → R} (hg0 : g 0 = 0) :
    ∀ k : ℕ, powSeq g k k = (g 1) ^ k := by
  intro k
  induction k with
  | zero => simp [powSeq]
  | succ k ih =>
    simp only [powSeq]
    have hterm : ∀ i ∈ Finset.range (k + 2),
        g i * powSeq g k (k + 1 - i) = if i = 1 then g 1 * (g 1) ^ k else 0 := by
      intro i hi
      have hik : i ≤ k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      by_cases hi0 : i = 0
      · subst hi0; simp [hg0]
      · by_cases hi1 : i = 1
        · subst hi1; simp [ih]
        · rw [if_neg hi1, powSeq_zero_of_lt hg0 k (k + 1 - i) (by omega), mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' _ 1,
      if_pos (Finset.mem_range.mpr (by omega)), pow_succ']

private lemma powSeq_congr {R : Type*} [CommRing R] {g1 g2 : ℕ → R} {N : ℕ}
    (hg : ∀ i ≤ N, g1 i = g2 i) : ∀ k n : ℕ, n ≤ N → powSeq g1 k n = powSeq g2 k n := by
  intro k
  induction k with
  | zero => intro n _; rfl
  | succ k ih =>
    intro n hn
    simp only [powSeq]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [hg i (le_trans hin hn), ih (n - i) (by omega)]

private lemma hockey_stick (k : ℕ) :
    ∀ m : ℕ, ∑ j ∈ Finset.range (m + 1), Nat.choose (j + k) k = Nat.choose (m + k + 1) (k + 1) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : m + 1 + k = (m + k) + 1 := by omega
    rw [h1, add_comm, ← Nat.choose_succ_succ]

private lemma powSeq_geom {R : Type*} [CommRing R] (b : R) :
    ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ,
      powSeq (geom b) k n = if k ≤ n then (Nat.choose (n - 1) (k - 1) : R) * b ^ (n - k) else 0 := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · intro n
      simp only [powSeq, geom]
      by_cases hn : 1 ≤ n
      · rw [if_pos hn]
        have hterm : ∀ i ∈ Finset.range (n + 1),
            (if i = 0 then (0 : R) else b ^ (i - 1)) * (if n - i = 0 then 1 else 0) =
            if i = n then b ^ (n - 1) else 0 := by
          intro i hi
          have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          by_cases h : i = n
          · subst h; simp [show i ≠ 0 by omega]
          · simp [h, show n - i ≠ 0 by omega]
        rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' _ n,
          if_pos (Finset.mem_range.mpr (Nat.lt_succ_self n))]
        simp
      · have hn0 : n = 0 := by omega
        subst hn0; simp
    · intro n
      simp only [powSeq]
      have hih := ih hkpos
      by_cases hkn : k + 1 ≤ n
      · rw [if_pos hkn]
        have hterm : ∀ i ∈ Finset.range (n + 1),
            geom b i * powSeq (geom b) k (n - i) =
            if 1 ≤ i ∧ i ≤ n - k then
              (Nat.choose (n - i - 1) (k - 1) : R) * b ^ (n - (k + 1))
            else 0 := by
          intro i hi
          have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          rw [hih (n - i)]
          dsimp [geom]
          by_cases hi0 : i = 0
          · subst hi0; simp
          · rw [if_neg hi0]
            by_cases hle : k ≤ n - i
            · rw [if_pos hle, if_pos ⟨by omega, by omega⟩]
              have hexp : (i - 1) + (n - i - k) = n - (k + 1) := by omega
              rw [← mul_assoc, mul_comm (b ^ (i - 1)), mul_assoc, ← pow_add, hexp]
            · rw [if_neg hle, if_neg (by omega), mul_zero]
        rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, ← Finset.sum_mul]
        congr 1
        have hbij : ∑ i ∈ (Finset.range (n + 1)).filter (fun i => 1 ≤ i ∧ i ≤ n - k),
            (Nat.choose (n - i - 1) (k - 1) : R) =
            ∑ j ∈ Finset.range (n - k), (Nat.choose (j + (k - 1)) (k - 1) : R) := by
          refine Finset.sum_bij (fun i _ => n - i - k) ?_ ?_ ?_ ?_
          · intro i hi; simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢; omega
          · intro i1 h1 i2 h2 heq; simp only [Finset.mem_filter, Finset.mem_range] at h1 h2; omega
          · intro j hj
            have hj_lt : j < n - k := Finset.mem_range.mp hj
            refine ⟨n - k - j, ?_, by omega⟩
            simp only [Finset.mem_filter, Finset.mem_range]; omega
          · intro i hi; simp only [Finset.mem_filter, Finset.mem_range] at hi; congr 2; omega
        rw [hbij, ← Nat.cast_sum]
        have hnk : n - k = (n - k - 1) + 1 := by omega
        rw [hnk, hockey_stick (k - 1) (n - k - 1)]
        congr 2 <;> omega
      · rw [if_neg hkn]
        refine Finset.sum_eq_zero (fun i hi => ?_)
        have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [hih (n - i)]
        dsimp [geom]
        by_cases hi0 : i = 0
        · subst hi0; simp
        · rw [if_neg hi0, if_neg (by omega), mul_zero]

private lemma comp_geom {R : Type*} [CommRing R] (a b : R) :
    comp (geom a) (geom b) = geom (a + b) := by
  ext n
  cases n with
  | zero => simp [comp, geom]
  | succ n =>
    simp only [comp, geom, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    rw [Finset.sum_range_succ']
    simp only [if_true, zero_mul, add_zero]
    have hterm : ∀ k ∈ Finset.range (n + 1),
        (if k + 1 = 0 then (0 : R) else a ^ (k + 1 - 1)) * powSeq (geom b) (k + 1) (n + 1) =
        a ^ k * b ^ (n - k) * (Nat.choose n k : R) := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel, powSeq_geom b (k + 1) (by omega) (n + 1),
        if_pos (by omega), Nat.add_sub_cancel, Nat.add_sub_cancel, Nat.succ_sub_succ]
      ring
    rw [Finset.sum_congr rfl hterm, ← add_pow]

private lemma prove_a393857 (a : ℕ → ℤ) (ha0 : a 0 = 0)
    (harec : ∀ n : ℕ, comp a (innerSeq a) n = if n = 1 then 1 else 0)
    (n : ℕ) (hn : 1 ≤ n) : a n ≡ 1 [ZMOD 6] := by
  let φ : ℤ →+* ZMod 6 := Int.castRingHom (ZMod 6)
  have hmod6 : ∀ k : ℕ, φ (a k) = geom (1 : ZMod 6) k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [ha0, geom]
      · have hcomp := congr_arg φ (harec k)
        rw [comp_map] at hcomp
        have hinner : ∀ i ≤ k, φ (innerSeq a i) = geom (-1 : ZMod 6) i := by
          intro i hi
          rcases i with _ | _ | i
          · simp [innerSeq, geom]
          · simp [innerSeq, geom]
          · simp only [innerSeq, map_mul, map_neg, map_pow, map_ofNat, geom,
              Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
            have hih : φ (a (i + 1)) = 1 := by
              have := ih (i + 1) (by omega)
              simpa [φ, geom] using this
            rw [hih, mul_one]
            have h5 : (5 : ZMod 6) = -1 := by decide
            rw [h5, pow_succ']; ring
        have hcomp_geom : comp (geom (1 : ZMod 6)) (geom (-1 : ZMod 6)) k = if k = 1 then 1 else 0 := by
          rw [comp_geom, add_neg_cancel]
          dsimp [geom]
          rcases k with _ | _ | k
          · omega
          · simp
          · simp [zero_pow (Nat.succ_ne_zero k)]
        have hcongr_in : comp (fun i => φ (a i)) (fun i => φ (innerSeq a i)) k =
            comp (fun i => φ (a i)) (geom (-1 : ZMod 6)) k := by
          simp only [comp]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [powSeq_congr hinner j k le_rfl]
        rw [hcongr_in] at hcomp
        have hrhs : φ (if k = 1 then 1 else 0) = if k = 1 then 1 else 0 := by split_ifs <;> simp
        rw [hrhs, ← hcomp_geom] at hcomp
        simp only [comp] at hcomp
        rw [Finset.sum_range_succ, Finset.sum_range_succ] at hcomp
        have hrest : ∑ j ∈ Finset.range k, φ (a j) * powSeq (geom (-1 : ZMod 6)) j k =
            ∑ j ∈ Finset.range k, geom (1 : ZMod 6) j * powSeq (geom (-1 : ZMod 6)) j k := by
          refine Finset.sum_congr rfl (fun j hj => ?_)
          rw [ih j (Finset.mem_range.mp hj)]
        rw [hrest] at hcomp
        have hdiag : powSeq (geom (-1 : ZMod 6)) k k = 1 := by
          rw [powSeq_diag (by simp [geom]), show geom (-1 : ZMod 6) 1 = 1 by simp [geom], one_pow]
        rw [hdiag, mul_one, mul_one] at hcomp
        exact add_left_cancel hcomp
  have h1 : (a n : ZMod 6) = ((1 : ℤ) : ZMod 6) := by
    have := hmod6 n
    simpa [φ, geom, show n ≠ 0 by omega] using this
  exact (ZMod.intCast_eq_intCast_iff (a n) 1 6).mp h1

end OMA.P_oeis_a393857

theorem OMA.solution : type_of% @OMA.S_oeis_a393857.main :=
  OMA.P_oeis_a393857.prove_a393857
