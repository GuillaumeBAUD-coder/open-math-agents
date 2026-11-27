import OMAStatements.S_oeis_a002293
import Mathlib

namespace OMA.OeisA002293

open scoped List

private lemma list_bool_count_add (L : List Bool) :
    L.count true + L.count false = L.length := by
  induction L with
  | nil => simp
  | cons b bs ih => cases b <;> simp <;> omega

/-! ## Part 1: Raney's Cycle Lemma for 3-Dyck paths -/

private def stepW (b : Bool) : ℤ := if b then 3 else -1

private def prefSum {m : ℕ} (s : Fin m → Bool) (k : ℕ) : ℤ :=
  ∑ i : Fin m, if (i : ℕ) < k then stepW (s i) else 0

private def IsDyck3 (n : ℕ) (p : Fin (4 * n) → Bool) : Prop :=
  (Finset.univ.filter (fun i => p i = true)).card = n ∧
  ∀ k ≤ 4 * n, 0 ≤ prefSum p k

private lemma prefSum_zero {m : ℕ} (s : Fin m → Bool) : prefSum s 0 = 0 := by
  simp [prefSum]

private lemma prefSum_succ {m : ℕ} (s : Fin m → Bool) (k : ℕ) (hk : k < m) :
    prefSum s (k + 1) = prefSum s k + stepW (s ⟨k, hk⟩) := by
  unfold prefSum
  have hsplit : ∀ i : Fin m,
      (if (i : ℕ) < k + 1 then stepW (s i) else 0) =
      (if (i : ℕ) < k then stepW (s i) else 0) +
      (if i = ⟨k, hk⟩ then stepW (s i) else 0) := by
    intro i
    by_cases hi : (i : ℕ) < k
    · have hne : i ≠ ⟨k, hk⟩ := fun h => by rw [h] at hi; exact lt_irrefl k hi
      simp [hi, Nat.lt_succ_of_lt hi, hne]
    · by_cases heq : (i : ℕ) = k
      · have hieq : i = ⟨k, hk⟩ := Fin.ext heq
        simp [hi, hieq]
      · have hnot : ¬ (i : ℕ) < k + 1 := by omega
        have hne : i ≠ ⟨k, hk⟩ := fun h => heq (congrArg Fin.val h)
        simp [hi, hnot, hne]
  simp_rw [hsplit, Finset.sum_add_distrib]
  simp

private lemma prefSum_full {m : ℕ} (s : Fin m → Bool) :
    prefSum s m = 4 * ((Finset.univ.filter (fun i => s i = true)).card : ℤ) - (m : ℤ) := by
  unfold prefSum
  have hall : ∀ i : Fin m, (if (i : ℕ) < m then stepW (s i) else 0) =
      (if s i = true then (4 : ℤ) else 0) - 1 := by
    intro i
    simp only [i.isLt, ↓reduceIte, stepW]
    cases s i <;> norm_num
  simp_rw [hall, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    Finset.sum_ite, Finset.sum_const_zero, add_zero]
  ring

private def rot {n : ℕ} (r : Fin (4 * n + 1)) (s : Fin (4 * n + 1) → Bool) : Fin (4 * n + 1) → Bool :=
  fun i => s (i + r)

private lemma rot_zero {n : ℕ} (s : Fin (4 * n + 1) → Bool) : rot 0 s = s := by
  funext i; simp [rot]

private lemma rot_add {n : ℕ} (r1 r2 : Fin (4 * n + 1)) (s : Fin (4 * n + 1) → Bool) :
    rot r1 (rot r2 s) = rot (r1 + r2) s := by
  funext i; simp [rot, add_assoc]

private lemma rot_card_true {n : ℕ} (r : Fin (4 * n + 1)) (s : Fin (4 * n + 1) → Bool) :
    (Finset.univ.filter (fun i => rot r s i = true)).card =
    (Finset.univ.filter (fun i => s i = true)).card := by
  refine Finset.card_bij (fun i _ => i + r) ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  · intro i1 _ i2 _ h; exact add_right_cancel h
  · intro j hj
    refine ⟨j - r, ?_, sub_add_cancel j r⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simpa [rot, sub_add_cancel] using (Finset.mem_filter.mp hj).2⟩

private lemma prefSum_rot {n : ℕ} (r : Fin (4 * n + 1)) (s : Fin (4 * n + 1) → Bool)
    (k : ℕ) (hk : k ≤ 4 * n + 1) :
    prefSum (rot r s) k =
      if r.val + k ≤ 4 * n + 1 then
        prefSum s (r.val + k) - prefSum s r.val
      else
        prefSum s (4 * n + 1) - prefSum s r.val + prefSum s (r.val + k - (4 * n + 1)) := by
  induction k with
  | zero =>
    simp [prefSum_zero]
  | succ k ih =>
    have hklt : k < 4 * n + 1 := by omega
    rw [prefSum_succ (rot r s) k hklt, ih (by omega)]
    have hrlt : r.val < 4 * n + 1 := r.isLt
    by_cases h1 : r.val + k < 4 * n + 1
    · rw [if_pos (show r.val + k ≤ 4 * n + 1 by omega),
          if_pos (show r.val + (k + 1) ≤ 4 * n + 1 by omega)]
      have hadd : ((⟨k, hklt⟩ : Fin (4 * n + 1)) + r).val = r.val + k := by
        rw [Fin.val_add, Nat.mod_eq_of_lt (by omega : k + r.val < 4 * n + 1)]; omega
      have hrot : rot r s ⟨k, hklt⟩ = s ⟨r.val + k, h1⟩ := by
        dsimp [rot]; congr 1; exact Fin.ext hadd
      rw [hrot, show r.val + (k + 1) = (r.val + k) + 1 by omega, prefSum_succ s (r.val + k) h1]
      ring
    · by_cases hEq : r.val + k = 4 * n + 1
      · rw [if_pos (show r.val + k ≤ 4 * n + 1 by omega),
            if_neg (show ¬ (r.val + (k + 1) ≤ 4 * n + 1) by omega)]
        have hadd : ((⟨k, hklt⟩ : Fin (4 * n + 1)) + r).val = 0 := by
          rw [Fin.val_add, show k + r.val = 4 * n + 1 by omega, Nat.mod_self]
        have hrot : rot r s ⟨k, hklt⟩ = s ⟨0, by omega⟩ := by
          dsimp [rot]; congr 1; exact Fin.ext hadd
        have hsub1 : r.val + (k + 1) - (4 * n + 1) = 1 := by omega
        rw [hEq, hrot, hsub1, prefSum_succ s 0 (by omega), prefSum_zero]
        ring
      · rw [if_neg (show ¬ (r.val + k ≤ 4 * n + 1) by omega),
            if_neg (show ¬ (r.val + (k + 1) ≤ 4 * n + 1) by omega)]
        have hj : r.val + k - (4 * n + 1) < 4 * n + 1 := by omega
        have hadd : ((⟨k, hklt⟩ : Fin (4 * n + 1)) + r).val = r.val + k - (4 * n + 1) := by
          rw [Fin.val_add]
          have hlt2 : k + r.val - (4 * n + 1) < 4 * n + 1 := by omega
          have heq2 : k + r.val = (4 * n + 1) + (k + r.val - (4 * n + 1)) := by omega
          rw [heq2, Nat.add_mod_left, Nat.mod_eq_of_lt hlt2]
          omega
        have hrot : rot r s ⟨k, hklt⟩ = s ⟨r.val + k - (4 * n + 1), hj⟩ := by
          dsimp [rot]; congr 1; exact Fin.ext hadd
        have hsub : r.val + (k + 1) - (4 * n + 1) = (r.val + k - (4 * n + 1)) + 1 := by omega
        rw [hrot, hsub, prefSum_succ s (r.val + k - (4 * n + 1)) hj]
        ring

private def extendFalse {n : ℕ} (p : Fin (4 * n) → Bool) : Fin (4 * n + 1) → Bool :=
  fun i => if h : i.val < 4 * n then p ⟨i.val, h⟩ else false

private lemma prefSum_extendFalse {n : ℕ} (p : Fin (4 * n) → Bool) (k : ℕ) (hk : k ≤ 4 * n) :
    prefSum (extendFalse p) k = prefSum p k := by
  unfold prefSum
  rw [Fin.sum_univ_castSucc]
  have hlast : (if (Fin.last (4 * n) : Fin (4 * n + 1)).val < k then
      stepW (extendFalse p (Fin.last (4 * n))) else 0) = 0 := by
    simp only [Fin.val_last]; split_ifs with h <;> [omega; rfl]
  rw [hlast, add_zero]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp only [Fin.val_castSucc, extendFalse, i.isLt, ↓reduceDIte, Fin.eta]

private lemma card_true_extendFalse {n : ℕ} (p : Fin (4 * n) → Bool) :
    (Finset.univ.filter (fun i => extendFalse p i = true)).card =
    (Finset.univ.filter (fun i => p i = true)).card := by
  have hlt_of_mem : ∀ i : Fin (4 * n + 1), i ∈ Finset.univ.filter (fun i => extendFalse p i = true) →
      i.val < 4 * n := by
    intro i hi
    have h := (Finset.mem_filter.mp hi).2
    by_contra hge
    simp [extendFalse, hge] at h
  refine Finset.card_bij (fun i hi => ⟨i.val, hlt_of_mem i hi⟩) ?_ ?_ ?_
  · intro i hi
    have hlt := hlt_of_mem i hi
    have h := (Finset.mem_filter.mp hi).2
    simp only [extendFalse, hlt, ↓reduceDIte] at h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  · intro i1 _ i2 _ h
    exact Fin.ext (Fin.mk.inj h)
  · intro j hj
    refine ⟨j.castSucc, ?_, by ext; simp⟩
    have h := (Finset.mem_filter.mp hj).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [extendFalse, j.isLt] using h⟩

private def SSet (n : ℕ) :=
  { s : Fin (4 * n + 1) → Bool // (Finset.univ.filter (fun i => s i = true)).card = n }

private lemma card_SSet (n : ℕ) : Nat.card (SSet n) = (4 * n + 1).choose n := by
  classical
  let e : SSet n ≃ { A : Finset (Fin (4 * n + 1)) // A.card = n } :=
    { toFun := fun s => ⟨Finset.univ.filter (fun i => s.1 i = true), s.2⟩
      invFun := fun A => ⟨fun i => decide (i ∈ A.1), by
        convert A.2
        ext i; simp⟩
      left_inv := fun s => by
        apply Subtype.ext; funext i; simp
      right_inv := fun A => by
        apply Subtype.ext; ext i; simp }
  let e2 : { A : Finset (Fin (4 * n + 1)) // A.card = n } ≃
      (Finset.powersetCard n (Finset.univ : Finset (Fin (4 * n + 1)))) :=
    { toFun := fun A => ⟨A.1, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, A.2⟩⟩
      invFun := fun A => ⟨A.1, (Finset.mem_powersetCard.mp A.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr (e.trans e2), Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

private lemma exists_unique_first_min {n : ℕ} (s : Fin (4 * n + 1) → Bool) :
    ∃! r : Fin (4 * n + 1),
      (∀ j : Fin (4 * n + 1), prefSum s r.val ≤ prefSum s j.val) ∧
      (∀ j : Fin (4 * n + 1), j < r → prefSum s r.val < prefSum s j.val) := by
  have hne : (Finset.univ : Finset (Fin (4 * n + 1))).Nonempty := ⟨0, Finset.mem_univ 0⟩
  obtain ⟨r0, _, hr0⟩ := Finset.exists_min_image Finset.univ (fun j : Fin (4 * n + 1) => prefSum s j.val) hne
  let mins := Finset.univ.filter (fun j : Fin (4 * n + 1) => prefSum s j.val = prefSum s r0.val)
  have hne_mins : mins.Nonempty := ⟨r0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  let r := mins.min' hne_mins
  have hr_mem : r ∈ mins := Finset.min'_mem mins hne_mins
  have hr_eq : prefSum s r.val = prefSum s r0.val := (Finset.mem_filter.mp hr_mem).2
  have hr_le : ∀ j : Fin (4 * n + 1), prefSum s r.val ≤ prefSum s j.val := by
    intro j; rw [hr_eq]; exact hr0 j (Finset.mem_univ j)
  have hr_lt : ∀ j : Fin (4 * n + 1), j < r → prefSum s r.val < prefSum s j.val := by
    intro j hj
    have hle := hr_le j
    have hne' : prefSum s j.val ≠ prefSum s r.val := by
      intro heq
      have hjmem : j ∈ mins := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by linarith⟩
      have := Finset.min'_le mins j hjmem
      exact not_lt.mpr this hj
    omega
  refine ⟨r, ⟨hr_le, hr_lt⟩, ?_⟩
  intro r' ⟨hr'_le, hr'_lt⟩
  by_contra hne'
  rcases lt_or_gt_of_ne hne' with hlt | hgt
  · have := hr_lt r' hlt
    have := hr'_le r
    omega
  · have := hr'_lt r hgt
    have := hr_le r'
    omega

private lemma isFirstMin_iff_dyck {n : ℕ} (s : SSet n) (r : Fin (4 * n + 1)) :
    ((∀ j : Fin (4 * n + 1), prefSum s.1 r.val ≤ prefSum s.1 j.val) ∧
     (∀ j : Fin (4 * n + 1), j < r → prefSum s.1 r.val < prefSum s.1 j.val)) ↔
    (∀ k ≤ 4 * n, 0 ≤ prefSum (rot r s.1) k) := by
  have hfull : prefSum s.1 (4 * n + 1) = -1 := by
    rw [prefSum_full, s.2]; push_cast; ring
  have hrlt : r.val < 4 * n + 1 := r.isLt
  constructor
  · rintro ⟨hle, hlt⟩ k hk
    rw [prefSum_rot r s.1 k (by omega)]
    split_ifs with h1
    · by_cases hEq : r.val + k = 4 * n + 1
      · rw [hEq, hfull]
        have hr_pos : 0 < r := Fin.pos_iff_ne_zero.mpr (fun h0 => by rw [h0] at hEq; simp at hEq; omega)
        have h0 := hlt 0 hr_pos
        rw [show (0 : Fin (4 * n + 1)).val = 0 from rfl, prefSum_zero] at h0
        omega
      · have hlt' : r.val + k < 4 * n + 1 := by omega
        have := hle ⟨r.val + k, hlt'⟩
        dsimp only at this
        omega
    · have hjlt : r.val + k - (4 * n + 1) < r.val := by omega
      have hj : (⟨r.val + k - (4 * n + 1), by omega⟩ : Fin (4 * n + 1)) < r := hjlt
      have := hlt ⟨r.val + k - (4 * n + 1), by omega⟩ hj
      dsimp only at this
      rw [hfull]
      omega
  · intro hdyck
    have hlt_of_lt : ∀ j : Fin (4 * n + 1), j < r → prefSum s.1 r.val < prefSum s.1 j.val := by
      intro j hj
      have hjv : j.val < r.val := hj
      by_cases hj0 : j.val = 0
      · have hk0 : 4 * n + 1 - r.val ≤ 4 * n := by omega
        have h0' := hdyck (4 * n + 1 - r.val) hk0
        rw [prefSum_rot r s.1 (4 * n + 1 - r.val) (by omega)] at h0'
        have hle0 : r.val + (4 * n + 1 - r.val) ≤ 4 * n + 1 := by omega
        rw [if_pos hle0, show r.val + (4 * n + 1 - r.val) = 4 * n + 1 by omega, hfull] at h0'
        rw [hj0, prefSum_zero]; omega
      · have hk : 4 * n + 1 + j.val - r.val ≤ 4 * n := by omega
        have h0 := hdyck (4 * n + 1 + j.val - r.val) hk
        rw [prefSum_rot r s.1 (4 * n + 1 + j.val - r.val) (by omega)] at h0
        have hnot' : ¬ (r.val + (4 * n + 1 + j.val - r.val) ≤ 4 * n + 1) := by omega
        rw [if_neg hnot', show r.val + (4 * n + 1 + j.val - r.val) - (4 * n + 1) = j.val by omega, hfull] at h0
        omega
    refine ⟨?_, hlt_of_lt⟩
    intro j
    have hjlt : j.val < 4 * n + 1 := j.isLt
    by_cases hj : r.val ≤ j.val
    · have hk : j.val - r.val ≤ 4 * n := by omega
      have h0 := hdyck (j.val - r.val) hk
      rw [prefSum_rot r s.1 (j.val - r.val) (by omega)] at h0
      have hle1 : r.val + (j.val - r.val) ≤ 4 * n + 1 := by omega
      rw [if_pos hle1, show r.val + (j.val - r.val) = j.val by omega] at h0
      omega
    · exact le_of_lt (hlt_of_lt j (by exact Nat.lt_of_not_ge hj))

private lemma card_dyck3_eq (n : ℕ) :
    Nat.card { p : Fin (4 * n) → Bool // IsDyck3 n p } = (4 * n).choose n / (3 * n + 1) := by
  classical
  let toS : Fin (4 * n + 1) × { p : Fin (4 * n) → Bool // IsDyck3 n p } → SSet n :=
    fun ⟨r, p⟩ => ⟨rot (-r) (extendFalse p.1), by
      rw [rot_card_true, card_true_extendFalse]; exact p.2.1⟩
  have hbij : Function.Bijective toS := by
    constructor
    · rintro ⟨r1, p1⟩ ⟨r2, p2⟩ hEq
      have hval : rot (-r1) (extendFalse p1.1) = rot (-r2) (extendFalse p2.1) := congrArg Subtype.val hEq
      set s : SSet n := toS ⟨r1, p1⟩
      have hs1 : rot r1 s.1 = extendFalse p1.1 := by
        dsimp [s, toS]; rw [rot_add, add_neg_cancel, rot_zero]
      have hs2 : rot r2 s.1 = extendFalse p2.1 := by
        have : s.1 = rot (-r2) (extendFalse p2.1) := hval
        rw [this, rot_add, add_neg_cancel, rot_zero]
      have hm1 : ∀ k ≤ 4 * n, 0 ≤ prefSum (rot r1 s.1) k := by
        intro k hk; rw [hs1, prefSum_extendFalse p1.1 k hk]; exact p1.2.2 k hk
      have hm2 : ∀ k ≤ 4 * n, 0 ≤ prefSum (rot r2 s.1) k := by
        intro k hk; rw [hs2, prefSum_extendFalse p2.1 k hk]; exact p2.2.2 k hk
      obtain ⟨r0, _, huniq⟩ := exists_unique_first_min s.1
      have hr1 : r1 = r0 := huniq r1 ((isFirstMin_iff_dyck s r1).mpr hm1)
      have hr2 : r2 = r0 := huniq r2 ((isFirstMin_iff_dyck s r2).mpr hm2)
      have hrr : r1 = r2 := hr1.trans hr2.symm
      subst hrr
      have hext : extendFalse p1.1 = extendFalse p2.1 := hs1.symm.trans hs2
      have hp : p1 = p2 := by
        apply Subtype.ext; funext i
        have := congrFun hext i.castSucc
        simpa [extendFalse, i.isLt] using this
      exact Prod.ext rfl hp
    · intro s
      obtain ⟨r, hr, _⟩ := exists_unique_first_min s.1
      have hdyck : ∀ k ≤ 4 * n, 0 ≤ prefSum (rot r s.1) k := (isFirstMin_iff_dyck s r).mp hr
      have hfull : prefSum (rot r s.1) (4 * n + 1) = -1 := by
        rw [prefSum_full, rot_card_true, s.2]; push_cast; ring
      have hlast_false : rot r s.1 (Fin.last (4 * n)) = false := by
        have hstep := prefSum_succ (rot r s.1) (4 * n) (Nat.lt_succ_self (4 * n))
        have hge := hdyck (4 * n) le_rfl
        have hlast_eq : (⟨4 * n, Nat.lt_succ_self (4 * n)⟩ : Fin (4 * n + 1)) = Fin.last (4 * n) := rfl
        rw [hlast_eq] at hstep
        cases hb : rot r s.1 (Fin.last (4 * n))
        · rfl
        · rw [hb] at hstep; simp [stepW] at hstep; omega
      let p : Fin (4 * n) → Bool := fun i => rot r s.1 i.castSucc
      have hext : extendFalse p = rot r s.1 := by
        funext i
        by_cases h : i.val < 4 * n
        · simp only [extendFalse, h, ↓reduceDIte, p]; congr 1
        · have hi : i = Fin.last (4 * n) := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
          subst hi
          simp [extendFalse, hlast_false]
      have hp_dyck : IsDyck3 n p := by
        constructor
        · rw [← card_true_extendFalse, hext, rot_card_true]; exact s.2
        · intro k hk; rw [← prefSum_extendFalse p k hk, hext]; exact hdyck k hk
      refine ⟨⟨r, ⟨p, hp_dyck⟩⟩, ?_⟩
      apply Subtype.ext
      dsimp [toS]
      rw [hext, rot_add, neg_add_cancel, rot_zero]
  have hcard : (4 * n + 1) * Nat.card { p : Fin (4 * n) → Bool // IsDyck3 n p } =
      (4 * n + 1).choose n := by
    have h1 := Nat.card_congr (Equiv.ofBijective toS hbij)
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin (4 * n + 1)), Fintype.card_fin,
      card_SSet] at h1
    exact h1
  have hbinom : (3 * n + 1) * (4 * n + 1).choose n = (4 * n + 1) * (4 * n).choose n := by
    have h1 := Nat.choose_mul_succ_eq (4 * n) n
    have hsub : 4 * n + 1 - n = 3 * n + 1 := by omega
    rw [hsub] at h1
    linarith
  have hmul : (3 * n + 1) * Nat.card { p : Fin (4 * n) → Bool // IsDyck3 n p } =
      (4 * n).choose n := by
    have h4 : (4 * n + 1) * ((3 * n + 1) * Nat.card { p : Fin (4 * n) → Bool // IsDyck3 n p }) =
        (4 * n + 1) * (4 * n).choose n := by
      calc (4 * n + 1) * ((3 * n + 1) * Nat.card { p : Fin (4 * n) → Bool // IsDyck3 n p })
          = (3 * n + 1) * ((4 * n + 1) * Nat.card { p : Fin (4 * n) → Bool // IsDyck3 n p }) := by ring
        _ = (3 * n + 1) * (4 * n + 1).choose n := by rw [hcard]
        _ = (4 * n + 1) * (4 * n).choose n := hbinom
    exact Nat.eq_of_mul_eq_mul_left (by omega) h4
  rw [← hmul, Nat.mul_div_cancel_left _ (by omega)]

/-! ## Part 2: List-based 3-Dyck paths and stack-sorting bijection -/

private def IsDyck3List (n : ℕ) (p : List Bool) : Prop :=
  p.length = 4 * n ∧ p.count true = n ∧
  ∀ k ≤ 4 * n, (p.take k).count false ≤ 3 * (p.take k).count true

private lemma prefSum_eq_count {m : ℕ} (p : Fin m → Bool) (k : ℕ) (hk : k ≤ m) :
    prefSum p k = 3 * (((List.ofFn p).take k).count true : ℤ) -
      (((List.ofFn p).take k).count false : ℤ) := by
  induction k with
  | zero => simp [prefSum_zero]
  | succ k ih =>
    have hklt : k < m := by omega
    have hlen : k < (List.ofFn p).length := by simp [hklt]
    rw [prefSum_succ p k hklt, ih (by omega), List.take_succ_eq_append_getElem hlen,
      List.count_append, List.count_append, List.getElem_ofFn]
    cases p ⟨k, hklt⟩ <;> simp [stepW] <;> ring

private lemma card_dyck3List_eq (n : ℕ) :
    Nat.card { p : List Bool // IsDyck3List n p } = (4 * n).choose n / (3 * n + 1) := by
  let e : { p : Fin (4 * n) → Bool // IsDyck3 n p } ≃ { p : List Bool // IsDyck3List n p } :=
    { toFun := fun p => ⟨List.ofFn p.1, by
        refine ⟨List.length_ofFn, ?_, ?_⟩
        · have hfull := prefSum_full p.1
          have hcnt := prefSum_eq_count p.1 (4 * n) le_rfl
          rw [List.take_of_length_le (by simp)] at hcnt
          have htot : (List.ofFn p.1).count true + (List.ofFn p.1).count false = 4 * n := by
            have hl : ∀ L : List Bool, L.count true + L.count false = L.length := by
              intro L; induction L with
              | nil => simp
              | cons b bs ih => cases b <;> simp [List.count_cons] <;> omega
            rw [hl, List.length_ofFn]
          have hcard := p.2.1
          omega
        · intro k hk
          have h1 := p.2.2 k hk
          rw [prefSum_eq_count p.1 k hk] at h1
          omega⟩
      invFun := fun p =>
        let f : Fin (4 * n) → Bool := fun i => p.1[i.val]'(by rw [p.2.1]; exact i.isLt)
        ⟨f, by
        have hlen := p.2.1
        have hof : List.ofFn f = p.1 := by
          apply List.ext_getElem
          · simp [p.2.1]
          · intro j hj1 hj2; simp [f]
        refine ⟨?_, ?_⟩
        · have hfull := prefSum_full f
          have hcnt := prefSum_eq_count f (4 * n) le_rfl
          rw [hof, List.take_of_length_le (by omega)] at hcnt
          rw [hfull] at hcnt
          have htot : p.1.count true + p.1.count false = 4 * n := by
            rw [list_bool_count_add, p.2.1]
          have hct := p.2.2.1
          push_cast at hcnt
          omega
        · intro k hk
          rw [prefSum_eq_count f k hk, hof]
          have := p.2.2.2 k hk
          omega⟩
      left_inv := fun p => by apply Subtype.ext; funext i; simp
      right_inv := fun p => by
        apply Subtype.ext
        apply List.ext_getElem
        · simp [p.2.1]
        · intro j hj1 hj2; simp }
  rw [← Nat.card_congr e, card_dyck3_eq]

private def popLe {n : ℕ} (x : Fin n) : List (Fin n) → List (Fin n) × List (Fin n)
  | [] => ([x], [])
  | y :: ys =>
    if y ≤ x then
      let r := popLe x ys
      (r.1, y :: r.2)
    else
      (x :: y :: ys, [])

private lemma popLe_perm {n : ℕ} (x : Fin n) (st : List (Fin n)) :
    (popLe x st).1 ++ (popLe x st).2 ~ x :: st := by
  induction st with
  | nil => simp [popLe]
  | cons y ys ih =>
    unfold popLe
    split_ifs
    · calc (popLe x ys).1 ++ y :: (popLe x ys).2
          ~ y :: ((popLe x ys).1 ++ (popLe x ys).2) := List.perm_middle
        _ ~ y :: x :: ys := ih.cons y
        _ ~ x :: y :: ys := List.Perm.swap x y ys
    · simp

private lemma popLe_head_eq {n : ℕ} (x : Fin n) (st : List (Fin n)) :
    ∃ rest : List (Fin n), (popLe x st).1 = x :: rest ∧ st = (popLe x st).2 ++ rest ∧
      (∀ y ∈ (popLe x st).2, y ≤ x) ∧
      (st.Pairwise (· < ·) → (x :: rest).Pairwise (· < ·)) := by
  induction st with
  | nil =>
    exact ⟨[], rfl, rfl, by simp [popLe], by simp⟩
  | cons y ys ih =>
    unfold popLe
    split_ifs with hle
    · obtain ⟨rest, h1, h2, h3, h4⟩ := ih
      refine ⟨rest, h1, ?_, ?_, ?_⟩
      · rw [List.cons_append]; exact congrArg (y :: ·) h2
      · intro z hz
        simp only [List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hle
        · exact h3 z hz
      · intro hp; exact h4 (List.pairwise_cons.mp hp).2
    · refine ⟨y :: ys, rfl, rfl, by simp, ?_⟩
      intro hp
      rw [List.pairwise_cons]
      refine ⟨?_, hp⟩
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact lt_of_not_ge hle
      · exact lt_trans (lt_of_not_ge hle) ((List.pairwise_cons.mp hp).1 z hz)

private def runFwd {n : ℕ} : List (Fin n) → List (Fin n) → Finset (Fin n) → List Bool × List (Fin n)
  | [], st, _ => (List.replicate st.length false, st)
  | x :: xs, st, seen =>
    let r := popLe x st
    let ds := List.replicate r.2.length false
    let res := runFwd xs r.1 (insert x seen)
    if x ∈ seen then
      (ds ++ res.1, r.2 ++ res.2)
    else
      (ds ++ true :: res.1, r.2 ++ res.2)

private lemma runFwd_out_perm {n : ℕ} (w st : List (Fin n)) (seen : Finset (Fin n)) :
    (runFwd w st seen).2 ~ w ++ st := by
  induction w generalizing st seen with
  | nil => simp [runFwd]
  | cons x xs ih =>
    unfold runFwd
    have hsplit : (if x ∈ seen then
        (List.replicate (popLe x st).2.length false ++ (runFwd xs (popLe x st).1 (insert x seen)).1,
         (popLe x st).2 ++ (runFwd xs (popLe x st).1 (insert x seen)).2)
      else
        (List.replicate (popLe x st).2.length false ++ true :: (runFwd xs (popLe x st).1 (insert x seen)).1,
         (popLe x st).2 ++ (runFwd xs (popLe x st).1 (insert x seen)).2)).2 =
        (popLe x st).2 ++ (runFwd xs (popLe x st).1 (insert x seen)).2 := by
      split_ifs <;> rfl
    rw [hsplit]
    calc (popLe x st).2 ++ (runFwd xs (popLe x st).1 (insert x seen)).2
        ~ (popLe x st).2 ++ (xs ++ (popLe x st).1) := (ih _ _).append_left _
      _ ~ xs ++ ((popLe x st).1 ++ (popLe x st).2) := by
          calc (popLe x st).2 ++ (xs ++ (popLe x st).1)
              = ((popLe x st).2 ++ xs) ++ (popLe x st).1 := (List.append_assoc _ _ _).symm
            _ ~ (xs ++ (popLe x st).2) ++ (popLe x st).1 := (List.perm_append_comm).append_right _
            _ = xs ++ ((popLe x st).2 ++ (popLe x st).1) := List.append_assoc _ _ _
            _ ~ xs ++ ((popLe x st).1 ++ (popLe x st).2) := List.perm_append_comm.append_left _
      _ ~ xs ++ (x :: st) := (popLe_perm x st).append_left _
      _ ~ x :: (xs ++ st) := List.perm_middle

private lemma runFwd_cons_st_of_le {n : ℕ} (c : Fin n) (w st : List (Fin n)) (seen : Finset (Fin n))
    (hle : ∀ a ∈ w, c ≤ a) :
    (runFwd w (c :: st) seen).1 = false :: (runFwd w st seen).1 := by
  cases w with
  | nil =>
    simp [runFwd, List.replicate_succ]
  | cons a as =>
    have hca : c ≤ a := hle a (by simp)
    unfold runFwd
    simp only [popLe, hca, ↓reduceIte, List.length_cons, List.replicate_succ, List.cons_append]
    split_ifs <;> rfl

private lemma runFwd_count_false {n : ℕ} (w st : List (Fin n)) (seen : Finset (Fin n)) :
    (runFwd w st seen).1.count false = (runFwd w st seen).2.length := by
  induction w generalizing st seen with
  | nil => simp [runFwd]
  | cons x xs ih =>
    unfold runFwd
    split_ifs <;> simp [List.count_append, ih]

private lemma runFwd_count_true {n : ℕ} (w st : List (Fin n)) (seen : Finset (Fin n)) :
    (runFwd w st seen).1.count true = (w.toFinset \ seen).card := by
  induction w generalizing st seen with
  | nil => simp [runFwd, List.count_replicate]
  | cons x xs ih =>
    unfold runFwd
    by_cases hx : x ∈ seen
    · simp only [hx, ↓reduceIte, List.count_append, List.count_replicate, beq_iff_eq,
        Bool.false_eq_true, ↓reduceIte, zero_add, ih, Finset.insert_eq_of_mem hx]
      congr 1; ext y; simp only [List.toFinset_cons, Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · intro ⟨hy, hns⟩; exact ⟨Or.inr hy, hns⟩
      · rintro ⟨rfl | hy, hns⟩
        · exact absurd hx hns
        · exact ⟨hy, hns⟩
    · simp only [hx, ↓reduceIte, List.count_append, List.count_cons, List.count_replicate,
        beq_iff_eq, Bool.false_eq_true, ↓reduceIte, zero_add, ih]
      have hcard : ((x :: xs).toFinset \ seen) = insert x (xs.toFinset \ insert x seen) := by
        ext y; simp only [List.toFinset_cons, Finset.mem_sdiff, Finset.mem_insert]
        by_cases hyx : y = x
        · subst hyx; simp [hx]
        · simp [hyx]
      rw [hcard, Finset.card_insert_of_notMem (by simp)]

private def allLabels (n : ℕ) : List (Fin n × Bool) :=
  (List.finRange n).reverse.flatMap (fun c => [(c, true), (c, true), (c, false)])

private def decStep {n : ℕ} (s : List (Fin n × Bool) × List (Fin n) × List (Fin n)) (b : Bool) :
    List (Fin n × Bool) × List (Fin n) × List (Fin n) :=
  match b, s.1, s.2.1 with
  | false, (c, true) :: ls, st => (ls, st, c :: s.2.2)
  | false, (c, false) :: ls, st => (ls, c :: st, s.2.2)
  | true, ls, x :: st => (ls, st, x :: s.2.2)
  | _, _, _ => s

private def decodeState {n : ℕ} (q : List Bool)
    (s : List (Fin n × Bool) × List (Fin n) × List (Fin n)) :
    List (Fin n × Bool) × List (Fin n) × List (Fin n) :=
  q.foldl decStep s

private def decodeList (n : ℕ) (p : List Bool) : List (Fin n) :=
  (decodeState p.reverse (allLabels n, [], [])).2.2

private def Avoids231 {n : ℕ} (w : List (Fin n)) : Prop :=
  ∀ i j k (hi : i < w.length) (hj : j < w.length) (hk : k < w.length),
    i < j → j < k → ¬ (w[k] < w[i] ∧ w[i] ≤ w[j])

private def StackInv {n : ℕ} (st acc : List (Fin n)) : Prop :=
  ∀ x ∈ st, ∀ j k (hj : j < acc.length) (hk : k < acc.length),
    j < k → x ≤ acc[j] → x ≤ acc[k]

private def LabelsInv {n : ℕ} (ls : List (Fin n × Bool)) : Prop :=
  ls.Pairwise (fun a b => b.1 ≤ a.1 ∧ (a.2 = false → b.1 < a.1))

private lemma labelsInv_allLabels (n : ℕ) : LabelsInv (allLabels n) := by
  unfold LabelsInv allLabels
  rw [List.pairwise_flatMap]
  refine ⟨?_, ?_⟩
  · intro c _; simp
  · rw [List.pairwise_reverse]
    have hfin : (List.finRange n).Pairwise (· < ·) := List.pairwise_lt_finRange n
    refine hfin.imp_of_mem ?_
    intro a b _ _ hab x hx y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      exact ⟨le_of_lt hab, fun _ => hab⟩

private lemma count_allLabels (n : ℕ) (c : Fin n) :
    ((allLabels n).map Prod.fst).count c = 3 := by
  unfold allLabels
  have hfn : ∀ d : Fin n,
      (List.map Prod.fst [(d, true), (d, true), (d, false)]).count c = if d = c then 3 else 0 := by
    intro d
    by_cases h : d = c
    · subst h; simp
    · simp [h]
  have hmap : (((List.finRange n).reverse.flatMap
      (fun d => [(d, true), (d, true), (d, false)])).map Prod.fst).count c =
      ((List.finRange n).reverse.map (fun d => if d = c then 3 else 0)).sum := by
    rw [List.map_flatMap, List.count_flatMap]
    congr 1
    refine List.map_congr_left ?_
    intro d _; exact hfn d
  rw [hmap, List.map_reverse, List.sum_reverse]
  have hnd : (List.finRange n).Nodup := List.nodup_finRange n
  have hsum : ((List.finRange n).map (fun d => if d = c then 3 else 0)).sum =
      ∑ d ∈ (List.finRange n).toFinset, if d = c then 3 else 0 := by
    rw [List.sum_toFinset _ hnd]
  rw [hsum]
  simp only [Finset.sum_ite_eq', List.mem_toFinset, List.mem_finRange, ↓reduceIte]

private lemma length_allLabels (n : ℕ) : (allLabels n).length = 3 * n := by
  unfold allLabels
  rw [List.length_flatMap]
  simp [List.map_const', List.sum_replicate, mul_comm]

private lemma count_false_allLabels_drop (n : ℕ) (m : ℕ) (hm : m ≤ 3 * n) :
    ((allLabels n).drop m).countP (fun x => !x.2) = n - m / 3 := by
  have hfull : ∀ L : List (Fin n),
      (L.flatMap (fun c => [(c, true), (c, true), (c, false)])).countP (fun x => !x.2) = L.length := by
    intro L
    induction L with
    | nil => simp
    | cons a L' ih =>
      simp only [List.flatMap_cons, List.countP_append, ih, List.length_cons]
      simp; omega
  have hget : ∀ (k : ℕ) (hk : k < (allLabels n).length),
      ((allLabels n)[k]'hk).2 = decide (k % 3 ≠ 2) := by
    intro k hk
    have haux : ∀ (L : List (Fin n)) (k : ℕ) (hk : k < (L.flatMap (fun c => [(c, true), (c, true), (c, false)])).length),
        ((L.flatMap (fun c => [(c, true), (c, true), (c, false)]))[k]'hk).2 = decide (k % 3 ≠ 2) := by
      intro L
      induction L with
      | nil => intro k hk; simp at hk
      | cons a L' ih =>
        intro k hk
        simp only [List.flatMap_cons, List.cons_append, List.nil_append] at hk ⊢
        rcases k with _ | _ | _ | k
        · rfl
        · rfl
        · rfl
        · have hk' : k < (L'.flatMap (fun c => [(c, true), (c, true), (c, false)])).length := by
            simp only [List.length_cons] at hk; omega
          have hmod : (k + 1 + 1 + 1) % 3 = k % 3 := by omega
          simpa [hmod] using ih k hk'
    exact haux (List.finRange n).reverse k hk
  have hcnt_all : (allLabels n).countP (fun x => !x.2) = n := by
    simpa [allLabels] using hfull (List.finRange n).reverse
  have htake_drop := congrArg (List.countP (fun x : Fin n × Bool => !x.2)) (List.take_append_drop m (allLabels n))
  rw [List.countP_append, hcnt_all] at htake_drop
  have htake : ∀ r ≤ 3 * n, ((allLabels n).take r).countP (fun x => !x.2) = r / 3 := by
    intro r
    induction r with
    | zero => intro _; simp
    | succ r ih =>
      intro hr
      have hr_lt : r < (allLabels n).length := by rw [length_allLabels]; omega
      rw [List.take_succ_eq_append_getElem hr_lt, List.countP_append, ih (by omega)]
      simp only [List.countP_cons, List.countP_nil, hget r hr_lt]
      have : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by omega
      rcases this with h | h | h <;> simp [h] <;> omega
  have htm := htake m hm
  omega

private def seenAt {n : ℕ} (ls : List (Fin n × Bool)) (st : List (Fin n)) : Finset (Fin n) :=
  st.toFinset ∪ ((ls.filter (fun p => !p.2)).map Prod.fst).toFinset

private structure DecInv {n : ℕ} (q_done : List Bool)
    (ls : List (Fin n × Bool)) (st acc : List (Fin n)) : Prop where
  ls_eq : ls = (allLabels n).drop (q_done.count false)
  cnt_le : q_done.count false ≤ 3 * n
  st_len : st.length + q_done.count true = q_done.count false / 3
  st_sorted : st.Pairwise (· < ·)
  st_gt_ls : ∀ x ∈ st, ∀ y ∈ ls, y.1 < x
  ls_le_acc : ∀ y ∈ ls, ∀ a ∈ acc, y.1 ≤ a
  avoid : Avoids231 acc
  stack_inv : StackInv st acc
  perm_all : (ls.map Prod.fst) ++ st ++ acc ~ (allLabels n).map Prod.fst
  fwd_eq : (runFwd acc st (seenAt ls st)).1 = q_done.reverse

private lemma decInv_init (n : ℕ) : DecInv (n := n) [] (allLabels n) [] [] := by
  refine ⟨by simp, by simp, by simp, List.Pairwise.nil, by simp, by simp, ?_, ?_, by simp, ?_⟩
  · intro i j k hi; simp at hi
  · intro x hx; simp at hx
  · simp [runFwd, seenAt]

private lemma decInv_step {n : ℕ} (q_done : List Bool) (ls : List (Fin n × Bool))
    (st acc : List (Fin n)) (b : Bool)
    (hinv : DecInv q_done ls st acc)
    (hb_false : b = false → q_done.count false < 3 * n)
    (hb_true : b = true → q_done.count true < q_done.count false / 3) :
    let s' := decStep (ls, st, acc) b
    DecInv (q_done ++ [b]) s'.1 s'.2.1 s'.2.2 := by
  have hls_inv : LabelsInv ls := by
    rw [hinv.ls_eq]
    exact (labelsInv_allLabels n).sublist (List.drop_sublist _ _)
  cases b
  · -- b = false
    have hlt : q_done.count false < 3 * n := hb_false rfl
    have hls_ne : ls ≠ [] := by
      intro h0
      have hlen : ls.length = 3 * n - q_done.count false := by
        rw [hinv.ls_eq, List.length_drop, length_allLabels]
      rw [h0] at hlen; simp at hlen; omega
    rcases ls with _ | ⟨⟨c, flag⟩, ls'⟩
    · exact absurd rfl hls_ne
    have hls'_eq : ls' = (allLabels n).drop (q_done.count false + 1) := by
      have h1 := hinv.ls_eq
      have h2 := List.drop_eq_getElem_cons (l := allLabels n) (i := q_done.count false)
        (by rw [length_allLabels]; omega)
      rw [h2] at h1
      exact List.cons.inj h1 |>.2
    have hcnt_f : (q_done ++ [false]).count false = q_done.count false + 1 := by simp
    have hcnt_t : (q_done ++ [false]).count true = q_done.count true := by simp
    have hpair := List.pairwise_cons.mp hls_inv
    have hst_gt_c : ∀ x ∈ st, c < x := fun x hx => hinv.st_gt_ls x hx (c, flag) (by simp)
    have hc_le_acc : ∀ a ∈ acc, c ≤ a := fun a ha => hinv.ls_le_acc (c, flag) (by simp) a ha
    have hls'_le_c : ∀ y ∈ ls', y.1 ≤ c := fun y hy => (hpair.1 y hy).1
    have hflag_mod : flag = decide (q_done.count false % 3 ≠ 2) := by
      have hget : ∀ (L : List (Fin n)) (k : ℕ) (hk : k < (L.flatMap (fun c => [(c, true), (c, true), (c, false)])).length),
          ((L.flatMap (fun c => [(c, true), (c, true), (c, false)]))[k]'hk).2 = decide (k % 3 ≠ 2) := by
        intro L
        induction L with
        | nil => intro k hk; simp at hk
        | cons a L' ih =>
          intro k hk
          simp only [List.flatMap_cons, List.cons_append, List.nil_append] at hk ⊢
          rcases k with _ | _ | _ | k
          · rfl
          · rfl
          · rfl
          · have hk' : k < (L'.flatMap (fun c => [(c, true), (c, true), (c, false)])).length := by
              simp only [List.length_cons] at hk; omega
            have hmod : (k + 1 + 1 + 1) % 3 = k % 3 := by omega
            simpa [hmod] using ih k hk'
      have h1 := hinv.ls_eq
      have h2 := List.drop_eq_getElem_cons (l := allLabels n) (i := q_done.count false)
        (by rw [length_allLabels]; omega)
      rw [h2] at h1
      have hhead : (c, flag) = (allLabels n)[q_done.count false]'(by rw [length_allLabels]; omega) :=
        List.cons.inj h1 |>.1
      have hflag_eq : flag = ((allLabels n)[q_done.count false]'(by rw [length_allLabels]; omega)).2 :=
        congrArg Prod.snd hhead
      rw [hflag_eq]
      exact hget (List.finRange n).reverse (q_done.count false) (by
        change _ < (allLabels n).length; rw [length_allLabels]; omega)
    cases flag
    · -- flag = false: push c onto st
      have hmod2 : q_done.count false % 3 = 2 := by
        by_contra hne; simp [hne] at hflag_mod
      have hdiv_succ : (q_done.count false + 1) / 3 = q_done.count false / 3 + 1 := by omega
      have hls'_lt_c : ∀ y ∈ ls', y.1 < c := fun y hy => (hpair.1 y hy).2 rfl
      have hseen_eq : seenAt ls' (c :: st) = seenAt ((c, false) :: ls') st := by
        ext z
        simp only [seenAt, Finset.mem_union, List.mem_toFinset, List.mem_cons, List.filter_cons,
          Bool.not_false, ↓reduceIte, List.map_cons]
        tauto
      refine ⟨by simpa [decStep, hcnt_f] using hls'_eq, by omega, ?_, ?_, ?_, ?_,
        hinv.avoid, ?_, ?_, ?_⟩
      · simp only [decStep, hcnt_f, hcnt_t, List.length_cons, hdiv_succ]
        have := hinv.st_len; omega
      · exact List.pairwise_cons.mpr ⟨hst_gt_c, hinv.st_sorted⟩
      · intro x hx y hy
        simp only [decStep, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hls'_lt_c y hy
        · exact hinv.st_gt_ls x hx y (List.mem_cons_of_mem _ hy)
      · intro y hy a ha
        exact hinv.ls_le_acc y (List.mem_cons_of_mem _ hy) a ha
      · intro x hx j k hj hk hjk hxj
        simp only [decStep, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hc_le_acc acc[k] (List.getElem_mem hk)
        · exact hinv.stack_inv x hx j k hj hk hjk hxj
      · simp only [decStep]
        have hp := hinv.perm_all
        simp only [List.map_cons, List.cons_append] at hp
        calc ls'.map Prod.fst ++ (c :: st) ++ acc
            ~ (c :: (ls'.map Prod.fst ++ st)) ++ acc := (List.perm_middle).append_right acc
          _ = c :: (ls'.map Prod.fst ++ st ++ acc) := by simp [List.append_assoc]
          _ ~ (allLabels n).map Prod.fst := hp
      · simp only [decStep, List.reverse_append, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.cons_append]
        rw [hseen_eq, runFwd_cons_st_of_le c acc st _ hc_le_acc, hinv.fwd_eq]
    · -- flag = true: prepend c to acc
      have hmod_ne2 : q_done.count false % 3 ≠ 2 := by
        intro h2; simp [h2] at hflag_mod
      have hdiv_eq : (q_done.count false + 1) / 3 = q_done.count false / 3 := by omega
      have hc_mem_ls' : (c, false) ∈ ls' := by
        -- Because flag = true means position % 3 ∈ {0, 1}, so (c, false) appears 1 or 2 steps later in allLabels!
        have hlen_all := length_allLabels n
        have hk3 : q_done.count false / 3 < n := by omega
        have hblk : ∀ (L : List (Fin n)) (k : ℕ), k % 3 ≠ 2 → k < 3 * L.length →
            ∃ a, ((L.flatMap (fun d => [(d, true), (d, true), (d, false)])).drop k) =
              (a, true) :: ((L.flatMap (fun d => [(d, true), (d, true), (d, false)])).drop (k + 1)) ∧
              (a, false) ∈ (L.flatMap (fun d => [(d, true), (d, true), (d, false)])).drop (k + 1) := by
          intro L
          induction L with
          | nil => intro k _ hk; simp at hk
          | cons a L' ih =>
            intro k hne hk
            simp only [List.flatMap_cons, List.cons_append, List.nil_append]
            rcases k with _ | _ | _ | k
            · exact ⟨a, rfl, by simp⟩
            · exact ⟨a, rfl, by simp⟩
            · omega
            · have hk' : k < 3 * L'.length := by simp only [List.length_cons] at hk; omega
              have hne' : k % 3 ≠ 2 := by omega
              simpa [List.drop_succ_cons] using ih k hne' hk'
        obtain ⟨a, ha1, ha2⟩ := hblk (List.finRange n).reverse (q_done.count false) hmod_ne2 (by simp; omega)
        have h1 := hinv.ls_eq
        rw [allLabels, ha1] at h1
        have hca : c = a := congrArg Prod.fst (List.cons.inj h1).1
        subst hca
        rw [hls'_eq]
        exact ha2
      have hseen_eq : seenAt ls' st = seenAt ((c, true) :: ls') st := by
        ext z
        simp only [seenAt, Finset.mem_union, List.mem_toFinset, List.filter_cons,
          Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hc_in_seen : c ∈ seenAt ls' st := by
        simp only [seenAt, Finset.mem_union, List.mem_toFinset, List.mem_map, List.mem_filter,
          Bool.not_eq_true']
        exact Or.inr ⟨(c, false), ⟨hc_mem_ls', rfl⟩, rfl⟩
      have hpop : popLe c st = (c :: st, []) := by
        cases st with
        | nil => rfl
        | cons y ys =>
          have hcy : c < y := hst_gt_c y (by simp)
          simp [popLe, not_le.mpr hcy]
      refine ⟨by simpa [decStep, hcnt_f] using hls'_eq, by omega, ?_, hinv.st_sorted, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [decStep, hcnt_f, hcnt_t, hdiv_eq]; exact hinv.st_len
      · intro x hx y hy; exact hinv.st_gt_ls x hx y (List.mem_cons_of_mem _ hy)
      · intro y hy a ha
        simp only [decStep, List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact hls'_le_c y hy
        · exact hinv.ls_le_acc y (List.mem_cons_of_mem _ hy) a ha
      · -- Avoids231 (c :: acc)
        simp only [decStep]
        intro i j k hi hj hk hij hjk ⟨hki, hij_le⟩
        rcases i with _ | i
        · rcases k with _ | k
          · omega
          · simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hki
            have hk' : k < acc.length := by simpa using hk
            have := hc_le_acc (acc[k]'hk') (List.getElem_mem hk')
            exact not_lt.mpr this hki
        · rcases j with _ | j
          · omega
          · rcases k with _ | k
            · omega
            · simp only [List.getElem_cons_succ] at hki hij_le
              exact hinv.avoid i j k (by simpa using hi) (by simpa using hj) (by simpa using hk)
                (by omega) (by omega) ⟨hki, hij_le⟩
      · -- StackInv st (c :: acc)
        simp only [decStep]
        intro x hx j k hj hk hjk hxj
        rcases j with _ | j
        · simp only [List.getElem_cons_zero] at hxj
          exact absurd (hst_gt_c x hx) (not_lt.mpr hxj)
        · rcases k with _ | k
          · omega
          · simp only [List.getElem_cons_succ] at hxj ⊢
            exact hinv.stack_inv x hx j k (by simpa using hj) (by simpa using hk) (by omega) hxj
      · simp only [decStep]
        have hp := hinv.perm_all
        simp only [List.map_cons, List.cons_append] at hp
        calc ls'.map Prod.fst ++ st ++ (c :: acc)
            ~ c :: (ls'.map Prod.fst ++ st ++ acc) := List.perm_middle
          _ ~ (allLabels n).map Prod.fst := hp
      · simp only [decStep, List.reverse_append, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.cons_append]
        unfold runFwd
        simp only [hpop, List.length_nil, List.replicate_zero, List.nil_append, hc_in_seen,
          ↓reduceIte, Finset.insert_eq_of_mem hc_in_seen]
        rw [hseen_eq, runFwd_cons_st_of_le c acc st _ hc_le_acc, hinv.fwd_eq]
  · -- b = true: pop x from st and prepend to acc
    have hlt : q_done.count true < q_done.count false / 3 := hb_true rfl
    have hst_ne : st ≠ [] := by
      intro h0; rw [h0] at hinv; have := hinv.st_len; simp at this; omega
    rcases st with _ | ⟨x, st'⟩
    · exact absurd rfl hst_ne
    have hcnt_f : (q_done ++ [true]).count false = q_done.count false := by simp
    have hcnt_t : (q_done ++ [true]).count true = q_done.count true + 1 := by simp
    have hst_pair := List.pairwise_cons.mp hinv.st_sorted
    have hx_gt_ls : ∀ y ∈ ls, y.1 < x := fun y hy => hinv.st_gt_ls x (by simp) y hy
    have hx_not_seen : x ∉ seenAt ls st' := by
      intro hmem
      simp only [seenAt, Finset.mem_union, List.mem_toFinset, List.mem_map, List.mem_filter] at hmem
      rcases hmem with hx' | ⟨p, ⟨hp, _⟩, rfl⟩
      · exact lt_irrefl x (hst_pair.1 x hx')
      · exact lt_irrefl p.1 (hx_gt_ls p hp)
    have hseen_ins : insert x (seenAt ls st') = seenAt ls (x :: st') := by
      ext z; simp only [seenAt, Finset.mem_insert, Finset.mem_union, List.mem_toFinset, List.mem_cons]
      tauto
    have hpop : popLe x st' = (x :: st', []) := by
      cases st' with
      | nil => rfl
      | cons y ys =>
        have hxy : x < y := hst_pair.1 y (by simp)
        simp [popLe, not_le.mpr hxy]
    refine ⟨by simpa [decStep, hcnt_f] using hinv.ls_eq, by simpa [hcnt_f] using hinv.cnt_le, ?_,
      hst_pair.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [decStep, hcnt_f, hcnt_t]
      have := hinv.st_len; simp only [List.length_cons] at this; omega
    · intro z hz y hy; exact hinv.st_gt_ls z (List.mem_cons_of_mem _ hz) y hy
    · intro y hy a ha
      simp only [decStep, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact le_of_lt (hx_gt_ls y hy)
      · exact hinv.ls_le_acc y hy a ha
    · -- Avoids231 (x :: acc)
      simp only [decStep]
      intro i j k hi hj hk hij hjk ⟨hki, hij_le⟩
      rcases i with _ | i
      · rcases j with _ | j
        · omega
        · rcases k with _ | k
          · omega
          · simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hki hij_le
            have hxk := hinv.stack_inv x (by simp) j k (by simpa using hj) (by simpa using hk)
              (by omega) hij_le
            exact not_lt.mpr hxk hki
      · rcases j with _ | j
        · omega
        · rcases k with _ | k
          · omega
          · simp only [List.getElem_cons_succ] at hki hij_le
            exact hinv.avoid i j k (by simpa using hi) (by simpa using hj) (by simpa using hk)
              (by omega) (by omega) ⟨hki, hij_le⟩
    · -- StackInv st' (x :: acc)
      simp only [decStep]
      intro z hz j k hj hk hjk hzj
      rcases j with _ | j
      · simp only [List.getElem_cons_zero] at hzj
        exact absurd (hst_pair.1 z hz) (not_lt.mpr hzj)
      · rcases k with _ | k
        · omega
        · simp only [List.getElem_cons_succ] at hzj ⊢
          exact hinv.stack_inv z (List.mem_cons_of_mem _ hz) j k (by simpa using hj)
            (by simpa using hk) (by omega) hzj
    · simp only [decStep]
      have hp := hinv.perm_all
      calc ls.map Prod.fst ++ st' ++ (x :: acc)
          ~ x :: (ls.map Prod.fst ++ st' ++ acc) := List.perm_middle
        _ ~ (ls.map Prod.fst ++ (x :: st')) ++ acc :=
            (List.perm_middle.symm).append_right acc
        _ ~ (allLabels n).map Prod.fst := hp
    · simp only [decStep, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append]
      unfold runFwd
      simp only [hpop, List.length_nil, List.replicate_zero, List.nil_append, hx_not_seen,
        ↓reduceIte, hseen_ins, hinv.fwd_eq]

private lemma decodeList_spec (n : ℕ) (p : List Bool) (hp : IsDyck3List n p) :
    (∀ c : Fin n, (decodeList n p).count c = 3) ∧
    Avoids231 (decodeList n p) ∧
    (runFwd (decodeList n p) [] ∅).1 = p := by
  have hrev_inv : ∀ q1 q2 : List Bool, q1 ++ q2 = p.reverse →
      let s := decodeState q1 (allLabels n, [], [])
      DecInv q1 s.1 s.2.1 s.2.2 := by
    intro q1
    induction q1 using List.reverseRecOn with
    | nil =>
      intro _ _; exact decInv_init n
    | append_singleton q1 b ih =>
      intro q2 hq
      have hinv1 := ih (b :: q2) (by simpa [List.append_assoc] using hq)
      have hlen_p : p.length = 4 * n := hp.1
      have hct_p : p.count true = n := hp.2.1
      have hcf_p : p.count false = 3 * n := by
        have htot := list_bool_count_add p
        omega
      have hq2_pref : q2.reverse = p.take q2.length := by
        have h1 : q2.reverse ++ (b :: q1.reverse) = p := by
          have := congrArg List.reverse hq
          simpa [List.reverse_append, List.append_assoc] using this
        rw [← h1, List.take_left' (by simp)]
      have hq2_len : q2.length ≤ 4 * n := by
        have := congrArg List.length hq
        simp only [List.length_append, List.length_singleton, List.length_reverse, hlen_p] at this
        omega
      have hdyck_q2 : (p.take q2.length).count false ≤ 3 * (p.take q2.length).count true :=
        hp.2.2 q2.length hq2_len
      rw [← hq2_pref, List.count_reverse, List.count_reverse] at hdyck_q2
      have hsplit_t : q1.count true + (if b = true then 1 else 0) + q2.count true = n := by
        have := congrArg (List.count true) hq
        simp only [List.count_append, List.count_singleton, List.count_reverse, hct_p, beq_iff_eq] at this
        omega
      have hsplit_f : q1.count false + (if b = false then 1 else 0) + q2.count false = 3 * n := by
        have := congrArg (List.count false) hq
        simp only [List.count_append, List.count_singleton, List.count_reverse, hcf_p, beq_iff_eq] at this
        omega
      have hstep := decInv_step q1 _ _ _ b hinv1
        (by intro hb; subst hb; simp only [↓reduceIte] at hsplit_f; omega)
        (by intro hb; subst hb; simp only [↓reduceIte, Bool.true_eq_false] at hsplit_t hsplit_f; omega)
      simpa [decodeState, List.foldl_append] using hstep
  have hfinal := hrev_inv p.reverse [] (List.append_nil _)
  have hcf : p.reverse.count false = 3 * n := by
    rw [List.count_reverse]
    have htot := list_bool_count_add p
    have := hp.1; have := hp.2.1; omega
  have hct : p.reverse.count true = n := by rw [List.count_reverse]; exact hp.2.1
  have hls_nil : (decodeState p.reverse (allLabels n, [], [])).1 = [] := by
    rw [hfinal.ls_eq, hcf, List.drop_eq_nil_iff, length_allLabels]
  have hst_nil : (decodeState p.reverse (allLabels n, [], [])).2.1 = [] := by
    have := hfinal.st_len
    rw [hct, hcf] at this
    have h0 : (decodeState p.reverse (allLabels n, [], [])).2.1.length = 0 := by omega
    exact List.eq_nil_of_length_eq_zero h0
  have hseen_empty : seenAt (decodeState p.reverse (allLabels n, [], [])).1
      (decodeState p.reverse (allLabels n, [], [])).2.1 = ∅ := by
    rw [hls_nil, hst_nil]; simp [seenAt]
  refine ⟨?_, hfinal.avoid, ?_⟩
  · intro c
    unfold decodeList
    have hperm := hfinal.perm_all
    rw [hls_nil, hst_nil] at hperm
    simp only [List.map_nil, List.nil_append] at hperm
    rw [hperm.count_eq, count_allLabels]
  · unfold decodeList
    have hfwd := hfinal.fwd_eq
    rw [hseen_empty, hst_nil, List.reverse_reverse] at hfwd
    exact hfwd

/-! ## Part 3: Injectivity of `runFwd` on uniform avoiding words -/

private lemma runFwd_sorted_of_avoid {n : ℕ} (w st : List (Fin n)) (seen : Finset (Fin n))
    (hst : st.Pairwise (· < ·))
    (havoid : Avoids231 w)
    (hcross : ∀ y ∈ st, ∀ j k (hj : j < w.length) (hk : k < w.length),
      j < k → y ≤ w[j] → y ≤ w[k]) :
    (runFwd w st seen).2.Pairwise (· ≤ ·) := by
  induction w generalizing st seen with
  | nil =>
    simp only [runFwd]
    exact hst.imp le_of_lt
  | cons x xs ih =>
    obtain ⟨rest, h1, h2, hle_pop, hst'⟩ := popLe_head_eq x st
    have hst_rest : (x :: rest).Pairwise (· < ·) := hst' hst
    have hpop_sorted : (popLe x st).2.Pairwise (· < ·) := by
      have : (popLe x st).2 <+: st := ⟨rest, h2.symm⟩
      exact hst.sublist this.sublist
    have hcross_xs : ∀ y ∈ x :: rest, ∀ j k (hj : j < xs.length) (hk : k < xs.length),
        j < k → y ≤ xs[j] → y ≤ xs[k] := by
      intro y hy j k hj hk hjk hyj
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy_rest
      · by_contra hlt
        have hlt' : xs[k] < y := lt_of_not_ge hlt
        exact havoid 0 (j + 1) (k + 1) (by simp) (by simpa using hj) (by simpa using hk)
          (by omega) (by omega) ⟨by simpa using hlt', by simpa using hyj⟩
      · have hy_st : y ∈ st := by rw [h2]; exact List.mem_append_right _ hy_rest
        exact hcross y hy_st (j + 1) (k + 1) (by simpa using hj) (by simpa using hk)
          (by omega) (by simpa using hyj)
    have havoid_xs : Avoids231 xs := by
      intro i j k hi hj hk hij hjk
      exact havoid (i + 1) (j + 1) (k + 1) (by simpa using hi) (by simpa using hj)
        (by simpa using hk) (by omega) (by omega)
    have hout_xs : (runFwd xs (popLe x st).1 (insert x seen)).2.Pairwise (· ≤ ·) := by
      rw [h1]; exact ih (x :: rest) (insert x seen) hst_rest havoid_xs hcross_xs
    have hpop_le_rest : ∀ y ∈ (popLe x st).2, ∀ z ∈ (runFwd xs (popLe x st).1 (insert x seen)).2,
        y ≤ z := by
      intro y hy z hz
      have hperm := runFwd_out_perm xs (popLe x st).1 (insert x seen)
      have hz_mem : z ∈ xs ++ (popLe x st).1 := hperm.subset hz
      rw [h1] at hz_mem
      simp only [List.mem_append, List.mem_cons] at hz_mem
      rcases hz_mem with hz_xs | rfl | hz_rest
      · obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hz_xs
        have hy_st : y ∈ st := by rw [h2]; exact List.mem_append_left _ hy
        exact hcross y hy_st 0 (idx + 1) (by simp) (by simpa using hidx) (by omega)
          (by simpa using hle_pop y hy)
      · exact hle_pop y hy
      · have hpw : ((popLe x st).2 ++ rest).Pairwise (· < ·) := by rwa [← h2]
        exact le_of_lt ((List.pairwise_append.mp hpw).2.2 y hy z hz_rest)
    unfold runFwd
    have hval : (if x ∈ seen then
        (List.replicate (popLe x st).2.length false ++ (runFwd xs (popLe x st).1 (insert x seen)).1,
         (popLe x st).2 ++ (runFwd xs (popLe x st).1 (insert x seen)).2)
      else
        (List.replicate (popLe x st).2.length false ++ true :: (runFwd xs (popLe x st).1 (insert x seen)).1,
         (popLe x st).2 ++ (runFwd xs (popLe x st).1 (insert x seen)).2)).2 =
        (popLe x st).2 ++ (runFwd xs (popLe x st).1 (insert x seen)).2 := by
      split_ifs <;> rfl
    rw [hval, List.pairwise_append]
    exact ⟨hpop_sorted.imp le_of_lt, hout_xs, hpop_le_rest⟩

private def popLeT {n : ℕ} (x : Fin n) (flag : Bool) :
    List (Fin n × Bool) → List (Fin n × Bool) × List (Fin n × Bool)
  | [] => ([(x, flag)], [])
  | y :: ys =>
    if y.1 ≤ x then
      let r := popLeT x flag ys
      (r.1, y :: r.2)
    else
      ((x, flag) :: y :: ys, [])

private def runFwdT {n : ℕ} :
    List (Fin n) → List (Fin n × Bool) → Finset (Fin n) → List Bool × List (Fin n × Bool)
  | [], st, _ => (List.replicate st.length false, st)
  | x :: xs, st, seen =>
    let flag := decide (x ∈ seen)
    let r := popLeT x flag st
    let ds := List.replicate r.2.length false
    let res := runFwdT xs r.1 (insert x seen)
    if x ∈ seen then
      (ds ++ res.1, r.2 ++ res.2)
    else
      (ds ++ true :: res.1, r.2 ++ res.2)

private lemma popLeT_fst {n : ℕ} (x : Fin n) (flag : Bool) (st : List (Fin n × Bool)) :
    (popLeT x flag st).1.map Prod.fst = (popLe x (st.map Prod.fst)).1 ∧
    (popLeT x flag st).2.map Prod.fst = (popLe x (st.map Prod.fst)).2 := by
  induction st with
  | nil => simp [popLeT, popLe]
  | cons y ys ih =>
    simp only [popLeT, List.map_cons, popLe]
    split_ifs
    · exact ⟨ih.1, by simp [ih.2]⟩
    · simp

private lemma runFwdT_eq_runFwd {n : ℕ} (w : List (Fin n)) (st : List (Fin n × Bool))
    (seen : Finset (Fin n)) :
    (runFwdT w st seen).1 = (runFwd w (st.map Prod.fst) seen).1 ∧
    (runFwdT w st seen).2.map Prod.fst = (runFwd w (st.map Prod.fst) seen).2 := by
  induction w generalizing st seen with
  | nil => simp [runFwdT, runFwd]
  | cons x xs ih =>
    unfold runFwdT runFwd
    have hp := popLeT_fst x (decide (x ∈ seen)) st
    have hlen : (popLeT x (decide (x ∈ seen)) st).2.length =
        (popLe x (st.map Prod.fst)).2.length := by
      rw [← List.length_map Prod.fst, hp.2]
    have hrec := ih (popLeT x (decide (x ∈ seen)) st).1 (insert x seen)
    rw [hp.1] at hrec
    split_ifs <;> simp [hlen, hrec.1, hrec.2, hp.2]

private lemma popLeT_head {n : ℕ} (x : Fin n) (flag : Bool) (st : List (Fin n × Bool)) :
    ∃ rest : List (Fin n × Bool), (popLeT x flag st).1 = (x, flag) :: rest ∧
      st = (popLeT x flag st).2 ++ rest ∧
      (∀ y ∈ (popLeT x flag st).2, y.1 ≤ x) := by
  induction st with
  | nil => exact ⟨[], rfl, rfl, by simp [popLeT]⟩
  | cons y ys ih =>
    unfold popLeT
    split_ifs with hle
    · obtain ⟨rest, h1, h2, h3⟩ := ih
      refine ⟨rest, h1, by rw [List.cons_append]; exact congrArg (y :: ·) h2, ?_⟩
      intro z hz; simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hle
      · exact h3 z hz
    · exact ⟨y :: ys, rfl, rfl, by simp⟩

private lemma decodeState_append {n : ℕ} (q1 q2 : List Bool)
    (s : List (Fin n × Bool) × List (Fin n) × List (Fin n)) :
    decodeState (q1 ++ q2) s = decodeState q2 (decodeState q1 s) :=
  List.foldl_append

private lemma decodeState_replicate_false_allFalse {n : ℕ}
    (L : List (Fin n × Bool)) (lsRest : List (Fin n × Bool)) (st acc : List (Fin n))
    (hall : ∀ p ∈ L, p.2 = false) :
    decodeState (List.replicate L.length false) (L.reverse ++ lsRest, st, acc) =
      (lsRest, L.map Prod.fst ++ st, acc) := by
  induction L generalizing lsRest st with
  | nil => simp [decodeState]
  | cons a L' ih =>
    have ha : a.2 = false := hall a (by simp)
    have hL' : ∀ p ∈ L', p.2 = false := fun p hp => hall p (List.mem_cons_of_mem _ hp)
    have hrep : List.replicate (a :: L').length false = List.replicate L'.length false ++ [false] := by
      simp [List.replicate_succ']
    rw [hrep, decodeState_append, List.reverse_cons, List.append_assoc, List.singleton_append]
    rw [ih (a :: lsRest) st hL']
    rcases a with ⟨c, f⟩
    simp only at ha; subst ha
    simp [decodeState, decStep]

private lemma decodeState_runFwdT {n : ℕ} (w : List (Fin n)) (stT : List (Fin n × Bool))
    (seen : Finset (Fin n)) (lsRest : List (Fin n × Bool))
    (hseen_st : ∀ p ∈ stT, p.1 ∈ seen)
    (hst_pw : (stT.map Prod.fst).Pairwise (· < ·))
    (havoid : Avoids231 w)
    (hseen_mono : ∀ c ∈ seen, ∀ k (hk : k < w.length), w[k] = c →
      ∀ m (hm : m < w.length), k < m → c ≤ w[m])
    (hcross : ∀ y ∈ stT.map Prod.fst, ∀ j k (hj : j < w.length) (hk : k < w.length),
      j < k → y ≤ w[j] → y ≤ w[k])
    (hst_tail_false : ∀ p ∈ stT.tail, p.2 = false)
    (hst_head_true : ∀ top rest, stT = (top, true) :: rest → ∀ a ∈ w, top ≤ a) :
    decodeState (runFwdT w stT seen).1.reverse ((runFwdT w stT seen).2.reverse ++ lsRest, [], []) =
      match stT with
      | (top, true) :: rest => (lsRest, rest.map Prod.fst, top :: w)
      | _ => (lsRest, stT.map Prod.fst, w) := by
  induction w generalizing stT seen lsRest with
  | nil =>
    simp only [runFwdT, List.reverse_replicate]
    cases stT with
    | nil => simp [decodeState]
    | cons hd tl =>
      rcases hd with ⟨top, fl⟩
      have htl_false : ∀ p ∈ tl, p.2 = false := hst_tail_false
      cases fl
      · have hall : ∀ p ∈ (top, false) :: tl, p.2 = false := by
          intro p hp; simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · rfl
          · exact htl_false p hp
        simpa using decodeState_replicate_false_allFalse ((top, false) :: tl) lsRest [] [] hall
      · have hrep : List.replicate ((top, true) :: tl).length false =
            List.replicate tl.length false ++ [false] := by simp [List.replicate_succ']
        rw [hrep, decodeState_append, List.reverse_cons, List.append_assoc, List.singleton_append]
        rw [decodeState_replicate_false_allFalse tl ((top, true) :: lsRest) [] [] htl_false]
        simp [decodeState, decStep]
  | cons x xs ih =>
    obtain ⟨rest, hr1, hr2, hle_pop⟩ := popLeT_head x (decide (x ∈ seen)) stT
    have hst_map := popLeT_fst x (decide (x ∈ seen)) stT
    have hpop_head_eq := popLe_head_eq x (stT.map Prod.fst)
    obtain ⟨restF, hrf1, hrf2, _, hrf_pw⟩ := hpop_head_eq
    have hst'_pw : ((popLeT x (decide (x ∈ seen)) stT).1.map Prod.fst).Pairwise (· < ·) := by
      rw [hst_map.1, hrf1]; exact hrf_pw hst_pw
    have hseen_st' : ∀ p ∈ (popLeT x (decide (x ∈ seen)) stT).1, p.1 ∈ insert x seen := by
      intro p hp
      rw [hr1] at hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact Finset.mem_insert_self x seen
      · exact Finset.mem_insert_of_mem (hseen_st p (by rw [hr2]; exact List.mem_append_right _ hp))
    have havoid_xs : Avoids231 xs := by
      intro i j k hi hj hk hij hjk
      exact havoid (i + 1) (j + 1) (k + 1) (by simpa using hi) (by simpa using hj)
        (by simpa using hk) (by omega) (by omega)
    have hseen_mono_xs : ∀ c ∈ insert x seen, ∀ k (hk : k < xs.length), xs[k] = c →
        ∀ m (hm : m < xs.length), k < m → c ≤ xs[m] := by
      intro c hc k hk hxk m hm hkm
      rcases Finset.mem_insert.mp hc with rfl | hc_old
      · by_contra hlt
        have hlt' : xs[m] < c := lt_of_not_ge hlt
        exact havoid 0 (k + 1) (m + 1) (by simp) (by simpa using hk) (by simpa using hm)
          (by omega) (by omega) ⟨by simpa using hlt', by simp [hxk]⟩
      · exact hseen_mono c hc_old (k + 1) (by simpa using hk) (by simpa using hxk) (m + 1)
          (by simpa using hm) (by omega)
    have hcross_xs : ∀ y ∈ (popLeT x (decide (x ∈ seen)) stT).1.map Prod.fst,
        ∀ j k (hj : j < xs.length) (hk : k < xs.length), j < k → y ≤ xs[j] → y ≤ xs[k] := by
      intro y hy j k hj hk hjk hyj
      rw [hr1, List.map_cons] at hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy_rest
      · by_contra hlt
        have hlt' : xs[k] < y := lt_of_not_ge hlt
        exact havoid 0 (j + 1) (k + 1) (by simp) (by simpa using hj) (by simpa using hk)
          (by omega) (by omega) ⟨by simpa using hlt', by simpa using hyj⟩
      · have hy_st : y ∈ stT.map Prod.fst := by
          rw [hr2, List.map_append]; exact List.mem_append_right _ hy_rest
        exact hcross y hy_st (j + 1) (k + 1) (by simpa using hj) (by simpa using hk)
          (by omega) (by simpa using hyj)
    -- If stT = (top, true) :: tl, then top ≤ x, so (top, true) is popped into (popLeT x _ stT).2!
    -- Therefore rest is a sublist of stT.tail, so EVERY element of rest has flag = false!
    have hrest_false : ∀ p ∈ rest, p.2 = false := by
      intro p hp
      cases stT with
      | nil =>
        have : rest = [] := by simp [popLeT] at hr1; exact hr1
        subst this; simp at hp
      | cons hd tl =>
        rcases hd with ⟨top, fl⟩
        cases fl
        · have hmem : p ∈ (top, false) :: tl := by rw [hr2]; exact List.mem_append_right _ hp
          simp only [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · rfl
          · exact hst_tail_false p hmem
        · have htop_le : top ≤ x := hst_head_true top tl rfl x (by simp)
          have hpop_cons : (popLeT x (decide (x ∈ seen)) ((top, true) :: tl)).2 =
              (top, true) :: (popLeT x (decide (x ∈ seen)) tl).2 := by
            simp [popLeT, htop_le]
          rw [hpop_cons, List.cons_append] at hr2
          have htl_eq : tl = (popLeT x (decide (x ∈ seen)) tl).2 ++ rest := (List.cons.inj hr2).2
          exact hst_tail_false p (by rw [htl_eq]; exact List.mem_append_right _ hp)
    have hst'_tail_false : ∀ p ∈ (popLeT x (decide (x ∈ seen)) stT).1.tail, p.2 = false := by
      rw [hr1]; exact hrest_false
    have hst'_head_true : ∀ top r', (popLeT x (decide (x ∈ seen)) stT).1 = (top, true) :: r' →
        ∀ a ∈ xs, top ≤ a := by
      intro top r' hEq a ha
      rw [hr1] at hEq
      have htop : x = top := congrArg Prod.fst (List.cons.inj hEq).1
      have hfl : decide (x ∈ seen) = true := congrArg Prod.snd (List.cons.inj hEq).1
      subst htop
      have hx_seen : x ∈ seen := of_decide_eq_true hfl
      obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem ha
      exact hseen_mono x hx_seen 0 (by simp) (by simp) (idx + 1) (by simpa using hidx) (by omega)
    have hrec := ih (popLeT x (decide (x ∈ seen)) stT).1 (insert x seen)
      ((popLeT x (decide (x ∈ seen)) stT).2.reverse ++ lsRest)
      hseen_st' hst'_pw havoid_xs hseen_mono_xs hcross_xs hst'_tail_false hst'_head_true
    -- Now trace runFwdT (x :: xs) stT seen!
    have hafter_x :
        decodeState (runFwdT (x :: xs) stT seen).1.reverse
          ((runFwdT (x :: xs) stT seen).2.reverse ++ lsRest, [], []) =
        decodeState (List.replicate (popLeT x (decide (x ∈ seen)) stT).2.length false)
          ((popLeT x (decide (x ∈ seen)) stT).2.reverse ++ lsRest, rest.map Prod.fst, x :: xs) := by
      unfold runFwdT
      by_cases hx : x ∈ seen
      · rw [if_pos hx]
        simp only [List.reverse_append, List.reverse_replicate, List.append_assoc]
        rw [decodeState_append, hrec, hr1]
        simp [hx]
      · rw [if_neg hx]
        simp only [List.reverse_append, List.reverse_cons, List.reverse_replicate,
          List.append_assoc, List.cons_append]
        rw [decodeState_append, hrec, hr1]
        simp only [hx, decide_false, List.nil_append, List.map_cons, decodeState, List.foldl_cons, decStep]
    rw [hafter_x]
    -- Finally process the popped prefix!
    cases stT with
    | nil =>
      have : rest = [] := by simp [popLeT] at hr1; exact hr1
      subst this
      simp [popLeT, decodeState]
    | cons hd tl =>
      rcases hd with ⟨top, fl⟩
      cases fl
      · -- All of stT has flag = false, so all of popped has flag = false!
        have hpop_false : ∀ p ∈ (popLeT x (decide (x ∈ seen)) ((top, false) :: tl)).2, p.2 = false := by
          intro p hp
          have hmem : p ∈ (top, false) :: tl := by rw [hr2]; exact List.mem_append_left _ hp
          simp only [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · rfl
          · exact hst_tail_false p hmem
        rw [decodeState_replicate_false_allFalse _ lsRest _ _ hpop_false]
        have hmap : ((popLeT x (decide (x ∈ seen)) ((top, false) :: tl)).2 ++ rest).map Prod.fst =
            ((top, false) :: tl).map Prod.fst := by rw [← hr2]
        rw [← List.map_append, hmap]
      · -- (top, true) is popped first, and the rest of popped has flag = false!
        have htop_le : top ≤ x := hst_head_true top tl rfl x (by simp)
        have hpop_cons : (popLeT x (decide (x ∈ seen)) ((top, true) :: tl)).2 =
            (top, true) :: (popLeT x (decide (x ∈ seen)) tl).2 := by
          simp [popLeT, htop_le]
        rw [hpop_cons]
        have htl_eq : tl = (popLeT x (decide (x ∈ seen)) tl).2 ++ rest := by
          rw [hpop_cons, List.cons_append] at hr2
          exact (List.cons.inj hr2).2
        have hpop2_false : ∀ p ∈ (popLeT x (decide (x ∈ seen)) tl).2, p.2 = false := by
          intro p hp
          exact hst_tail_false p (by rw [htl_eq]; exact List.mem_append_left _ hp)
        have hrep : List.replicate ((top, true) :: (popLeT x (decide (x ∈ seen)) tl).2).length false =
            List.replicate (popLeT x (decide (x ∈ seen)) tl).2.length false ++ [false] := by
          simp [List.replicate_succ']
        rw [hrep, decodeState_append, List.reverse_cons, List.append_assoc, List.singleton_append]
        rw [decodeState_replicate_false_allFalse _ ((top, true) :: lsRest) _ _ hpop2_false]
        simp only [decodeState, List.foldl_cons, List.foldl_nil, decStep]
        have hmap : ((popLeT x (decide (x ∈ seen)) tl).2 ++ rest).map Prod.fst = tl.map Prod.fst := by
          rw [← htl_eq]
        rw [← List.map_append, hmap]

private lemma runFwdT_out_eq_allLabels_reverse {n : ℕ} (w : List (Fin n))
    (hcnt : ∀ c : Fin n, w.count c = 3) (havoid : Avoids231 w) :
    (runFwdT w [] ∅).2.reverse = allLabels n := by
  -- First, the .fst projection is sorted and has count 3 for every c, so it equals (allLabels n).reverse.map Prod.fst!
  have hrf := runFwdT_eq_runFwd w [] ∅
  have hsort_fst : ((runFwdT w [] ∅).2.map Prod.fst).Pairwise (· ≤ ·) := by
    rw [hrf.2]
    exact runFwd_sorted_of_avoid w [] ∅ List.Pairwise.nil havoid (by simp)
  have hperm_fst : (runFwdT w [] ∅).2.map Prod.fst ~ w := by
    rw [hrf.2]; simpa using runFwd_out_perm w [] ∅
  -- Second, for every c, the subsequence of (runFwdT w [] ∅).2 with .fst = c is [(c, false), (c, true), (c, true)]!
  -- Because the first occurrence of c in w gets flag=false, subsequent get flag=true, and pushing c pops any earlier c!
  have hblock : ∀ (L : List (Fin n × Bool)),
      (L.map Prod.fst).Pairwise (· ≤ ·) →
      (∀ c : Fin n, (L.map Prod.fst).count c = 3) →
      (∀ c : Fin n, L.filter (fun p => p.1 == c) = [(c, false), (c, true), (c, true)]) →
      L.reverse = allLabels n := by
    intro L hpw hc hfilt
    -- Prove L = (List.finRange n).flatMap (fun c => [(c, false), (c, true), (c, true)])!
    have hL : L = (List.finRange n).flatMap (fun c => [(c, false), (c, true), (c, true)]) := by
      -- Since L.map Prod.fst is sorted with 3 copies of each c, L is the concat of its filters by c!
      have hconcat : ∀ (cs : List (Fin n)) (M : List (Fin n × Bool)),
          cs.Pairwise (· < ·) →
          (M.map Prod.fst).Pairwise (· ≤ ·) →
          (∀ p ∈ M, p.1 ∈ cs) →
          M = cs.flatMap (fun c => M.filter (fun p => p.1 == c)) := by
        intro cs
        induction cs with
        | nil =>
          intro M _ _ hmem
          cases M with
          | nil => rfl
          | cons a _ => exact absurd (hmem a (by simp)) (by simp)
        | cons c cs' ih =>
          intro M hcs hM hmem
          rw [List.flatMap_cons]
          have hcs_pair := List.pairwise_cons.mp hcs
          -- Split M into takeWhile (·.1 == c) and dropWhile (·.1 == c)
          -- Actually prove by induction on M!
          induction M with
          | nil =>
            have : cs'.flatMap (fun d => ([] : List (Fin n × Bool)).filter (fun p => p.1 == d)) = [] := by
              simp
            simp [this]
          | cons a M' ihM =>
            have ha_mem : a.1 ∈ c :: cs' := hmem a (by simp)
            have hM'_pw : (M'.map Prod.fst).Pairwise (· ≤ ·) := (List.pairwise_cons.mp hM).2
            have hM'_mem : ∀ p ∈ M', p.1 ∈ c :: cs' := fun p hp => hmem p (List.mem_cons_of_mem _ hp)
            simp only [List.mem_cons] at ha_mem
            rcases ha_mem with ha_eq | ha_in
            · -- a.1 = c
              have hnot_in : ∀ d ∈ cs', (a :: M').filter (fun p => p.1 == d) = M'.filter (fun p => p.1 == d) := by
                intro d hd
                have hne : a.1 ≠ d := by rw [ha_eq]; exact ne_of_lt (hcs_pair.1 d hd)
                simp [List.filter_cons, hne]
              have hflat_eq : cs'.flatMap (fun d => (a :: M').filter (fun p => p.1 == d)) =
                  cs'.flatMap (fun d => M'.filter (fun p => p.1 == d)) := by
                refine List.flatMap_congr ?_
                intro d hd; exact hnot_in d hd
              rw [hflat_eq]
              simp only [List.filter_cons, ha_eq, beq_self_eq_true, ↓reduceIte,
                List.cons_append]
              congr 1
              exact ihM hM'_pw hM'_mem
            · -- a.1 ∈ cs', so c < a.1, hence ALL of (a :: M') has .1 > c, so filter (· == c) = []!
              have hca : c < a.1 := hcs_pair.1 a.1 ha_in
              have hall_gt : ∀ p ∈ a :: M', c < p.1 := by
                intro p hp
                simp only [List.mem_cons] at hp
                rcases hp with rfl | hp
                · exact hca
                · exact lt_of_lt_of_le hca ((List.pairwise_cons.mp hM).1 p.1 (List.mem_map_of_mem hp))
              have hf0 : (a :: M').filter (fun p => p.1 == c) = [] := by
                rw [List.filter_eq_nil_iff]
                intro p hp; simp [ne_of_gt (hall_gt p hp)]
              rw [hf0, List.nil_append]
              refine ih (a :: M') hcs_pair.2 hM ?_
              intro p hp
              have := hmem p hp
              simp only [List.mem_cons] at this
              exact this.resolve_left (ne_of_gt (hall_gt p hp))
      rw [hconcat (List.finRange n) L (List.pairwise_lt_finRange n) hpw (fun p _ => List.mem_finRange p.1)]
      refine List.flatMap_congr ?_
      intro c _; exact hfilt c
    rw [hL, allLabels, List.reverse_flatMap]
    congr 1
  have hpop_rest_gt : ∀ (x : Fin n) (fl : Bool) (stT : List (Fin n × Bool)) (rest : List (Fin n × Bool)),
      (stT.map Prod.fst).Pairwise (· < ·) →
      (popLeT x fl stT).1 = (x, fl) :: rest →
      ∀ q ∈ rest, x < q.1 := by
    intro x fl stT rest hpw h1 q hq
    have hfst := popLeT_fst x fl stT
    have hph := popLe_head_eq x (stT.map Prod.fst)
    obtain ⟨restF, hrF1, _, _, hpw'⟩ := hph
    have hmap : ((x, fl) :: rest).map Prod.fst = x :: restF := by
      rw [← h1, hfst.1, hrF1]
    have hpw_x : (x :: rest.map Prod.fst).Pairwise (· < ·) := by
      rw [← List.map_cons (f := Prod.fst) (a := (x, fl)), hmap]
      exact hpw' hpw
    exact (List.pairwise_cons.mp hpw_x).1 q.1 (List.mem_map_of_mem hq)
  have hfilt_gen : ∀ (w' : List (Fin n)) (stT : List (Fin n × Bool)) (seen : Finset (Fin n)) (c : Fin n),
      (stT.map Prod.fst).Pairwise (· < ·) →
      (∀ p ∈ stT, p.1 = c → c ∈ seen) →
      (c ∈ seen →
        (runFwdT w' stT seen).2.filter (fun p => p.1 == c) =
          stT.filter (fun p => p.1 == c) ++ List.replicate (w'.count c) (c, true)) ∧
      (c ∉ seen →
        (runFwdT w' stT seen).2.filter (fun p => p.1 == c) =
          if w'.count c = 0 then [] else (c, false) :: List.replicate (w'.count c - 1) (c, true)) := by
    intro w'
    induction w' with
    | nil =>
      intro stT seen c _ hst_c
      constructor
      · intro _; simp [runFwdT]
      · intro hnot
        have hnil : stT.filter (fun p => p.1 == c) = [] := by
          rw [List.filter_eq_nil_iff]
          intro p hp; simp only [beq_iff_eq]; intro heq; exact hnot (hst_c p hp heq)
        simp [runFwdT, hnil]
    | cons x xs ih =>
      intro stT seen c hpw hst_c
      obtain ⟨rest, hr1, hr2, _⟩ := popLeT_head x (decide (x ∈ seen)) stT
      have hfst := popLeT_fst x (decide (x ∈ seen)) stT
      obtain ⟨restF, hrF1, _, _, hpw'⟩ := popLe_head_eq x (stT.map Prod.fst)
      have hpw_next : ((popLeT x (decide (x ∈ seen)) stT).1.map Prod.fst).Pairwise (· < ·) := by
        rw [hfst.1, hrF1]; exact hpw' hpw
      have hst_c_next : ∀ p ∈ (popLeT x (decide (x ∈ seen)) stT).1, p.1 = c → c ∈ insert x seen := by
        intro p hp hpc
        rw [hr1] at hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · simp only at hpc; subst hpc; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hst_c p (by rw [hr2]; exact List.mem_append_right _ hp) hpc)
      have hih := ih (popLeT x (decide (x ∈ seen)) stT).1 (insert x seen) c hpw_next hst_c_next
      have hst_split : stT.filter (fun p => p.1 == c) =
          (popLeT x (decide (x ∈ seen)) stT).2.filter (fun p => p.1 == c) ++
          rest.filter (fun p => p.1 == c) := by
        conv_lhs => rw [hr2]
        rw [List.filter_append]
      have hout_eq : (runFwdT (x :: xs) stT seen).2 =
          (popLeT x (decide (x ∈ seen)) stT).2 ++
          (runFwdT xs (popLeT x (decide (x ∈ seen)) stT).1 (insert x seen)).2 := by
        conv_lhs => unfold runFwdT
        dsimp only; split_ifs <;> rfl
      rw [hout_eq, List.filter_append]
      by_cases hxc : x = c
      · subst hxc
        have hrest_nil : rest.filter (fun p => p.1 == x) = [] := by
          rw [List.filter_eq_nil_iff]
          intro q hq; simp [ne_of_gt (hpop_rest_gt x _ stT rest hpw hr1 q hq)]
        have hpop_eq : (popLeT x (decide (x ∈ seen)) stT).2.filter (fun p => p.1 == x) =
            stT.filter (fun p => p.1 == x) := by
          rw [hst_split, hrest_nil, List.append_nil]
        have hrec := hih.1 (Finset.mem_insert_self x seen)
        rw [hr1] at hrec
        simp only [List.filter_cons, beq_self_eq_true, ↓reduceIte, hrest_nil] at hrec
        rw [hpop_eq, hr1, hrec]
        constructor
        · intro hx
          simp [hx, List.count_cons, List.replicate_succ]
        · intro hnx
          have hst_nil : stT.filter (fun p => p.1 == x) = [] := by
            rw [List.filter_eq_nil_iff]
            intro p hp; simp only [beq_iff_eq]; intro heq; exact hnx (hst_c p hp heq)
          simp [hnx, hst_nil, List.count_cons]
      · have hnext_filt : (popLeT x (decide (x ∈ seen)) stT).1.filter (fun p => p.1 == c) =
            rest.filter (fun p => p.1 == c) := by
          rw [hr1, List.filter_cons]; simp [hxc]
        have hcnt_eq : (x :: xs).count c = xs.count c := by
          simp [List.count_cons, beq_iff_eq, hxc]
        constructor
        · intro hc
          have hrec := hih.1 (Finset.mem_insert_of_mem hc)
          rw [hnext_filt] at hrec
          rw [hrec, ← List.append_assoc, ← hst_split, hcnt_eq]
        · intro hnc
          have hnc' : c ∉ insert x seen := by
            simp only [Finset.mem_insert, not_or]; exact ⟨Ne.symm hxc, hnc⟩
          have hst_nil : stT.filter (fun p => p.1 == c) = [] := by
            rw [List.filter_eq_nil_iff]
            intro p hp; simp only [beq_iff_eq]; intro heq; exact hnc (hst_c p hp heq)
          have hpop_nil : (popLeT x (decide (x ∈ seen)) stT).2.filter (fun p => p.1 == c) = [] := by
            rw [hst_nil] at hst_split
            exact (List.append_eq_nil_iff.mp hst_split.symm).1
          rw [hpop_nil, List.nil_append, hih.2 hnc', hcnt_eq]
  refine hblock (runFwdT w [] ∅).2 hsort_fst (fun c => by rw [hperm_fst.count_eq, hcnt c]) ?_
  intro c
  have h := (hfilt_gen w [] ∅ c List.Pairwise.nil (by simp)).2 (by simp)
  rw [hcnt c] at h
  simpa using h

private lemma decodeList_runFwd {n : ℕ} (w : List (Fin n))
    (hcnt : ∀ c : Fin n, w.count c = 3) (havoid : Avoids231 w) :
    decodeList n (runFwd w [] ∅).1 = w := by
  unfold decodeList
  have hrf := runFwdT_eq_runFwd w [] ∅
  have hout := runFwdT_out_eq_allLabels_reverse w hcnt havoid
  have hdec := decodeState_runFwdT w [] ∅ [] (by simp) List.Pairwise.nil havoid
    (by simp) (by simp) (by simp) (by intro _ _ h; cases h)
  simp only [List.append_nil, List.map_nil] at hrf hdec
  rw [hrf.1] at *
  rw [← hout, hdec]

private lemma list_length_eq_sum_count {n : ℕ} (w : List (Fin n)) :
    w.length = ∑ c : Fin n, w.count c := by
  induction w with
  | nil => simp
  | cons a as ih =>
    rw [List.length_cons, ih]
    have h1 : ∀ c : Fin n, (a :: as).count c = as.count c + if a = c then 1 else 0 := by
      intro c; simp [List.count_cons, beq_iff_eq]
    simp_rw [h1, Finset.sum_add_distrib]
    simp

private lemma length_le_three_mul_card {n : ℕ} (L : List (Fin n)) (S : Finset (Fin n))
    (hmem : ∀ y ∈ L, y ∈ S) (hcnt : ∀ c : Fin n, L.count c ≤ 3) :
    L.length ≤ 3 * S.card := by
  have hsum : L.length = ∑ c ∈ S, L.count c := by
    induction L with
    | nil => simp
    | cons a as ih =>
      have ha : a ∈ S := hmem a (by simp)
      have has : ∀ y ∈ as, y ∈ S := fun y hy => hmem y (List.mem_cons_of_mem _ hy)
      have hcnt' : ∀ c : Fin n, as.count c ≤ 3 := fun c => le_trans (by simp [List.count_cons]) (hcnt c)
      rw [List.length_cons, ih has hcnt']
      have h1 : ∀ c : Fin n, (a :: as).count c = as.count c + if a = c then 1 else 0 := by
        intro c; simp [List.count_cons, beq_iff_eq]
      simp_rw [h1, Finset.sum_add_distrib]
      have h2 : (∑ c ∈ S, if a = c then 1 else 0) = 1 := by
        simp [ha]
      omega
  rw [hsum]
  calc ∑ c ∈ S, L.count c ≤ ∑ _c ∈ S, 3 := Finset.sum_le_sum (fun c _ => hcnt c)
    _ = 3 * S.card := by simp [mul_comm]

private lemma runFwd_prefix_bound {n : ℕ} (w st outBefore : List (Fin n)) (seen : Finset (Fin n))
    (hst_seen : ∀ y ∈ st, y ∈ seen)
    (hout_seen : ∀ y ∈ outBefore, y ∈ seen)
    (hcnt_tot : ∀ c : Fin n, (outBefore ++ (runFwd w st seen).2).count c ≤ 3) :
    ∀ k ≤ (runFwd w st seen).1.length,
      ((runFwd w st seen).1.take k).count false + outBefore.length ≤
        3 * (((runFwd w st seen).1.take k).count true + seen.card) := by
  induction w generalizing st outBefore seen with
  | nil =>
    intro k hk
    simp only [runFwd, List.length_replicate] at hk ⊢
    have htake : (List.replicate st.length false).take k = List.replicate k false := by
      rw [List.take_replicate, min_eq_left hk]
    simp only [htake, List.count_replicate, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, zero_add]
    have hlen : (outBefore ++ st.take k).length ≤ 3 * seen.card := by
      refine length_le_three_mul_card (outBefore ++ st.take k) seen ?_ ?_
      · intro y hy
        simp only [List.mem_append] at hy
        rcases hy with hy | hy
        · exact hout_seen y hy
        · exact hst_seen y (List.mem_of_mem_take hy)
      · intro c
        have hsub : (outBefore ++ st.take k).Sublist (outBefore ++ st) :=
          List.Sublist.append_left (List.take_sublist k st) outBefore
        exact le_trans (hsub.count_le c) (by simpa [runFwd] using hcnt_tot c)
    rw [List.length_append, List.length_take, min_eq_left hk] at hlen
    omega
  | cons x xs ih =>
    intro k hk
    obtain ⟨rest, hr1, hr2, _, _⟩ := popLe_head_eq x st
    set popped := (popLe x st).2
    set st' := (popLe x st).1
    have hout_eq : (runFwd (x :: xs) st seen).2 = popped ++ (runFwd xs st' (insert x seen)).2 := by
      conv_lhs => unfold runFwd
      dsimp only; split_ifs <;> rfl
    have hpop_seen : ∀ y ∈ popped, y ∈ seen := fun y hy =>
      hst_seen y (by rw [hr2]; exact List.mem_append_left _ hy)
    have hst'_seen : ∀ y ∈ st', y ∈ insert x seen := by
      intro y hy; rw [hr1] at hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact Finset.mem_insert_self y seen
      · exact Finset.mem_insert_of_mem (hst_seen y (by rw [hr2]; exact List.mem_append_right _ hy))
    have hout'_seen : ∀ y ∈ outBefore ++ popped, y ∈ insert x seen := by
      intro y hy
      simp only [List.mem_append] at hy
      rcases hy with hy | hy
      · exact Finset.mem_insert_of_mem (hout_seen y hy)
      · exact Finset.mem_insert_of_mem (hpop_seen y hy)
    have hcnt' : ∀ c : Fin n, ((outBefore ++ popped) ++ (runFwd xs st' (insert x seen)).2).count c ≤ 3 := by
      intro c; rw [List.append_assoc, ← hout_eq]; exact hcnt_tot c
    have hds_bound : ∀ j ≤ popped.length, j + outBefore.length ≤ 3 * seen.card := by
      intro j hj
      have hlen : (outBefore ++ popped.take j).length ≤ 3 * seen.card := by
        refine length_le_three_mul_card (outBefore ++ popped.take j) seen ?_ ?_
        · intro y hy
          simp only [List.mem_append] at hy
          rcases hy with hy | hy
          · exact hout_seen y hy
          · exact hpop_seen y (List.mem_of_mem_take hy)
        · intro c
          have hsub : (outBefore ++ popped.take j).Sublist ((outBefore ++ popped) ++ (runFwd xs st' (insert x seen)).2) := by
            have h1 : (outBefore ++ popped.take j).Sublist (outBefore ++ popped) :=
              List.Sublist.append_left (List.take_sublist j popped) outBefore
            exact h1.trans (List.sublist_append_left _ _)
          exact le_trans (hsub.count_le c) (hcnt' c)
      rw [List.length_append, List.length_take, min_eq_left hj] at hlen
      omega
    by_cases hx : x ∈ seen
    · have hp_eq : (runFwd (x :: xs) st seen).1 =
          List.replicate popped.length false ++ (runFwd xs st' (insert x seen)).1 := by
        conv_lhs => unfold runFwd
        dsimp only; rw [if_pos hx]
      rw [hp_eq] at hk ⊢
      by_cases hkj : k ≤ popped.length
      · rw [List.take_append_of_le_length (by simpa using hkj), List.take_replicate, min_eq_left hkj]
        simp only [List.count_replicate, beq_iff_eq, Bool.false_eq_true, ↓reduceIte, zero_add]
        exact hds_bound k hkj
      · rw [List.take_append, List.take_of_length_le (by simp; omega), List.length_replicate,
          List.count_append, List.count_append]
        simp only [List.count_replicate, beq_iff_eq, Bool.false_eq_true, ↓reduceIte, zero_add]
        have hk' : k - popped.length ≤ (runFwd xs st' (insert x seen)).1.length := by
          simp only [List.length_append, List.length_replicate] at hk; omega
        have hrec := ih st' (outBefore ++ popped) (insert x seen) hst'_seen hout'_seen hcnt'
          (k - popped.length) hk'
        rw [List.length_append] at hrec
        rw [Finset.insert_eq_of_mem hx] at hrec ⊢
        omega
    · have hp_eq : (runFwd (x :: xs) st seen).1 =
          List.replicate popped.length false ++ true :: (runFwd xs st' (insert x seen)).1 := by
        conv_lhs => unfold runFwd
        dsimp only; rw [if_neg hx]
      rw [hp_eq] at hk ⊢
      by_cases hkj : k ≤ popped.length
      · rw [List.take_append_of_le_length (by simpa using hkj), List.take_replicate, min_eq_left hkj]
        simp only [List.count_replicate, beq_iff_eq, Bool.false_eq_true, ↓reduceIte, zero_add]
        exact hds_bound k hkj
      · rw [List.take_append, List.take_of_length_le (by simp; omega), List.length_replicate]
        have hk1 : k - popped.length = (k - popped.length - 1) + 1 := by omega
        rw [hk1, List.take_succ_cons, List.count_append, List.count_append,
          List.count_cons, List.count_cons]
        simp only [List.count_replicate, beq_iff_eq, Bool.false_eq_true, Bool.true_eq_false,
          ↓reduceIte, zero_add, add_zero]
        have hk' : k - popped.length - 1 ≤ (runFwd xs st' (insert x seen)).1.length := by
          simp only [List.length_append, List.length_replicate, List.length_cons] at hk; omega
        have hrec := ih st' (outBefore ++ popped) (insert x seen) hst'_seen hout'_seen hcnt'
          (k - popped.length - 1) hk'
        rw [List.length_append, Finset.card_insert_of_notMem hx] at hrec
        omega

private lemma length_eq_three_mul {n : ℕ} (w : List (Fin n))
    (hcnt : ∀ c : Fin n, w.count c = 3) : w.length = 3 * n := by
  rw [list_length_eq_sum_count]
  simp_rw [hcnt]
  simp [mul_comm]

private lemma runFwd_isDyck3List {n : ℕ} (w : List (Fin n))
    (hcnt : ∀ c : Fin n, w.count c = 3) :
    IsDyck3List n (runFwd w [] ∅).1 := by
  have hlen_w : w.length = 3 * n := length_eq_three_mul w hcnt
  have hcf : (runFwd w [] ∅).1.count false = 3 * n := by
    rw [runFwd_count_false, (runFwd_out_perm w [] ∅).length_eq, List.append_nil, hlen_w]
  have hct : (runFwd w [] ∅).1.count true = n := by
    rw [runFwd_count_true, Finset.sdiff_empty]
    have hfin : w.toFinset = Finset.univ := by
      ext c; simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
      exact List.count_pos_iff.mp (by rw [hcnt c]; omega)
    rw [hfin, Finset.card_univ, Fintype.card_fin]
  have hlen_p : (runFwd w [] ∅).1.length = 4 * n := by
    have := list_bool_count_add (runFwd w [] ∅).1
    omega
  refine ⟨hlen_p, hct, ?_⟩
  intro k hk
  have hb := runFwd_prefix_bound w [] [] ∅ (by simp) (by simp)
    (fun c => by
      simp only [List.nil_append]
      rw [(runFwd_out_perm w [] ∅).count_eq, List.append_nil, hcnt c])
    k (by omega)
  simpa using hb

private def UniformAvoidingList (n : ℕ) :=
  { w : List (Fin n) // (∀ c : Fin n, w.count c = 3) ∧ Avoids231 w }

private def uniformAvoidingWord_equiv_list (n : ℕ) :
    { word : Fin (3 * n) → Fin n // OMA.S_oeis_a002293.IsUniformAvoidingWord word } ≃
      UniformAvoidingList n :=
  { toFun := fun w => ⟨List.ofFn w.1, by
      constructor
      · intro c
        rw [List.count_eq_length_filter, List.ofFn_eq_map, List.filter_map, List.length_map]
        rw [← List.toFinset_card_of_nodup ((List.nodup_finRange (3 * n)).filter _)]
        have h := w.2.1 c
        convert h using 2
        ext i; simp
      · intro i j k hi hj hk hij hjk
        rw [List.length_ofFn] at hi hj hk
        simp only [List.getElem_ofFn]
        exact w.2.2 ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ hij hjk⟩
    invFun := fun w =>
      have hlen : w.1.length = 3 * n := length_eq_three_mul w.1 w.2.1
      ⟨fun i => w.1[i.val]'(by omega), by
        constructor
        · intro c
          have hof : List.ofFn (fun i : Fin (3 * n) => w.1[i.val]'(by omega)) = w.1 := by
            apply List.ext_getElem
            · simp [hlen]
            · intro j hj1 hj2; simp
          have h := w.2.1 c
          rw [← hof, List.count_eq_length_filter, List.ofFn_eq_map, List.filter_map, List.length_map,
            ← List.toFinset_card_of_nodup ((List.nodup_finRange (3 * n)).filter _)] at h
          convert h using 2
          ext i; simp
        · intro i j k hij hjk
          exact w.2.2 i.val j.val k.val (by omega) (by omega) (by omega) hij hjk⟩
    left_inv := fun w => by
      apply Subtype.ext; funext i; simp
    right_inv := fun w => by
      apply Subtype.ext
      apply List.ext_getElem
      · simp [length_eq_three_mul w.1 w.2.1]
      · intro j hj1 hj2; simp }

end OMA.OeisA002293

theorem OMA.solution : type_of% @OMA.S_oeis_a002293.main := by
  intro n
  let e1 := OMA.OeisA002293.uniformAvoidingWord_equiv_list n
  let e2 : OMA.OeisA002293.UniformAvoidingList n ≃ { p : List Bool // OMA.OeisA002293.IsDyck3List n p } :=
    { toFun := fun w => ⟨(OMA.OeisA002293.runFwd w.1 [] ∅).1, OMA.OeisA002293.runFwd_isDyck3List w.1 w.2.1⟩
      invFun := fun p => ⟨OMA.OeisA002293.decodeList n p.1,
        (OMA.OeisA002293.decodeList_spec n p.1 p.2).1,
        (OMA.OeisA002293.decodeList_spec n p.1 p.2).2.1⟩
      left_inv := fun w => Subtype.ext (OMA.OeisA002293.decodeList_runFwd w.1 w.2.1 w.2.2)
      right_inv := fun p => Subtype.ext (OMA.OeisA002293.decodeList_spec n p.1 p.2).2.2 }
  rw [Nat.card_congr (e1.trans e2)]
  exact OMA.OeisA002293.card_dyck3List_eq n


