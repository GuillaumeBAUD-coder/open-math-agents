import OMAStatements.S_oeis_a205163
import Mathlib

namespace OMA.S_oeis_a205163

section generic
variable {S : Type} [Fintype S] [DecidableEq S] (R : S → S → Prop) [DecidableRel R]

def Chain (n : ℕ) := {y : Fin (n + 1) → S // ∀ i : Fin n, R (y i.castSucc) (y i.succ)}

instance (n : ℕ) : Fintype (Chain R n) := by unfold Chain; infer_instance

def V : ℕ → S → ℕ
  | 0, _ => 1
  | n + 1, s => ∑ t, if R s t then V n t else 0

theorem cardStart (n : ℕ) (s : S) :
    Fintype.card {y : Chain R n // y.1 0 = s} = V R n s := by
  induction n generalizing s with
  | zero =>
    simp only [V]
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨⟨fun _ => s, fun i => i.elim0⟩, rfl⟩, ?_⟩
    rintro ⟨⟨y, hy⟩, h0⟩
    apply Subtype.ext; apply Subtype.ext
    funext j
    have : j = 0 := Fin.ext (by have := j.2; omega)
    subst this; exact h0
  | succ n ih =>
    have e : {y : Chain R (n + 1) // y.1 0 = s} ≃
        Σ t : S, {z : Chain R n // z.1 0 = t ∧ R s t} :=
      { toFun := fun y => ⟨y.1.1 1, ⟨⟨fun j => y.1.1 j.succ, fun i => y.1.2 i.succ⟩, rfl, by
          have h := y.1.2 0
          have h0 : y.1.1 (Fin.castSucc 0) = s := y.2
          rw [h0] at h
          exact h⟩⟩
        invFun := fun p => ⟨⟨Fin.cons s p.2.1.1, by
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · have h2 := p.2.2.2
            rw [← p.2.2.1] at h2
            simpa using h2
          · simpa using p.2.1.2 j⟩, rfl⟩
        left_inv := by
          rintro ⟨⟨y, hy⟩, h0⟩
          apply Subtype.ext; apply Subtype.ext
          funext j
          refine Fin.cases ?_ (fun k => ?_) j
          · simpa using h0.symm
          · simp
        right_inv := by
          rintro ⟨t, ⟨⟨z, hz⟩, h1, h2⟩⟩
          simp only [Fin.cons_succ]
          have : (Fin.cons s z : Fin (n + 2) → S) 1 = t := by
            have : (1 : Fin (n + 2)) = Fin.succ 0 := rfl
            rw [this, Fin.cons_succ]; exact h1
          subst this
          rfl }
    rw [Fintype.card_congr e, Fintype.card_sigma]
    simp only [V]
    apply Finset.sum_congr rfl
    intro t _
    by_cases h : R s t
    · simp only [h, if_true, and_true]
      exact ih t
    · simp only [h, if_false, and_false]
      simp [Fintype.card_eq_zero_iff]

theorem cardChain (n : ℕ) : Fintype.card (Chain R n) = ∑ s, V R n s := by
  rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (fun y : Chain R n => y.1 0)), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro s _
  exact cardStart R n s

theorem rec_gen (m : ℕ) (c : ℕ → ℤ)
    (h0 : ∀ s, ∑ j ∈ Finset.range (m + 1), c j * (V R j s : ℤ) = 0) :
    ∀ n s, ∑ j ∈ Finset.range (m + 1), c j * (V R (n + j) s : ℤ) = 0 := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    intro s
    have : ∀ j, (V R (n + 1 + j) s : ℤ) = ∑ t, if R s t then (V R (n + j) t : ℤ) else 0 := by
      intro j
      rw [show n + 1 + j = (n + j) + 1 by omega]
      simp [V]
    simp only [this, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro t _
    by_cases h : R s t
    · have := ih t
      simp only [h, if_true]
      simpa [← Finset.mul_sum] using this
    · simp [h]

theorem rec_total (m : ℕ) (c : ℕ → ℤ)
    (h0 : ∀ s, ∑ j ∈ Finset.range (m + 1), c j * (V R j s : ℤ) = 0) (n : ℕ) :
    ∑ j ∈ Finset.range (m + 1), c j * (∑ s, (V R (n + j) s : ℤ)) = 0 := by
  have h := Finset.sum_eq_zero (s := (Finset.univ : Finset S)) (fun s _ => rec_gen R m c h0 n s)
  rw [Finset.sum_comm] at h
  simpa [Finset.mul_sum] using h
end generic

open Finset

abbrev Row := Fin 2 → Fin 4

def rowOK (k : ℕ) (r : Row) : Prop := (r 0).val ≤ k ∧ (r 1).val ≤ max k ((r 0).val + 1)
instance (k : ℕ) (r : Row) : Decidable (rowOK k r) := by unfold rowOK; infer_instance
def kup (k : ℕ) (r : Row) : ℕ := max k (1 + max (r 0).val (r 1).val)
def stepOK (p r : Row) : Prop := p 0 ≠ r 1 ∨ p 1 ≠ r 0
instance (p r : Row) : Decidable (stepOK p r) := by unfold stepOK; infer_instance

def RowMajorRel {m : ℕ} (k : ℕ) (x : Fin m → Row) : Prop :=
  ∀ i j, ∀ u : Fin 4, u < x i j → u.val < k ∨ ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ x i' j' = u
instance {m : ℕ} (k : ℕ) (x : Fin m → Row) : Decidable (RowMajorRel k x) := by
  unfold RowMajorRel; infer_instance

def PP {n : ℕ} (r : Row) (t : Fin n → Row) : Prop :=
  ∀ i : Fin n, stepOK ((Fin.cons r t : Fin (n + 1) → Row) i.castSucc) (t i)
instance {n : ℕ} (r : Row) (t : Fin n → Row) : Decidable (PP r t) := by unfold PP; infer_instance

lemma row_iff (k : ℕ) (hk : k ≤ 4) (r : Row) :
    (∀ j : Fin 2, ∀ u : Fin 4, u < r j → u.val < k ∨ ∃ j' : Fin 2, j' < j ∧ r j' = u) ↔ rowOK k r := by
  revert r
  interval_cases k <;> decide

lemma kup_iff (k : ℕ) (hk : k ≤ 4) (r : Row) (h : rowOK k r) (u : Fin 4) :
    u.val < kup k r ↔ u.val < k ∨ ∃ j, r j = u := by
  revert r u
  interval_cases k <;> decide

lemma kup_ge (k : ℕ) (r : Row) : k ≤ kup k r := le_max_left _ _
lemma kup_le (k : ℕ) (hk : k ≤ 4) (r : Row) : kup k r ≤ 4 := by
  unfold kup
  have := (r 0).2; have := (r 1).2
  omega

lemma rm_cons {m : ℕ} (k : ℕ) (hk : k ≤ 4) (r : Row) (x : Fin m → Row) :
    RowMajorRel k (Fin.cons r x : Fin (m + 1) → Row) ↔ rowOK k r ∧ RowMajorRel (kup k r) x := by
  have hrow := row_iff k hk r
  constructor
  · intro h
    have h0 : rowOK k r := by
      rw [← hrow]
      intro j u hu
      have := h 0 j u (by simpa using hu)
      rcases this with h1 | ⟨i', j', hij, hx⟩
      · left; exact h1
      · right
        rcases hij with h2 | ⟨h2, h3⟩
        · exact absurd h2 (Fin.not_lt_zero _)
        · subst h2
          exact ⟨j', h3, by simpa using hx⟩
    refine ⟨h0, ?_⟩
    intro i j u hu
    have := h i.succ j u (by simpa using hu)
    rcases this with h1 | ⟨i', j', hij, hx⟩
    · left; exact lt_of_lt_of_le h1 (kup_ge k r)
    · cases i' using Fin.cases with
      | zero =>
        left
        rw [kup_iff k hk r h0]
        right
        exact ⟨j', by simpa using hx⟩
      | succ i'' =>
        right
        refine ⟨i'', j', ?_, ?_⟩
        · simpa using hij
        · simpa using hx
  · rintro ⟨h0, h⟩ i j u hu
    cases i using Fin.cases with
    | zero =>
      have := (hrow.mpr h0) j u (by simpa using hu)
      rcases this with h1 | ⟨j', hj', hx⟩
      · left; exact h1
      · right; exact ⟨0, j', Or.inr ⟨rfl, hj'⟩, by simpa using hx⟩
    | succ i =>
      have := h i j u (by simpa using hu)
      rcases this with h1 | ⟨i', j', hij, hx⟩
      · rcases (kup_iff k hk r h0 u).mp h1 with h2 | ⟨j', hj'⟩
        · left; exact h2
        · right; exact ⟨0, j', by simp, by simpa using hj'⟩
      · right; exact ⟨i'.succ, j', by simpa using hij, by simpa using hx⟩

lemma blocks_iff {n : ℕ} (x : Fin (n + 1) → Row) :
    BlocksOK x ↔ ∀ i : Fin n, stepOK (x i.castSucc) (x i.succ) := by
  constructor
  · intro h i
    have := h i.castSucc i.succ 0 1 (by simp) (by simp)
    unfold stepOK
    exact this
  · intro h i i' j j' hi hj
    have hlt : i.val < n := by have := i'.2; omega
    have e1 : i = (⟨i.val, hlt⟩ : Fin n).castSucc := rfl
    have e2 : i' = (⟨i.val, hlt⟩ : Fin n).succ := by ext; simp [hi]
    have hj0 : j = 0 := by ext; have := j'.2; simp; omega
    have hj1 : j' = 1 := by ext; have := j'.2; simp; omega
    subst hj0 hj1
    have := h ⟨i.val, hlt⟩
    rw [← e1, ← e2] at this
    unfold stepOK at this
    exact this

lemma card_cons (n : ℕ) (Q : (Fin (n + 1) → Row) → Prop) [DecidablePred Q] :
    ((univ : Finset (Fin (n + 1) → Row)).filter Q).card =
      ∑ r : Row, ((univ : Finset (Fin n → Row)).filter (fun t => Q (Fin.cons r t))).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x : Fin (n + 1) → Row => x 0)
    (t := (univ : Finset Row)) (by simp)]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.card_nbij' (fun x => Fin.tail x) (fun t => Fin.cons r t)
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨h2, h1⟩ := hx
    have : (Fin.cons r (Fin.tail x) : Fin (n + 1) → Row) = x := by
      rw [← h1]; exact Fin.cons_self_tail x
    rw [this]; exact h2
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    exact ⟨ht, by simp⟩
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [← hx.2]; exact Fin.cons_self_tail x
  · intro t _
    simp

def Cnt (n : ℕ) (r : Row) (k : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Row)).filter (fun t => PP r t ∧ RowMajorRel k t)).card

lemma PP_cons {n : ℕ} (r r' : Row) (t : Fin n → Row) :
    PP r (Fin.cons r' t : Fin (n + 1) → Row) ↔ stepOK r r' ∧ PP r' t := by
  unfold PP
  rw [Fin.forall_fin_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, ← Fin.succ_castSucc]

lemma Cnt_succ (n : ℕ) (r : Row) (k : ℕ) (hk : k ≤ 4) :
    Cnt (n + 1) r k = ∑ r' : Row, if stepOK r r' ∧ rowOK k r' then Cnt n r' (kup k r') else 0 := by
  unfold Cnt
  rw [card_cons]
  apply Finset.sum_congr rfl
  intro r' _
  by_cases hc : stepOK r r' ∧ rowOK k r'
  · rw [if_pos hc]
    congr 1
    apply Finset.filter_congr
    intro t _
    rw [PP_cons, rm_cons k hk]
    constructor
    · rintro ⟨⟨_, h2⟩, _, h4⟩; exact ⟨h2, h4⟩
    · rintro ⟨h2, h4⟩; exact ⟨⟨hc.1, h2⟩, hc.2, h4⟩
  · rw [if_neg hc]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro t _ ht
    rw [PP_cons, rm_cons k hk] at ht
    exact hc ⟨ht.1.1, ht.2.1⟩

abbrev St := Row × Fin 5

def Rel : St → St → Prop := fun s t => (stepOK s.1 t.1 ∧ rowOK s.2.val t.1) ∧ t.2.val = kup s.2.val t.1
instance : DecidableRel Rel := fun s t => by unfold Rel; infer_instance

lemma V_eq (n : ℕ) : ∀ s : St, V Rel n s = Cnt n s.1 s.2.val := by
  induction n with
  | zero =>
    intro s
    simp only [V, Cnt]
    symm
    rw [Finset.card_eq_one]
    refine ⟨Fin.elim0, ?_⟩
    ext t
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro _; funext i; exact i.elim0
    · intro _; exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro s
    rw [Cnt_succ n s.1 s.2.val (by have := s.2.2; omega)]
    simp only [V]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro r' _
    by_cases hc : stepOK s.1 r' ∧ rowOK s.2.val r'
    · rw [if_pos hc]
      have hlt : kup s.2.val r' < 5 := by
        have := kup_le s.2.val (by have := s.2.2; omega) r'; omega
      rw [Finset.sum_eq_single (⟨kup s.2.val r', hlt⟩ : Fin 5)]
      · have : Rel s (r', ⟨kup s.2.val r', hlt⟩) := ⟨hc, rfl⟩
        rw [if_pos this, ih]
      · intro b _ hb
        have : ¬ Rel s (r', b) := by
          rintro ⟨_, h2⟩
          apply hb; ext; simpa using h2
        rw [if_neg this]
      · intro h; exact absurd (mem_univ _) h
    · rw [if_neg hc]
      apply Finset.sum_eq_zero
      intro b _
      have : ¬ Rel s (r', b) := fun h => hc h.1
      rw [if_neg this]

def k0 (r : Row) : Fin 5 := ⟨kup 0 r % 5, Nat.mod_lt _ (by omega)⟩

lemma k0_val (r : Row) : (k0 r).val = kup 0 r := by
  have := kup_le 0 (by omega) r
  unfold k0; simp; omega

theorem a_eq (n : ℕ) : a n = ∑ r : Row, if rowOK 0 r then V Rel n (r, k0 r) else 0 := by
  unfold a
  rw [card_cons n]
  apply Finset.sum_congr rfl
  intro r _
  rw [show V Rel n (r, k0 r) = Cnt n r (kup 0 r) by rw [V_eq]; simp [k0_val]]
  have hb : ∀ t : Fin n → Row, BlocksOK (Fin.cons r t : Fin (n + 1) → Row) ↔ PP r t := by
    intro t
    rw [blocks_iff]
    unfold PP
    simp
  have hm : ∀ t : Fin n → Row, RowMajorNew (Fin.cons r t : Fin (n + 1) → Row) ↔
      rowOK 0 r ∧ RowMajorRel (kup 0 r) t := by
    intro t
    rw [← rm_cons 0 (by omega)]
    unfold RowMajorNew RowMajorRel
    simp
  by_cases hc : rowOK 0 r
  · rw [if_pos hc]
    unfold Cnt
    congr 1
    apply Finset.filter_congr
    intro t _
    rw [hb, hm]
    tauto
  · rw [if_neg hc, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro t _ ht
    exact hc ((hm t).mp ht.2).1

def cc : ℕ → ℤ := fun j => [(0 : ℤ), 0, 45, -18, 1].getD j 0

theorem hrec (k : ℕ) : (a (k + 4) : ℤ) = (18 : ℤ) * a (k + 3) + (-45 : ℤ) * a (k + 2) := by
  have h := rec_gen Rel 4 cc (by decide +kernel)
  have e0 : cc 0 = 0 := rfl
  have e1 : cc 1 = 0 := rfl
  have e2 : cc 2 = 45 := rfl
  have e3 : cc 3 = -18 := rfl
  have e4 : cc 4 = 1 := rfl
  have e : ∀ r : Row, (if rowOK 0 r then (V Rel (k + 4) (r, k0 r) : ℤ) else 0) =
      18 * (if rowOK 0 r then (V Rel (k + 3) (r, k0 r) : ℤ) else 0) +
      (-45) * (if rowOK 0 r then (V Rel (k + 2) (r, k0 r) : ℤ) else 0) := by
    intro r
    split_ifs
    · have := h k (r, k0 r)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, e4] at this
      linarith
    · simp
  simp only [a_eq]
  push_cast
  rw [Finset.sum_congr rfl (fun r _ => e r), Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]

theorem v1 : a 1 = 13 := by rw [a_eq]; decide +kernel
theorem v2 : a 2 = 159 := by rw [a_eq]; decide +kernel
theorem v3 : a 3 = 2277 := by rw [a_eq]; decide +kernel
theorem v0 : a 0 = 2 := by rw [a_eq]; decide +kernel

theorem closed (m : ℕ) : a (m + 1) = 3 ^ m * (2 * 5 ^ (m + 1) + 3) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m < 3
    · interval_cases m
      · simpa using v1
      · simpa using v2
      · simpa using v3
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
      have h1 := ih (j + 2) (by omega)
      have h2 := ih (j + 1) (by omega)
      have h := hrec j
      have h1' : (a (j + 3) : ℤ) = 3 ^ (j + 2) * (2 * 5 ^ (j + 2 + 1) + 3) := by exact_mod_cast h1
      have h2' : (a (j + 2) : ℤ) = 3 ^ (j + 1) * (2 * 5 ^ (j + 1 + 1) + 3) := by exact_mod_cast h2
      have : (a (j + 3 + 1) : ℤ) = 3 ^ (j + 3) * (2 * 5 ^ (j + 3 + 1) + 3) := by
        rw [show j + 3 + 1 = j + 4 from rfl, h, h1', h2']
        ring
      exact_mod_cast this

open PowerSeries in
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - 3 * X) * (1 - 15 * X)) = X * (13 - 75 * X) := by
  have h18 : (C (18 : ℚ) : PowerSeries ℚ) = 18 := map_ofNat _ 18
  have h45 : (C (45 : ℚ) : PowerSeries ℚ) = 45 := map_ofNat _ 45
  have h13 : (C (13 : ℚ) : PowerSeries ℚ) = 13 := map_ofNat _ 13
  have h75 : (C (75 : ℚ) : PowerSeries ℚ) = 75 := map_ofNat _ 75
  set F : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hF
  have e1 : F * ((1 - 3 * X) * (1 - 15 * X)) =
      F - C 18 * (X * F) + C 45 * (X * (X * F)) := by
    rw [h18, h45]; ring
  have e2 : (X * (13 - 75 * X) : PowerSeries ℚ) = C 13 * X - C 75 * X ^ 2 := by
    rw [h13, h75]; ring
  rw [e1, e2]
  have c : ∀ n, coeff n F = if n = 0 then 0 else (a n : ℚ) := fun n => by rw [hF, coeff_mk]
  ext n
  rcases n with _ | _ | _ | k
  · have h0 : constantCoeff F = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, c]; simp
    simp [c, h0]
  · simp [c, v1, coeff_succ_X_mul, coeff_C_mul]
  · simp [c, v1, v2, coeff_succ_X_mul, coeff_C_mul, coeff_X_pow]
    norm_num
  · simp only [map_sub, map_add, coeff_C_mul, coeff_succ_X_mul, c]
    rw [coeff_X_pow, coeff_X]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
    have a3 := closed (k + 2)
    have a2 := closed (k + 1)
    have a1 := closed k
    simp only [show k + 3 = k + 2 + 1 from rfl, show k + 2 = k + 1 + 1 from rfl, show k + 1 = k + 1 from rfl]
    have b3 : (a (k + 2 + 1) : ℚ) = 3 ^ (k + 2) * (2 * 5 ^ (k + 2 + 1) + 3) := by exact_mod_cast a3
    have b2 : (a (k + 1 + 1) : ℚ) = 3 ^ (k + 1) * (2 * 5 ^ (k + 1 + 1) + 3) := by exact_mod_cast a2
    have b1 : (a (k + 1) : ℚ) = 3 ^ k * (2 * 5 ^ (k + 1) + 3) := by exact_mod_cast a1
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, add_eq_zero, OfNat.ofNat_ne_zero]
    rw [b3, b2, b1]
    ring_nf
    rw [if_neg (by omega), if_neg (by omega)]
    simp

end OMA.S_oeis_a205163

theorem OMA.solution : type_of% @OMA.S_oeis_a205163.main := by
  refine ⟨OMA.S_oeis_a205163.gf, fun n hn => ?_⟩
  cases n with
  | zero => omega
  | succ m => simpa using OMA.S_oeis_a205163.closed m
