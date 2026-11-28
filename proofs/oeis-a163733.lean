import OMAStatements.S_oeis_a163733

open OMA.S_oeis_a163733 PowerSeries

namespace A163733Proof

abbrev Row := Fin 2 → Fin 2

def compat (u v : Row) : Prop := (u 0 = 1 ∧ v 0 = 1) ∨ (u 1 = 1 ∧ v 1 = 1)

instance (u v : Row) : Decidable (compat u v) := by unfold compat; infer_instance

theorem fin2_cases (j : Fin 2) : j = 0 ∨ j = 1 := by fin_cases j <;> simp

theorem conn_iff {n : ℕ} (A : Fin n → Row) (hc : CornersOne A) :
    OnesConnected A ↔
      (∀ i, A i 0 = 1 ∨ A i 1 = 1) ∧ (∀ i k : Fin n, k.val = i.val + 1 → compat (A i) (A k)) := by
  constructor
  · intro H
    refine ⟨fun i => ?_, fun i k hk => ?_⟩
    · by_contra hz
      push Not at hz
      have hi0 : i.val ≠ 0 := fun h => hz.1 (hc i 0 (Or.inl h))
      have hi1 : i.val + 1 ≠ n := fun h => hz.1 (hc i 0 (Or.inr h))
      obtain ⟨p, hp, q, hq1, hqS, hadj⟩ := H (Finset.univ.filter fun p => p.1 < i ∧ A p.1 p.2 = 1)
        (fun p hp => (Finset.mem_filter.1 hp).2.2)
        ⟨(⟨0, by omega⟩, 0), Finset.mem_filter.2 ⟨Finset.mem_univ _,
          by rw [Fin.lt_def]; simp; omega, hc _ _ (Or.inl rfl)⟩⟩
        ⟨(⟨n - 1, by omega⟩, 0), hc _ _ (Or.inr (by simp; omega)), by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, Fin.lt_def]
          intro h; omega⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, Fin.lt_def] at hp hqS
      have hq : ¬ q.1.val < i.val := fun h => hqS h hq1
      rcases hadj with ⟨h1, _⟩ | ⟨h2, h3 | h3⟩
      · rw [← h1] at hq; exact hq hp.1
      · have : q.1 = i := Fin.ext (by omega)
        have hq1' : A i q.2 = 1 := by rw [← this]; exact hq1
        rcases fin2_cases q.2 with h | h <;> rw [h] at hq1'
        · exact hz.1 hq1'
        · exact hz.2 hq1'
      · omega
    · by_contra hz
      have hk1 : k.val < n := k.isLt
      obtain ⟨p, hp, q, hq1, hqS, hadj⟩ := H (Finset.univ.filter fun p => p.1 ≤ i ∧ A p.1 p.2 = 1)
        (fun p hp => (Finset.mem_filter.1 hp).2.2)
        ⟨(⟨0, by omega⟩, 0), Finset.mem_filter.2 ⟨Finset.mem_univ _,
          by rw [Fin.le_def]; simp, hc _ _ (Or.inl rfl)⟩⟩
        ⟨(⟨n - 1, by omega⟩, 0), hc _ _ (Or.inr (by simp; omega)), by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, Fin.le_def]
          intro h; omega⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, Fin.le_def] at hp hqS
      have hq : ¬ q.1.val ≤ i.val := fun h => hqS h hq1
      rcases hadj with ⟨h1, _⟩ | ⟨h2, h3 | h3⟩
      · rw [← h1] at hq; exact hq hp.1
      · have e1 : p.1 = i := Fin.ext (by omega)
        have e2 : q.1 = k := Fin.ext (by omega)
        apply hz
        have hp' : A i p.2 = 1 := by rw [← e1]; exact hp.2
        have hq' : A k p.2 = 1 := by rw [← e2, h2]; exact hq1
        rcases fin2_cases p.2 with h | h <;> rw [h] at hp' hq'
        · exact Or.inl ⟨hp', hq'⟩
        · exact Or.inr ⟨hp', hq'⟩
      · omega
  · rintro ⟨hnz, hcp⟩ S hS ⟨p0, hp0⟩ ⟨q0, hq0, hq0S⟩
    by_contra H
    have cl : ∀ p ∈ S, ∀ q : Fin n × Fin 2, A q.1 q.2 = 1 → Adj p q → q ∈ S := by
      intro p hp q hq ha
      by_contra hqS
      exact H ⟨p, hp, q, hq, hqS, ha⟩
    have rowcl : ∀ (i : Fin n) (j j' : Fin 2), (i, j) ∈ S → A i j' = 1 → (i, j') ∈ S := by
      intro i j j' hj hj'
      by_cases e : j = j'
      · rw [← e]; exact hj
      · refine cl _ hj (i, j') hj' (Or.inl ⟨rfl, ?_⟩)
        rcases fin2_cases j with rfl | rfl <;> rcases fin2_cases j' with rfl | rfl <;> simp_all
    have step : ∀ i k : Fin n, (k.val = i.val + 1 ∨ i.val = k.val + 1) →
        (∃ j, (i, j) ∈ S) → ∃ j, (k, j) ∈ S := by
      intro i k hik ⟨j, hj⟩
      have hc' : compat (A i) (A k) ∨ compat (A k) (A i) := by
        rcases hik with h | h
        · exact Or.inl (hcp i k h)
        · exact Or.inr (hcp k i h)
      have : ∃ c, A i c = 1 ∧ A k c = 1 := by
        simp only [compat] at hc'
        rcases hc' with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨0, h1, h2⟩
        · exact ⟨1, h1, h2⟩
        · exact ⟨0, h2, h1⟩
        · exact ⟨1, h2, h1⟩
      obtain ⟨c, hic, hkc⟩ := this
      have h1 := rowcl i j c hj hic
      exact ⟨c, cl _ h1 (k, c) hkc (Or.inr ⟨rfl, by show i.val + 1 = k.val ∨ k.val + 1 = i.val; omega⟩)⟩
    have up : ∀ d : ℕ, ∀ i : Fin n, i.val = p0.1.val + d → ∃ j, (i, j) ∈ S := by
      intro d
      induction d with
      | zero => intro i hi; exact ⟨p0.2, by rw [show i = p0.1 from Fin.ext hi]; exact hp0⟩
      | succ d ih =>
        intro i hi
        exact step ⟨i.val - 1, by omega⟩ i (Or.inl (by simp; omega))
          (ih _ (by simp; omega))
    have down : ∀ d : ℕ, ∀ i : Fin n, i.val + d = p0.1.val → ∃ j, (i, j) ∈ S := by
      intro d
      induction d with
      | zero => intro i hi; exact ⟨p0.2, by rw [show i = p0.1 from Fin.ext hi]; exact hp0⟩
      | succ d ih =>
        intro i hi
        have hlt := p0.1.isLt
        exact step ⟨i.val + 1, by omega⟩ i (Or.inr (by simp))
          (ih _ (by simp; omega))
    have hall : ∀ i : Fin n, ∃ j, (i, j) ∈ S := by
      intro i
      by_cases h : p0.1.val ≤ i.val
      · exact up (i.val - p0.1.val) i (by omega)
      · exact down (p0.1.val - i.val) i (by omega)
    obtain ⟨j, hj⟩ := hall q0.1
    exact hq0S (rowcl q0.1 j q0.2 hj hq0)

theorem ite3 (p q r : Prop) [Decidable p] [Decidable q] [Decidable r] :
    ((if p then 1 else 0) + (if q then 1 else 0) + (if r then 1 else 0) ≤ 2) ↔
      ¬ (p ∧ q ∧ r) := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;> simp [hp, hq, hr]

theorem lr {n : ℕ} (A : Fin n → Row) (i : Fin n) (j : Fin 2) :
    (if LeftOne A i j then 1 else 0) + (if RightOne A i j then 1 else 0) =
      if (∃ j', j' ≠ j ∧ A i j' = 1) then 1 else 0 := by
  rcases fin2_cases j with rfl | rfl <;> simp [LeftOne, RightOne, Fin.exists_fin_two]

theorem deg_iff {n : ℕ} (A : Fin n → Row) (i : Fin n) (j : Fin 2) :
    numAdjOnes A i j ≤ 2 ↔ ¬ ((∃ j', j' ≠ j ∧ A i j' = 1) ∧ UpOne A i j ∧ DownOne A i j) := by
  unfold numAdjOnes
  rw [lr, ite3]

def upHas (up : Option Row) (j : Fin 2) : Prop := ∃ u, up = some u ∧ u j = 1

instance (up : Option Row) (j : Fin 2) : Decidable (upHas up j) := by
  unfold upHas; infer_instance

def upCompat (up : Option Row) (v : Row) : Prop := ∀ u, up = some u → compat u v

instance (up : Option Row) (v : Row) : Decidable (upCompat up v) := by
  unfold upCompat; infer_instance

-- The row scan: up is the row above, fb marks columns where the first row must hold 0.
def Ext (up : Option Row) (fb : Row) {m : ℕ} (y : Fin m → Row) : Prop :=
  (∀ k : Fin m, k.val = 0 → ∀ j, ¬ (fb j = 1 ∧ y k j = 1)) ∧
  (∀ i, y i 0 = 1 ∨ y i 1 = 1) ∧
  (∀ k : Fin m, k.val = 0 → upCompat up (y k)) ∧
  (∀ i k : Fin m, k.val = i.val + 1 → compat (y i) (y k)) ∧
  (∀ i j, y i j = 1 → ¬ ((∃ j', j' ≠ j ∧ y i j' = 1) ∧
      ((i.val = 0 ∧ upHas up j) ∨ ∃ i' : Fin m, i'.val + 1 = i.val ∧ y i' j = 1) ∧
      ∃ k : Fin m, k.val = i.val + 1 ∧ y k j = 1)) ∧
  (∀ i : Fin m, i.val + 1 = m → y i = ![1, 1]) ∧ (m = 0 → up = some ![1, 1])

instance (up : Option Row) (fb : Row) {m : ℕ} (y : Fin m → Row) : Decidable (Ext up fb y) := by
  unfold Ext; infer_instance

theorem row11 (r : Row) : r = ![1, 1] ↔ ∀ j, r j = 1 := by
  rw [funext_iff, Fin.forall_fin_two, Fin.forall_fin_two]; simp

theorem valid_iff {m : ℕ} (A : Fin (m + 1) → Row) :
    Valid A ↔ A 0 = ![1, 1] ∧ Ext none 0 A := by
  have hcor : CornersOne A ↔ A 0 = ![1, 1] ∧ ∀ i : Fin (m + 1), i.val + 1 = m + 1 →
      A i = ![1, 1] := by
    simp only [CornersOne, row11]
    constructor
    · intro h; exact ⟨fun j => h 0 j (Or.inl rfl), fun i hi j => h i j (Or.inr hi)⟩
    · rintro ⟨h0, h1⟩ i j (hi | hi)
      · rw [show i = 0 from Fin.ext hi]; exact h0 j
      · exact h1 i hi j
  have hdeg : (∀ i j, A i j = 1 → numAdjOnes A i j ≤ 2) ↔
      ∀ i j, A i j = 1 → ¬ ((∃ j', j' ≠ j ∧ A i j' = 1) ∧
        ((i.val = 0 ∧ upHas none j) ∨
          ∃ i' : Fin (m + 1), i'.val + 1 = i.val ∧ A i' j = 1) ∧
        ∃ k : Fin (m + 1), k.val = i.val + 1 ∧ A k j = 1) := by
    simp only [deg_iff, UpOne, DownOne, upHas]
    simp
  constructor
  · rintro ⟨hc, hk, hd⟩
    obtain ⟨h0, hl⟩ := hcor.1 hk
    obtain ⟨l1, l2⟩ := (conn_iff A hk).1 hc
    exact ⟨h0, fun _ _ _ h => by simp at h, l1, fun _ _ _ h => by simp at h, l2, hdeg.1 hd, hl,
      fun h => by omega⟩
  · rintro ⟨h0, -, l1, -, l2, hd, hl, -⟩
    have hk := hcor.2 ⟨h0, hl⟩
    exact ⟨(conn_iff A hk).2 ⟨l1, l2⟩, hk, hdeg.2 hd⟩

def okr (up : Option Row) (fb r : Row) : Prop :=
  (∀ j, ¬ (fb j = 1 ∧ r j = 1)) ∧ (r 0 = 1 ∨ r 1 = 1) ∧ upCompat up r

instance (up : Option Row) (fb r : Row) : Decidable (okr up fb r) := by
  unfold okr; infer_instance

def nfb (up : Option Row) (r : Row) : Row := fun j =>
  if (∃ j', j' ≠ j ∧ r j' = 1) ∧ r j = 1 ∧ upHas up j then 1 else 0

theorem nfb_one (up : Option Row) (r : Row) (j : Fin 2) :
    nfb up r j = 1 ↔ (∃ j', j' ≠ j ∧ r j' = 1) ∧ r j = 1 ∧ upHas up j := by
  unfold nfb
  by_cases h : (∃ j', j' ≠ j ∧ r j' = 1) ∧ r j = 1 ∧ upHas up j
  · rw [if_pos h]; exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]; exact ⟨fun e => absurd e (by decide), fun e => absurd e h⟩

@[simp] theorem upHas_some (r : Row) (j : Fin 2) : upHas (some r) j ↔ r j = 1 := by
  simp [upHas]

@[simp] theorem upCompat_some (r v : Row) : upCompat (some r) v ↔ compat r v := by
  simp [upCompat]

theorem ext_cons (up : Option Row) (fb : Row) {m : ℕ} (r : Row) (y : Fin m → Row) :
    Ext up fb (Fin.cons r y : Fin (m + 1) → Row) ↔ okr up fb r ∧ Ext (some r) (nfb up r) y := by
  unfold Ext okr
  simp only [Fin.forall_fin_succ, Fin.exists_fin_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.val_zero, Fin.val_succ, nfb_one]
  simp
  constructor
  · rintro ⟨h1, ⟨h2, h3⟩, h4, ⟨h5, h6⟩, ⟨h7, h8⟩, h9, h10⟩
    refine ⟨⟨h1, h2, h4⟩, ?_, h3, h5, h6, h8, h10, h9⟩
    intro k hk
    exact ⟨fun a b c => h7.1 b a c k hk, fun a b c => h7.2 b a c k hk⟩
  · rintro ⟨⟨h1, h2, h4⟩, g1, g2, g3, g4, g5, g6, g7⟩
    refine ⟨h1, ⟨h2, g2⟩, h4, ⟨g3, g4⟩, ⟨⟨?_, ?_⟩, g5⟩, g7, g6⟩
    · intro a b c k hk; exact (g1 k hk).1 b a c
    · intro a b c k hk; exact (g1 k hk).2 b a c

def G (up : Option Row) (fb : Row) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun y : Fin n → Row => Ext up fb y).card

theorem G_succ (up : Option Row) (fb : Row) (n : ℕ) :
    G up fb (n + 1) = ∑ r : Row, if okr up fb r then G (some r) (nfb up r) n else 0 := by
  rw [G, Finset.card_filter, ← (Fin.consEquiv fun _ => Row).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, ext_cons]
  by_cases h : okr up fb r
  · rw [if_pos h, G, Finset.card_filter]
    exact Finset.sum_congr rfl fun B _ => by simp [h]
  · simp [h]

def cnt : ℕ → Option Row → Row → ℕ
  | 0, up, _ => if up = some ![1, 1] then 1 else 0
  | n + 1, up, fb => ∑ r : Row, if okr up fb r then cnt n (some r) (nfb up r) else 0

theorem cnt_succ (n : ℕ) (up : Option Row) (fb : Row) :
    cnt (n + 1) up fb = ∑ r : Row, if okr up fb r then cnt n (some r) (nfb up r) else 0 := by
  rw [cnt]

theorem G_eq (n : ℕ) : ∀ up fb, G up fb n = cnt n up fb := by
  induction n with
  | zero =>
    intro up fb
    rw [G, cnt]
    by_cases h : up = some ![1, 1]
    · rw [if_pos h, Finset.filter_true_of_mem]
      · simp
      · intro y _
        refine ⟨fun k => k.elim0, fun k => k.elim0, fun k => k.elim0, fun k => k.elim0,
          fun k => k.elim0, fun k => k.elim0, fun _ => h⟩
    · rw [if_neg h, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro y _ hy
      exact h (hy.2.2.2.2.2.2 rfl)
  | succ n ih =>
    intro up fb
    rw [G_succ, cnt_succ]
    simp only [ih]

theorem a_eq (m : ℕ) : a (m + 1) = cnt m (some ![1, 1]) ![0, 0] := by
  rw [← G_eq, a, G, Finset.card_filter, Finset.card_filter,
    ← (Fin.consEquiv fun _ => Row).sum_comp, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (![1, 1] : Row)]
  · refine Finset.sum_congr rfl fun y _ => ?_
    have hn : nfb none ![1, 1] = ![0, 0] := by decide +kernel
    have ho : okr none 0 ![1, 1] := by
      refine ⟨by decide, by decide, fun u h => by simp at h⟩
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, valid_iff, Fin.cons_zero, ext_cons, hn, ho,
      true_and]
  · intro r _ hr
    refine Finset.sum_eq_zero fun y _ => ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, valid_iff, Fin.cons_zero, hr, false_and,
      if_false]
  · intro h; exact absurd (Finset.mem_univ _) h

def W (n : ℕ) (up : Option Row) (fb : Row) : ℤ :=
  (cnt (n + 2) up fb : ℤ) - cnt (n + 1) up fb - cnt n up fb

theorem W_succ (n : ℕ) (up : Option Row) (fb : Row) :
    W (n + 1) up fb = ∑ r : Row, if okr up fb r then W n (some r) (nfb up r) else 0 := by
  simp only [W, show n + 1 + 2 = n + 2 + 1 by ring]
  rw [cnt_succ (n + 2) up fb, cnt_succ (n + 1) up fb, cnt_succ n up fb]
  push_cast [Nat.cast_sum, Nat.cast_ite]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> simp

def inS (up : Option Row) (fb : Row) : Prop :=
  (up = some ![1, 1] ∧ fb = ![0, 1]) ∨ (up = some ![1, 1] ∧ fb = ![1, 0]) ∨
    (up = some ![0, 1] ∧ fb = ![0, 0]) ∨ (up = some ![1, 0] ∧ fb = ![0, 0])

instance (up : Option Row) (fb : Row) : Decidable (inS up fb) := by unfold inS; infer_instance

theorem W_base : ∀ up fb, inS up fb → W 0 up fb = 0 := by decide +kernel

theorem inS_step : ∀ up fb, inS up fb → ∀ r, okr up fb r → inS (some r) (nfb up r) := by
  decide +kernel

theorem inS_init : ∀ r, okr (some ![1, 1]) ![0, 0] r → ∀ r', okr (some r) (nfb (some ![1, 1]) r) r' →
    inS (some r') (nfb (some r) r') := by
  decide +kernel

theorem W_zero (n : ℕ) : ∀ up fb, inS up fb → W n up fb = 0 := by
  induction n with
  | zero => exact W_base
  | succ n ih =>
    intro up fb h
    rw [W_succ]
    refine Finset.sum_eq_zero fun r _ => ?_
    split_ifs with hr
    · exact ih _ _ (inS_step up fb h r hr)
    · rfl

theorem a_rec (m : ℕ) : (a (m + 5) : ℤ) = a (m + 4) + a (m + 3) := by
  have h : W (m + 2) (some ![1, 1]) ![0, 0] = 0 := by
    rw [W_succ]
    refine Finset.sum_eq_zero fun r _ => ?_
    split_ifs with hr
    · rw [W_succ]
      refine Finset.sum_eq_zero fun r' _ => ?_
      split_ifs with hr'
      · exact W_zero m _ _ (inS_init r hr r' hr')
      · rfl
    · rfl
  simp only [W] at h
  rw [a_eq, a_eq, a_eq]
  simp only [show m + 2 + 2 = m + 4 by ring, show m + 2 + 1 = m + 3 by ring] at h
  linarith

theorem a1 : a 1 = 1 := by rw [a_eq]; decide +kernel
theorem a2 : a 2 = 1 := by rw [a_eq]; decide +kernel
theorem a3 : a 3 = 2 := by rw [a_eq]; decide +kernel
theorem a4 : a 4 = 2 := by rw [a_eq]; decide +kernel

theorem gf : (1 - X - X ^ 2) * mk (fun n => (a (n + 1) : ℤ)) = (1 - X ^ 3 : PowerSeries ℤ) := by
  set s : PowerSeries ℤ := mk (fun n => (a (n + 1) : ℤ)) with hs
  have hd : (1 - X - X ^ 2) * s = s - s * X ^ 1 - s * X ^ 2 := by
    simp only [pow_one]
    ring
  have hn : (1 - X ^ 3 : PowerSeries ℤ) = C (1 : ℤ) - C (1 : ℤ) * X ^ 3 := by
    simp only [map_one]
    ring
  rw [hd, hn]
  ext n
  simp only [map_sub, coeff_mul_X_pow', coeff_C, hs, coeff_mk]
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n) with h | h | h | h | h
  · subst h; simp [a1]
  · subst h; simp [a1, a2]
  · subst h; simp [a1, a2, a3]
  · subst h; simp [a2, a3, a4]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have := a_rec m
    simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega]
    simp only [show m + 4 + 1 = m + 5 by omega, show m + 3 + 1 = m + 4 by omega,
      show m + 2 + 1 = m + 3 by omega]
    simp
    omega

end A163733Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a163733.main := A163733Proof.gf
