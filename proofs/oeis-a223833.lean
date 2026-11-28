import OMAStatements.S_oeis_a223833
import Mathlib

/-!
OEIS A223833. Transfer argument on the last two rows.  Rows are encoded as triples of bits.
For the first two rows u, v let U m u v be the number of good arrays with m + 2 rows starting
with u, v.  Peeling off the first row gives a linear recursion for U, and from one step on
every U is a cubic polynomial in m written in the binomial basis; the coefficient tables are
checked by kernel evaluation.
-/

namespace OMA.A223833aux

open OMA.S_oeis_a223833

abbrev T := Fin 2 × Fin 2 × Fin 2

def dec (t : T) : Fin 3 → Fin 2 := ![t.1, t.2.1, t.2.2]

def enc (r : Fin 3 → Fin 2) : T := (r 0, r 1, r 2)

theorem dec_enc (r : Fin 3 → Fin 2) : dec (enc r) = r := by
  funext i
  fin_cases i <;> rfl

theorem enc_dec (t : T) : enc (dec t) = t := by
  obtain ⟨a, b, c⟩ := t
  rfl

def encEquiv : (Fin 3 → Fin 2) ≃ T := ⟨enc, dec, dec_enc, enc_dec⟩

def LnT (t : T) : Prop := LineOK (dec t)

def BkT (u v : T) : Prop := BlockOK (dec u) (dec v)

def TrT (u v w : T) : Prop := TriOK (dec u) (dec v) (dec w)

instance : DecidablePred LnT := fun t => by
  unfold LnT LineOK
  infer_instance

instance : DecidableRel BkT := fun u v => by
  unfold BkT BlockOK
  infer_instance

instance (u v w : T) : Decidable (TrT u v w) := by
  unfold TrT TriOK
  infer_instance

abbrev GoodT {n : ℕ} (y : Fin n → T) : Prop :=
  (∀ i, LnT (y i)) ∧
    (∀ i j : Fin n, (j : ℕ) = i + 1 → BkT (y i) (y j)) ∧
    (∀ i j l : Fin n, (j : ℕ) = i + 1 → (l : ℕ) = j + 1 → TrT (y i) (y j) (y l))

theorem goodT_iff {n : ℕ} (y : Fin n → T) : GoodT y ↔ Good (fun i => dec (y i)) := Iff.rfl

theorem a_eq (n : ℕ) : a n = (Finset.univ.filter (fun y : Fin n → T => GoodT y)).card := by
  unfold a
  have e : {x : Fin n → Fin 3 → Fin 2 // Good x} ≃ {y : Fin n → T // GoodT y} :=
    (Equiv.piCongrRight (fun _ => encEquiv)).subtypeEquiv (fun x => by
      show Good x ↔ GoodT (fun i => enc (x i))
      have h : (fun i => dec (enc (x i))) = x := by
        funext i
        exact dec_enc (x i)
      rw [goodT_iff]
      show Good x ↔ Good (fun i => dec (enc (x i)))
      rw [h])
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem v1 (m : ℕ) : ((1 : Fin (m + 3)) : ℕ) = 1 := by
  simp

theorem v2 (m : ℕ) : ((2 : Fin (m + 3)) : ℕ) = 2 := by
  simp

theorem good_peel {m : ℕ} (y : Fin (m + 3) → T) :
    GoodT y ↔ LnT (y 0) ∧ BkT (y 0) (y 1) ∧ TrT (y 0) (y 1) (y 2) ∧ GoodT (Fin.tail y) := by
  constructor
  · rintro ⟨hL, hB, hT⟩
    refine ⟨hL 0, hB 0 1 (by rw [v1]; simp), hT 0 1 2 (by rw [v1]; simp) (by rw [v1, v2]), ?_, ?_, ?_⟩
    · intro i
      exact hL i.succ
    · intro i j hij
      exact hB i.succ j.succ (by simp [hij])
    · intro i j l h1 h2
      exact hT i.succ j.succ l.succ (by simp [h1]) (by simp [h2])
  · rintro ⟨hL0, hB0, hT0, gL, gB, gT⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i
      refine Fin.cases hL0 (fun i' => ?_) i
      exact gL i'
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        have hj : j = 1 := Fin.ext (by rw [v1]; simpa using hij)
        subst hj
        exact hB0
      | succ i' =>
        induction j using Fin.cases with
        | zero => simp at hij
        | succ j' => exact gB i' j' (by simpa using hij)
    · intro i j l h1 h2
      induction i using Fin.cases with
      | zero =>
        have hj : j = 1 := Fin.ext (by rw [v1]; simpa using h1)
        subst hj
        have hl : l = 2 := Fin.ext (by rw [v2]; rw [v1] at h2; simpa using h2)
        subst hl
        exact hT0
      | succ i' =>
        induction j using Fin.cases with
        | zero => simp at h1
        | succ j' =>
          induction l using Fin.cases with
          | zero => simp at h2
          | succ l' => exact gT i' j' l' (by simpa using h1) (by simpa using h2)

theorem good2 (y : Fin 2 → T) : GoodT y ↔ LnT (y 0) ∧ LnT (y 1) ∧ BkT (y 0) (y 1) := by
  constructor
  · rintro ⟨hL, hB, -⟩
    exact ⟨hL 0, hL 1, hB 0 1 rfl⟩
  · rintro ⟨h0, h1, hB⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact h0
      · exact h1
    · intro i j hij
      have hjlt := j.isLt
      have hi : i = 0 := Fin.ext (by show (i : ℕ) = 0; omega)
      have hj : j = 1 := Fin.ext (by show (j : ℕ) = 1; omega)
      subst hi
      subst hj
      exact hB
    · intro i j l h1' h2'
      have := l.isLt
      omega

def U (m : ℕ) (u v : T) : ℕ :=
  (Finset.univ.filter (fun y : Fin (m + 2) → T => GoodT y ∧ y 0 = u ∧ y 1 = v)).card

theorem U_zero (u v : T) : U 0 u v = if LnT u ∧ LnT v ∧ BkT u v then 1 else 0 := by
  unfold U
  by_cases hc : LnT u ∧ LnT v ∧ BkT u v
  · rw [if_pos hc, Finset.card_eq_one]
    refine ⟨![u, v], ?_⟩
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h0, h1⟩
      funext i
      fin_cases i
      · simpa using h0
      · simpa using h1
    · rintro rfl
      exact ⟨(good2 _).2 hc, rfl, rfl⟩
  · rw [if_neg hc, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y _ hy
    obtain ⟨hg, h0, h1⟩ := hy
    have := (good2 y).1 hg
    rw [h0, h1] at this
    exact hc this

theorem U_succ (m : ℕ) (u v : T) :
    U (m + 1) u v
      = if LnT u ∧ BkT u v then ∑ w : T, (if TrT u v w then U m v w else 0) else 0 := by
  by_cases hc : LnT u ∧ BkT u v
  · rw [if_pos hc]
    have h1 : U (m + 1) u v
        = ((Finset.univ.filter (fun w : T => TrT u v w)).sigma
            (fun w => Finset.univ.filter
              (fun z : Fin (m + 2) → T => GoodT z ∧ z 0 = v ∧ z 1 = w))).card := by
      unfold U
      refine Finset.card_nbij' (fun y => ⟨y 2, Fin.tail y⟩)
        (fun p => Fin.cons (α := fun _ => T) u p.2) ?_ ?_ ?_ ?_
      · intro y hy
        obtain ⟨hg, h0, h1⟩ := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
        obtain ⟨_, _, hT, hG⟩ := (good_peel y).1 hg
        refine Finset.mem_coe.2 (Finset.mem_sigma.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩,
          Finset.mem_filter.2 ⟨Finset.mem_univ _, hG, ?_, ?_⟩⟩)
        · rw [← h0, ← h1]
          exact hT
        · show y (Fin.succ 0) = v
          rw [Fin.succ_zero_eq_one]
          exact h1
        · show y (Fin.succ 1) = y 2
          rw [Fin.succ_one_eq_two]
      · intro p hp
        have hp' := Finset.mem_sigma.1 (Finset.mem_coe.1 hp)
        have hT := (Finset.mem_filter.1 hp'.1).2
        obtain ⟨hG, h0, h1⟩ := (Finset.mem_filter.1 hp'.2).2
        have c0 : (Fin.cons (α := fun _ => T) u p.2 : Fin (m + 3) → T) 0 = u := rfl
        have c1 : (Fin.cons (α := fun _ => T) u p.2 : Fin (m + 3) → T) 1 = v := by
          rw [← Fin.succ_zero_eq_one, Fin.cons_succ]
          exact h0
        have c2 : (Fin.cons (α := fun _ => T) u p.2 : Fin (m + 3) → T) 2 = p.1 := by
          rw [← Fin.succ_one_eq_two, Fin.cons_succ]
          exact h1
        refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _,
          (good_peel _).2 ⟨?_, ?_, ?_, ?_⟩, c0, c1⟩)
        · beta_reduce
          rw [c0]
          exact hc.1
        · beta_reduce
          rw [c0, c1]
          exact hc.2
        · beta_reduce
          rw [c0, c1, c2]
          exact hT
        · beta_reduce
          rw [Fin.tail_cons]
          exact hG
      · intro y hy
        obtain ⟨hg, h0, h1⟩ := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
        show Fin.cons (α := fun _ => T) u (Fin.tail y) = y
        rw [← h0]
        exact Fin.cons_self_tail y
      · intro p hp
        have hp' := Finset.mem_sigma.1 (Finset.mem_coe.1 hp)
        obtain ⟨hG, h0, h1⟩ := (Finset.mem_filter.1 hp'.2).2
        obtain ⟨w, z⟩ := p
        have c2 : (Fin.cons (α := fun _ => T) u z : Fin (m + 3) → T) 2 = w := by
          rw [← Fin.succ_one_eq_two, Fin.cons_succ]
          exact h1
        show (⟨(Fin.cons (α := fun _ => T) u z : Fin (m + 3) → T) 2,
          Fin.tail (Fin.cons (α := fun _ => T) u z)⟩ : (_ : T) × (Fin (m + 2) → T)) = ⟨w, z⟩
        rw [c2, Fin.tail_cons]
    rw [h1, Finset.card_sigma, Finset.sum_filter]
    rfl
  · rw [if_neg hc]
    unfold U
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y _ hy
    obtain ⟨hg, h0, h1⟩ := hy
    obtain ⟨hL, hB, _, _⟩ := (good_peel y).1 hg
    rw [h0] at hL
    rw [h0, h1] at hB
    exact hc ⟨hL, hB⟩

def idx (t : T) : ℕ := t.1.val * 4 + t.2.1.val * 2 + t.2.2.val

def look (tb : List (List ℕ)) (u v : T) : ℕ := (tb.getD (idx u) []).getD (idx v) 0

def d0 : T → T → ℕ := look [[7, 3, 4, 2, 3, 0, 2, 1], [0, 2, 0, 2, 0, 0, 0, 1],
  [0, 0, 4, 2, 0, 0, 2, 1], [0, 0, 0, 2, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 2, 1],
  [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 1], [0, 0, 0, 0, 0, 0, 0, 1]]

def d1 : T → T → ℕ := look [[15, 2, 5, 1, 2, 0, 1, 0], [0, 2, 0, 1, 0, 0, 0, 0],
  [0, 0, 5, 1, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 1, 0],
  [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0]]

def d2 : T → T → ℕ := look [[11, 1, 2, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0],
  [0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]

def d3 : T → T → ℕ := look [[4, 0, 0, 0, 0, 0, 0, 0], [], [], [], [], [], [], []]

set_option maxRecDepth 100000 in
theorem F0 : ∀ u v : T, (if LnT u ∧ BkT u v then
    ∑ w : T, (if TrT u v w then (if LnT v ∧ LnT w ∧ BkT v w then 1 else 0) else 0) else 0)
      = d0 u v := by
  decide

set_option maxRecDepth 100000 in
theorem F1 : ∀ u v : T, (if LnT u ∧ BkT u v then
    ∑ w : T, (if TrT u v w then d0 v w else 0) else 0) = d0 u v + d1 u v := by
  decide

set_option maxRecDepth 100000 in
theorem F2 : ∀ u v : T, (if LnT u ∧ BkT u v then
    ∑ w : T, (if TrT u v w then d1 v w else 0) else 0) = d1 u v + d2 u v := by
  decide

set_option maxRecDepth 100000 in
theorem F3 : ∀ u v : T, (if LnT u ∧ BkT u v then
    ∑ w : T, (if TrT u v w then d2 v w else 0) else 0) = d2 u v + d3 u v := by
  decide

set_option maxRecDepth 100000 in
theorem F4 : ∀ u v : T, (if LnT u ∧ BkT u v then
    ∑ w : T, (if TrT u v w then d3 v w else 0) else 0) = d3 u v := by
  decide

set_option maxRecDepth 100000 in
theorem S0 : ∑ s : T × T, d0 s.1 s.2 = 48 := by decide

set_option maxRecDepth 100000 in
theorem S1 : ∑ s : T × T, d1 s.1 s.2 = 41 := by decide

set_option maxRecDepth 100000 in
theorem S2 : ∑ s : T × T, d2 s.1 s.2 = 19 := by decide

set_option maxRecDepth 100000 in
theorem S3 : ∑ s : T × T, d3 s.1 s.2 = 4 := by decide

set_option maxRecDepth 100000 in
theorem Se : ∑ s : T × T, (if LnT s.1 ∧ LnT s.2 ∧ BkT s.1 s.2 then 1 else 0) = 22 := by decide

set_option maxRecDepth 100000 in
theorem L7 : (Finset.univ.filter (fun t : T => LnT t)).card = 7 := by decide

theorem Upoly (m : ℕ) : ∀ u v : T, U (m + 1) u v
    = d0 u v + d1 u v * m + d2 u v * m.choose 2 + d3 u v * m.choose 3 := by
  induction m with
  | zero =>
    intro u v
    rw [U_succ]
    simp only [U_zero]
    rw [F0 u v]
    simp
  | succ m ih =>
    intro u v
    rw [U_succ]
    have key : ∀ w : T, (if TrT u v w then U (m + 1) v w else 0)
        = (if TrT u v w then d0 v w else 0) + (if TrT u v w then d1 v w else 0) * m
          + (if TrT u v w then d2 v w else 0) * m.choose 2
          + (if TrT u v w then d3 v w else 0) * m.choose 3 := by
      intro w
      rw [ih v w]
      by_cases h : TrT u v w <;> simp [h]
    rw [Finset.sum_congr rfl (fun w _ => key w)]
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
    have f1 := F1 u v
    have f2 := F2 u v
    have f3 := F3 u v
    have f4 := F4 u v
    have p2 : (m + 1).choose 2 = m.choose 1 + m.choose 2 := Nat.choose_succ_succ m 1
    have p3 : (m + 1).choose 3 = m.choose 2 + m.choose 3 := Nat.choose_succ_succ m 2
    rw [Nat.choose_one_right] at p2
    by_cases hc : LnT u ∧ BkT u v
    · rw [if_pos hc] at f1 f2 f3 f4 ⊢
      rw [f1, f2, f3, f4, p2, p3]
      ring
    · rw [if_neg hc] at f1 f2 f3 f4 ⊢
      have z0 : d0 u v = 0 := by omega
      have z1 : d1 u v = 0 := by omega
      have z2 : d2 u v = 0 := by omega
      have z3 : d3 u v = 0 := by omega
      rw [z0, z1, z2, z3]
      simp

theorem fiber (m : ℕ) : (Finset.univ.filter (fun y : Fin (m + 2) → T => GoodT y)).card
    = ∑ s : T × T, U m s.1 s.2 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun y => (y 0, y 1)) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  unfold U
  congr 1
  ext y
  constructor
  · intro h
    have h1 := Finset.mem_filter.1 h
    have h2 := Finset.mem_filter.1 h1.1
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h2.2, congrArg Prod.fst h1.2,
      congrArg Prod.snd h1.2⟩
  · intro h
    have h1 := Finset.mem_filter.1 h
    exact Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, h1.2.1⟩,
      Prod.ext h1.2.2.1 h1.2.2.2⟩

theorem a_one : a 1 = 7 := by
  rw [a_eq]
  have e : (Finset.univ.filter (fun y : Fin 1 → T => GoodT y)).card
      = (Finset.univ.filter (fun t : T => LnT t)).card := by
    refine Finset.card_nbij' (fun y => y 0) (fun t => fun _ => t) ?_ ?_ ?_ ?_
    · intro y hy
      have h := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
      exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, h.1 0⟩)
    · intro t ht
      have h := (Finset.mem_filter.1 (Finset.mem_coe.1 ht)).2
      refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, fun _ => h, ?_, ?_⟩)
      · intro i j hij
        have := j.isLt
        omega
      · intro i j l h1 h2
        have := l.isLt
        omega
    · intro y hy
      funext i
      show y 0 = y i
      rw [Fin.eq_zero i]
    · intro t ht
      rfl
  rw [e]
  exact L7

theorem a_two : a 2 = 22 := by
  rw [a_eq]
  have h := fiber 0
  simp only [U_zero] at h
  rw [Se] at h
  exact h

theorem a_ge3 (m : ℕ) : a (m + 3) = 48 + 41 * m + 19 * m.choose 2 + 4 * m.choose 3 := by
  have h : a (m + 3) = ∑ s : T × T, U (m + 1) s.1 s.2 := (a_eq (m + 3)).trans (fiber (m + 1))
  rw [h]
  simp only [Upoly]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, S0, S1, S2, S3]

theorem ch2 (m : ℕ) : ((m.choose 2 : ℕ) : ℚ) = (m : ℚ) * ((m : ℚ) - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have p2 : (m + 1).choose 2 = m.choose 1 + m.choose 2 := Nat.choose_succ_succ m 1
    rw [p2, Nat.choose_one_right]
    push_cast
    rw [ih]
    ring

theorem ch3 (m : ℕ) : ((m.choose 3 : ℕ) : ℚ) = (m : ℚ) * ((m : ℚ) - 1) * ((m : ℚ) - 2) / 6 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have p3 : (m + 1).choose 3 = m.choose 2 + m.choose 3 := Nat.choose_succ_succ m 2
    rw [p3]
    push_cast
    rw [ih, ch2]
    ring

theorem closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ)
    = (2 / 3) * (n : ℚ) ^ 3 + (3 / 2) * (n : ℚ) ^ 2 + (35 / 6) * (n : ℚ) - 1 := by
  by_cases h1 : n = 1
  · subst h1
    rw [a_one]
    norm_num
  by_cases h2 : n = 2
  · subst h2
    rw [a_two]
    norm_num
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [a_ge3 m]
  push_cast
  rw [ch2, ch3]
  ring

theorem gf_aux (f : ℕ → ℚ) (h0 : f 0 = 0) (h1 : f 1 = 7) (h2 : f 2 = 22) (h3 : f 3 = 48)
    (h4 : f 4 = 89)
    (hr : ∀ n, f (n + 5) = 4 * f (n + 4) - 6 * f (n + 3) + 4 * f (n + 2) - f (n + 1)) :
    PowerSeries.mk f * (1 - PowerSeries.X) ^ 4
      = PowerSeries.X * (7 - 6 * PowerSeries.X + 2 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3) := by
  have k2 : (PowerSeries.C (2 : ℚ) : PowerSeries ℚ) = 2 := map_ofNat _ 2
  have k4 : (PowerSeries.C (4 : ℚ) : PowerSeries ℚ) = 4 := map_ofNat _ 4
  have k6 : (PowerSeries.C (6 : ℚ) : PowerSeries ℚ) = 6 := map_ofNat _ 6
  have k7 : (PowerSeries.C (7 : ℚ) : PowerSeries ℚ) = 7 := map_ofNat _ 7
  have e1 : PowerSeries.mk f * (1 - PowerSeries.X) ^ 4
      = PowerSeries.mk f - PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 1 * PowerSeries.mk f)
        + PowerSeries.C (6 : ℚ) * (PowerSeries.X ^ 2 * PowerSeries.mk f)
        - PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 3 * PowerSeries.mk f)
        + PowerSeries.X ^ 4 * PowerSeries.mk f := by
    rw [k4, k6]
    ring
  have e2 : (PowerSeries.X : PowerSeries ℚ)
        * (7 - 6 * PowerSeries.X + 2 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3)
      = PowerSeries.C (7 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 2
        + PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.X ^ 4 := by
    rw [k2, k6, k7]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_mk, PowerSeries.coeff_X_pow]
  rcases n with _ | _ | _ | _ | _ | n
  · norm_num [h0]
  · norm_num [h0, h1]
  · norm_num [h0, h1, h2]
  · norm_num [h0, h1, h2, h3]
  · norm_num [h0, h1, h2, h3, h4]
  · have := hr n
    simp
    linarith

end OMA.A223833aux

open OMA.S_oeis_a223833 OMA.A223833aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a223833.main := by
  have hq : ∀ k : ℕ, (a (k + 5) : ℚ) = 4 * (a (k + 4) : ℚ) - 6 * (a (k + 3) : ℚ)
      + 4 * (a (k + 2) : ℚ) - (a (k + 1) : ℚ) := by
    intro k
    rw [closed (k + 5) (by omega), closed (k + 4) (by omega), closed (k + 3) (by omega),
      closed (k + 2) (by omega), closed (k + 1) (by omega)]
    push_cast
    ring
  refine ⟨?_, ?_, closed⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
    have e1 : k + 5 - 1 = k + 4 := by omega
    have e2 : k + 5 - 2 = k + 3 := by omega
    have e3 : k + 5 - 3 = k + 2 := by omega
    have e4 : k + 5 - 4 = k + 1 := by omega
    rw [e1, e2, e3, e4]
    have := hq k
    exact_mod_cast this
  · unfold G
    rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    apply gf_aux
    · simp
    · simp [a_one]
    · simp [a_two]
    · have h := closed 3 (by norm_num)
      norm_num at h
      simp [h]
    · have h := closed 4 (by norm_num)
      norm_num at h
      simp [h]
    · intro n
      have := hq n
      simpa using this
