import OMAStatements.S_oeis_a183981
import Mathlib

/-!
Rows are `Fin 5 → Bool` and `OK s r x` says that every `2 × 2` block of the consecutive rows
`r, x` sums to `s`. For `n ≥ 1` the common sum is at most `4` and is fixed by the first block, so
the count is `F n = ∑ s < 5, S s n 1`, where `S s L f` sums `f (last row)` over the row
sequences of length `L + 1` whose consecutive pairs are all `OK s`. The successors of a row are
listed by `nx s` (checked against `OK` on all pairs by `decide +kernel`), which gives a transfer
operator `T s` with `S s (L + m) 1 = S s L (E s m)`. The identity
`E 5 + 6 E 2 = 3 E 4 + 4 E 1` holds on every row, so `F` satisfies the order-4 recurrence; the
closed form and the generating function follow from it and `F 1, …, F 4`.
-/

namespace R183981
open OMA.S_oeis_a183981

abbrev Row := Fin 5 → Bool

abbrev OK (s : ℕ) (r x : Row) : Prop :=
  ∀ j : Fin 4, blockSum (r ⟨j.1, by omega⟩) (r ⟨j.1 + 1, by omega⟩) (x ⟨j.1, by omega⟩)
    (x ⟨j.1 + 1, by omega⟩) = s

def flip (p : ℕ) (r : Row) : Row := fun j => if j.1 % 2 = p then !r j else r j

def allP (p : ℕ) (b : Bool) (r : Row) : Bool := decide (∀ j : Fin 5, j.1 % 2 = p → r j = b)

def alt (r : Row) : Bool := decide (∀ j : Fin 4, r ⟨j.1 + 1, by omega⟩ = !r ⟨j.1, by omega⟩)

def nx : ℕ → Row → List Row
  | 0, r => if allP 0 false r && allP 1 false r then [r] else []
  | 1, r => (if allP 0 false r then [flip 1 r] else []) ++
      (if allP 1 false r then [flip 0 r] else [])
  | 2, r => (fun j => !r j) :: (if alt r then [r] else [])
  | 3, r => (if allP 0 true r then [flip 1 r] else []) ++
      (if allP 1 true r then [flip 0 r] else [])
  | 4, r => if allP 0 true r && allP 1 true r then [r] else []
  | _, _ => []

def T (s : ℕ) (f : Row → ℕ) (r : Row) : ℕ := ((nx s r).map f).sum

def E (s : ℕ) : ℕ → Row → ℕ
  | 0 => fun _ => 1
  | m + 1 => T s (E s m)

def rsum : (m : ℕ) → ((Fin m → Bool) → ℕ) → ℕ
  | 0, f => f Fin.elim0
  | m + 1, f => rsum m (fun x => f (Fin.cons (α := fun _ => Bool) false x)) +
      rsum m (fun x => f (Fin.cons (α := fun _ => Bool) true x))

def rall : (m : ℕ) → ((Fin m → Bool) → Bool) → Bool
  | 0, p => p Fin.elim0
  | m + 1, p => rall m (fun x => p (Fin.cons (α := fun _ => Bool) false x)) &&
      rall m (fun x => p (Fin.cons (α := fun _ => Bool) true x))

theorem rall_spec : ∀ (m : ℕ) (p : (Fin m → Bool) → Bool), rall m p = true → ∀ x, p x = true
  | 0, p, h, x => by
    have hx : x = Fin.elim0 := funext (fun i => Fin.elim0 i)
    rw [hx]
    exact h
  | m + 1, p, h, x => by
    rw [rall, Bool.and_eq_true] at h
    rw [← Fin.cons_self_tail x]
    cases x 0
    · exact rall_spec m _ h.1 (Fin.tail x)
    · exact rall_spec m _ h.2 (Fin.tail x)

theorem rsum_eq : ∀ (m : ℕ) (f : (Fin m → Bool) → ℕ), ∑ x, f x = rsum m f
  | 0, f => by
    rw [Fintype.sum_unique, rsum]
    exact congrArg f (Subsingleton.elim _ _)
  | m + 1, f => by
    rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
      rsum, rsum_eq m, rsum_eq m, add_comm]
    rfl

theorem cnt_dec : ∀ s : Fin 5, rall 5 (fun r => rall 5 (fun x =>
    decide ((if OK s r x then 1 else 0) = (nx s r).count x))) = true := by
  decide +kernel

theorem cnt_eq (s : ℕ) (hs : s < 5) (r x : Row) :
    (if OK s r x then 1 else 0) = (nx s r).count x :=
  of_decide_eq_true (rall_spec 5 _ (rall_spec 5 _ (cnt_dec ⟨s, hs⟩) r) x)

theorem tsum (s : ℕ) (hs : s < 5) (f : Row → ℕ) (r : Row) :
    (∑ x : Row, if OK s r x then f x else 0) = T s f r := by
  have h1 : ((nx s r).map f).sum = ∑ x : Row, (nx s r).count x • f x := by
    rw [Finset.sum_list_map_count]
    refine Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => ?_)
    rw [List.count_eq_zero.2 (fun h => hx (List.mem_toFinset.2 h)), zero_smul]
  rw [T, h1]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← cnt_eq s hs r x]
  split_ifs <;> simp

def S (s L : ℕ) (f : Row → ℕ) : ℕ :=
  ∑ A : Fin (L + 1) → Row,
    if (∀ i : Fin L, OK s (A i.castSucc) (A i.succ)) then f (A (Fin.last L)) else 0

theorem valid_snoc {s L : ℕ} (w : Fin (L + 1) → Row) (x : Row) :
    (∀ i : Fin (L + 1), OK s (Fin.snoc (α := fun _ => Row) w x i.castSucc)
        (Fin.snoc (α := fun _ => Row) w x i.succ)) ↔
      (∀ i : Fin L, OK s (w i.castSucc) (w i.succ)) ∧ OK s (w (Fin.last L)) x := by
  have h1 : ∀ i : Fin L, Fin.snoc (α := fun _ => Row) w x i.castSucc.castSucc = w i.castSucc :=
    fun i => by rw [Fin.snoc_castSucc]
  have h2 : ∀ i : Fin L, Fin.snoc (α := fun _ => Row) w x i.castSucc.succ = w i.succ :=
    fun i => by rw [Fin.succ_castSucc, Fin.snoc_castSucc]
  have h3 : Fin.snoc (α := fun _ => Row) w x (Fin.last L).castSucc = w (Fin.last L) := by
    rw [Fin.snoc_castSucc]
  have h4 : Fin.snoc (α := fun _ => Row) w x (Fin.last L).succ = x := Fin.snoc_last ..
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · have hi := h i.castSucc
      rwa [h1, h2] at hi
    · have hl := h (Fin.last L)
      rwa [h3, h4] at hl
  · rintro ⟨hw, hx⟩ i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [h1, h2]
      exact hw j
    · rw [h3, h4]
      exact hx

theorem step_w {s : ℕ} (hs : s < 5) {L : ℕ} (w : Fin (L + 1) → Row) (f : Row → ℕ) :
    (∑ x : Row, if (∀ i : Fin (L + 1), OK s (Fin.snoc (α := fun _ => Row) w x i.castSucc)
        (Fin.snoc (α := fun _ => Row) w x i.succ))
      then f (Fin.snoc (α := fun _ => Row) w x (Fin.last (L + 1))) else 0) =
    if (∀ i : Fin L, OK s (w i.castSucc) (w i.succ)) then T s f (w (Fin.last L)) else 0 := by
  rw [← tsum s hs]
  by_cases hw : ∀ i : Fin L, OK s (w i.castSucc) (w i.succ)
  · rw [if_pos hw]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : OK s (w (Fin.last L)) x
    · rw [if_pos ((valid_snoc w x).2 ⟨hw, hx⟩), if_pos hx, Fin.snoc_last]
    · rw [if_neg (fun h => hx ((valid_snoc w x).1 h).2), if_neg hx]
  · rw [if_neg hw]
    exact Finset.sum_eq_zero (fun x _ => if_neg (fun h => hw ((valid_snoc w x).1 h).1))

theorem pull {s : ℕ} (hs : s < 5) (L : ℕ) (f : Row → ℕ) : S s (L + 1) f = S s L (T s f) := by
  have he : S s (L + 1) f = ∑ p : Row × (Fin (L + 1) → Row),
      if (∀ i : Fin (L + 1), OK s (Fin.snoc (α := fun _ => Row) p.2 p.1 i.castSucc)
        (Fin.snoc (α := fun _ => Row) p.2 p.1 i.succ))
      then f (Fin.snoc (α := fun _ => Row) p.2 p.1 (Fin.last (L + 1))) else 0 :=
    (Equiv.sum_comp (Fin.snocEquiv fun _ => Row)
      (fun A : Fin (L + 1 + 1) → Row =>
        if (∀ i : Fin (L + 1), OK s (A i.castSucc) (A i.succ))
        then f (A (Fin.last (L + 1))) else 0)).symm
  rw [he, Fintype.sum_prod_type, Finset.sum_comm]
  unfold S
  exact Finset.sum_congr rfl (fun w _ => step_w hs w f)

theorem iter {s : ℕ} (hs : s < 5) (m : ℕ) : ∀ L, S s (L + m) (fun _ => 1) = S s L (E s m) := by
  induction m with
  | zero => intro L; rfl
  | succ m ih =>
    intro L
    rw [show L + (m + 1) = L + 1 + m by omega, ih (L + 1)]
    exact pull hs L (E s m)

theorem S0 (s : ℕ) (f : Row → ℕ) : S s 0 f = ∑ r, f r := by
  rw [← (Equiv.funUnique (Fin 1) Row).sum_comp f]
  unfold S
  refine Fintype.sum_congr _ _ (fun A => ?_)
  have h0 : ∀ i : Fin 0, OK s (A i.castSucc) (A i.succ) := fun i => Fin.elim0 i
  exact (if_pos h0).trans rfl

theorem bs_le (a b c d : Bool) : blockSum a b c d ≤ 4 := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem lt5 {a b c d : Bool} {s : ℕ} (h : blockSum a b c d = s) : s < 5 := by
  rw [← h]
  have := bs_le a b c d
  omega

theorem point (n : ℕ) (hn : 1 ≤ n) (B : Fin (n + 1) → Row) {P : Prop} {dP : Decidable P}
    (hP : P ↔ ∃ s : ℕ, ∀ i : Fin n, OK s (B i.castSucc) (B i.succ)) :
    (if P then 1 else 0) =
      ∑ s : Fin 5, if (∀ i : Fin n, OK s (B i.castSucc) (B i.succ)) then 1 else 0 := by
  by_cases h : ∃ s : ℕ, ∀ i : Fin n, OK s (B i.castSucc) (B i.succ)
  · obtain ⟨s0, hs0⟩ := h
    have key : ∀ t : ℕ, (∀ i : Fin n, OK t (B i.castSucc) (B i.succ)) → t = s0 := by
      intro t ht
      exact (ht ⟨0, hn⟩ ⟨0, by omega⟩).symm.trans (hs0 ⟨0, hn⟩ ⟨0, by omega⟩)
    have hlt : s0 < 5 := lt5 (hs0 ⟨0, hn⟩ ⟨0, by omega⟩)
    rw [if_pos (hP.2 ⟨s0, hs0⟩), Finset.sum_eq_single (⟨s0, hlt⟩ : Fin 5)]
    · exact (if_pos hs0).symm
    · intro t _ ht
      exact if_neg (fun h' => ht (Fin.ext (key t h')))
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · rw [if_neg (fun h' => h (hP.1 h'))]
    symm
    exact Finset.sum_eq_zero (fun t _ => if_neg (fun h' => h ⟨t, h'⟩))

def F (n : ℕ) : ℕ := ∑ s : Fin 5, S s n (fun _ => 1)

theorem card_eq (n : ℕ) (hn : 1 ≤ n) : A183981 n = F n / 4 := by
  rw [A183981, Finset.card_filter]
  congr 1
  rw [← (Equiv.curry (Fin (n + 1)) (Fin 5) Bool).symm.sum_comp]
  unfold F S
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun B _ => point n hn B Iff.rfl)

theorem F_S (L m : ℕ) : F (L + m) = ∑ s : Fin 5, S s L (E s m) :=
  Finset.sum_congr rfl (fun s _ => iter s.isLt m L)

theorem ident_dec : ∀ s : Fin 5, rall 5 (fun r =>
    decide (E s 5 r + 6 * E s 2 r = 3 * E s 4 r + 4 * E s 1 r)) = true := by
  decide +kernel

theorem rec_S (s : Fin 5) (L : ℕ) :
    S s L (E s 5) + 6 * S s L (E s 2) = 3 * S s L (E s 4) + 4 * S s L (E s 1) := by
  unfold S
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  by_cases hA : ∀ i : Fin L, OK s (A i.castSucc) (A i.succ)
  · simp only [if_pos hA]
    exact of_decide_eq_true (rall_spec 5 _ (ident_dec s) _)
  · simp only [if_neg hA, mul_zero, add_zero]

theorem F_rec (L : ℕ) : F (L + 5) + 6 * F (L + 2) = 3 * F (L + 4) + 4 * F (L + 1) := by
  rw [F_S L 5, F_S L 2, F_S L 4, F_S L 1, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun s _ => rec_S s L)

theorem F_val (m : ℕ) : F m = ∑ s : Fin 5, rsum 5 (E s m) := by
  have h := F_S 0 m
  rw [Nat.zero_add] at h
  rw [h]
  exact Finset.sum_congr rfl (fun s _ => by rw [S0, rsum_eq])

theorem F1 : F 1 = 60 := by
  rw [F_val, Fin.sum_univ_five]
  decide +kernel

theorem F2 : F 2 = 68 := by
  rw [F_val, Fin.sum_univ_five]
  decide +kernel

theorem F3 : F 3 = 80 := by
  rw [F_val, Fin.sum_univ_five]
  decide +kernel

theorem F4 : F 4 = 104 := by
  rw [F_val, Fin.sum_univ_five]
  decide +kernel

def hc : ℕ → ℕ
  | 0 => 3
  | 1 => 4
  | n + 2 => 2 * hc n

theorem F_closed : ∀ n, 1 ≤ n → F n = 2 * 2 ^ n + 2 * hc n + 48
  | 0, h => absurd h (by omega)
  | 1, _ => F1.trans (by decide)
  | 2, _ => F2.trans (by decide)
  | 3, _ => F3.trans (by decide)
  | 4, _ => F4.trans (by decide)
  | L + 5, _ => by
    have e := F_rec L
    have i1 := F_closed (L + 1) (by omega)
    have i2 := F_closed (L + 2) (by omega)
    have i4 := F_closed (L + 4) (by omega)
    have hh5 : hc (L + 5) = 4 * hc (L + 1) := by
      rw [show L + 5 = L + 1 + 2 + 2 by omega, hc.eq_3, hc.eq_3]
      ring
    have hh4 : hc (L + 4) = 2 * hc (L + 2) := by
      rw [show L + 4 = L + 2 + 2 by omega, hc.eq_3]
    have p5 : 2 ^ (L + 5) = 32 * 2 ^ L := by ring
    have p4 : 2 ^ (L + 4) = 16 * 2 ^ L := by ring
    have p2 : 2 ^ (L + 2) = 4 * 2 ^ L := by ring
    have p1 : 2 ^ (L + 1) = 2 * 2 ^ L := by ring
    omega

theorem hc_even (q : ℕ) : hc (2 * q) = 3 * 2 ^ q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [show 2 * (q + 1) = 2 * q + 2 by ring, hc.eq_3, ih]
    ring

theorem hc_odd (q : ℕ) : hc (2 * q + 1) = 4 * 2 ^ q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [show 2 * (q + 1) + 1 = 2 * q + 1 + 2 by ring, hc.eq_3, ih]
    ring

theorem hc_two (n : ℕ) (hn : 1 ≤ n) : hc n % 2 = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases m with _ | m
  · rfl
  · rw [show m + 1 + 1 = m + 2 by omega, hc.eq_3]
    omega

theorem pow_pred (n : ℕ) (hn : 1 ≤ n) : 2 ^ n = 2 * 2 ^ (n - 1) := by
  rw [← pow_succ']
  congr 1
  omega

theorem F_four (n : ℕ) (hn : 1 ≤ n) : F n = 4 * A183981 n := by
  rw [card_eq n hn]
  have h1 := F_closed n hn
  have h2 := hc_two n hn
  have h3 := pow_pred n hn
  omega

theorem A_rec (L : ℕ) :
    A183981 (L + 5) + 6 * A183981 (L + 2) = 3 * A183981 (L + 4) + 4 * A183981 (L + 1) := by
  have e := F_rec L
  rw [F_four (L + 5) (by omega), F_four (L + 2) (by omega), F_four (L + 4) (by omega),
    F_four (L + 1) (by omega)] at e
  omega

theorem A1 : A183981 1 = 15 := by have := F_four 1 le_rfl; rw [F1] at this; omega
theorem A2 : A183981 2 = 17 := by have := F_four 2 (by norm_num); rw [F2] at this; omega
theorem A3 : A183981 3 = 20 := by have := F_four 3 (by norm_num); rw [F3] at this; omega
theorem A4 : A183981 4 = 26 := by have := F_four 4 (by norm_num); rw [F4] at this; omega

noncomputable def Bs (j : ℕ) : PowerSeries ℤ := PowerSeries.mk (fun n => (A183981 (n + j) : ℤ))

theorem shiftB (j : ℕ) : Bs j = PowerSeries.C (A183981 j : ℤ) + PowerSeries.X * Bs (j + 1) := by
  ext m
  rcases m with _ | m
  · rw [map_add, Bs, PowerSeries.coeff_mk, PowerSeries.coeff_zero_X_mul,
      PowerSeries.coeff_zero_C, Nat.zero_add, add_zero]
  · rw [map_add, Bs, PowerSeries.coeff_mk, PowerSeries.coeff_succ_X_mul, Bs,
      PowerSeries.coeff_mk, PowerSeries.coeff_C, if_neg (Nat.add_one_ne_zero m), zero_add,
      show m + 1 + j = m + (j + 1) by omega]

theorem ps : (1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A183981 n : ℤ)) =
      PowerSeries.X * (15 - 28 * PowerSeries.X - 31 * PowerSeries.X ^ 2 +
        56 * PowerSeries.X ^ 3) := by
  have s0 : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A183981 n : ℤ)) =
      PowerSeries.X * Bs 1 := by
    ext m
    rcases m with _ | m
    · rw [PowerSeries.coeff_mk, PowerSeries.coeff_zero_X_mul, if_pos rfl]
    · rw [PowerSeries.coeff_mk, PowerSeries.coeff_succ_X_mul, Bs, PowerSeries.coeff_mk,
        if_neg (Nat.add_one_ne_zero m)]
  have s1 : Bs 1 = 15 + PowerSeries.X * Bs 2 := by rw [shiftB, A1]; norm_num
  have s2 : Bs 2 = 17 + PowerSeries.X * Bs 3 := by rw [shiftB, A2]; norm_num
  have s3 : Bs 3 = 20 + PowerSeries.X * Bs 4 := by rw [shiftB, A3]; norm_num
  have s4 : Bs 4 = 26 + PowerSeries.X * Bs 5 := by rw [shiftB, A4]; norm_num
  have R : Bs 5 + PowerSeries.C 6 * Bs 2 = PowerSeries.C 3 * Bs 4 + PowerSeries.C 4 * Bs 1 := by
    ext m
    simp only [Bs, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    have := A_rec m
    exact_mod_cast this
  simp only [map_ofNat] at R
  rw [s0]
  linear_combination (PowerSeries.X - 3 * PowerSeries.X ^ 2 + 6 * PowerSeries.X ^ 4) * s1 +
    (PowerSeries.X ^ 2 - 3 * PowerSeries.X ^ 3) * s2 +
    (PowerSeries.X ^ 3 - 3 * PowerSeries.X ^ 4) * s3 + PowerSeries.X ^ 4 * s4 +
    PowerSeries.X ^ 5 * R

theorem closed_even (n : ℕ) (hn : 1 ≤ n) (he : Even n) :
    2 * A183981 n = 3 * 2 ^ (n / 2) + 2 ^ n + 24 := by
  have hF := F_four n hn
  have hC := F_closed n hn
  have h3 := pow_pred n hn
  obtain ⟨q, rfl⟩ := he
  have hq2 := hc_even q
  rw [show 2 * q = q + q by ring] at hq2
  rw [show (q + q) / 2 = q by omega]
  have hq := pow_pred q (by omega)
  omega

theorem closed_odd (n : ℕ) (hn : 1 ≤ n) (he : ¬Even n) :
    A183981 n = 2 ^ ((n + 1) / 2) + 2 ^ (n - 1) + 12 := by
  have hF := F_four n hn
  have hC := F_closed n hn
  have h3 := pow_pred n hn
  obtain ⟨q, rfl⟩ := Nat.not_even_iff_odd.1 he
  rw [hc_odd] at hC
  rw [show (2 * q + 1 + 1) / 2 = q + 1 by omega, pow_succ]
  omega

end R183981

theorem OMA.solution : type_of% @OMA.S_oeis_a183981.main := by
  refine ⟨R183981.ps, fun n hn => ?_⟩
  split_ifs with he
  · exact R183981.closed_even n hn he
  · exact R183981.closed_odd n hn he
