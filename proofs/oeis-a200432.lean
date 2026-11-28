import OMAStatements.S_oeis_a200432
import Mathlib

/-! Proof for OEIS A200432: under zero sum, a run of three adjacent entries sums to zero iff the other two
(adjacent) entries do, so the conditions say that all five cyclic adjacent pairs have nonzero sum.
Inclusion–exclusion over these five pairs (Mathlib's `inclusion_exclusion_card_inf_compl`), with the
subsets reduced by rotation to eight representatives, gives
`a(n) = N5 - 5(2n+1)N3 + 5N3 + 5(2n+1)^2 - 10(2n+1) + 4`, where `N3 = 3n^2 + 3n + 1` and
`N5 = (115n^4 + 230n^3 + 185n^2 + 70n + 12)/12` count zero-sum arrays of length 3 and 5, computed as
coefficients of `(1 + x + ⋯ + x^(2n))^k`. Hence `a(n) = 5n(n-1)(23n^2 - 3n + 10)/12`, and the g.f.
follows coefficientwise.
Credit: Sudharsan Rajendiran -/

namespace OMA.P200432
open Finset OMA.S_oeis_a200432

/-! ## Zero-sum arrays via generating functions -/

noncomputable abbrev arrN (m k : ℕ) : Finset (Fin k → ℕ) := Fintype.piFinset fun _ : Fin k => range (m + 1)

/-- `1 + X + ⋯ + X^m`. -/
noncomputable def PP (m : ℕ) : PowerSeries ℚ := ∑ i ∈ range (m + 1), PowerSeries.X ^ i

lemma coeff_PP (m i : ℕ) : PowerSeries.coeff i (PP m) = if i ≤ m then 1 else 0 := by
  unfold PP
  simp [map_sum, PowerSeries.coeff_X_pow, Nat.lt_succ_iff]

lemma cnt_coeff (m : ℕ) : ∀ (k s : ℕ),
    (((arrN m k).filter (fun a => ∑ i, a i = s)).card : ℚ) = PowerSeries.coeff s (PP m ^ k) := by
  intro k
  induction k with
  | zero =>
    intro s
    simp only [pow_zero, PowerSeries.coeff_one]
    by_cases hs : s = 0
    · subst hs; rw [filter_true_of_mem (fun a _ => by simp)]; simp
    · rw [if_neg hs]
      rw [show (arrN m 0).filter (fun a => ∑ i, a i = s) = ∅ by
        rw [filter_eq_empty_iff]; intro a _; simp [Ne.symm hs]]
      simp
  | succ k ih =>
    intro s
    rw [pow_succ', PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have e : ((arrN m (k + 1)).filter (fun a => ∑ i, a i = s)).card =
        ∑ x ∈ range (s + 1), ((range (m + 1)).filter (fun y => y = x)).card *
          ((arrN m k).filter (fun a => ∑ i, a i = s - x)).card := by
      rw [card_eq_sum_card_fiberwise (f := fun a => a 0) (t := range (s + 1))]
      · apply sum_congr rfl; intro x hx
        simp only [mem_range] at hx
        rw [show ((range (m + 1)).filter (fun y => y = x)).card = if x ≤ m then 1 else 0 by
          split_ifs with h
          · rw [card_eq_one]; exact ⟨x, by ext y; simp only [mem_filter, mem_range, mem_singleton]; exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩⟩
          · rw [card_eq_zero, filter_eq_empty_iff]; intro y hy; simp at hy; omega]
        split_ifs with hxm
        · rw [one_mul]
          apply card_nbij' (fun a => Fin.tail a) (fun w => Fin.cons x w)
          · intro a ha
            simp only [coe_filter, Fintype.mem_piFinset, mem_range, Set.mem_ofPred_eq, mem_filter] at ha ⊢
            refine ⟨fun i => ha.1.1 _, ?_⟩
            have := ha.1.2; rw [Fin.sum_univ_succ] at this
            have h2 := ha.2
            show ∑ i : Fin k, a i.succ = s - x; omega
          · intro w hw
            simp only [coe_filter, Fintype.mem_piFinset, mem_range, Set.mem_ofPred_eq, mem_filter] at hw ⊢
            refine ⟨⟨fun i => ?_, ?_⟩, by simp⟩
            · refine Fin.cases ?_ (fun j => ?_) i
              · simp; omega
              · simpa using hw.1 j
            · rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]; omega
          · intro a ha
            simp only [coe_filter, mem_filter] at ha
            rw [← ha.2]; exact Fin.cons_self_tail a
          · intro w _; simp
        · rw [zero_mul, card_eq_zero, filter_eq_empty_iff]
          intro a ha h0
          simp only [mem_filter, Fintype.mem_piFinset, mem_range] at ha
          have := ha.1 0; omega
      · intro a ha
        simp only [mem_coe, mem_filter, Fintype.mem_piFinset] at ha
        simp only [mem_coe, mem_range]
        have := ha.2; rw [Fin.sum_univ_succ] at this; omega
    rw [e]; push_cast
    apply sum_congr rfl; intro x hx
    simp only [mem_range] at hx
    rw [ih, coeff_PP]
    split_ifs with h
    · rw [show ((range (m + 1)).filter (fun y => y = x)).card = 1 by
        rw [card_eq_one]; exact ⟨x, by ext y; simp only [mem_filter, mem_range, mem_singleton]; exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩⟩]; simp
    · rw [show ((range (m + 1)).filter (fun y => y = x)).card = 0 by
        rw [card_eq_zero, filter_eq_empty_iff]; intro y hy; simp at hy; omega]; simp


lemma PP_mul (m : ℕ) : PP m * (1 - PowerSeries.X) = 1 - PowerSeries.X ^ (m + 1) := by
  unfold PP; rw [mul_sub, mul_one, sum_mul]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, sum_range_succ (fun i => PowerSeries.X ^ i * PowerSeries.X)]
    calc _ = (∑ x ∈ range (m + 1), PowerSeries.X ^ x - ∑ i ∈ range (m + 1), PowerSeries.X ^ i * PowerSeries.X)
          + PowerSeries.X ^ (m + 1) - PowerSeries.X ^ (m + 1) * PowerSeries.X := by ring
      _ = _ := by rw [ih]; ring

/-- `1/(1 - X)^(d+1)`. -/
noncomputable def GG (d : ℕ) : PowerSeries ℚ := PowerSeries.mk fun j => ((d + j).choose d : ℚ)

lemma GG_inv (d : ℕ) : (1 - PowerSeries.X) ^ (d + 1) * GG d = 1 := by
  have := (PowerSeries.invOneSubPow ℚ (d + 1)).inv_val
  rw [PowerSeries.invOneSubPow_inv_eq_one_sub_pow] at this
  simpa [GG, PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose] using this

lemma PP_pow (m d : ℕ) : PP m ^ (d + 1) = (1 - PowerSeries.X ^ (m + 1)) ^ (d + 1) * GG d := by
  calc PP m ^ (d + 1) = PP m ^ (d + 1) * ((1 - PowerSeries.X) ^ (d + 1) * GG d) := by rw [GG_inv, mul_one]
    _ = (PP m * (1 - PowerSeries.X)) ^ (d + 1) * GG d := by rw [mul_pow, mul_assoc]
    _ = _ := by rw [PP_mul]

lemma cXG (d s : ℕ) (c : ℚ) (j : ℕ) : PowerSeries.coeff s (PowerSeries.C c * (PowerSeries.X ^ j * GG d)) =
    c * (if j ≤ s then ((d + (s - j)).choose d : ℚ) else 0) := by
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  simp [GG]

lemma choose4 (a : ℕ) : ((a.choose 4 : ℕ) : ℚ) = (a : ℚ) * (a - 1) * (a - 2) * (a - 3) / 24 := by
  rw [Nat.cast_choose_eq_descPochhammer_div]
  simp [descPochhammer_succ_right, Polynomial.eval_mul, Nat.factorial] <;> ring

/-- zero-sum arrays of length `k` in `[-n, n]`. -/
noncomputable def Zk (n k : ℕ) : Finset (Fin k → ℤ) :=
  (Fintype.piFinset fun _ : Fin k => Icc (-(n : ℤ)) n).filter (fun v => ∑ i, v i = 0)

lemma Zk_shift (n k : ℕ) : (Zk n k).card = ((arrN (2 * n) k).filter (fun a => ∑ i, a i = k * n)).card := by
  unfold Zk
  apply card_nbij' (fun v : Fin k → ℤ => fun i => (v i + n).toNat) (fun a : Fin k → ℕ => fun i => (a i : ℤ) - n)
  · intro v hv
    simp only [coe_filter, Fintype.mem_piFinset, mem_Icc, Set.mem_ofPred_eq, mem_range] at hv ⊢
    refine ⟨fun i => by have := hv.1 i; omega, ?_⟩
    have h1 : ((∑ i, (v i + n).toNat : ℕ) : ℤ) = ∑ i, (v i + n) := by
      push_cast; apply sum_congr rfl; intro i _; have := hv.1 i; omega
    have h2 : ∑ i, (v i + (n : ℤ)) = k * n := by rw [sum_add_distrib, hv.2]; simp
    exact_mod_cast h1.trans h2
  · intro w hw
    simp only [coe_filter, Fintype.mem_piFinset, mem_Icc, Set.mem_ofPred_eq, mem_range] at hw ⊢
    refine ⟨fun i => by have := hw.1 i; omega, ?_⟩
    rw [sum_sub_distrib]
    have : ((∑ i, w i : ℕ) : ℤ) = (k * n : ℕ) := by rw [hw.2]
    push_cast at this; simp [this]
  · intro v hv
    simp only [coe_filter, Fintype.mem_piFinset, mem_Icc, Set.mem_ofPred_eq] at hv
    ext i; have := hv.1 i; simp; omega
  · intro w _
    ext i; simp

lemma N3 (n : ℕ) : ((Zk n 3).card : ℚ) = 3 * (n : ℚ) ^ 2 + 3 * n + 1 := by
  rw [Zk_shift, cnt_coeff, show PP (2 * n) ^ 3 = PP (2 * n) ^ (2 + 1) from rfl, PP_pow]
  have expand : ((1 - PowerSeries.X ^ (2 * n + 1)) ^ (2 + 1) : PowerSeries ℚ) =
      PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 0 + PowerSeries.C (-3 : ℚ) * PowerSeries.X ^ (2 * n + 1)
      + PowerSeries.C (3 : ℚ) * PowerSeries.X ^ (2 * (2 * n + 1)) + PowerSeries.C (-1 : ℚ) * PowerSeries.X ^ (3 * (2 * n + 1)) := by
    simp only [map_neg, map_one, map_ofNat]; ring
  rw [expand]
  simp only [add_mul, mul_assoc, map_add, cXG]
  rw [if_pos (Nat.zero_le _), if_neg (show ¬ 2 * (2 * n + 1) ≤ 3 * n by omega),
    if_neg (show ¬ 3 * (2 * n + 1) ≤ 3 * n by omega)]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num [Nat.choose]
  · rw [if_pos (show 2 * n + 1 ≤ 3 * n by omega), show 2 + (3 * n - 0) = 3 * n + 2 by omega,
      show 2 + (3 * n - (2 * n + 1)) = n + 1 by omega, Nat.cast_choose_two, Nat.cast_choose_two]
    push_cast; ring

lemma N5 (n : ℕ) : ((Zk n 5).card : ℚ) = (115 * (n : ℚ) ^ 4 + 230 * (n : ℚ) ^ 3 + 185 * (n : ℚ) ^ 2 + 70 * n + 12) / 12 := by
  rw [Zk_shift, cnt_coeff, show PP (2 * n) ^ 5 = PP (2 * n) ^ (4 + 1) from rfl, PP_pow]
  have expand : ((1 - PowerSeries.X ^ (2 * n + 1)) ^ (4 + 1) : PowerSeries ℚ) =
      PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 0 + PowerSeries.C (-5 : ℚ) * PowerSeries.X ^ (2 * n + 1)
      + PowerSeries.C (10 : ℚ) * PowerSeries.X ^ (2 * (2 * n + 1)) + PowerSeries.C (-10 : ℚ) * PowerSeries.X ^ (3 * (2 * n + 1))
      + PowerSeries.C (5 : ℚ) * PowerSeries.X ^ (4 * (2 * n + 1)) + PowerSeries.C (-1 : ℚ) * PowerSeries.X ^ (5 * (2 * n + 1)) := by
    simp only [map_neg, map_one, map_ofNat]; ring
  rw [expand]
  simp only [add_mul, mul_assoc, map_add, cXG]
  rw [if_pos (Nat.zero_le _), if_neg (show ¬ 3 * (2 * n + 1) ≤ 5 * n by omega),
    if_neg (show ¬ 4 * (2 * n + 1) ≤ 5 * n by omega), if_neg (show ¬ 5 * (2 * n + 1) ≤ 5 * n by omega)]
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> norm_num [Nat.choose]
  · rw [if_pos (show 2 * n + 1 ≤ 5 * n by omega), if_pos (show 2 * (2 * n + 1) ≤ 5 * n by omega),
      show 4 + (5 * n - 0) = 5 * n + 4 by omega, show 4 + (5 * n - (2 * n + 1)) = 3 * n + 3 by omega,
      show 4 + (5 * n - 2 * (2 * n + 1)) = n + 2 by omega, choose4, choose4, choose4]
    push_cast; ring

/-! ## Inclusion–exclusion over the five cyclic adjacent pairs -/

/-- arrays in `Zk n 5` whose cyclic adjacent pairs indexed by `t` sum to zero. -/
noncomputable def F (n : ℕ) (t : Finset (Fin 5)) : ℕ :=
  ((Zk n 5).filter (fun v => ∀ i ∈ t, v i + v (i + 1) = 0)).card

lemma F_rot (n : ℕ) (t : Finset (Fin 5)) : F n (t.image (· + 1)) = F n t := by
  unfold F Zk
  apply card_nbij' (fun v : Fin 5 → ℤ => fun j => v (j + 1)) (fun w : Fin 5 → ℤ => fun j => w (j - 1))
  · intro v hv
    simp only [coe_filter, mem_filter, Set.mem_ofPred_eq, forall_mem_image, Fintype.mem_piFinset] at hv ⊢
    refine ⟨⟨fun i => hv.1.1 _, ?_⟩, fun i hi => by simpa using hv.2 hi⟩
    rw [← hv.1.2]; exact Equiv.sum_comp (Equiv.addRight (1 : Fin 5)) v
  · intro w hw
    simp only [coe_filter, mem_filter, Set.mem_ofPred_eq, forall_mem_image, Fintype.mem_piFinset] at hw ⊢
    refine ⟨⟨fun i => hw.1.1 _, ?_⟩, fun i hi => by simpa using hw.2 i hi⟩
    rw [← hw.1.2]; exact Equiv.sum_comp (Equiv.subRight (1 : Fin 5)) w
  · intro v _; ext j; simp
  · intro w _; ext j; simp

def ty (t : Finset (Fin 5)) : ℕ :=
  if t.card = 0 then 0 else if t.card = 1 then 1 else if t.card = 2 then
    (if ∃ i : Fin 5, t = {i, i + 1} then 2 else 3) else if t.card = 3 then 4 else 5

lemma ty_rot : ∀ t : Finset (Fin 5), ty (t.image (· + 1)) = ty t := by decide

def R : Finset (Finset (Fin 5)) := {∅, {0}, {0, 1}, {0, 2}, {0, 1, 2}, {0, 1, 3}, {0, 1, 2, 3}, univ}

lemma cover : ∀ t : Finset (Fin 5), t ∈ R ∨ t.image (· + 1) ∈ R ∨ (t.image (· + 1)).image (· + 1) ∈ R ∨
    ((t.image (· + 1)).image (· + 1)).image (· + 1) ∈ R ∨
    (((t.image (· + 1)).image (· + 1)).image (· + 1)).image (· + 1) ∈ R := by decide

/-- the intersection counts by type. -/
noncomputable def val (n : ℕ) : ℕ → ℕ
  | 0 => (Zk n 5).card
  | 1 => (2 * n + 1) * (Zk n 3).card
  | 2 => (Zk n 3).card
  | 3 => (2 * n + 1) ^ 2
  | 4 => 2 * n + 1
  | _ => 1

lemma cIcc (n : ℕ) : (Icc (-(n : ℤ)) n).card = 2 * n + 1 := by rw [Int.card_Icc]; omega


lemma F0 (n : ℕ) : F n ∅ = (Zk n 5).card := by
  unfold F; rw [filter_true_of_mem]; simp

lemma F1 (n : ℕ) : F n {0} = (2 * n + 1) * (Zk n 3).card := by
  unfold F; rw [← cIcc, ← card_product]
  apply card_nbij' (fun v : Fin 5 → ℤ => (v 0, ![v 2, v 3, v 4])) (fun p : ℤ × (Fin 3 → ℤ) => ![p.1, -p.1, p.2 0, p.2 1, p.2 2])
  · intro v hv; (simp [Zk, Fin.forall_fin_succ, Fin.sum_univ_five, Fin.sum_univ_three] at * <;> omega)
  · intro p hp; (simp [Zk, Fin.forall_fin_succ, Fin.sum_univ_five, Fin.sum_univ_three] at * <;> omega)
  · intro v hv; ext i; fin_cases i <;> simp [Zk, Fin.forall_fin_succ, Fin.sum_univ_five] at hv ⊢ <;> omega
  · intro p _; ext i <;> simp; fin_cases i <;> simp

lemma F01 (n : ℕ) : F n {0, 1} = (Zk n 3).card := by
  unfold F
  apply card_nbij' (fun v : Fin 5 → ℤ => ![v 0, v 3, v 4]) (fun w : Fin 3 → ℤ => ![w 0, -w 0, w 0, w 1, w 2])
  · intro v hv; (simp [Zk, Fin.forall_fin_succ, Fin.sum_univ_five, Fin.sum_univ_three] at * <;> omega)
  · intro p hp; (simp [Zk, Fin.forall_fin_succ, Fin.sum_univ_five, Fin.sum_univ_three] at * <;> omega)
  · intro v hv; ext i; fin_cases i <;> simp [Zk, Fin.forall_fin_succ, Fin.sum_univ_five] at hv ⊢ <;> omega
  · intro p _; ext i; fin_cases i <;> simp

lemma F02 (n : ℕ) : F n {0, 2} = (2 * n + 1) ^ 2 := by
  unfold F; rw [← cIcc, sq, ← card_product]
  apply card_nbij' (fun v : Fin 5 → ℤ => (v 0, v 2)) (fun p : ℤ × ℤ => ![p.1, -p.1, p.2, -p.2, 0])
  · intro v hv; (simp [Zk, Fin.forall_fin_succ, Fin.sum_univ_five, Fin.sum_univ_three] at * <;> omega)
  · intro p hp; simp [Zk, Fin.forall_fin_succ, Fin.sum_univ_five, Prod.le_def] at *; omega
  · intro v hv; ext i; fin_cases i <;> simp [Zk, Fin.forall_fin_succ, Fin.sum_univ_five] at hv ⊢ <;> omega
  · intro p _; simp

lemma F012 (n : ℕ) : F n {0, 1, 2} = 2 * n + 1 := by
  unfold F; rw [← cIcc]
  apply card_nbij' (fun v : Fin 5 → ℤ => v 0) (fun x : ℤ => ![x, -x, x, -x, 0])
  · intro v hv; (simp [Zk, Fin.forall_fin_succ, Fin.sum_univ_five, Fin.sum_univ_three] at * <;> omega)
  · intro p hp; (simp [Zk, Fin.forall_fin_succ, Fin.sum_univ_five, Fin.sum_univ_three] at * <;> omega)
  · intro v hv; ext i; fin_cases i <;> simp [Zk, Fin.forall_fin_succ, Fin.sum_univ_five] at hv ⊢ <;> omega
  · intro p _; simp

lemma F013 (n : ℕ) : F n {0, 1, 3} = 2 * n + 1 := by
  unfold F; rw [← cIcc]
  apply card_nbij' (fun v : Fin 5 → ℤ => v 3) (fun x : ℤ => ![0, 0, 0, x, -x])
  · intro v hv; (simp [Zk, Fin.forall_fin_succ, Fin.sum_univ_five, Fin.sum_univ_three] at * <;> omega)
  · intro p hp; (simp [Zk, Fin.forall_fin_succ, Fin.sum_univ_five, Fin.sum_univ_three] at * <;> omega)
  · intro v hv; ext i; fin_cases i <;> simp [Zk, Fin.forall_fin_succ, Fin.sum_univ_five] at hv ⊢ <;> omega
  · intro p _; simp

lemma F0123 (n : ℕ) : F n {0, 1, 2, 3} = 1 := by
  unfold F; rw [card_eq_one]; refine ⟨0, ?_⟩
  ext v; simp only [mem_filter, mem_singleton]
  constructor
  · intro hv; ext i; simp [Zk] at hv; fin_cases i <;> simp [Zk, Fin.forall_fin_succ, Fin.sum_univ_five] at hv ⊢ <;> omega
  · rintro rfl; simp [Zk]

lemma Funiv (n : ℕ) : F n univ = 1 := by
  unfold F; rw [card_eq_one]; refine ⟨0, ?_⟩
  ext v; simp only [mem_filter, mem_singleton]
  constructor
  · intro hv; ext i; simp [Zk, Fin.forall_fin_succ, Fin.sum_univ_five] at hv; fin_cases i <;> simp [Zk, Fin.forall_fin_succ, Fin.sum_univ_five] at hv ⊢ <;> omega
  · rintro rfl; simp [Zk]

lemma F_rep (n : ℕ) : ∀ t ∈ R, F n t = val n (ty t) := by
  intro t ht
  simp only [R, mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [F0, show ty ∅ = 0 by decide]; rfl
  · rw [F1, show ty {0} = 1 by decide]; rfl
  · rw [F01, show ty {0, 1} = 2 by decide]; rfl
  · rw [F02, show ty {0, 2} = 3 by decide]; rfl
  · rw [F012, show ty {0, 1, 2} = 4 by decide]; rfl
  · rw [F013, show ty {0, 1, 3} = 4 by decide]; rfl
  · rw [F0123, show ty {0, 1, 2, 3} = 5 by decide]; rfl
  · rw [Funiv, show ty univ = 5 by decide]; rfl

lemma F_eq (n : ℕ) (t : Finset (Fin 5)) : F n t = val n (ty t) := by
  rcases cover t with h | h | h | h | h
  · exact F_rep n t h
  · rw [← F_rot, F_rep n _ h, ty_rot]
  · rw [← F_rot, ← F_rot, F_rep n _ h, ty_rot, ty_rot]
  · rw [← F_rot, ← F_rot, ← F_rot, F_rep n _ h, ty_rot, ty_rot, ty_rot]
  · rw [← F_rot, ← F_rot, ← F_rot, ← F_rot, F_rep n _ h, ty_rot, ty_rot, ty_rot, ty_rot]

def c (k : ℕ) : ℤ := ∑ t ∈ (univ : Finset (Fin 5)).powerset.filter (fun t => ty t = k), (-1 : ℤ) ^ t.card

lemma cvals : c 0 = 1 ∧ c 1 = -5 ∧ c 2 = 5 ∧ c 3 = 5 ∧ c 4 = -10 ∧ c 5 = 4 := by decide

lemma ty_lt : ∀ t ∈ (univ : Finset (Fin 5)).powerset, ty t ∈ range 6 := by
  intro t _; simp only [mem_range]; unfold ty; split_ifs <;> omega

lemma cyc (v : Fin 5 → ℤ) (hs : ∑ i, v i = 0) :
    ((∀ i : Fin 4, v i.castSucc + v i.succ ≠ 0) ∧
      ∀ i : Fin 3, v i.castSucc.castSucc + v i.succ.castSucc + v i.succ.succ ≠ 0) ↔
    ∀ i : Fin 5, ¬ (v i + v (i + 1) = 0) := by
  simp only [Fin.forall_fin_succ, IsEmpty.forall_iff, and_true, Fin.sum_univ_five] at hs ⊢
  simp
  omega

lemma card_sub (Z : Finset (Fin 5 → ℤ)) (P : (Fin 5 → ℤ) → Prop) [DecidablePred P] :
    (univ.filter (fun v : Z => P v.1)).card = (Z.filter P).card := by
  apply card_bij (fun v _ => v.1)
  · intro v hv; simp only [mem_filter, mem_univ, true_and] at hv; exact mem_filter.2 ⟨v.2, hv⟩
  · intro v _ w _ h; exact Subtype.ext h
  · intro w hw; rw [mem_filter] at hw; exact ⟨⟨w, hw.1⟩, by simp [hw.2], rfl⟩

lemma inf_filter {α : Type*} [Fintype α] [DecidableEq α] (Q : Fin 5 → α → Prop) [∀ i, DecidablePred (Q i)]
    (t : Finset (Fin 5)) : t.inf (fun i => univ.filter (Q i)) = univ.filter (fun x => ∀ i ∈ t, Q i x) := by
  induction t using Finset.induction_on with
  | empty => ext x; simp
  | insert a t ha ih => rw [inf_insert, ih]; ext x; simp

lemma ie (n : ℕ) : (a n : ℤ) = ∑ k ∈ range 6, c k * val n k := by
  classical
  let Z := Zk n 5
  have h1 : a n = (Z.filter (fun v => ∀ i : Fin 5, ¬ (v i + v (i + 1) = 0))).card := by
    unfold a; simp only [Z, Zk, filter_filter]
    congr 1; apply filter_congr; intro v _
    constructor
    · rintro ⟨hs, h⟩; exact ⟨hs, (cyc v hs).1 h⟩
    · rintro ⟨hs, h⟩; exact ⟨hs, (cyc v hs).2 h⟩
  have h2 := inclusion_exclusion_card_inf_compl (univ : Finset (Fin 5))
    (fun i => univ.filter (fun v : Z => v.1 i + v.1 (i + 1) = 0))
  simp only [compl_filter, inf_filter, mem_univ, true_imp_iff] at h2
  have h0 := card_sub Z (fun w => ∀ i : Fin 5, ¬ (w i + w (i + 1) = 0))
  try simp only at h0
  rw [h1, ← h0, h2]
  have h3 : ∀ t : Finset (Fin 5), ((univ.filter (fun v : Z => ∀ i ∈ t, v.1 i + v.1 (i + 1) = 0)).card : ℤ) =
      val n (ty t) := by
    intro t
    have h4 := card_sub Z (fun w => ∀ i ∈ t, w i + w (i + 1) = 0)
    try simp only at h4
    rw [h4]
    exact_mod_cast F_eq n t
  simp only [h3]
  rw [← sum_fiberwise_of_maps_to ty_lt]
  apply sum_congr rfl; intro k _
  unfold c; rw [sum_mul]
  apply sum_congr rfl; intro t ht; rw [(mem_filter.1 ht).2]

lemma closed (n : ℕ) : (a n : ℚ) = 5 * (n : ℚ) * (n - 1) * (23 * (n : ℚ) ^ 2 - 3 * n + 10) / 12 := by
  have h := ie n
  simp only [sum_range_succ, sum_range_zero, zero_add, cvals, val] at h
  have h' : (a n : ℚ) = 1 * (Zk n 5).card + (-5) * ((2 * n + 1) * (Zk n 3).card) + 5 * (Zk n 3).card +
      5 * (2 * n + 1) ^ 2 + (-10) * (2 * n + 1) + 4 := by exact_mod_cast h
  rw [h', N5, N3]; ring

end OMA.P200432

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a200432.main := by
  ext m
  have hX : ((1 - X) ^ 5 : PowerSeries ℚ) = C (1 : ℚ) * X ^ 0 + C (-5 : ℚ) * X ^ 1 + C (10 : ℚ) * X ^ 2 + C (-10 : ℚ) * X ^ 3 + C (5 : ℚ) * X ^ 4 + C (-1 : ℚ) * X ^ 5 := by
    simp only [map_neg, map_one, map_ofNat]; ring
  rw [hX]
  have hN : (10 * X ^ 2 * (8 + 12 * X + 3 * X ^ 2) : PowerSeries ℚ) = X ^ 2 * C (80 : ℚ) + X ^ 3 * C (120 : ℚ) + X ^ 4 * C (30 : ℚ) := by
    simp only [map_ofNat]; ring
  rw [hN]
  simp only [mul_add, map_add, coeff_mk, mul_left_comm _ (C _), coeff_C_mul, coeff_mul_X_pow', coeff_X_pow,
    coeff_mul_C, Nat.zero_le, if_true, Nat.sub_zero]
  have t0 : (OMA.S_oeis_a200432.a 0 : ℚ) = 0 := by rw [OMA.P200432.closed]; norm_num
  have t1 : (OMA.S_oeis_a200432.a 1 : ℚ) = 0 := by rw [OMA.P200432.closed]; norm_num
  have t2 : (OMA.S_oeis_a200432.a 2 : ℚ) = 80 := by rw [OMA.P200432.closed]; norm_num
  have t3 : (OMA.S_oeis_a200432.a 3 : ℚ) = 520 := by rw [OMA.P200432.closed]; norm_num
  have t4 : (OMA.S_oeis_a200432.a 4 : ℚ) = 1830 := by rw [OMA.P200432.closed]; norm_num
  have t5 : (OMA.S_oeis_a200432.a 5 : ℚ) = 4750 := by rw [OMA.P200432.closed]; norm_num
  rcases Nat.lt_or_ge m 6 with hm | hm
  · interval_cases m <;> norm_num [t0, t1, t2, t3, t4, t5]
  · obtain ⟨p, rfl⟩ : ∃ p, m = p + 6 := ⟨m - 6, by omega⟩
    simp only [if_pos (show 1 ≤ p + 6 by omega), if_pos (show 2 ≤ p + 6 by omega), if_pos (show 3 ≤ p + 6 by omega),
      if_pos (show 4 ≤ p + 6 by omega), if_pos (show 5 ≤ p + 6 by omega)]
    simp only [if_neg (show ¬ (p + 6 = 2) by omega), if_neg (show ¬ (p + 6 = 3) by omega), if_neg (show ¬ (p + 6 = 4) by omega)]
    rw [show p + 6 - 1 = p + 5 by omega, show p + 6 - 2 = p + 4 by omega, show p + 6 - 3 = p + 3 by omega,
      show p + 6 - 4 = p + 2 by omega, show p + 6 - 5 = p + 1 by omega]
    rw [OMA.P200432.closed (p + 6), OMA.P200432.closed (p + 5), OMA.P200432.closed (p + 4), OMA.P200432.closed (p + 3),
      OMA.P200432.closed (p + 2), OMA.P200432.closed (p + 1)]
    push_cast
    ring
