import OMAStatements.S_oeis_a269091
import Mathlib

namespace OMA.S_oeis_a269091
open PowerSeries

def V {S : Type} [Fintype S] (R : S → S → Prop) [DecidableRel R] : ℕ → S → ℕ
  | 0, _ => 1
  | n + 1, s => ∑ t, if R s t then V R n t else 0

section generic
variable {S : Type} [Fintype S] [DecidableEq S] (R : S → S → Prop) [DecidableRel R]

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

theorem rec_w (m : ℕ) (c : ℕ → ℤ) (w : S → ℤ)
    (h0 : ∀ s, ∑ j ∈ Finset.range (m + 1), c j * (V R j s : ℤ) = 0) (n : ℕ) :
    ∑ j ∈ Finset.range (m + 1), c j * (∑ s, w s * (V R (n + j) s : ℤ)) = 0 := by
  have h : ∑ s, w s * ∑ j ∈ Finset.range (m + 1), c j * (V R (n + j) s : ℤ) = 0 :=
    Finset.sum_eq_zero (fun s _ => by rw [rec_gen R m c h0 n s, mul_zero])
  simp only [Finset.mul_sum] at h ⊢
  rw [Finset.sum_comm] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro s _
  ring
end generic

abbrev Row := Fin 2 → Fin 4
def hh (r : Row) : ℕ := if (r 0 : ℕ) + (r 1 : ℕ) = 3 then 1 else 0
def vv (r r' : Row) : ℕ :=
  (if (r 0 : ℕ) + (r' 0 : ℕ) = 3 then 1 else 0) + (if (r 1 : ℕ) + (r' 1 : ℕ) = 3 then 1 else 0)
def cst (r r' : Row) : ℕ := vv r r' + hh r'
def tot {n : ℕ} (x : Fin (n + 1) → Row) : ℕ := ∑ i : Fin n, cst (x i.castSucc) (x i.succ)
abbrev St := Row × Fin 2
def Rel (s t : St) : Prop := (t.2 : ℕ) + cst s.1 t.1 = s.2
instance : DecidableRel Rel := fun s t => by unfold Rel; infer_instance
def T (n : ℕ) (s : St) : ℕ :=
  (Finset.univ.filter (fun x : Fin (n + 1) → Row => x 0 = s.1 ∧ tot x ≤ s.2)).card

theorem tot_succ {n : ℕ} (x : Fin (n + 2) → Row) :
    tot x = cst (x 0) (x 1) + tot (Fin.tail x) := by
  unfold tot
  rw [Fin.sum_univ_succ]
  congr 1

theorem fiber (n : ℕ) (r r' : Row) (b : ℕ) :
    (Finset.univ.filter (fun x : Fin (n + 2) → Row => (x 0 = r ∧ tot x ≤ b) ∧ x 1 = r')).card =
    (Finset.univ.filter (fun x : Fin (n + 1) → Row => x 0 = r' ∧ tot x + cst r r' ≤ b)).card := by
  refine Finset.card_bij' (fun x _ => Fin.tail x) (fun x _ => Fin.cons r x) ?hi ?hj ?li ?ri
  case hi =>
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨⟨h0, h1⟩, h2⟩ := hx
    have := tot_succ x
    refine ⟨by simpa [Fin.tail] using h2, ?_⟩
    rw [h0, h2] at this
    omega
  case hj =>
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨h0, h1⟩ := hx
    have := tot_succ (Fin.cons r x : Fin (n + 2) → Row)
    simp only [Fin.cons_zero, Fin.tail_cons] at this
    have h2 : (Fin.cons r x : Fin (n + 2) → Row) 1 = r' := by
      have : (1 : Fin (n + 2)) = Fin.succ 0 := rfl
      rw [this, Fin.cons_succ]; exact h0
    refine ⟨⟨rfl, ?_⟩, h2⟩
    rw [h2] at this
    omega
  case li =>
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨⟨h0, h1⟩, h2⟩ := hx
    rw [← h0]
    exact Fin.cons_self_tail x
  case ri =>
    intro x hx
    exact Fin.tail_cons _ _

theorem T_eq (n : ℕ) (s : St) : T n s = V Rel n s := by
  induction n generalizing s with
  | zero =>
    simp only [V, T]
    rw [Finset.card_eq_one]
    refine ⟨fun _ => s.1, ?_⟩
    apply Finset.ext
    intro x
    rw [Finset.mem_filter, Finset.mem_singleton]
    have ht : tot x = 0 := by simp [tot]
    constructor
    · rintro ⟨_, h, _⟩
      funext i
      have : i = 0 := Fin.ext (by have := i.2; simp only [Fin.val_zero]; omega)
      subst this; exact h
    · rintro rfl
      exact ⟨Finset.mem_univ _, rfl, by omega⟩
  | succ n ih =>
    obtain ⟨r, b⟩ := s
    simp only [V]
    rw [Fintype.sum_prod_type]
    simp only [← ih]
    unfold T
    rw [Finset.card_eq_sum_card_fiberwise (f := fun x : Fin (n + 2) → Row => x 1) (t := Finset.univ)
      (by simp)]
    apply Finset.sum_congr rfl
    intro r' _
    rw [Finset.filter_filter]
    have := fiber n r r' (b : ℕ)
    rw [this]
    have hsum : ∀ (c : ℕ) (b : Fin 2) (f : Fin 2 → ℕ),
        (∑ b' : Fin 2, if (b' : ℕ) + c = (b : ℕ) then f b' else 0) =
          if c ≤ (b : ℕ) then f ⟨(b : ℕ) - c, by omega⟩ else 0 := by
      intro c b f
      rw [Fin.sum_univ_two]
      rcases b with ⟨_ | _ | b, hb⟩ <;> rcases c with _ | _ | c <;> simp <;> omega
    have hrel : ∀ b' : Fin 2, Rel (r, b) (r', b') ↔ (b' : ℕ) + cst r r' = (b : ℕ) := fun b' => Iff.rfl
    simp only [hrel]
    rw [hsum]
    by_cases hc : cst r r' ≤ (b : ℕ)
    · rw [if_pos hc]
      congr 1
      apply Finset.filter_congr
      intro x _
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by simp only at *; omega⟩
    · rw [if_neg hc, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _ hx
      omega

theorem pairs_eq (m : ℕ) (x : Fin (m + 1) → Row) : pairsTotallingThree m x = hh (x 0) + tot x := by
  unfold pairsTotallingThree tot cst vv hh
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Finset.sum_add_distrib]
  ring

theorem cnt (m : ℕ) (B : Fin 2) :
    (Finset.univ.filter (fun x : Fin (m + 1) → Row => hh (x 0) + tot x ≤ (B : ℕ))).card =
    ∑ s : St, if (s.2 : ℕ) + hh s.1 = (B : ℕ) then T m s else 0 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x : Fin (m + 1) → Row => x 0) (t := Finset.univ)
    (by simp)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.filter_filter]
  have hsum : ∀ (c : ℕ) (b : Fin 2) (f : Fin 2 → ℕ),
      (∑ b' : Fin 2, if (b' : ℕ) + c = (b : ℕ) then f b' else 0) =
        if c ≤ (b : ℕ) then f ⟨(b : ℕ) - c, by omega⟩ else 0 := by
    intro c b f
    rw [Fin.sum_univ_two]
    rcases b with ⟨_ | _ | b, hb⟩ <;> rcases c with _ | _ | c <;> simp <;> omega
  dsimp only
  rw [hsum]
  by_cases hc : hh r ≤ (B : ℕ)
  · rw [if_pos hc]
    unfold T
    congr 1
    apply Finset.filter_congr
    intro x _
    constructor
    · rintro ⟨h2, h1⟩
      subst h1
      refine ⟨rfl, ?_⟩
      dsimp only at *
      omega
    · rintro ⟨h1, h2⟩
      subst h1
      refine ⟨?_, rfl⟩
      dsimp only at *
      omega
  · rw [if_neg hc, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x _ ⟨h2, h1⟩
    subst h1
    omega

def w (s : St) : ℤ :=
  (if (s.2 : ℕ) + hh s.1 = 1 then 1 else 0) - (if (s.2 : ℕ) + hh s.1 = 0 then 1 else 0)

theorem a_eq (m : ℕ) : (a (m + 1) : ℤ) = ∑ s : St, w s * (V Rel m s : ℤ) := by
  have h1 : (Finset.univ.filter (fun x : Fin (m + 1) → Row => pairsTotallingThree m x = 1)) =
      SDiff.sdiff (Finset.univ.filter (fun x : Fin (m + 1) → Row => hh (x 0) + tot x ≤ ((1 : Fin 2) : ℕ)))
      (Finset.univ.filter (fun x : Fin (m + 1) → Row => hh (x 0) + tot x ≤ ((0 : Fin 2) : ℕ))) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, pairs_eq]
    simp only [Fin.val_zero, Fin.val_one]
    omega
  have h2 : (Finset.univ.filter (fun x : Fin (m + 1) → Row => hh (x 0) + tot x ≤ ((0 : Fin 2) : ℕ))) ⊆
      (Finset.univ.filter (fun x : Fin (m + 1) → Row => hh (x 0) + tot x ≤ ((1 : Fin 2) : ℕ))) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_zero, Fin.val_one] at hx ⊢
    omega
  have h3 : a (m + 1) = (Finset.univ.filter (fun x : Fin (m + 1) → Row => hh (x 0) + tot x ≤ ((1 : Fin 2) : ℕ))).card -
      (Finset.univ.filter (fun x : Fin (m + 1) → Row => hh (x 0) + tot x ≤ ((0 : Fin 2) : ℕ))).card := by
    rw [← Finset.card_sdiff_of_subset h2, ← h1]
    simp only [a, pairs_eq]
  have h4 := Finset.card_le_card h2
  rw [h3, Nat.cast_sub h4, cnt, cnt]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [← T_eq]
  unfold w
  simp only [Fin.val_zero, Fin.val_one]
  split_ifs <;> omega

def A (m : ℕ) : ℤ := ∑ s : St, w s * (V Rel m s : ℤ)

theorem a_eq' (m : ℕ) : (a (m + 1) : ℤ) = A m := a_eq m

def cc : ℕ → ℤ := fun j => [(0 : ℤ), 0, 49, -14, 1].getD j 0

theorem hrecA (k : ℕ) : A (k + 4) = 14 * A (k + 3) - 49 * A (k + 2) := by
  have h := rec_w Rel 4 cc w (by decide +kernel) k
  have e0 : cc 0 = 0 := rfl
  have e1 : cc 1 = 0 := rfl
  have e2 : cc 2 = 49 := rfl
  have e3 : cc 3 = -14 := rfl
  have e4 : cc 4 = 1 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, e4, zero_mul, zero_add] at h
  unfold A
  linarith

theorem vA0 : A 0 = 4 := by unfold A; decide +kernel
theorem vA1 : A 1 = 96 := by unfold A; decide +kernel
theorem vA2 : A 2 = 1152 := by unfold A; decide +kernel
theorem vA3 : A 3 = 11424 := by unfold A; decide +kernel

theorem closedA (j : ℕ) : (A (j + 1) : ℚ) = ((96 : ℚ) + (480 / 7 : ℚ) * (j : ℚ)) * (7 : ℚ) ^ j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases h : j ≤ 2
    · interval_cases j
      · rw [vA1]; norm_num
      · rw [vA2]; norm_num
      · rw [vA3]; norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 3 := ⟨j - 3, by omega⟩
      have r : (A (k + 3 + 1) : ℚ) = 14 * A (k + 3) - 49 * A (k + 2) := by
        exact_mod_cast hrecA k
      have i1 := ih (k + 2) (by omega)
      have i2 := ih (k + 1) (by omega)
      rw [r, i1, i2]
      push_cast
      ring

theorem closed (j : ℕ) : (a (j + 2) : ℚ) = ((96 : ℚ) + (480 / 7 : ℚ) * (j : ℚ)) * (7 : ℚ) ^ j := by
  have h : (a (j + 1 + 1) : ℚ) = A (j + 1) := by exact_mod_cast a_eq' (j + 1)
  rw [h]
  exact closedA j

theorem gfgen (ρ n1 n2 n3 : ℚ) (b : ℕ → ℚ) (h0 : b 0 = 0) (h1 : b 1 = n1)
    (h2 : b 2 - 2 * ρ * b 1 = n2) (h3 : b 3 - 2 * ρ * b 2 + ρ ^ 2 * b 1 = n3)
    (h4 : ∀ n, b (n + 4) - 2 * ρ * b (n + 3) + ρ ^ 2 * b (n + 2) = 0) :
    PowerSeries.mk b * (1 - C ρ * X) ^ 2 = C n1 * X + C n2 * X ^ 2 + C n3 * X ^ 3 := by
  have e : PowerSeries.mk b * (1 - C ρ * X) ^ 2 = PowerSeries.mk b - C (2 * ρ) * (X * PowerSeries.mk b) +
      C (ρ ^ 2) * (X * (X * PowerSeries.mk b)) := by
    rw [map_mul, map_pow, map_ofNat]; ring
  rw [e]
  have h2' : b 2 - 2 * ρ * b 1 = n2 := h2
  generalize 2 * ρ = c1 at h2' h3 h4 ⊢
  generalize ρ ^ 2 = c2 at h3 h4 ⊢
  ext n
  rcases n with _ | _ | _ | _ | n
  · simp [h0]
  · simp [h1, h0]
  · simp [coeff_X_pow, coeff_X]
    linarith [h0, h1, show c2 * b 0 = 0 by rw [h0]; ring]
  · simp [coeff_X_pow, coeff_X]
    linarith [h0, h1, show c2 * b 0 = 0 by rw [h0]; ring]
  · simp [coeff_X_pow, coeff_X]
    linarith [h4 n, h0, h1, show c2 * b 0 = 0 by rw [h0]; ring]


theorem hrecQ (j : ℕ) :
    (a (j + 4) : ℚ) = 14 * (a (j + 3) : ℚ) - 49 * (a (j + 2) : ℚ) := by
  have c4 : (a (j + 4) : ℚ) = ((96 : ℚ) + (480 / 7 : ℚ) * ((j + 2 : ℕ) : ℚ)) * (7 : ℚ) ^ (j + 2) := closed (j + 2)
  have c3 : (a (j + 3) : ℚ) = ((96 : ℚ) + (480 / 7 : ℚ) * ((j + 1 : ℕ) : ℚ)) * (7 : ℚ) ^ (j + 1) := closed (j + 1)
  have c2 : (a (j + 2) : ℚ) = ((96 : ℚ) + (480 / 7 : ℚ) * (j : ℚ)) * (7 : ℚ) ^ j := closed j
  rw [c4, c3, c2]
  push_cast
  ring

theorem ha1 : (a 1 : ℚ) = 4 := by
  have := a_eq' 0
  rw [vA0] at this
  have h : (a 1 : ℤ) = 4 := by simpa using this
  exact_mod_cast h

theorem ha2 : (a 2 : ℚ) = 96 := by
  have := a_eq' 1
  rw [vA1] at this
  have h : (a 2 : ℤ) = 96 := by simpa using this
  exact_mod_cast h

theorem ha3 : (a 3 : ℚ) = 1152 := by
  have := a_eq' 2
  rw [vA2] at this
  have h : (a 3 : ℤ) = 1152 := by simpa using this
  exact_mod_cast h

end OMA.S_oeis_a269091

open OMA.S_oeis_a269091 in
theorem OMA.solution : type_of% @OMA.S_oeis_a269091.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
    have e1 : j + 4 - 1 = j + 3 := by omega
    have e2 : j + 4 - 2 = j + 2 := by omega
    rw [e1, e2]
    have := hrecQ j
    exact_mod_cast this
  · have key := gfgen (7 : ℚ) (4 : ℚ) (40 : ℚ) (4 : ℚ) (fun n => (a n : ℚ))
      (by simp [a]) (by simpa using ha1) (by rw [ha2, ha1]; norm_num)
      (by rw [ha3, ha2, ha1]; norm_num) (fun n => by rw [hrecQ n]; ring)
    simp only [map_ofNat] at key
    rw [key]
    ring
  · intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
    rw [closed j]
    push_cast
    simp only [zpow_sub₀ (by norm_num : (7:ℚ) ≠ 0), zpow_add₀ (by norm_num : (7:ℚ) ≠ 0), zpow_natCast, zpow_ofNat]
    field_simp
    ring

