import OMAStatements.S_oeis_a211476
import Mathlib

namespace OMA.S_oeis_a211476

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

def M1 : Fin 3 → Fin 3 → Prop := fun a b =>
  (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 1 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)
def M2 : Fin 3 → Fin 3 → Prop := fun a b =>
  (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 0) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 0) ∨ (a = 2 ∧ b = 1)
def M12 : Fin 3 → Fin 3 → Prop := fun a b => M1 a b ∧ M2 a b

instance : DecidableRel M1 := fun a b => by unfold M1; infer_instance
instance : DecidableRel M2 := fun a b => by unfold M2; infer_instance
instance : DecidableRel M12 := fun a b => by unfold M12; infer_instance

def Gd (n : ℕ) (x : Fin (n + 1) → Fin 3) : Prop := ∀ i j : Fin n,
    nd (v x i.castSucc) (v x i.succ) (v x j.castSucc) (v x j.succ) ∈ ({1, 3} : Finset ℕ)

lemma okM (R : Fin 3 → Fin 3 → Prop) (hR : R = M1 ∨ R = M2) :
    ∀ a b c d : Fin 3, R a b → R c d →
      nd (((a : ℕ) : ℤ) - 1) (((b : ℕ) : ℤ) - 1) (((c : ℕ) : ℤ) - 1) (((d : ℕ) : ℤ) - 1) ∈ ({1, 3} : Finset ℕ) := by
  rcases hR with rfl | rfl
  · unfold M1 nd; decide +kernel
  · unfold M2 nd; decide +kernel

lemma badM : ∀ a b c d : Fin 3, (M2 a b ∧ ¬ M1 a b) → (M1 c d ∧ ¬ M2 c d) →
      nd (((a : ℕ) : ℤ) - 1) (((b : ℕ) : ℤ) - 1) (((c : ℕ) : ℤ) - 1) (((d : ℕ) : ℤ) - 1) ∉ ({1, 3} : Finset ℕ) := by
  decide +kernel

lemma singM : ∀ a b : Fin 3,
      nd (((a : ℕ) : ℤ) - 1) (((b : ℕ) : ℤ) - 1) (((a : ℕ) : ℤ) - 1) (((b : ℕ) : ℤ) - 1) ∈ ({1, 3} : Finset ℕ) →
      M1 a b ∨ M2 a b := by
  decide +kernel

lemma gd_iff (n : ℕ) (x : Fin (n + 1) → Fin 3) :
    Gd n x ↔ (∀ i : Fin n, M1 (x i.castSucc) (x i.succ)) ∨ (∀ i : Fin n, M2 (x i.castSucc) (x i.succ)) := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hc
    have hi2 : M2 (x i.castSucc) (x i.succ) := by
      rcases singM _ _ (h i i) with h1 | h1
      · exact absurd h1 hi
      · exact h1
    have hj1 : M1 (x j.castSucc) (x j.succ) := by
      rcases singM _ _ (h j j) with h1 | h1
      · exact h1
      · exact absurd h1 hj
    exact badM _ _ _ _ ⟨hi2, hi⟩ ⟨hj1, hj⟩ (h i j)
  · rintro (h | h) i j
    · exact okM M1 (Or.inl rfl) _ _ _ _ (h i) (h j)
    · exact okM M2 (Or.inr rfl) _ _ _ _ (h i) (h j)

lemma chain_card (R : Fin 3 → Fin 3 → Prop) [DecidableRel R] (n : ℕ) :
    Fintype.card (Chain R n) =
      ((Finset.univ : Finset (Fin (n + 1) → Fin 3)).filter
        (fun x => ∀ i : Fin n, R (x i.castSucc) (x i.succ))).card := by
  unfold Chain
  convert Fintype.card_subtype (α := Fin (n + 1) → Fin 3) (fun x => ∀ i : Fin n, R (x i.castSucc) (x i.succ)) using 1

theorem a_eq (n : ℕ) : (a n : ℤ) + (∑ s, V M12 n s : ℕ) = (∑ s, V M1 n s : ℕ) + (∑ s, V M2 n s : ℕ) := by
  rw [← cardChain, ← cardChain, ← cardChain, chain_card, chain_card, chain_card]
  have h1 : a n = ((Finset.univ : Finset (Fin (n + 1) → Fin 3)).filter
      (fun x => (∀ i : Fin n, M1 (x i.castSucc) (x i.succ)) ∨ (∀ i : Fin n, M2 (x i.castSucc) (x i.succ)))).card := by
    unfold a
    congr 1
    apply Finset.filter_congr
    intro x _
    exact gd_iff n x
  have h2 := Finset.card_union_add_card_inter
    ((Finset.univ : Finset (Fin (n + 1) → Fin 3)).filter (fun x => ∀ i : Fin n, M1 (x i.castSucc) (x i.succ)))
    ((Finset.univ : Finset (Fin (n + 1) → Fin 3)).filter (fun x => ∀ i : Fin n, M2 (x i.castSucc) (x i.succ)))
  rw [← Finset.filter_or, ← Finset.filter_and] at h2
  have h3 : ((Finset.univ : Finset (Fin (n + 1) → Fin 3)).filter
      (fun x => (∀ i : Fin n, M1 (x i.castSucc) (x i.succ)) ∧ (∀ i : Fin n, M2 (x i.castSucc) (x i.succ)))) =
      (Finset.univ : Finset (Fin (n + 1) → Fin 3)).filter (fun x => ∀ i : Fin n, M12 (x i.castSucc) (x i.succ)) := by
    apply Finset.filter_congr
    intro x _
    constructor
    · rintro ⟨ha, hb⟩ i; exact ⟨ha i, hb i⟩
    · intro h; exact ⟨fun i => (h i).1, fun i => (h i).2⟩
  rw [h3] at h2
  rw [h1]
  exact_mod_cast h2

def cc : ℕ → ℤ := fun j => [(4 : ℤ), 2, -4, -1, 1].getD j 0

theorem hrec1 (n : ℕ) : ∑ j ∈ Finset.range 5, cc j * (∑ s, (V M1 (n + j) s : ℤ)) = 0 :=
  rec_total M1 4 cc (by decide +kernel) n
theorem hrec2 (n : ℕ) : ∑ j ∈ Finset.range 5, cc j * (∑ s, (V M2 (n + j) s : ℤ)) = 0 :=
  rec_total M2 4 cc (by decide +kernel) n
theorem hrec12 (n : ℕ) : ∑ j ∈ Finset.range 5, cc j * (∑ s, (V M12 (n + j) s : ℤ)) = 0 :=
  rec_total M12 4 cc (by decide +kernel) n

theorem hrec (n : ℕ) : (a (n + 4) : ℤ) = a (n + 3) + 4 * a (n + 2) - 2 * a (n + 1) - 4 * a n := by
  have h1 := hrec1 n
  have h2 := hrec2 n
  have h3 := hrec12 n
  have e0 : cc 0 = 4 := rfl
  have e1 : cc 1 = 2 := rfl
  have e2 : cc 2 = -4 := rfl
  have e3 : cc 3 = -1 := rfl
  have e4 : cc 4 = 1 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, e4, Nat.add_zero, zero_add] at h1 h2 h3
  have q0 := a_eq n
  have q1 := a_eq (n + 1)
  have q2 := a_eq (n + 2)
  have q3 := a_eq (n + 3)
  have q4 := a_eq (n + 4)
  push_cast at q0 q1 q2 q3 q4
  linarith

def Vt (n : ℕ) : ℕ := (∑ s, V M1 n s) + (∑ s, V M2 n s) - (∑ s, V M12 n s)

theorem a_Vt (n : ℕ) : a n = Vt n := by
  have h := a_eq n
  unfold Vt
  omega

theorem a_vals : a 0 = 3 ∧ a 1 = 7 ∧ a 2 = 17 ∧ a 3 = 37 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [a_Vt]; decide +kernel
  · rw [a_Vt]; decide +kernel
  · rw [a_Vt]; decide +kernel
  · rw [a_Vt]; decide +kernel

theorem a4 : a 4 = 79 := by
  obtain ⟨v0, v1, v2, v3⟩ := a_vals
  have h := hrec 0
  simp only [zero_add, v0, v1, v2, v3] at h
  exact_mod_cast (by simpa using h : (a 4 : ℤ) = 79)

theorem closed (m : ℕ) :
    (a (2 * m) : ℚ) = (-9 * 2 ^ m + 17 * (2 ^ m) ^ 2 + 1) / 3 ∧
    (a (2 * m + 1) : ℚ) = (34 * (2 ^ m) ^ 2 - 12 * 2 ^ m - 1) / 3 ∧
    (a (2 * m + 2) : ℚ) = (-9 * (2 * 2 ^ m) + 17 * (2 * 2 ^ m) ^ 2 + 1) / 3 ∧
    (a (2 * m + 3) : ℚ) = (34 * (2 * 2 ^ m) ^ 2 - 12 * (2 * 2 ^ m) - 1) / 3 := by
  induction m with
  | zero =>
    obtain ⟨v0, v1, v2, v3⟩ := a_vals
    simp only [mul_zero, zero_add, pow_zero, v0, v1, v2, v3]
    norm_num
  | succ m ih =>
    obtain ⟨h0, h1, h2, h3⟩ := ih
    have r0 : (a (2 * m + 4) : ℚ) = a (2 * m + 3) + 4 * a (2 * m + 2) - 2 * a (2 * m + 1) - 4 * a (2 * m) := by
      exact_mod_cast hrec (2 * m)
    have r1 : (a (2 * m + 5) : ℚ) = a (2 * m + 4) + 4 * a (2 * m + 3) - 2 * a (2 * m + 2) - 4 * a (2 * m + 1) := by
      exact_mod_cast hrec (2 * m + 1)
    have e2 : 2 * (m + 1) = 2 * m + 2 := by ring
    have e3 : 2 * (m + 1) + 1 = 2 * m + 3 := by ring
    have e4 : 2 * (m + 1) + 2 = 2 * m + 4 := by ring
    have e5 : 2 * (m + 1) + 3 = 2 * m + 5 := by ring
    have p1 : (2 : ℚ) ^ (m + 1) = 2 * 2 ^ m := by ring
    rw [e2, show 2 * m + 2 + 1 = 2 * m + 3 from rfl, show 2 * m + 2 + 2 = 2 * m + 4 from rfl,
      show 2 * m + 2 + 3 = 2 * m + 5 from rfl, p1]
    refine ⟨h2, h3, ?_, ?_⟩
    · rw [r0, h3, h2, h1, h0]; ring
    · rw [r1, r0, h3, h2, h1, h0]; ring

theorem gf_part :
    PowerSeries.X * PowerSeries.mk (fun n => (a (n + 1) : ℚ)) *
        ((1 + PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2)) =
      PowerSeries.X * (7 + 10 * PowerSeries.X - 8 * PowerSeries.X ^ 2 -
        12 * PowerSeries.X ^ 3) := by
  obtain ⟨v0, v1, v2, v3⟩ := a_vals
  have v4 := a4
  set f : PowerSeries ℚ := PowerSeries.mk (fun n => (a (n + 1) : ℚ)) with hf
  have hP : f * ((1 + PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2)) =
      f - PowerSeries.X * f - PowerSeries.C (4:ℚ) * (PowerSeries.X * (PowerSeries.X * f)) +
        PowerSeries.C (2:ℚ) * (PowerSeries.X * (PowerSeries.X * (PowerSeries.X * f))) +
        PowerSeries.C (4:ℚ) * (PowerSeries.X * (PowerSeries.X * (PowerSeries.X * (PowerSeries.X * f)))) := by
    rw [show PowerSeries.C (4:ℚ) = 4 from map_ofNat _ 4, show PowerSeries.C (2:ℚ) = 2 from map_ofNat _ 2]
    ring
  have hR : (7 + 10 * PowerSeries.X - 8 * PowerSeries.X ^ 2 - 12 * PowerSeries.X ^ 3 : PowerSeries ℚ) =
      PowerSeries.C (7:ℚ) + PowerSeries.C (10:ℚ) * PowerSeries.X - PowerSeries.C (8:ℚ) * PowerSeries.X ^ 2 -
        PowerSeries.C (12:ℚ) * PowerSeries.X ^ 3 := by
    rw [show PowerSeries.C (7:ℚ) = 7 from map_ofNat _ 7, show PowerSeries.C (10:ℚ) = 10 from map_ofNat _ 10,
      show PowerSeries.C (8:ℚ) = 8 from map_ofNat _ 8, show PowerSeries.C (12:ℚ) = 12 from map_ofNat _ 12]
  have key : f * ((1 + PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2)) =
      (7 + 10 * PowerSeries.X - 8 * PowerSeries.X ^ 2 - 12 * PowerSeries.X ^ 3 : PowerSeries ℚ) := by
    rw [hP, hR]
    ext n
    rcases n with _ | _ | _ | _ | n
    · simp [hf, v1]
    · simp [hf, v1, v2, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
      norm_num
    · simp [hf, v1, v2, v3, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      norm_num
    · simp [hf, v1, v2, v3, v4, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      norm_num
    · have h' : (a (n + 1 + 1 + 1 + 1 + 1) : ℚ) = a (n + 3 + 1) + 4 * (a (n + 2 + 1) : ℚ) - 2 * (a (n + 1 + 1) : ℚ) - 4 * (a (n + 1) : ℚ) := by
        exact_mod_cast hrec (n + 1)
      simp only [map_add, map_sub, hf, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
      simp [PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
      linarith [h']
  rw [mul_assoc, key]

end OMA.S_oeis_a211476

theorem OMA.solution : type_of% @OMA.S_oeis_a211476.main := by
  refine ⟨OMA.S_oeis_a211476.gf_part, ?_, ?_⟩
  · intro n hn he
    obtain ⟨m, rfl⟩ := he
    have h := (OMA.S_oeis_a211476.closed m).1
    have e : m + m = 2 * m := by ring
    rw [e, h, show 2 * m / 2 = m by omega, pow_mul']
    try ring
  · intro n hn ho
    obtain ⟨m, rfl⟩ := ho
    have h := (OMA.S_oeis_a211476.closed m).2.1
    have q1 : (2 : ℚ) ^ (2 * m + 1) = 2 * (2 ^ m) ^ 2 := by ring
    have q2 : (2 : ℚ) ^ (m + 2) = 4 * 2 ^ m := by ring
    rw [h, show (2 * m + 1 + 3) / 2 = m + 2 by omega, q1, q2]
    ring
