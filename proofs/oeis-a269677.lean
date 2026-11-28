import OMAStatements.S_oeis_a269677

namespace A269677P
open OMA.S_oeis_a269677

def st (l : List (Fin 8)) : Option (Fin 8) := (repeats l).head?

theorem chain_cons {R : Fin 8 → Fin 8 → Prop} (a : Fin 8) (L : List (Fin 8)) :
    List.IsChain R (a :: L) ↔ (∀ y ∈ L.head?, R a y) ∧ List.IsChain R L := by
  cases L <;> simp

theorem valid_cc (c b : Fin 8) (t : List (Fin 8)) :
    Valid (c :: b :: t) ↔ (c = b → ∀ y ∈ st (b :: t), Adjacent c y) ∧ Valid (b :: t) := by
  unfold Valid st
  by_cases h : c = b
  · subst h; simp only [repeats, if_true]; rw [chain_cons]; simp
  · simp [repeats, h]

theorem st_cc (c b : Fin 8) (t : List (Fin 8)) :
    st (c :: b :: t) = if c = b then some c else st (b :: t) := by
  unfold st; by_cases h : c = b <;> simp [repeats, h]

theorem sum_cons {n : ℕ} (F : List (Fin 8) → ℕ) :
    ∑ f : Fin (n + 1) → Fin 8, F (List.ofFn f) =
      ∑ x, ∑ g : Fin n → Fin 8, F (x :: List.ofFn g) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 8) _ _ (fun p => by
    simp [Fin.consEquiv, List.ofFn_succ])).symm

def cnt (n : ℕ) (c : Fin 8) (r : Option (Fin 8)) : ℕ :=
  ∑ g : Fin n → Fin 8, if Valid (c :: List.ofFn g) ∧ st (c :: List.ofFn g) = r then 1 else 0

def Tp (c b : Fin 8) (r' r : Option (Fin 8)) : Prop :=
  (c = b → ∀ y, r' = some y → Adjacent c y) ∧ (if c = b then some c else r') = r

instance (c b : Fin 8) (r' r : Option (Fin 8)) : Decidable (Tp c b r' r) := by
  unfold Tp; infer_instance

theorem cnt_succ (n : ℕ) (c : Fin 8) (r : Option (Fin 8)) :
    cnt (n + 1) c r = ∑ b, ∑ r', (if Tp c b r' r then 1 else 0) * cnt n b r' := by
  unfold cnt
  rw [sum_cons (F := fun l => if Valid (c :: l) ∧ st (c :: l) = r then 1 else 0)]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  have key : (Valid (c :: b :: List.ofFn g) ∧ st (c :: b :: List.ofFn g) = r) ↔
      Tp c b (st (b :: List.ofFn g)) r ∧ Valid (b :: List.ofFn g) := by
    rw [valid_cc, st_cc]; unfold Tp
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨fun h y hy => h1 h y (by simp [hy]), h3⟩, h2⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨⟨fun h y hy => h1 h y (by simpa using hy), h2⟩, h3⟩
  simp only [key]
  by_cases hv : Valid (b :: List.ofFn g) <;> simp [hv]

def cls (c : Fin 8) : Option (Fin 8) → Fin 4
  | none => 0
  | some r => if r = c then 1 else if Adjacent c r then 2 else 3

def Cm : Fin 4 → Fin 4 → ℕ := ![![7, 0, 0, 0], ![1, 0, 4, 5], ![0, 1, 1, 5], ![0, 1, 2, 4]]

theorem coef : ∀ c r j, (∑ b, ∑ r', (if Tp c b r' r then 1 else 0) *
    (if cls b r' = j then 1 else 0)) = Cm (cls c r) j := by
  decide +kernel

def V : ℕ → Fin 4 → ℕ
  | 0 => ![1, 0, 0, 0]
  | n + 1 => fun k => ∑ j, Cm k j * V n j

theorem cnt_eq (n : ℕ) : ∀ c r, cnt n c r = V n (cls c r) := by
  induction n with
  | zero =>
    intro c r
    have h : ∀ g : Fin 0 → Fin 8, List.ofFn g = [] := fun g => by simp
    simp only [cnt, h]
    cases r with
    | none => simp [Valid, repeats, st, cls, V]
    | some r => simp [Valid, repeats, st, cls, V]; split_ifs <;> rfl
  | succ n ih =>
    intro c r
    rw [cnt_succ]
    simp only [ih]
    have e : ∀ b r', V n (cls b r') = ∑ j, (if cls b r' = j then 1 else 0) * V n j := by
      intro b r'; simp
    simp only [e, Finset.mul_sum]
    rw [show V (n + 1) (cls c r) = ∑ j, Cm (cls c r) j * V n j from rfl]
    simp only [← coef c r, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r' _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring

theorem tot : ∀ j, (∑ c : Fin 8, ∑ r : Option (Fin 8), (if cls c r = j then 1 else 0)) =
    ![8, 8, 16, 40] j := by
  decide +kernel

theorem a_succ (n : ℕ) : a (n + 1) = ∑ j, ![8, 8, 16, 40] j * V n j := by
  have h1 : a (n + 1) = ∑ c, ∑ r, cnt n c r := by
    unfold a
    rw [Finset.card_filter, sum_cons (F := fun l => if Valid l then 1 else 0)]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    unfold cnt
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    by_cases hv : Valid (c :: List.ofFn g) <;> simp [hv]
  rw [h1]
  simp only [cnt_eq]
  have e : ∀ b r', V n (cls b r') = ∑ j, (if cls b r' = j then 1 else 0) * V n j := by
    intro b r'; simp
  simp only [e, ← tot, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  conv_rhs => rw [Finset.sum_comm]

theorem rec3 (n : ℕ) : (a (n + 4) : ℤ) = 13 * a (n + 3) - 33 * a (n + 2) - 63 * a (n + 1) := by
  simp only [a_succ, V, Fin.sum_univ_four, Cm]
  simp
  ring

theorem a1 : a 1 = 8 := by simp [a_succ, V, Fin.sum_univ_four]
theorem a2 : a 2 = 64 := by simp [a_succ, V, Fin.sum_univ_four, Cm]
theorem a3 : a 3 = 504 := by simp [a_succ, V, Fin.sum_univ_four, Cm]

end A269677P

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a269677.main := by
  open OMA.S_oeis_a269677 A269677P in
  refine ⟨?_, ?_⟩
  · rw [show ((1 - 7 * X) * (1 - 6 * X - 9 * X ^ 2) : PowerSeries ℤ)
        = 1 - C 13 * X ^ 1 + C 33 * X ^ 2 + C 63 * X ^ 3 by simp only [map_ofNat]; ring,
      show (8 * X * (1 - 5 * X - 8 * X ^ 2) : PowerSeries ℤ)
        = X * (C 8 - C 40 * X ^ 1 - C 64 * X ^ 2) by simp only [map_ofNat]; ring,
      show ∀ p : PowerSeries ℤ, (1 - C 13 * X ^ 1 + C 33 * X ^ 2 + C 63 * X ^ 3) * (X * p)
        = X * (p - C 13 * (p * X ^ 1) + C 33 * (p * X ^ 2) + C 63 * (p * X ^ 3)) from
        fun p => by ring]
    congr 1
    ext n
    simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_C]
    rcases n with _ | _ | _ | n
    · simp [a1]
    · simp [a1, a2]
    · simp [a1, a2, a3]
    · have := rec3 n
      simp only [show n + 1 + 1 + 1 = n + 3 by ring]
      simp
      rw [this]
      ring
  · set s := Real.sqrt 2 with hsdef
    have hs : s ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    let b : ℕ → ℝ := fun n => (-216 * 7 ^ n + (140 - 98 * s) * (3 - 3 * s) ^ n +
        14 * (3 * (1 + s)) ^ n * (10 + 7 * s)) / 63
    have hx : (3 - 3 * s) ^ 2 = 6 * (3 - 3 * s) + 9 := by linear_combination 9 * hs
    have hy : (3 * (1 + s)) ^ 2 = 6 * (3 * (1 + s)) + 9 := by linear_combination 9 * hs
    have hb : ∀ n, b (n + 3) = 13 * b (n + 2) - 33 * b (n + 1) - 63 * b n := by
      intro n
      simp only [b]
      linear_combination ((140 - 98 * s) / 63) * ((3 - 3 * s) ^ n * (3 - 3 * s - 7)) * hx +
        (14 * (10 + 7 * s) / 63) * ((3 * (1 + s)) ^ n * (3 * (1 + s) - 7)) * hy
    have b1 : b 1 = 8 := by simp only [b]; linear_combination (28 / 3) * hs
    have b2 : b 2 = 64 := by simp only [b]; linear_combination 96 * hs
    have b3 : b 3 = 504 := by simp only [b]; linear_combination (84 * s ^ 2 + 780) * hs
    have key : ∀ n, (a (n + 1) : ℝ) = b (n + 1) ∧ (a (n + 2) : ℝ) = b (n + 2) ∧
        (a (n + 3) : ℝ) = b (n + 3) := by
      intro n
      induction n with
      | zero => refine ⟨?_, ?_, ?_⟩ <;> simp [a1, a2, a3, b1, b2, b3]
      | succ n ih =>
        refine ⟨ih.2.1, ih.2.2, ?_⟩
        have h := rec3 n
        have h' : (a (n + 4) : ℝ) = 13 * a (n + 3) - 33 * a (n + 2) - 63 * a (n + 1) := by
          exact_mod_cast h
        rw [show n + 1 + 3 = n + 4 by ring, h', hb (n + 1), ih.1, ih.2.1, ih.2.2]
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact (key m).1

