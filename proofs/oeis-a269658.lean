import OMAStatements.S_oeis_a269658

namespace OMA.P_oeis_a269658

open OMA.S_oeis_a269658

private lemma a_closed (n : ℕ) : a n = (n + 1) ^ 5 - 3 * n * (n + 1) := by
  unfold a
  have hcompl : Fintype.card {f : Fin 5 → Fin (n + 1) // isValid n f} +
      Fintype.card {f : Fin 5 → Fin (n + 1) // ¬ isValid n f} = (n + 1) ^ 5 := by
    have h1 := Fintype.card_subtype_compl (fun f : Fin 5 → Fin (n + 1) => isValid n f)
    have hle : Fintype.card {f : Fin 5 → Fin (n + 1) // isValid n f} ≤ Fintype.card (Fin 5 → Fin (n + 1)) :=
      Fintype.card_subtype_le _
    have h2 : Fintype.card (Fin 5 → Fin (n + 1)) = (n + 1) ^ 5 := by simp
    omega
  -- Bad arrays split into 3 pairwise disjoint sets: (0,1)=(2,3), (0,1)=(3,4), (1,2)=(3,4)
  -- each in bijection with Fin n × Fin (n + 1)
  let φ : Fin 3 × Fin n × Fin (n + 1) → {f : Fin 5 → Fin (n + 1) // ¬ isValid n f} :=
    fun ⟨k, x, y⟩ =>
      if k.1 = 0 then
        ⟨fun r => match r.1 with
          | 0 => ⟨x.1, by omega⟩ | 1 => ⟨x.1 + 1, by omega⟩
          | 2 => ⟨x.1, by omega⟩ | 3 => ⟨x.1 + 1, by omega⟩ | _ => y,
         by intro hv; exact hv ⟨0, by omega⟩ ⟨2, by omega⟩ (by dsimp; omega) ⟨rfl, rfl, rfl⟩⟩
      else if k.1 = 1 then
        ⟨fun r => match r.1 with
          | 0 => ⟨x.1, by omega⟩ | 1 => ⟨x.1 + 1, by omega⟩
          | 2 => y | 3 => ⟨x.1, by omega⟩ | _ => ⟨x.1 + 1, by omega⟩,
         by intro hv; exact hv ⟨0, by omega⟩ ⟨3, by omega⟩ (by dsimp; omega) ⟨rfl, rfl, rfl⟩⟩
      else
        ⟨fun r => match r.1 with
          | 0 => y | 1 => ⟨x.1, by omega⟩
          | 2 => ⟨x.1 + 1, by omega⟩ | 3 => ⟨x.1, by omega⟩ | _ => ⟨x.1 + 1, by omega⟩,
         by intro hv; exact hv ⟨1, by omega⟩ ⟨3, by omega⟩ (by dsimp; omega) ⟨rfl, rfl, rfl⟩⟩
  have hbij : Function.Bijective φ := by
    constructor
    · rintro ⟨ka, xa, ya⟩ ⟨kb, xb, yb⟩ heq
      have hfun := congrArg Subtype.val heq
      fin_cases ka <;> fin_cases kb
      · have h0 := congrArg Fin.val (congrFun hfun 0)
        have h4 := congrFun hfun 4
        simp [φ] at h0 h4; exact Prod.ext rfl (Prod.ext (Fin.ext h0) h4)
      · have h0 := congrArg Fin.val (congrFun hfun 0)
        have h3 := congrArg Fin.val (congrFun hfun 3)
        simp [φ] at h0 h3; omega
      · have h1 := congrArg Fin.val (congrFun hfun 1)
        have h2 := congrArg Fin.val (congrFun hfun 2)
        have h3 := congrArg Fin.val (congrFun hfun 3)
        simp [φ] at h1 h2 h3; omega
      · have h0 := congrArg Fin.val (congrFun hfun 0)
        have h3 := congrArg Fin.val (congrFun hfun 3)
        simp [φ] at h0 h3; omega
      · have h0 := congrArg Fin.val (congrFun hfun 0)
        have h2 := congrFun hfun 2
        simp [φ] at h0 h2; exact Prod.ext rfl (Prod.ext (Fin.ext h0) h2)
      · have h1 := congrArg Fin.val (congrFun hfun 1)
        have h3 := congrArg Fin.val (congrFun hfun 3)
        have h4 := congrArg Fin.val (congrFun hfun 4)
        simp [φ] at h1 h3 h4; omega
      · have h1 := congrArg Fin.val (congrFun hfun 1)
        have h2 := congrArg Fin.val (congrFun hfun 2)
        have h3 := congrArg Fin.val (congrFun hfun 3)
        simp [φ] at h1 h2 h3; omega
      · have h1 := congrArg Fin.val (congrFun hfun 1)
        have h3 := congrArg Fin.val (congrFun hfun 3)
        have h4 := congrArg Fin.val (congrFun hfun 4)
        simp [φ] at h1 h3 h4; omega
      · have h0 := congrFun hfun 0
        have h1 := congrArg Fin.val (congrFun hfun 1)
        simp [φ] at h0 h1; exact Prod.ext rfl (Prod.ext (Fin.ext h1) h0)
    · rintro ⟨f, hnv⟩
      unfold isValid at hnv; push Not at hnv
      obtain ⟨i, j, hij, hstep, h0, h1⟩ := hnv
      have h0v : (f ⟨j.1, by omega⟩).1 = (f ⟨i.1, by omega⟩).1 := congrArg Fin.val h0
      have h1v : (f ⟨j.1 + 1, by omega⟩).1 = (f ⟨i.1 + 1, by omega⟩).1 := congrArg Fin.val h1
      fin_cases i <;> fin_cases j <;> dsimp at hij hstep h0v h1v
      all_goals try omega
      · -- i=0, j=2
        have hxlt : (f 0).1 < n := by have := (f 1).2; omega
        refine ⟨⟨0, ⟨(f 0).1, hxlt⟩, f 4⟩, Subtype.ext ?_⟩
        funext r; fin_cases r <;> (apply Fin.ext; simp [φ]; try omega)
      · -- i=0, j=3
        have hxlt : (f 0).1 < n := by have := (f 1).2; omega
        refine ⟨⟨1, ⟨(f 0).1, hxlt⟩, f 2⟩, Subtype.ext ?_⟩
        funext r; fin_cases r <;> (apply Fin.ext; simp [φ]; try omega)
      · -- i=1, j=3
        have hxlt : (f 1).1 < n := by have := (f 2).2; omega
        refine ⟨⟨2, ⟨(f 1).1, hxlt⟩, f 0⟩, Subtype.ext ?_⟩
        funext r; fin_cases r <;> (apply Fin.ext; simp [φ]; try omega)
  have hbad : Fintype.card {f : Fin 5 → Fin (n + 1) // ¬ isValid n f} = 3 * n * (n + 1) := by
    rw [← Fintype.card_congr (Equiv.ofBijective φ hbij), Fintype.card_prod, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
    ring
  omega

private lemma a_closed_q (n : ℕ) : (a n : ℚ) = ((n : ℚ) + 1) ^ 5 - 3 * (n : ℚ) * ((n : ℚ) + 1) := by
  have hle : 3 * n * (n + 1) ≤ (n + 1) ^ 5 := by
    have h1 : 3 * n ≤ (n + 1) ^ 4 := by
      have : (n + 1) ^ 4 = n ^ 4 + 4 * n ^ 3 + 6 * n ^ 2 + 4 * n + 1 := by ring
      omega
    nlinarith
  have h := a_closed n
  have h1 : ((a n : ℕ) : ℚ) = (((n + 1) ^ 5 - 3 * n * (n + 1) : ℕ) : ℚ) := by exact_mod_cast h
  rw [h1, Nat.cast_sub hle]
  push_cast; ring

private lemma coeff_X_pow_mul_eq (f : PowerSeries ℚ) (j n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X ^ j * f) = if j ≤ n then PowerSeries.coeff (n - j) f else 0 := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', mul_assoc]
    cases n with
    | zero => simp
    | succ m =>
      rw [PowerSeries.coeff_succ_X_mul, ih m]
      split_ifs with h1 h2
      · simp [Nat.succ_sub_succ]
      · omega
      · omega
      · rfl

private lemma coeff_mul_X_pow_eq (f : PowerSeries ℚ) (j n : ℕ) :
    PowerSeries.coeff n (f * PowerSeries.X ^ j) = if j ≤ n then PowerSeries.coeff (n - j) f else 0 := by
  rw [mul_comm]; exact coeff_X_pow_mul_eq f j n

theorem solution : type_of% @OMA.S_oeis_a269658.main := by
  have hrec : ∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 6 * (a (n - 1) : ℤ) - 15 * (a (n - 2) : ℤ) + 20 * (a (n - 3) : ℤ) -
      15 * (a (n - 4) : ℤ) + 6 * (a (n - 5) : ℤ) - (a (n - 6) : ℤ) := by
    intro n hn
    have hq : (a n : ℚ) = 6 * (a (n - 1) : ℚ) - 15 * (a (n - 2) : ℚ) + 20 * (a (n - 3) : ℚ) -
        15 * (a (n - 4) : ℚ) + 6 * (a (n - 5) : ℚ) - (a (n - 6) : ℚ) := by
      simp only [a_closed_q]
      simp only [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega),
        Nat.cast_sub (show 3 ≤ n by omega), Nat.cast_sub (show 4 ≤ n by omega),
        Nat.cast_sub (show 5 ≤ n by omega), Nat.cast_sub (show 6 ≤ n by omega), Nat.cast_ofNat]
      ring
    exact_mod_cast hq
  refine ⟨?_, hrec, a_closed⟩
  ext n
  have hexp : (1 - (PowerSeries.X : PowerSeries ℚ)) ^ 6 =
      1 - PowerSeries.C 6 * PowerSeries.X ^ 1 + PowerSeries.C 15 * PowerSeries.X ^ 2 -
      PowerSeries.C 20 * PowerSeries.X ^ 3 + PowerSeries.C 15 * PowerSeries.X ^ 4 -
      PowerSeries.C 6 * PowerSeries.X ^ 5 + PowerSeries.X ^ 6 := by
    simp only [map_ofNat]; ring
  rw [hexp]
  have hR : (1 + 20 * PowerSeries.X + 84 * PowerSeries.X ^ 2 + 8 * PowerSeries.X ^ 3 + 7 * PowerSeries.X ^ 4 : PowerSeries ℚ) =
      PowerSeries.C 1 + PowerSeries.C 20 * PowerSeries.X ^ 1 + PowerSeries.C 84 * PowerSeries.X ^ 2 +
      PowerSeries.C 8 * PowerSeries.X ^ 3 + PowerSeries.C 7 * PowerSeries.X ^ 4 := by
    simp only [map_ofNat, map_one]; ring
  rw [hR]
  have hc : ∀ (c : ℚ) (j : ℕ), PowerSeries.coeff n (PowerSeries.mk (fun m => (a m : ℚ)) * (PowerSeries.C c * PowerSeries.X ^ j)) =
      c * if j ≤ n then (a (n - j) : ℚ) else 0 := by
    intro c j
    rw [mul_comm (PowerSeries.C c), ← mul_assoc, mul_comm _ (PowerSeries.C c),
        PowerSeries.coeff_C_mul, coeff_mul_X_pow_eq, PowerSeries.coeff_mk]
  have hX : ∀ (j : ℕ), PowerSeries.coeff n (PowerSeries.mk (fun m => (a m : ℚ)) * PowerSeries.X ^ j) =
      if j ≤ n then (a (n - j) : ℚ) else 0 := by
    intro j; rw [coeff_mul_X_pow_eq, PowerSeries.coeff_mk]
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, PowerSeries.coeff_mk, hc, hX,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_C, PowerSeries.coeff_X_pow]
  rcases n with _ | _ | _ | _ | _ | _ | m
  · simp [a_closed_q]
  · simp [a_closed_q]; norm_num
  · simp [a_closed_q]; norm_num
  · simp [a_closed_q]; norm_num
  · simp [a_closed_q]; norm_num
  · simp [a_closed_q]; norm_num
  · simp only [Nat.add_assoc, Nat.reduceAdd,
      show 1 ≤ m + 6 by omega, show 2 ≤ m + 6 by omega, show 3 ≤ m + 6 by omega,
      show 4 ≤ m + 6 by omega, show 5 ≤ m + 6 by omega, show 6 ≤ m + 6 by omega,
      show ¬(m + 6 = 0) by omega, show ¬(m + 6 = 1) by omega, show ¬(m + 6 = 2) by omega,
      show ¬(m + 6 = 3) by omega, show ¬(m + 6 = 4) by omega, ↓reduceIte,
      show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega,
      show m + 6 - 4 = m + 2 by omega, show m + 6 - 5 = m + 1 by omega, show m + 6 - 6 = m by omega]
    have hr := hrec (m + 6) (by omega)
    simp only [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega,
      show m + 6 - 4 = m + 2 by omega, show m + 6 - 5 = m + 1 by omega, show m + 6 - 6 = m by omega] at hr
    have hrq : (a (m + 6) : ℚ) = 6 * (a (m + 5) : ℚ) - 15 * (a (m + 4) : ℚ) + 20 * (a (m + 3) : ℚ) -
        15 * (a (m + 2) : ℚ) + 6 * (a (m + 1) : ℚ) - (a m : ℚ) := by exact_mod_cast hr
    linarith

end OMA.P_oeis_a269658

theorem OMA.solution : type_of% @OMA.S_oeis_a269658.main :=
  OMA.P_oeis_a269658.solution
