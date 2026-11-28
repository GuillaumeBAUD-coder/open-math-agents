import OMAStatements.S_oeis_a183644

open OMA.S_oeis_a183644 PowerSeries

private abbrev Row := Fin 2 → Fin 5

private def total (u : Row) : ℕ := (u 0 : ℕ) + u 1

private theorem total_lt (u : Row) : total u < 9 := by
  unfold total
  have h₀ := (u 0).isLt
  have h₁ := (u 1).isLt
  omega

private def complementOdd {n : ℕ} (x : Fin (n+1) → Row) (i : Fin (n+1)) (j : Fin 2) :
    Fin 5 := if i.val % 2 = 0 then x i j else (x i j).rev

private theorem normalize_involutive {n : ℕ} (x : Fin (n+1) → Row) :
    complementOdd (complementOdd x) = x := by
  funext i j
  by_cases h : i.val % 2 = 0 <;> simp [complementOdd,h]

private theorem reverse_value (i : Fin 5) : i.rev.val = 4-i.val := by
  fin_cases i <;> decide

private theorem normalize_total {n : ℕ} (x : Fin (n+1) → Row) (i : Fin (n+1)) :
    total (complementOdd x i) = if i.val % 2 = 0 then total (x i) else 8-total (x i) := by
  by_cases h : i.val % 2 = 0
  · simp [complementOdd,h,total]
  · simp only [complementOdd,h,if_false,total]
    have h₀ := (x i 0).isLt
    have h₁ := (x i 1).isLt
    rw [reverse_value,reverse_value]
    omega

private theorem normalize_criterion {n : ℕ} (x : Fin (n+1) → Row) :
    (∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ)) ↔
      ∀ i, total (complementOdd x i) = total (complementOdd x 0) := by
  have hadj (i : Fin n) : BlockOK (x i.castSucc) (x i.succ) ↔
      total (complementOdd x i.castSucc) = total (complementOdd x i.succ) := by
    rw [normalize_total, normalize_total]
    have h₀ := total_lt (x i.castSucc)
    have h₁ := total_lt (x i.succ)
    unfold BlockOK total at *
    simp only [Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> omega
  constructor
  · intro h i
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih => exact ((hadj i).mp (h i)).symm.trans ih
  · intro h i
    exact (hadj i).mpr ((h i.castSucc).trans (h i.succ).symm)

private abbrev Arrays (n : ℕ) :=
  {x : Fin (n+1) → Row // ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ)}

private abbrev Uniform (n : ℕ) :=
  {x : Fin (n+1) → Row // ∀ i, total (x i) = total (x 0)}

private def normalEquiv (n : ℕ) : Arrays n ≃ Uniform n where
  toFun x := ⟨complementOdd x.1, (normalize_criterion x.1).mp x.2⟩
  invFun x := ⟨complementOdd x.1, (normalize_criterion _).mpr (by
    rw [normalize_involutive]
    exact x.2)⟩
  left_inv x := Subtype.ext (normalize_involutive x.1)
  right_inv x := Subtype.ext (normalize_involutive x.1)

private abbrev RowsOfSum (s : Fin 9) := {u : Row // total u = s.val}

private noncomputable def uniformEquiv (n : ℕ) :
    (Σ s : Fin 9, Fin (n+1) → RowsOfSum s) ≃ Uniform n := by
  refine Equiv.ofBijective (fun z => ⟨fun i => (z.2 i).1,
    fun i => (z.2 i).2.trans (z.2 0).2.symm⟩) ⟨?_,?_⟩
  · rintro ⟨s,u⟩ ⟨t,v⟩ h
    have h' : (fun i => (u i).1) = fun i => (v i).1 := congrArg Subtype.val h
    have he : s = t := Fin.ext ((u 0).2.symm.trans
      ((congrArg total (congrFun h' 0)).trans (v 0).2))
    subst t
    have hu : u = v := funext fun i => Subtype.ext (congrFun h' i)
    rw [hu]
  · intro x
    let s : Fin 9 := ⟨total (x.1 0),total_lt _⟩
    exact ⟨⟨s,fun i => ⟨x.1 i,x.2 i⟩⟩,Subtype.ext rfl⟩

private theorem row_card (s : Fin 9) :
    Fintype.card (RowsOfSum s) = min (s.val+1) (9-s.val) := by
  fin_cases s <;> decide +kernel

private theorem count_rows (n : ℕ) :
    a n = 2 + 2*2^(n+1) + 2*3^(n+1) + 2*4^(n+1) + 5^(n+1) := by
  change Nat.card (Arrays n) = _
  rw [Nat.card_congr ((normalEquiv n).trans (uniformEquiv n).symm), Nat.card_eq_fintype_card,
    Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_fin, row_card]
  simp [Fin.sum_univ_succ]
  ring

private theorem recurrence (n : ℕ) (hn : 6 ≤ n) :
    (a n : ℤ) = 15*a (n-1)-85*a (n-2)+225*a (n-3)-274*a (n-4)+120*a (n-5) := by
  let k := n-6
  have he : n = k+6 := by dsimp [k]; omega
  rw [he, show k+6-1=k+5 by omega, show k+6-2=k+4 by omega,
    show k+6-3=k+3 by omega, show k+6-4=k+2 by omega, show k+6-5=k+1 by omega]
  simp only [count_rows, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  norm_num [pow_add]
  ring

private noncomputable def factor (r : ℚ) : ℚ⟦X⟧ := 1 - C r * X

private def tail (r : ℚ) : ℚ⟦X⟧ := mk fun n => if n = 0 then 0 else r^(n+1)

private theorem tail_factor (r : ℚ) : tail r * factor r = C (r^2)*X := by
  rw [factor, mul_sub, mul_one, ←mul_assoc]
  ext n
  cases n with
  | zero => simp [tail]
  | succ n =>
    simp only [map_sub, coeff_succ_mul_X, coeff_mul_C, tail, coeff_mk, Nat.succ_ne_zero, if_false]
    cases n with
    | zero => simp
    | succ n =>
      simp [pow_succ]

private theorem series :
    mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  let D : ℚ⟦X⟧ := factor 1 * factor 2 * factor 3 * factor 4 * factor 5
  let N : ℚ⟦X⟧ := X*(85 - 950*X + 3683*X^2 - 5770*X^3 + 3000*X^4)
  have hG : G = N * D⁻¹ := by simp only [G,N,D,factor,map_one,map_ofNat,one_mul]
  rw [hG]
  apply (eq_mul_inv_iff_mul_eq (by simp [D,factor])).mpr
  have hA : mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) =
      C 2*tail 1 + C 2*tail 2 + C 2*tail 3 + C 2*tail 4 + tail 5 := by
    ext n
    by_cases hn : n=0
    · simp [tail, hn]
    · simp [tail, hn, coeff_C_mul, count_rows, Nat.cast_pow]
  rw [hA]
  calc
    _ =
      C 2*(tail 1*factor 1)*(factor 2*factor 3*factor 4*factor 5) +
      C 2*(tail 2*factor 2)*(factor 1*factor 3*factor 4*factor 5) +
      C 2*(tail 3*factor 3)*(factor 1*factor 2*factor 4*factor 5) +
      C 2*(tail 4*factor 4)*(factor 1*factor 2*factor 3*factor 5) +
      (tail 5*factor 5)*(factor 1*factor 2*factor 3*factor 4) := by dsimp [D]; ring
    _ = N := by
      simp only [tail_factor]
      simp only [factor, N, map_one]
      norm_num [map_ofNat]
      ring

theorem OMA.solution : type_of% @OMA.S_oeis_a183644.main := by
  refine ⟨recurrence,series,?_⟩
  intro n _
  rw [count_rows, show (4:ℕ) = 2^2 by decide, ←pow_mul]
  rw [show 2*(n+1) = 2+2*n by omega, show 2+n=n+1+1 by omega,
    show 3+2*n=(2+2*n)+1 by omega]
  simp only [pow_succ]
  ring