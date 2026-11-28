import OMAStatements.S_oeis_a229795

/-!
Relabel the symbols that occur in a matrix by their ranks. This preserves
both lexicographic comparisons. For each set of k symbols the number of
admissible matrices that use them all is therefore independent of the set.
Only k = 1, 2, 3, 4 can occur.
-/

namespace DoubleLexMatrices

open Finset OMA.S_oeis_a229795

private abbrev Grid (α : Type) := Fin 2 → Fin 2 → α

private def valid {α : Type} [LinearOrder α] (m : Grid α) : Prop :=
  (m 0 0 < m 1 0 ∨ (m 0 0 = m 1 0 ∧ m 0 1 ≤ m 1 1)) ∧
  (m 0 0 < m 0 1 ∨ (m 0 0 = m 0 1 ∧ m 1 0 ≤ m 1 1))

private instance {α : Type} [LinearOrder α] : DecidablePred (@valid α _) :=
  fun _ => by unfold valid; infer_instance

private def letters {α : Type} [DecidableEq α] (m : Grid α) : Finset α :=
  univ.image fun p : Fin 2 × Fin 2 => m p.1 p.2

private theorem mem_letters {α : Type} [DecidableEq α] (m : Grid α) (y : α) :
    y ∈ letters m ↔ ∃ i j, m i j = y := by
  simp [letters, Prod.exists]

private def full (k : ℕ) : ℕ :=
  ((univ : Finset (Grid (Fin k))).filter (fun m => valid m ∧ letters m = univ)).card

private theorem enough (k : ℕ) (hk : 4 < k) : full k = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro m hm
  have he := (mem_filter.mp hm).2.2
  have hc := Finset.card_image_le (f := fun p : Fin 2 × Fin 2 => m p.1 p.2)
    (s := (univ : Finset (Fin 2 × Fin 2)))
  change (letters m).card ≤ _ at hc
  rw [he] at hc
  simp at hc
  omega

private theorem fiber (n : ℕ) (s : Finset (Fin (n+1))) :
    (((univ : Finset (Grid (Fin (n+1)))).filter valid).filter (fun m => letters m = s)).card =
      full s.card := by
  let e := s.orderIsoOfFin rfl
  let expand (m : Grid (Fin s.card)) : Grid (Fin (n+1)) := fun i j => (e (m i j)).val
  have preserves (m) : valid (expand m) ↔ valid m := by simp [valid, expand, e]
  symm
  apply Finset.card_bij (fun m _ => expand m)
  · intro m hm
    obtain ⟨hv, hu⟩ := (mem_filter.mp hm).2
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, (preserves m).mpr hv⟩, ?_⟩
    ext y
    rw [mem_letters]
    constructor
    · rintro ⟨i,j,rfl⟩
      exact (e (m i j)).property
    · intro hy
      let d : Fin s.card := e.symm ⟨y, hy⟩
      have hd : d ∈ letters m := by rw [hu]; exact mem_univ _
      obtain ⟨i,j,hij⟩ := (mem_letters m d).mp hd
      exact ⟨i,j, by simp [expand, hij, d]⟩
  · intro m _ w _ h
    funext i j
    apply e.injective
    apply Subtype.ext
    exact congrFun (congrFun h i) j
  · intro m hm
    obtain ⟨hv, hs⟩ := mem_filter.mp hm
    have hm' (i j) : m i j ∈ s := by
      rw [← hs, mem_letters]
      exact ⟨i,j,rfl⟩
    let w : Grid (Fin s.card) := fun i j => e.symm ⟨m i j, hm' i j⟩
    have ew : expand w = m := by funext i j; simp [expand, w]
    refine ⟨w, mem_filter.mpr ⟨mem_univ _, (preserves w).mp (ew ▸ (mem_filter.mp hv).2), ?_⟩, ew⟩
    apply eq_univ_of_forall
    intro d
    have hy : (e d).val ∈ letters m := hs.symm ▸ (e d).property
    obtain ⟨i,j,hij⟩ := (mem_letters m _).mp hy
    refine (mem_letters w d).mpr ⟨i,j, ?_⟩
    apply e.injective
    apply Subtype.ext
    simpa [w] using hij

private theorem decompose (n : ℕ) : a n = ∑ s : Finset (Fin (n+1)), full s.card := by
  have ha : a n = ((univ : Finset (Grid (Fin (n+1)))).filter valid).card := by
    unfold a
    congr 1
  rw [ha]
  simp_rw [← fiber n]
  simpa using (sum_card_fiberwise_eq_card_filter
    ((univ : Finset (Grid (Fin (n+1)))).filter valid) univ letters).symm


set_option maxRecDepth 12000 in
set_option maxHeartbeats 1200000 in
private theorem ranks (k : ℕ) : full k =
    (if k = 1 then 1 else 0) + (if k = 2 then 5 else 0) +
    (if k = 3 then 11 else 0) + (if k = 4 then 8 else 0) := by
  rcases k with _ | _ | _ | _ | _ | k
  · decide
  · decide
  · decide
  · decide
  · decide
  rw [enough _ (by omega)]
  simp [show k+5 ≠ 2 by omega,
    show k+5 ≠ 3 by omega, show k+5 ≠ 4 by omega]

private theorem binomial (n : ℕ) (hn : 3 ≤ n) :
    a n = (n+1).choose 1 + 5*(n+1).choose 2 + 11*(n+1).choose 3 + 8*(n+1).choose 4 := by
  have h := Finset.sum_powerset_apply_card full (x := (univ : Finset (Fin (n+1))))
  rw [decompose]
  simp only [powerset_univ, card_univ, Fintype.card_fin] at h
  rw [h]
  simp only [ranks, nsmul_eq_mul, Nat.mul_add, mul_ite, mul_zero, mul_one, sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_range, if_pos (show 1 < n+1+1 by omega),
    if_pos (show 2 < n+1+1 by omega), if_pos (show 3 < n+1+1 by omega),
    if_pos (show 4 < n+1+1 by omega), Nat.cast_id]
  ring


private theorem poly (n : ℕ) : 6*(a n : ℤ) =
    2*(n : ℤ)^4 + 7*(n : ℤ)^3 + 13*(n : ℤ)^2 + 14*n + 6 := by
  by_cases small : n < 3
  · interval_cases n <;> decide
  obtain ⟨k,rfl⟩ : ∃ k, n=k+3 := ⟨n-3, by omega⟩
  suffices h : 6*a (k+3) = 2*(k+3)^4+7*(k+3)^3+13*(k+3)^2+14*(k+3)+6 by
    exact_mod_cast h
  rw [binomial _ (by omega), Nat.choose_one_right]
  have e2 := Nat.descFactorial_eq_factorial_mul_choose (k+4) 2
  have e3 := Nat.descFactorial_eq_factorial_mul_choose (k+4) 3
  have e4 := Nat.descFactorial_eq_factorial_mul_choose (k+4) 4
  norm_num [Nat.descFactorial, Nat.factorial] at e2 e3 e4
  simp only [show k+4-2=k+2 by omega, show k+4-3=k+1 by omega] at e3 e4
  rw [show k+3+1=k+4 by omega]
  nlinarith only [e2,e3,e4]

private theorem backward (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 5*a (n-1)-10*a (n-2)+10*a (n-3)-5*a (n-4)+a (n-5) := by
  obtain ⟨k,rfl⟩ : ∃ k, n=k+6 := ⟨n-6, by omega⟩
  simp only [show k+6-1=k+5 by omega, show k+6-2=k+4 by omega,
    show k+6-3=k+3 by omega, show k+6-4=k+2 by omega, show k+6-5=k+1 by omega]
  have h6 := poly (k+6)
  have h5 := poly (k+5)
  have h4 := poly (k+4)
  have h3 := poly (k+3)
  have h2 := poly (k+2)
  have h1 := poly (k+1)
  push_cast at h6 h5 h4 h3 h2 h1
  nlinarith only [h6,h5,h4,h3,h2,h1]

open PowerSeries in
private theorem generating :
    (1-X)^5 * PowerSeries.mk (fun n => if n=0 then (0 : ℤ) else a n) =
      X*(7-6*X+11*X^2-5*X^3+X^4) := by
  let F := PowerSeries.mk (fun n => if n=0 then (0 : ℤ) else a n)
  change _ * F = _
  suffices H : F - (5:ℕ) • (F*X^1) + (10:ℕ) • (F*X^2) - (10:ℕ) • (F*X^3)
      + (5:ℕ) • (F*X^4) - F*X^5 =
      (7:ℕ) • (X^1 : PowerSeries ℤ) - (6:ℕ) • X^2 + (11:ℕ) • X^3 - (5:ℕ) • X^4 + X^5 by
    simp only [nsmul_eq_mul, Nat.cast_ofNat] at H
    linear_combination H
  have h1 := poly 1
  have h2 := poly 2
  have h3 := poly 3
  have h4 := poly 4
  have h5 := poly 5
  norm_num at h1 h2 h3 h4 h5
  ext n
  simp only [map_add, map_sub, map_nsmul]
  simp only [nsmul_eq_mul, Nat.cast_ofNat, coeff_mul_X_pow', coeff_X_pow, F, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | _ | k
  all_goals try (solve | norm_num <;> omega)
  have h := backward (k+6) (by omega)
  simp [show 1 ≤ k+6 by omega, show 2 ≤ k+6 by omega, show 3 ≤ k+6 by omega,
    show 4 ≤ k+6 by omega, show 5 ≤ k+6 by omega,
    show k+6 ≠ 2 by omega, show k+6 ≠ 3 by omega, show k+6 ≠ 4 by omega, show k+6 ≠ 5 by omega]
  simp only [Nat.add_assoc, Nat.reduceAdd] at h ⊢
  simp only [show k+6-1=k+5 by omega, show k+6-2=k+4 by omega,
    show k+6-3=k+3 by omega, show k+6-4=k+2 by omega, show k+6-5=k+1 by omega] at h
  omega

theorem result : type_of% @OMA.S_oeis_a229795.main := ⟨backward, generating⟩

end DoubleLexMatrices

theorem OMA.solution : type_of% @OMA.S_oeis_a229795.main := DoubleLexMatrices.result
