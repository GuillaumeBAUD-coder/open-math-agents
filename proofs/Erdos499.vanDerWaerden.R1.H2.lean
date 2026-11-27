import OMAReductions.R_Erdos499_vanDerWaerden_R1

/-! The finite product rule differentiates one column at a time in the
permanent expansion. The first k columns coincide at zero, so swapping two
of them identifies their derivative contributions. -/

open Matrix Finset

theorem OMA.solution : OMA.R_Erdos499_vanDerWaerden_R1.H2 := by
  classical
  intro n k hk hkn v w C
  let p : Fin n := ⟨k-1,by omega⟩
  have hp : p.val < k := by dsimp [p]; omega
  let A (t : ℝ) : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j =>
    if j.val < k then v i + t*w i else C i j
  let B (j : Fin n) : Matrix (Fin n) (Fin n) ℝ := (A 0).updateCol j w
  have exch (j : Fin n) (hj : j.val < k) : (B j).permanent = (B p).permanent := by
    rw [← Matrix.permanent_permute_rows (Equiv.swap p j) (B p)]
    congr 1
    ext i l
    by_cases hl : l=j
    · subst l
      simp [B, Matrix.submatrix_apply]
    by_cases hlp : l=p
    · subst l
      have hjp := Ne.symm hl
      simp [B,A, Matrix.submatrix_apply,hl,hjp,hp,hj]
    · simp [B,Matrix.submatrix_apply, hl,hlp,
        Equiv.swap_apply_of_ne_of_ne hlp hl]
  have hf (σ : Equiv.Perm (Fin n)) (j : Fin n) :
      HasDerivAt (fun t => A t (σ j) j) (if j.val < k then w (σ j) else 0) 0 := by
    by_cases hj : j.val < k
    · simpa [A,hj,Pi.add_def] using ((hasDerivAt_const (0:ℝ) (v (σ j))).add
        ((hasDerivAt_id (0:ℝ)).mul_const (w (σ j))))
    · simpa [A,hj] using hasDerivAt_const (0:ℝ) (C (σ j) j)
  have hpterm (σ : Equiv.Perm (Fin n)) (j : Fin n) :
      (∏ l ∈ univ.erase j, A 0 (σ l) l) • (if j.val < k then w (σ j) else 0) =
      if j.val < k then ∏ l, B j (σ l) l else 0 := by
    by_cases hj : j.val < k
    · simp only [if_pos hj,smul_eq_mul]
      rw [← prod_erase_mul _ _ (mem_univ j)]
      congr 1
      · apply prod_congr rfl
        intro l hl
        simp [B,(mem_erase.mp hl).1]
      · simp [B]
    · simp [hj]
  have hd := HasDerivAt.fun_sum (u:=univ) (fun σ _ =>
    HasDerivAt.fun_finsetProd (u:=univ) (fun j _ => hf σ j))
  simp_rw [hpterm] at hd
  rw [sum_comm] at hd
  have one (j : Fin n) : (∑ σ : Equiv.Perm (Fin n), if j.val < k then ∏ l, B j (σ l) l else 0) =
      if j.val < k then (B p).permanent else 0 := by
    by_cases hj : j.val < k
    · simpa only [if_pos hj,Matrix.permanent] using exch j hj
    · simp [hj]
  simp_rw [one] at hd
  let e : Fin k ↪ Fin n := ⟨fun i => ⟨i.val,by omega⟩,fun a b h => Fin.ext (congrArg (fun x : Fin n => x.val) h)⟩
  have hs : (univ.filter fun j : Fin n => j.val < k) = univ.map e := by
    ext j
    simp only [mem_filter,mem_univ,true_and,mem_map]
    constructor
    · exact fun h => ⟨⟨j.val,h⟩,Fin.ext rfl⟩
    · rintro ⟨i,rfl⟩
      exact i.isLt
  rw [← sum_filter, sum_const, hs,card_map,card_univ,Fintype.card_fin,nsmul_eq_mul] at hd
  have he : B p = Matrix.of (fun i j : Fin n =>
      if j.val+1 < k then v i else if j.val+1=k then w i else C i j) := by
    ext i j
    by_cases h : j=p
    · subst j
      simp [B, p,show k-1+1=k by omega]
    · have hh : j.val ≠ k-1 := fun hv => h (Fin.ext hv)
      simp [B,A,h,show j.val+1 ≠ k by omega,
        show (j.val+1<k) ↔ j.val<k by omega]
  rw [he] at hd
  exact hd
