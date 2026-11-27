import OMAReductions.R_Erdos258_erdos_258_variants_monotone_R1

/-! A tail with geometrically bounded digits becomes strictly between zero and
one after clearing the fixed rational denominator and the initial base product.
The corresponding scaled partial sum is an integer. -/

open Finset Filter

theorem OMA.solution : OMA.R_Erdos258_erdos_258_variants_monotone_R1.H2 := by
  classical
  rintro a d ha grow hd ⟨L,hL,good⟩
  let Q (n : ℕ) := ∏ i ∈ Icc 1 n, a i
  let t (j : ℕ) : ℝ := (d (j+1):ℝ)/(Q (j+1):ℝ)
  change Irrational (∑' j, t j)
  by_contra hrat
  obtain ⟨q,hq⟩ := exists_rat_of_not_irrational hrat
  have qp := q.den_pos
  let R := 4*L
  obtain ⟨N,hgood,hlarge⟩ := (good.and_eventually
    ((eventually_atTop.1 (grow.eventually_ge_atTop (q.den*R))) |>.elim
      (fun b hb => (eventually_ge_atTop b).mono (fun n hn j hj => hb j (hn.trans hj))))).exists
  have pos (n : ℕ) : 0<Q n := prod_pos (fun i _ => lt_of_lt_of_le (by decide : 0<2) (ha i))
  have step (n : ℕ) : Q (n+1)=Q n*a (n+1) := prod_Icc_succ_top (by omega) a
  have bound (j : ℕ) : Q N*q.den*R^(j+1) ≤ Q (j+N+1) := by
    induction j with
    | zero =>
      simpa [mul_assoc,step N] using Nat.mul_le_mul_left (Q N) (hlarge (N+1) (by omega))
    | succ j ih =>
      rw [show (j+1)+N+1=(j+N+1)+1 by omega,step (j+N+1),pow_succ R (j+1),← mul_assoc]
      apply Nat.mul_le_mul ih
      exact (by simpa using Nat.mul_le_mul_right R qp : R ≤ q.den*R).trans (hlarge _ (by omega))
  let D := q.den*Q N
  have hD : 0<D := Nat.mul_pos qp (pos N)
  have hpos (j : ℕ) : 0<t j := div_pos (by exact_mod_cast hd j) (by exact_mod_cast pos (j+1))
  have term (j : ℕ) : (D:ℝ)*t (j+N) ≤ (1/4:ℝ)^(j+1) := by
    have hb : D*L^(j+1)*4^(j+1) ≤ Q (j+N+1) := by
      simpa [D,R,mul_pow,mul_comm,mul_left_comm,mul_assoc] using bound j
    have hdj : d (j+N+1) ≤ L^(j+1) := by simpa [Nat.add_comm j N] using hgood j
    have hmul := (Nat.mul_le_mul_right (4^(j+1)) (Nat.mul_le_mul_left D hdj)).trans hb
    have hr : (D:ℝ)*(d (j+N+1):ℝ)*(4:ℝ)^(j+1) ≤ Q (j+N+1) := by exact_mod_cast hmul
    have hqn : (0:ℝ)<Q (j+N+1) := by exact_mod_cast pos _
    dsimp [t]
    rw [one_div_pow,← mul_div_assoc,div_le_div_iff₀ hqn (by positivity)]
    linarith
  let g (j : ℕ) := (D:ℝ)*t (j+N)
  have gn (j : ℕ) : 0 ≤ g j := mul_nonneg (Nat.cast_nonneg _) (hpos _).le
  have geom := summable_geometric_of_lt_one (by norm_num : 0 ≤ (1/4:ℝ)) (by norm_num : (1/4:ℝ)<1)
  have sg1 : Summable (fun j : ℕ => (1/4:ℝ)^(j+1)) := (summable_nat_add_iff 1).mpr geom
  have sg : Summable g := Summable.of_nonneg_of_le gn term sg1
  have ts : Summable t := by
    apply (summable_nat_add_iff N).mp
    apply Summable.of_nonneg_of_le (fun j => (hpos (j+N)).le) _ sg
    intro j
    have hD1 : (1:ℝ) ≤ D := by exact_mod_cast hD
    simpa [g] using mul_le_mul_of_nonneg_right hD1 (hpos (j+N)).le
  have tail₀ : 0 < ∑' j, g j := sg.tsum_pos gn 0 (mul_pos (by exact_mod_cast hD) (hpos _))
  have tail₁ : (∑' j, g j) < 1 := by
    have h := sg.tsum_le_tsum term sg1
    have geomval := tsum_geometric_of_lt_one (by norm_num : 0 ≤ (1/4:ℝ)) (by norm_num : (1/4:ℝ)<1)
    have e := geom.sum_add_tsum_nat_add 1
    simp only [sum_range_one,pow_zero,geomval] at e
    linarith
  have integral (j : ℕ) (hj : j ∈ range N) : ∃ z : ℕ, (D:ℝ)*t j=z := by
    have div : Q (j+1) ∣ Q N := Finset.prod_dvd_prod_of_subset _ _ _ (by
      apply Icc_subset_Icc_right
      exact mem_range.mp hj)
    obtain ⟨v,hv⟩ := div
    refine ⟨q.den*v*d (j+1),?_⟩
    have hp : (Q (j+1):ℝ)≠0 := by exact_mod_cast (pos (j+1)).ne'
    dsimp [D,t]
    rw [hv]
    push_cast
    field_simp
  choose z hz using integral
  let c := ∑ j ∈ (range N).attach, z j j.2
  have pref : (D:ℝ)*(∑ j ∈ range N,t j) = c := by
    rw [mul_sum,← sum_attach]
    dsimp [c]
    push_cast
    exact sum_congr rfl (fun j _ => hz j j.2)
  have split := ts.sum_add_tsum_nat_add N
  have eq : (D:ℝ)*(∑' j,t j) = (q.num : ℝ)*Q N := by
    rw [hq,Rat.cast_def]
    dsimp [D]
    push_cast
    field_simp
  have full : (c:ℝ)+(∑' j,g j)=(q.num:ℝ)*Q N := by
    rw [← eq,← split,mul_add,pref]
    simp [g,tsum_mul_left]
  let v : ℤ := q.num*Q N-c
  have vz : (v:ℝ) = ∑' j,g j := by dsimp [v]; push_cast; linarith
  have vpos : (0:ℤ)<v := by exact_mod_cast (vz ▸ tail₀ : (0:ℝ)<v)
  have vlt : v<(1:ℤ) := by exact_mod_cast (vz ▸ tail₁ : (v:ℝ)<1)
  omega
