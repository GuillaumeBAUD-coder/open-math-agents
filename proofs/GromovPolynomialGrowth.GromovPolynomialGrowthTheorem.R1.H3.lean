import OMAReductions.R_GromovPolynomialGrowth_GromovPolynomialGrowthTheorem_R1
import Mathlib

/-! Choose a finite set of coset representatives. Each generator times a representative
rewrites as a representative times a subgroup word of bounded length. Induction from
the right end of a word gives a linear bound on the total subgroup word length. -/

open Set GromovPolynomialGrowth

theorem OMA.solution : OMA.R_GromovPolynomialGrowth_GromovPolynomialGrowthTheorem_R1.H3 := by
  classical
  intro G _ H hidx hpoly
  let := hidx
  obtain ⟨S, hS, hgen, C, d, hC, hbound⟩ := hpoly
  let rep (g : G) : G := (QuotientGroup.mk g : G ⧸ H).out
  let R : Set G := insert 1 (range fun q : G ⧸ H => q.out)
  have hR : R.Finite := (finite_range _).insert _
  have hr (g : G) : rep g ∈ R := Or.inr ⟨_, rfl⟩
  let rem (g : G) : H := ⟨(rep g)⁻¹ * g, QuotientGroup.eq.mp
    (QuotientGroup.out_eq' (QuotientGroup.mk g : G ⧸ H))⟩
  have split (g : G) : rep g * (rem g : G) = g := by simp [rem]
  let T := R ∪ H.subtype '' S
  have hT : T.Finite := hR.union (hS.image _)
  have genT : Subgroup.closure T = ⊤ := by
    have hh : Subgroup.closure S ≤ (Subgroup.closure T).comap H.subtype :=
      (Subgroup.closure_le _).2 fun x hx => Subgroup.subset_closure (Or.inr ⟨x,hx,rfl⟩ : (x:G) ∈ T)
    rw [hgen] at hh
    apply top_unique
    intro g _
    rw [← split g]
    exact (Subgroup.closure T).mul_mem (Subgroup.subset_closure (Or.inl (hr g))) (hh (Subgroup.mem_top (rem g)))
  let A := T ∪ (fun g : G => g⁻¹) '' T
  have hA : A.Finite := hT.union (hT.image _)
  let B := (fun p : G × G => rem (p.1 * p.2)) '' (A ×ˢ R)
  have hB : B.Finite := (hA.prod hR).image _
  choose len hlen using exists_cayleyBall_mem_of_closure_eq_top hgen
  obtain ⟨k,hk⟩ := (hB.image len).bddAbove
  let K := k+1
  have short (s r : G) (hs : s ∈ A) (hr' : r ∈ R) : rem (s*r) ∈ CayleyBall S K := by
    have hm : rem (s*r) ∈ B := ⟨(s,r), ⟨hs,hr'⟩, rfl⟩
    exact cayleyBall_monotone S (Nat.le_trans (hk ⟨_,hm,rfl⟩) (Nat.le_succ _)) (hlen _)
  have rewriteWord (l : List G) (hl : ∀ s ∈ l, s ∈ T ∨ s⁻¹ ∈ T) :
      ∃ r ∈ R, ∃ h ∈ CayleyBall S (K*l.length), l.prod = r * (h : G) := by
    induction l with
    | nil => exact ⟨1, Or.inl rfl, 1, one_mem_cayleyBall _ _, by simp⟩
    | cons s l ih =>
      obtain ⟨r,hr',h,hh,he⟩ := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      have hs : s ∈ A := (hl s (by simp)).elim Or.inl (fun hx => Or.inr ⟨s⁻¹,hx,inv_inv s⟩)
      refine ⟨rep (s*r), hr _, rem (s*r)*h, ?_, ?_⟩
      · simpa [Nat.mul_succ, Nat.add_comm] using cayleyBall_mul S (short s r hs hr') hh
      · simp only [List.prod_cons, he, Subgroup.coe_mul]
        rw [← mul_assoc, ← mul_assoc, split]
  let pair (p : G × H) := p.1 * (p.2 : G)
  have growth (n : ℕ) : GrowthFunction T n ≤ R.ncard * GrowthFunction S (K*n) := by
    let P := R ×ˢ CayleyBall S (K*n)
    have hP : P.Finite := hR.prod (cayleyBall_finite hS _)
    have sub : CayleyBall T n ⊆ pair '' P := by
      rintro g ⟨l,hl,ha,rfl⟩
      obtain ⟨r,hr',h,hh,he⟩ := rewriteWord l ha
      exact ⟨(r,h), ⟨hr',cayleyBall_monotone _ (Nat.mul_le_mul_left K hl) hh⟩,he.symm⟩
    exact (ncard_le_ncard sub (hP.image pair)).trans ((ncard_image_le hP).trans_eq ncard_prod)
  refine ⟨T,hT,genT,(R.ncard+1 : ℝ)*C*(K:ℝ)^d,d,?_,?_⟩
  · have hkpos : 0 < K := Nat.succ_pos k
    positivity
  · intro n hn
    have hnK : 0 < K*n := Nat.mul_pos (Nat.succ_pos _) hn
    calc
      (GrowthFunction T n : ℝ) ≤ (R.ncard : ℝ) * GrowthFunction S (K*n) := by exact_mod_cast growth n
      _ ≤ ((R.ncard : ℝ)+1) * (C * ((K*n : ℕ) : ℝ)^d) := by
        exact mul_le_mul (by linarith) (hbound _ hnK) (by positivity) (by positivity)
      _ = _ := by push_cast; rw [mul_pow]; ring
