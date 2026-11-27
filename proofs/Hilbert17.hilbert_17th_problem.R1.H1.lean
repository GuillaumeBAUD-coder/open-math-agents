import OMAReductions.R_Hilbert17_hilbert_17th_problem_R1

/-!
Artin–Schreier separation for sums of squares. Starting with the sums of squares, adjoin the negative of the given element and take a maximal field preordering. Adjoining any element whose negative is absent preserves properness, so the maximal preordering is total.
-/
namespace AH17
variable {K : Type*} [Field K]

-- An element whose negative is absent can be adjoined to a preordering.
theorem extend (P : RingPreordering K) (x : K) (hx : -x ∉ P) :
    ∃ Q : RingPreordering K, P ≤ Q ∧ x ∈ Q := by
  let S : Set K := {z | ∃ u ∈ P, ∃ v ∈ P, z = u + v*x}
  have incl {u : K} (hu : u∈P) : u∈S := ⟨u,hu,0,zero_mem _,by ring⟩
  have add {a b : K} (ha : a∈S) (hb : b∈S) : a+b∈S := by
    obtain ⟨u,hu,v,hv,rfl⟩ := ha
    obtain ⟨s,hs,t,ht,rfl⟩ := hb
    exact ⟨u+s,add_mem hu hs,v+t,add_mem hv ht,by ring⟩
  have mul {a b : K} (ha : a∈S) (hb : b∈S) : a*b∈S := by
    obtain ⟨u,hu,v,hv,rfl⟩ := ha
    obtain ⟨s,hs,t,ht,rfl⟩ := hb
    exact ⟨u*s+(v*t)*(x*x),add_mem (mul_mem hu hs) (mul_mem (mul_mem hv ht) (P.mul_self_mem x)),
      u*t+v*s,add_mem (mul_mem hu ht) (mul_mem hv hs),by ring⟩
  have neg : -1∉S := by
    rintro ⟨u,hu,v,hv,h⟩
    by_cases hz : v=0
    · have h' : (-1:K)=u := by simpa [hz] using h
      exact P.neg_one_notMem (h' ▸ hu)
    · apply hx
      have eq : -x=(1+u)*v⁻¹ := by field_simp; linear_combination h
      rw [eq]
      exact mul_mem (add_mem (one_mem _) hu) (RingPreordering.inv_mem hv)
  exact ⟨RingPreordering.mk' S add mul (fun t => incl (P.mul_self_mem t)) neg,
    fun _ h => incl h,0,zero_mem _,1,one_mem _,by ring⟩

theorem maximal (P : RingPreordering K) : ∃ Q : RingPreordering K, P≤Q ∧ IsMax Q := by
  apply zorn_le_nonempty_Ici₀ P _ P le_rfl
  intro c _ hchain B hB
  let S : Set K := {x | ∃ Q ∈ c, x∈Q}
  have both {x y : K} (hx : x∈S) (hy : y∈S) : ∃ Q∈c,x∈Q ∧ y∈Q := by
    obtain ⟨Q,hQ,hx⟩ := hx
    obtain ⟨R,hR,hy⟩ := hy
    rcases hchain.total hQ hR with h|h
    · exact ⟨R,hR,h hx,hy⟩
    · exact ⟨Q,hQ,hx,h hy⟩
  let M := RingPreordering.mk' S
    (fun hx hy => by obtain ⟨Q,hQ,hx,hy⟩ := both hx hy; exact ⟨Q,hQ,add_mem hx hy⟩)
    (fun hx hy => by obtain ⟨Q,hQ,hx,hy⟩ := both hx hy; exact ⟨Q,hQ,mul_mem hx hy⟩)
    (fun x => ⟨B,hB,B.mul_self_mem x⟩)
    (by rintro ⟨Q,_,h⟩; exact Q.neg_one_notMem h)
  exact ⟨M,fun Q hQ x hx => ⟨Q,hQ,hx⟩⟩

theorem order {K : Type} [Field K] [IsSemireal K] {a : K} (ha : ¬ IsSumSq a) :
    ∃ (_ : LinearOrder K) (_ : IsStrictOrderedRing K), a<0 := by
  classical
  let P := RingPreordering.mk' {s : K | IsSumSq s}
    (fun x y => IsSumSq.add x y) (fun x y => IsSumSq.mul x y)
    IsSumSq.mul_self (IsSemireal.not_isSumSq_neg_one K)
  obtain ⟨Q,_,hq⟩ := extend P (-a) (by simpa [P] using ha)
  obtain ⟨M,hQM,hmax⟩ := maximal Q
  have total (x : K) : x ∈ M ∨ -x ∈ M := by
    by_cases h : -x∈M
    · exact Or.inr h
    obtain ⟨N,hMN,hx⟩ := extend M x h
    exact Or.inl (hmax hMN hx)
  let C : RingCone K := ⟨M.toSubsemiring,fun h h' => M.eq_zero_of_mem_of_neg_mem h h'⟩
  letI : HasMemOrNegMem C := ⟨total⟩
  letI : LinearOrder K := .mkOfAddGroupCone C
  letI : IsOrderedRing K := IsOrderedRing.mkOfCone C
  refine ⟨inferInstance,inferInstance,lt_of_le_of_ne ?_ ?_⟩
  · change 0-a ∈ C
    simpa using (show -a ∈ C from hQM hq)
  · rintro rfl; exact ha .zero
end AH17


theorem OMA.solution : OMA.R_Hilbert17_hilbert_17th_problem_R1.H1 := AH17.order
