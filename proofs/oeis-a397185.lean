import OMAStatements.S_oeis_a397185

-- Credit: @rleshner

namespace BitCover

def P (n x : ℕ) : Prop := 1≤x ∧ x≤n ∧
  (x=1 ∨ x=n ∨ (x+2)%4=n%4 ∨ (x≤4 ∧ x%4=n%4))

instance (n x : ℕ) : Decidable (P n x) := by unfold P; infer_instance

def pairAt (n s x : ℕ) : Prop := x ≤ s ∧ P n x ∧ P n (s-x)

set_option maxHeartbeats 2800000 in
theorem coverage (n t : ℕ) (hn : 9 ≤ n) (ht : 1 ≤ t) (hu : t ≤ n) :
    ∃ i j : ℕ, P n i ∧ P n j ∧ i+j=2*t := by
  have wit (x : ℕ) (hx : pairAt n (2*t) x) :
      ∃ i j : ℕ, P n i ∧ P n j ∧ i+j=2*t := ⟨x,2*t-x,hx.2.1,hx.2.2,by have := hx.1; omega⟩
  rcases (by omega : n%4 = 0 ∨ n%4 = 1 ∨ n%4 = 2 ∨ n%4 = 3) with h|h|h|h <;>
    rcases (by omega : t%2 = 0 ∨ t%2 = 1) with g|g
  · by_cases small2 : t = 2
    · subst t; exact wit 2 (by unfold pairAt P; omega)
    by_cases last : t = n
    · subst t; exact wit n (by unfold pairAt P; omega)
    by_cases low : 2*t ≤ n+2
    · exact wit 2 (by unfold pairAt P; omega)
    · exact wit (n-2) (by unfold pairAt P; omega)
  · by_cases small1 : t = 1
    · subst t; exact wit 1 (by unfold pairAt P; omega)
    by_cases small3 : t = 3
    · subst t; exact wit 2 (by unfold pairAt P; omega)
    by_cases last : t = n
    · subst t; exact wit n (by unfold pairAt P; omega)
    by_cases low : 2*t ≤ n+4
    · exact wit 4 (by unfold pairAt P; omega)
    · exact wit n (by unfold pairAt P; omega)
  · by_cases small2 : t = 2
    · subst t; exact wit 1 (by unfold pairAt P; omega)
    by_cases last : t = n
    · subst t; exact wit n (by unfold pairAt P; omega)
    by_cases low : 2*t ≤ n+1
    · exact wit 1 (by unfold pairAt P; omega)
    · exact wit n (by unfold pairAt P; omega)
  · by_cases small1 : t = 1
    · subst t; exact wit 1 (by unfold pairAt P; omega)
    by_cases small3 : t = 3
    · subst t; exact wit 3 (by unfold pairAt P; omega)
    by_cases last : t = n
    · subst t; exact wit n (by unfold pairAt P; omega)
    by_cases low : 2*t ≤ n+3
    · exact wit 3 (by unfold pairAt P; omega)
    · exact wit (n-2) (by unfold pairAt P; omega)
  · by_cases small2 : t = 2
    · subst t; exact wit 2 (by unfold pairAt P; omega)
    by_cases last : t = n
    · subst t; exact wit n (by unfold pairAt P; omega)
    by_cases low : 2*t ≤ n+4
    · exact wit 4 (by unfold pairAt P; omega)
    · exact wit (n-2) (by unfold pairAt P; omega)
  · by_cases small1 : t = 1
    · subst t; exact wit 1 (by unfold pairAt P; omega)
    by_cases small3 : t = 3
    · subst t; exact wit 2 (by unfold pairAt P; omega)
    by_cases last : t = n
    · subst t; exact wit n (by unfold pairAt P; omega)
    by_cases low : 2*t ≤ n+2
    · exact wit 2 (by unfold pairAt P; omega)
    · exact wit n (by unfold pairAt P; omega)
  · by_cases small2 : t = 2
    · subst t; exact wit 1 (by unfold pairAt P; omega)
    by_cases last : t = n
    · subst t; exact wit n (by unfold pairAt P; omega)
    by_cases low : 2*t ≤ n+3
    · exact wit 3 (by unfold pairAt P; omega)
    · exact wit n (by unfold pairAt P; omega)
  · by_cases small1 : t = 1
    · subst t; exact wit 1 (by unfold pairAt P; omega)
    by_cases small3 : t = 3
    · subst t; exact wit 1 (by unfold pairAt P; omega)
    by_cases last : t = n
    · subst t; exact wit n (by unfold pairAt P; omega)
    by_cases low : 2*t ≤ n+1
    · exact wit 1 (by unfold pairAt P; omega)
    · exact wit (n-2) (by unfold pairAt P; omega)

def below (n x i : ℕ) : Prop := 1 ≤ i ∧ (i < x ∨ (x < i ∧ P n i))

set_option maxHeartbeats 2000000 in
theorem obstruction (n x : ℕ) (hn : 9≤n) (hx : P n x) :
    ∃ t : ℕ, 1≤t ∧ t≤n ∧ ∀ i j : ℕ, below n x i → below n x j → i+j ≠ 2*t := by
  by_cases small : x ≤ 4
  · have hxpos := hx.1
    interval_cases x
    · exact ⟨1,by omega,by omega,by intro i j hi hj; unfold below P at hi hj; omega⟩
    · exact ⟨2,by omega,by omega,by intro i j hi hj; unfold below P at hi hj; unfold P at hx; omega⟩
    · by_cases rn : n%4=3
      · exact ⟨4,by omega,by omega,by intro i j hi hj; unfold below P at hi hj; omega⟩
      · exact ⟨(n+3)/2,by omega,by omega,by intro i j hi hj; unfold below P at hi hj; unfold P at hx; omega⟩
    · by_cases rn : n%4=0
      · exact ⟨5,by omega,by omega,by intro i j hi hj; unfold below P at hi hj; omega⟩
      · exact ⟨(n+4)/2,by omega,by omega,by intro i j hi hj; unfold below P at hi hj; unfold P at hx; omega⟩
  · refine ⟨(n+x)/2,by omega,by have := hx.2.1; omega,?_⟩
    intro i j hi hj
    unfold below P at hi hj
    unfold P at hx
    omega

end BitCover

open OMA.S_oeis_a397185
namespace BitCover

private theorem minimum_eq (n m : ℕ) (hm : 0 < m) (ok : covers n m.bitIndices.toFinset)
    (minimal : ∀ v, 0 < v → covers n v.bitIndices.toFinset → m ≤ v) : a n = m := by
  let s := {v : ℕ | 0 < v ∧ covers n v.bitIndices.toFinset}
  have h : m∈s := ⟨hm,ok⟩
  exact le_antisymm (Nat.sInf_le h) (le_csInf ⟨m,h⟩ (fun v hv => minimal v hv.1 hv.2))

private def mask (n : ℕ) : Finset ℕ := (Finset.range n).filter (fun i => P n (i+1))

private theorem mem_mask {i n : ℕ} : i ∈ mask n ↔ P n (i+1) := by
  simp only [mask, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  intro h
  have := h.2.1
  omega

private theorem mask_minimum (n : ℕ) (hn : 9 ≤ n) :
    a n = ∑ i ∈ mask n, 2^i := by
  let m := ∑ i ∈ mask n, 2^i
  have eqbits : m.bitIndices.toFinset = mask n := Finset.toFinset_bitIndices_sum_two_pow _
  have nonempty : 0∈mask n := mem_mask.mpr ⟨by omega,by omega,Or.inl rfl⟩
  have pos : 0 < m := by
    have := Finset.single_le_sum (f:=fun i : ℕ => (2:ℕ)^i) (fun _ _=>Nat.zero_le _) nonempty
    change 0 < ∑ i ∈ mask n, 2^i
    exact lt_of_lt_of_le (by decide : 0<2^0) this
  apply minimum_eq n m pos
  · rw [eqbits]
    intro t ht hu
    obtain ⟨i,j,hi,hj,hs⟩ := coverage n t hn ht hu
    have h1 : i-1+1=i := by have := hi.1; omega
    have h2 : j-1+1=j := by have := hj.1; omega
    exact ⟨i-1,mem_mask.mpr (by rwa [h1]),j-1,mem_mask.mpr (by rwa [h2]),by omega⟩
  · intro v _ hv
    by_contra! lt
    change v < ∑ i ∈ mask n, 2^i at lt
    rw [← Finset.sum_toFinset_bitIndices_two_pow v] at lt
    apply (Finset.geomSum_lt_geomSum_iff_toColex_lt_toColex (by decide : 2 ≤ 2)).mp at lt
    obtain ⟨a,ha,na,h⟩ := Finset.Colex.toColex_lt_toColex_iff_exists_forall_lt.mp lt
    obtain ⟨t,ht,hu,forbid⟩ := obstruction n (a+1) hn (mem_mask.mp ha)
    obtain ⟨i,hi,j,hj,hs⟩ := hv t ht hu
    have below' {b} (hb : b∈v.bitIndices.toFinset) : below n (a+1) (b+1) := by
      refine ⟨by omega,?_⟩
      by_cases small : b < a
      · exact Or.inl (by omega)
      · have ne : b ≠ a := fun eq => na (eq ▸ hb)
        have hm : b∈mask n := by by_contra absent; exact small (h b hb absent)
        exact Or.inr ⟨by omega,mem_mask.mp hm⟩
    exact forbid _ _ (below' hi) (below' hj) hs

private theorem shiftP (k i : ℕ) (hk : 5 ≤ k) :
    P (2*k) (i+2) ↔ P (2*k-1) (i+1) := by
  unfold P
  rcases (by omega : k = 2*(k/2) ∨ k = 2*(k/2)+1) with h|h <;> omega

private theorem double_mask (k : ℕ) (hk : 5 ≤ k) :
    mask (2*k) = insert 0 ((mask (2*k-1)).image Nat.succ) := by
  ext i
  cases i with
  | zero => simp [mem_mask, P]; omega
  | succ i => simpa [mem_mask] using shiftP k i hk

private theorem large_even (k : ℕ) (hk : 5 ≤ k) : a (2*k) = 2*a (2*k-1)+1 := by
  rw [mask_minimum _ (by omega : 9≤2*k), mask_minimum _ (by omega : 9≤2*k-1),double_mask k hk]
  rw [Finset.sum_insert (by simp),Finset.sum_image (by intro a _ b _ h; exact Nat.succ.inj h)]
  simp only [pow_zero,pow_succ, ← Finset.sum_mul]
  omega

private def good (n m : ℕ) : Prop := ∀ t ∈ Finset.Icc 1 n,
    ∃ i ∈ m.bitIndices.toFinset, ∃ j ∈ m.bitIndices.toFinset, (i+1)+(j+1)=2*t

private instance (n m : ℕ) : Decidable (good n m) := by unfold good; infer_instance

private theorem good_iff (n m : ℕ) : good n m ↔ covers n m.bitIndices.toFinset := by
  simp only [good,covers,Finset.mem_Icc,and_imp]

private def cert (n m : ℕ) : Prop := 0 < m ∧ good n m ∧ ∀ v ∈ Finset.range m, 0 < v → ¬good n v

private instance (n m : ℕ) : Decidable (cert n m) := by unfold cert; infer_instance

private theorem cert_eq {n m} (h : cert n m) : a n = m := by
  apply minimum_eq n m h.1 ((good_iff _ _).mp h.2.1)
  intro v hv hg
  by_contra! hh
  exact h.2.2 v (Finset.mem_range.mpr hh) hv ((good_iff _ _).mpr hg)

private theorem small_even (k : ℕ) (hk : 1 ≤ k) (hs : k < 5) :
    a (2*k) = 2*a (2*k-1)+1 := by
  interval_cases k
  · norm_num [cert_eq (show cert 2 3 by decide +kernel), cert_eq (show cert 1 1 by decide +kernel)]
  · norm_num [cert_eq (show cert 4 11 by decide +kernel), cert_eq (show cert 3 5 by decide +kernel)]
  · norm_num [cert_eq (show cert 6 43 by decide +kernel), cert_eq (show cert 5 21 by decide +kernel)]
  · norm_num [cert_eq (show cert 8 167 by decide +kernel), cert_eq (show cert 7 83 by decide +kernel)]

end BitCover

theorem OMA.solution : type_of% @OMA.S_oeis_a397185.main := by
  intro k hk
  by_cases h : 5≤k
  · exact BitCover.large_even k h
  · exact BitCover.small_even k hk (by omega)
