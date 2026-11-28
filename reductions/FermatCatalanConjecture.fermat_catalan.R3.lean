import FormalConjectures.Wikipedia.FermatCatalanConjecture

/-! Finiteness follows from a uniform prime bound on two of the three powered values. -/

namespace OMA.R_FermatCatalanConjecture_fermat_catalan_R3

open FermatCatalanConjecture

def H1 : Prop :=
  ∀ S : Finset ℕ, {u : ℤ × ℤ | u.1 ≠ 0 ∧ u.2 ≠ 0 ∧ u.1.natAbs.Coprime u.2.natAbs ∧
    u.1.natAbs.primeFactors ⊆ S ∧ u.2.natAbs.primeFactors ⊆ S ∧
    ∃ z n : ℕ, 0 < z ∧ 2 ≤ n ∧ u.1 + u.2 = ((z^n : ℕ) : ℤ)}.Finite

def H2 : Prop :=
  ∃ S : Finset ℕ, ∀ t ∈ FermatCatalanSet,
    (t.1.primeFactors ⊆ S ∧ t.2.1.primeFactors ⊆ S) ∨
    (t.1.primeFactors ⊆ S ∧ t.2.2.primeFactors ⊆ S) ∨
    (t.2.1.primeFactors ⊆ S ∧ t.2.2.primeFactors ⊆ S)

lemma exponent_two {f : Fin 6 → ℕ} (member : f ∈ FermatCatalanSet')
    {i : Fin 6} (index : i ∈ Finset.Icc (3 : Fin 6) 5) : 2 ≤ f i := by
  by_contra! small
  have one : f i = 1 := by have := member.1 i; omega
  have term := Finset.single_le_sum (f := fun j => (1 / f j : ℝ)) (fun j _ => by positivity) index
  rw [one, Nat.cast_one, div_one] at term
  exact member.2.2.2.not_ge term

lemma finite_slice (units : H1) (S : Finset ℕ) :
    {t ∈ FermatCatalanSet |
      (t.1.primeFactors ⊆ S ∧ t.2.1.primeFactors ⊆ S) ∨
      (t.1.primeFactors ⊆ S ∧ t.2.2.primeFactors ⊆ S) ∨
      (t.2.1.primeFactors ⊆ S ∧ t.2.2.primeFactors ⊆ S)}.Finite := by
  classical
  obtain ⟨M,bound⟩ := ((units S).image (fun u : ℤ × ℤ => u.1.natAbs + u.2.natAbs)).bddAbove
  apply ((Set.finite_Iic M).prod ((Set.finite_Iic M).prod (Set.finite_Iic M))).subset
  rintro t ⟨⟨f,hf,rfl⟩,supported⟩
  let A := f 0 ^ f 3
  let B := f 1 ^ f 4
  let C := f 2 ^ f 5
  have ha : 0 < A := pow_pos (hf.1 _) _
  have hb : 0 < B := pow_pos (hf.1 _) _
  have eqn : A+B=C := hf.2.2.1
  have hc : 0 < C := eqn ▸ add_pos ha hb
  have cop : A.Coprime B := (show (f 0).Coprime (f 1) from hf.2.1 (by simp) (by simp) (by decide)).pow _ _
  have zi : (A:ℤ)+(B:ℤ)=(C:ℤ) := by exact_mod_cast eqn
  have nonzero {a : ℕ} (p : 0 < a) : (a:ℤ) ≠ 0 := by exact_mod_cast p.ne'
  have difference {u v z n : ℕ} (hu : 0 < u) (hv : 0 < v) (co : u.Coprime v)
      (su : u.primeFactors ⊆ S) (sv : v.primeFactors ⊆ S) (hz : 0 < z) (hn : 2 ≤ n)
      (eq : (u:ℤ) + -(v:ℤ) = ((z^n : ℕ) : ℤ)) : u ≤ M := by
    apply (Nat.le_add_right u v).trans
    exact bound ⟨((u:ℤ),-(v:ℤ)),⟨nonzero hu,neg_ne_zero.mpr (nonzero hv),by simpa using co,su,
      by simpa using sv,z,n,hz,hn,eq⟩,by simp⟩
  have cap : C ≤ M := by
    rcases supported with ⟨a,b⟩ | ⟨a,c⟩ | ⟨b,c⟩
    · exact bound ⟨((A:ℤ),(B:ℤ)),⟨nonzero ha,nonzero hb,cop,a,b,
          f 2,f 5,hf.1 _,exponent_two hf (by decide),zi⟩,eqn⟩
    · have co : C.Coprime A := (eqn ▸ Nat.coprime_self_add_right.mpr cop).symm
      exact difference hc ha co c a (hf.1 1) (exponent_two hf (i := 4) (by decide))
        (show (C:ℤ) + -(A:ℤ) = (B:ℤ) by omega)
    · have co : C.Coprime B := (eqn ▸ Nat.coprime_add_self_right.mpr cop.symm).symm
      exact difference hc hb co c b (hf.1 0) (exponent_two hf (i := 3) (by decide))
        (show (C:ℤ) + -(B:ℤ) = (A:ℤ) by omega)
  exact ⟨(Nat.le_add_right A B).trans (eqn ▸ cap), (Nat.le_add_left B A).trans (eqn ▸ cap), cap⟩

lemma bounded_of_finite (finite : FermatCatalanSet.Finite) : H2 := by
  classical
  let factors (t : ℕ × ℕ × ℕ) := t.1.primeFactors ∪ t.2.1.primeFactors
  refine ⟨finite.toFinset.biUnion factors, ?_⟩
  intro t ht
  have cover : factors t ⊆ finite.toFinset.biUnion factors :=
    fun _ hp => Finset.mem_biUnion.mpr ⟨t,finite.mem_toFinset.mpr ht,hp⟩
  exact Or.inl ⟨Finset.subset_union_left.trans cover,Finset.subset_union_right.trans cover⟩

theorem main : H1 → H2 → type_of% @FermatCatalanConjecture.fermat_catalan := by
  rintro units ⟨S,cover⟩
  exact (finite_slice units S).subset fun t ht => ⟨ht,cover t ht⟩

end OMA.R_FermatCatalanConjecture_fermat_catalan_R3
