import OMAReductions.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1

open Erdos724

private def square {n : ℕ} {R : Type*} [CommRing R] (e : Fin n ≃ R)
    (c : R) (hc : IsUnit c) : LatinSquare n where
  mat i j := e.symm (e i + c * e j)
  row_injective i := by
    intro j k h
    exact e.injective (hc.mul_right_inj.mp (add_left_cancel (e.symm.injective h)))
  col_injective j := by
    intro i k h
    exact e.injective (add_right_cancel (e.symm.injective h))

private lemma construct {n : ℕ} {R : Type*} [CommRing R] (e : Fin n ≃ R)
    (c : R) (hc : IsUnit c) (hd : IsUnit (c - 1)) (hne : c ≠ 1) :
    ∃ L M : LatinSquare n, L ≠ M ∧ IsOrthogonal L M := by
  refine ⟨square e 1 isUnit_one, square e c hc, ?_, ?_⟩
  · intro h
    have he := congrArg (fun L : LatinSquare n => e (L.mat (e.symm 0) (e.symm 1))) h
    exact hne (by simpa [square] using he.symm)
  · rintro ⟨i,j⟩ ⟨k,l⟩ h
    have h₁ := congrArg (fun p : Fin n × Fin n => e p.1) h
    have h₂ := congrArg (fun p : Fin n × Fin n => e p.2) h
    change e (e.symm (e i + 1 * e j)) = e (e.symm (e k + 1 * e l)) at h₁
    change e (e.symm (e i + c * e j)) = e (e.symm (e k + c * e l)) at h₂
    simp only [Equiv.apply_symm_apply, one_mul] at h₁ h₂
    have hj : e j = e l := hd.mul_right_inj.mp (by linear_combination h₂ - h₁)
    rw [hj] at h₁
    exact Prod.ext (e.injective (add_right_cancel h₁)) (e.injective hj)

theorem OMA.solution : OMA.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1.H2 := by
  classical
  intro n h4 hn
  obtain ⟨k,m,hm,rfl⟩ := Nat.exists_eq_two_pow_mul_odd (show n ≠ 0 by omega)
  have hk : 2 ≤ k := by
    by_contra! h
    obtain ⟨t, ht⟩ := hm
    interval_cases k <;> simp at h4 <;> omega
  let F := GaloisField 2 k
  letI : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = 2 ^ k := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 k (by omega)
  have hlarge : 2 < Fintype.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) hk)
  let f := Fintype.equivFin F
  obtain ⟨v,hv₀,hv₁⟩ := Fin.exists_ne_and_ne_of_two_lt (f 0) (f 1) hlarge
  let u := f.symm v
  have hu₀ : u ≠ 0 := fun h => hv₀ (by simpa [u] using congrArg f h)
  have hu₁ : u ≠ 1 := fun h => hv₁ (by simpa [u] using congrArg f h)
  haveI : NeZero m := ⟨by rintro rfl; simp at hm⟩
  let R := F × ZMod m
  let e : Fin (2^k*m) ≃ R := Fintype.equivOfCardEq (by simp [R, hF, ZMod.card])
  apply construct e (u, (2 : ZMod m))
  · apply Prod.isUnit_iff.mpr
    exact ⟨hu₀.isUnit, by simpa using (ZMod.isUnit_iff_coprime 2 m).mpr hm.coprime_two_left⟩
  · apply Prod.isUnit_iff.mpr
    exact ⟨(sub_ne_zero.mpr hu₁).isUnit, by change IsUnit (2 - 1 : ZMod m); ring_nf; exact isUnit_one⟩
  · exact fun h => hu₁ (congrArg Prod.fst h)
