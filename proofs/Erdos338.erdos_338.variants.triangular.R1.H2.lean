import OMAReductions.R_Erdos338_erdos_338_variants_triangular_R1

namespace OMA.TriangularBasis

lemma residue (k : ℕ) : (k*(k+1)/2)%9=0 ∨ (k*(k+1)/2)%9=1 ∨
    (k*(k+1)/2)%9=3 ∨ (k*(k+1)/2)%9=6 := by
  rw [← Nat.mod_mul_right_div_self (k*(k+1)) 2 9]
  norm_num
  rw [Nat.mul_mod k (k+1) 18, Nat.add_mod k 1 18]
  have h := Nat.mod_lt k (by decide : 0 < 18)
  interval_cases hk : k%18 <;> norm_num [hk]

lemma not_two (u v : ℕ) : (u*(u+1)/2+v*(v+1)/2)%9 ≠ 5 := by
  have hu := residue u
  have hv := residue v
  rw [Nat.add_mod]
  omega

lemma small_sum (S : Multiset ℕ) (hS : ∀ a ∈ S, ∃ u : ℕ, u*(u+1)/2=a)
    (hcard : S.card ≤ 2) : S.sum%9 ≠ 5 := by
  have he : (S.toList : Multiset ℕ)=S := Multiset.coe_toList _
  rw [← he] at hS hcard ⊢
  generalize S.toList = l at *
  rcases l with _ | ⟨a, _ | ⟨b,l⟩⟩
  · simp
  · obtain ⟨u,rfl⟩ := hS a (by simp)
    simpa using not_two u 0
  · have hl : l=[] := by
      apply List.length_eq_zero_iff.mp
      simp only [Multiset.coe_card, List.length_cons] at hcard
      omega
    subst l
    obtain ⟨u,rfl⟩ := hS a (by simp)
    obtain ⟨v,rfl⟩ := hS b (by simp)
    simpa using not_two u v

end OMA.TriangularBasis

-- Step Erdos338.erdos_338.variants.triangular.R1.H2: hypothesis H2 of reduction Erdos338.erdos_338.variants.triangular.R1
-- Credit: @DeepDuke
-- H2 := ¬ HasOrder (Set.range fun k : ℕ ↦ k * (k + 1) / 2) 2

theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_triangular_R1.H2 := by
  intro h
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp h
  obtain ⟨S,hS,hcard,hsum⟩ := hN (9*N+5) (by omega)
  have hbad := OMA.TriangularBasis.small_sum S hS hcard
  rw [hsum] at hbad
  omega

