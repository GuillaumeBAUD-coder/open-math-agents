import OMAReductions.R_Erdos338_erdos_338_variants_squares_R1

namespace OMA.DistinctSquares

lemma residue (a : ℕ) : a^2 % 8 = 0 ∨ a^2 % 8 = 1 ∨ a^2 % 8 = 4 := by
  have h := Nat.mod_lt a (by decide : 0 < 8)
  interval_cases he : a%8 <;> norm_num [Nat.pow_mod, he]

lemma four_div (a b c d : ℕ)
    (ha : a%8=0 ∨ a%8=1 ∨ a%8=4) (hb : b%8=0 ∨ b%8=1 ∨ b%8=4)
    (hc : c%8=0 ∨ c%8=1 ∨ c%8=4) (hd : d%8=0 ∨ d%8=1 ∨ d%8=4)
    (hs : (a+b+c+d)%8=0) : 4 ∣ a ∧ 4 ∣ b ∧ 4 ∣ c ∧ 4 ∣ d := by
  rw [Nat.add_mod (a+b+c) d, Nat.add_mod (a+b) c, Nat.add_mod a b] at hs
  have h1 := Nat.mod_mod_of_dvd a (by decide : 4 ∣ 8)
  have h2 := Nat.mod_mod_of_dvd b (by decide : 4 ∣ 8)
  have h3 := Nat.mod_mod_of_dvd c (by decide : 4 ∣ 8)
  have h4 := Nat.mod_mod_of_dvd d (by decide : 4 ∣ 8)
  simp only [Nat.dvd_iff_mod_eq_zero]
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
    rcases hc with hc | hc | hc <;> rcases hd with hd | hd | hd <;> omega

lemma list_div (l : List ℕ) (hlen : l.length ≤ 4)
    (hr : ∀ a ∈ l, a%8=0 ∨ a%8=1 ∨ a%8=4) (hz : l.sum%8=0) :
    ∀ a ∈ l, 4 ∣ a := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d,l⟩⟩⟩⟩
  · simp
  · have H := four_div a 0 0 0 (hr a (by simp)) (by simp) (by simp) (by simp)
      (by simpa using hz)
    simpa using H.1
  · have H := four_div a b 0 0 (hr a (by simp)) (hr b (by simp)) (by simp) (by simp)
      (by simpa using hz)
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact H.1
    · exact H.2.1
  · have H := four_div a b c 0 (hr a (by simp)) (hr b (by simp)) (hr c (by simp))
      (by simp) (by simpa [add_assoc] using hz)
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact H.1
    · exact H.2.1
    · exact H.2.2.1
  · have hl : l = [] := by apply List.length_eq_zero_iff.mp; simp only [List.length_cons] at hlen; omega
    subst l
    have H := four_div a b c d (hr a (by simp)) (hr b (by simp)) (hr c (by simp))
      (hr d (by simp)) (by simpa [add_assoc] using hz)
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact H.1
    · exact H.2.1
    · exact H.2.2.1
    · exact H.2.2.2

lemma finset_div (S : Finset ℕ) (hcard : S.card ≤ 4)
    (hS : ∀ a ∈ S, ∃ u : ℕ, u^2=a) (hz : (∑ a ∈ S, a)%8=0) :
    ∀ a ∈ S, 4 ∣ a := by
  have hlen : S.toList.length ≤ 4 := by simpa using hcard
  have hr : ∀ a ∈ S.toList, a%8=0 ∨ a%8=1 ∨ a%8=4 := by
    intro a ha
    obtain ⟨u,rfl⟩ := hS a (by simpa using ha)
    exact residue u
  have hzero : S.toList.sum%8=0 := by simpa using hz
  simpa only [Finset.mem_toList] using list_div S.toList hlen hr hzero

lemma no_rep (k : ℕ) : ∀ S : Finset ℕ, (∀ a ∈ S, ∃ u : ℕ, u^2=a) →
    S.card ≤ 4 → (∑ a ∈ S, a) ≠ 2*4^k := by
  induction k with
  | zero =>
    intro S hS hc he
    norm_num at he
    have hsub : S ⊆ {0,1} := by
      intro a ha
      have hle : a ≤ 2 := by
        have hh := Finset.single_le_sum (fun b (_ : b ∈ S) => Nat.zero_le b) ha
        omega
      obtain ⟨u,hu⟩ := hS a ha
      have hu1 : u ≤ 1 := by nlinarith
      interval_cases u <;> simp_all
    have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun b _ _ => Nat.zero_le b)
    norm_num at hh
    omega
  | succ k ih =>
    intro S hS hc he
    have hz : (∑ a ∈ S, a)%8=0 := by
      rw [he, pow_succ]
      have hh : 2*(4^k*4) = 8*4^k := by ring
      rw [hh]
      simp
    have hd := finset_div S hc hS hz
    let T := S.image (fun a => a/4)
    have hinj : Set.InjOn (fun a : ℕ => a/4) (S : Set ℕ) := by
      intro a ha b hb hab
      dsimp only at hab
      have h1 := Nat.div_mul_cancel (hd a ha)
      have h2 := Nat.div_mul_cancel (hd b hb)
      omega
    have hscale : (∑ a ∈ T, a)*4 = ∑ a ∈ S, a := by
      rw [Finset.sum_image hinj, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      exact Nat.div_mul_cancel (hd a ha)
    have hTsum : (∑ a ∈ T, a) = 2*4^k := by
      rw [he, pow_succ] at hscale
      omega
    have hTcard : T.card ≤ 4 := Finset.card_image_le.trans hc
    have hTsquare : ∀ a ∈ T, ∃ u : ℕ, u^2=a := by
      intro a ha
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨u,hu⟩ := hS b hb
      have htwo : 2 ∣ u := Nat.prime_two.dvd_of_dvd_pow
        ((show 2 ∣ 4 by decide).trans (hu.symm ▸ hd b hb))
      obtain ⟨v,hv⟩ := htwo
      refine ⟨v, ?_⟩
      rw [← hu, hv, show (2*v)^2=4*v^2 by ring]
      simp
    exact ih T hTsquare hTcard hTsum

end OMA.DistinctSquares

-- Step Erdos338.erdos_338.variants.squares.R1.H3: hypothesis H3 of reduction Erdos338.erdos_338.variants.squares.R1
-- Credit: @DeepDuke
-- H3 := ¬ HasRestrictedOrder (Set.range fun k : ℕ ↦ k ^ 2) 4

theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_squares_R1.H3 := by
  intro h
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp h
  have hpow : N < 4^N := Nat.lt_pow_self (by decide : 1 < 4)
  obtain ⟨S,hS,hcard,hsum⟩ := hN (2*4^N) (by omega)
  exact OMA.DistinctSquares.no_rep N S hS hcard hsum

