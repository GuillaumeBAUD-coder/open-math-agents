import OMAReductions.R_Green4_large_green_4_R1
import Mathlib

/-!
# Proof of `Green4.large_green_4.R1.H3`

Elementary combinatorial stability-to-exactness upgrade for large product-free
subsets of the alternating groups `A_n` (Keevash–Lifshitz–Minzer 2022,
Theorem 1.1 / Section 6):

Given a product-free subset `S ⊆ A_n` with `|S| ≥ |extremalFamily x I|` for all
`x, I` and `|S \ extremalFamily x I| < n^(-33/50) |A_n|` (up to inversion):
1. **Exact `r`-point fibre & avoidance counting on `A_n`:** Every partial injection
   on `r ≤ n - 2` points has exactly `(n - r)! / 2` even completions. This gives
   exact 1-, 2-, 3-point fibre densities, an exact formula for `|extremalFamily x I|`,
   and a uniform positive avoidance constant `c > 0` for sets of size `O(√n)`.
2. **Thresholded target set `J`:** No element of `S` fixes `x`. Defining
   `J = {j : Pr(π ∈ S | π(x) = j) ≥ δ}` gives `x ∉ J`, `a √n ≤ |J| ≤ b √n`,
   `H = μ(F \ S) = o(|J| / n)`, and `H ≤ E = μ(S \ F)` where `F = extremalFamily x J`.
3. **Inside-edge bound (`E_in ≤ H / 4`):** Splitting `J` into good (`h_i ≤ η`) and
   bad (`t ≤ n H / η`) indices, both-good edges are impossible, one-good edges are
   bounded by an elementary second-moment / Chebyshev variance bound for uniform
   subset sampling without replacement, and both-bad edges cost `t^2 |J| / (n(n-1))`.
4. **Outside-target bound (`E_out ≤ H / 2`):** A two-point-fibre bijection
   `β ↦ σ β⁻¹` yields the dichotomy `A(i, k, y) ∨ B(i, σ⁻¹ k)`. Bonferroni bounds
   exceptional targets `|Y| ≤ 24 H n^2 / (c m^2)` (contributing `≤ H / 4`), while
   non-exceptional targets force `≥ ⌈m / 2⌉` hits in `Z_0` (`|Z_0| ≤ 6 H n(n-1) / (c m)`),
   contributing `≤ H / 4`.
5. **Conclusion:** `E ≤ (3 / 4) H` and `H ≤ E` force `H = E = 0`, hence `S ⊆ F`.
-/

namespace OMA.P_Green4_H3

open scoped BigOperators
open Filter Finset Green4 Set

/- ### Section 1: Exact `r`-Point Fibre and Avoidance Counting on `A_n` -/

section Counting

variable {n : ℕ}

private abbrev Alt (n : ℕ) := alternatingGroup (Fin n)

private lemma descFactorial_mono {a b r : ℕ} (h : a ≤ b) : a.descFactorial r ≤ b.descFactorial r := by
  rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range]
  exact Finset.prod_le_prod' fun i _ => by omega

private lemma card_alt (hn : 2 ≤ n) : 2 * Fintype.card (Alt n) = n.factorial := by
  have hsurj : Function.Surjective (Equiv.Perm.sign : Equiv.Perm (Fin n) →* ℤˣ) := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one _⟩
    · refine ⟨Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩, ?_⟩
      exact Equiv.Perm.sign_swap (by simp [Fin.ext_iff])
  have hidx : (alternatingGroup (Fin n)).index = 2 := by
    change (Equiv.Perm.sign : Equiv.Perm (Fin n) →* ℤˣ).ker.index = 2
    rw [Subgroup.index_ker]
    have hrange : (Equiv.Perm.sign : Equiv.Perm (Fin n) →* ℤˣ).range = ⊤ :=
      MonoidHom.range_eq_top.mpr hsurj
    rw [hrange]
    simp [Nat.card_eq_fintype_card]
  have hmul := Subgroup.card_mul_index (alternatingGroup (Fin n))
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin, hidx] at hmul
  dsimp only [Alt]
  omega

private lemma card_alt_pos (hn : 2 ≤ n) : 0 < Fintype.card (Alt n) := by
  have h := card_alt hn
  have hf : 2 ≤ n.factorial := by
    calc 2 = (2 : ℕ).factorial := by decide
      _ ≤ n.factorial := Nat.factorial_le hn
  omega

/-- Exact count of permutations in `S_n` agreeing with an injection `f` on a finset `U`. -/
private lemma card_perm_agree_on (U : Finset (Fin n)) (f : Fin n → Fin n)
    (hf : Set.InjOn f (U : Set (Fin n))) :
    (Finset.univ.filter fun π : Equiv.Perm (Fin n) => ∀ u ∈ U, π u = f u).card =
      (n - U.card).factorial := by
  classical
  let V : Finset (Fin n) := U.image f
  have hUV : U.card = V.card := (Finset.card_image_of_injOn hf).symm
  have hcompl : (Finset.univ \ U).card = (Finset.univ \ V).card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_sdiff, Finset.inter_univ, hUV]
  have hcard_c : Fintype.card {x : Fin n // x ∉ U} = Fintype.card {y : Fin n // y ∉ V} := by
    have h1 : Fintype.card {x : Fin n // x ∉ U} = (Finset.univ \ U).card := by
      rw [← Fintype.card_coe]; apply Fintype.card_congr
      exact { toFun := fun x => ⟨x.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, x.2⟩⟩
              invFun := fun x => ⟨x.1, (Finset.mem_sdiff.mp x.2).2⟩
              left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    have h2 : Fintype.card {y : Fin n // y ∉ V} = (Finset.univ \ V).card := by
      rw [← Fintype.card_coe]; apply Fintype.card_congr
      exact { toFun := fun x => ⟨x.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, x.2⟩⟩
              invFun := fun x => ⟨x.1, (Finset.mem_sdiff.mp x.2).2⟩
              left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    rw [h1, h2, hcompl]
  let e_c : {x : Fin n // x ∉ U} ≃ {y : Fin n // y ∉ V} := Fintype.equivOfCardEq hcard_c
  let e_U : {x : Fin n // x ∈ U} ≃ {y : Fin n // y ∈ V} :=
    Equiv.ofBijective (fun x => ⟨f x.1, Finset.mem_image_of_mem f x.2⟩) ⟨
      fun a b h => Subtype.ext (hf a.2 b.2 (congrArg Subtype.val h)),
      fun y => by
        obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp y.2
        exact ⟨⟨u, hu⟩, Subtype.ext heq⟩⟩
  let π₀ : Equiv.Perm (Fin n) :=
    (Equiv.sumCompl (· ∈ U)).symm.trans ((Equiv.sumCongr e_U e_c).trans (Equiv.sumCompl (· ∈ V)))
  have hπ₀ : ∀ u ∈ U, π₀ u = f u := by
    intro u hu
    simp [π₀, Equiv.sumCompl_symm_apply_of_pos hu, e_U]
    rfl
  let S := Finset.univ.filter fun π : Equiv.Perm (Fin n) => ∀ u ∈ U, π u = f u
  let H := Finset.univ.filter fun τ : Equiv.Perm (Fin n) => ∀ u ∈ U, τ u = u
  have hSH : S.card = H.card := by
    refine Finset.card_bij (fun π _ => π₀⁻¹ * π) ?_ ?_ ?_
    · intro π hπ
      rw [Finset.mem_filter] at hπ ⊢
      refine ⟨Finset.mem_univ _, fun u hu => ?_⟩
      change π₀⁻¹ (π u) = u
      rw [hπ.2 u hu, ← hπ₀ u hu]
      exact Equiv.symm_apply_apply π₀ u
    · intro π₁ _ π₂ _ h; exact mul_left_cancel h
    · intro τ hτ
      rw [Finset.mem_filter] at hτ
      refine ⟨π₀ * τ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u hu => ?_⟩, by simp⟩
      change π₀ (τ u) = f u
      rw [hτ.2 u hu, hπ₀ u hu]
  have hH : H.card = Fintype.card (Equiv.Perm {x : Fin n // x ∉ U}) := by
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun τ hτ => Equiv.ofBijective
        (fun x : {x : Fin n // x ∉ U} => ⟨τ x.1, fun hxU => x.2 (by
          have h1 : τ (τ x.1) = τ x.1 := (Finset.mem_filter.mp hτ).2 (τ x.1) hxU
          have h2 : τ x.1 = x.1 := τ.injective h1
          rwa [← h2])⟩)
        ⟨fun a b h => Subtype.ext (τ.injective (congrArg Subtype.val h)),
         fun y => ⟨⟨τ.symm y.1, fun hxU => y.2 (by
           have h1 : τ (τ.symm y.1) = τ.symm y.1 := (Finset.mem_filter.mp hτ).2 (τ.symm y.1) hxU
           have h2 : y.1 = τ.symm y.1 := by simpa using h1
           rwa [h2])⟩, Subtype.ext (by simp)⟩⟩) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro τ₁ hτ₁ τ₂ hτ₂ heq
      refine Equiv.ext fun x => ?_
      by_cases hx : x ∈ U
      · rw [(Finset.mem_filter.mp hτ₁).2 x hx, (Finset.mem_filter.mp hτ₂).2 x hx]
      · exact congrArg (fun σ => (σ ⟨x, hx⟩).1) heq
    · intro σ _
      let τ : Equiv.Perm (Fin n) :=
        (Equiv.sumCompl (· ∈ U)).symm.trans ((Equiv.sumCongr (Equiv.refl _) σ).trans (Equiv.sumCompl (· ∈ U)))
      refine ⟨τ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u hu => ?_⟩, ?_⟩
      · simp [τ, Equiv.sumCompl_symm_apply_of_pos hu]
      · ext ⟨x, hx⟩
        simp [τ]
  rw [hSH, hH, Fintype.card_perm]
  have hc : Fintype.card {x : Fin n // x ∉ U} = n - U.card := by
    have h1 : Fintype.card {x : Fin n // x ∉ U} = (Finset.univ \ U).card := by
      rw [← Fintype.card_coe]; apply Fintype.card_congr
      exact { toFun := fun x => ⟨x.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, x.2⟩⟩
              invFun := fun x => ⟨x.1, (Finset.mem_sdiff.mp x.2).2⟩
              left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    rw [h1, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  rw [hc]

/-- Exact count of even permutations in `A_n` agreeing with an injection `f` on `U` (`|U| + 2 ≤ n`). -/
private lemma card_alt_agree_on (U : Finset (Fin n)) (hU : U.card + 2 ≤ n)
    (f : Fin n → Fin n) (hf : Set.InjOn f (U : Set (Fin n))) :
    2 * (Finset.univ.filter fun π : Alt n => ∀ u ∈ U, π.1 u = f u).card =
      (n - U.card).factorial := by
  classical
  let S := Finset.univ.filter fun π : Equiv.Perm (Fin n) => ∀ u ∈ U, π u = f u
  let S_even := S.filter fun π => Equiv.Perm.sign π = 1
  let S_odd := S.filter fun π => Equiv.Perm.sign π = -1
  have hA : (Finset.univ.filter fun π : Alt n => ∀ u ∈ U, π.1 u = f u).card = S_even.card := by
    refine Finset.card_bij (fun π _ => π.1) ?_ ?_ ?_
    · intro π hπ
      rw [Finset.mem_filter] at hπ
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hπ.2⟩,
        Equiv.Perm.mem_alternatingGroup.mp π.2⟩
    · intro π₁ _ π₂ _ h; exact Subtype.ext h
    · intro π hπ
      obtain ⟨hπS, hsign⟩ := Finset.mem_filter.mp hπ
      exact ⟨⟨π, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hπS).2⟩, rfl⟩
  have hcompl_card : 2 ≤ (Finset.univ \ U).card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]; omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (Finset.univ \ U).card)
  have haU : a ∉ U := (Finset.mem_sdiff.mp ha).2
  have hbU : b ∉ U := (Finset.mem_sdiff.mp hb).2
  let t : Equiv.Perm (Fin n) := Equiv.swap a b
  have ht_sign : Equiv.Perm.sign t = -1 := Equiv.Perm.sign_swap hab
  have heq_eo : S_even.card = S_odd.card := by
    refine Finset.card_bij (fun π _ => π * t) ?_ ?_ ?_
    · intro π hπ
      obtain ⟨hπS, hsign⟩ := Finset.mem_filter.mp hπ
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u hu => ?_⟩, ?_⟩
      · change π (t u) = f u
        have hua : u ≠ a := fun h => haU (h ▸ hu)
        have hub : u ≠ b := fun h => hbU (h ▸ hu)
        rw [Equiv.swap_apply_of_ne_of_ne hua hub]
        exact (Finset.mem_filter.mp hπS).2 u hu
      · rw [map_mul, hsign, ht_sign, one_mul]
    · intro π₁ _ π₂ _ h; exact mul_right_cancel h
    · intro π hπ
      obtain ⟨hπS, hsign⟩ := Finset.mem_filter.mp hπ
      refine ⟨π * t, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u hu => ?_⟩, ?_⟩, ?_⟩
      · change π (t u) = f u
        have hua : u ≠ a := fun h => haU (h ▸ hu)
        have hub : u ≠ b := fun h => hbU (h ▸ hu)
        rw [Equiv.swap_apply_of_ne_of_ne hua hub]
        exact (Finset.mem_filter.mp hπS).2 u hu
      · rw [map_mul, hsign, ht_sign]; decide
      · simp [mul_assoc, t]
  have hpart : S_even.card + S_odd.card = S.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext π
      simp only [S_even, S_odd, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hs | hs
        · exact Or.inl ⟨h, hs⟩
        · exact Or.inr ⟨h, hs⟩
    · rw [Finset.disjoint_filter]; intro π _ h1 h2; rw [h1] at h2; exact absurd h2 (by decide)
  rw [hA]
  have hS : S.card = (n - U.card).factorial := card_perm_agree_on U f hf
  omega

/-- Normalized uniform measure on `A_n`. -/
private noncomputable def μ (S : Finset (Alt n)) : ℝ :=
  (S.card : ℝ) / (Fintype.card (Alt n) : ℝ)

private lemma μ_nonneg (S : Finset (Alt n)) : 0 ≤ μ S := by
  unfold μ; positivity

private lemma μ_le_one (S : Finset (Alt n)) : μ S ≤ 1 := by
  unfold μ
  rcases Nat.eq_zero_or_pos (Fintype.card (Alt n)) with h0 | hpos
  · rw [h0]; simp
  · rw [div_le_one (by exact_mod_cast hpos)]
    exact_mod_cast (Finset.card_le_univ S)

private lemma μ_mono {S T : Finset (Alt n)} (h : S ⊆ T) : μ S ≤ μ T := by
  unfold μ
  exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card h) (Nat.cast_nonneg _)

private lemma μ_union_le (S T : Finset (Alt n)) : μ (S ∪ T) ≤ μ S + μ T := by
  unfold μ
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_union_le S T) (Nat.cast_nonneg _)

private lemma μ_biUnion_le {ι : Type*} [DecidableEq ι] (I : Finset ι) (f : ι → Finset (Alt n)) :
    μ (I.biUnion f) ≤ ∑ i ∈ I, μ (f i) := by
  unfold μ
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_biUnion_le) (Nat.cast_nonneg _)

private lemma μ_sum_disjoint {ι : Type*} (I : Finset ι) (f : ι → Finset (Alt n))
    (hdisj : (I : Set ι).PairwiseDisjoint f) :
    μ (I.biUnion f) = ∑ i ∈ I, μ (f i) := by
  unfold μ
  rw [Finset.card_biUnion hdisj, Nat.cast_sum, Finset.sum_div]

private lemma μ_image_mul_right (S : Finset (Alt n)) (σ : Alt n) :
    μ (S.image (· * σ)) = μ S := by
  unfold μ
  rw [Finset.card_image_of_injective _ (mul_left_injective σ)]

private lemma μ_image_mul_left (S : Finset (Alt n)) (σ : Alt n) :
    μ (S.image (σ * ·)) = μ S := by
  unfold μ
  rw [Finset.card_image_of_injective _ (mul_right_injective σ)]

private lemma μ_sdiff_le (S T : Finset (Alt n)) : μ (S \ T) = μ S - μ (S ∩ T) := by
  unfold μ
  have h := Finset.card_sdiff_add_card_inter S T
  have hR : ((S \ T).card : ℝ) + ((S ∩ T).card : ℝ) = (S.card : ℝ) := by exact_mod_cast h
  rw [← sub_div, show (S.card : ℝ) - ((S ∩ T).card : ℝ) = ((S \ T).card : ℝ) by linarith]

private lemma μ_agree_on (hn : 2 ≤ n) (U : Finset (Fin n)) (hU : U.card + 2 ≤ n)
    (f : Fin n → Fin n) (hf : Set.InjOn f (U : Set (Fin n))) :
    μ (Finset.univ.filter fun π : Alt n => ∀ u ∈ U, π.1 u = f u) =
      ((n - U.card).factorial : ℝ) / (n.factorial : ℝ) := by
  unfold μ
  have h1 := card_alt_agree_on U hU f hf
  have h2 := card_alt hn
  have h1R : 2 * ((Finset.univ.filter fun π : Alt n => ∀ u ∈ U, π.1 u = f u).card : ℝ) =
      ((n - U.card).factorial : ℝ) := by exact_mod_cast h1
  have h2R : 2 * (Fintype.card (Alt n) : ℝ) = (n.factorial : ℝ) := by exact_mod_cast h2
  have hpos : (0 : ℝ) < (Fintype.card (Alt n) : ℝ) := by exact_mod_cast card_alt_pos hn
  have hfac_pos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  rw [div_eq_div_iff hpos.ne' hfac_pos.ne']
  nlinarith

private lemma μ_fiber1 (hn : 3 ≤ n) (x y : Fin n) :
    μ (Finset.univ.filter fun π : Alt n => π.1 x = y) = 1 / (n : ℝ) := by
  have h := μ_agree_on (by omega) {x} (by simp; omega) (fun _ => y) (by simp)
  have hfilt : (Finset.univ.filter fun π : Alt n => ∀ u ∈ ({x} : Finset (Fin n)), π.1 u = y) =
      (Finset.univ.filter fun π : Alt n => π.1 x = y) := by
    ext π; simp
  rw [hfilt] at h
  rw [h, Finset.card_singleton]
  have hfac : n.factorial = n * (n - 1).factorial := by
    cases n with
    | zero => omega
    | succ m => simp [Nat.factorial_succ]
  rw [hfac, Nat.cast_mul]
  have h1 : (0 : ℝ) < ((n - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (n - 1)
  have h2 : (0 : ℝ) < (n : ℝ) := by positivity
  field_simp

private lemma μ_fiber2 (hn : 4 ≤ n) {x₁ x₂ y₁ y₂ : Fin n} (hx : x₁ ≠ x₂) (hy : y₁ ≠ y₂) :
    μ (Finset.univ.filter fun π : Alt n => π.1 x₁ = y₁ ∧ π.1 x₂ = y₂) =
      1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
  classical
  let f : Fin n → Fin n := fun u => if u = x₁ then y₁ else y₂
  have hf : Set.InjOn f (({x₁, x₂} : Finset (Fin n)) : Set (Fin n)) := by
    intro a ha b hb hab
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · simp [f, hx.symm] at hab; exact absurd hab hy
    · simp [f, hx.symm] at hab; exact absurd hab.symm hy
    · rfl
  have h := μ_agree_on (by omega) {x₁, x₂} (by rw [Finset.card_pair hx]; omega) f hf
  have hfilt : (Finset.univ.filter fun π : Alt n => ∀ u ∈ ({x₁, x₂} : Finset (Fin n)), π.1 u = f u) =
      (Finset.univ.filter fun π : Alt n => π.1 x₁ = y₁ ∧ π.1 x₂ = y₂) := by
    ext π; simp [f, hx.symm]
  rw [hfilt, Finset.card_pair hx] at h
  rw [h]
  have hfac : n.factorial = n * (n - 1) * (n - 2).factorial := by
    rcases Nat.exists_eq_add_of_le hn with ⟨m, rfl⟩
    have : (4 + m) - 1 = 3 + m := by omega
    have : (4 + m) - 2 = 2 + m := by omega
    simp only [‹(4 + m) - 1 = 3 + m›, ‹(4 + m) - 2 = 2 + m›]
    rw [show 4 + m = (3 + m) + 1 by omega, Nat.factorial_succ,
      show 3 + m = (2 + m) + 1 by omega, Nat.factorial_succ]
    ring
  rw [hfac]
  push_cast
  have hsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [hsub]
  have h1 : (0 : ℝ) < ((n - 2).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (n - 2)
  have h2 : (0 : ℝ) < (n : ℝ) := by positivity
  have h3 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  field_simp

private lemma μ_fiber3 (hn : 5 ≤ n) {x₁ x₂ x₃ y₁ y₂ y₃ : Fin n}
    (hx12 : x₁ ≠ x₂) (hx13 : x₁ ≠ x₃) (hx23 : x₂ ≠ x₃)
    (hy12 : y₁ ≠ y₂) (hy13 : y₁ ≠ y₃) (hy23 : y₂ ≠ y₃) :
    μ (Finset.univ.filter fun π : Alt n => π.1 x₁ = y₁ ∧ π.1 x₂ = y₂ ∧ π.1 x₃ = y₃) =
      1 / ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2)) := by
  classical
  let U : Finset (Fin n) := {x₁, x₂, x₃}
  have hUcard : U.card = 3 := by simp [U, hx12, hx13, hx23]
  let f : Fin n → Fin n := fun u => if u = x₁ then y₁ else if u = x₂ then y₂ else y₃
  have hf : Set.InjOn f (U : Set (Fin n)) := by
    intro a ha b hb hab
    simp only [U, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      simp [f, hx12.symm, hx13.symm, hx23.symm] at hab
    all_goals first | rfl | exact absurd hab hy12 | exact absurd hab.symm hy12 |
      exact absurd hab hy13 | exact absurd hab.symm hy13 | exact absurd hab hy23 | exact absurd hab.symm hy23
  have h := μ_agree_on (by omega) U (by rw [hUcard]; omega) f hf
  have hfilt : (Finset.univ.filter fun π : Alt n => ∀ u ∈ U, π.1 u = f u) =
      (Finset.univ.filter fun π : Alt n => π.1 x₁ = y₁ ∧ π.1 x₂ = y₂ ∧ π.1 x₃ = y₃) := by
    ext π; simp [U, f, hx12.symm, hx13.symm, hx23.symm]
  rw [hfilt, hUcard] at h
  rw [h]
  have hfac : n.factorial = n * (n - 1) * (n - 2) * (n - 3).factorial := by
    rcases Nat.exists_eq_add_of_le hn with ⟨m, rfl⟩
    rw [show 5 + m - 1 = 4 + m by omega, show 5 + m - 2 = 3 + m by omega, show 5 + m - 3 = 2 + m by omega]
    rw [show 5 + m = (4 + m) + 1 by omega, Nat.factorial_succ,
      show 4 + m = (3 + m) + 1 by omega, Nat.factorial_succ,
      show 3 + m = (2 + m) + 1 by omega, Nat.factorial_succ]
    ring
  rw [hfac]; push_cast
  have hsub1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hsub2 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; simp
  rw [hsub1, hsub2]
  have h1 : (0 : ℝ) < ((n - 3).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (n - 3)
  have h2 : (0 : ℝ) < (n : ℝ) := by positivity
  have h3 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h4 : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  field_simp

/-- Exact count of even permutations agreeing with `f` on `U` and mapping `A` (disjoint from `U`) outside `B`. -/
private lemma card_alt_agree_and_avoid (U A B : Finset (Fin n)) (hdisj : Disjoint U A)
    (hUA : U.card + A.card + 2 ≤ n) (f : Fin n → Fin n) (hf : Set.InjOn f (U : Set (Fin n))) :
    2 * (Finset.univ.filter fun π : Alt n => (∀ u ∈ U, π.1 u = f u) ∧ ∀ a ∈ A, π.1 a ∉ B).card =
      ((Finset.univ \ (U.image f ∪ B)).card.descFactorial A.card) * (n - U.card - A.card).factorial := by
  classical
  induction A using Finset.induction_on generalizing U f with
  | empty =>
    simp only [Finset.notMem_empty, false_implies, implies_true, and_true, Finset.card_empty,
      Nat.descFactorial_zero, one_mul, Nat.sub_zero]
    exact card_alt_agree_on U (by simpa using hUA) f hf
  | @insert a A' haA ih =>
    have haU : a ∉ U := fun h => Finset.disjoint_left.mp hdisj h (Finset.mem_insert_self a A')
    have hdisj' : Disjoint (insert a U) A' := by
      rw [Finset.disjoint_insert_left]
      exact ⟨haA, Disjoint.mono_right (Finset.subset_insert a A') hdisj⟩
    have hcard_ins : (insert a U).card = U.card + 1 := Finset.card_insert_of_notMem haU
    have hcard_A : (insert a A').card = A'.card + 1 := Finset.card_insert_of_notMem haA
    let R := Finset.univ \ (U.image f ∪ B)
    let S := Finset.univ.filter fun π : Alt n => (∀ u ∈ U, π.1 u = f u) ∧ ∀ x ∈ insert a A', π.1 x ∉ B
    have hpart : S = R.biUnion fun y =>
        Finset.univ.filter fun π : Alt n =>
          (∀ u ∈ insert a U, π.1 u = Function.update f a y u) ∧ ∀ x ∈ A', π.1 x ∉ B := by
      ext π
      simp only [S, R, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_sdiff, Finset.mem_union, Finset.mem_image, not_or]
      constructor
      · rintro ⟨hU, hA⟩
        refine ⟨π.1 a, ⟨?_, hA a (Finset.mem_insert_self a A')⟩, ?_, fun x hx => hA x (Finset.mem_insert_of_mem hx)⟩
        · rintro ⟨u, hu, heq⟩
          have : π.1 u = π.1 a := (hU u hu).trans heq
          exact haU (π.1.injective this ▸ hu)
        · intro u hu
          rcases Finset.mem_insert.mp hu with rfl | huU
          · simp
          · have hua : u ≠ a := fun h => haU (h ▸ huU)
            rw [Function.update_of_ne hua]; exact hU u huU
      · rintro ⟨y, ⟨hyf, hyB⟩, hU, hA⟩
        have hπa : π.1 a = y := by simpa using hU a (Finset.mem_insert_self a U)
        refine ⟨fun u hu => ?_, fun x hx => ?_⟩
        · have := hU u (Finset.mem_insert_of_mem hu)
          have hua : u ≠ a := fun h => haU (h ▸ hu)
          rwa [Function.update_of_ne hua] at this
        · rcases Finset.mem_insert.mp hx with rfl | hx'
          · rwa [hπa]
          · exact hA x hx'
    have hdisj_y : (R : Set (Fin n)).PairwiseDisjoint fun y =>
        Finset.univ.filter fun π : Alt n =>
          (∀ u ∈ insert a U, π.1 u = Function.update f a y u) ∧ ∀ x ∈ A', π.1 x ∉ B := by
      intro y₁ _ y₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro π h1 h2
      have e1 : π.1 a = y₁ := by simpa using (Finset.mem_filter.mp h1).2.1 a (Finset.mem_insert_self a U)
      have e2 : π.1 a = y₂ := by simpa using (Finset.mem_filter.mp h2).2.1 a (Finset.mem_insert_self a U)
      exact hne (e1.symm.trans e2)
    have hcard_S : 2 * S.card = ∑ y ∈ R, 2 * (Finset.univ.filter fun π : Alt n =>
        (∀ u ∈ insert a U, π.1 u = Function.update f a y u) ∧ ∀ x ∈ A', π.1 x ∉ B).card := by
      rw [hpart, Finset.card_biUnion hdisj_y, Finset.mul_sum]
    rw [hcard_S]
    have hterm : ∀ y ∈ R, 2 * (Finset.univ.filter fun π : Alt n =>
        (∀ u ∈ insert a U, π.1 u = Function.update f a y u) ∧ ∀ x ∈ A', π.1 x ∉ B).card =
        ((R.card - 1).descFactorial A'.card) * (n - U.card - (A'.card + 1)).factorial := by
      intro y hy
      have hy_not_img : y ∉ U.image f := fun h => (Finset.mem_sdiff.mp hy).2 (Finset.mem_union_left B h)
      have hy_not_B : y ∉ B := fun h => (Finset.mem_sdiff.mp hy).2 (Finset.mem_union_right (U.image f) h)
      have hfinj : Set.InjOn (Function.update f a y) ((insert a U : Finset (Fin n)) : Set (Fin n)) := by
        intro u hu v hv huv
        simp only [Finset.coe_insert, Set.mem_insert_iff] at hu hv
        by_cases hua : u = a
        · by_cases hva : v = a
          · exact hua.trans hva.symm
          · have hvU : v ∈ U := hv.resolve_left hva
            rw [hua, Function.update_self, Function.update_of_ne hva] at huv
            exact absurd (huv ▸ Finset.mem_image_of_mem f hvU) hy_not_img
        · have huU : u ∈ U := hu.resolve_left hua
          by_cases hva : v = a
          · rw [hva, Function.update_self, Function.update_of_ne hua] at huv
            exact absurd (huv.symm ▸ Finset.mem_image_of_mem f huU) hy_not_img
          · have hvU : v ∈ U := hv.resolve_left hva
            rw [Function.update_of_ne hua, Function.update_of_ne hva] at huv
            exact hf huU hvU huv
      have hrec := ih (insert a U) hdisj' (by omega) (Function.update f a y) hfinj
      have himg_eq : (insert a U).image (Function.update f a y) = insert y (U.image f) := by
        ext z
        simp only [Finset.mem_image, Finset.mem_insert]
        constructor
        · rintro ⟨u, hu, rfl⟩
          rcases hu with rfl | huU
          · exact Or.inl (by simp)
          · have hua : u ≠ a := fun h => haU (h ▸ huU)
            exact Or.inr ⟨u, huU, by rw [Function.update_of_ne hua]⟩
        · intro hz
          rcases hz with rfl | ⟨u, huU, rfl⟩
          · exact ⟨a, Or.inl rfl, by simp⟩
          · have hua : u ≠ a := fun h => haU (h ▸ huU)
            exact ⟨u, Or.inr huU, by rw [Function.update_of_ne hua]⟩
      have hR' : Finset.univ \ ((insert a U).image (Function.update f a y) ∪ B) = R.erase y := by
        ext z
        simp only [R, himg_eq, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
          Finset.mem_insert, Finset.mem_erase, not_or]
        tauto
      rw [hrec, hR', Finset.card_erase_of_mem hy, hcard_ins, show n - (U.card + 1) - A'.card = n - U.card - (A'.card + 1) by omega]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, hcard_A, ← mul_assoc]
    congr 1
    rcases Nat.eq_zero_or_pos R.card with h0 | hpos
    · rw [h0]; simp
    · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      rw [hm]; simp only [Nat.succ_sub_one, Nat.succ_descFactorial_succ]

private lemma card_extremalFamily_eq (x : Fin n) (I : Finset (Fin n)) :
    (extremalFamily x (I : Set (Fin n))).ncard =
      (Finset.univ.filter fun π : Alt n => π.1 x ∈ I ∧ ∀ a ∈ I, π.1 a ∉ I).card := by
  rw [← Set.ncard_coe_finset]
  congr 1; ext π
  simp only [extremalFamily, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
    true_and, Set.disjoint_left, Set.mem_image]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun a ha => h2 ⟨a, ha, rfl⟩⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun _ ⟨a, ha, heq⟩ => heq ▸ h2 a ha⟩

private lemma μ_extremalFamily_exact (hn : 4 ≤ n) (x : Fin n) (I : Finset (Fin n))
    (hxI : x ∉ I) (hI : I.card + 3 ≤ n) :
    μ (Finset.univ.filter fun π : Alt n => π.1 x ∈ I ∧ ∀ a ∈ I, π.1 a ∉ I) =
      (I.card : ℝ) * (((n - I.card).descFactorial I.card : ℝ) * ((n - 1 - I.card).factorial : ℝ)) /
        (n.factorial : ℝ) := by
  classical
  let F := Finset.univ.filter fun π : Alt n => π.1 x ∈ I ∧ ∀ a ∈ I, π.1 a ∉ I
  have hpart : F = I.biUnion fun y =>
      Finset.univ.filter fun π : Alt n => (∀ u ∈ ({x} : Finset (Fin n)), π.1 u = y) ∧ ∀ a ∈ I, π.1 a ∉ I := by
    ext π; simp [F]
  have hdisj_y : (I : Set (Fin n)).PairwiseDisjoint fun y =>
      Finset.univ.filter fun π : Alt n => (∀ u ∈ ({x} : Finset (Fin n)), π.1 u = y) ∧ ∀ a ∈ I, π.1 a ∉ I := by
    intro y₁ _ y₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro π h1 h2
    have e1 : π.1 x = y₁ := (Finset.mem_filter.mp h1).2.1 x (Finset.mem_singleton_self x)
    have e2 : π.1 x = y₂ := (Finset.mem_filter.mp h2).2.1 x (Finset.mem_singleton_self x)
    exact hne (e1.symm.trans e2)
  have hcard : 2 * F.card = I.card * ((n - I.card).descFactorial I.card * (n - 1 - I.card).factorial) := by
    rw [hpart, Finset.card_biUnion hdisj_y, Finset.mul_sum]
    have hterm : ∀ y ∈ I, 2 * (Finset.univ.filter fun π : Alt n =>
        (∀ u ∈ ({x} : Finset (Fin n)), π.1 u = y) ∧ ∀ a ∈ I, π.1 a ∉ I).card =
        (n - I.card).descFactorial I.card * (n - 1 - I.card).factorial := by
      intro y hy
      have hc := card_alt_agree_and_avoid {x} I I (Finset.disjoint_singleton_left.mpr hxI)
        (by simp; omega) (fun _ => y) (by simp)
      have hunion : ({x} : Finset (Fin n)).image (fun _ => y) ∪ I = I := by
        ext z; simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton, exists_eq_left]
        exact ⟨fun h => h.elim (fun e => e ▸ hy) id, Or.inr⟩
      rw [hunion, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
        Finset.card_singleton] at hc
      exact hc
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]
  unfold μ
  have h1R : 2 * (F.card : ℝ) =
      (I.card : ℝ) * (((n - I.card).descFactorial I.card : ℝ) * ((n - 1 - I.card).factorial : ℝ)) := by
    exact_mod_cast hcard
  have h2R : 2 * (Fintype.card (Alt n) : ℝ) = (n.factorial : ℝ) := by
    exact_mod_cast card_alt (by omega)
  have hpos : (0 : ℝ) < (Fintype.card (Alt n) : ℝ) := by exact_mod_cast card_alt_pos (by omega)
  have hfac_pos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  change (F.card : ℝ) / (Fintype.card (Alt n) : ℝ) = _
  rw [div_eq_div_iff hpos.ne' hfac_pos.ne']
  nlinarith

/-- Elementary exponential lower bound for falling factorial ratios:
if `2 * (k + r) ≤ m` and `0 < m`, then `((m - k).descFactorial r : ℝ) / (m.descFactorial r : ℝ) ≥ exp(-4 * k * r / m)`. -/
private lemma descFactorial_ratio_ge_exp {m k r : ℕ} (hm : 0 < m) (hkr : 4 * k + 2 * r ≤ m) :
    Real.exp (-4 * (k : ℝ) * (r : ℝ) / (m : ℝ)) ≤
      ((m - k).descFactorial r : ℝ) / (m.descFactorial r : ℝ) := by
  have hprod : ∀ j, j ≤ r →
      Real.exp (-4 * (k : ℝ) * (j : ℝ) / (m : ℝ)) ≤
        ((m - k).descFactorial j : ℝ) / (m.descFactorial j : ℝ) := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      have hj' : j < r := by omega
      have hih := ih (by omega)
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_mul, mul_div_mul_comm]
      have hden_pos : (0 : ℝ) < ((m - j : ℕ) : ℝ) := by
        have : 0 < m - j := by omega
        exact_mod_cast this
      have hstep : Real.exp (-4 * (k : ℝ) / (m : ℝ)) ≤ ((m - k - j : ℕ) : ℝ) / ((m - j : ℕ) : ℝ) := by
        have hsub : ((m - k - j : ℕ) : ℝ) / ((m - j : ℕ) : ℝ) = 1 - (k : ℝ) / ((m - j : ℕ) : ℝ) := by
          have : m - k - j + k = m - j := by omega
          have hR : ((m - k - j : ℕ) : ℝ) + (k : ℝ) = ((m - j : ℕ) : ℝ) := by exact_mod_cast this
          field_simp; linarith
        rw [hsub]
        have hmj : (m : ℝ) / 2 ≤ ((m - j : ℕ) : ℝ) := by
          have : m ≤ 2 * (m - j) := by omega
          have hR : (m : ℝ) ≤ 2 * ((m - j : ℕ) : ℝ) := by exact_mod_cast this
          linarith
        have h1 : 1 - (k : ℝ) / ((m - j : ℕ) : ℝ) ≥ 1 - 2 * (k : ℝ) / (m : ℝ) := by
          have hdiv : (k : ℝ) / ((m - j : ℕ) : ℝ) ≤ (k : ℝ) / ((m : ℝ) / 2) :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg k) (by positivity) hmj
          have : (k : ℝ) / ((m : ℝ) / 2) = 2 * (k : ℝ) / (m : ℝ) := by ring
          linarith
        have h2 : Real.exp (-4 * (k : ℝ) / (m : ℝ)) ≤ 1 - 2 * (k : ℝ) / (m : ℝ) := by
          have hx : 0 ≤ 2 * (k : ℝ) / (m : ℝ) := by positivity
          have hx1 : 2 * (k : ℝ) / (m : ℝ) ≤ 1 / 2 := by
            have : 4 * k ≤ m := by omega
            have hR : 4 * (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast this
            rw [div_le_iff₀ (by exact_mod_cast hm)]; linarith
          have h4 : 1 + 4 * (k : ℝ) / (m : ℝ) ≤ Real.exp (4 * (k : ℝ) / (m : ℝ)) := by
            linarith [Real.add_one_le_exp (4 * (k : ℝ) / (m : ℝ))]
          have hmul : 1 ≤ (1 - 2 * (k : ℝ) / (m : ℝ)) * Real.exp (4 * (k : ℝ) / (m : ℝ)) := by
            have h1x : 0 ≤ 1 - 2 * (k : ℝ) / (m : ℝ) := by linarith
            have h2x : 4 * (k : ℝ) / (m : ℝ) = 2 * (2 * (k : ℝ) / (m : ℝ)) := by ring
            have : 1 ≤ (1 - 2 * (k : ℝ) / (m : ℝ)) * (1 + 4 * (k : ℝ) / (m : ℝ)) := by rw [h2x]; nlinarith
            exact this.trans (mul_le_mul_of_nonneg_left h4 h1x)
          have hpos_e : 0 < Real.exp (4 * (k : ℝ) / (m : ℝ)) := Real.exp_pos _
          have heq_neg : Real.exp (-4 * (k : ℝ) / (m : ℝ)) = (Real.exp (4 * (k : ℝ) / (m : ℝ)))⁻¹ := by
            rw [← Real.exp_neg]; congr 1; ring
          rw [heq_neg, inv_le_comm₀ hpos_e (by linarith)]
          exact (inv_le_iff_one_le_mul₀ (by linarith)).mpr (by linarith)
        linarith
      have hmul_e : Real.exp (-4 * (k : ℝ) * ((j + 1 : ℕ) : ℝ) / (m : ℝ)) =
          Real.exp (-4 * (k : ℝ) / (m : ℝ)) * Real.exp (-4 * (k : ℝ) * (j : ℝ) / (m : ℝ)) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      rw [hmul_e]
      exact mul_le_mul hstep hih (Real.exp_nonneg _) (by positivity)
  exact hprod r le_rfl

/-- Elementary upper bound for falling factorial ratios:
if `k + r ≤ m` and `0 < m`, then `((m - k).descFactorial r : ℝ) / (m.descFactorial r : ℝ) ≤ exp(-k * r / m)`. -/
private lemma descFactorial_ratio_le_exp {m k r : ℕ} (hm : 0 < m) (hkr : k + r ≤ m) :
    ((m - k).descFactorial r : ℝ) / (m.descFactorial r : ℝ) ≤
      Real.exp (-(k : ℝ) * (r : ℝ) / (m : ℝ)) := by
  have hprod : ∀ j, j ≤ r →
      ((m - k).descFactorial j : ℝ) / (m.descFactorial j : ℝ) ≤
        Real.exp (-(k : ℝ) * (j : ℝ) / (m : ℝ)) := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      have hih := ih (by omega)
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_mul, mul_div_mul_comm]
      have hden_pos : (0 : ℝ) < ((m - j : ℕ) : ℝ) := by
        have : 0 < m - j := by omega
        exact_mod_cast this
      have hstep : ((m - k - j : ℕ) : ℝ) / ((m - j : ℕ) : ℝ) ≤ Real.exp (-(k : ℝ) / (m : ℝ)) := by
        have hsub : ((m - k - j : ℕ) : ℝ) / ((m - j : ℕ) : ℝ) = 1 - (k : ℝ) / ((m - j : ℕ) : ℝ) := by
          have : m - k - j + k = m - j := by omega
          have hR : ((m - k - j : ℕ) : ℝ) + (k : ℝ) = ((m - j : ℕ) : ℝ) := by exact_mod_cast this
          field_simp; linarith
        rw [hsub]
        have hmj : ((m - j : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.sub_le m j
        have hdiv : (k : ℝ) / (m : ℝ) ≤ (k : ℝ) / ((m - j : ℕ) : ℝ) :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg k) hden_pos hmj
        have hexp : 1 - (k : ℝ) / (m : ℝ) ≤ Real.exp (-(k : ℝ) / (m : ℝ)) := by
          rw [neg_div]
          linarith [Real.add_one_le_exp (-((k : ℝ) / (m : ℝ)))]
        linarith
      have hmul_e : Real.exp (-(k : ℝ) * ((j + 1 : ℕ) : ℝ) / (m : ℝ)) =
          Real.exp (-(k : ℝ) / (m : ℝ)) * Real.exp (-(k : ℝ) * (j : ℝ) / (m : ℝ)) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      rw [hmul_e]
      exact mul_le_mul hstep hih (by positivity) (Real.exp_nonneg _)
  exact hprod r le_rfl

/-- Uniform avoidance lower bound inside a prescribed `r`-point fibre (`|U| ≤ 2`). -/
private lemma μ_agree_and_avoid_ge (hn : 4 ≤ n) (U A B : Finset (Fin n)) (hdisj : Disjoint U A)
    (hUA : U.card + A.card + 2 ≤ n) (hsmall : 4 * (B.card + U.card) + 2 * A.card ≤ n - U.card)
    (f : Fin n → Fin n) (hf : Set.InjOn f (U : Set (Fin n))) :
    Real.exp (-4 * ((B.card + U.card : ℕ) : ℝ) * (A.card : ℝ) / ((n - U.card : ℕ) : ℝ)) *
        μ (Finset.univ.filter fun π : Alt n => ∀ u ∈ U, π.1 u = f u) ≤
      μ (Finset.univ.filter fun π : Alt n => (∀ u ∈ U, π.1 u = f u) ∧ ∀ a ∈ A, π.1 a ∉ B) := by
  classical
  have h1 := card_alt_agree_and_avoid U A B hdisj hUA f hf
  have h2 := card_alt_agree_on U (by omega) f hf
  have hR_ge : n - U.card - (B.card + U.card) ≤ (Finset.univ \ (U.image f ∪ B)).card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    have hbu : (U.image f ∪ B).card ≤ U.card + B.card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_right Finset.card_image_le _)
    omega
  have hdesc_mono : ((n - U.card - (B.card + U.card)).descFactorial A.card) ≤
      (Finset.univ \ (U.image f ∪ B)).card.descFactorial A.card :=
    descFactorial_mono hR_ge
  have hfac_eq : (n - U.card).factorial = (n - U.card).descFactorial A.card * (n - U.card - A.card).factorial := by
    rw [mul_comm, Nat.factorial_mul_descFactorial (by omega)]
  have hrat := descFactorial_ratio_ge_exp (m := n - U.card) (k := B.card + U.card) (r := A.card)
    (by omega) hsmall
  have hpos_alt : (0 : ℝ) < (Fintype.card (Alt n) : ℝ) := by exact_mod_cast card_alt_pos (by omega)
  have hpos_df : (0 : ℝ) < ((n - U.card).descFactorial A.card : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr (by omega)
  have h1R : 2 * ((Finset.univ.filter fun π : Alt n => (∀ u ∈ U, π.1 u = f u) ∧ ∀ a ∈ A, π.1 a ∉ B).card : ℝ) =
      ((Finset.univ \ (U.image f ∪ B)).card.descFactorial A.card : ℝ) * ((n - U.card - A.card).factorial : ℝ) := by
    exact_mod_cast h1
  have h2R : 2 * ((Finset.univ.filter fun π : Alt n => ∀ u ∈ U, π.1 u = f u).card : ℝ) =
      ((n - U.card).descFactorial A.card : ℝ) * ((n - U.card - A.card).factorial : ℝ) := by
    rw [hfac_eq] at h2; exact_mod_cast h2
  have hmonoR : ((n - U.card - (B.card + U.card)).descFactorial A.card : ℝ) ≤
      ((Finset.univ \ (U.image f ∪ B)).card.descFactorial A.card : ℝ) := by exact_mod_cast hdesc_mono
  have hmul : Real.exp (-4 * ((B.card + U.card : ℕ) : ℝ) * (A.card : ℝ) / ((n - U.card : ℕ) : ℝ)) *
      ((n - U.card).descFactorial A.card : ℝ) ≤
      ((Finset.univ \ (U.image f ∪ B)).card.descFactorial A.card : ℝ) :=
    ((le_div_iff₀ hpos_df).mp hrat).trans hmonoR
  unfold μ
  rw [mul_div_assoc']
  apply div_le_div_of_nonneg_right _ hpos_alt.le
  have h3 := mul_le_mul_of_nonneg_right hmul (Nat.cast_nonneg ((n - U.card - A.card).factorial))
  nlinarith

end Counting

/- ### Section 2: Extremal Density Bounds, `no_fix_x`, and Thresholded Set `J` -/

section Setup

private noncomputable def c_avoid : ℝ := Real.exp (-2200)
private noncomputable def a_const : ℝ := 1 / 100
private noncomputable def b_const : ℝ := 8
private noncomputable def δ_const : ℝ := c_avoid / 1000000
private noncomputable def η_const : ℝ := c_avoid * δ_const / 16

private lemma c_avoid_pos : 0 < c_avoid := Real.exp_pos _
private lemma c_avoid_le_one : c_avoid ≤ 1 := by
  unfold c_avoid; exact Real.exp_le_one_iff.mpr (by norm_num)
private lemma δ_const_pos : 0 < δ_const := by unfold δ_const; have := c_avoid_pos; positivity
private lemma η_const_pos : 0 < η_const := by unfold η_const; have := c_avoid_pos; have := δ_const_pos; positivity

/-- Lower bound on the maximum extremal family density: for `n ≥ 100`, there exist `x, I`
with `μ(extremalFamily x I) ≥ (1 / 32) / √n`. -/
private lemma exists_extremal_lower {n : ℕ} (hn : 100 ≤ n) :
    ∃ (x : Fin n) (I : Finset (Fin n)), x ∉ I ∧
      (1 / 32 : ℝ) / Real.sqrt (n : ℝ) ≤
        μ (Finset.univ.filter fun π : Alt n => π.1 x ∈ I ∧ ∀ a ∈ I, π.1 a ∉ I) := by
  classical
  let k := Nat.sqrt (n / 2)
  have hk_pos : 1 ≤ k := Nat.le_sqrt.mpr (by omega)
  have hk_sq : k ^ 2 ≤ n / 2 := by simpa [sq] using Nat.sqrt_le (n / 2)
  have hk_gt : n / 2 < (k + 1) ^ 2 := by simpa [sq] using Nat.lt_succ_sqrt (n / 2)
  have h2k2 : 2 * k ^ 2 ≤ n := by omega
  have hk_le : 6 * k + 4 ≤ n := by nlinarith
  let x : Fin n := ⟨0, by omega⟩
  let I : Finset (Fin n) := Finset.univ.filter fun i : Fin n => 1 ≤ i.val ∧ i.val ≤ k
  have hxI : x ∉ I := by simp [x, I]
  have hI_card : I.card = k := by
    have hbij : I.card = (Finset.Icc 1 k).card := by
      refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
      · intro i hi; simp [I] at hi; exact Finset.mem_Icc.mpr hi
      · intro i _ j _ h; exact Fin.ext h
      · intro m hm
        have ⟨h1, h2⟩ := Finset.mem_Icc.mp hm
        exact ⟨⟨m, by omega⟩, by simp [I, h1, h2], rfl⟩
    rw [hbij, Nat.card_Icc]; omega
  refine ⟨x, I, hxI, ?_⟩
  rw [μ_extremalFamily_exact (by omega) x I hxI (by rw [hI_card]; omega), hI_card]
  have hfac : n.factorial = n * ((n - 1).descFactorial k * (n - 1 - k).factorial) := by
    rw [mul_comm ((n - 1).descFactorial k), Nat.factorial_mul_descFactorial (by omega)]
    cases n with
    | zero => omega
    | succ m => simp [Nat.factorial_succ]
  rw [hfac, Nat.cast_mul, Nat.cast_mul]
  have hpos_fac : (0 : ℝ) < ((n - 1 - k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hpos_n : (0 : ℝ) < (n : ℝ) := by positivity
  have hpos_df : (0 : ℝ) < ((n - 1).descFactorial k : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr (by omega)
  have hrat : (k : ℝ) * (((n - k).descFactorial k : ℝ) * ((n - 1 - k).factorial : ℝ)) /
      ((n : ℝ) * (((n - 1).descFactorial k : ℝ) * ((n - 1 - k).factorial : ℝ))) =
      ((k : ℝ) / (n : ℝ)) * (((n - k).descFactorial k : ℝ) / ((n - 1).descFactorial k : ℝ)) := by
    field_simp
  rw [hrat]
  have hdesc_ge : ((n - 1 - k).descFactorial k : ℝ) ≤ ((n - k).descFactorial k : ℝ) := by
    exact_mod_cast descFactorial_mono (by omega)
  have hexp := descFactorial_ratio_ge_exp (m := n - 1) (k := k) (r := k) (by omega) (by omega)
  have hexp_ge : Real.exp (-2.5 : ℝ) ≤ Real.exp (-4 * (k : ℝ) * (k : ℝ) / ((n - 1 : ℕ) : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hksqR : (k : ℝ) * (k : ℝ) ≤ (n : ℝ) / 2 := by
      have : 2 * (k * k) ≤ n := by nlinarith
      have hR : 2 * ((k : ℝ) * (k : ℝ)) ≤ (n : ℝ) := by exact_mod_cast this
      linarith
    have hnm1 : (n : ℝ) * (4 / 5 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; simp
      have : (100 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hdiv : 4 * (k : ℝ) * (k : ℝ) / ((n - 1 : ℕ) : ℝ) ≤ 2.5 := by
      rw [div_le_iff₀ (by exact_mod_cast (show 0 < n - 1 by omega))]
      nlinarith
    have hneg : -4 * (k : ℝ) * (k : ℝ) / ((n - 1 : ℕ) : ℝ) = -(4 * (k : ℝ) * (k : ℝ) / ((n - 1 : ℕ) : ℝ)) := by ring
    linarith
  have hratio_ge : Real.exp (-2.5 : ℝ) ≤ ((n - k).descFactorial k : ℝ) / ((n - 1).descFactorial k : ℝ) :=
    hexp_ge.trans (hexp.trans (div_le_div_of_nonneg_right hdesc_ge hpos_df.le))
  have hk_lower : (1 / 2 : ℝ) * Real.sqrt (n : ℝ) ≤ (k : ℝ) := by
    have hk1 : (n : ℝ) / 2 ≤ ((k + 1 : ℕ) : ℝ) ^ 2 := by
      have : n ≤ 2 * (k + 1) ^ 2 := by omega
      have hR : (n : ℝ) ≤ 2 * ((k + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast this
      linarith
    have h7 : 7 ≤ k := Nat.le_sqrt.mpr (by omega)
    have h7R : (7 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h7
    have hsq_k : (n : ℝ) / 4 ≤ (k : ℝ) ^ 2 := by
      push_cast at hk1; nlinarith
    have hsqrt := Real.sqrt_le_sqrt hsq_k
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq (Nat.cast_nonneg k)] at hsqrt
    have : Real.sqrt (4 : ℝ) = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [this] at hsqrt; linarith
  have h1 : (1 / 32 : ℝ) ≤ (1 / 2 : ℝ) * Real.exp (-2.5 : ℝ) := by
    have he1 : Real.exp (1 : ℝ) ≤ 3 := le_of_lt (Real.exp_one_lt_d9.trans (by norm_num))
    have he5 : Real.exp (5 : ℝ) ≤ 243 := by
      rw [show (5 : ℝ) = (5 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
      calc (Real.exp 1) ^ 5 ≤ (3 : ℝ) ^ 5 := pow_le_pow_left₀ (Real.exp_nonneg _) he1 5
        _ = 243 := by norm_num
    have he25 : Real.exp (2.5 : ℝ) ≤ 16 := by
      have hsq : (Real.exp (2.5 : ℝ)) ^ 2 ≤ 16 ^ 2 := by
        rw [← Real.exp_nat_mul, show (2 : ℕ) * (2.5 : ℝ) = 5 by norm_num]
        linarith
      nlinarith [Real.exp_pos (2.5 : ℝ)]
    have hinv : (1 / 16 : ℝ) ≤ Real.exp (-2.5 : ℝ) := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (Real.exp_pos _) he25
    linarith
  have hkn : (1 / 2 : ℝ) / Real.sqrt (n : ℝ) ≤ (k : ℝ) / (n : ℝ) := by
    rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hpos_n) hpos_n]
    have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hpos_n.le
    nlinarith [hk_lower, Real.sqrt_nonneg (n : ℝ)]
  calc (1 / 32 : ℝ) / Real.sqrt (n : ℝ)
      ≤ ((1 / 2 : ℝ) / Real.sqrt (n : ℝ)) * Real.exp (-2.5 : ℝ) := by
        rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right h1 (Real.sqrt_nonneg _)
    _ ≤ ((k : ℝ) / (n : ℝ)) * (((n - k).descFactorial k : ℝ) / ((n - 1).descFactorial k : ℝ)) :=
        mul_le_mul hkn hratio_ge (Real.exp_nonneg _) (by positivity)

/-- Upper bound on the density of any `extremalFamily x I`:
both `≤ |I| / n` and (when `x ∉ I` and `2 |I| ≤ n`) `≤ (|I| / n) * exp(-(|I| - 1) * |I| / n)`. -/
private lemma μ_extremalFamily_upper {n : ℕ} (hn : 10 ≤ n) (x : Fin n) (I : Finset (Fin n)) :
    μ (Finset.univ.filter fun π : Alt n => π.1 x ∈ I ∧ ∀ a ∈ I, π.1 a ∉ I) ≤ (I.card : ℝ) / (n : ℝ) := by
  classical
  let F := Finset.univ.filter fun π : Alt n => π.1 x ∈ I ∧ ∀ a ∈ I, π.1 a ∉ I
  have hsub : F ⊆ I.biUnion fun y => Finset.univ.filter fun π : Alt n => π.1 x = y := by
    intro π hπ
    have h1 := (Finset.mem_filter.mp hπ).2.1
    exact Finset.mem_biUnion.mpr ⟨π.1 x, h1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  calc μ F ≤ μ (I.biUnion fun y => Finset.univ.filter fun π : Alt n => π.1 x = y) := μ_mono hsub
    _ ≤ ∑ y ∈ I, μ (Finset.univ.filter fun π : Alt n => π.1 x = y) := μ_biUnion_le _ _
    _ = ∑ _y ∈ I, (1 / (n : ℝ)) := Finset.sum_congr rfl fun y _ => μ_fiber1 (by omega) x y
    _ = (I.card : ℝ) / (n : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring

private lemma μ_extremalFamily_exp_upper {n : ℕ} (hn : 10 ≤ n) (x : Fin n) (I : Finset (Fin n))
    (hxI : x ∉ I) (hI : 2 * I.card ≤ n) (hI_pos : 1 ≤ I.card) :
    μ (Finset.univ.filter fun π : Alt n => π.1 x ∈ I ∧ ∀ a ∈ I, π.1 a ∉ I) ≤
      ((I.card : ℝ) / (n : ℝ)) * Real.exp (-(((I.card - 1 : ℕ) : ℝ) * (I.card : ℝ)) / (n : ℝ)) := by
  classical
  rw [μ_extremalFamily_exact (by omega) x I hxI (by omega)]
  have hfac : n.factorial = n * ((n - 1).descFactorial I.card * (n - 1 - I.card).factorial) := by
    rw [mul_comm ((n - 1).descFactorial I.card), Nat.factorial_mul_descFactorial (by omega)]
    cases n with
    | zero => omega
    | succ m => simp [Nat.factorial_succ]
  rw [hfac, Nat.cast_mul, Nat.cast_mul]
  have hpos_fac : (0 : ℝ) < ((n - 1 - I.card).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hpos_n : (0 : ℝ) < (n : ℝ) := by positivity
  have hpos_df : (0 : ℝ) < ((n - 1).descFactorial I.card : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr (by omega)
  have hrat : (I.card : ℝ) * (((n - I.card).descFactorial I.card : ℝ) * ((n - 1 - I.card).factorial : ℝ)) /
      ((n : ℝ) * (((n - 1).descFactorial I.card : ℝ) * ((n - 1 - I.card).factorial : ℝ))) =
      ((I.card : ℝ) / (n : ℝ)) * (((n - I.card).descFactorial I.card : ℝ) / ((n - 1).descFactorial I.card : ℝ)) := by
    field_simp
  rw [hrat]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have heq : n - I.card = (n - 1) - (I.card - 1) := by omega
  rw [heq]
  have hle := descFactorial_ratio_le_exp (m := n - 1) (k := I.card - 1) (r := I.card) (by omega) (by omega)
  refine hle.trans (Real.exp_le_exp.mpr ?_)
  have hnm1 : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
  have hnum : 0 ≤ ((I.card - 1 : ℕ) : ℝ) * (I.card : ℝ) := by positivity
  have hdiv : ((I.card - 1 : ℕ) : ℝ) * (I.card : ℝ) / (n : ℝ) ≤
      ((I.card - 1 : ℕ) : ℝ) * (I.card : ℝ) / ((n - 1 : ℕ) : ℝ) :=
    div_le_div_of_nonneg_left hnum (by exact_mod_cast (show 0 < n - 1 by omega)) hnm1
  have hneg1 : -(((I.card - 1 : ℕ) : ℝ)) * (I.card : ℝ) / ((n - 1 : ℕ) : ℝ) =
      -(((I.card - 1 : ℕ) : ℝ) * (I.card : ℝ) / ((n - 1 : ℕ) : ℝ)) := by ring
  have hneg2 : -(((I.card - 1 : ℕ) : ℝ) * (I.card : ℝ)) / (n : ℝ) =
      -(((I.card - 1 : ℕ) : ℝ) * (I.card : ℝ) / (n : ℝ)) := by ring
  linarith

/-- Any set `I` whose extremal family has density `≥ (1 / 40) / √n` satisfies `x ∉ I`
and `(1 / 40) √n ≤ |I| ≤ 4 √n` (for `n ≥ 10000`). -/
private lemma extremal_card_bounds {n : ℕ} (hn : 10000 ≤ n) (x : Fin n) (I : Finset (Fin n))
    (hge : (1 / 40 : ℝ) / Real.sqrt (n : ℝ) ≤
      μ (Finset.univ.filter fun π : Alt n => π.1 x ∈ I ∧ ∀ a ∈ I, π.1 a ∉ I)) :
    x ∉ I ∧ 2 * a_const * Real.sqrt (n : ℝ) ≤ (I.card : ℝ) ∧
      (I.card : ℝ) ≤ (b_const / 2) * Real.sqrt (n : ℝ) := by
  have hpos_n : (0 : ℝ) < (n : ℝ) := by positivity
  have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hpos_n
  have hsq_ge : (100 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [show (100 : ℝ) = Real.sqrt (10000 : ℝ) by rw [show (10000 : ℝ) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hF_pos : 0 < μ (Finset.univ.filter fun π : Alt n => π.1 x ∈ I ∧ ∀ a ∈ I, π.1 a ∉ I) :=
    lt_of_lt_of_le (by positivity) hge
  have hxI : x ∉ I := by
    intro hx
    have hempty : (Finset.univ.filter fun π : Alt n => π.1 x ∈ I ∧ ∀ a ∈ I, π.1 a ∉ I) = ∅ := by
      ext π; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨h1, h2⟩; exact h2 x hx h1
    rw [hempty] at hF_pos; simp [μ] at hF_pos
  have h2I : 2 * I.card ≤ n := by
    by_contra hgt
    have hempty : (Finset.univ.filter fun π : Alt n => π.1 x ∈ I ∧ ∀ a ∈ I, π.1 a ∉ I) = ∅ := by
      ext π; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨_, h2⟩
      have hdisj : Disjoint (I.image π.1) I := by
        rw [Finset.disjoint_left]; intro z hz; obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz; exact h2 a ha
      have hsum := Finset.card_union_of_disjoint hdisj
      have himg : (I.image π.1).card = I.card := Finset.card_image_of_injective _ π.1.injective
      have hle : (I.image π.1 ∪ I).card ≤ n := by
        simpa [Fintype.card_fin] using Finset.card_le_univ (I.image π.1 ∪ I)
      omega
    rw [hempty] at hF_pos; simp [μ] at hF_pos
  have hlo : (1 / 40 : ℝ) * Real.sqrt (n : ℝ) ≤ (I.card : ℝ) := by
    have hup := μ_extremalFamily_upper (by omega) x I
    have h1 : (1 / 40 : ℝ) / Real.sqrt (n : ℝ) ≤ (I.card : ℝ) / (n : ℝ) := hge.trans hup
    rw [div_le_div_iff₀ hsq_pos hpos_n] at h1
    have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hpos_n.le
    nlinarith
  have hI_pos : 1 ≤ I.card := by
    have : (1 : ℝ) ≤ (I.card : ℝ) := by linarith
    exact_mod_cast this
  have hhi : (I.card : ℝ) ≤ 4 * Real.sqrt (n : ℝ) := by
    by_contra hgt
    push Not at hgt
    have hexp := μ_extremalFamily_exp_upper (by omega) x I hxI h2I hI_pos
    have hbound : (1 / 40 : ℝ) / Real.sqrt (n : ℝ) ≤
        ((I.card : ℝ) / (n : ℝ)) * Real.exp (-(((I.card - 1 : ℕ) : ℝ) * (I.card : ℝ)) / (n : ℝ)) :=
      hge.trans hexp
    let t : ℝ := (I.card : ℝ) / Real.sqrt (n : ℝ)
    have ht_gt : 4 < t := by dsimp [t]; rw [lt_div_iff₀ hsq_pos]; linarith
    have hsub1 : ((I.card - 1 : ℕ) : ℝ) = (I.card : ℝ) - 1 := by rw [Nat.cast_sub hI_pos]; simp
    have hexp_arg : t ^ 2 / 2 ≤ (((I.card - 1 : ℕ) : ℝ) * (I.card : ℝ)) / (n : ℝ) := by
      rw [hsub1, le_div_iff₀ hpos_n]
      have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hpos_n.le
      have ht_sq : t ^ 2 * (n : ℝ) = (I.card : ℝ) ^ 2 := by
        dsimp [t]; rw [div_pow, Real.sq_sqrt hpos_n.le]; field_simp
      nlinarith
    have h_te : t * Real.exp (-(t ^ 2 / 2)) < 1 / 40 := by
      have hu : 0 ≤ t ^ 2 / 2 := by positivity
      have hsum : (t ^ 2 / 2) ^ 4 / 24 ≤ Real.exp (t ^ 2 / 2) := by
        have h1 := Real.sum_le_exp_of_nonneg hu 5
        have h2 : (t ^ 2 / 2) ^ 4 / (Nat.factorial 4 : ℝ) ≤
            ∑ i ∈ Finset.range 5, (t ^ 2 / 2) ^ i / (Nat.factorial i : ℝ) :=
          Finset.single_le_sum (f := fun i => (t ^ 2 / 2) ^ i / (Nat.factorial i : ℝ))
            (fun i _ => by positivity) (by decide : 4 ∈ Finset.range 5)
        norm_num [Nat.factorial] at h2
        linarith
      have h40 : 40 * t < Real.exp (t ^ 2 / 2) := by
        have ht3 : 64 < t ^ 3 := by nlinarith
        have ht7 : 40 * t < (t ^ 2 / 2) ^ 4 / 24 := by
          have : (t ^ 2 / 2) ^ 4 / 24 = t * (t ^ 3 * (t ^ 4 / 384)) := by ring
          have ht4 : 256 < t ^ 4 := by nlinarith
          nlinarith
        linarith
      rw [Real.exp_neg]
      have hepos : 0 < Real.exp (t ^ 2 / 2) := Real.exp_pos _
      rw [show t * (Real.exp (t ^ 2 / 2))⁻¹ = t / Real.exp (t ^ 2 / 2) by ring,
        div_lt_div_iff₀ hepos (by norm_num)]
      linarith
    have hrel : ((I.card : ℝ) / (n : ℝ)) * Real.exp (-(((I.card - 1 : ℕ) : ℝ) * (I.card : ℝ)) / (n : ℝ)) ≤
        (t * Real.exp (-(t ^ 2 / 2))) / Real.sqrt (n : ℝ) := by
      have h1 : (I.card : ℝ) / (n : ℝ) = t / Real.sqrt (n : ℝ) := by
        dsimp [t]; rw [div_div, Real.mul_self_sqrt hpos_n.le]
      rw [h1, div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hsq_pos.le
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      rw [neg_div]
      linarith
    have hfinal : (1 / 40 : ℝ) / Real.sqrt (n : ℝ) < (1 / 40 : ℝ) / Real.sqrt (n : ℝ) := by
      calc (1 / 40 : ℝ) / Real.sqrt (n : ℝ)
          ≤ (t * Real.exp (-(t ^ 2 / 2))) / Real.sqrt (n : ℝ) := hbound.trans hrel
        _ < (1 / 40 : ℝ) / Real.sqrt (n : ℝ) := div_lt_div_of_pos_right h_te hsq_pos
    exact lt_irrefl _ hfinal
  refine ⟨hxI, ?_, ?_⟩
  · unfold a_const; linarith
  · unfold b_const; linarith

/-- Uniform avoidance lower bound with explicit constant `c_avoid = exp(-2000)` whenever
`|U| ≤ 2`, `|A| ≤ 16 √n`, `|B| ≤ 16 √n`, `n ≥ 100000`. -/
private lemma μ_avoid_ge_c {n : ℕ} (hn : 100000 ≤ n) (U A B : Finset (Fin n)) (hdisj : Disjoint U A)
    (hU : U.card ≤ 2) (hA : (A.card : ℝ) ≤ 16 * Real.sqrt (n : ℝ))
    (hB : (B.card : ℝ) ≤ 16 * Real.sqrt (n : ℝ)) (f : Fin n → Fin n) (hf : Set.InjOn f (U : Set (Fin n))) :
    c_avoid * μ (Finset.univ.filter fun π : Alt n => ∀ u ∈ U, π.1 u = f u) ≤
      μ (Finset.univ.filter fun π : Alt n => (∀ u ∈ U, π.1 u = f u) ∧ ∀ a ∈ A, π.1 a ∉ B) := by
  have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hsq_ge : (300 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have : (90000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 90000 ≤ n by omega)
    calc (300 : ℝ) = Real.sqrt (90000 : ℝ) := by
          rw [show (90000 : ℝ) = 300 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt this
  have hsq_sq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt (by positivity)
  have hAB_small : 4 * (B.card + U.card) + 2 * A.card ≤ n - U.card := by
    have hR : 4 * ((B.card : ℝ) + (U.card : ℝ)) + 2 * (A.card : ℝ) + (U.card : ℝ) ≤ (n : ℝ) := by
      have hUR : (U.card : ℝ) ≤ 2 := by exact_mod_cast hU
      nlinarith
    have hN : 4 * (B.card + U.card) + 2 * A.card + U.card ≤ n := by exact_mod_cast hR
    omega
  have hUA : U.card + A.card + 2 ≤ n := by omega
  have hmain := μ_agree_and_avoid_ge (by omega) U A B hdisj hUA hAB_small f hf
  refine le_trans (mul_le_mul_of_nonneg_right ?_ (μ_nonneg _)) hmain
  unfold c_avoid
  apply Real.exp_le_exp.mpr
  have hden : (n : ℝ) / 2 ≤ ((n - U.card : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    have hUR : (U.card : ℝ) ≤ 2 := by exact_mod_cast hU
    have hnR : (100000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hnum : ((B.card + U.card : ℕ) : ℝ) * (A.card : ℝ) ≤ 260 * (n : ℝ) := by
    push_cast
    have hUR : (U.card : ℝ) ≤ 2 := by exact_mod_cast hU
    nlinarith
  have hden_pos : (0 : ℝ) < ((n - U.card : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - U.card by omega)
  have hdiv : 4 * ((B.card + U.card : ℕ) : ℝ) * (A.card : ℝ) / ((n - U.card : ℕ) : ℝ) ≤ 2200 := by
    rw [div_le_iff₀ hden_pos]
    nlinarith
  have hneg : -4 * ((B.card + U.card : ℕ) : ℝ) * (A.card : ℝ) / ((n - U.card : ℕ) : ℝ) =
      -(4 * ((B.card + U.card : ℕ) : ℝ) * (A.card : ℝ) / ((n - U.card : ℕ) : ℝ)) := by ring
  linarith

end Setup


/- ### Section 3: Subset-Sampling Variance / Chebyshev Bound & Inside-Edge Bound -/

section InsideEdges

/-- Exact count of `s`-subsets of `W` disjoint from `A`. -/
private lemma card_powersetCard_disjoint {n : ℕ} (W A : Finset (Fin n)) (s : ℕ) :
    ((W.powersetCard s).filter fun T => Disjoint A T).card = (W \ A).card.choose s := by
  have heq : (W.powersetCard s).filter (fun T => Disjoint A T) = (W \ A).powersetCard s := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_sdiff, disjoint_comm]
    tauto
  rw [heq, Finset.card_powersetCard]

/-- Ratio of binomial coefficients equals ratio of falling factorials. -/
private lemma choose_div_choose_eq_descFactorial {a b s : ℕ} (hs : s ≤ b) :
    ((a.choose s : ℕ) : ℝ) / ((b.choose s : ℕ) : ℝ) =
      ((a.descFactorial s : ℕ) : ℝ) / ((b.descFactorial s : ℕ) : ℝ) := by
  have h1 : (s.factorial : ℝ) * (a.choose s : ℝ) = (a.descFactorial s : ℝ) := by
    exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose a s).symm
  have h2 : (s.factorial : ℝ) * (b.choose s : ℝ) = (b.descFactorial s : ℝ) := by
    exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose b s).symm
  have hsf : (s.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos s).ne'
  have hbd : (b.descFactorial s : ℝ) ≠ 0 := by exact_mod_cast (Nat.descFactorial_pos.mpr hs).ne'
  have hbc : (b.choose s : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hs).ne'
  rw [div_eq_div_iff hbc hbd]
  nlinarith

/-- Pairwise correlation upper bound for uniform `s`-subset avoidance:
for `A₁, A₂ ⊆ W` with `r₁ = |A₁|`, `r₂ = |A₂|`, `q = |A₁ ∩ A₂|`, `|W| = m`,
if `4 * (r₁ + r₂ + s) ≤ m`, then
`Pr(Disjoint (A₁ ∪ A₂) T) ≤ Pr(Disjoint A₁ T) * Pr(Disjoint A₂ T) * exp(4 * s * q / m)`. -/
private lemma descFactorial_union_le {m r₁ r₂ q s : ℕ} (hm : 0 < m)
    (hsmall : 4 * (r₁ + r₂ + s) ≤ m) (hq1 : q ≤ r₁) (hq2 : q ≤ r₂) :
    (((m - (r₁ + r₂ - q)).descFactorial s : ℕ) : ℝ) / ((m.descFactorial s : ℕ) : ℝ) ≤
      ((((m - r₁).descFactorial s : ℕ) : ℝ) / ((m.descFactorial s : ℕ) : ℝ)) *
      ((((m - r₂).descFactorial s : ℕ) : ℝ) / ((m.descFactorial s : ℕ) : ℝ)) *
      Real.exp (4 * (s : ℝ) * (q : ℝ) / (m : ℝ)) := by
  have hprod : ∀ j, j ≤ s →
      (((m - (r₁ + r₂ - q)).descFactorial j : ℕ) : ℝ) / ((m.descFactorial j : ℕ) : ℝ) ≤
        ((((m - r₁).descFactorial j : ℕ) : ℝ) / ((m.descFactorial j : ℕ) : ℝ)) *
        ((((m - r₂).descFactorial j : ℕ) : ℝ) / ((m.descFactorial j : ℕ) : ℝ)) *
        Real.exp (4 * (j : ℝ) * (q : ℝ) / (m : ℝ)) := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      have hih := ih (by omega)
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_succ]
      push_cast
      have hmj : (0 : ℝ) < ((m - j : ℕ) : ℝ) := by exact_mod_cast (show 0 < m - j by omega)
      have hmr1 : (0 : ℝ) < ((m - r₁ - j : ℕ) : ℝ) := by exact_mod_cast (show 0 < m - r₁ - j by omega)
      have hmr2 : (0 : ℝ) < ((m - r₂ - j : ℕ) : ℝ) := by exact_mod_cast (show 0 < m - r₂ - j by omega)
      have hstep : ((m - (r₁ + r₂ - q) - j : ℕ) : ℝ) / ((m - j : ℕ) : ℝ) ≤
          (((m - r₁ - j : ℕ) : ℝ) / ((m - j : ℕ) : ℝ)) *
          (((m - r₂ - j : ℕ) : ℝ) / ((m - j : ℕ) : ℝ)) *
          Real.exp (4 * (q : ℝ) / (m : ℝ)) := by
        have hcast0 : ((m - j : ℕ) : ℝ) = (m : ℝ) - (j : ℝ) := by rw [Nat.cast_sub (by omega)]
        have hcast1 : ((m - r₁ - j : ℕ) : ℝ) = (m : ℝ) - (r₁ : ℝ) - (j : ℝ) := by
          rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        have hcast2 : ((m - r₂ - j : ℕ) : ℝ) = (m : ℝ) - (r₂ : ℝ) - (j : ℝ) := by
          rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        have hcast12 : ((m - (r₁ + r₂ - q) - j : ℕ) : ℝ) = (m : ℝ) - (r₁ : ℝ) - (r₂ : ℝ) + (q : ℝ) - (j : ℝ) := by
          rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_add]; ring
        have hnum_le : ((m - (r₁ + r₂ - q) - j : ℕ) : ℝ) * ((m - j : ℕ) : ℝ) ≤
            ((m - r₁ - j : ℕ) : ℝ) * ((m - r₂ - j : ℕ) : ℝ) + (q : ℝ) * ((m - j : ℕ) : ℝ) := by
          rw [hcast0, hcast1, hcast2, hcast12]
          have hr12 : (0 : ℝ) ≤ (r₁ : ℝ) * (r₂ : ℝ) := by positivity
          nlinarith
        have hden_ge : ((m : ℝ) / 2) * ((m - j : ℕ) : ℝ) ≤
            ((m - r₁ - j : ℕ) : ℝ) * ((m - r₂ - j : ℕ) : ℝ) := by
          rw [hcast0, hcast1, hcast2]
          have hsmallR : 4 * ((r₁ : ℝ) + (r₂ : ℝ) + (s : ℝ)) ≤ (m : ℝ) := by exact_mod_cast hsmall
          have hjR : (j : ℝ) ≤ (s : ℝ) := by exact_mod_cast (show j ≤ s by omega)
          nlinarith
        have h1add : ((m - (r₁ + r₂ - q) - j : ℕ) : ℝ) * ((m - j : ℕ) : ℝ) ≤
            ((m - r₁ - j : ℕ) : ℝ) * ((m - r₂ - j : ℕ) : ℝ) * (1 + 4 * (q : ℝ) / (m : ℝ)) := by
          have hq_term : (q : ℝ) * ((m - j : ℕ) : ℝ) ≤
              ((m - r₁ - j : ℕ) : ℝ) * ((m - r₂ - j : ℕ) : ℝ) * (4 * (q : ℝ) / (m : ℝ)) := by
            have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
            have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
            have h1 : (q : ℝ) * ((m - j : ℕ) : ℝ) * (m : ℝ) ≤
                ((m - r₁ - j : ℕ) : ℝ) * ((m - r₂ - j : ℕ) : ℝ) * (4 * (q : ℝ)) := by
              have h2 := mul_le_mul_of_nonneg_right hden_ge (show (0 : ℝ) ≤ 4 * (q : ℝ) by linarith)
              have h3 : (q : ℝ) * ((m - j : ℕ) : ℝ) * (m : ℝ) ≤ (m : ℝ) / 2 * ((m - j : ℕ) : ℝ) * (4 * (q : ℝ)) := by
                have : (m : ℝ) / 2 * ((m - j : ℕ) : ℝ) * (4 * (q : ℝ)) = 2 * ((q : ℝ) * ((m - j : ℕ) : ℝ) * (m : ℝ)) := by ring
                have hnn : 0 ≤ (q : ℝ) * ((m - j : ℕ) : ℝ) * (m : ℝ) := by positivity
                linarith
              exact h3.trans h2
            rw [mul_div_assoc', le_div_iff₀ hmpos]; linarith
          linarith
        have hexp : 1 + 4 * (q : ℝ) / (m : ℝ) ≤ Real.exp (4 * (q : ℝ) / (m : ℝ)) := by
          have := Real.add_one_le_exp (4 * (q : ℝ) / (m : ℝ)); linarith
        have hfinal : ((m - (r₁ + r₂ - q) - j : ℕ) : ℝ) * ((m - j : ℕ) : ℝ) ≤
            ((m - r₁ - j : ℕ) : ℝ) * ((m - r₂ - j : ℕ) : ℝ) * Real.exp (4 * (q : ℝ) / (m : ℝ)) :=
          h1add.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
        rw [div_mul_div_comm, div_mul_eq_mul_div, div_le_div_iff₀ hmj (mul_pos hmj hmj)]
        nlinarith
      have hmul_e : Real.exp (4 * ((j : ℝ) + 1) * (q : ℝ) / (m : ℝ)) =
          Real.exp (4 * (j : ℝ) * (q : ℝ) / (m : ℝ)) * Real.exp (4 * (q : ℝ) / (m : ℝ)) := by
        rw [← Real.exp_add]; congr 1; ring
      have hlhs : ((m - (r₁ + r₂ - q) - j : ℕ) : ℝ) * ((m - (r₁ + r₂ - q)).descFactorial j : ℝ) /
          (((m - j : ℕ) : ℝ) * (m.descFactorial j : ℝ)) =
          (((m - (r₁ + r₂ - q)).descFactorial j : ℝ) / (m.descFactorial j : ℝ)) *
          (((m - (r₁ + r₂ - q) - j : ℕ) : ℝ) / ((m - j : ℕ) : ℝ)) := by ring
      have hrhs : (((m - r₁ - j : ℕ) : ℝ) * ((m - r₁).descFactorial j : ℝ) /
          (((m - j : ℕ) : ℝ) * (m.descFactorial j : ℝ))) *
          (((m - r₂ - j : ℕ) : ℝ) * ((m - r₂).descFactorial j : ℝ) /
          (((m - j : ℕ) : ℝ) * (m.descFactorial j : ℝ))) *
          Real.exp (4 * ((j : ℝ) + 1) * (q : ℝ) / (m : ℝ)) =
          ((((m - r₁).descFactorial j : ℝ) / (m.descFactorial j : ℝ)) *
           (((m - r₂).descFactorial j : ℝ) / (m.descFactorial j : ℝ)) *
           Real.exp (4 * (j : ℝ) * (q : ℝ) / (m : ℝ))) *
          ((((m - r₁ - j : ℕ) : ℝ) / ((m - j : ℕ) : ℝ)) *
           (((m - r₂ - j : ℕ) : ℝ) / ((m - j : ℕ) : ℝ)) *
           Real.exp (4 * (q : ℝ) / (m : ℝ))) := by
        rw [hmul_e]; ring
      rw [hlhs, hrhs]
      exact mul_le_mul hih hstep (by positivity) (by positivity)
  exact hprod s le_rfl

set_option maxHeartbeats 2000000 in
/-- Elementary second-moment / Chebyshev concentration bound for uniform `s`-subset avoidance:
for `C ⊆ Ω_v = {γ ∈ A_n | γ(x) = v}` of conditional density `≥ δ_const`, `D` of size `≤ 2`,
`W` of size `≥ n - 2`, `s ≤ 8 √n`, `x ∉ J`, `|J| ≤ 8 √n`,
the fraction of `T ∈ W.powersetCard s` with `Z(T) ≤ η_const` is at most
`40000 / (c_avoid * δ_const)^2 / n^(1/4)` (for `n ≥ 10^8` and `√n ≥ 100 / δ_const`). -/
private lemma subset_avoid_chebyshev {n : ℕ} (hn : 100000000 ≤ n)
    (hbig : 100 / δ_const ≤ Real.sqrt (n : ℝ))
    (x v : Fin n) (J D W : Finset (Fin n)) (s : ℕ)
    (hxJ : x ∉ J) (hJ : (J.card : ℝ) ≤ b_const * Real.sqrt (n : ℝ))
    (hD : D.card ≤ 2) (hW : n - 2 ≤ W.card) (hs : (s : ℝ) ≤ b_const * Real.sqrt (n : ℝ))
    (C : Finset (Alt n)) (hC_sub : ∀ γ ∈ C, γ.1 x = v)
    (hC_dens : δ_const ≤ (C.card : ℝ) / ((Finset.univ.filter fun γ : Alt n => γ.1 x = v).card : ℝ)) :
    let Ω := Finset.univ.filter fun γ : Alt n => γ.1 x = v
    let Z (T : Finset (Fin n)) : ℝ := ((C.filter fun γ => ∀ a ∈ J, γ.1 a ∉ D ∪ T).card : ℝ) / (Ω.card : ℝ)
    (((W.powersetCard s).filter fun T => Z T ≤ η_const).card : ℝ) / ((W.powersetCard s).card : ℝ) ≤
      (40000 : ℝ) / ((c_avoid * δ_const) ^ 2 * (n : ℝ) ^ ((1 : ℝ) / 4)) := by
  classical
  intro Ω Z
  have hnR : (100000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnm1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hsq_ge : (10000 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have : (100000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    calc (10000 : ℝ) = Real.sqrt (100000000 : ℝ) := by
          rw [show (100000000 : ℝ) = 10000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt this
  have hsq_sq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt (by positivity)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hn4_pos : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hn_pos _
  have hn4_sq : ((n : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt (n : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]; norm_num
  have hn4_ge : (100 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := by nlinarith [hn4_pos, hn4_sq, hsq_ge]
  have hs_le_W : s ≤ W.card := by
    have h1 : (s : ℝ) ≤ 8 * Real.sqrt (n : ℝ) := by unfold b_const at hs; exact hs
    have h2 : (s : ℝ) ≤ (n : ℝ) - 2 := by nlinarith
    have h3 : s ≤ n - 2 := by
      have : (s : ℝ) + 2 ≤ (n : ℝ) := by linarith
      have : s + 2 ≤ n := by exact_mod_cast this
      omega
    omega
  have hP_pos : (0 : ℝ) < ((W.powersetCard s).card : ℝ) := by
    rw [Finset.card_powersetCard]; exact_mod_cast Nat.choose_pos hs_le_W
  have hΩ_card : 2 * Ω.card = (n - 1).factorial := by
    have h := card_alt_agree_on {x} (by simp; omega) (fun _ => v) (by simp)
    have hfilt : (Finset.univ.filter fun π : Alt n => ∀ u ∈ ({x} : Finset (Fin n)), π.1 u = v) = Ω := by
      ext π; simp [Ω]
    rw [hfilt, Finset.card_singleton] at h; exact h
  have hΩ_pos : (0 : ℝ) < (Ω.card : ℝ) := by
    have : 2 ≤ (n - 1).factorial := by
      calc 2 = (2 : ℕ).factorial := by decide
        _ ≤ (n - 1).factorial := Nat.factorial_le (by omega)
    have : 0 < Ω.card := by omega
    exact_mod_cast this
  let C' := C.filter fun γ => ∀ a ∈ J, γ.1 a ∉ D
  have hZ_eq : ∀ T : Finset (Fin n), Z T =
      ((C'.filter fun γ => Disjoint (J.image γ.1) T).card : ℝ) / (Ω.card : ℝ) := by
    intro T; dsimp only [Z]; congr 3; ext γ
    simp only [C', Finset.mem_filter, Finset.mem_union, not_or, Finset.disjoint_left, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, fun a ha => (h2 a ha).1⟩, fun z ⟨a, ha, hz⟩ => hz ▸ (h2 a ha).2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, fun a ha => ⟨h2 a ha, h3 ⟨a, ha, rfl⟩⟩⟩
  -- Step 1: Lower bound on C'.card / Ω.card ≥ δ_const - 2 * |J| / (n - 1)
  have hC'_dens : δ_const - 2 * (J.card : ℝ) / ((n : ℝ) - 1) ≤ (C'.card : ℝ) / (Ω.card : ℝ) := by
    have hbad_sub : C \ C' ⊆ (J ×ˢ D).biUnion fun ad =>
        Finset.univ.filter fun γ : Alt n => γ.1 x = v ∧ γ.1 ad.1 = ad.2 := by
      intro γ hγ
      obtain ⟨hγC, hγnot⟩ := Finset.mem_sdiff.mp hγ
      simp only [C', Finset.mem_filter, hγC, true_and, not_forall, Classical.not_not] at hγnot
      obtain ⟨a, haJ, haD⟩ := hγnot
      exact Finset.mem_biUnion.mpr ⟨(a, γ.1 a), Finset.mem_product.mpr ⟨haJ, haD⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC_sub γ hγC, rfl⟩⟩
    have hbad_card : ((C \ C').card : ℝ) / (Ω.card : ℝ) ≤ (D.card : ℝ) * (J.card : ℝ) / ((n : ℝ) - 1) := by
      have hsum : ((C \ C').card : ℝ) ≤ ∑ ad ∈ J ×ˢ D,
          ((Finset.univ.filter fun γ : Alt n => γ.1 x = v ∧ γ.1 ad.1 = ad.2).card : ℝ) := by
        exact_mod_cast (Finset.card_le_card hbad_sub).trans Finset.card_biUnion_le
      have hterm : ∀ ad ∈ J ×ˢ D, ((Finset.univ.filter fun γ : Alt n => γ.1 x = v ∧ γ.1 ad.1 = ad.2).card : ℝ) ≤
          (Ω.card : ℝ) / ((n : ℝ) - 1) := by
        intro ad had
        obtain ⟨haJ, _⟩ := Finset.mem_product.mp had
        have hax : x ≠ ad.1 := fun e => hxJ (e ▸ haJ)
        by_cases hdv : v = ad.2
        · have hempty : (Finset.univ.filter fun γ : Alt n => γ.1 x = v ∧ γ.1 ad.1 = ad.2) = ∅ := by
            ext γ; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
            rintro ⟨h1, h2⟩; exact hax (γ.1.injective (h1.trans (hdv.trans h2.symm)))
          rw [hempty]; simp; exact div_nonneg hΩ_pos.le hnm1_pos.le
        · have h1 := μ_fiber2 (by omega) hax hdv
          have h2 := μ_fiber1 (by omega) x v
          have hpos_alt : (0 : ℝ) < (Fintype.card (Alt n) : ℝ) := by exact_mod_cast card_alt_pos (by omega)
          unfold μ at h1 h2
          change ((Finset.univ.filter fun γ : Alt n => γ.1 x = v).card : ℝ) / (Fintype.card (Alt n) : ℝ) = 1 / (n : ℝ) at h2
          have hΩ_eq : (Ω.card : ℝ) = (Fintype.card (Alt n) : ℝ) / (n : ℝ) := by
            change ((Finset.univ.filter fun γ : Alt n => γ.1 x = v).card : ℝ) = _
            rw [eq_div_iff hn_pos.ne']; linarith [(div_eq_div_iff hpos_alt.ne' hn_pos.ne').mp h2]
          have hfib_eq : ((Finset.univ.filter fun γ : Alt n => γ.1 x = v ∧ γ.1 ad.1 = ad.2).card : ℝ) =
              (Fintype.card (Alt n) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
            rw [eq_div_iff (mul_pos hn_pos hnm1_pos).ne']
            have := (div_eq_div_iff hpos_alt.ne' (mul_pos hn_pos hnm1_pos).ne').mp h1
            linarith
          rw [hfib_eq, hΩ_eq, div_div]
      calc ((C \ C').card : ℝ) / (Ω.card : ℝ)
          ≤ (∑ _ad ∈ J ×ˢ D, ((Ω.card : ℝ) / ((n : ℝ) - 1))) / (Ω.card : ℝ) :=
            div_le_div_of_nonneg_right (hsum.trans (Finset.sum_le_sum hterm)) hΩ_pos.le
        _ = ((J ×ˢ D).card : ℝ) / ((n : ℝ) - 1) := by
            rw [Finset.sum_const, nsmul_eq_mul]; field_simp
        _ = (D.card : ℝ) * (J.card : ℝ) / ((n : ℝ) - 1) := by
            rw [Finset.card_product, Nat.cast_mul, mul_comm]
    have hsplit : (C.card : ℝ) = (C'.card : ℝ) + ((C \ C').card : ℝ) := by
      have hsub : C' ⊆ C := Finset.filter_subset _ _
      have := Finset.card_sdiff_add_card_eq_card hsub
      have hR : ((C \ C').card : ℝ) + (C'.card : ℝ) = (C.card : ℝ) := by exact_mod_cast this
      linarith
    have hD_R : (D.card : ℝ) ≤ 2 := by exact_mod_cast hD
    have h1 : (D.card : ℝ) * (J.card : ℝ) / ((n : ℝ) - 1) ≤ 2 * (J.card : ℝ) / ((n : ℝ) - 1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hD_R (Nat.cast_nonneg _)) (by linarith)
    have h2 : (C.card : ℝ) / (Ω.card : ℝ) = (C'.card : ℝ) / (Ω.card : ℝ) + ((C \ C').card : ℝ) / (Ω.card : ℝ) := by
      rw [← add_div, hsplit]
    linarith
  -- Step 2: Exact expectation EZ and second moment EZ2 via swapping sums
  let P := W.powersetCard s
  let pAvoid (A : Finset (Fin n)) : ℝ := ((W \ A).card.choose s : ℝ) / (P.card : ℝ)
  have hEZ_eq : (∑ T ∈ P, Z T) / (P.card : ℝ) = (∑ γ ∈ C', pAvoid (J.image γ.1)) / (Ω.card : ℝ) := by
    have hswap : ∑ T ∈ P, ((C'.filter fun γ => Disjoint (J.image γ.1) T).card : ℝ) =
        ∑ γ ∈ C', ((W \ J.image γ.1).card.choose s : ℝ) := by
      simp_rw [Finset.card_filter, Nat.cast_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [← Nat.cast_sum, ← Finset.card_filter, card_powersetCard_disjoint]
    simp_rw [hZ_eq, ← Finset.sum_div, hswap, pAvoid, ← Finset.sum_div]
    rw [div_div, div_div, mul_comm (Ω.card : ℝ) (P.card : ℝ)]
  have hpAvoid_ge : ∀ γ ∈ C', c_avoid ≤ pAvoid (J.image γ.1) := by
    intro γ _
    dsimp only [pAvoid, P]
    rw [Finset.card_powersetCard, choose_div_choose_eq_descFactorial hs_le_W]
    have hA_le : (J.image γ.1 ∩ W).card ≤ J.card :=
      (Finset.card_le_card Finset.inter_subset_left).trans Finset.card_image_le
    have hcard_sdiff : W.card - J.card ≤ (W \ J.image γ.1).card := by
      have h1 := Finset.card_sdiff_add_card_inter W (J.image γ.1)
      have h2 : (W ∩ J.image γ.1).card ≤ J.card := by
        rw [Finset.inter_comm]; exact hA_le
      omega
    have hmono : ((W.card - J.card).descFactorial s : ℝ) ≤ ((W \ J.image γ.1).card.descFactorial s : ℝ) := by
      exact_mod_cast descFactorial_mono hcard_sdiff
    have hsmall : 4 * J.card + 2 * s ≤ W.card := by
      have hR : 4 * (J.card : ℝ) + 2 * (s : ℝ) + 2 ≤ (n : ℝ) := by
        unfold b_const at hJ hs; nlinarith
      have : 4 * J.card + 2 * s + 2 ≤ n := by exact_mod_cast hR
      omega
    have hexp := descFactorial_ratio_ge_exp (m := W.card) (k := J.card) (r := s) (by omega) hsmall
    have hpos_df : (0 : ℝ) < (W.card.descFactorial s : ℝ) := by
      exact_mod_cast Nat.descFactorial_pos.mpr hs_le_W
    refine le_trans ?_ (hexp.trans (div_le_div_of_nonneg_right hmono hpos_df.le))
    unfold c_avoid
    apply Real.exp_le_exp.mpr
    have hW_ge : (n : ℝ) / 2 ≤ (W.card : ℝ) := by
      have : n ≤ 2 * W.card := by omega
      have hR : (n : ℝ) ≤ 2 * (W.card : ℝ) := by exact_mod_cast this
      linarith
    have hW_pos : (0 : ℝ) < (W.card : ℝ) := by linarith
    have hnum : (J.card : ℝ) * (s : ℝ) ≤ 64 * (n : ℝ) := by
      unfold b_const at hJ hs; nlinarith
    have hdiv : 4 * (J.card : ℝ) * (s : ℝ) / (W.card : ℝ) ≤ 2200 := by
      rw [div_le_iff₀ hW_pos]; nlinarith
    have hneg : -4 * (J.card : ℝ) * (s : ℝ) / (W.card : ℝ) = -(4 * (J.card : ℝ) * (s : ℝ) / (W.card : ℝ)) := by ring
    linarith
  let EZ : ℝ := (∑ T ∈ P, Z T) / (P.card : ℝ)
  have hEZ_ge : c_avoid * δ_const / 2 ≤ EZ := by
    have h1 : c_avoid * ((C'.card : ℝ) / (Ω.card : ℝ)) ≤ EZ := by
      dsimp only [EZ]; rw [hEZ_eq, mul_div_assoc']
      apply div_le_div_of_nonneg_right _ hΩ_pos.le
      calc c_avoid * (C'.card : ℝ) = ∑ _γ ∈ C', c_avoid := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ ∑ γ ∈ C', pAvoid (J.image γ.1) := Finset.sum_le_sum hpAvoid_ge
    have h2 : δ_const / 2 ≤ (C'.card : ℝ) / (Ω.card : ℝ) := by
      have hsmall : 2 * (J.card : ℝ) / ((n : ℝ) - 1) ≤ δ_const / 2 := by
        have hnm1 : (n : ℝ) / 2 ≤ (n : ℝ) - 1 := by linarith
        have h1 : 2 * (J.card : ℝ) ≤ 16 * Real.sqrt (n : ℝ) := by unfold b_const at hJ; linarith
        have h2 : 100 ≤ δ_const * Real.sqrt (n : ℝ) := by
          have := (div_le_iff₀ δ_const_pos).mp hbig; linarith
        rw [div_le_iff₀ hnm1_pos]
        nlinarith [hsq_sq, δ_const_pos]
      linarith
    have := mul_le_mul_of_nonneg_left h2 c_avoid_pos.le
    linarith
  -- Step 3: Second moment EZ2 ≤ EZ^2 + 300 / n^(1/4)
  have hEZ2_eq : (∑ T ∈ P, (Z T) ^ 2) / (P.card : ℝ) =
      (∑ γ₁ ∈ C', ∑ γ₂ ∈ C', pAvoid (J.image γ₁.1 ∪ J.image γ₂.1)) / ((Ω.card : ℝ) ^ 2) := by
    have hswap : ∑ T ∈ P, (((C'.filter fun γ => Disjoint (J.image γ.1) T).card : ℝ) ^ 2) =
        ∑ γ₁ ∈ C', ∑ γ₂ ∈ C', ((W \ (J.image γ₁.1 ∪ J.image γ₂.1)).card.choose s : ℝ) := by
      have hsq_card : ∀ T ∈ P, (((C'.filter fun γ => Disjoint (J.image γ.1) T).card : ℝ) ^ 2) =
          ∑ γ₁ ∈ C', ∑ γ₂ ∈ C', if Disjoint (J.image γ₁.1 ∪ J.image γ₂.1) T then (1 : ℝ) else 0 := by
        intro T _
        rw [sq, Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun γ₁ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun γ₂ _ => ?_
        by_cases h1 : Disjoint (J.image γ₁.1) T <;> by_cases h2 : Disjoint (J.image γ₂.1) T <;>
          simp [Finset.disjoint_union_left, h1, h2]
      rw [Finset.sum_congr rfl hsq_card, Finset.sum_comm]
      refine Finset.sum_congr rfl fun γ₁ _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun γ₂ _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast card_powersetCard_disjoint W (J.image γ₁.1 ∪ J.image γ₂.1) s
    simp_rw [hZ_eq, div_pow, ← Finset.sum_div, hswap, pAvoid, ← Finset.sum_div]
    rw [div_div, div_div, mul_comm ((Ω.card : ℝ) ^ 2) (P.card : ℝ)]
  -- Average intersection size ∑_{γ₁, γ₂ ∈ Ω} |(J.image γ₁) ∩ (J.image γ₂)| ≤ (|J|^2 / (n - 1)) * |Ω|^2
  have hinter_sum : (∑ γ₁ ∈ Ω, ∑ γ₂ ∈ Ω, (((J.image γ₁.1) ∩ (J.image γ₂.1)).card : ℝ)) ≤
      ((J.card : ℝ) ^ 2 / ((n : ℝ) - 1)) * ((Ω.card : ℝ) ^ 2) := by
    have hcard_inter : ∀ γ₁ γ₂ : Alt n, (((J.image γ₁.1) ∩ (J.image γ₂.1)).card : ℝ) =
        ∑ a ∈ J, ∑ b ∈ J, if γ₁.1 a = γ₂.1 b then (1 : ℝ) else 0 := by
      intro γ₁ γ₂
      have hbij : ((J.image γ₁.1) ∩ (J.image γ₂.1)).card =
          ((J ×ˢ J).filter fun ab => γ₁.1 ab.1 = γ₂.1 ab.2).card := by
        refine Finset.card_bij (fun z hz => (γ₁.1.symm z, γ₂.1.symm z)) ?_ ?_ ?_
        · intro z hz
          obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hz
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h1
          obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp h2
          refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
          · simpa using ha
          · rw [← heq]; simpa using hb
          · simp
        · intro z₁ _ z₂ _ h; exact γ₁.1.symm.injective (congrArg Prod.fst h)
        · intro ab hab
          obtain ⟨habp, heq⟩ := Finset.mem_filter.mp hab
          obtain ⟨ha, hb⟩ := Finset.mem_product.mp habp
          exact ⟨γ₁.1 ab.1, Finset.mem_inter.mpr ⟨Finset.mem_image_of_mem _ ha,
            heq ▸ Finset.mem_image_of_mem _ hb⟩, Prod.ext (by simp) (by rw [heq]; simp)⟩
      rw [hbij, Finset.card_filter, Finset.sum_product, Nat.cast_sum]
      refine Finset.sum_congr rfl fun a _ => by rw [Nat.cast_sum]; refine Finset.sum_congr rfl fun b _ => by split_ifs <;> simp
    simp_rw [hcard_inter]
    have hswap2 : ∑ a ∈ J, ∑ γ₁ ∈ Ω, ∑ γ₂ ∈ Ω, ∑ b ∈ J, (if γ₁.1 a = γ₂.1 b then (1 : ℝ) else 0) =
        ∑ a ∈ J, ∑ b ∈ J, ∑ γ₁ ∈ Ω, ((Ω.filter fun γ₂ => γ₂.1 b = γ₁.1 a).card : ℝ) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      have h1 : ∀ γ₂ ∈ Ω, ∑ γ₁ ∈ Ω, ∑ b ∈ J, (if γ₁.1 a = γ₂.1 b then (1 : ℝ) else 0) =
          ∑ b ∈ J, ∑ γ₁ ∈ Ω, (if γ₁.1 a = γ₂.1 b then (1 : ℝ) else 0) := fun _ _ => Finset.sum_comm
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun γ₁ _ => ?_
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun γ₂ _ => by by_cases h : γ₁.1 a = γ₂.1 b <;> simp [h, eq_comm]
    -- Fix first swap order cleanly
    have hLHS : ∑ γ₁ ∈ Ω, ∑ γ₂ ∈ Ω, ∑ a ∈ J, ∑ b ∈ J, (if γ₁.1 a = γ₂.1 b then (1 : ℝ) else 0) =
        ∑ a ∈ J, ∑ b ∈ J, ∑ γ₁ ∈ Ω, ((Ω.filter fun γ₂ => γ₂.1 b = γ₁.1 a).card : ℝ) := by
      calc ∑ γ₁ ∈ Ω, ∑ γ₂ ∈ Ω, ∑ a ∈ J, ∑ b ∈ J, (if γ₁.1 a = γ₂.1 b then (1 : ℝ) else 0)
          = ∑ γ₁ ∈ Ω, ∑ a ∈ J, ∑ γ₂ ∈ Ω, ∑ b ∈ J, (if γ₁.1 a = γ₂.1 b then (1 : ℝ) else 0) :=
              Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = ∑ a ∈ J, ∑ γ₁ ∈ Ω, ∑ γ₂ ∈ Ω, ∑ b ∈ J, (if γ₁.1 a = γ₂.1 b then (1 : ℝ) else 0) := Finset.sum_comm
        _ = _ := hswap2
    rw [hLHS]
    have hinner : ∀ a ∈ J, ∀ b ∈ J, ∀ γ₁ ∈ Ω,
        ((Ω.filter fun γ₂ => γ₂.1 b = γ₁.1 a).card : ℝ) ≤ (Ω.card : ℝ) / ((n : ℝ) - 1) := by
      intro a ha b hb γ₁ hγ₁
      have hax : x ≠ a := fun e => hxJ (e ▸ ha)
      have hbx : x ≠ b := fun e => hxJ (e ▸ hb)
      have hγ₁x : γ₁.1 x = v := (Finset.mem_filter.mp hγ₁).2
      have hne_v : v ≠ γ₁.1 a := fun e => hax (γ₁.1.injective (hγ₁x.trans e))
      have hfilt : Ω.filter (fun γ₂ => γ₂.1 b = γ₁.1 a) =
          Finset.univ.filter (fun γ₂ : Alt n => γ₂.1 x = v ∧ γ₂.1 b = γ₁.1 a) := by
        ext γ₂; simp [Ω]
      rw [hfilt]
      have h1 := μ_fiber2 (by omega) hbx hne_v
      have h2 := μ_fiber1 (by omega) x v
      have hpos_alt : (0 : ℝ) < (Fintype.card (Alt n) : ℝ) := by exact_mod_cast card_alt_pos (by omega)
      unfold μ at h1 h2
      have hΩ_eq : (Ω.card : ℝ) = (Fintype.card (Alt n) : ℝ) / (n : ℝ) := by
        change ((Finset.univ.filter fun γ : Alt n => γ.1 x = v).card : ℝ) = _
        rw [eq_div_iff hn_pos.ne']; linarith [(div_eq_div_iff hpos_alt.ne' hn_pos.ne').mp h2]
      have hfib_eq : ((Finset.univ.filter fun γ : Alt n => γ.1 x = v ∧ γ.1 b = γ₁.1 a).card : ℝ) =
          (Fintype.card (Alt n) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
        rw [eq_div_iff (by positivity)]
        have hnm1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
        linarith [(div_eq_div_iff hpos_alt.ne' (mul_pos hn_pos hnm1).ne').mp h1]
      rw [hfib_eq, hΩ_eq, div_div]
    calc ∑ a ∈ J, ∑ b ∈ J, ∑ γ₁ ∈ Ω, ((Ω.filter fun γ₂ => γ₂.1 b = γ₁.1 a).card : ℝ)
        ≤ ∑ _a ∈ J, ∑ _b ∈ J, ∑ _γ₁ ∈ Ω, ((Ω.card : ℝ) / ((n : ℝ) - 1)) :=
          Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => Finset.sum_le_sum fun γ₁ hγ₁ =>
            hinner a ha b hb γ₁ hγ₁
      _ = ((J.card : ℝ) ^ 2 / ((n : ℝ) - 1)) * ((Ω.card : ℝ) ^ 2) := by
          simp only [Finset.sum_const, nsmul_eq_mul]; ring
  -- Split pairs (γ₁, γ₂) ∈ C' × C' by q = |(J.image γ₁) ∩ (J.image γ₂)| ≤ n^(1/4)
  have hEZ2_le : (∑ T ∈ P, (Z T) ^ 2) / (P.card : ℝ) ≤
      EZ ^ 2 + (300 : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [hEZ2_eq]
    let Q := (C' ×ˢ C').filter fun g => (n : ℝ) ^ ((1 : ℝ) / 4) < (((J.image g.1.1) ∩ (J.image g.2.1)).card : ℝ)
    have hQ_markov : (Q.card : ℝ) / ((Ω.card : ℝ) ^ 2) ≤ (100 : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 4) := by
      have hQ_sum : (Q.card : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4) ≤
          ∑ γ₁ ∈ Ω, ∑ γ₂ ∈ Ω, (((J.image γ₁.1) ∩ (J.image γ₂.1)).card : ℝ) := by
        have hsub_Ω : Q ⊆ Ω ×ˢ Ω := fun g hg => by
          have hgC := (Finset.mem_filter.mp hg).1
          obtain ⟨h1, h2⟩ := Finset.mem_product.mp hgC
          exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC_sub _ (Finset.mem_filter.mp h1).1⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC_sub _ (Finset.mem_filter.mp h2).1⟩⟩
        calc (Q.card : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4)
            = ∑ _g ∈ Q, (n : ℝ) ^ ((1 : ℝ) / 4) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ g ∈ Q, (((J.image g.1.1) ∩ (J.image g.2.1)).card : ℝ) :=
              Finset.sum_le_sum fun g hg => (Finset.mem_filter.mp hg).2.le
          _ ≤ ∑ g ∈ Ω ×ˢ Ω, (((J.image g.1.1) ∩ (J.image g.2.1)).card : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub_Ω fun _ _ _ => Nat.cast_nonneg _
          _ = ∑ γ₁ ∈ Ω, ∑ γ₂ ∈ Ω, (((J.image γ₁.1) ∩ (J.image γ₂.1)).card : ℝ) := Finset.sum_product ..
      have hle1 := hQ_sum.trans hinter_sum
      have hJ2 : (J.card : ℝ) ^ 2 / ((n : ℝ) - 1) ≤ 100 := by
        rw [div_le_iff₀ (by linarith)]
        have : (J.card : ℝ) ≤ 8 * Real.sqrt (n : ℝ) := by unfold b_const at hJ; exact hJ
        have : (100000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        nlinarith [hsq_sq]
      have hle2 : (Q.card : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ 100 * ((Ω.card : ℝ) ^ 2) :=
        hle1.trans (mul_le_mul_of_nonneg_right hJ2 (by positivity))
      rw [div_le_div_iff₀ (by positivity) hn4_pos]
      linarith
    have hpair_good : ∀ γ₁ ∈ C', ∀ γ₂ ∈ C',
        (((J.image γ₁.1) ∩ (J.image γ₂.1)).card : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) →
        pAvoid (J.image γ₁.1 ∪ J.image γ₂.1) ≤
          (1 + 200 / (n : ℝ) ^ ((1 : ℝ) / 4)) * (pAvoid (J.image γ₁.1) * pAvoid (J.image γ₂.1)) := by
      intro γ₁ _ γ₂ _ hq_le
      let A₁ := J.image γ₁.1 ∩ W
      let A₂ := J.image γ₂.1 ∩ W
      have hA1_card : A₁.card ≤ J.card := (Finset.card_le_card Finset.inter_subset_left).trans Finset.card_image_le
      have hA2_card : A₂.card ≤ J.card := (Finset.card_le_card Finset.inter_subset_left).trans Finset.card_image_le
      have hq_card : (A₁ ∩ A₂).card ≤ ((J.image γ₁.1) ∩ (J.image γ₂.1)).card :=
        Finset.card_le_card (Finset.inter_subset_inter Finset.inter_subset_left Finset.inter_subset_left)
      have hW_sdiff1 : (W \ J.image γ₁.1).card = W.card - A₁.card := by
        have h := Finset.card_sdiff_add_card_inter W (J.image γ₁.1)
        have hcomm : (W ∩ J.image γ₁.1).card = A₁.card := by rw [Finset.inter_comm]
        omega
      have hW_sdiff2 : (W \ J.image γ₂.1).card = W.card - A₂.card := by
        have h := Finset.card_sdiff_add_card_inter W (J.image γ₂.1)
        have hcomm : (W ∩ J.image γ₂.1).card = A₂.card := by rw [Finset.inter_comm]
        omega
      have hW_sdiff12 : (W \ (J.image γ₁.1 ∪ J.image γ₂.1)).card = W.card - (A₁.card + A₂.card - (A₁ ∩ A₂).card) := by
        have h := Finset.card_sdiff_add_card_inter W (J.image γ₁.1 ∪ J.image γ₂.1)
        have hun : W ∩ (J.image γ₁.1 ∪ J.image γ₂.1) = A₁ ∪ A₂ := by
          ext z; simp only [A₁, A₂, Finset.mem_inter, Finset.mem_union]; tauto
        have hcu := Finset.card_union_add_card_inter A₁ A₂
        rw [hun] at h; omega
      dsimp only [pAvoid, P]
      rw [Finset.card_powersetCard, choose_div_choose_eq_descFactorial hs_le_W,
        choose_div_choose_eq_descFactorial hs_le_W, choose_div_choose_eq_descFactorial hs_le_W,
        hW_sdiff1, hW_sdiff2, hW_sdiff12]
      have hsmall4 : 4 * (A₁.card + A₂.card + s) ≤ W.card := by
        have hR : 4 * ((A₁.card : ℝ) + (A₂.card : ℝ) + (s : ℝ)) + 2 ≤ (n : ℝ) := by
          have h1 : (A₁.card : ℝ) ≤ (J.card : ℝ) := by exact_mod_cast hA1_card
          have h2 : (A₂.card : ℝ) ≤ (J.card : ℝ) := by exact_mod_cast hA2_card
          unfold b_const at hJ hs; nlinarith
        have : 4 * (A₁.card + A₂.card + s) + 2 ≤ n := by exact_mod_cast hR
        omega
      have hdu := descFactorial_union_le (m := W.card) (r₁ := A₁.card) (r₂ := A₂.card)
        (q := (A₁ ∩ A₂).card) (s := s) (by omega) hsmall4
        (Finset.card_le_card Finset.inter_subset_left) (Finset.card_le_card Finset.inter_subset_right)
      have hexp_le : Real.exp (4 * (s : ℝ) * ((A₁ ∩ A₂).card : ℝ) / (W.card : ℝ)) ≤
          1 + 200 / (n : ℝ) ^ ((1 : ℝ) / 4) := by
        have harg : 4 * (s : ℝ) * ((A₁ ∩ A₂).card : ℝ) / (W.card : ℝ) ≤ 64 / (n : ℝ) ^ ((1 : ℝ) / 4) := by
          have hW_ge : (n : ℝ) / 2 ≤ (W.card : ℝ) := by
            have : n ≤ 2 * W.card := by omega
            have hR : (n : ℝ) ≤ 2 * (W.card : ℝ) := by exact_mod_cast this
            linarith
          have hW_pos : (0 : ℝ) < (W.card : ℝ) := by linarith
          have hqR : ((A₁ ∩ A₂).card : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) :=
            (Nat.cast_le.mpr hq_card).trans hq_le
          have hsR : (s : ℝ) ≤ 8 * Real.sqrt (n : ℝ) := by unfold b_const at hs; exact hs
          rw [div_le_div_iff₀ hW_pos hn4_pos]
          have hmul : (n : ℝ) ^ ((1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4) = Real.sqrt (n : ℝ) := by
            rw [← sq, hn4_sq]
          have hstep1 : 4 * (s : ℝ) * ((A₁ ∩ A₂).card : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4) ≤
              4 * (8 * Real.sqrt (n : ℝ)) * (n : ℝ) ^ ((1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4) := by
            have : 0 ≤ 4 * (s : ℝ) := by positivity
            have h1 := mul_le_mul_of_nonneg_left hqR this
            have h2 := mul_le_mul_of_nonneg_right hsR (show (0 : ℝ) ≤ 4 * (n : ℝ) ^ ((1 : ℝ) / 4) by positivity)
            nlinarith [hn4_pos]
          have hstep2 : 4 * (8 * Real.sqrt (n : ℝ)) * (n : ℝ) ^ ((1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4) =
              32 * (n : ℝ) := by
            calc _ = 32 * (Real.sqrt (n : ℝ) * ((n : ℝ) ^ ((1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4))) := by ring
              _ = 32 * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by rw [hmul]
              _ = 32 * (n : ℝ) := by rw [hsq_sq]
          nlinarith
        have h3x : Real.exp (64 / (n : ℝ) ^ ((1 : ℝ) / 4)) ≤ 1 + 200 / (n : ℝ) ^ ((1 : ℝ) / 4) := by
          have hx : 64 / (n : ℝ) ^ ((1 : ℝ) / 4) ≤ 2 / 3 := by
            rw [div_le_div_iff₀ hn4_pos (by norm_num)]; linarith
          have h1 : 1 - 64 / (n : ℝ) ^ ((1 : ℝ) / 4) ≤ Real.exp (-(64 / (n : ℝ) ^ ((1 : ℝ) / 4))) := by
            have := Real.add_one_le_exp (-(64 / (n : ℝ) ^ ((1 : ℝ) / 4))); linarith
          rw [Real.exp_neg] at h1
          have hpos_l : 0 < 1 - 64 / (n : ℝ) ^ ((1 : ℝ) / 4) := by linarith
          have hinv : Real.exp (64 / (n : ℝ) ^ ((1 : ℝ) / 4)) ≤ (1 - 64 / (n : ℝ) ^ ((1 : ℝ) / 4))⁻¹ := by
            rw [← inv_inv (Real.exp _)]
            exact inv_anti₀ hpos_l h1
          have hbound_inv : (1 - 64 / (n : ℝ) ^ ((1 : ℝ) / 4))⁻¹ ≤ 1 + 200 / (n : ℝ) ^ ((1 : ℝ) / 4) := by
            rw [inv_le_iff_one_le_mul₀ hpos_l]
            have h200 : 200 / (n : ℝ) ^ ((1 : ℝ) / 4) = (25 / 8 : ℝ) * (64 / (n : ℝ) ^ ((1 : ℝ) / 4)) := by ring
            rw [h200]
            nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 64) hn4_pos.le]
          exact hinv.trans hbound_inv
        exact (Real.exp_le_exp.mpr harg).trans h3x
      calc _ ≤ _ := hdu
        _ ≤ _ := by
          rw [mul_comm (1 + 200 / (n : ℝ) ^ ((1 : ℝ) / 4))]
          exact mul_le_mul_of_nonneg_left hexp_le (by positivity)
    have hsum_split : (∑ γ₁ ∈ C', ∑ γ₂ ∈ C', pAvoid (J.image γ₁.1 ∪ J.image γ₂.1)) ≤
        (1 + 200 / (n : ℝ) ^ ((1 : ℝ) / 4)) * (∑ γ₁ ∈ C', pAvoid (J.image γ₁.1)) ^ 2 + (Q.card : ℝ) := by
      rw [← Finset.sum_product']
      have hterm : ∀ g ∈ C' ×ˢ C', pAvoid (J.image g.1.1 ∪ J.image g.2.1) ≤
          (1 + 200 / (n : ℝ) ^ ((1 : ℝ) / 4)) * (pAvoid (J.image g.1.1) * pAvoid (J.image g.2.1)) +
          (if g ∈ Q then (1 : ℝ) else 0) := by
        intro g hg
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hg
        by_cases hq : g ∈ Q
        · rw [if_pos hq]
          have hp1 : pAvoid (J.image g.1.1 ∪ J.image g.2.1) ≤ 1 := by
            dsimp only [pAvoid, P]
            rw [div_le_one hP_pos, Finset.card_powersetCard]
            exact_mod_cast Nat.choose_le_choose s (Finset.card_le_card Finset.sdiff_subset)
          have hnn : 0 ≤ (1 + 200 / (n : ℝ) ^ ((1 : ℝ) / 4)) * (pAvoid (J.image g.1.1) * pAvoid (J.image g.2.1)) := by
            dsimp only [pAvoid]; positivity
          linarith
        · rw [if_neg hq, add_zero]
          have hq_le : (((J.image g.1.1) ∩ (J.image g.2.1)).card : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := by
            simp only [Q, Finset.mem_filter, hg, true_and, not_lt] at hq; exact hq
          exact hpair_good g.1 h1 g.2 h2 hq_le
      calc ∑ g ∈ C' ×ˢ C', pAvoid (J.image g.1.1 ∪ J.image g.2.1)
          ≤ ∑ g ∈ C' ×ˢ C', ((1 + 200 / (n : ℝ) ^ ((1 : ℝ) / 4)) * (pAvoid (J.image g.1.1) * pAvoid (J.image g.2.1)) +
              if g ∈ Q then (1 : ℝ) else 0) := Finset.sum_le_sum hterm
        _ = (1 + 200 / (n : ℝ) ^ ((1 : ℝ) / 4)) * (∑ γ₁ ∈ C', pAvoid (J.image γ₁.1)) ^ 2 + (Q.card : ℝ) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_product, sq, Finset.sum_mul]
            congr 1
            · congr 1; refine Finset.sum_congr rfl fun γ₁ _ => by dsimp only; rw [← Finset.mul_sum]
            · rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (Finset.filter_subset _ _),
                Finset.sum_const, nsmul_eq_mul, mul_one]
    have hEZ_le1 : EZ ≤ 1 := by
      dsimp only [EZ]
      rw [div_le_one hP_pos]
      calc ∑ T ∈ P, Z T ≤ ∑ _T ∈ P, (1 : ℝ) := Finset.sum_le_sum fun T _ => by
              dsimp only [Z]
              rw [div_le_one hΩ_pos]
              have hsub : C.filter (fun γ => ∀ a ∈ J, γ.1 a ∉ D ∪ T) ⊆ Ω := fun γ hγ =>
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC_sub γ (Finset.mem_filter.mp hγ).1⟩
              exact_mod_cast Finset.card_le_card hsub
        _ = (P.card : ℝ) := by simp
    have hEZ_sq_eq : ((∑ γ₁ ∈ C', pAvoid (J.image γ₁.1)) ^ 2) / ((Ω.card : ℝ) ^ 2) = EZ ^ 2 := by
      dsimp only [EZ]; rw [hEZ_eq, div_pow]
    have hΩ_sq_nn : (0 : ℝ) ≤ (Ω.card : ℝ) ^ 2 := sq_nonneg _
    calc (∑ γ₁ ∈ C', ∑ γ₂ ∈ C', pAvoid (J.image γ₁.1 ∪ J.image γ₂.1)) / ((Ω.card : ℝ) ^ 2)
        ≤ ((1 + 200 / (n : ℝ) ^ ((1 : ℝ) / 4)) * (∑ γ₁ ∈ C', pAvoid (J.image γ₁.1)) ^ 2 + (Q.card : ℝ)) / ((Ω.card : ℝ) ^ 2) :=
          div_le_div_of_nonneg_right hsum_split hΩ_sq_nn
      _ = (1 + 200 / (n : ℝ) ^ ((1 : ℝ) / 4)) * EZ ^ 2 + (Q.card : ℝ) / ((Ω.card : ℝ) ^ 2) := by
          rw [add_div, mul_div_assoc, hEZ_sq_eq]
      _ ≤ EZ ^ 2 + 200 / (n : ℝ) ^ ((1 : ℝ) / 4) + 100 / (n : ℝ) ^ ((1 : ℝ) / 4) := by
          have hEZ0 : 0 ≤ EZ := by
            dsimp only [EZ]; exact div_nonneg (Finset.sum_nonneg fun _ _ => by dsimp only [Z]; positivity) hP_pos.le
          have hsq1 : EZ ^ 2 ≤ 1 := by
            calc EZ ^ 2 = EZ * EZ := sq EZ
              _ ≤ 1 * 1 := mul_le_mul hEZ_le1 hEZ_le1 hEZ0 zero_le_one
              _ = 1 := one_mul 1
          have h1 : (200 / (n : ℝ) ^ ((1 : ℝ) / 4)) * EZ ^ 2 ≤ 200 / (n : ℝ) ^ ((1 : ℝ) / 4) :=
            mul_le_of_le_one_right (div_nonneg (by norm_num) hn4_pos.le) hsq1
          have h3 : (1 + 200 / (n : ℝ) ^ ((1 : ℝ) / 4)) * EZ ^ 2 =
              EZ ^ 2 + (200 / (n : ℝ) ^ ((1 : ℝ) / 4)) * EZ ^ 2 := by
            rw [add_mul, one_mul]
          rw [h3]
          exact add_le_add (add_le_add le_rfl h1) hQ_markov
      _ = EZ ^ 2 + 300 / (n : ℝ) ^ ((1 : ℝ) / 4) := by
          rw [add_assoc, ← add_div]; norm_num
  -- Step 4: Chebyshev's inequality
  let Bad := P.filter fun T => Z T ≤ η_const
  have hgap : c_avoid * δ_const / 4 ≤ EZ - η_const := by
    unfold η_const
    have hcd : 0 < c_avoid * δ_const := mul_pos c_avoid_pos δ_const_pos
    linarith [hEZ_ge]
  have hvar : (∑ T ∈ P, (Z T - EZ) ^ 2) / (P.card : ℝ) ≤ (300 : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 4) := by
    have hexpand : ∑ T ∈ P, (Z T - EZ) ^ 2 = (∑ T ∈ P, (Z T) ^ 2) - (P.card : ℝ) * EZ ^ 2 := by
      have h1 : ∑ T ∈ P, (Z T - EZ) ^ 2 = ∑ T ∈ P, ((Z T) ^ 2 - 2 * EZ * Z T + EZ ^ 2) :=
        Finset.sum_congr rfl fun T _ => by ring
      rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      have hEZ_sum : ∑ T ∈ P, Z T = (P.card : ℝ) * EZ := by
        dsimp only [EZ]; rw [mul_div_cancel₀ _ hP_pos.ne']
      rw [hEZ_sum]; ring
    rw [hexpand, sub_div, mul_div_cancel_left₀ _ hP_pos.ne']
    linarith
  have hcheb : ((Bad.card : ℝ) / (P.card : ℝ)) * (c_avoid * δ_const / 4) ^ 2 ≤
      (∑ T ∈ P, (Z T - EZ) ^ 2) / (P.card : ℝ) := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hP_pos.le
    calc (Bad.card : ℝ) * (c_avoid * δ_const / 4) ^ 2
        = ∑ _T ∈ Bad, (c_avoid * δ_const / 4) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ T ∈ Bad, (Z T - EZ) ^ 2 := Finset.sum_le_sum fun T hT => by
          have hZT : Z T ≤ η_const := (Finset.mem_filter.mp hT).2
          have hpos : 0 ≤ c_avoid * δ_const / 4 := by have := c_avoid_pos; have := δ_const_pos; positivity
          have : c_avoid * δ_const / 4 ≤ EZ - Z T := by linarith
          nlinarith
      _ ≤ ∑ T ∈ P, (Z T - EZ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _
  have hcd_pos : 0 < (c_avoid * δ_const) ^ 2 := by have := c_avoid_pos; have := δ_const_pos; positivity
  have h1 := hcheb.trans hvar
  rw [div_le_div_iff₀ hP_pos (mul_pos hcd_pos hn4_pos)]
  have h2 : (Bad.card : ℝ) * (c_avoid * δ_const / 4) ^ 2 * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ 300 * (P.card : ℝ) := by
    have := (div_le_div_iff₀ hP_pos hn4_pos).mp (by rwa [div_mul_eq_mul_div] at h1)
    linarith
  nlinarith

end InsideEdges


/-- Exact fibre count of `σ ↦ A.image σ.1` on `{σ ∈ A_n | ∀ u ∈ U, σ u = f u}`:
every `T ∈ (univ \ U.image f).powersetCard |A|` has the exact same fibre size. -/
private lemma card_alt_image_eq_const {n : ℕ} (U A T : Finset (Fin n)) (f : Fin n → Fin n)
    (hdisj : Disjoint U A) (hf : Set.InjOn f (U : Set (Fin n)))
    (hUA : U.card + A.card + 2 ≤ n)
    (hT : T ∈ (Finset.univ \ U.image f).powersetCard A.card) :
    2 * (Finset.univ.filter fun σ : Alt n => (∀ u ∈ U, σ.1 u = f u) ∧ A.image σ.1 = T).card =
      A.card.factorial * (n - (U.card + A.card)).factorial := by
  classical
  have hTsub : T ⊆ Finset.univ \ U.image f := (Finset.mem_powersetCard.mp hT).1
  have hTcard : T.card = A.card := (Finset.mem_powersetCard.mp hT).2
  let S := Finset.univ.filter fun σ : Alt n => (∀ u ∈ U, σ.1 u = f u) ∧ A.image σ.1 = T
  let piece (e : A ≃ T) : Finset (Alt n) :=
    Finset.univ.filter fun σ : Alt n =>
      ∀ u ∈ U ∪ A, σ.1 u = if hu : u ∈ U then f u else if ha : u ∈ A then (e ⟨u, ha⟩).1 else u
  have hpart : S = Finset.univ.biUnion piece := by
    ext σ
    simp only [S, piece, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · rintro ⟨hσU, hσA⟩
      have hmap : ∀ a : A, σ.1 a.1 ∈ T := fun a => hσA ▸ Finset.mem_image_of_mem σ.1 a.2
      let φ : A → T := fun a => ⟨σ.1 a.1, hmap a⟩
      have hφ_inj : Function.Injective φ := fun a₁ a₂ h => Subtype.ext (σ.1.injective (congrArg Subtype.val h))
      have hcard_eq : Fintype.card A = Fintype.card T := by simp [hTcard]
      have hφ_bij : Function.Bijective φ := (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hφ_inj, hcard_eq⟩
      refine ⟨Equiv.ofBijective φ hφ_bij, ?_⟩
      intro u hu
      by_cases huU : u ∈ U
      · simp [huU, hσU u huU]
      · have huA : u ∈ A := (Finset.mem_union.mp hu).resolve_left huU
        simp [huU, huA, φ]
    · rintro ⟨e, he⟩
      refine ⟨fun u hu => ?_, ?_⟩
      · have h1 := he u (Finset.mem_union_left A hu)
        simpa [hu] using h1
      · ext y
        simp only [Finset.mem_image]
        constructor
        · rintro ⟨a, ha, rfl⟩
          have haU : a ∉ U := Finset.disjoint_right.mp hdisj ha
          have h1 := he a (Finset.mem_union_right U ha)
          simp only [haU, ↓reduceDIte, ha] at h1
          rw [h1]
          exact (e ⟨a, ha⟩).2
        · intro hy
          refine ⟨(e.symm ⟨y, hy⟩).1, (e.symm ⟨y, hy⟩).2, ?_⟩
          have haU : (e.symm ⟨y, hy⟩).1 ∉ U := Finset.disjoint_right.mp hdisj (e.symm ⟨y, hy⟩).2
          have h1 := he (e.symm ⟨y, hy⟩).1 (Finset.mem_union_right U (e.symm ⟨y, hy⟩).2)
          simp only [haU, ↓reduceDIte, (e.symm ⟨y, hy⟩).2] at h1
          rw [h1]
          exact congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
  have hdisj_p : Set.PairwiseDisjoint (Finset.univ : Finset (A ≃ T)) piece := by
    intro e₁ _ e₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro σ h1 h2
    have he1 := (Finset.mem_filter.mp h1).2
    have he2 := (Finset.mem_filter.mp h2).2
    apply hne
    ext ⟨a, ha⟩
    have haU : a ∉ U := Finset.disjoint_right.mp hdisj ha
    have h1a := he1 a (Finset.mem_union_right U ha)
    have h2a := he2 a (Finset.mem_union_right U ha)
    simp only [haU, ↓reduceDIte, ha] at h1a h2a
    exact congrArg Fin.val (h1a.symm.trans h2a)
  have hpiece_card : ∀ e : A ≃ T, 2 * (piece e).card = (n - (U.card + A.card)).factorial := by
    intro e
    let g : Fin n → Fin n := fun u =>
      if hu : u ∈ U then f u else if ha : u ∈ A then (e ⟨u, ha⟩).1 else u
    have hginj : Set.InjOn g ((U ∪ A : Finset (Fin n)) : Set (Fin n)) := by
      intro u hu v hv huv
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hu hv
      by_cases huU : u ∈ U <;> by_cases hvU : v ∈ U
      · simp only [g, huU, hvU, ↓reduceDIte] at huv
        exact hf huU hvU huv
      · have hvA : v ∈ A := hv.resolve_left hvU
        simp only [g, huU, hvU, hvA, ↓reduceDIte] at huv
        have hmemT : f u ∈ T := huv ▸ (e ⟨v, hvA⟩).2
        exact absurd (Finset.mem_image_of_mem f huU) (Finset.mem_sdiff.mp (hTsub hmemT)).2
      · have huA : u ∈ A := hu.resolve_left huU
        simp only [g, huU, hvU, huA, ↓reduceDIte] at huv
        have hmemT : f v ∈ T := huv.symm ▸ (e ⟨u, huA⟩).2
        exact absurd (Finset.mem_image_of_mem f hvU) (Finset.mem_sdiff.mp (hTsub hmemT)).2
      · have huA : u ∈ A := hu.resolve_left huU
        have hvA : v ∈ A := hv.resolve_left hvU
        simp only [g, huU, hvU, huA, hvA, ↓reduceDIte] at huv
        have heq : (⟨u, huA⟩ : A) = ⟨v, hvA⟩ := e.injective (Subtype.ext huv)
        exact congrArg Subtype.val heq
    have hcard_UA : (U ∪ A).card = U.card + A.card := Finset.card_union_of_disjoint hdisj
    have hres := card_alt_agree_on (U ∪ A) (by omega) g hginj
    rw [hcard_UA] at hres
    exact hres
  have hsum : 2 * S.card = ∑ e : A ≃ T, 2 * (piece e).card := by
    rw [hpart, Finset.card_biUnion hdisj_p, Finset.mul_sum]
  rw [hsum]
  have hcongr : ∑ e : A ≃ T, 2 * (piece e).card = ∑ _e : A ≃ T, (n - (U.card + A.card)).factorial :=
    Finset.sum_congr rfl fun e _ => hpiece_card e
  rw [hcongr, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  congr 1
  have heq_card : Fintype.card A = Fintype.card T := by simp [hTcard]
  have hAT : Nonempty (A ≃ T) := Fintype.card_eq.mp heq_card
  obtain ⟨e0⟩ := hAT
  have hbij : Fintype.card (A ≃ T) = Fintype.card (Equiv.Perm A) :=
    Fintype.card_congr (Equiv.equivCongr (Equiv.refl A) e0.symm)
  rw [hbij, Fintype.card_perm, Fintype.card_coe]

/-- The conditional fraction of `σ ∈ A_n` agreeing with `f` on `U` whose image `A.image σ.1`
satisfies `Bad` equals the fraction of `T ∈ (univ \ U.image f).powersetCard |A|` satisfying `Bad`. -/
private lemma ratio_alt_image_bad {n : ℕ} (U A : Finset (Fin n)) (f : Fin n → Fin n)
    (hdisj : Disjoint U A) (hf : Set.InjOn f (U : Set (Fin n)))
    (hUA : U.card + A.card + 2 ≤ n) (Bad : Finset (Fin n) → Prop) [DecidablePred Bad] :
    let Ω := Finset.univ.filter fun σ : Alt n => ∀ u ∈ U, σ.1 u = f u
    let P := (Finset.univ \ U.image f).powersetCard A.card
    ((Ω.filter fun σ => Bad (A.image σ.1)).card : ℝ) / (Ω.card : ℝ) =
      ((P.filter Bad).card : ℝ) / (P.card : ℝ) := by
  classical
  intro Ω P
  have himg_mem : ∀ σ ∈ Ω, A.image σ.1 ∈ P := by
    intro σ hσ
    have hσU := (Finset.mem_filter.mp hσ).2
    rw [Finset.mem_powersetCard]
    refine ⟨?_, Finset.card_image_of_injective A σ.1.injective⟩
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hmem
    obtain ⟨u, hu, hfu⟩ := Finset.mem_image.mp hmem
    have : σ.1 u = σ.1 a := (hσU u hu).trans hfu
    exact Finset.disjoint_left.mp hdisj hu (σ.1.injective this ▸ ha)
  have hpart_bad : Ω.filter (fun σ => Bad (A.image σ.1)) =
      (P.filter Bad).biUnion fun T => Finset.univ.filter fun σ : Alt n => (∀ u ∈ U, σ.1 u = f u) ∧ A.image σ.1 = T := by
    ext σ
    simp only [Ω, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · rintro ⟨hσU, hB⟩
      exact ⟨A.image σ.1, ⟨himg_mem σ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσU⟩), hB⟩, hσU, rfl⟩
    · rintro ⟨T, ⟨_, hBT⟩, hσU, hEq⟩
      exact ⟨hσU, hEq ▸ hBT⟩
  have hpart_all : Ω =
      P.biUnion fun T => Finset.univ.filter fun σ : Alt n => (∀ u ∈ U, σ.1 u = f u) ∧ A.image σ.1 = T := by
    ext σ
    simp only [Ω, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro hσU
      exact ⟨A.image σ.1, himg_mem σ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσU⟩), hσU, rfl⟩
    · rintro ⟨T, _, hσU, _⟩
      exact hσU
  have hdisj_T : ∀ S' : Finset (Finset (Fin n)),
      Set.PairwiseDisjoint (S' : Set (Finset (Fin n)))
        (fun T => Finset.univ.filter fun σ : Alt n => (∀ u ∈ U, σ.1 u = f u) ∧ A.image σ.1 = T) := by
    intro S' T₁ _ T₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro σ h1 h2
    exact hne ((Finset.mem_filter.mp h1).2.2.symm.trans (Finset.mem_filter.mp h2).2.2)
  have hcard_bad : 2 * (Ω.filter fun σ => Bad (A.image σ.1)).card =
      (P.filter Bad).card * (A.card.factorial * (n - (U.card + A.card)).factorial) := by
    rw [hpart_bad, Finset.card_biUnion (hdisj_T _), Finset.mul_sum]
    rw [Finset.sum_congr rfl fun T hT =>
      card_alt_image_eq_const U A T f hdisj hf hUA (Finset.mem_filter.mp hT).1]
    rw [Finset.sum_const, smul_eq_mul]
  have hcard_all : 2 * Ω.card =
      P.card * (A.card.factorial * (n - (U.card + A.card)).factorial) := by
    rw [hpart_all, Finset.card_biUnion (hdisj_T _), Finset.mul_sum]
    rw [Finset.sum_congr rfl fun T hT => card_alt_image_eq_const U A T f hdisj hf hUA hT]
    rw [Finset.sum_const, smul_eq_mul]
  have hK_pos : (0 : ℝ) < (A.card.factorial * (n - (U.card + A.card)).factorial : ℕ) := by
    exact_mod_cast Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  have hP_pos : (0 : ℝ) < (P.card : ℝ) := by
    have hcard_sdiff : (Finset.univ \ U.image f).card = n - U.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
        Finset.card_image_of_injOn hf]
    have hPcard : P.card = (n - U.card).choose A.card := by rw [Finset.card_powersetCard, hcard_sdiff]
    rw [hPcard]
    exact_mod_cast Nat.choose_pos (by omega)
  have hΩ_pos : (0 : ℝ) < (Ω.card : ℝ) := by
    have h2 : (2 : ℝ) * (Ω.card : ℝ) = (P.card : ℝ) * ((A.card.factorial * (n - (U.card + A.card)).factorial : ℕ) : ℝ) := by
      exact_mod_cast hcard_all
    nlinarith
  rw [div_eq_div_iff hΩ_pos.ne' hP_pos.ne']
  have hbR : (2 : ℝ) * ((Ω.filter fun σ => Bad (A.image σ.1)).card : ℝ) =
      ((P.filter Bad).card : ℝ) * ((A.card.factorial * (n - (U.card + A.card)).factorial : ℕ) : ℝ) := by
    exact_mod_cast hcard_bad
  have haR : (2 : ℝ) * (Ω.card : ℝ) =
      (P.card : ℝ) * ((A.card.factorial * (n - (U.card + A.card)).factorial : ℕ) : ℝ) := by
    exact_mod_cast hcard_all
  nlinarith

/- ### Section 4: Thresholded Set `J`, Inside Edges, and Outside Targets -/

section MainProof

private lemma μ_biUnion_of_disjoint {n : ℕ} {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {f : ι → Finset (Alt n)}
    (h : Set.PairwiseDisjoint (s : Set ι) f) :
    μ (s.biUnion f) = ∑ i ∈ s, μ (f i) := by
  unfold μ
  rw [Finset.card_biUnion h, Nat.cast_sum, Finset.sum_div]

/-- No element of a large product-free set `S` close to `F_I^x` can fix `x`. -/
private lemma no_fix_x {n : ℕ} (hn : 100000 ≤ n) (S : Finset (Alt n))
    (hpf : ProdFree (S : Set (Alt n))) (x : Fin n) (I : Finset (Fin n))
    (hxI : x ∉ I) (hI_lo : 2 * a_const * Real.sqrt (n : ℝ) ≤ (I.card : ℝ))
    (hI_hi : (I.card : ℝ) ≤ (b_const / 2) * Real.sqrt (n : ℝ))
    (hD : μ ((Finset.univ.filter fun π : Alt n => π.1 x ∈ I ∧ ∀ a ∈ I, π.1 a ∉ I) \ S) <
      c_avoid * a_const / Real.sqrt (n : ℝ)) :
    ∀ σ ∈ S, σ.1 x ≠ x := by
  classical
  let F_I := Finset.univ.filter fun π : Alt n => π.1 x ∈ I ∧ ∀ a ∈ I, π.1 a ∉ I
  intro σ hσ hfix
  let A := I ∪ I.image σ.1
  let G := Finset.univ.filter fun α : Alt n => α.1 x ∈ I ∧ ∀ a ∈ A, α.1 a ∉ I
  have hxA : x ∉ A := by
    intro hx
    rcases Finset.mem_union.mp hx with h1 | h2
    · exact hxI h1
    · obtain ⟨a, ha, haeq⟩ := Finset.mem_image.mp h2
      exact hxI (σ.1.injective (haeq.trans hfix.symm) ▸ ha)
  have hA_card : (A.card : ℝ) ≤ 16 * Real.sqrt (n : ℝ) := by
    have h1 : A.card ≤ I.card + (I.image σ.1).card := Finset.card_union_le _ _
    have h2 : (I.image σ.1).card = I.card := Finset.card_image_of_injective _ σ.1.injective
    have h3 : (A.card : ℝ) ≤ 2 * (I.card : ℝ) := by exact_mod_cast (by omega : A.card ≤ 2 * I.card)
    unfold b_const at hI_hi
    linarith
  have hI_card : (I.card : ℝ) ≤ 16 * Real.sqrt (n : ℝ) := by
    unfold b_const at hI_hi; linarith
  have hG_lower : 2 * c_avoid * a_const / Real.sqrt (n : ℝ) ≤ μ G := by
    have hpart : G = I.biUnion fun y =>
        Finset.univ.filter fun α : Alt n => (∀ u ∈ ({x} : Finset (Fin n)), α.1 u = y) ∧ ∀ a ∈ A, α.1 a ∉ I := by
      ext α
      simp only [G, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨α.1 x, h1, fun u hu => by rw [hu], h2⟩
      · rintro ⟨y, hy, h1, h2⟩
        exact ⟨(h1 x rfl).symm ▸ hy, h2⟩
    have hdisj_y : Set.PairwiseDisjoint (I : Set (Fin n))
        (fun y => Finset.univ.filter fun α : Alt n => (∀ u ∈ ({x} : Finset (Fin n)), α.1 u = y) ∧ ∀ a ∈ A, α.1 a ∉ I) := by
      intro y₁ _ y₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro α h1 h2
      exact hne (((Finset.mem_filter.mp h1).2.1 x (Finset.mem_singleton_self x)).symm.trans
        ((Finset.mem_filter.mp h2).2.1 x (Finset.mem_singleton_self x)))
    have hsum : μ G = ∑ y ∈ I, μ (Finset.univ.filter fun α : Alt n =>
        (∀ u ∈ ({x} : Finset (Fin n)), α.1 u = y) ∧ ∀ a ∈ A, α.1 a ∉ I) := by
      rw [hpart, μ_biUnion_of_disjoint hdisj_y]
    have hterm : ∀ y ∈ I, c_avoid / (n : ℝ) ≤ μ (Finset.univ.filter fun α : Alt n =>
        (∀ u ∈ ({x} : Finset (Fin n)), α.1 u = y) ∧ ∀ a ∈ A, α.1 a ∉ I) := by
      intro y _
      have hdisj_xA : Disjoint ({x} : Finset (Fin n)) A := Finset.disjoint_singleton_left.mpr hxA
      have hfinj : Set.InjOn (fun _ : Fin n => y) (({x} : Finset (Fin n)) : Set (Fin n)) := by
        intro u hu v hv _; simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hu hv; exact hu.trans hv.symm
      have h1 := μ_avoid_ge_c hn {x} A I hdisj_xA (by simp) hA_card hI_card (fun _ => y) hfinj
      have hfib : μ (Finset.univ.filter fun α : Alt n => ∀ u ∈ ({x} : Finset (Fin n)), α.1 u = y) = 1 / (n : ℝ) := by
        convert μ_fiber1 (by omega) x y using 2
        ext α; simp
      rw [hfib, mul_one_div] at h1
      exact h1
    have hge_sum : (I.card : ℝ) * (c_avoid / (n : ℝ)) ≤ μ G := by
      rw [hsum]
      calc (I.card : ℝ) * (c_avoid / (n : ℝ))
          = ∑ _y ∈ I, c_avoid / (n : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum hterm
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
    have hsq_sq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn_pos.le
    have hstep : 2 * c_avoid * a_const / Real.sqrt (n : ℝ) ≤ (I.card : ℝ) * (c_avoid / (n : ℝ)) := by
      rw [mul_div_assoc', div_le_div_iff₀ hsq_pos hn_pos]
      have h1 := mul_le_mul_of_nonneg_right hI_lo c_avoid_pos.le
      have h2 := mul_le_mul_of_nonneg_right h1 hsq_pos.le
      have h3 : 2 * c_avoid * a_const * (n : ℝ) = 2 * a_const * Real.sqrt (n : ℝ) * c_avoid * Real.sqrt (n : ℝ) := by
        calc 2 * c_avoid * a_const * (n : ℝ)
            = 2 * c_avoid * a_const * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by rw [hsq_sq]
          _ = 2 * a_const * Real.sqrt (n : ℝ) * c_avoid * Real.sqrt (n : ℝ) := by ring
      linarith
    exact hstep.trans hge_sum
  have hG_upper : μ G ≤ 2 * μ (F_I \ S) := by
    let G1 := G.filter fun α => α ∉ S
    let G2 := G.filter fun α => α * σ ∉ S
    have hcov : G ⊆ G1 ∪ G2 := by
      intro α hα
      by_cases h1 : α ∈ S
      · by_cases h2 : α * σ ∈ S
        · exact absurd h2 (hpf α h1 σ hσ)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hα, h2⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hα, h1⟩)
    have hG1_sub : G1 ⊆ F_I \ S := by
      intro α hα
      have ⟨hαG, hαnS⟩ := Finset.mem_filter.mp hα
      have ⟨hxα, hAα⟩ := (Finset.mem_filter.mp hαG).2
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxα,
        fun a ha => hAα a (Finset.mem_union_left _ ha)⟩, hαnS⟩
    have hG2_sub : G2.image (fun α => α * σ) ⊆ F_I \ S := by
      intro β hβ
      obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hβ
      have ⟨hαG, hαnS⟩ := Finset.mem_filter.mp hα
      have ⟨hxα, hAα⟩ := (Finset.mem_filter.mp hαG).2
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, hαnS⟩
      · show α.1 (σ.1 x) ∈ I; rw [hfix]; exact hxα
      · intro a ha
        show α.1 (σ.1 a) ∉ I
        exact hAα (σ.1 a) (Finset.mem_union_right _ (Finset.mem_image_of_mem σ.1 ha))
    have hG2_card : G2.card ≤ (F_I \ S).card := by
      have hinj : Function.Injective (fun α : Alt n => α * σ) := mul_left_injective σ
      rw [← Finset.card_image_of_injective G2 hinj]
      exact Finset.card_le_card hG2_sub
    have hμG1 : μ G1 ≤ μ (F_I \ S) := μ_mono hG1_sub
    have hμG2 : μ G2 ≤ μ (F_I \ S) := by
      unfold μ
      exact div_le_div_of_nonneg_right (by exact_mod_cast hG2_card) (by positivity)
    calc μ G ≤ μ (G1 ∪ G2) := μ_mono hcov
      _ ≤ μ G1 + μ G2 := μ_union_le G1 G2
      _ ≤ 2 * μ (F_I \ S) := by linarith
  change μ (F_I \ S) < c_avoid * a_const / Real.sqrt (n : ℝ) at hD
  have h2D : 2 * μ (F_I \ S) < 2 * c_avoid * a_const / Real.sqrt (n : ℝ) := by
    have : 2 * (c_avoid * a_const / Real.sqrt (n : ℝ)) = 2 * c_avoid * a_const / Real.sqrt (n : ℝ) := by ring
    linarith
  linarith

set_option maxHeartbeats 800000 in
/-- Properties of the thresholded target set `J = {j | Pr(π ∈ S | π(x) = j) ≥ δ_const}`. -/
private lemma threshold_J_props {n : ℕ} (hn : 100000 ≤ n)
    (hbig : (1 + 200 / δ_const) * (n : ℝ) ^ (-(33 : ℝ) / 50) ≤ (1 / 200 : ℝ) / Real.sqrt (n : ℝ))
    (hbig2 : (2 / δ_const) * (n : ℝ) * (n : ℝ) ^ (-(33 : ℝ) / 50) ≤ a_const * Real.sqrt (n : ℝ))
    (hbig3 : (n : ℝ) ^ (-(33 : ℝ) / 50) < c_avoid * a_const / Real.sqrt (n : ℝ))
    (S : Finset (Alt n)) (hpf : ProdFree (S : Set (Alt n)))
    (hmax : ∀ (z : Fin n) (K : Finset (Fin n)),
      (Finset.univ.filter fun π : Alt n => π.1 z ∈ K ∧ ∀ a ∈ K, π.1 a ∉ K).card ≤ S.card)
    (x : Fin n) (I : Finset (Fin n))
    (happrox : μ (S \ Finset.univ.filter fun π : Alt n => π.1 x ∈ I ∧ ∀ a ∈ I, π.1 a ∉ I) <
      (n : ℝ) ^ (-(33 : ℝ) / 50)) :
    let p (j : Fin n) : ℝ :=
      ((S.filter fun π => π.1 x = j).card : ℝ) / ((Finset.univ.filter fun π : Alt n => π.1 x = j).card : ℝ)
    let J : Finset (Fin n) := Finset.univ.filter fun j => δ_const ≤ p j
    let F : Finset (Alt n) := Finset.univ.filter fun π : Alt n => π.1 x ∈ J ∧ ∀ a ∈ J, π.1 a ∉ J
    x ∉ J ∧ a_const * Real.sqrt (n : ℝ) ≤ (J.card : ℝ) ∧ (J.card : ℝ) ≤ b_const * Real.sqrt (n : ℝ) ∧
      μ (F \ S) ≤ μ (S \ F) ∧ μ (F \ S) ≤ (1 + 200 / δ_const) * (n : ℝ) ^ (-(33 : ℝ) / 50) := by
  classical
  intro p J F
  let F_I := Finset.univ.filter fun π : Alt n => π.1 x ∈ I ∧ ∀ a ∈ I, π.1 a ∉ I
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  have hcard_alt_pos : (0 : ℝ) < (Fintype.card (Alt n) : ℝ) := by exact_mod_cast card_alt_pos (by omega)
  -- Step 1: `μ (F_I \ S) ≤ μ (S \ F_I) < n^(-33/50)` and `I` size bounds
  have hDI_le : μ (F_I \ S) ≤ μ (S \ F_I) := by
    unfold μ
    apply div_le_div_of_nonneg_right _ hcard_alt_pos.le
    have h1 : F_I.card ≤ S.card := hmax x I
    have h2 : (F_I \ S).card + (F_I ∩ S).card = F_I.card := Finset.card_sdiff_add_card_inter F_I S
    have h3 : (S \ F_I).card + (S ∩ F_I).card = S.card := Finset.card_sdiff_add_card_inter S F_I
    rw [Finset.inter_comm] at h3
    exact_mod_cast (by omega : (F_I \ S).card ≤ (S \ F_I).card)
  have hDI_lt : μ (F_I \ S) < (n : ℝ) ^ (-(33 : ℝ) / 50) := hDI_le.trans_lt happrox
  have hS_lower : (1 / 32 : ℝ) / Real.sqrt (n : ℝ) ≤ μ S := by
    obtain ⟨z, K, _, hK⟩ := exists_extremal_lower (n := n) (by omega)
    refine hK.trans ?_
    unfold μ
    exact div_le_div_of_nonneg_right (by exact_mod_cast hmax z K) hcard_alt_pos.le
  have hFI_lower : (1 / 40 : ℝ) / Real.sqrt (n : ℝ) ≤ μ F_I := by
    have hsub : S ⊆ F_I ∪ (S \ F_I) := fun π hπ => by
      by_cases h : π ∈ F_I
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hπ, h⟩)
    have h1 : μ S ≤ μ F_I + μ (S \ F_I) := (μ_mono hsub).trans (μ_union_le _ _)
    have h2 : (n : ℝ) ^ (-(33 : ℝ) / 50) ≤ (1 / 200 : ℝ) / Real.sqrt (n : ℝ) := by
      have hpos : (0 : ℝ) < (n : ℝ) ^ (-(33 : ℝ) / 50) := Real.rpow_pos_of_pos hn_pos _
      have hcoef : (1 : ℝ) ≤ 1 + 200 / δ_const := by have := δ_const_pos; linarith [div_pos (show (0 : ℝ) < 200 by norm_num) this]
      nlinarith
    have h3 : (1 / 40 : ℝ) / Real.sqrt (n : ℝ) = (1 / 32 : ℝ) / Real.sqrt (n : ℝ) - (1 / 160 : ℝ) / Real.sqrt (n : ℝ) := by ring
    have h4 : (1 / 200 : ℝ) / Real.sqrt (n : ℝ) ≤ (1 / 160 : ℝ) / Real.sqrt (n : ℝ) :=
      div_le_div_of_nonneg_right (by norm_num) hsq_pos.le
    linarith
  obtain ⟨hxI, hI_lo, hI_hi⟩ := extremal_card_bounds (by omega) x I hFI_lower
  -- Step 2: `x ∉ J` via `no_fix_x`
  have hnofix : ∀ σ ∈ S, σ.1 x ≠ x := no_fix_x hn S hpf x I hxI hI_lo hI_hi (hDI_lt.trans hbig3)
  have hxJ : x ∉ J := by
    intro hx
    have hp : δ_const ≤ p x := (Finset.mem_filter.mp hx).2
    have hempty : S.filter (fun π => π.1 x = x) = ∅ := by
      ext π; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
      rintro ⟨h1, h2⟩; exact hnofix π h1 h2
    have hpx : p x = 0 := by dsimp only [p]; rw [hempty]; simp
    linarith [δ_const_pos]
  -- Step 3: `p j = n * μ (S ∩ Ω_j)`
  have hp_eq : ∀ j : Fin n, p j = (n : ℝ) * μ (S.filter fun π => π.1 x = j) := by
    intro j
    have hfib := μ_fiber1 (by omega) x j
    unfold μ at hfib ⊢
    dsimp only [p]
    have hΩ_ne : ((Finset.univ.filter fun π : Alt n => π.1 x = j).card : ℝ) ≠ 0 := by
      intro h0; rw [h0, zero_div] at hfib; exact (one_div_pos.mpr hn_pos).ne' hfib.symm
    have hΩ_eq : ((Finset.univ.filter fun π : Alt n => π.1 x = j).card : ℝ) =
        (Fintype.card (Alt n) : ℝ) / (n : ℝ) := by
      have := (div_eq_iff hcard_alt_pos.ne').mp hfib
      linarith [show (1 / (n : ℝ)) * (Fintype.card (Alt n) : ℝ) = (Fintype.card (Alt n) : ℝ) / (n : ℝ) by ring]
    rw [hΩ_eq]
    field_simp
  -- Step 4: Bound `d = |(I \ J) ∪ (J \ I)|`
  have hIJ_sdiff : ((I \ J).card : ℝ) * (δ_const / (n : ℝ)) ≤ μ (F_I \ S) := by
    have hsub : (I \ J).biUnion (fun i => (F_I \ S).filter fun π => π.1 x = i) ⊆ F_I \ S := by
      intro π hπ; obtain ⟨_, _, h2⟩ := Finset.mem_biUnion.mp hπ; exact (Finset.mem_filter.mp h2).1
    have hdisj : Set.PairwiseDisjoint ((I \ J : Finset (Fin n)) : Set (Fin n))
        (fun i => (F_I \ S).filter fun π => π.1 x = i) := by
      intro i₁ _ i₂ _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]
      intro π h1 h2; exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    have h1 : ∑ i ∈ I \ J, μ ((F_I \ S).filter fun π => π.1 x = i) ≤ μ (F_I \ S) := by
      rw [← μ_biUnion_of_disjoint hdisj]; exact μ_mono hsub
    refine le_trans ?_ h1
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun i hi => ?_
    have hiI : i ∈ I := (Finset.mem_sdiff.mp hi).1
    have hinJ : i ∉ J := (Finset.mem_sdiff.mp hi).2
    have hpi : p i < δ_const := by
      by_contra hge; push Not at hge
      exact hinJ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hge⟩)
    have hF_fib : c_avoid / (n : ℝ) ≤ μ (F_I.filter fun π => π.1 x = i) := by
      have hdisj_xI : Disjoint ({x} : Finset (Fin n)) I := Finset.disjoint_singleton_left.mpr hxI
      have hI_16 : (I.card : ℝ) ≤ 16 * Real.sqrt (n : ℝ) := by unfold b_const at hI_hi; linarith
      have hfinj : Set.InjOn (fun _ : Fin n => i) (({x} : Finset (Fin n)) : Set (Fin n)) := by
        intro u hu v hv _; simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hu hv; exact hu.trans hv.symm
      have hav := μ_avoid_ge_c hn {x} I I hdisj_xI (by simp) hI_16 hI_16 (fun _ => i) hfinj
      have hfib1 : μ (Finset.univ.filter fun π : Alt n => ∀ u ∈ ({x} : Finset (Fin n)), π.1 u = i) = 1 / (n : ℝ) := by
        convert μ_fiber1 (by omega) x i using 2; ext π; simp
      rw [hfib1] at hav
      have heq_set : (Finset.univ.filter fun π : Alt n => (∀ u ∈ ({x} : Finset (Fin n)), π.1 u = i) ∧ ∀ a ∈ I, π.1 a ∉ I) =
          F_I.filter fun π => π.1 x = i := by
        ext π; simp only [F_I, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨⟨(h1 x rfl).symm ▸ hiI, h2⟩, h1 x rfl⟩
        · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨fun u hu => hu ▸ h3, h2⟩
      rw [heq_set, mul_one_div] at hav; exact hav
    have hcov : F_I.filter (fun π => π.1 x = i) ⊆
        ((F_I \ S).filter fun π => π.1 x = i) ∪ (S.filter fun π => π.1 x = i) := by
      intro π hπ
      have ⟨hπF, hπx⟩ := Finset.mem_filter.mp hπ
      by_cases hπS : π ∈ S
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hπS, hπx⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hπF, hπS⟩, hπx⟩)
    have hle : μ (F_I.filter fun π => π.1 x = i) ≤
        μ ((F_I \ S).filter fun π => π.1 x = i) + μ (S.filter fun π => π.1 x = i) :=
      (μ_mono hcov).trans (μ_union_le _ _)
    have hS_fib : μ (S.filter fun π => π.1 x = i) < δ_const / (n : ℝ) := by
      have := hp_eq i
      rw [lt_div_iff₀ hn_pos]; linarith
    have hδ_half : 2 * δ_const ≤ c_avoid := by unfold δ_const; linarith [c_avoid_pos]
    have hcd : δ_const / (n : ℝ) ≤ c_avoid / (n : ℝ) - δ_const / (n : ℝ) := by
      rw [← sub_div]; exact div_le_div_of_nonneg_right (by linarith) hn_pos.le
    linarith
  have hJI_sdiff : ((J \ I).card : ℝ) * (δ_const / (n : ℝ)) ≤ μ (S \ F_I) := by
    have hsub : (J \ I).biUnion (fun j => S.filter fun π => π.1 x = j) ⊆ S \ F_I := by
      intro π hπ
      obtain ⟨j, hj, hπj⟩ := Finset.mem_biUnion.mp hπ
      have ⟨hπS, hπx⟩ := Finset.mem_filter.mp hπj
      refine Finset.mem_sdiff.mpr ⟨hπS, ?_⟩
      intro hπF
      exact (Finset.mem_sdiff.mp hj).2 (hπx ▸ (Finset.mem_filter.mp hπF).2.1)
    have hdisj : Set.PairwiseDisjoint ((J \ I : Finset (Fin n)) : Set (Fin n))
        (fun j => S.filter fun π => π.1 x = j) := by
      intro j₁ _ j₂ _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]
      intro π h1 h2; exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    have h1 : ∑ j ∈ J \ I, μ (S.filter fun π => π.1 x = j) ≤ μ (S \ F_I) := by
      rw [← μ_biUnion_of_disjoint hdisj]; exact μ_mono hsub
    refine le_trans ?_ h1
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun j hj => ?_
    have hpj : δ_const ≤ p j := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hj).1).2
    rw [hp_eq j] at hpj
    rw [div_le_iff₀ hn_pos]; linarith
  have hd_bound : ((I \ J).card : ℝ) + ((J \ I).card : ℝ) ≤
      (2 / δ_const) * (n : ℝ) * (n : ℝ) ^ (-(33 : ℝ) / 50) := by
    have hsum : (((I \ J).card : ℝ) + ((J \ I).card : ℝ)) * (δ_const / (n : ℝ)) ≤
        2 * (n : ℝ) ^ (-(33 : ℝ) / 50) := by linarith
    have hpos_dn : 0 < δ_const / (n : ℝ) := div_pos δ_const_pos hn_pos
    have h1 := (le_div_iff₀ hpos_dn).mpr hsum
    have h2 : 2 * (n : ℝ) ^ (-(33 : ℝ) / 50) / (δ_const / (n : ℝ)) =
        (2 / δ_const) * (n : ℝ) * (n : ℝ) ^ (-(33 : ℝ) / 50) := by
      have := δ_const_pos.ne'; field_simp
    linarith
  have hd_le_a : ((I \ J).card : ℝ) + ((J \ I).card : ℝ) ≤ a_const * Real.sqrt (n : ℝ) :=
    hd_bound.trans hbig2
  -- Step 5: `a_const √n ≤ |J| ≤ b_const √n`
  have hJ_lo : a_const * Real.sqrt (n : ℝ) ≤ (J.card : ℝ) := by
    have hcard : I.card ≤ J.card + (I \ J).card := by
      have h1 : I ⊆ J ∪ (I \ J) := fun a ha => by
        by_cases h : a ∈ J; exact Finset.mem_union_left _ h; exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨ha, h⟩)
      exact (Finset.card_le_card h1).trans (Finset.card_union_le _ _)
    have hcardR : (I.card : ℝ) ≤ (J.card : ℝ) + ((I \ J).card : ℝ) := by exact_mod_cast hcard
    have hnn : (0 : ℝ) ≤ ((J \ I).card : ℝ) := Nat.cast_nonneg _
    linarith
  have hJ_hi : (J.card : ℝ) ≤ b_const * Real.sqrt (n : ℝ) := by
    have hcard : J.card ≤ I.card + (J \ I).card := by
      have h1 : J ⊆ I ∪ (J \ I) := fun a ha => by
        by_cases h : a ∈ I; exact Finset.mem_union_left _ h; exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨ha, h⟩)
      exact (Finset.card_le_card h1).trans (Finset.card_union_le _ _)
    have hcardR : (J.card : ℝ) ≤ (I.card : ℝ) + ((J \ I).card : ℝ) := by exact_mod_cast hcard
    have hnn : (0 : ℝ) ≤ ((I \ J).card : ℝ) := Nat.cast_nonneg _
    have hab : a_const ≤ b_const / 2 := by unfold a_const b_const; norm_num
    nlinarith
  -- Step 6: `μ (F \ S) ≤ μ (S \ F)`
  have hH_le_E : μ (F \ S) ≤ μ (S \ F) := by
    unfold μ
    apply div_le_div_of_nonneg_right _ hcard_alt_pos.le
    have h1 : F.card ≤ S.card := hmax x J
    have h2 : (F \ S).card + (F ∩ S).card = F.card := Finset.card_sdiff_add_card_inter F S
    have h3 : (S \ F).card + (S ∩ F).card = S.card := Finset.card_sdiff_add_card_inter S F
    rw [Finset.inter_comm] at h3
    exact_mod_cast (by omega : (F \ S).card ≤ (S \ F).card)
  -- Step 7: `μ (F \ S) ≤ μ (F_I \ S) + μ (F \ F_I) ≤ (1 + 200 / δ_const) * n^(-33/50)`
  have hFFI : μ (F \ F_I) ≤ (200 / δ_const) * (n : ℝ) ^ (-(33 : ℝ) / 50) := by
    -- Partition `F \ F_I` into `π.1 x ∈ J \ I`, `(a ∈ I \ J, π.1 a ∈ I)`, and `(a ∈ I ∩ J, π.1 a ∈ I \ J)`
    let E1 := (J \ I).biUnion fun y => Finset.univ.filter fun π : Alt n => π.1 x = y
    let E2 := ((I \ J) ×ˢ I).biUnion fun p =>
      I.biUnion fun y => Finset.univ.filter fun π : Alt n => π.1 x = y ∧ π.1 p.1 = p.2
    let E3 := (I ×ˢ (I \ J)).biUnion fun p =>
      I.biUnion fun y => Finset.univ.filter fun π : Alt n => π.1 x = y ∧ π.1 p.1 = p.2
    have hcov : F \ F_I ⊆ E1 ∪ (E2 ∪ E3) := by
      intro π hπ
      have ⟨hπF, hπnFI⟩ := Finset.mem_sdiff.mp hπ
      have ⟨hxJ', hJavoid⟩ := (Finset.mem_filter.mp hπF).2
      by_cases hxI' : π.1 x ∈ I
      · have hex : ∃ a ∈ I, π.1 a ∈ I := by
          by_contra hall; push Not at hall
          exact hπnFI (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxI', hall⟩)
        obtain ⟨a, haI, hπaI⟩ := hex
        by_cases haJ : a ∈ J
        · have hπanJ : π.1 a ∉ J := hJavoid a haJ
          refine Finset.mem_union_right _ (Finset.mem_union_right _ ?_)
          exact Finset.mem_biUnion.mpr ⟨(a, π.1 a), Finset.mem_product.mpr ⟨haI, Finset.mem_sdiff.mpr ⟨hπaI, hπanJ⟩⟩,
            Finset.mem_biUnion.mpr ⟨π.1 x, hxI', Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, rfl⟩⟩⟩
        · refine Finset.mem_union_right _ (Finset.mem_union_left _ ?_)
          exact Finset.mem_biUnion.mpr ⟨(a, π.1 a), Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨haI, haJ⟩, hπaI⟩,
            Finset.mem_biUnion.mpr ⟨π.1 x, hxI', Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, rfl⟩⟩⟩
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨π.1 x, Finset.mem_sdiff.mpr ⟨hxJ', hxI'⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩)
    have hμ1 : μ E1 ≤ ((J \ I).card : ℝ) / (n : ℝ) := by
      calc μ E1 ≤ ∑ y ∈ J \ I, μ (Finset.univ.filter fun π : Alt n => π.1 x = y) := μ_biUnion_le _ _
        _ = ∑ _y ∈ J \ I, (1 / (n : ℝ)) := Finset.sum_congr rfl fun y _ => μ_fiber1 (by omega) x y
        _ = ((J \ I).card : ℝ) / (n : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    have hnm1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
      have : (100000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hfib2_le : ∀ (a b y : Fin n), a ∈ I →
        μ (Finset.univ.filter fun π : Alt n => π.1 x = y ∧ π.1 a = b) ≤ 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
      intro a b y haI
      have hxa : x ≠ a := fun h => hxI (h ▸ haI)
      by_cases hyb : y = b
      · have hempty : (Finset.univ.filter fun π : Alt n => π.1 x = y ∧ π.1 a = b) = ∅ := by
          ext π; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          rintro ⟨h1, h2⟩; exact hxa (π.1.injective (h1.trans (hyb.trans h2.symm)))
        rw [hempty]; simp only [μ, Finset.card_empty, Nat.cast_zero, zero_div]
        exact div_nonneg zero_le_one (mul_pos hn_pos hnm1_pos).le
      · rw [μ_fiber2 (by omega) hxa hyb]
    have hμ2 : μ E2 ≤ ((I \ J).card : ℝ) * (I.card : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
      calc μ E2 ≤ ∑ p ∈ (I \ J) ×ˢ I, ∑ y ∈ I, μ (Finset.univ.filter fun π : Alt n => π.1 x = y ∧ π.1 p.1 = p.2) :=
              (μ_biUnion_le _ _).trans (Finset.sum_le_sum fun p _ => μ_biUnion_le _ _)
        _ ≤ ∑ _p ∈ (I \ J) ×ˢ I, ∑ _y ∈ I, (1 / ((n : ℝ) * ((n : ℝ) - 1))) :=
              Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun y _ =>
                hfib2_le p.1 p.2 y (Finset.mem_sdiff.mp (Finset.mem_product.mp hp).1).1
        _ = ((I \ J).card : ℝ) * (I.card : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
              rw [Finset.sum_const, Finset.sum_const, Finset.card_product, nsmul_eq_mul, nsmul_eq_mul]
              push_cast; ring
    have hμ3 : μ E3 ≤ ((I \ J).card : ℝ) * (I.card : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
      calc μ E3 ≤ ∑ p ∈ I ×ˢ (I \ J), ∑ y ∈ I, μ (Finset.univ.filter fun π : Alt n => π.1 x = y ∧ π.1 p.1 = p.2) :=
              (μ_biUnion_le _ _).trans (Finset.sum_le_sum fun p _ => μ_biUnion_le _ _)
        _ ≤ ∑ _p ∈ I ×ˢ (I \ J), ∑ _y ∈ I, (1 / ((n : ℝ) * ((n : ℝ) - 1))) :=
              Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun y _ =>
                hfib2_le p.1 p.2 y (Finset.mem_product.mp hp).1
        _ = ((I \ J).card : ℝ) * (I.card : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
              rw [Finset.sum_const, Finset.sum_const, Finset.card_product, nsmul_eq_mul, nsmul_eq_mul]
              push_cast; ring
    have hI_sq : (I.card : ℝ) ^ 2 ≤ 16 * (n : ℝ) := by
      unfold b_const at hI_hi
      have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn_pos.le
      nlinarith
    have hnm1 : (n : ℝ) / 2 ≤ (n : ℝ) - 1 := by
      have : (100000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hfrac : (I.card : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 32 / (n : ℝ) := by
      rw [div_le_div_iff₀ (by nlinarith) hn_pos]
      nlinarith
    have hμ2' : μ E2 ≤ 32 * ((I \ J).card : ℝ) / (n : ℝ) := by
      refine hμ2.trans ?_
      have h1 := mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg (I \ J).card)
      have h2 : ((I \ J).card : ℝ) * (I.card : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) =
          ((I \ J).card : ℝ) * ((I.card : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) - 1))) := by ring
      have h3 : ((I \ J).card : ℝ) * (32 / (n : ℝ)) = 32 * ((I \ J).card : ℝ) / (n : ℝ) := by ring
      linarith
    have hμ3' : μ E3 ≤ 32 * ((I \ J).card : ℝ) / (n : ℝ) := by
      refine hμ3.trans ?_
      have h1 := mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg (I \ J).card)
      have h2 : ((I \ J).card : ℝ) * (I.card : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) =
          ((I \ J).card : ℝ) * ((I.card : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) - 1))) := by ring
      have h3 : ((I \ J).card : ℝ) * (32 / (n : ℝ)) = 32 * ((I \ J).card : ℝ) / (n : ℝ) := by ring
      linarith
    have htot : μ (F \ F_I) ≤ 65 * (((I \ J).card : ℝ) + ((J \ I).card : ℝ)) / (n : ℝ) := by
      have h1 : μ (F \ F_I) ≤ μ E1 + (μ E2 + μ E3) :=
        (μ_mono hcov).trans ((μ_union_le _ _).trans (add_le_add le_rfl (μ_union_le _ _)))
      have h2 : μ E1 + (μ E2 + μ E3) ≤
          ((J \ I).card : ℝ) / (n : ℝ) + (32 * ((I \ J).card : ℝ) / (n : ℝ) + 32 * ((I \ J).card : ℝ) / (n : ℝ)) :=
        add_le_add hμ1 (add_le_add hμ2' hμ3')
      have h3 : ((J \ I).card : ℝ) / (n : ℝ) + (32 * ((I \ J).card : ℝ) / (n : ℝ) + 32 * ((I \ J).card : ℝ) / (n : ℝ)) ≤
          65 * (((I \ J).card : ℝ) + ((J \ I).card : ℝ)) / (n : ℝ) := by
        have hnn1 : (0 : ℝ) ≤ ((I \ J).card : ℝ) / (n : ℝ) := div_nonneg (Nat.cast_nonneg _) hn_pos.le
        have hnn2 : (0 : ℝ) ≤ ((J \ I).card : ℝ) / (n : ℝ) := div_nonneg (Nat.cast_nonneg _) hn_pos.le
        have ha : 65 * (((I \ J).card : ℝ) + ((J \ I).card : ℝ)) / (n : ℝ) =
            65 * (((I \ J).card : ℝ) / (n : ℝ)) + 65 * (((J \ I).card : ℝ) / (n : ℝ)) := by ring
        have hb : 32 * ((I \ J).card : ℝ) / (n : ℝ) = 32 * (((I \ J).card : ℝ) / (n : ℝ)) := by ring
        linarith
      exact h1.trans (h2.trans h3)
    refine htot.trans ?_
    rw [div_le_iff₀ hn_pos]
    have h4 : 65 * ((2 / δ_const) * (n : ℝ) * (n : ℝ) ^ (-(33 : ℝ) / 50)) ≤
        (200 / δ_const) * (n : ℝ) ^ (-(33 : ℝ) / 50) * (n : ℝ) := by
      have hpos : 0 < (n : ℝ) * (n : ℝ) ^ (-(33 : ℝ) / 50) / δ_const :=
        div_pos (mul_pos hn_pos (Real.rpow_pos_of_pos hn_pos _)) δ_const_pos
      have h5 : 65 * ((2 / δ_const) * (n : ℝ) * (n : ℝ) ^ (-(33 : ℝ) / 50)) =
          130 * ((n : ℝ) * (n : ℝ) ^ (-(33 : ℝ) / 50) / δ_const) := by ring
      have h6 : (200 / δ_const) * (n : ℝ) ^ (-(33 : ℝ) / 50) * (n : ℝ) =
          200 * ((n : ℝ) * (n : ℝ) ^ (-(33 : ℝ) / 50) / δ_const) := by ring
      linarith
    linarith [mul_le_mul_of_nonneg_left hd_bound (show (0 : ℝ) ≤ 65 by norm_num)]
  have hH_upper : μ (F \ S) ≤ (1 + 200 / δ_const) * (n : ℝ) ^ (-(33 : ℝ) / 50) := by
    have hcov : F \ S ⊆ (F_I \ S) ∪ (F \ F_I) := by
      intro π hπ
      have ⟨hπF, hπnS⟩ := Finset.mem_sdiff.mp hπ
      by_cases h : π ∈ F_I
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h, hπnS⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hπF, h⟩)
    have h1 := (μ_mono hcov).trans (μ_union_le _ _)
    linarith
  exact ⟨hxJ, hJ_lo, hJ_hi, hH_le_E, hH_upper⟩

set_option maxHeartbeats 2000000 in
/-- Inside-edge bound: `μ {σ ∈ S \ F | σ.1 x ∈ J} ≤ μ (F \ S) / 4`. -/
private lemma inside_edges_le {n : ℕ} (hn : 100000000 ≤ n)
    (hbig1 : 100 / δ_const ≤ Real.sqrt (n : ℝ))
    (hbig2 : (40000 : ℝ) * (2 * b_const ^ 2 / η_const) / ((c_avoid * δ_const) ^ 2 * (n : ℝ) ^ ((1 : ℝ) / 4)) ≤ 1 / 16)
    (S : Finset (Alt n)) (hpf : ProdFree (S : Set (Alt n)))
    (x : Fin n) (J : Finset (Fin n)) (hxJ : x ∉ J)
    (hJ_lo : a_const * Real.sqrt (n : ℝ) ≤ (J.card : ℝ))
    (hJ_hi : (J.card : ℝ) ≤ b_const * Real.sqrt (n : ℝ))
    (hJ_dens : ∀ j ∈ J, δ_const ≤ ((S.filter fun π => π.1 x = j).card : ℝ) /
      ((Finset.univ.filter fun π : Alt n => π.1 x = j).card : ℝ))
    (hH_small : μ ((Finset.univ.filter fun π : Alt n => π.1 x ∈ J ∧ ∀ a ∈ J, π.1 a ∉ J) \ S) ≤
      (η_const ^ 2 / (16 * b_const)) / Real.sqrt (n : ℝ)) :
    let F := Finset.univ.filter fun π : Alt n => π.1 x ∈ J ∧ ∀ a ∈ J, π.1 a ∉ J
    μ ((S \ F).filter fun σ => σ.1 x ∈ J) ≤ μ (F \ S) / 4 := by
  classical
  intro F
  let H := μ (F \ S)
  let h_val (i : Fin n) : ℝ :=
    (((F \ S).filter fun π => π.1 x = i).card : ℝ) /
    ((Finset.univ.filter fun π : Alt n => π.1 x = i).card : ℝ)
  let J_bad := J.filter fun i => η_const < h_val i
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  have hsq_sq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn_pos.le
  have hcard_alt_pos : (0 : ℝ) < (Fintype.card (Alt n) : ℝ) := by exact_mod_cast card_alt_pos (by omega)
  have hΩ_eq : ∀ v : Fin n, ((Finset.univ.filter fun π : Alt n => π.1 x = v).card : ℝ) =
      (Fintype.card (Alt n) : ℝ) / (n : ℝ) := by
    intro v
    have hfib := μ_fiber1 (by omega) x v
    unfold μ at hfib
    have := (div_eq_iff hcard_alt_pos.ne').mp hfib
    linarith [show (1 / (n : ℝ)) * (Fintype.card (Alt n) : ℝ) = (Fintype.card (Alt n) : ℝ) / (n : ℝ) by ring]
  have hh_eq : ∀ i : Fin n, h_val i = (n : ℝ) * μ ((F \ S).filter fun π => π.1 x = i) := by
    intro i; dsimp only [h_val]; unfold μ; rw [hΩ_eq i]; field_simp
  -- Step 1: Bound `t = J_bad.card ≤ n * H / η_const`
  have ht_bound : (J_bad.card : ℝ) ≤ (n : ℝ) * H / η_const := by
    have hsub : J_bad.biUnion (fun i => (F \ S).filter fun π => π.1 x = i) ⊆ F \ S := by
      intro π hπ; obtain ⟨_, _, h2⟩ := Finset.mem_biUnion.mp hπ; exact (Finset.mem_filter.mp h2).1
    have hdisj : Set.PairwiseDisjoint (J_bad : Set (Fin n)) (fun i => (F \ S).filter fun π => π.1 x = i) := by
      intro i₁ _ i₂ _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]
      intro π h1 h2; exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    have hsum : ∑ i ∈ J_bad, μ ((F \ S).filter fun π => π.1 x = i) ≤ H := by
      rw [← μ_biUnion_of_disjoint hdisj]; exact μ_mono hsub
    have hlow : (J_bad.card : ℝ) * (η_const / (n : ℝ)) ≤ ∑ i ∈ J_bad, μ ((F \ S).filter fun π => π.1 x = i) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun i hi => ?_
      have hgt : η_const < h_val i := (Finset.mem_filter.mp hi).2
      rw [hh_eq i] at hgt
      rw [div_le_iff₀ hn_pos]; linarith
    have h1 : (J_bad.card : ℝ) * η_const ≤ (n : ℝ) * H := by
      have := hlow.trans hsum
      have hmul : (J_bad.card : ℝ) * (η_const / (n : ℝ)) * (n : ℝ) = (J_bad.card : ℝ) * η_const := by field_simp
      nlinarith
    exact (le_div_iff₀ η_const_pos).mpr h1
  -- Step 2: Case 1 (both `i, j` good): impossible!
  have hboth_good : ∀ i ∈ J, ∀ j ∈ J, i ∉ J_bad → j ∉ J_bad →
      ∀ σ ∈ S, σ.1 i ≠ j := by
    intro i hi j hj hiG hjG σ hσ hσij
    have hhi : h_val i ≤ η_const := by
      by_contra hgt; push Not at hgt; exact hiG (Finset.mem_filter.mpr ⟨hi, hgt⟩)
    have hhj : h_val j ≤ η_const := by
      by_contra hgt; push Not at hgt; exact hjG (Finset.mem_filter.mpr ⟨hj, hgt⟩)
    let B := J ∪ J.image σ⁻¹.1
    let G := Finset.univ.filter fun β : Alt n => β.1 x = i ∧ ∀ a ∈ J, β.1 a ∉ B
    have hB_card : (B.card : ℝ) ≤ 16 * Real.sqrt (n : ℝ) := by
      have h1 : B.card ≤ J.card + (J.image σ⁻¹.1).card := Finset.card_union_le _ _
      have h2 : (J.image σ⁻¹.1).card = J.card := Finset.card_image_of_injective _ σ⁻¹.1.injective
      have h3 : (B.card : ℝ) ≤ 2 * (J.card : ℝ) := by exact_mod_cast (by omega : B.card ≤ 2 * J.card)
      unfold b_const at hJ_hi; linarith
    have hJ_16 : (J.card : ℝ) ≤ 16 * Real.sqrt (n : ℝ) := by unfold b_const at hJ_hi; linarith
    have hG_lo : c_avoid / (n : ℝ) ≤ μ G := by
      have hdisj_xJ : Disjoint ({x} : Finset (Fin n)) J := Finset.disjoint_singleton_left.mpr hxJ
      have hfinj : Set.InjOn (fun _ : Fin n => i) (({x} : Finset (Fin n)) : Set (Fin n)) := by
        intro u hu v hv _; simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hu hv; exact hu.trans hv.symm
      have hav := μ_avoid_ge_c (by omega) {x} J B hdisj_xJ (by simp) hJ_16 hB_card (fun _ => i) hfinj
      have hfib1 : μ (Finset.univ.filter fun β : Alt n => ∀ u ∈ ({x} : Finset (Fin n)), β.1 u = i) = 1 / (n : ℝ) := by
        convert μ_fiber1 (by omega) x i using 2; ext β; simp
      rw [hfib1] at hav
      have heqG : (Finset.univ.filter fun β : Alt n => (∀ u ∈ ({x} : Finset (Fin n)), β.1 u = i) ∧ ∀ a ∈ J, β.1 a ∉ B) = G := by
        ext β; simp [G]
      rw [heqG, mul_one_div] at hav; exact hav
    have hG_hi : μ G ≤ (h_val i + h_val j) / (n : ℝ) := by
      let G1 := G.filter fun β => β ∉ S
      let G2 := G.filter fun β => σ * β ∉ S
      have hcov : G ⊆ G1 ∪ G2 := by
        intro β hβ
        by_cases h1 : β ∈ S
        · by_cases h2 : σ * β ∈ S
          · exact absurd h2 (hpf σ hσ β h1)
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hβ, h2⟩)
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hβ, h1⟩)
      have hG1_sub : G1 ⊆ (F \ S).filter fun β => β.1 x = i := by
        intro β hβ
        have ⟨hβG, hβnS⟩ := Finset.mem_filter.mp hβ
        have ⟨hβx, hβa⟩ := (Finset.mem_filter.mp hβG).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hβx ▸ hi,
          fun a ha => fun hmem => hβa a ha (Finset.mem_union_left _ hmem)⟩, hβnS⟩, hβx⟩
      have hG2_sub : G2.image (fun β => σ * β) ⊆ (F \ S).filter fun γ => γ.1 x = j := by
        intro γ hγ
        obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.mp hγ
        have ⟨hβG, hβnS⟩ := Finset.mem_filter.mp hβ
        have ⟨hβx, hβa⟩ := (Finset.mem_filter.mp hβG).2
        have hσβx : (σ * β).1 x = j := by show σ.1 (β.1 x) = j; rw [hβx, hσij]
        refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσβx ▸ hj, ?_⟩, hβnS⟩, hσβx⟩
        intro a ha hmem
        have : β.1 a ∈ J.image σ⁻¹.1 := Finset.mem_image.mpr ⟨(σ * β).1 a, hmem, by
          show σ⁻¹.1 (σ.1 (β.1 a)) = β.1 a; exact (σ.1.symm_apply_apply _)⟩
        exact hβa a ha (Finset.mem_union_right _ this)
      have hG2_card : G2.card ≤ ((F \ S).filter fun γ => γ.1 x = j).card := by
        rw [← Finset.card_image_of_injective G2 (mul_right_injective σ)]
        exact Finset.card_le_card hG2_sub
      have hμ1 : μ G1 ≤ h_val i / (n : ℝ) := by
        have := μ_mono hG1_sub; rw [hh_eq i]; field_simp; linarith
      have hμ2 : μ G2 ≤ h_val j / (n : ℝ) := by
        have h2 : μ G2 ≤ μ ((F \ S).filter fun γ => γ.1 x = j) := by
          unfold μ; exact div_le_div_of_nonneg_right (by exact_mod_cast hG2_card) hcard_alt_pos.le
        rw [hh_eq j]; field_simp; linarith
      calc μ G ≤ μ (G1 ∪ G2) := μ_mono hcov
        _ ≤ μ G1 + μ G2 := μ_union_le _ _
        _ ≤ (h_val i + h_val j) / (n : ℝ) := by rw [add_div]; linarith
    have hη_small : 2 * η_const < c_avoid := by
      unfold η_const δ_const
      have hc := c_avoid_pos
      have hc1 : c_avoid ≤ 1 := by unfold c_avoid; exact Real.exp_le_one_iff.mpr (by norm_num)
      nlinarith
    have hcontra : c_avoid / (n : ℝ) ≤ 2 * η_const / (n : ℝ) := by
      refine hG_lo.trans (hG_hi.trans ?_)
      exact div_le_div_of_nonneg_right (by linarith) hn_pos.le
    rw [div_le_div_iff_of_pos_right hn_pos] at hcontra
    linarith
  -- Step 3: Case 2a (`i` good, `j` bad) and Case 2b (`i` bad, `j` good) via `subset_avoid_chebyshev`
  let C_cheb : ℝ := (40000 : ℝ) / ((c_avoid * δ_const) ^ 2 * (n : ℝ) ^ ((1 : ℝ) / 4))
  have hnm1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (100000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hC_nn : 0 ≤ C_cheb := div_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hn_pos.le _))
  have hJ_card_ge2 : 2 ≤ J.card := by
    have hsq10000 : (10000 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      have : (100000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      calc (10000 : ℝ) = Real.sqrt (100000000 : ℝ) := by
            rw [show (100000000 : ℝ) = 10000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt this
    have : (2 : ℝ) ≤ (J.card : ℝ) := by unfold a_const at hJ_lo; linarith
    exact_mod_cast this
  have hJ_small_n : J.card + 4 ≤ n := by
    have hsq10000 : (10000 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      have : (100000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      calc (10000 : ℝ) = Real.sqrt (100000000 : ℝ) := by
            rw [show (100000000 : ℝ) = 10000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt this
    have : (J.card : ℝ) + 4 ≤ (n : ℝ) := by unfold b_const at hJ_hi; nlinarith
    exact_mod_cast this
  have hone_good_i : ∀ i ∈ J, ∀ j ∈ J, ∀ k ∈ J, j ≠ k → i ∉ J_bad →
      μ (S.filter fun σ => σ.1 x = k ∧ σ.1 i = j) ≤ C_cheb / ((n : ℝ) * ((n : ℝ) - 1)) := by
    intro i hi j hj k hk hjk hiG
    have hhi : h_val i ≤ η_const := by
      by_contra hgt; push Not at hgt; exact hiG (Finset.mem_filter.mpr ⟨hi, hgt⟩)
    have hxi : x ≠ i := fun h => hxJ (h ▸ hi)
    let Ω₂ := Finset.univ.filter fun σ : Alt n => σ.1 x = k ∧ σ.1 i = j
    let Ω_j := Finset.univ.filter fun γ : Alt n => γ.1 x = j
    let C := S.filter fun γ => γ.1 x = j
    let Z (T : Finset (Fin n)) : ℝ :=
      ((C.filter fun γ => ∀ a ∈ J, γ.1 a ∉ ({j} : Finset (Fin n)) ∪ T).card : ℝ) / (Ω_j.card : ℝ)
    -- Every `σ ∈ S ∩ Ω₂` satisfies `Z ((J.erase i).image σ.1) ≤ η_const`
    have hZ_bad : ∀ σ ∈ S.filter (fun σ => σ.1 x = k ∧ σ.1 i = j), Z ((J.erase i).image σ.1) ≤ η_const := by
      intro σ hσ
      have ⟨hσS, hσx, hσi⟩ := Finset.mem_filter.mp hσ
      let T := (J.erase i).image σ.1
      have hJimg : J.image σ.1 = ({j} : Finset (Fin n)) ∪ T := by
        ext y; simp only [T, Finset.mem_image, Finset.mem_union, Finset.mem_singleton, Finset.mem_erase]
        constructor
        · rintro ⟨a, ha, rfl⟩
          by_cases hai : a = i
          · exact Or.inl (hai ▸ hσi)
          · exact Or.inr ⟨a, ⟨hai, ha⟩, rfl⟩
        · rintro (rfl | ⟨a, ⟨_, ha⟩, rfl⟩)
          · exact ⟨i, hi, hσi⟩
          · exact ⟨a, ha, rfl⟩
      let Good_γ := C.filter fun γ => ∀ a ∈ J, γ.1 a ∉ ({j} : Finset (Fin n)) ∪ T
      have himg_sub : Good_γ.image (fun γ => σ⁻¹ * γ) ⊆ (F \ S).filter fun β => β.1 x = i := by
        intro β hβ
        obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hβ
        have ⟨hγC, hγav⟩ := Finset.mem_filter.mp hγ
        have ⟨hγS, hγx⟩ := Finset.mem_filter.mp hγC
        have hβx : (σ⁻¹ * γ).1 x = i := by
          show σ.1⁻¹ (γ.1 x) = i
          rw [hγx, ← hσi]; simp
        have hβnS : σ⁻¹ * γ ∉ S := fun hmem => hpf σ hσS (σ⁻¹ * γ) hmem (by simpa using hγS)
        refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hβx ▸ hi, ?_⟩, hβnS⟩, hβx⟩
        intro a ha hmem
        have hγa : γ.1 a ∈ J.image σ.1 := by
          refine Finset.mem_image.mpr ⟨(σ⁻¹ * γ).1 a, hmem, ?_⟩
          show σ.1 (σ.1⁻¹ (γ.1 a)) = γ.1 a; simp
        rw [hJimg] at hγa
        exact hγav a ha hγa
      have hcard_le : Good_γ.card ≤ ((F \ S).filter fun β => β.1 x = i).card := by
        rw [← Finset.card_image_of_injective Good_γ (mul_right_injective σ⁻¹)]
        exact Finset.card_le_card himg_sub
      have hΩ_same : (Ω_j.card : ℝ) = ((Finset.univ.filter fun β : Alt n => β.1 x = i).card : ℝ) := by
        rw [hΩ_eq j, hΩ_eq i]
      have hle : Z T ≤ h_val i := by
        dsimp only [Z, h_val]
        rw [hΩ_same]
        exact div_le_div_of_nonneg_right (by exact_mod_cast hcard_le) (Nat.cast_nonneg _)
      exact hle.trans hhi
    -- Apply `ratio_alt_image_bad` + `subset_avoid_chebyshev`
    let U : Finset (Fin n) := {x, i}
    let f : Fin n → Fin n := Function.update (fun _ => k) i j
    have hdisj_UA : Disjoint U (J.erase i) := by
      rw [Finset.disjoint_left]; intro u hu
      simp only [U, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with hu1 | hu2
      · rw [hu1]; exact fun h => hxJ (Finset.mem_of_mem_erase h)
      · rw [hu2]; exact Finset.notMem_erase i J
    have hfinj : Set.InjOn f (U : Set (Fin n)) := by
      intro u hu v hv huv
      simp only [U, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
      rcases hu with hu1 | hu2 <;> rcases hv with hv1 | hv2
      · exact hu1.trans hv1.symm
      · rw [hu1, hv2] at huv; simp [f, hxi] at huv; exact absurd huv.symm hjk
      · rw [hu2, hv1] at huv; simp [f, hxi] at huv; exact absurd huv hjk
      · exact hu2.trans hv2.symm
    have hU_card : U.card = 2 := Finset.card_pair hxi
    have hUimg : U.image f = {j, k} := by
      ext y; simp [U, f, hxi]; tauto
    have hΩ₂_eq : Ω₂ = Finset.univ.filter fun σ : Alt n => ∀ u ∈ U, σ.1 u = f u := by
      ext σ; simp only [Ω₂, U, f, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩ u (rfl | rfl)
        · simp [hxi, h1]
        · simp [h2]
      · intro h
        exact ⟨by simpa [hxi] using h x (Or.inl rfl), by simpa using h i (Or.inr rfl)⟩
    have hsub_bad : S.filter (fun σ => σ.1 x = k ∧ σ.1 i = j) ⊆
        Ω₂.filter fun σ => Z ((J.erase i).image σ.1) ≤ η_const := by
      intro σ hσ
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hσ).2⟩, hZ_bad σ hσ⟩
    have hrat := ratio_alt_image_bad U (J.erase i) f hdisj_UA hfinj (by rw [hU_card, Finset.card_erase_of_mem hi]; omega)
      (fun T => Z T ≤ η_const)
    dsimp only at hrat
    rw [← hΩ₂_eq, hUimg] at hrat
    have hW_card : n - 2 ≤ (Finset.univ \ ({j, k} : Finset (Fin n))).card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, Finset.card_pair hjk]
    have hs_hi : ((J.erase i).card : ℝ) ≤ b_const * Real.sqrt (n : ℝ) := by
      have : (J.erase i).card ≤ J.card := Finset.card_erase_le
      exact le_trans (by exact_mod_cast this) hJ_hi
    have hcheb := subset_avoid_chebyshev hn hbig1 x j J {j} (Finset.univ \ {j, k}) (J.erase i).card
      hxJ hJ_hi (by simp) hW_card hs_hi C (fun γ hγ => (Finset.mem_filter.mp hγ).2) (hJ_dens j hj)
    have hμΩ₂ : μ Ω₂ = 1 / ((n : ℝ) * ((n : ℝ) - 1)) := μ_fiber2 (by omega) hxi hjk.symm
    have hμ_ratio : μ (S.filter fun σ => σ.1 x = k ∧ σ.1 i = j) / μ Ω₂ ≤ C_cheb := by
      have h1 : μ (S.filter fun σ => σ.1 x = k ∧ σ.1 i = j) / μ Ω₂ ≤
          ((Ω₂.filter fun σ => Z ((J.erase i).image σ.1) ≤ η_const).card : ℝ) / (Ω₂.card : ℝ) := by
        unfold μ
        rw [div_div_div_cancel_right₀ hcard_alt_pos.ne']
        exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub_bad) (Nat.cast_nonneg _)
      exact h1.trans (hrat.le.trans hcheb)
    have hΩ₂_pos : 0 < μ Ω₂ := by rw [hμΩ₂]; exact div_pos zero_lt_one (mul_pos hn_pos hnm1_pos)
    have := (div_le_iff₀ hΩ₂_pos).mp hμ_ratio
    rw [hμΩ₂] at this
    linarith [show C_cheb * (1 / ((n : ℝ) * ((n : ℝ) - 1))) = C_cheb / ((n : ℝ) * ((n : ℝ) - 1)) by ring]
  have hone_good_j : ∀ i ∈ J, ∀ j ∈ J, ∀ k ∈ J, j ≠ k → j ∉ J_bad →
      μ (S.filter fun σ => σ.1 x = k ∧ σ.1 i = j) ≤ C_cheb / ((n : ℝ) * ((n : ℝ) - 1)) := by
    intro i hi j hj k hk hjk hjG
    have hhj : h_val j ≤ η_const := by
      by_contra hgt; push Not at hgt; exact hjG (Finset.mem_filter.mpr ⟨hj, hgt⟩)
    have hxi : x ≠ i := fun h => hxJ (h ▸ hi)
    -- Map `σ ↦ σ⁻¹` so `τ.1 k = x ∧ τ.1 j = i`
    let S_inv := (S.filter fun σ => σ.1 x = k ∧ σ.1 i = j).image (·⁻¹)
    let Ω₂ := Finset.univ.filter fun τ : Alt n => τ.1 k = x ∧ τ.1 j = i
    let Ω_i := Finset.univ.filter fun γ : Alt n => γ.1 x = i
    let C := S.filter fun γ => γ.1 x = i
    let A := (J.erase j).erase k
    let Z (T : Finset (Fin n)) : ℝ :=
      ((C.filter fun γ => ∀ a ∈ J, γ.1 a ∉ ({x, i} : Finset (Fin n)) ∪ T).card : ℝ) / (Ω_i.card : ℝ)
    have hZ_bad : ∀ τ ∈ S_inv, Z (A.image τ.1) ≤ η_const := by
      intro τ hτ
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hτ
      have ⟨hσS, hσx, hσi⟩ := Finset.mem_filter.mp hσ
      let T := A.image σ⁻¹.1
      have hJimg : J.image σ⁻¹.1 = ({x, i} : Finset (Fin n)) ∪ T := by
        ext y; simp only [T, A, Finset.mem_image, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, Finset.mem_erase]
        constructor
        · rintro ⟨a, ha, rfl⟩
          by_cases hak : a = k
          · exact Or.inl (Or.inl (by rw [hak, ← hσx]; show σ.1⁻¹ (σ.1 x) = x; simp))
          · by_cases haj : a = j
            · exact Or.inl (Or.inr (by rw [haj, ← hσi]; show σ.1⁻¹ (σ.1 i) = i; simp))
            · exact Or.inr ⟨a, ⟨hak, haj, ha⟩, rfl⟩
        · rintro ((hyx | hyi) | ⟨a, ⟨_, _, ha⟩, rfl⟩)
          · exact ⟨k, hk, by rw [hyx, ← hσx]; show σ.1⁻¹ (σ.1 x) = x; simp⟩
          · exact ⟨j, hj, by rw [hyi, ← hσi]; show σ.1⁻¹ (σ.1 i) = i; simp⟩
          · exact ⟨a, ha, rfl⟩
      let Good_γ := C.filter fun γ => ∀ a ∈ J, γ.1 a ∉ ({x, i} : Finset (Fin n)) ∪ T
      have himg_sub : Good_γ.image (fun γ => σ * γ) ⊆ (F \ S).filter fun β => β.1 x = j := by
        intro β hβ
        obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hβ
        have ⟨hγC, hγav⟩ := Finset.mem_filter.mp hγ
        have ⟨hγS, hγx⟩ := Finset.mem_filter.mp hγC
        have hβx : (σ * γ).1 x = j := by show σ.1 (γ.1 x) = j; rw [hγx, hσi]
        have hβnS : σ * γ ∉ S := fun hmem => hpf σ hσS γ hγS hmem
        refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hβx ▸ hj, ?_⟩, hβnS⟩, hβx⟩
        intro a ha hmem
        have hγa : γ.1 a ∈ J.image σ⁻¹.1 := by
          refine Finset.mem_image.mpr ⟨(σ * γ).1 a, hmem, ?_⟩
          show σ.1⁻¹ (σ.1 (γ.1 a)) = γ.1 a; simp
        rw [hJimg] at hγa
        exact hγav a ha hγa
      have hcard_le : Good_γ.card ≤ ((F \ S).filter fun β => β.1 x = j).card := by
        rw [← Finset.card_image_of_injective Good_γ (mul_right_injective σ)]
        exact Finset.card_le_card himg_sub
      have hΩ_same : (Ω_i.card : ℝ) = ((Finset.univ.filter fun β : Alt n => β.1 x = j).card : ℝ) := by
        rw [hΩ_eq i, hΩ_eq j]
      have hle : Z T ≤ h_val j := by
        dsimp only [Z, h_val]
        rw [hΩ_same]
        exact div_le_div_of_nonneg_right (by exact_mod_cast hcard_le) (Nat.cast_nonneg _)
      exact hle.trans hhj
    let U : Finset (Fin n) := {k, j}
    let f : Fin n → Fin n := Function.update (fun _ => x) j i
    have hkj : k ≠ j := hjk.symm
    have hdisj_UA : Disjoint U A := by
      rw [Finset.disjoint_left]; intro u hu
      simp only [U, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with hu1 | hu2
      · rw [hu1]; exact Finset.notMem_erase k _
      · rw [hu2]; exact fun h => Finset.notMem_erase j J (Finset.mem_of_mem_erase h)
    have hfinj : Set.InjOn f (U : Set (Fin n)) := by
      intro u hu v hv huv
      simp only [U, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
      rcases hu with hu1 | hu2 <;> rcases hv with hv1 | hv2
      · exact hu1.trans hv1.symm
      · rw [hu1, hv2] at huv; simp [f, hkj] at huv; exact absurd huv hxi
      · rw [hu2, hv1] at huv; simp [f, hkj] at huv; exact absurd huv.symm hxi
      · exact hu2.trans hv2.symm
    have hU_card : U.card = 2 := Finset.card_pair hkj
    have hUimg : U.image f = {x, i} := by
      ext y; simp [U, f, hkj]
    have hΩ₂_eq : Ω₂ = Finset.univ.filter fun τ : Alt n => ∀ u ∈ U, τ.1 u = f u := by
      ext τ; simp only [Ω₂, U, f, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩ u (hu1 | hu2)
        · rw [hu1]; simp [hkj, h1]
        · rw [hu2]; simp [h2]
      · intro h
        exact ⟨by simpa [hkj] using h k (Or.inl rfl), by simpa using h j (Or.inr rfl)⟩
    have hSinv_sub : S_inv ⊆ Ω₂.filter fun τ => Z (A.image τ.1) ≤ η_const := by
      intro τ hτ
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hτ
      have ⟨_, hσx, hσi⟩ := Finset.mem_filter.mp hσ
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, hZ_bad σ⁻¹ hτ⟩
      · show σ.1⁻¹ k = x; rw [← hσx]; simp
      · show σ.1⁻¹ j = i; rw [← hσi]; simp
    have hA_le : A.card ≤ J.card := (Finset.card_erase_le).trans Finset.card_erase_le
    have hrat := ratio_alt_image_bad U A f hdisj_UA hfinj (by rw [hU_card]; omega) (fun T => Z T ≤ η_const)
    dsimp only at hrat
    rw [← hΩ₂_eq, hUimg] at hrat
    have hW_card : n - 2 ≤ (Finset.univ \ ({x, i} : Finset (Fin n))).card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, Finset.card_pair hxi]
    have hcheb := subset_avoid_chebyshev hn hbig1 x i J {x, i} (Finset.univ \ {x, i}) A.card
      hxJ hJ_hi (by rw [Finset.card_pair hxi]) hW_card (le_trans (by exact_mod_cast hA_le) hJ_hi)
      C (fun γ hγ => (Finset.mem_filter.mp hγ).2) (hJ_dens i hi)
    have hμΩ₂ : μ Ω₂ = 1 / ((n : ℝ) * ((n : ℝ) - 1)) := μ_fiber2 (by omega) hkj hxi
    have hcard_inv : S_inv.card = (S.filter fun σ => σ.1 x = k ∧ σ.1 i = j).card :=
      Finset.card_image_of_injective _ inv_injective
    have hμ_inv : μ S_inv = μ (S.filter fun σ => σ.1 x = k ∧ σ.1 i = j) := by
      unfold μ; rw [hcard_inv]
    have hμ_ratio : μ S_inv / μ Ω₂ ≤ C_cheb := by
      have h1 : μ S_inv / μ Ω₂ ≤ ((Ω₂.filter fun τ => Z (A.image τ.1) ≤ η_const).card : ℝ) / (Ω₂.card : ℝ) := by
        unfold μ
        rw [div_div_div_cancel_right₀ hcard_alt_pos.ne']
        exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hSinv_sub) (Nat.cast_nonneg _)
      exact h1.trans (hrat.le.trans hcheb)
    have hΩ₂_pos : 0 < μ Ω₂ := by rw [hμΩ₂]; exact div_pos zero_lt_one (mul_pos hn_pos hnm1_pos)
    have := (div_le_iff₀ hΩ₂_pos).mp hμ_ratio
    rw [hμΩ₂, hμ_inv] at this
    linarith [show C_cheb * (1 / ((n : ℝ) * ((n : ℝ) - 1))) = C_cheb / ((n : ℝ) * ((n : ℝ) - 1)) by ring]
  -- Step 4: Sum over all `(i, j, k) ∈ J × J × J`
  let T1 := (J ×ˢ J_bad) ×ˢ J
  let T2 := (J_bad ×ˢ J) ×ˢ J
  let T3 := (J_bad ×ˢ J_bad) ×ˢ J
  have hcov : (S \ F).filter (fun σ => σ.1 x ∈ J) ⊆
      (T1.biUnion fun p => S.filter fun σ => σ.1 x = p.2 ∧ σ.1 p.1.1 = p.1.2 ∧ p.1.1 ∉ J_bad) ∪
      ((T2.biUnion fun p => S.filter fun σ => σ.1 x = p.2 ∧ σ.1 p.1.1 = p.1.2 ∧ p.1.2 ∉ J_bad) ∪
       (T3.biUnion fun p => S.filter fun σ => σ.1 x = p.2 ∧ σ.1 p.1.1 = p.1.2)) := by
    intro σ hσ
    have ⟨hσSF, hσxJ⟩ := Finset.mem_filter.mp hσ
    have ⟨hσS, hσnF⟩ := Finset.mem_sdiff.mp hσSF
    have hex : ∃ i ∈ J, σ.1 i ∈ J := by
      by_contra hall; push Not at hall
      exact hσnF (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσxJ, hall⟩)
    obtain ⟨i, hi, hσiJ⟩ := hex
    by_cases hiB : i ∈ J_bad
    · by_cases hjB : σ.1 i ∈ J_bad
      · refine Finset.mem_union_right _ (Finset.mem_union_right _ ?_)
        exact Finset.mem_biUnion.mpr ⟨((i, σ.1 i), σ.1 x),
          Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hiB, hjB⟩, hσxJ⟩,
          Finset.mem_filter.mpr ⟨hσS, rfl, rfl⟩⟩
      · refine Finset.mem_union_right _ (Finset.mem_union_left _ ?_)
        exact Finset.mem_biUnion.mpr ⟨((i, σ.1 i), σ.1 x),
          Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hiB, hσiJ⟩, hσxJ⟩,
          Finset.mem_filter.mpr ⟨hσS, rfl, rfl, hjB⟩⟩
    · by_cases hjB : σ.1 i ∈ J_bad
      · refine Finset.mem_union_left _ ?_
        exact Finset.mem_biUnion.mpr ⟨((i, σ.1 i), σ.1 x),
          Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hi, hjB⟩, hσxJ⟩,
          Finset.mem_filter.mpr ⟨hσS, rfl, rfl, hiB⟩⟩
      · exact absurd rfl (hboth_good i hi (σ.1 i) hσiJ hiB hjB σ hσS)
  have hterm1 : ∀ p ∈ T1,
      μ (S.filter fun σ => σ.1 x = p.2 ∧ σ.1 p.1.1 = p.1.2 ∧ p.1.1 ∉ J_bad) ≤
        C_cheb / ((n : ℝ) * ((n : ℝ) - 1)) := by
    intro p hp
    have ⟨hp1, hk⟩ := Finset.mem_product.mp hp
    have ⟨hi, hjB⟩ := Finset.mem_product.mp hp1
    have hj : p.1.2 ∈ J := (Finset.mem_filter.mp hjB).1
    by_cases hiB : p.1.1 ∈ J_bad
    · have hempty : S.filter (fun σ => σ.1 x = p.2 ∧ σ.1 p.1.1 = p.1.2 ∧ p.1.1 ∉ J_bad) = ∅ := by
        ext σ; simp [hiB]
      rw [hempty]; simp [μ]; exact div_nonneg hC_nn (mul_pos hn_pos hnm1_pos).le
    · by_cases hjk : p.1.2 = p.2
      · have hempty : S.filter (fun σ => σ.1 x = p.2 ∧ σ.1 p.1.1 = p.1.2 ∧ p.1.1 ∉ J_bad) = ∅ := by
          ext σ; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
          rintro ⟨_, h1, h2, _⟩
          exact (fun h : x = p.1.1 => hxJ (h ▸ hi)) (σ.1.injective (h1.trans (hjk.symm.trans h2.symm)))
        rw [hempty]; simp [μ]; exact div_nonneg hC_nn (mul_pos hn_pos hnm1_pos).le
      · refine le_trans (μ_mono fun σ hσ => ?_) (hone_good_i p.1.1 hi p.1.2 hj p.2 hk hjk hiB)
        have ⟨h1, h2, h3, _⟩ := Finset.mem_filter.mp hσ
        exact Finset.mem_filter.mpr ⟨h1, h2, h3⟩
  have hterm2 : ∀ p ∈ T2,
      μ (S.filter fun σ => σ.1 x = p.2 ∧ σ.1 p.1.1 = p.1.2 ∧ p.1.2 ∉ J_bad) ≤
        C_cheb / ((n : ℝ) * ((n : ℝ) - 1)) := by
    intro p hp
    have ⟨hp1, hk⟩ := Finset.mem_product.mp hp
    have ⟨hiB, hj⟩ := Finset.mem_product.mp hp1
    have hi : p.1.1 ∈ J := (Finset.mem_filter.mp hiB).1
    by_cases hjB : p.1.2 ∈ J_bad
    · have hempty : S.filter (fun σ => σ.1 x = p.2 ∧ σ.1 p.1.1 = p.1.2 ∧ p.1.2 ∉ J_bad) = ∅ := by
        ext σ; simp [hjB]
      rw [hempty]; simp [μ]; exact div_nonneg hC_nn (mul_pos hn_pos hnm1_pos).le
    · by_cases hjk : p.1.2 = p.2
      · have hempty : S.filter (fun σ => σ.1 x = p.2 ∧ σ.1 p.1.1 = p.1.2 ∧ p.1.2 ∉ J_bad) = ∅ := by
          ext σ; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
          rintro ⟨_, h1, h2, _⟩
          exact (fun h : x = p.1.1 => hxJ (h ▸ hi)) (σ.1.injective (h1.trans (hjk.symm.trans h2.symm)))
        rw [hempty]; simp [μ]; exact div_nonneg hC_nn (mul_pos hn_pos hnm1_pos).le
      · refine le_trans (μ_mono fun σ hσ => ?_) (hone_good_j p.1.1 hi p.1.2 hj p.2 hk hjk hjB)
        have ⟨h1, h2, h3, _⟩ := Finset.mem_filter.mp hσ
        exact Finset.mem_filter.mpr ⟨h1, h2, h3⟩
  have hterm3 : ∀ p ∈ T3,
      μ (S.filter fun σ => σ.1 x = p.2 ∧ σ.1 p.1.1 = p.1.2) ≤ 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
    intro p hp
    have hi : p.1.1 ∈ J := (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_product.mp hp).1).1).1
    have hxi : x ≠ p.1.1 := fun h => hxJ (h ▸ hi)
    by_cases hjk : p.1.2 = p.2
    · have hempty : S.filter (fun σ => σ.1 x = p.2 ∧ σ.1 p.1.1 = p.1.2) = ∅ := by
        ext σ; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
        rintro ⟨_, h1, h2⟩; exact hxi (σ.1.injective (h1.trans (hjk.symm.trans h2.symm)))
      rw [hempty]; simp only [μ, Finset.card_empty, Nat.cast_zero, zero_div]
      exact div_nonneg zero_le_one (mul_pos hn_pos hnm1_pos).le
    · refine le_trans (μ_mono fun σ hσ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hσ).2⟩) ?_
      rw [μ_fiber2 (by omega) hxi (Ne.symm hjk)]
  have hμ1 : μ (T1.biUnion fun p => S.filter fun σ => σ.1 x = p.2 ∧ σ.1 p.1.1 = p.1.2 ∧ p.1.1 ∉ J_bad) ≤
      (J_bad.card : ℝ) * (J.card : ℝ) ^ 2 * C_cheb / ((n : ℝ) * ((n : ℝ) - 1)) := by
    refine (μ_biUnion_le _ _).trans ((Finset.sum_le_sum hterm1).trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul]; simp only [T1, Finset.card_product]; push_cast; ring_nf; rfl
  have hμ2 : μ (T2.biUnion fun p => S.filter fun σ => σ.1 x = p.2 ∧ σ.1 p.1.1 = p.1.2 ∧ p.1.2 ∉ J_bad) ≤
      (J_bad.card : ℝ) * (J.card : ℝ) ^ 2 * C_cheb / ((n : ℝ) * ((n : ℝ) - 1)) := by
    refine (μ_biUnion_le _ _).trans ((Finset.sum_le_sum hterm2).trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul]; simp only [T2, Finset.card_product]; push_cast; ring_nf; rfl
  have hμ3 : μ (T3.biUnion fun p => S.filter fun σ => σ.1 x = p.2 ∧ σ.1 p.1.1 = p.1.2) ≤
      (J_bad.card : ℝ) ^ 2 * (J.card : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    refine (μ_biUnion_le _ _).trans ((Finset.sum_le_sum hterm3).trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul]; simp only [T3, Finset.card_product]; push_cast; ring_nf; rfl
  -- Combine with `t ≤ n H / η_const`, `|J| ≤ b_const √n`, `H ≤ (η_const^2 / (16 b_const)) / √n`
  have hnm1 : (n : ℝ) / 2 ≤ (n : ℝ) - 1 := by
    have : (100000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hH_nn : 0 ≤ H := μ_nonneg _
  have hpart12 : 2 * ((J_bad.card : ℝ) * (J.card : ℝ) ^ 2 * C_cheb / ((n : ℝ) * ((n : ℝ) - 1))) ≤ H / 8 := by
    have hJsq : (J.card : ℝ) ^ 2 ≤ b_const ^ 2 * (n : ℝ) := by nlinarith [hJ_hi, hsq_sq]
    have hnum : 2 * ((J_bad.card : ℝ) * (J.card : ℝ) ^ 2 * C_cheb) ≤
        2 * (((n : ℝ) * H / η_const) * (b_const ^ 2 * (n : ℝ)) * C_cheb) := by
      have h1 := mul_le_mul ht_bound hJsq (sq_nonneg _) (by have := η_const_pos; positivity)
      have h2 := mul_le_mul_of_nonneg_right h1 hC_nn
      linarith
    have hden_pos : 0 < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
    have hdiv : 2 * ((J_bad.card : ℝ) * (J.card : ℝ) ^ 2 * C_cheb / ((n : ℝ) * ((n : ℝ) - 1))) ≤
        4 * (b_const ^ 2 / η_const) * C_cheb * H := by
      rw [show 2 * ((J_bad.card : ℝ) * (J.card : ℝ) ^ 2 * C_cheb / ((n : ℝ) * ((n : ℝ) - 1))) =
        2 * ((J_bad.card : ℝ) * (J.card : ℝ) ^ 2 * C_cheb) / ((n : ℝ) * ((n : ℝ) - 1)) by ring]
      rw [div_le_iff₀ hden_pos]
      have hcoef : 2 * (((n : ℝ) * H / η_const) * (b_const ^ 2 * (n : ℝ)) * C_cheb) =
          (4 * (b_const ^ 2 / η_const) * C_cheb * H) * ((n : ℝ) * ((n : ℝ) / 2)) := by ring
      have hnn : 0 ≤ 4 * (b_const ^ 2 / η_const) * C_cheb * H := by have := η_const_pos; unfold b_const; positivity
      have h3 : (4 * (b_const ^ 2 / η_const) * C_cheb * H) * ((n : ℝ) * ((n : ℝ) / 2)) ≤
          (4 * (b_const ^ 2 / η_const) * C_cheb * H) * ((n : ℝ) * ((n : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnm1 hn_pos.le) hnn
      linarith
    have hcoef_le : 4 * (b_const ^ 2 / η_const) * C_cheb ≤ 1 / 8 := by
      dsimp only [C_cheb]
      have : 4 * (b_const ^ 2 / η_const) * ((40000 : ℝ) / ((c_avoid * δ_const) ^ 2 * (n : ℝ) ^ ((1 : ℝ) / 4))) =
          2 * ((40000 : ℝ) * (2 * b_const ^ 2 / η_const) / ((c_avoid * δ_const) ^ 2 * (n : ℝ) ^ ((1 : ℝ) / 4))) := by ring
      linarith
    nlinarith
  have hpart3 : (J_bad.card : ℝ) ^ 2 * (J.card : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ H / 8 := by
    have ht_le2 : (J_bad.card : ℝ) ≤ (η_const / (16 * b_const)) * Real.sqrt (n : ℝ) := by
      have h1 : (n : ℝ) * H / η_const ≤ (n : ℝ) * ((η_const ^ 2 / (16 * b_const)) / Real.sqrt (n : ℝ)) / η_const := by
        apply div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hH_small hn_pos.le) η_const_pos.le
      have h2 : (n : ℝ) * ((η_const ^ 2 / (16 * b_const)) / Real.sqrt (n : ℝ)) / η_const =
          (η_const / (16 * b_const)) * Real.sqrt (n : ℝ) := by
        have hηne := η_const_pos.ne'
        have hsqne := hsq_pos.ne'
        have hbne : b_const ≠ 0 := by unfold b_const; norm_num
        field_simp
        nlinarith [hsq_sq]
      linarith
    have hden_pos : 0 < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
    rw [div_le_iff₀ hden_pos]
    have h1 : (J_bad.card : ℝ) * (J.card : ℝ) ≤ (η_const / 16) * (n : ℝ) := by
      have hprod := mul_le_mul ht_le2 hJ_hi (Nat.cast_nonneg _) (by have := η_const_pos; unfold b_const; positivity)
      have hbne : b_const ≠ 0 := by unfold b_const; norm_num
      have hsimp : (η_const / (16 * b_const)) * Real.sqrt (n : ℝ) * (b_const * Real.sqrt (n : ℝ)) =
          (η_const / 16) * (n : ℝ) := by
        field_simp; rw [Real.sq_sqrt hn_pos.le]
      linarith
    have h2 : (J_bad.card : ℝ) ^ 2 * (J.card : ℝ) ≤ ((n : ℝ) * H / η_const) * ((η_const / 16) * (n : ℝ)) := by
      rw [sq, mul_assoc]
      exact mul_le_mul ht_bound h1 (by positivity) (by have := η_const_pos; positivity)
    have h3 : ((n : ℝ) * H / η_const) * ((η_const / 16) * (n : ℝ)) = (H / 8) * ((n : ℝ) * ((n : ℝ) / 2)) := by
      have hηne := η_const_pos.ne'; field_simp; ring
    have h4 : (H / 8) * ((n : ℝ) * ((n : ℝ) / 2)) ≤ (H / 8) * ((n : ℝ) * ((n : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnm1 hn_pos.le) (by linarith)
    linarith
  have htot : μ ((S \ F).filter fun σ => σ.1 x ∈ J) ≤
      μ (T1.biUnion fun p => S.filter fun σ => σ.1 x = p.2 ∧ σ.1 p.1.1 = p.1.2 ∧ p.1.1 ∉ J_bad) +
      (μ (T2.biUnion fun p => S.filter fun σ => σ.1 x = p.2 ∧ σ.1 p.1.1 = p.1.2 ∧ p.1.2 ∉ J_bad) +
       μ (T3.biUnion fun p => S.filter fun σ => σ.1 x = p.2 ∧ σ.1 p.1.1 = p.1.2)) :=
    (μ_mono hcov).trans ((μ_union_le _ _).trans (add_le_add le_rfl (μ_union_le _ _)))
  have hsum_bound : μ ((S \ F).filter fun σ => σ.1 x ∈ J) ≤
      2 * ((J_bad.card : ℝ) * (J.card : ℝ) ^ 2 * C_cheb / ((n : ℝ) * ((n : ℝ) - 1))) +
      (J_bad.card : ℝ) ^ 2 * (J.card : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    have h1 := htot.trans (add_le_add hμ1 (add_le_add hμ2 hμ3))
    have h2 : (J_bad.card : ℝ) * (J.card : ℝ) ^ 2 * C_cheb / ((n : ℝ) * ((n : ℝ) - 1)) +
        ((J_bad.card : ℝ) * (J.card : ℝ) ^ 2 * C_cheb / ((n : ℝ) * ((n : ℝ) - 1)) +
         (J_bad.card : ℝ) ^ 2 * (J.card : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) =
        2 * ((J_bad.card : ℝ) * (J.card : ℝ) ^ 2 * C_cheb / ((n : ℝ) * ((n : ℝ) - 1))) +
        (J_bad.card : ℝ) ^ 2 * (J.card : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by ring
    exact h2 ▸ h1
  have hfinal : μ ((S \ F).filter fun σ => σ.1 x ∈ J) ≤ H / 8 + H / 8 :=
    hsum_bound.trans (add_le_add hpart12 hpart3)
  have hquarter : H / 8 + H / 8 = H / 4 := by ring
  exact hquarter ▸ hfinal

end MainProof


/- ### Section 4b: Outside Targets (`σ(x) ∉ J`) via Two-Point Fibre Dichotomy & Bonferroni -/

section OutsideTargets

/-- Two-point fibre dichotomy for an outsider `σ ∈ S` with `y = σ(x) ∉ J`:
for every `i, k ∈ J`, putting `z = σ⁻¹(k)`, we have `z ≠ x` and at least one of
`A(i, k, y)` or `B(i, z)` holds with threshold `(c_avoid / 3) / (n (n - 1))`. -/
private lemma two_point_dichotomy {n : ℕ} (hn : 100000 ≤ n)
    (S : Finset (Alt n)) (hpf : ProdFree (S : Set (Alt n)))
    (x : Fin n) (J : Finset (Fin n)) (hxJ : x ∉ J)
    (hJ_hi : (J.card : ℝ) ≤ b_const * Real.sqrt (n : ℝ))
    (σ : Alt n) (hσ : σ ∈ S) (hy : σ.1 x ∉ J)
    (i k : Fin n) (hi : i ∈ J) (hk : k ∈ J) :
    let F := Finset.univ.filter fun π : Alt n => π.1 x ∈ J ∧ ∀ a ∈ J, π.1 a ∉ J
    let Q := F \ S
    let y := σ.1 x
    let z := σ⁻¹.1 k
    z ≠ x ∧
      ((c_avoid / 3) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ μ (Q.filter fun π => π.1 x = k ∧ π.1 i = y) ∨
       (c_avoid / 3) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ μ (Q.filter fun π => π.1 x = i ∧ π.1 z = x)) := by
  classical
  intro F Q y z
  have hzx : z ≠ x := by
    intro h
    have : σ.1 x = k := by
      have h1 : σ.1 z = k := σ.1.apply_symm_apply k
      rwa [h] at h1
    exact hy (this ▸ hk)
  have hix : i ≠ x := fun h => hxJ (h ▸ hi)
  let U : Finset (Fin n) := {x, z}
  let A : Finset (Fin n) := (J ∪ J.image σ⁻¹.1).erase z
  let f : Fin n → Fin n := Function.update (fun _ => i) z x
  have hxA : x ∉ J ∪ J.image σ⁻¹.1 := by
    intro hx
    rcases Finset.mem_union.mp hx with h1 | h2
    · exact hxJ h1
    · obtain ⟨a, ha, haeq⟩ := Finset.mem_image.mp h2
      have : σ.1 x = a := by rw [← haeq]; exact σ.1.apply_symm_apply a
      exact hy (this ▸ ha)
  have hdisj_UA : Disjoint U A := by
    rw [Finset.disjoint_left]; intro u hu
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with hu1 | hu2
    · rw [hu1]; exact fun h => hxA (Finset.mem_of_mem_erase h)
    · rw [hu2]; exact Finset.notMem_erase z _
  have hfinj : Set.InjOn f (U : Set (Fin n)) := by
    intro u hu v hv huv
    simp only [U, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with hu1 | hu2 <;> rcases hv with hv1 | hv2
    · exact hu1.trans hv1.symm
    · rw [hu1, hv2] at huv; simp [f, hzx.symm] at huv; exact absurd huv hix
    · rw [hu2, hv1] at huv; simp [f, hzx.symm] at huv; exact absurd huv.symm hix
    · exact hu2.trans hv2.symm
  have hA_card : (A.card : ℝ) ≤ 16 * Real.sqrt (n : ℝ) := by
    have h1 : A.card ≤ (J ∪ J.image σ⁻¹.1).card := Finset.card_erase_le
    have h2 : (J ∪ J.image σ⁻¹.1).card ≤ J.card + (J.image σ⁻¹.1).card := Finset.card_union_le _ _
    have h3 : (J.image σ⁻¹.1).card = J.card := Finset.card_image_of_injective _ σ⁻¹.1.injective
    have h4 : (A.card : ℝ) ≤ 2 * (J.card : ℝ) := by exact_mod_cast (by omega : A.card ≤ 2 * J.card)
    unfold b_const at hJ_hi; linarith
  have hJ_16 : (J.card : ℝ) ≤ 16 * Real.sqrt (n : ℝ) := by unfold b_const at hJ_hi; linarith
  let G := Finset.univ.filter fun β : Alt n => (∀ u ∈ U, β.1 u = f u) ∧ ∀ a ∈ A, β.1 a ∉ J
  have hG_lo : c_avoid / ((n : ℝ) * ((n : ℝ) - 1)) ≤ μ G := by
    have hav := μ_avoid_ge_c hn U A J hdisj_UA (by rw [Finset.card_pair hzx.symm]) hA_card hJ_16 f hfinj
    have hfib : μ (Finset.univ.filter fun β : Alt n => ∀ u ∈ U, β.1 u = f u) = 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
      have heq : (Finset.univ.filter fun β : Alt n => ∀ u ∈ U, β.1 u = f u) =
          Finset.univ.filter fun β : Alt n => β.1 x = i ∧ β.1 z = x := by
        ext β; simp only [U, f, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro h; exact ⟨by simpa [hzx.symm] using h x (Or.inl rfl), by simpa using h z (Or.inr rfl)⟩
        · rintro ⟨h1, h2⟩ u (hu1 | hu2)
          · rw [hu1]; simp [hzx.symm, h1]
          · rw [hu2]; simp [h2]
      rw [heq, μ_fiber2 (by omega) hzx.symm hix]
    rw [hfib, mul_one_div] at hav
    exact hav
  -- Every `β ∈ G` yields `β ∈ F` and `α = σ * β⁻¹ ∈ F` with `α * β = σ ∈ S`
  let G1 := G.filter fun β => β ∉ S
  let G2 := G.filter fun β => σ * β⁻¹ ∉ S
  have hcov : G ⊆ G1 ∪ G2 := by
    intro β hβ
    by_cases h1 : β ∈ S
    · by_cases h2 : σ * β⁻¹ ∈ S
      · exact absurd (by simpa using hσ) (hpf (σ * β⁻¹) h2 β h1)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hβ, h2⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hβ, h1⟩)
  have hβ_props : ∀ β ∈ G, β.1 x = i ∧ β.1 z = x ∧ ∀ a ∈ J ∪ J.image σ⁻¹.1, β.1 a ∉ J := by
    intro β hβ
    have ⟨hβU, hβA⟩ := (Finset.mem_filter.mp hβ).2
    have hβx : β.1 x = i := by simpa [U, f, hzx.symm] using hβU x (by simp [U])
    have hβz : β.1 z = x := by simpa [U, f] using hβU z (by simp [U])
    refine ⟨hβx, hβz, fun a ha => ?_⟩
    by_cases haz : a = z
    · rw [haz, hβz]; exact hxJ
    · exact hβA a (Finset.mem_erase.mpr ⟨haz, ha⟩)
  have hG1_sub : G1 ⊆ Q.filter fun π => π.1 x = i ∧ π.1 z = x := by
    intro β hβ
    have ⟨hβG, hβnS⟩ := Finset.mem_filter.mp hβ
    obtain ⟨hβx, hβz, hβav⟩ := hβ_props β hβG
    exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hβx ▸ hi, fun a ha => hβav a (Finset.mem_union_left _ ha)⟩, hβnS⟩, hβx, hβz⟩
  have hG2_sub : G2.image (fun β => σ * β⁻¹) ⊆ Q.filter fun π => π.1 x = k ∧ π.1 i = y := by
    intro α hα
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.mp hα
    have ⟨hβG, hαnS⟩ := Finset.mem_filter.mp hβ
    obtain ⟨hβx, hβz, hβav⟩ := hβ_props β hβG
    have hαx : (σ * β⁻¹).1 x = k := by
      show σ.1 (β⁻¹.1 x) = k
      have h1 : β⁻¹.1 x = z := by rw [← hβz]; exact β.1.symm_apply_apply z
      rw [h1]; exact σ.1.apply_symm_apply k
    have hαi : (σ * β⁻¹).1 i = y := by
      show σ.1 (β⁻¹.1 i) = σ.1 x
      have h1 : β⁻¹.1 i = x := by rw [← hβx]; exact β.1.symm_apply_apply x
      rw [h1]
    refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hαx ▸ hk, ?_⟩, hαnS⟩, hαx, hαi⟩
    intro a ha hmem
    have hu : β⁻¹.1 a ∈ J.image σ⁻¹.1 :=
      Finset.mem_image.mpr ⟨(σ * β⁻¹).1 a, hmem, by show σ⁻¹.1 (σ.1 (β⁻¹.1 a)) = β⁻¹.1 a; exact σ.1.symm_apply_apply _⟩
    have hβu : β.1 (β⁻¹.1 a) = a := β.1.apply_symm_apply a
    exact hβav (β⁻¹.1 a) (Finset.mem_union_right _ hu) (by rwa [hβu])
  have hG2_card : G2.card ≤ (Q.filter fun π => π.1 x = k ∧ π.1 i = y).card := by
    have hinj : Function.Injective (fun β : Alt n => σ * β⁻¹) :=
      fun β₁ β₂ h => inv_injective (mul_left_cancel h)
    rw [← Finset.card_image_of_injective G2 hinj]
    exact Finset.card_le_card hG2_sub
  have hcard_alt_pos : (0 : ℝ) < (Fintype.card (Alt n) : ℝ) := by exact_mod_cast card_alt_pos (by omega)
  have hμG1 : μ G1 ≤ μ (Q.filter fun π => π.1 x = i ∧ π.1 z = x) := μ_mono hG1_sub
  have hμG2 : μ G2 ≤ μ (Q.filter fun π => π.1 x = k ∧ π.1 i = y) := by
    unfold μ; exact div_le_div_of_nonneg_right (by exact_mod_cast hG2_card) hcard_alt_pos.le
  have hsum_ge : c_avoid / ((n : ℝ) * ((n : ℝ) - 1)) ≤
      μ (Q.filter fun π => π.1 x = k ∧ π.1 i = y) + μ (Q.filter fun π => π.1 x = i ∧ π.1 z = x) :=
    hG_lo.trans ((μ_mono hcov).trans ((μ_union_le G1 G2).trans (by linarith)))
  refine ⟨hzx, ?_⟩
  by_contra hboth
  push Not at hboth
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hnm1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (100000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hpos : 0 < c_avoid / ((n : ℝ) * ((n : ℝ) - 1)) :=
    div_pos c_avoid_pos (mul_pos hn_pos hnm1_pos)
  have h23 : (c_avoid / 3) / ((n : ℝ) * ((n : ℝ) - 1)) + (c_avoid / 3) / ((n : ℝ) * ((n : ℝ) - 1)) =
      (2 / 3) * (c_avoid / ((n : ℝ) * ((n : ℝ) - 1))) := by ring
  linarith

/-- Elementary Bonferroni inequality on finite sets:
`∑ |A_e| - ∑_{e₁ ≠ e₂} |A_{e₁} ∩ A_{e₂}| ≤ |Q|` whenever every `A_e ⊆ Q`. -/
private lemma bonferroni_card_le {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (Idx : Finset ι) (Q : Finset α) (A : ι → Finset α) (hsub : ∀ e ∈ Idx, A e ⊆ Q) :
    (∑ e ∈ Idx, ((A e).card : ℝ)) -
      (∑ e₁ ∈ Idx, ∑ e₂ ∈ Idx.erase e₁, ((A e₁ ∩ A e₂).card : ℝ)) ≤ (Q.card : ℝ) := by
  classical
  have h1 : ∑ e ∈ Idx, ((A e).card : ℝ) = ∑ π ∈ Q, ((Idx.filter fun e => π ∈ A e).card : ℝ) := by
    have ha : ∀ e ∈ Idx, ((A e).card : ℝ) = ∑ π ∈ Q, if π ∈ A e then (1 : ℝ) else 0 := by
      intro e he
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (hsub e he),
        Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl ha, Finset.sum_comm]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h2 : ∑ e₁ ∈ Idx, ∑ e₂ ∈ Idx.erase e₁, ((A e₁ ∩ A e₂).card : ℝ) =
      ∑ π ∈ Q, ((Idx.filter fun e => π ∈ A e).card : ℝ) * (((Idx.filter fun e => π ∈ A e).card : ℝ) - 1) := by
    have hb : ∀ e₁ ∈ Idx, ∀ e₂ ∈ Idx.erase e₁,
        ((A e₁ ∩ A e₂).card : ℝ) = ∑ π ∈ Q, if π ∈ A e₁ ∧ π ∈ A e₂ then (1 : ℝ) else 0 := by
      intro e₁ he₁ e₂ _
      have hsub12 : A e₁ ∩ A e₂ ⊆ Q := Finset.inter_subset_left.trans (hsub e₁ he₁)
      rw [← Finset.sum_filter]
      have heq : Q.filter (fun π => π ∈ A e₁ ∧ π ∈ A e₂) = A e₁ ∩ A e₂ := by
        ext π; simp only [Finset.mem_filter, Finset.mem_inter]
        exact ⟨fun h => h.2, fun h => ⟨hsub12 (Finset.mem_inter.mpr h), h⟩⟩
      rw [heq, Finset.sum_const, nsmul_eq_mul, mul_one]
    calc ∑ e₁ ∈ Idx, ∑ e₂ ∈ Idx.erase e₁, ((A e₁ ∩ A e₂).card : ℝ)
        = ∑ e₁ ∈ Idx, ∑ e₂ ∈ Idx.erase e₁, ∑ π ∈ Q, if π ∈ A e₁ ∧ π ∈ A e₂ then (1 : ℝ) else 0 :=
          Finset.sum_congr rfl fun e₁ he₁ => Finset.sum_congr rfl fun e₂ he₂ => hb e₁ he₁ e₂ he₂
      _ = ∑ e₁ ∈ Idx, ∑ π ∈ Q, ∑ e₂ ∈ Idx.erase e₁, if π ∈ A e₁ ∧ π ∈ A e₂ then (1 : ℝ) else 0 :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ π ∈ Q, ∑ e₁ ∈ Idx, ∑ e₂ ∈ Idx.erase e₁, if π ∈ A e₁ ∧ π ∈ A e₂ then (1 : ℝ) else 0 :=
          Finset.sum_comm
      _ = ∑ π ∈ Q, ((Idx.filter fun e => π ∈ A e).card : ℝ) * (((Idx.filter fun e => π ∈ A e).card : ℝ) - 1) := by
          refine Finset.sum_congr rfl fun π _ => ?_
          let R := Idx.filter fun e => π ∈ A e
          have hinner : ∀ e₁ ∈ Idx,
              (∑ e₂ ∈ Idx.erase e₁, if π ∈ A e₁ ∧ π ∈ A e₂ then (1 : ℝ) else 0) =
                if e₁ ∈ R then ((R.card : ℝ) - 1) else 0 := by
            intro e₁ he₁
            by_cases hmem : π ∈ A e₁
            · have he1R : e₁ ∈ R := Finset.mem_filter.mpr ⟨he₁, hmem⟩
              simp only [he1R, ↓reduceIte, hmem, true_and]
              rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
              have heq : (Idx.erase e₁).filter (fun e₂ => π ∈ A e₂) = R.erase e₁ := by
                ext e₂; simp only [R, Finset.mem_filter, Finset.mem_erase]; tauto
              rw [heq, Finset.card_erase_of_mem he1R, Nat.cast_sub (Finset.one_le_card.mpr ⟨e₁, he1R⟩)]
              simp
            · have he1nR : e₁ ∉ R := fun h => hmem (Finset.mem_filter.mp h).2
              simp [he1nR, hmem]
          rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter,
            Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (Finset.filter_subset _ _),
            Finset.sum_const, nsmul_eq_mul]
  rw [h1, h2, ← Finset.sum_sub_distrib]
  calc ∑ π ∈ Q, (((Idx.filter fun e => π ∈ A e).card : ℝ) -
        ((Idx.filter fun e => π ∈ A e).card : ℝ) * (((Idx.filter fun e => π ∈ A e).card : ℝ) - 1))
      ≤ ∑ _π ∈ Q, (1 : ℝ) := Finset.sum_le_sum fun π _ => by
        rcases Nat.lt_trichotomy (Idx.filter fun e => π ∈ A e).card 1 with h0 | h1 | h2
        · have : (Idx.filter fun e => π ∈ A e).card = 0 := by omega
          rw [this]; norm_num
        · rw [h1]; norm_num
        · have hge : (2 : ℝ) ≤ ((Idx.filter fun e => π ∈ A e).card : ℝ) := by exact_mod_cast h2
          nlinarith
    _ = (Q.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

set_option maxHeartbeats 1200000 in
/-- Exceptional outside targets `Y` contribute at most `H / 4` to `μ (S \ F)`. -/
private lemma exceptional_Y_bound {n : ℕ} (hn : 100000 ≤ n)
    (hbig_c : 400 * b_const / c_avoid ≤ Real.sqrt (n : ℝ))
    (S : Finset (Alt n)) (x : Fin n) (J : Finset (Fin n)) (hxJ : x ∉ J)
    (hJ_lo : a_const * Real.sqrt (n : ℝ) ≤ (J.card : ℝ))
    (hJ_hi : (J.card : ℝ) ≤ b_const * Real.sqrt (n : ℝ))
    (houtside_dens : ∀ y ∉ J, ((S.filter fun π => π.1 x = y).card : ℝ) /
      ((Finset.univ.filter fun π : Alt n => π.1 x = y).card : ℝ) < δ_const)
    (hH_small : μ ((Finset.univ.filter fun π : Alt n => π.1 x ∈ J ∧ ∀ a ∈ J, π.1 a ∉ J) \ S) <
      (c_avoid ^ 2 * a_const / 20000) / Real.sqrt (n : ℝ)) :
    let F := Finset.univ.filter fun π : Alt n => π.1 x ∈ J ∧ ∀ a ∈ J, π.1 a ∉ J
    let Q := F \ S
    let Y := (Finset.univ \ J).filter fun y =>
      (J.card : ℝ) ^ 2 / 4 ≤
        (((J ×ˢ J).filter fun p =>
          (c_avoid / 3) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ μ (Q.filter fun π => π.1 x = p.2 ∧ π.1 p.1 = y)).card : ℝ)
    μ (S.filter fun σ => σ.1 x ∈ Y) ≤ μ Q / 4 := by
  classical
  intro F Q Y
  let H := μ Q
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  have hsq_sq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn_pos.le
  have hnm1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (100000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hnm2_pos : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (100000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hcard_alt_pos : (0 : ℝ) < (Fintype.card (Alt n) : ℝ) := by exact_mod_cast card_alt_pos (by omega)
  have hm_pos : (0 : ℝ) < (J.card : ℝ) := by
    have : 0 < a_const * Real.sqrt (n : ℝ) := by unfold a_const; positivity
    linarith
  -- Step 1: Bonferroni lower bound on `H` for any `L ⊆ Y` with `L.card ≤ c_avoid * n / (200 * J.card)`
  have hbonf : ∀ L : Finset (Fin n), L ⊆ Y → (L.card : ℝ) ≤ c_avoid * (n : ℝ) / (200 * (J.card : ℝ)) →
      c_avoid * (L.card : ℝ) * (J.card : ℝ) ^ 2 / (24 * (n : ℝ) ^ 2) ≤ H := by
    intro L hLY hL_small
    let Idx := J ×ˢ L
    let A (e : Fin n × Fin n) : Finset (Alt n) := Q.filter fun π => π.1 e.1 = e.2
    have hsub : ∀ e ∈ Idx, A e ⊆ Q := fun e _ => Finset.filter_subset _ _
    have hB := bonferroni_card_le Idx Q A hsub
    have hB_μ : (∑ e ∈ Idx, μ (A e)) - (∑ e₁ ∈ Idx, ∑ e₂ ∈ Idx.erase e₁, μ (A e₁ ∩ A e₂)) ≤ H := by
      have hdiv := div_le_div_of_nonneg_right hB hcard_alt_pos.le
      rw [sub_div, Finset.sum_div, Finset.sum_div] at hdiv
      have hinner : ∀ e₁ ∈ Idx, (∑ e₂ ∈ Idx.erase e₁, ((A e₁ ∩ A e₂).card : ℝ)) / (Fintype.card (Alt n) : ℝ) =
          ∑ e₂ ∈ Idx.erase e₁, μ (A e₁ ∩ A e₂) := fun e₁ _ => by rw [Finset.sum_div]; rfl
      rw [Finset.sum_congr rfl hinner] at hdiv
      exact hdiv
    -- Lower bound first sum
    have hfirst : c_avoid * (L.card : ℝ) * (J.card : ℝ) ^ 2 / (12 * (n : ℝ) * ((n : ℝ) - 1)) ≤ ∑ e ∈ Idx, μ (A e) := by
      have hsplit : ∀ e ∈ Idx, μ (A e) = ∑ k ∈ J, μ (Q.filter fun π => π.1 x = k ∧ π.1 e.1 = e.2) := by
        intro e _
        have hpart : A e = J.biUnion fun k => Q.filter fun π => π.1 x = k ∧ π.1 e.1 = e.2 := by
          ext π; simp only [A, Finset.mem_filter, Finset.mem_biUnion]
          constructor
          · rintro ⟨hπQ, hπe⟩
            have hπxJ : π.1 x ∈ J := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hπQ).1).2.1
            exact ⟨π.1 x, hπxJ, hπQ, rfl, hπe⟩
          · rintro ⟨k, _, hπQ, _, hπe⟩; exact ⟨hπQ, hπe⟩
        have hdisj : Set.PairwiseDisjoint (J : Set (Fin n)) (fun k => Q.filter fun π => π.1 x = k ∧ π.1 e.1 = e.2) := by
          intro k₁ _ k₂ _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]
          intro π h1 h2; exact hne ((Finset.mem_filter.mp h1).2.1.symm.trans (Finset.mem_filter.mp h2).2.1)
        rw [hpart, μ_biUnion_of_disjoint hdisj]
      rw [Finset.sum_congr rfl hsplit, Finset.sum_product_right]
      have hper_y : ∀ y ∈ L, c_avoid * (J.card : ℝ) ^ 2 / (12 * (n : ℝ) * ((n : ℝ) - 1)) ≤
          ∑ i ∈ J, ∑ k ∈ J, μ (Q.filter fun π => π.1 x = k ∧ π.1 i = y) := by
        intro y hyL
        have hyY := (Finset.mem_filter.mp (hLY hyL)).2
        let Good := (J ×ˢ J).filter fun p =>
          (c_avoid / 3) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ μ (Q.filter fun π => π.1 x = p.2 ∧ π.1 p.1 = y)
        calc c_avoid * (J.card : ℝ) ^ 2 / (12 * (n : ℝ) * ((n : ℝ) - 1))
            = ((J.card : ℝ) ^ 2 / 4) * ((c_avoid / 3) / ((n : ℝ) * ((n : ℝ) - 1))) := by
              have hne1 : (n : ℝ) ≠ 0 := hn_pos.ne'
              have hne2 : (n : ℝ) - 1 ≠ 0 := hnm1_pos.ne'
              field_simp; ring
          _ ≤ (Good.card : ℝ) * ((c_avoid / 3) / ((n : ℝ) * ((n : ℝ) - 1))) :=
              mul_le_mul_of_nonneg_right hyY (div_nonneg (by linarith [c_avoid_pos]) (mul_pos hn_pos hnm1_pos).le)
          _ = ∑ _p ∈ Good, ((c_avoid / 3) / ((n : ℝ) * ((n : ℝ) - 1))) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ p ∈ Good, μ (Q.filter fun π => π.1 x = p.2 ∧ π.1 p.1 = y) :=
              Finset.sum_le_sum fun p hp => (Finset.mem_filter.mp hp).2
          _ ≤ ∑ p ∈ J ×ˢ J, μ (Q.filter fun π => π.1 x = p.2 ∧ π.1 p.1 = y) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => μ_nonneg _
          _ = ∑ i ∈ J, ∑ k ∈ J, μ (Q.filter fun π => π.1 x = k ∧ π.1 i = y) := Finset.sum_product _ _ _
      calc c_avoid * (L.card : ℝ) * (J.card : ℝ) ^ 2 / (12 * (n : ℝ) * ((n : ℝ) - 1))
          = ∑ _y ∈ L, c_avoid * (J.card : ℝ) ^ 2 / (12 * (n : ℝ) * ((n : ℝ) - 1)) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ _ := Finset.sum_le_sum hper_y
    -- Upper bound pairwise intersection sum using `μ_fiber3`
    have hsecond : ∑ e₁ ∈ Idx, ∑ e₂ ∈ Idx.erase e₁, μ (A e₁ ∩ A e₂) ≤
        (L.card : ℝ) ^ 2 * (J.card : ℝ) ^ 3 / ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2)) := by
      have hpair : ∀ e₁ ∈ Idx, ∀ e₂ ∈ Idx.erase e₁,
          μ (A e₁ ∩ A e₂) ≤ (J.card : ℝ) / ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2)) := by
        intro e₁ he₁ e₂ he₂
        have he12 : e₂ ≠ e₁ := (Finset.mem_erase.mp he₂).1
        have he₂Idx : e₂ ∈ Idx := (Finset.mem_erase.mp he₂).2
        have hi1 : e₁.1 ∈ J := (Finset.mem_product.mp he₁).1
        have hy1 : e₁.2 ∉ J := (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hLY (Finset.mem_product.mp he₁).2)).1).2
        have hi2 : e₂.1 ∈ J := (Finset.mem_product.mp he₂Idx).1
        have hy2 : e₂.2 ∉ J := (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hLY (Finset.mem_product.mp he₂Idx).2)).1).2
        by_cases hi_eq : e₁.1 = e₂.1
        · have hy_ne : e₁.2 ≠ e₂.2 := fun h => he12 (Prod.ext hi_eq.symm h.symm)
          have hempty : A e₁ ∩ A e₂ = ∅ := by
            ext π; simp only [A, Finset.mem_inter, Finset.mem_filter, Finset.notMem_empty, iff_false]
            rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩; exact hy_ne (h1.symm.trans (hi_eq ▸ h2))
          rw [hempty]; simp only [μ, Finset.card_empty, Nat.cast_zero, zero_div]
          exact div_nonneg (Nat.cast_nonneg _) (mul_pos (mul_pos hn_pos hnm1_pos) hnm2_pos).le
        · by_cases hy_eq : e₁.2 = e₂.2
          · have hempty : A e₁ ∩ A e₂ = ∅ := by
              ext π; simp only [A, Finset.mem_inter, Finset.mem_filter, Finset.notMem_empty, iff_false]
              rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩; exact hi_eq (π.1.injective (h1.trans (hy_eq.trans h2.symm)))
            rw [hempty]; simp only [μ, Finset.card_empty, Nat.cast_zero, zero_div]
            exact div_nonneg (Nat.cast_nonneg _) (mul_pos (mul_pos hn_pos hnm1_pos) hnm2_pos).le
          · have hsub3 : A e₁ ∩ A e₂ ⊆ J.biUnion fun k =>
                Finset.univ.filter fun π : Alt n => π.1 x = k ∧ π.1 e₁.1 = e₁.2 ∧ π.1 e₂.1 = e₂.2 := by
              intro π hπ
              have ⟨h1, h2⟩ := Finset.mem_inter.mp hπ
              have ⟨hπQ, hπ1⟩ := Finset.mem_filter.mp h1
              have ⟨_, hπ2⟩ := Finset.mem_filter.mp h2
              have hπxJ : π.1 x ∈ J := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hπQ).1).2.1
              exact Finset.mem_biUnion.mpr ⟨π.1 x, hπxJ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, hπ1, hπ2⟩⟩
            calc μ (A e₁ ∩ A e₂)
                ≤ ∑ k ∈ J, μ (Finset.univ.filter fun π : Alt n => π.1 x = k ∧ π.1 e₁.1 = e₁.2 ∧ π.1 e₂.1 = e₂.2) :=
                  (μ_mono hsub3).trans (μ_biUnion_le _ _)
              _ = ∑ _k ∈ J, (1 / ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2))) :=
                  Finset.sum_congr rfl fun k hk =>
                    μ_fiber3 (by omega) (fun h => hxJ (h ▸ hi1)) (fun h => hxJ (h ▸ hi2)) hi_eq
                      (fun h => hy1 (h ▸ hk)) (fun h => hy2 (h ▸ hk)) hy_eq
              _ = (J.card : ℝ) / ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2)) := by
                  rw [Finset.sum_const, nsmul_eq_mul]; ring
      calc ∑ e₁ ∈ Idx, ∑ e₂ ∈ Idx.erase e₁, μ (A e₁ ∩ A e₂)
          ≤ ∑ e₁ ∈ Idx, ∑ _e₂ ∈ Idx.erase e₁, ((J.card : ℝ) / ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2))) :=
            Finset.sum_le_sum fun e₁ he₁ => Finset.sum_le_sum fun e₂ he₂ => hpair e₁ he₁ e₂ he₂
        _ ≤ ∑ _e₁ ∈ Idx, ∑ _e₂ ∈ Idx, ((J.card : ℝ) / ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2))) :=
            Finset.sum_le_sum fun e₁ _ => Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun _ _ _ =>
              div_nonneg (Nat.cast_nonneg _) (mul_pos (mul_pos hn_pos hnm1_pos) hnm2_pos).le
        _ = (L.card : ℝ) ^ 2 * (J.card : ℝ) ^ 3 / ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2)) := by
            rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
            simp only [Idx, Finset.card_product]; push_cast; ring
    -- Combine: `first ≥ c |L| m^2 / (12 n^2)` and `second ≤ c |L| m^2 / (24 n^2)`
    have hfirst' : c_avoid * (L.card : ℝ) * (J.card : ℝ) ^ 2 / (12 * (n : ℝ) ^ 2) ≤ ∑ e ∈ Idx, μ (A e) := by
      refine le_trans ?_ hfirst
      apply div_le_div_of_nonneg_left (by have := c_avoid_pos; positivity) (by nlinarith)
      nlinarith
    have hsecond' : ∑ e₁ ∈ Idx, ∑ e₂ ∈ Idx.erase e₁, μ (A e₁ ∩ A e₂) ≤
        c_avoid * (L.card : ℝ) * (J.card : ℝ) ^ 2 / (24 * (n : ℝ) ^ 2) := by
      refine hsecond.trans ?_
      have hden_ge : (n : ℝ) ^ 3 / 2 ≤ (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
        have hn100 : (100000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        nlinarith
      have hden_pos : 0 < (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) := mul_pos (mul_pos hn_pos hnm1_pos) hnm2_pos
      have hLm : (L.card : ℝ) * (J.card : ℝ) ≤ c_avoid * (n : ℝ) / 200 := by
        have := (le_div_iff₀ (by positivity : 0 < 200 * (J.card : ℝ))).mp hL_small
        linarith
      rw [div_le_div_iff₀ hden_pos (by positivity : 0 < 24 * (n : ℝ) ^ 2)]
      have h1 : (L.card : ℝ) ^ 2 * (J.card : ℝ) ^ 3 * (24 * (n : ℝ) ^ 2) ≤
          (c_avoid * (n : ℝ) / 200) * ((L.card : ℝ) * (J.card : ℝ) ^ 2 * (24 * (n : ℝ) ^ 2)) := by
        have heq : (L.card : ℝ) ^ 2 * (J.card : ℝ) ^ 3 * (24 * (n : ℝ) ^ 2) =
            ((L.card : ℝ) * (J.card : ℝ)) * ((L.card : ℝ) * (J.card : ℝ) ^ 2 * (24 * (n : ℝ) ^ 2)) := by ring
        rw [heq]
        exact mul_le_mul_of_nonneg_right hLm (by positivity)
      have h2 : (c_avoid * (n : ℝ) / 200) * ((L.card : ℝ) * (J.card : ℝ) ^ 2 * (24 * (n : ℝ) ^ 2)) ≤
          c_avoid * (L.card : ℝ) * (J.card : ℝ) ^ 2 * ((n : ℝ) ^ 3 / 2) := by
        have hnn : 0 ≤ c_avoid * (L.card : ℝ) * (J.card : ℝ) ^ 2 * (n : ℝ) ^ 3 := by
          have := c_avoid_pos; positivity
        have heq1 : (c_avoid * (n : ℝ) / 200) * ((L.card : ℝ) * (J.card : ℝ) ^ 2 * (24 * (n : ℝ) ^ 2)) =
            (24 / 200 : ℝ) * (c_avoid * (L.card : ℝ) * (J.card : ℝ) ^ 2 * (n : ℝ) ^ 3) := by ring
        have heq2 : c_avoid * (L.card : ℝ) * (J.card : ℝ) ^ 2 * ((n : ℝ) ^ 3 / 2) =
            (1 / 2 : ℝ) * (c_avoid * (L.card : ℝ) * (J.card : ℝ) ^ 2 * (n : ℝ) ^ 3) := by ring
        linarith
      have h3 : c_avoid * (L.card : ℝ) * (J.card : ℝ) ^ 2 * ((n : ℝ) ^ 3 / 2) ≤
          c_avoid * (L.card : ℝ) * (J.card : ℝ) ^ 2 * ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2)) :=
        mul_le_mul_of_nonneg_left hden_ge (by have := c_avoid_pos; positivity)
      linarith
    have hdiff : c_avoid * (L.card : ℝ) * (J.card : ℝ) ^ 2 / (24 * (n : ℝ) ^ 2) =
        c_avoid * (L.card : ℝ) * (J.card : ℝ) ^ 2 / (12 * (n : ℝ) ^ 2) -
        c_avoid * (L.card : ℝ) * (J.card : ℝ) ^ 2 / (24 * (n : ℝ) ^ 2) := by ring
    linarith
  -- Step 2: Rule out `Y.card > c_avoid * n / (200 * J.card)`
  have hY_small : (Y.card : ℝ) ≤ c_avoid * (n : ℝ) / (200 * (J.card : ℝ)) := by
    by_contra hgt; push Not at hgt
    let ℓ := Nat.floor (c_avoid * (n : ℝ) / (200 * (J.card : ℝ)))
    have hℓ_le_R : (ℓ : ℝ) ≤ c_avoid * (n : ℝ) / (200 * (J.card : ℝ)) :=
      Nat.floor_le (div_nonneg (mul_nonneg c_avoid_pos.le hn_pos.le) (by positivity))
    have hℓ_le_Y : ℓ ≤ Y.card := by
      have : (ℓ : ℝ) < (Y.card : ℝ) := lt_of_le_of_lt hℓ_le_R hgt
      exact_mod_cast this.le
    obtain ⟨L, hLY, hLcard⟩ := Finset.exists_subset_card_eq hℓ_le_Y
    have hlow := hbonf L hLY (by rwa [hLcard])
    rw [hLcard] at hlow
    have hℓ_ge : c_avoid * (n : ℝ) / (400 * (J.card : ℝ)) ≤ (ℓ : ℝ) := by
      have h1 : c_avoid * (n : ℝ) / (200 * (J.card : ℝ)) - 1 < (ℓ : ℝ) :=
        Nat.sub_one_lt_floor (c_avoid * (n : ℝ) / (200 * (J.card : ℝ)))
      have h2 : (2 : ℝ) ≤ c_avoid * (n : ℝ) / (200 * (J.card : ℝ)) := by
        rw [le_div_iff₀ (by positivity : 0 < 200 * (J.card : ℝ))]
        have h3 := (div_le_iff₀ c_avoid_pos).mp hbig_c
        have h4 := mul_le_mul_of_nonneg_right h3 hsq_pos.le
        have h5 : 400 * (J.card : ℝ) ≤ 400 * (b_const * Real.sqrt (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hJ_hi (by norm_num)
        nlinarith [hsq_sq]
      have hhalf : c_avoid * (n : ℝ) / (400 * (J.card : ℝ)) =
          (c_avoid * (n : ℝ) / (200 * (J.card : ℝ))) / 2 := by ring
      linarith
    have hH_contra : (c_avoid ^ 2 * a_const / 20000) / Real.sqrt (n : ℝ) ≤ H := by
      refine le_trans ?_ hlow
      have h1 : c_avoid * (c_avoid * (n : ℝ) / (400 * (J.card : ℝ))) * (J.card : ℝ) ^ 2 / (24 * (n : ℝ) ^ 2) ≤
          c_avoid * (ℓ : ℝ) * (J.card : ℝ) ^ 2 / (24 * (n : ℝ) ^ 2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hℓ_ge c_avoid_pos.le) (sq_nonneg _)
      refine le_trans ?_ h1
      have hsimp : c_avoid * (c_avoid * (n : ℝ) / (400 * (J.card : ℝ))) * (J.card : ℝ) ^ 2 / (24 * (n : ℝ) ^ 2) =
          c_avoid ^ 2 * (J.card : ℝ) / (9600 * (n : ℝ)) := by
        have hmne := hm_pos.ne'
        have hnne := hn_pos.ne'
        field_simp; ring
      rw [hsimp, div_le_div_iff₀ hsq_pos (by positivity : 0 < 9600 * (n : ℝ))]
      have hmul := mul_le_mul_of_nonneg_left hJ_lo (sq_nonneg c_avoid)
      have hmul2 := mul_le_mul_of_nonneg_right hmul hsq_pos.le
      have hc2a : 0 ≤ c_avoid ^ 2 * a_const * (n : ℝ) := by unfold a_const; positivity
      have hlhs : c_avoid ^ 2 * a_const / 20000 * (9600 * (n : ℝ)) =
          (9600 / 20000 : ℝ) * (c_avoid ^ 2 * a_const * (n : ℝ)) := by ring
      have hrhs : c_avoid ^ 2 * (a_const * Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ) =
          c_avoid ^ 2 * a_const * (n : ℝ) := by
        calc c_avoid ^ 2 * (a_const * Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ)
            = c_avoid ^ 2 * a_const * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by ring
          _ = c_avoid ^ 2 * a_const * (n : ℝ) := by rw [hsq_sq]
      linarith
    exact not_lt_of_ge hH_contra hH_small
  -- Step 3: Apply `hbonf` to `L = Y` and bound `μ (S.filter (·.1 x ∈ Y)) ≤ (δ_const / n) * Y.card ≤ H / 4`
  have hY_bonf := hbonf Y (Finset.Subset.refl Y) hY_small
  have hY_card_le : (Y.card : ℝ) ≤ 24 * H * (n : ℝ) ^ 2 / (c_avoid * (J.card : ℝ) ^ 2) := by
    have hpos : 0 < c_avoid * (J.card : ℝ) ^ 2 := mul_pos c_avoid_pos (sq_pos_of_pos hm_pos)
    rw [le_div_iff₀ hpos]
    have h1 := (div_le_iff₀ (by positivity : 0 < 24 * (n : ℝ) ^ 2)).mp hY_bonf
    linarith
  have hS_Y : μ (S.filter fun σ => σ.1 x ∈ Y) ≤ (δ_const / (n : ℝ)) * (Y.card : ℝ) := by
    have hpart : S.filter (fun σ => σ.1 x ∈ Y) = Y.biUnion fun y => S.filter fun σ => σ.1 x = y := by
      ext σ; simp only [Finset.mem_filter, Finset.mem_biUnion]
      exact ⟨fun ⟨h1, h2⟩ => ⟨σ.1 x, h2, h1, rfl⟩, fun ⟨y, hy, h1, h2⟩ => ⟨h1, h2 ▸ hy⟩⟩
    rw [hpart]
    calc μ (Y.biUnion fun y => S.filter fun σ => σ.1 x = y)
        ≤ ∑ y ∈ Y, μ (S.filter fun σ => σ.1 x = y) := μ_biUnion_le _ _
      _ ≤ ∑ _y ∈ Y, (δ_const / (n : ℝ)) := Finset.sum_le_sum fun y hy => by
          have hynJ : y ∉ J := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1).2
          have hd := houtside_dens y hynJ
          have hfib := μ_fiber1 (by omega) x y
          unfold μ at hfib ⊢
          have hΩ_eq : ((Finset.univ.filter fun π : Alt n => π.1 x = y).card : ℝ) =
              (Fintype.card (Alt n) : ℝ) / (n : ℝ) := by
            have := (div_eq_iff hcard_alt_pos.ne').mp hfib
            linarith [show (1 / (n : ℝ)) * (Fintype.card (Alt n) : ℝ) = (Fintype.card (Alt n) : ℝ) / (n : ℝ) by ring]
          rw [hΩ_eq] at hd
          have hpos_Ω : 0 < (Fintype.card (Alt n) : ℝ) / (n : ℝ) := div_pos hcard_alt_pos hn_pos
          have h1 := (div_lt_iff₀ hpos_Ω).mp hd
          rw [div_le_div_iff₀ hcard_alt_pos hn_pos]
          have h2 : δ_const * ((Fintype.card (Alt n) : ℝ) / (n : ℝ)) * (n : ℝ) =
              δ_const * (Fintype.card (Alt n) : ℝ) := by field_simp
          nlinarith
      _ = (δ_const / (n : ℝ)) * (Y.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  refine hS_Y.trans ?_
  have h1 : (δ_const / (n : ℝ)) * (Y.card : ℝ) ≤ (δ_const / (n : ℝ)) * (24 * H * (n : ℝ) ^ 2 / (c_avoid * (J.card : ℝ) ^ 2)) :=
    mul_le_mul_of_nonneg_left hY_card_le (div_nonneg δ_const_pos.le hn_pos.le)
  have hJsq : a_const ^ 2 * (n : ℝ) ≤ (J.card : ℝ) ^ 2 := by
    have ha0 : 0 ≤ a_const * Real.sqrt (n : ℝ) := by unfold a_const; positivity
    have hsq2 := pow_le_pow_left₀ ha0 hJ_lo 2
    rw [mul_pow, Real.sq_sqrt hn_pos.le] at hsq2
    exact hsq2
  have h2 : (δ_const / (n : ℝ)) * (24 * H * (n : ℝ) ^ 2 / (c_avoid * (J.card : ℝ) ^ 2)) ≤
      (24 * δ_const / (c_avoid * a_const ^ 2)) * H := by
    have hH_nn : 0 ≤ H := μ_nonneg _
    have hca : 0 < c_avoid * (a_const ^ 2 * (n : ℝ)) := by
      unfold a_const; exact mul_pos c_avoid_pos (mul_pos (by norm_num) hn_pos)
    have hle : 24 * H * (n : ℝ) ^ 2 / (c_avoid * (J.card : ℝ) ^ 2) ≤
        24 * H * (n : ℝ) ^ 2 / (c_avoid * (a_const ^ 2 * (n : ℝ))) :=
      div_le_div_of_nonneg_left (by positivity) hca (mul_le_mul_of_nonneg_left hJsq c_avoid_pos.le)
    have hmul := mul_le_mul_of_nonneg_left hle (div_nonneg δ_const_pos.le hn_pos.le)
    have heq : (δ_const / (n : ℝ)) * (24 * H * (n : ℝ) ^ 2 / (c_avoid * (a_const ^ 2 * (n : ℝ)))) =
        (24 * δ_const / (c_avoid * a_const ^ 2)) * H := by
      have hcne := c_avoid_pos.ne'
      have hane : a_const ≠ 0 := by unfold a_const; norm_num
      field_simp
    linarith
  have hcoef : 24 * δ_const / (c_avoid * a_const ^ 2) ≤ 1 / 4 := by
    unfold δ_const a_const
    have hcne := c_avoid_pos.ne'
    have : 24 * (c_avoid / 1000000) / (c_avoid * (1 / 100 : ℝ) ^ 2) = 24 / 100 := by field_simp; ring
    linarith
  have hH_nn : 0 ≤ H := μ_nonneg _
  nlinarith

set_option maxHeartbeats 800000 in
/-- Non-exceptional outside targets (`y ∉ J ∪ Y`) contribute at most `H / 4` to `μ (S \ F)`. -/
private lemma non_exceptional_Z0_bound {n : ℕ} (hn : 100000 ≤ n)
    (S : Finset (Alt n)) (hpf : ProdFree (S : Set (Alt n)))
    (x : Fin n) (J : Finset (Fin n)) (hxJ : x ∉ J)
    (hJ_lo : a_const * Real.sqrt (n : ℝ) ≤ (J.card : ℝ))
    (hJ_hi : (J.card : ℝ) ≤ b_const * Real.sqrt (n : ℝ))
    (hH_small : μ ((Finset.univ.filter fun π : Alt n => π.1 x ∈ J ∧ ∀ a ∈ J, π.1 a ∉ J) \ S) ≤
      (c_avoid * a_const / 200) / Real.sqrt (n : ℝ))
    (hexp_small : (1 / 2 : ℝ) ^ J.card ≤ (c_avoid * a_const ^ 2) / (48 * (n : ℝ))) :
    let F := Finset.univ.filter fun π : Alt n => π.1 x ∈ J ∧ ∀ a ∈ J, π.1 a ∉ J
    let Q := F \ S
    let Y := (Finset.univ \ J).filter fun y =>
      (J.card : ℝ) ^ 2 / 4 ≤
        (((J ×ˢ J).filter fun p =>
          (c_avoid / 3) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ μ (Q.filter fun π => π.1 x = p.2 ∧ π.1 p.1 = y)).card : ℝ)
    μ (S.filter fun σ => σ.1 x ∉ J ∧ σ.1 x ∉ Y) ≤ μ Q / 4 := by
  classical
  intro F Q Y
  let H := μ Q
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  have hsq_sq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn_pos.le
  have hnm1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (100000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hm_pos : (0 : ℝ) < (J.card : ℝ) := by
    have : 0 < a_const * Real.sqrt (n : ℝ) := by unfold a_const; positivity
    linarith
  let Bpred (i z : Fin n) : Prop :=
    (c_avoid / 3) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ μ (Q.filter fun π => π.1 x = i ∧ π.1 z = x)
  let Z0 : Finset (Fin n) := (Finset.univ.erase x).filter fun z =>
    (J.card : ℝ) / 2 ≤ ((J.filter fun i => Bpred i z).card : ℝ)
  -- Step 1: Disjointness of `Q ∩ {π.1 x = i ∧ π.1 z = x}` bounds `|Z0|`
  have hZ0_bound : (Z0.card : ℝ) ≤ 6 * H * (n : ℝ) * ((n : ℝ) - 1) / (c_avoid * (J.card : ℝ)) := by
    let Pairs := (J ×ˢ Z0).filter fun p => Bpred p.1 p.2
    have hdisj : Set.PairwiseDisjoint (Pairs : Set (Fin n × Fin n))
        (fun p => Q.filter fun π => π.1 x = p.1 ∧ π.1 p.2 = x) := by
      intro p₁ _ p₂ _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]
      intro π h1 h2
      have ⟨_, h1x, h1z⟩ := Finset.mem_filter.mp h1
      have ⟨_, h2x, h2z⟩ := Finset.mem_filter.mp h2
      exact hne (Prod.ext (h1x.symm.trans h2x) (π.1.injective (h1z.trans h2z.symm)))
    have hsub : Pairs.biUnion (fun p => Q.filter fun π => π.1 x = p.1 ∧ π.1 p.2 = x) ⊆ Q := by
      intro π hπ; obtain ⟨_, _, h2⟩ := Finset.mem_biUnion.mp hπ; exact (Finset.mem_filter.mp h2).1
    have hsum_le : ∑ p ∈ Pairs, μ (Q.filter fun π => π.1 x = p.1 ∧ π.1 p.2 = x) ≤ H := by
      rw [← μ_biUnion_of_disjoint hdisj]; exact μ_mono hsub
    have hPairs_card : (Z0.card : ℝ) * ((J.card : ℝ) / 2) ≤ (Pairs.card : ℝ) := by
      have hcard_eq : Pairs.card = ∑ z ∈ Z0, (J.filter fun i => Bpred i z).card := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product_right]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [hcard_eq, Nat.cast_sum]
      calc (Z0.card : ℝ) * ((J.card : ℝ) / 2)
          = ∑ _z ∈ Z0, ((J.card : ℝ) / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ z ∈ Z0, ((J.filter fun i => Bpred i z).card : ℝ) :=
            Finset.sum_le_sum fun z hz => (Finset.mem_filter.mp hz).2
    have hlow : (Pairs.card : ℝ) * ((c_avoid / 3) / ((n : ℝ) * ((n : ℝ) - 1))) ≤ H := by
      calc (Pairs.card : ℝ) * ((c_avoid / 3) / ((n : ℝ) * ((n : ℝ) - 1)))
          = ∑ _p ∈ Pairs, ((c_avoid / 3) / ((n : ℝ) * ((n : ℝ) - 1))) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ p ∈ Pairs, μ (Q.filter fun π => π.1 x = p.1 ∧ π.1 p.2 = x) :=
            Finset.sum_le_sum fun p hp => (Finset.mem_filter.mp hp).2
        _ ≤ H := hsum_le
    have h1 : (Z0.card : ℝ) * ((J.card : ℝ) / 2) * ((c_avoid / 3) / ((n : ℝ) * ((n : ℝ) - 1))) ≤ H :=
      (mul_le_mul_of_nonneg_right hPairs_card (div_nonneg (by linarith [c_avoid_pos]) (mul_pos hn_pos hnm1_pos).le)).trans hlow
    have hden_pos : 0 < c_avoid * (J.card : ℝ) := mul_pos c_avoid_pos hm_pos
    rw [le_div_iff₀ hden_pos]
    have h2 := mul_le_mul_of_nonneg_right h1 (show (0 : ℝ) ≤ 6 * (n : ℝ) * ((n : ℝ) - 1) by nlinarith)
    have hlhs : (Z0.card : ℝ) * ((J.card : ℝ) / 2) * ((c_avoid / 3) / ((n : ℝ) * ((n : ℝ) - 1))) *
        (6 * (n : ℝ) * ((n : ℝ) - 1)) = (Z0.card : ℝ) * (c_avoid * (J.card : ℝ)) := by
      have hne1 : (n : ℝ) ≠ 0 := hn_pos.ne'
      have hne2 : (n : ℝ) - 1 ≠ 0 := hnm1_pos.ne'
      field_simp; ring
    linarith
  -- Step 2: Every `σ ∈ S` with `σ.1 x ∉ J ∪ Y` hits `Z0` at `≥ s = (J.card + 1) / 2` elements of `J`
  let s : ℕ := (J.card + 1) / 2
  have hhit : ∀ σ ∈ S.filter (fun σ => σ.1 x ∉ J ∧ σ.1 x ∉ Y),
      s ≤ (J.filter fun k => σ⁻¹.1 k ∈ Z0).card := by
    intro σ hσ
    have ⟨hσS, hynJ, hynY⟩ := Finset.mem_filter.mp hσ
    let y := σ.1 x
    have hA_lt : (((J ×ˢ J).filter fun p =>
        (c_avoid / 3) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ μ (Q.filter fun π => π.1 x = p.2 ∧ π.1 p.1 = y)).card : ℝ) <
        (J.card : ℝ) ^ 2 / 4 := by
      by_contra hge; push Not at hge
      exact hynY (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hynJ⟩, hge⟩)
    let Bpairs := (J ×ˢ J).filter fun p => Bpred p.1 (σ⁻¹.1 p.2)
    have hB_gt : (3 / 4 : ℝ) * (J.card : ℝ) ^ 2 < (Bpairs.card : ℝ) := by
      have hcov : J ×ˢ J ⊆ ((J ×ˢ J).filter fun p =>
          (c_avoid / 3) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ μ (Q.filter fun π => π.1 x = p.2 ∧ π.1 p.1 = y)) ∪ Bpairs := by
        intro p hp
        have ⟨hi, hk⟩ := Finset.mem_product.mp hp
        rcases (two_point_dichotomy hn S hpf x J hxJ hJ_hi σ hσS hynJ p.1 p.2 hi hk).2 with hA | hB
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, hA⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, hB⟩)
      have hcard : (J.card : ℝ) ^ 2 ≤
          (((J ×ˢ J).filter fun p =>
            (c_avoid / 3) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ μ (Q.filter fun π => π.1 x = p.2 ∧ π.1 p.1 = y)).card : ℝ) +
          (Bpairs.card : ℝ) := by
        have h1 := (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
        rw [Finset.card_product] at h1
        have h1R : ((J.card * J.card : ℕ) : ℝ) ≤
            ((((J ×ˢ J).filter fun p =>
              (c_avoid / 3) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ μ (Q.filter fun π => π.1 x = p.2 ∧ π.1 p.1 = y)).card +
              Bpairs.card : ℕ) : ℝ) := by exact_mod_cast h1
        push_cast at h1R; nlinarith
      linarith
    let K_hit := J.filter fun k => σ⁻¹.1 k ∈ Z0
    have hB_up : (Bpairs.card : ℝ) ≤ (K_hit.card : ℝ) * (J.card : ℝ) + ((J.card : ℝ) - (K_hit.card : ℝ)) * ((J.card : ℝ) / 2) := by
      have hsum : (Bpairs.card : ℝ) = ∑ k ∈ J, ((J.filter fun i => Bpred i (σ⁻¹.1 k)).card : ℝ) := by
        have h1 : Bpairs.card = ∑ k ∈ J, (J.filter fun i => Bpred i (σ⁻¹.1 k)).card := by
          rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product_right]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        rw [h1, Nat.cast_sum]
      rw [hsum]
      have hterm : ∀ k ∈ J, ((J.filter fun i => Bpred i (σ⁻¹.1 k)).card : ℝ) ≤
          if k ∈ K_hit then (J.card : ℝ) else (J.card : ℝ) / 2 := by
        intro k hk
        by_cases hmem : k ∈ K_hit
        · simp only [hmem, ↓reduceIte]
          exact_mod_cast Finset.card_filter_le _ _
        · simp only [hmem, ↓reduceIte]
          have hzx : σ⁻¹.1 k ≠ x := (two_point_dichotomy hn S hpf x J hxJ hJ_hi σ hσS hynJ k k hk hk).1
          by_contra hgt; push Not at hgt
          exact hmem (Finset.mem_filter.mpr ⟨hk, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hzx, Finset.mem_univ _⟩, hgt.le⟩⟩)
      calc ∑ k ∈ J, ((J.filter fun i => Bpred i (σ⁻¹.1 k)).card : ℝ)
          ≤ ∑ k ∈ J, if k ∈ K_hit then (J.card : ℝ) else (J.card : ℝ) / 2 := Finset.sum_le_sum hterm
        _ = (K_hit.card : ℝ) * (J.card : ℝ) + ((J \ K_hit).card : ℝ) * ((J.card : ℝ) / 2) := by
            rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
            have h1 : J.filter (fun k => k ∈ K_hit) = K_hit := by
              rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (Finset.filter_subset _ _)]
            have h2 : J.filter (fun k => k ∉ K_hit) = J \ K_hit := by
              ext k; simp only [Finset.mem_filter, Finset.mem_sdiff]
            rw [h1, h2]
        _ = (K_hit.card : ℝ) * (J.card : ℝ) + ((J.card : ℝ) - (K_hit.card : ℝ)) * ((J.card : ℝ) / 2) := by
            rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.filter_subset _ _),
              Nat.cast_sub (Finset.card_le_card (Finset.filter_subset _ _))]
    have hK_gt : (J.card : ℝ) / 2 < (K_hit.card : ℝ) := by nlinarith
    have hK_nat : J.card < 2 * K_hit.card := by
      have : (J.card : ℝ) < (2 * K_hit.card : ℕ) := by push_cast; linarith
      exact_mod_cast this
    change s ≤ K_hit.card
    dsimp only [s]
    omega
  -- Step 3: Split on `Z0.card < s` vs `s ≤ Z0.card`
  by_cases hZ_lt : Z0.card < s
  · have hempty : S.filter (fun σ => σ.1 x ∉ J ∧ σ.1 x ∉ Y) = ∅ := by
      ext σ; simp only [Finset.notMem_empty, iff_false]
      intro hσ
      have hs_le := hhit σ hσ
      have hsub : (J.filter fun k => σ⁻¹.1 k ∈ Z0).image σ⁻¹.1 ⊆ Z0 := by
        intro z hz; obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz; exact (Finset.mem_filter.mp hk).2
      have hle := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ σ⁻¹.1.injective] at hle
      omega
    rw [hempty]; simp only [μ, Finset.card_empty, Nat.cast_zero, zero_div]
    exact div_nonneg (μ_nonneg _) (by norm_num)
  · push Not at hZ_lt
    -- `H ≥ c_avoid * a_const^2 / (12 * n)`
    have hH_lower : c_avoid * a_const ^ 2 / (12 * (n : ℝ)) ≤ H := by
      have hs_ge : (J.card : ℝ) / 2 ≤ (Z0.card : ℝ) := by
        have hnat : J.card ≤ 2 * s := by dsimp only [s]; omega
        have h1 : (J.card : ℝ) ≤ 2 * (s : ℝ) := by exact_mod_cast hnat
        have h2 : (s : ℝ) ≤ (Z0.card : ℝ) := by exact_mod_cast hZ_lt
        linarith
      have h1 := hs_ge.trans hZ0_bound
      have h2 := (le_div_iff₀ (mul_pos c_avoid_pos hm_pos)).mp h1
      have hJsq : a_const ^ 2 * (n : ℝ) ≤ (J.card : ℝ) ^ 2 := by
        have ha0 : 0 ≤ a_const * Real.sqrt (n : ℝ) := by unfold a_const; positivity
        have hsq2 := pow_le_pow_left₀ ha0 hJ_lo 2
        rw [mul_pow, Real.sq_sqrt hn_pos.le] at hsq2
        exact hsq2
      have h3 : c_avoid * a_const ^ 2 * (n : ℝ) ≤ 12 * H * (n : ℝ) * ((n : ℝ) - 1) := by
        have hmul := mul_le_mul_of_nonneg_left hJsq c_avoid_pos.le
        nlinarith
      rw [div_le_iff₀ (by positivity : 0 < 12 * (n : ℝ))]
      have hH_nn : 0 ≤ H := μ_nonneg _
      nlinarith
    -- `Z0.card ≤ n / 32`
    have hZ0_small : (Z0.card : ℝ) ≤ (n : ℝ) / 32 := by
      refine hZ0_bound.trans ?_
      have h1 : 6 * H * (n : ℝ) * ((n : ℝ) - 1) ≤ 6 * ((c_avoid * a_const / 200) / Real.sqrt (n : ℝ)) * (n : ℝ) ^ 2 := by
        have hH' : H ≤ (c_avoid * a_const / 200) / Real.sqrt (n : ℝ) := hH_small
        have hnn : 0 ≤ (c_avoid * a_const / 200) / Real.sqrt (n : ℝ) := by unfold a_const; have := c_avoid_pos; positivity
        have hprod1 : H * (n : ℝ) ≤ ((c_avoid * a_const / 200) / Real.sqrt (n : ℝ)) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right hH' hn_pos.le
        have hprod2 : H * (n : ℝ) * ((n : ℝ) - 1) ≤ ((c_avoid * a_const / 200) / Real.sqrt (n : ℝ)) * (n : ℝ) * (n : ℝ) :=
          mul_le_mul hprod1 (by linarith) hnm1_pos.le (mul_nonneg hnn hn_pos.le)
        nlinarith
      rw [div_le_div_iff₀ (mul_pos c_avoid_pos hm_pos) (by norm_num : (0 : ℝ) < 32)]
      have h2 : 6 * ((c_avoid * a_const / 200) / Real.sqrt (n : ℝ)) * (n : ℝ) ^ 2 * 32 ≤
          (n : ℝ) * (c_avoid * (a_const * Real.sqrt (n : ℝ))) := by
        have heq : 6 * ((c_avoid * a_const / 200) / Real.sqrt (n : ℝ)) * (n : ℝ) ^ 2 * 32 =
            (192 / 200 : ℝ) * ((n : ℝ) * (c_avoid * (a_const * Real.sqrt (n : ℝ)))) := by
          have hsqne := hsq_pos.ne'
          field_simp; rw [Real.sq_sqrt hn_pos.le]; ring
        have hnn : 0 ≤ (n : ℝ) * (c_avoid * (a_const * Real.sqrt (n : ℝ))) := by
          unfold a_const; have := c_avoid_pos; positivity
        linarith
      have h3 : (n : ℝ) * (c_avoid * (a_const * Real.sqrt (n : ℝ))) ≤ (n : ℝ) * (c_avoid * (J.card : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hJ_lo c_avoid_pos.le) hn_pos.le
      linarith
    -- Union bound over `K ∈ J.powersetCard s`
    have hcov : S.filter (fun σ => σ.1 x ∉ J ∧ σ.1 x ∉ Y) ⊆
        (J.powersetCard s).biUnion fun K => Finset.univ.filter fun σ : Alt n => ∀ k ∈ K, σ⁻¹.1 k ∈ Z0 := by
      intro σ hσ
      obtain ⟨K, hKsub, hKcard⟩ := Finset.exists_subset_card_eq (hhit σ hσ)
      exact Finset.mem_biUnion.mpr ⟨K, Finset.mem_powersetCard.mpr ⟨hKsub.trans (Finset.filter_subset _ _), hKcard⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun k hk => (Finset.mem_filter.mp (hKsub hk)).2⟩⟩
    have hs_small : s + 2 ≤ n ∧ (s : ℝ) ≤ (n : ℝ) / 2 := by
      have hsq300 : (300 : ℝ) ≤ Real.sqrt (n : ℝ) := by
        have : (90000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 90000 ≤ n by omega)
        calc (300 : ℝ) = Real.sqrt (90000 : ℝ) := by
              rw [show (90000 : ℝ) = 300 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
          _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt this
      have hsJ : s ≤ J.card := by dsimp only [s]; omega
      have h1 : (s : ℝ) ≤ 8 * Real.sqrt (n : ℝ) := le_trans (Nat.cast_le.mpr hsJ) (by unfold b_const at hJ_hi; exact hJ_hi)
      have h2 : (s : ℝ) + 2 ≤ (n : ℝ) / 2 := by nlinarith
      exact ⟨by exact_mod_cast (show (s : ℝ) + 2 ≤ (n : ℝ) by linarith), by linarith⟩
    have hper_K : ∀ K ∈ J.powersetCard s,
        μ (Finset.univ.filter fun σ : Alt n => ∀ k ∈ K, σ⁻¹.1 k ∈ Z0) ≤ (1 / 16 : ℝ) ^ s := by
      intro K hK
      have hKcard : K.card = s := (Finset.mem_powersetCard.mp hK).2
      -- Biject `σ ↦ σ⁻¹` to apply `card_alt_agree_and_avoid` with `U = ∅`, `A = K`, `B = univ \ Z0`
      have hcard_eq : (Finset.univ.filter fun σ : Alt n => ∀ k ∈ K, σ⁻¹.1 k ∈ Z0).card =
          (Finset.univ.filter fun τ : Alt n => (∀ u ∈ (∅ : Finset (Fin n)), τ.1 u = u) ∧
            ∀ k ∈ K, τ.1 k ∉ Finset.univ \ Z0).card := by
        refine Finset.card_bij (fun σ _ => σ⁻¹) (fun σ hσ => ?_) (fun _ _ _ _ h => inv_injective h) (fun τ hτ => ?_)
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, IsEmpty.forall_iff,
            Finset.mem_sdiff, not_not] at hσ ⊢
          exact ⟨fun _ => trivial, fun k hk => hσ k hk⟩
        · refine ⟨τ⁻¹, ?_, inv_inv τ⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, IsEmpty.forall_iff,
            Finset.mem_sdiff, not_not] at hτ ⊢
          intro k hk; simpa using hτ.2 k hk
      have hcount := card_alt_agree_and_avoid (∅ : Finset (Fin n)) K (Finset.univ \ Z0)
        (Finset.disjoint_empty_left K) (by simp [hKcard]; omega) id (by simp)
      have hsdiff_eq : (Finset.univ \ ((∅ : Finset (Fin n)).image id ∪ (Finset.univ \ Z0))).card = Z0.card := by
        have : Finset.univ \ ((∅ : Finset (Fin n)).image id ∪ (Finset.univ \ Z0)) = Z0 := by
          ext z; simp
        rw [this]
      rw [hsdiff_eq, Finset.card_empty, Nat.sub_zero, hKcard] at hcount
      have hcard_alt := card_alt (n := n) (by omega)
      have hμ_eq : μ (Finset.univ.filter fun σ : Alt n => ∀ k ∈ K, σ⁻¹.1 k ∈ Z0) =
          ((Z0.card.descFactorial s : ℕ) : ℝ) / ((n.descFactorial s : ℕ) : ℝ) := by
        unfold μ
        rw [hcard_eq]
        have hfac : n.factorial = n.descFactorial s * (n - s).factorial := by
          rw [mul_comm, Nat.factorial_mul_descFactorial (by omega)]
        have h1 : (2 : ℝ) * ((Finset.univ.filter fun τ : Alt n => (∀ u ∈ (∅ : Finset (Fin n)), τ.1 u = u) ∧
            ∀ k ∈ K, τ.1 k ∉ Finset.univ \ Z0).card : ℝ) =
            ((Z0.card.descFactorial s : ℕ) : ℝ) * (((n - s).factorial : ℕ) : ℝ) := by
          exact_mod_cast hcount
        have h2 : (2 : ℝ) * (Fintype.card (Alt n) : ℝ) =
            ((n.descFactorial s : ℕ) : ℝ) * (((n - s).factorial : ℕ) : ℝ) := by
          exact_mod_cast hcard_alt.trans hfac
        have hpos_alt : (0 : ℝ) < (Fintype.card (Alt n) : ℝ) := by exact_mod_cast card_alt_pos (by omega)
        have hpos_df : (0 : ℝ) < ((n.descFactorial s : ℕ) : ℝ) := by
          exact_mod_cast Nat.descFactorial_pos.mpr (by omega)
        have hpos_fac : (0 : ℝ) < (((n - s).factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
        rw [div_eq_div_iff hpos_alt.ne' hpos_df.ne']
        nlinarith
      rw [hμ_eq]
      -- Bound `(Z0.card.descFactorial s) / (n.descFactorial s) ≤ (Z0.card / (n - s))^s ≤ (1/16)^s`
      have hdf_ratio : ((Z0.card.descFactorial s : ℕ) : ℝ) / ((n.descFactorial s : ℕ) : ℝ) ≤
          ((Z0.card : ℝ) / ((n : ℝ) - (s : ℝ))) ^ s := by
        rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range, Nat.cast_prod, Nat.cast_prod,
          ← Finset.prod_div_distrib]
        calc ∏ i ∈ Finset.range s, (((Z0.card - i : ℕ) : ℝ) / ((n - i : ℕ) : ℝ))
            ≤ ∏ _i ∈ Finset.range s, ((Z0.card : ℝ) / ((n : ℝ) - (s : ℝ))) :=
              Finset.prod_le_prod (fun i _ => by positivity) fun i hi => by
                have hi_lt : i < s := Finset.mem_range.mp hi
                have hnum : ((Z0.card - i : ℕ) : ℝ) ≤ (Z0.card : ℝ) := by exact_mod_cast Nat.sub_le Z0.card i
                have hden : (n : ℝ) - (s : ℝ) ≤ ((n - i : ℕ) : ℝ) := by
                  rw [Nat.cast_sub (by omega)]
                  have : (i : ℝ) ≤ (s : ℝ) := by exact_mod_cast hi_lt.le
                  linarith
                have hns_pos : 0 < (n : ℝ) - (s : ℝ) := by linarith [hs_small.2]
                exact (div_le_div_of_nonneg_right hnum (by exact_mod_cast (show 0 ≤ n - i by omega))).trans
                  (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hns_pos hden)
          _ = ((Z0.card : ℝ) / ((n : ℝ) - (s : ℝ))) ^ s := by rw [Finset.prod_const, Finset.card_range]
      refine hdf_ratio.trans (pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) (by linarith [hs_small.2])) ?_ s)
      rw [div_le_iff₀ (by linarith [hs_small.2])]
      linarith [hZ0_small, hs_small.2]
    have hP_card : ((J.powersetCard s).card : ℝ) ≤ (2 : ℝ) ^ J.card := by
      have h1 : (J.powersetCard s).card ≤ J.powerset.card :=
        Finset.card_le_card fun K hK => Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hK).1
      rw [Finset.card_powerset] at h1
      exact_mod_cast h1
    calc μ (S.filter fun σ => σ.1 x ∉ J ∧ σ.1 x ∉ Y)
        ≤ ∑ K ∈ J.powersetCard s, μ (Finset.univ.filter fun σ : Alt n => ∀ k ∈ K, σ⁻¹.1 k ∈ Z0) :=
          (μ_mono hcov).trans (μ_biUnion_le _ _)
      _ ≤ ∑ _K ∈ J.powersetCard s, (1 / 16 : ℝ) ^ s := Finset.sum_le_sum hper_K
      _ = ((J.powersetCard s).card : ℝ) * (1 / 16 : ℝ) ^ s := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ J.card * (1 / 16 : ℝ) ^ s := mul_le_mul_of_nonneg_right hP_card (by positivity)
      _ ≤ (1 / 2 : ℝ) ^ J.card := by
          have h2s : J.card ≤ 2 * s := by dsimp only [s]; omega
          have h1 : (1 / 16 : ℝ) ^ s = (1 / 4 : ℝ) ^ (2 * s) := by
            rw [pow_mul]; norm_num
          have h2 : (1 / 4 : ℝ) ^ (2 * s) ≤ (1 / 4 : ℝ) ^ J.card :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) h2s
          have h3 : (2 : ℝ) ^ J.card * (1 / 4 : ℝ) ^ J.card = (1 / 2 : ℝ) ^ J.card := by
            rw [← mul_pow]; norm_num
          calc (2 : ℝ) ^ J.card * (1 / 16 : ℝ) ^ s
              = (2 : ℝ) ^ J.card * (1 / 4 : ℝ) ^ (2 * s) := by rw [h1]
            _ ≤ (2 : ℝ) ^ J.card * (1 / 4 : ℝ) ^ J.card := mul_le_mul_of_nonneg_left h2 (by positivity)
            _ = (1 / 2 : ℝ) ^ J.card := h3
      _ ≤ (c_avoid * a_const ^ 2) / (48 * (n : ℝ)) := hexp_small
      _ ≤ H / 4 := by
          have : (c_avoid * a_const ^ 2) / (48 * (n : ℝ)) = (c_avoid * a_const ^ 2 / (12 * (n : ℝ))) / 4 := by ring
          linarith

end OutsideTargets

/- ### Section 5: Assembly (`forward_exact` and `OMA.solution`) -/

section Assembly

/-- Forward stability-to-exactness upgrade for large `n`. -/
private lemma forward_exact {n : ℕ} (hn : 100000000 ≤ n)
    (h1 : 100 / δ_const ≤ Real.sqrt (n : ℝ))
    (h2 : (40000 : ℝ) * (2 * b_const ^ 2 / η_const) / ((c_avoid * δ_const) ^ 2 * (n : ℝ) ^ ((1 : ℝ) / 4)) ≤ 1 / 16)
    (h3 : (1 + 200 / δ_const) * (n : ℝ) ^ (-(33 : ℝ) / 50) ≤ (1 / 200 : ℝ) / Real.sqrt (n : ℝ))
    (h4 : (2 / δ_const) * (n : ℝ) * (n : ℝ) ^ (-(33 : ℝ) / 50) ≤ a_const * Real.sqrt (n : ℝ))
    (h5 : (n : ℝ) ^ (-(33 : ℝ) / 50) < c_avoid * a_const / Real.sqrt (n : ℝ))
    (h6 : (1 + 200 / δ_const) * (n : ℝ) ^ (-(33 : ℝ) / 50) ≤ (η_const ^ 2 / (16 * b_const)) / Real.sqrt (n : ℝ))
    (h7 : (1 + 200 / δ_const) * (n : ℝ) ^ (-(33 : ℝ) / 50) < (c_avoid ^ 2 * a_const / 20000) / Real.sqrt (n : ℝ))
    (h8 : (1 + 200 / δ_const) * (n : ℝ) ^ (-(33 : ℝ) / 50) ≤ (c_avoid * a_const / 200) / Real.sqrt (n : ℝ))
    (h9 : 400 * b_const / c_avoid ≤ Real.sqrt (n : ℝ))
    (h10 : ∀ m : ℕ, a_const * Real.sqrt (n : ℝ) ≤ (m : ℝ) → (1 / 2 : ℝ) ^ m ≤ (c_avoid * a_const ^ 2) / (48 * (n : ℝ)))
    (S : Set (Alt n)) (hpf : ProdFree S)
    (hmax : ∀ (z : Fin n) (K : Set (Fin n)), (extremalFamily z K).ncard ≤ S.ncard)
    (x : Fin n) (I : Set (Fin n))
    (happrox : ((S \ extremalFamily x I).ncard : ℝ) / (Fintype.card (Alt n) : ℝ) < (n : ℝ) ^ (-(33 : ℝ) / 50)) :
    ∃ (J : Set (Fin n)), S ⊆ extremalFamily x J := by
  classical
  let Sf : Finset (Alt n) := S.toFinset
  let If : Finset (Fin n) := I.toFinset
  have hSf_coe : (Sf : Set (Alt n)) = S := Set.coe_toFinset S
  have hF_eq : ∀ (z : Fin n) (Kf : Finset (Fin n)),
      ((Finset.univ.filter fun π : Alt n => π.1 z ∈ Kf ∧ ∀ a ∈ Kf, π.1 a ∉ Kf) : Set (Alt n)) =
        extremalFamily z (Kf : Set (Fin n)) := by
    intro z Kf; ext π
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, extremalFamily, Set.mem_setOf_eq,
      Set.disjoint_left, Set.mem_image]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun y ⟨a, ha, hay⟩ => hay ▸ h2 a ha⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun a ha => h2 ⟨a, ha, rfl⟩⟩
  have hmax_f : ∀ (z : Fin n) (Kf : Finset (Fin n)),
      (Finset.univ.filter fun π : Alt n => π.1 z ∈ Kf ∧ ∀ a ∈ Kf, π.1 a ∉ Kf).card ≤ Sf.card := by
    intro z Kf
    have h1 := hmax z (Kf : Set (Fin n))
    rw [← hF_eq z Kf, ← hSf_coe, Set.ncard_coe_finset, Set.ncard_coe_finset] at h1
    exact h1
  have happrox_f : μ (Sf \ Finset.univ.filter fun π : Alt n => π.1 x ∈ If ∧ ∀ a ∈ If, π.1 a ∉ If) <
      (n : ℝ) ^ (-(33 : ℝ) / 50) := by
    unfold μ
    rw [← Set.ncard_coe_finset, Finset.coe_sdiff, hSf_coe, hF_eq x If, Set.coe_toFinset I]
    exact happrox
  let p (j : Fin n) : ℝ :=
    ((Sf.filter fun π => π.1 x = j).card : ℝ) / ((Finset.univ.filter fun π : Alt n => π.1 x = j).card : ℝ)
  let Jf : Finset (Fin n) := Finset.univ.filter fun j => δ_const ≤ p j
  let Ff : Finset (Alt n) := Finset.univ.filter fun π : Alt n => π.1 x ∈ Jf ∧ ∀ a ∈ Jf, π.1 a ∉ Jf
  obtain ⟨hxJ, hJ_lo, hJ_hi, hH_le_E, hH_upper⟩ :=
    threshold_J_props (by omega) h3 h4 h5 Sf (by rwa [hSf_coe]) hmax_f x If happrox_f
  have hJ_dens : ∀ j ∈ Jf, δ_const ≤ p j := fun j hj => (Finset.mem_filter.mp hj).2
  have hout_dens : ∀ y ∉ Jf, p y < δ_const := fun y hy => by
    by_contra hge; push Not at hge
    exact hy (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hge⟩)
  have hEin := inside_edges_le hn h1 h2 Sf (by rwa [hSf_coe]) x Jf hxJ hJ_lo hJ_hi hJ_dens (hH_upper.trans h6)
  have hEY := exceptional_Y_bound (by omega) h9 Sf x Jf hxJ hJ_lo hJ_hi hout_dens (hH_upper.trans_lt h7)
  have hEZ := non_exceptional_Z0_bound (by omega) Sf (by rwa [hSf_coe]) x Jf hxJ hJ_lo hJ_hi
    (hH_upper.trans h8) (h10 Jf.card hJ_lo)
  let Y := (Finset.univ \ Jf).filter fun y =>
    (Jf.card : ℝ) ^ 2 / 4 ≤
      (((Jf ×ˢ Jf).filter fun p =>
        (c_avoid / 3) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ μ ((Ff \ Sf).filter fun π => π.1 x = p.2 ∧ π.1 p.1 = y)).card : ℝ)
  have hcov : Sf \ Ff ⊆
      ((Sf \ Ff).filter fun σ => σ.1 x ∈ Jf) ∪
      ((Sf.filter fun σ => σ.1 x ∈ Y) ∪ (Sf.filter fun σ => σ.1 x ∉ Jf ∧ σ.1 x ∉ Y)) := by
    intro σ hσ
    have hσS := (Finset.mem_sdiff.mp hσ).1
    by_cases h1 : σ.1 x ∈ Jf
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hσ, h1⟩)
    · by_cases h2 : σ.1 x ∈ Y
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hσS, h2⟩))
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hσS, h1, h2⟩))
  have hE_le : μ (Sf \ Ff) ≤ (3 / 4 : ℝ) * μ (Ff \ Sf) := by
    have h1 := (μ_mono hcov).trans ((μ_union_le _ _).trans (add_le_add le_rfl (μ_union_le _ _)))
    linarith
  have hE_zero : μ (Sf \ Ff) = 0 := by
    have hnn : 0 ≤ μ (Sf \ Ff) := μ_nonneg _
    have hnnH : 0 ≤ μ (Ff \ Sf) := μ_nonneg _
    linarith
  have hcard_zero : (Sf \ Ff).card = 0 := by
    unfold μ at hE_zero
    have hpos : (Fintype.card (Alt n) : ℝ) ≠ 0 := by exact_mod_cast (card_alt_pos (by omega)).ne'
    have h0 : ((Sf \ Ff).card : ℝ) = 0 := (div_eq_zero_iff.mp hE_zero).resolve_right hpos
    exact_mod_cast h0
  have hsub_f : Sf ⊆ Ff := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hcard_zero)
  refine ⟨(Jf : Set (Fin n)), ?_⟩
  rw [← hSf_coe, ← hF_eq x Jf]
  exact Finset.coe_subset.mpr hsub_f

end Assembly

end OMA.P_Green4_H3

/-- Final proof of `Green4.large_green_4.R1.H3`. -/
theorem OMA.solution : OMA.R_Green4_large_green_4_R1.H3 := by
  open OMA.P_Green4_H3 in
  -- Collect all asymptotic thresholds on `n` via `Filter.Eventually`
  have h_n10 : ∀ᶠ n : ℕ in Filter.atTop, 100000000 ≤ n := Filter.eventually_ge_atTop _
  have h_sqrt_top : Filter.Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) Filter.atTop Filter.atTop :=
    (Real.tendsto_sqrt_atTop).comp tendsto_natCast_atTop_atTop
  have h_n4_top : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 4)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop
  have h_neg425 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (-(4 : ℝ) / 25)) Filter.atTop (nhds 0) := by
    simpa [Function.comp_def, neg_div] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4 / 25)).comp tendsto_natCast_atTop_atTop
  have h1 : ∀ᶠ n : ℕ in Filter.atTop, 100 / δ_const ≤ Real.sqrt (n : ℝ) :=
    h_sqrt_top.eventually (Filter.eventually_ge_atTop _)
  have h9 : ∀ᶠ n : ℕ in Filter.atTop, 400 * b_const / c_avoid ≤ Real.sqrt (n : ℝ) :=
    h_sqrt_top.eventually (Filter.eventually_ge_atTop _)
  have h2 : ∀ᶠ n : ℕ in Filter.atTop,
      (40000 : ℝ) * (2 * b_const ^ 2 / η_const) / ((c_avoid * δ_const) ^ 2 * (n : ℝ) ^ ((1 : ℝ) / 4)) ≤ 1 / 16 := by
    have ht : Filter.Tendsto (fun n : ℕ =>
        (40000 : ℝ) * (2 * b_const ^ 2 / η_const) / ((c_avoid * δ_const) ^ 2 * (n : ℝ) ^ ((1 : ℝ) / 4)))
        Filter.atTop (nhds 0) := by
      have hconst_pos : 0 < (c_avoid * δ_const) ^ 2 := sq_pos_of_pos (mul_pos c_avoid_pos δ_const_pos)
      have hden : Filter.Tendsto (fun n : ℕ => (c_avoid * δ_const) ^ 2 * (n : ℝ) ^ ((1 : ℝ) / 4))
          Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop hconst_pos h_n4_top
      exact tendsto_const_nhds.div_atTop hden
    exact ht.eventually (Iic_mem_nhds (by norm_num))
  -- Helper: `n^(-33/50) * √n = n^(-4/25) → 0`
  have hprod_zero : ∀ C > (0 : ℝ), ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ (-(33 : ℝ) / 50) < C / Real.sqrt (n : ℝ) := by
    intro C hC
    filter_upwards [Filter.eventually_ge_atTop 1, h_neg425.eventually (Iio_mem_nhds hC)] with n hn hlt
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
    rw [lt_div_iff₀ hsq_pos, Real.sqrt_eq_rpow, ← Real.rpow_add hn_pos]
    have hexp : -(33 : ℝ) / 50 + 1 / 2 = -(4 : ℝ) / 25 := by norm_num
    rwa [hexp]
  have hcoef_pos : 0 < 1 + 200 / δ_const := by have := δ_const_pos; positivity
  have h3 : ∀ᶠ n : ℕ in Filter.atTop,
      (1 + 200 / δ_const) * (n : ℝ) ^ (-(33 : ℝ) / 50) ≤ (1 / 200 : ℝ) / Real.sqrt (n : ℝ) := by
    filter_upwards [hprod_zero ((1 / 200 : ℝ) / (1 + 200 / δ_const)) (by positivity)] with n hn
    have := mul_le_mul_of_nonneg_left hn.le hcoef_pos.le
    have heq : (1 + 200 / δ_const) * ((1 / 200 : ℝ) / (1 + 200 / δ_const) / Real.sqrt (n : ℝ)) =
        (1 / 200 : ℝ) / Real.sqrt (n : ℝ) := by field_simp
    linarith
  have h4 : ∀ᶠ n : ℕ in Filter.atTop,
      (2 / δ_const) * (n : ℝ) * (n : ℝ) ^ (-(33 : ℝ) / 50) ≤ a_const * Real.sqrt (n : ℝ) := by
    have hC_pos : 0 < a_const / (2 / δ_const) := by unfold a_const; have := δ_const_pos; positivity
    filter_upwards [Filter.eventually_ge_atTop 1, hprod_zero (a_const / (2 / δ_const)) hC_pos] with n hn hlt
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
    have h1 := mul_le_mul_of_nonneg_left hlt.le (show 0 ≤ (2 / δ_const) * (n : ℝ) by have := δ_const_pos; positivity)
    have h2 : (2 / δ_const) * (n : ℝ) * (a_const / (2 / δ_const) / Real.sqrt (n : ℝ)) = a_const * Real.sqrt (n : ℝ) := by
      have hδne := δ_const_pos.ne'
      have hsqne := hsq_pos.ne'
      field_simp; rw [Real.sq_sqrt hn_pos.le]; ring
    linarith
  have h5 : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ (-(33 : ℝ) / 50) < c_avoid * a_const / Real.sqrt (n : ℝ) :=
    hprod_zero (c_avoid * a_const) (by unfold a_const; exact mul_pos c_avoid_pos (by norm_num))
  have h6 : ∀ᶠ n : ℕ in Filter.atTop,
      (1 + 200 / δ_const) * (n : ℝ) ^ (-(33 : ℝ) / 50) ≤ (η_const ^ 2 / (16 * b_const)) / Real.sqrt (n : ℝ) := by
    have hC_pos : 0 < (η_const ^ 2 / (16 * b_const)) / (1 + 200 / δ_const) := by
      unfold b_const; have := η_const_pos; positivity
    filter_upwards [hprod_zero _ hC_pos] with n hn
    have := mul_le_mul_of_nonneg_left hn.le hcoef_pos.le
    have heq : (1 + 200 / δ_const) * ((η_const ^ 2 / (16 * b_const)) / (1 + 200 / δ_const) / Real.sqrt (n : ℝ)) =
        (η_const ^ 2 / (16 * b_const)) / Real.sqrt (n : ℝ) := by field_simp
    linarith
  have h7 : ∀ᶠ n : ℕ in Filter.atTop,
      (1 + 200 / δ_const) * (n : ℝ) ^ (-(33 : ℝ) / 50) < (c_avoid ^ 2 * a_const / 20000) / Real.sqrt (n : ℝ) := by
    have hC_pos : 0 < (c_avoid ^ 2 * a_const / 20000) / (1 + 200 / δ_const) := by
      unfold a_const; have := c_avoid_pos; positivity
    filter_upwards [hprod_zero _ hC_pos] with n hn
    have := mul_lt_mul_of_pos_left hn hcoef_pos
    have heq : (1 + 200 / δ_const) * ((c_avoid ^ 2 * a_const / 20000) / (1 + 200 / δ_const) / Real.sqrt (n : ℝ)) =
        (c_avoid ^ 2 * a_const / 20000) / Real.sqrt (n : ℝ) := by field_simp
    linarith
  have h8 : ∀ᶠ n : ℕ in Filter.atTop,
      (1 + 200 / δ_const) * (n : ℝ) ^ (-(33 : ℝ) / 50) ≤ (c_avoid * a_const / 200) / Real.sqrt (n : ℝ) := by
    have hC_pos : 0 < (c_avoid * a_const / 200) / (1 + 200 / δ_const) := by
      unfold a_const; have := c_avoid_pos; positivity
    filter_upwards [hprod_zero _ hC_pos] with n hn
    have := mul_le_mul_of_nonneg_left hn.le hcoef_pos.le
    have heq : (1 + 200 / δ_const) * ((c_avoid * a_const / 200) / (1 + 200 / δ_const) / Real.sqrt (n : ℝ)) =
        (c_avoid * a_const / 200) / Real.sqrt (n : ℝ) := by field_simp
    linarith
  have h10 : ∀ᶠ n : ℕ in Filter.atTop, ∀ m : ℕ, a_const * Real.sqrt (n : ℝ) ≤ (m : ℝ) →
      (1 / 2 : ℝ) ^ m ≤ (c_avoid * a_const ^ 2) / (48 * (n : ℝ)) := by
    -- Elementary: `2^m ≥ m^3 / 6` for all `m`, so for `m ≥ a_const √n`, `2^m ≥ a_const^3 n^(3/2) / 6 ≥ 48 n / (c_avoid a_const^2)`
    have h_big : ∀ᶠ n : ℕ in Filter.atTop, 288 / (c_avoid * a_const ^ 5) ≤ Real.sqrt (n : ℝ) :=
      h_sqrt_top.eventually (Filter.eventually_ge_atTop _)
    filter_upwards [Filter.eventually_ge_atTop 1, h_big] with n hn hsq m hm
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
    have h2pow : ((m : ℝ) ^ 3) / 6 ≤ (2 : ℝ) ^ m := by
      have hnat_all : ∀ r : ℕ, r ^ 3 ≤ 6 * 2 ^ r := by
        intro r
        induction r with
        | zero => norm_num
        | succ k ih =>
          rcases lt_or_ge k 4 with hk | hk
          · interval_cases k <;> norm_num
          · have hk2 : 4 * k ≤ k ^ 2 := by nlinarith
            have hk3 : 4 * k ^ 2 ≤ k ^ 3 := by nlinarith
            have h1 : (k + 1) ^ 3 ≤ 2 * k ^ 3 := by nlinarith
            have h2 : 6 * 2 ^ (k + 1) = 2 * (6 * 2 ^ k) := by rw [pow_succ]; ring
            linarith
      have hR : (m : ℝ) ^ 3 ≤ 6 * (2 : ℝ) ^ m := by exact_mod_cast hnat_all m
      linarith
    have hm3 : (a_const * Real.sqrt (n : ℝ)) ^ 3 ≤ (m : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by unfold a_const; positivity) hm 3
    have h48 : 48 * (n : ℝ) / (c_avoid * a_const ^ 2) ≤ (2 : ℝ) ^ m := by
      have ha_pos : 0 < a_const := by unfold a_const; norm_num
      have h1 : 48 * (n : ℝ) / (c_avoid * a_const ^ 2) ≤ (a_const * Real.sqrt (n : ℝ)) ^ 3 / 6 := by
        rw [div_le_div_iff₀ (mul_pos c_avoid_pos (sq_pos_of_pos ha_pos)) (by norm_num)]
        have hcube : (a_const * Real.sqrt (n : ℝ)) ^ 3 = a_const ^ 3 * (n : ℝ) * Real.sqrt (n : ℝ) := by
          have : (Real.sqrt (n : ℝ)) ^ 3 = Real.sqrt (n : ℝ) * (Real.sqrt (n : ℝ)) ^ 2 := by ring
          rw [mul_pow, this, Real.sq_sqrt hn_pos.le]; ring
        rw [hcube]
        have hmul := (div_le_iff₀ (mul_pos c_avoid_pos (pow_pos ha_pos 5))).mp hsq
        have hmul_n := mul_le_mul_of_nonneg_right hmul hn_pos.le
        nlinarith
      linarith
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
    rw [one_div, inv_pow, inv_le_comm₀ h2pos (by unfold a_const; have := c_avoid_pos; positivity)]
    have hinv : ((c_avoid * a_const ^ 2) / (48 * (n : ℝ)))⁻¹ = 48 * (n : ℝ) / (c_avoid * a_const ^ 2) := by
      rw [inv_div]
    rwa [hinv]
  filter_upwards [h_n10, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10] with
    n hn h1' h2' h3' h4' h5' h6' h7' h8' h9' h10'
  intro S hpf hmax hex
  obtain ⟨x, I, hcase⟩ := hex
  rcases hcase with hfwd | hinv
  · obtain ⟨J, hJ⟩ := forward_exact hn h1' h2' h3' h4' h5' h6' h7' h8' h9' h10' S hpf hmax x I hfwd
    exact ⟨x, J, Or.inl hJ⟩
  · -- Inverted case: apply `forward_exact` to `S' = S.image (·⁻¹)`
    let S' : Set (alternatingGroup (Fin n)) := S.image (·⁻¹)
    have hpf' : Green4.ProdFree S' := OMA.R_Green4_large_green_4_R1.inverse_product_free hpf
    have hcard_S' : S'.ncard = S.ncard := Set.ncard_image_of_injective S inv_injective
    have hmax' : ∀ (z : Fin n) (K : Set (Fin n)), (Green4.extremalFamily z K).ncard ≤ S'.ncard := by
      intro z K; rw [hcard_S']; exact hmax z K
    have hdiff_eq : (S' \ Green4.extremalFamily x I).ncard =
        (S \ (Green4.extremalFamily x I).image (·⁻¹)).ncard := by
      have himg : (S \ (Green4.extremalFamily x I).image (·⁻¹)).image (·⁻¹) = S' \ Green4.extremalFamily x I := by
        ext π
        simp only [S', Set.mem_image, Set.mem_diff]
        constructor
        · rintro ⟨σ, ⟨hσS, hσn⟩, rfl⟩
          exact ⟨⟨σ, hσS, rfl⟩, fun hmem => hσn ⟨σ⁻¹, hmem, inv_inv σ⟩⟩
        · rintro ⟨⟨σ, hσS, rfl⟩, hσn⟩
          exact ⟨σ, ⟨hσS, by rintro ⟨τ, hτ, hEq⟩; exact hσn (inv_injective (hEq.trans (inv_inv σ).symm) ▸ hτ)⟩, rfl⟩
      rw [← himg, Set.ncard_image_of_injective _ inv_injective]
    have hfwd' : ((S' \ Green4.extremalFamily x I).ncard : ℝ) / Fintype.card (alternatingGroup (Fin n)) <
        (n : ℝ) ^ (-(33 : ℝ) / 50) := by
      rwa [hdiff_eq]
    obtain ⟨J, hJ⟩ := forward_exact hn h1' h2' h3' h4' h5' h6' h7' h8' h9' h10' S' hpf' hmax' x I hfwd'
    refine ⟨x, J, Or.inr ?_⟩
    intro σ hσ
    have hσ' : σ⁻¹ ∈ Green4.extremalFamily x J := hJ ⟨σ, hσ, rfl⟩
    exact ⟨σ⁻¹, hσ', inv_inv σ⟩
