import FormalConjectures.GreensOpenProblems.«32»

/-!
# A coset hole in a binary vector space

Tom Sanders' averaging argument, recorded by Ben Green in 100 Open Problems, Problem 32.
Credit: @carterleffen
-/
namespace OMA.Green32Proof

open Module

/-- Split the coordinates into two blocks and choose a sparse fibre over the first block.
A hyperplane in the second block contains the linear span of all occupied tails. -/
lemma hole_of_split {k m b : ℕ} (A : Finset (𝔽₂ (k + m)))
    (hcard : A.card ≤ 2 ^ k * b) (hm : b < m) :
    Green32.HasCosetHole A (2 ^ (m - 1)) := by
  classical
  let head := LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.castAdd m : Fin k → Fin (k + m))
  let tail := LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.natAdd k : Fin m → Fin (k + m))
  obtain ⟨y, _, hy⟩ := Finset.exists_card_fiber_le_of_card_le_mul
    (f := head) (s := A) (t := Finset.univ) Finset.univ_nonempty (n := b) (by
      simpa [𝔽₂, 𝔽, ZMod.card] using hcard)
  let occupied := (A.filter fun x ↦ head x = y).image tail
  let S := Submodule.span (ZMod 2) (occupied : Set (𝔽₂ m))
  have hsmall : finrank (ZMod 2) S < m :=
    (finrank_span_finset_le_card occupied).trans_lt ((Finset.card_image_le.trans hy).trans_lt hm)
  have hproper : S < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro h
    have heq : finrank (ZMod 2) S = m := by
      rw [h, finrank_top]
      simp [𝔽₂, 𝔽]
    exact (Nat.ne_of_lt hsmall) heq
  obtain ⟨f, hf, hker⟩ := S.exists_le_ker_of_lt_top hproper
  obtain ⟨z, hz⟩ := DFunLike.ne_iff.mp hf
  let projection := head.prod (f.comp tail)
  let v : 𝔽₂ (k + m) := Fin.append y z
  have hv : projection v = (y, f z) := by
    have hhead : head v = y := by ext i; simp [head, v]
    have htail : tail v = z := by ext i; simp [tail, v]
    exact Prod.ext hhead (congrArg f htail)
  refine ⟨projection.ker, v, ?_, ?_⟩
  · rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    apply Nat.pow_le_pow_right (by decide)
    have hnull : finrank (ZMod 2) projection.range + finrank (ZMod 2) projection.ker = k + m :=
      projection.finrank_range_add_finrank_ker.trans (by simp)
    have hr : finrank (ZMod 2) projection.range ≤ k + 1 :=
      (Submodule.finrank_le projection.range).trans_eq (by simp [finrank_prod])
    change m - 1 ≤ finrank (ZMod 2) projection.ker
    omega
  · intro w hw
    have heq : projection (v + w.val) = (y, f z) := by
      rw [map_add, show projection w.val = 0 from w.property, add_zero, hv]
    have hhead : head (v + w.val) = y := congrArg Prod.fst heq
    have htail : tail (v + w.val) ∈ S := Submodule.subset_span <|
      Finset.mem_image.mpr ⟨_, Finset.mem_filter.mpr ⟨hw, hhead⟩, rfl⟩
    exact hz ((congrArg Prod.snd heq).symm.trans (hker htail))

end OMA.Green32Proof

theorem OMA.solution : type_of% @Green32.green_32.variants.finite_field := by
  classical
  filter_upwards [Filter.eventually_ge_atTop 2048] with n hn
  -- With this split some fibre has at most 1024 points, fewer than its dimension.
  -- Losing one more dimension still leaves at least 100 times the square root.
  let k := n / 2 - 9
  let m := n - k
  have hn' : n = k + m := by dsimp [k, m]; omega
  have hdim : 1024 < m := by dsimp [m, k]; omega
  have hexp : n ≤ 2 * (k + 10) := by dsimp [k]; omega
  have hroom : k + 17 ≤ m - 1 := by dsimp [m, k]; omega
  have hsqrt : Real.sqrt (2 ^ n : ℝ) ≤ 2 ^ (k + 10) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  intro A hA
  have hsize : A.card ≤ 2 ^ k * 1024 := by
    rw [hA]
    apply Nat.floor_le_of_le
    norm_num [pow_add] at hsqrt ⊢
    exact hsqrt
  have htarget : ⌊100 * Real.sqrt (2 ^ n : ℝ)⌋₊ ≤ 2 ^ (m - 1) := by
    apply Nat.floor_le_of_le
    push_cast
    calc
      100 * Real.sqrt (2 ^ n : ℝ) ≤ 100 * 2 ^ (k + 10) := by gcongr
      _ ≤ 2 ^ (k + 17) := by
        calc
          _ ≤ 2 ^ (k + 10) * (2 : ℝ) ^ 7 := by rw [mul_comm]; gcongr; norm_num
          _ = _ := (pow_add (2 : ℝ) (k + 10) 7).symm
      _ ≤ 2 ^ (m - 1) := pow_le_pow_right₀ (by norm_num) hroom
  obtain ⟨W, v, hW, hv⟩ : Green32.HasCosetHole A (2 ^ (m - 1)) := by
    revert A
    generalize k = k' at hn' ⊢
    generalize m = m' at hn' hdim ⊢
    subst n
    exact fun A _ hsize ↦ OMA.Green32Proof.hole_of_split A hsize hdim
  exact ⟨W, v, htarget.trans hW, hv⟩
