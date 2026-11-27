import OMAReductions.R_Green40_green_40_upper_bound_f_two_R1

/-! A radius-two binary code from the 50-column seed of Stephen Wu
(arXiv:2608.27494, matrix H_r10_n50.txt, wustep/maths at 736a38f).
Give each seed column and the zero column a distinct slope over a larger
field, and append the nonzero vertical vectors. -/

open Green40 Finset
open scoped Pointwise

private def bits (i : Fin 51) : BitVec 10 :=
  #[0, 1, 2, 4, 15, 16, 32, 65, 86, 128, 173, 183, 202, 212, 247, 256, 297, 320, 329, 341, 366, 373, 381, 391, 403, 438, 460, 479, 491, 502, 559, 576, 608, 653, 734, 742, 754, 771, 777, 789, 821, 846, 855, 869, 881, 893, 897, 927, 981, 1003, 1004][i.val]!

private def decode (b : BitVec 10) : 𝔽₂ 10 :=
  fun i => if b.getLsbD i.val then 1 else 0

private lemma decode_add (a b : BitVec 10) :
    decode (a ^^^ b) = decode a + decode b := by
  funext i
  simp only [decode, BitVec.getLsbD_xor, Pi.add_apply]
  cases a.getLsbD i.val <;> cases b.getLsbD i.val <;> decide

private lemma decode_onto : Function.Surjective decode := by
  have inj : Function.Injective decode := by
    intro a b h
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have he := congrFun h ⟨j, hj⟩
    change (if a.getLsbD j then (1 : ZMod 2) else 0) =
      (if b.getLsbD j then 1 else 0) at he
    cases ha : a.getLsbD j <;> cases hb : b.getLsbD j <;> simp_all
  exact ((Fintype.bijective_iff_injective_and_card _).2 ⟨inj, by
    let e : BitVec 10 ≃ Fin (2 ^ 10) :=
      ⟨BitVec.toFin, @BitVec.ofFin 10, BitVec.ofFin_toFin, BitVec.toFin_ofFin⟩
    simpa [𝔽₂, 𝔽, ZMod.card] using Fintype.card_congr e⟩).2

private def seed (i : Fin 51) := decode (bits i)

-- Bit t in the mask records whether t is the XOR of two seed columns.
private def unionMask {α : Type*} (f : α → ℕ) : List α → ℕ
  | [] => 0
  | a :: l => f a ||| unionMask f l

private lemma mask_spec {α : Type*} (f : α → ℕ) (l : List α) (t : ℕ) :
    (unionMask f l).testBit t = true ↔ ∃ a ∈ l, (f a).testBit t = true := by
  induction l with
  | nil => simp [unionMask]
  | cons a l ih => simp [unionMask, ih]

private def rowMask (i : Fin 51) : ℕ :=
  unionMask (fun j => 2 ^ (bits i ^^^ bits j).toNat) (List.finRange 51)

set_option maxRecDepth 10000 in
private lemma mask_complete : unionMask rowMask (List.finRange 51) = 2 ^ 1024 - 1 := by
  decide +kernel

private lemma seed_cover (a : 𝔽₂ 10) (ha : a ≠ 0) :
    ∃ i j : Fin 51, i ≠ j ∧ seed i + seed j = a := by
  obtain ⟨x, rfl⟩ := decode_onto a
  have hmem : (unionMask rowMask (List.finRange 51)).testBit x.toNat = true := by
    rw [mask_complete, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true x.isLt
  obtain ⟨i, _, hi⟩ := (mask_spec ..).mp hmem
  obtain ⟨j, _, hj⟩ := (mask_spec ..).mp (show (rowMask i).testBit x.toNat = true from hi)
  rw [Nat.testBit_two_pow, decide_eq_true_eq] at hj
  have h : bits i ^^^ bits j = x := BitVec.eq_of_toNat_eq hj
  refine ⟨i, j, ?_, (decode_add _ _).symm.trans (congrArg decode h)⟩
  intro e
  rw [e, BitVec.xor_self] at h
  exact ha (by rw [← h]; funext i; simp [decode])

private def columns {K : Type*} [Field K] (slope : Fin 51 ↪ K) :
    (Fin 51 × K) ⊕ Kˣ → 𝔽₂ 10 × K × K
  | .inl (i, t) => (seed i, t, slope i * t)
  | .inr t => (0, 0, t.val)

private theorem columns_cover {K : Type*} [Field K] (slope : Fin 51 ↪ K)
    (s : 𝔽₂ 10 × K × K) :
    ∃ i j, columns slope i + columns slope j = s := by
  obtain ⟨a, x, y⟩ := s
  have h0 : seed 0 = 0 := by decide
  by_cases ha : a = 0
  · subst a
    by_cases hz : y - slope 0 * x = 0
    · refine ⟨.inl (0, x), .inl (0, 0), ?_⟩
      simp [columns, h0, sub_eq_zero.mp hz]
    · refine ⟨.inl (0, x), .inr (Units.mk0 _ hz), ?_⟩
      simp [columns, h0]
  · obtain ⟨i, j, hij, hsum⟩ := seed_cover a ha
    let u := (y - slope j * x) / (slope i - slope j)
    refine ⟨.inl (i, u), .inl (j, x - u), ?_⟩
    refine Prod.ext hsum (Prod.ext (by change u + (x - u) = x; ring) ?_)
    change slope i * u + slope j * (x - u) = y
    have hne : slope i - slope j ≠ 0 := sub_ne_zero.mpr (slope.injective.ne hij)
    dsimp [u]
    field_simp
    ring

private theorem code_of_columns {n : ℕ} {S : Type*} [AddCommGroup S] [Module (ZMod 2) S]
    [Finite S] (col : Fin n → S) (hcol : ∀ s, ∃ i j, col i + col j = s) :
    ∃ V : Submodule (ZMod 2) (𝔽₂ n), IsCoveringSubspace n 2 V ∧
      Nat.card V = 2 ^ (n - Module.finrank (ZMod 2) S) := by
  classical
  let L : 𝔽₂ n →ₗ[ZMod 2] S :=
    { toFun := fun x => ∑ i, x i • col i
      map_add' := by intro x y; simp [add_smul, sum_add_distrib]
      map_smul' := by intro c x; simp [Finset.smul_sum, mul_smul] }
  let e (i : Fin n) : 𝔽₂ n := Pi.single i 1
  have hL (i : Fin n) : L (e i) = col i := by
    change (∑ j, (Pi.single i 1 : 𝔽₂ n) j • col j) = col i
    rw [sum_eq_single i] <;> simp_all [Pi.single_eq_of_ne]
  have small (i j : Fin n) : e i + e j ∈ hammingBall n 2 := by
    change (univ.filter (fun k => (e i + e j) k ≠ 0)).card ≤ 2
    calc _ ≤ ({i, j} : Finset _).card := by
           apply card_le_card
           intro k hk
           by_contra h
           simp only [mem_insert, mem_singleton, not_or] at h
           exact (mem_filter.mp hk).2 (by simp [e, Pi.single_eq_of_ne, h.1, h.2])
         _ ≤ 2 := by simpa using card_insert_le i {j}
  have rep (s : S) : ∃ z ∈ hammingBall n 2, L z = s := by
    obtain ⟨i, j, hij⟩ := hcol s
    exact ⟨e i + e j, small i j, by rw [map_add, hL, hL, hij]⟩
  refine ⟨L.ker, ?_, ?_⟩
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨z, hz, h⟩ := rep (L x)
    exact ⟨x - z, LinearMap.mem_ker.mpr (by rw [map_sub, h, sub_self]), z, hz, sub_add_cancel x z⟩
  · have surj : Function.Surjective L := fun s => by
      obtain ⟨z, _, h⟩ := rep s
      exact ⟨z, h⟩
    have hdim := L.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr surj, finrank_top, Module.finrank_fin_fun] at hdim
    have hk : Module.finrank (ZMod 2) L.ker = n - Module.finrank (ZMod 2) S := by omega
    have := Fintype.ofFinite L.ker
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hk]

theorem OMA.solution : OMA.R_Green40_green_40_upper_bound_f_two_R1.H1 := by
  classical
  intro k hk
  let K := GaloisField 2 (k - 1)
  let _ := Fintype.ofFinite K
  have hp : k - 1 ≠ 0 := by omega
  have hK : Fintype.card K = 2 ^ (k - 1) := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card 2 _ hp
  have hpow : 2 ^ k = 2 ^ (k - 1) * 2 := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
  have hlarge : 51 ≤ Fintype.card K := by
    rw [hK]
    calc 51 ≤ 2 ^ 9 := by decide
         _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  let slope : Fin 51 ↪ K := (Fin.castLEEmb hlarge).trans (Fintype.equivFin K).symm.toEmbedding
  let n := 26 * 2 ^ k - 1
  have hu : Fintype.card Kˣ = 2 ^ (k - 1) - 1 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units, Nat.card_eq_fintype_card, hK]
  have hc : Fintype.card (Fin n) = Fintype.card ((Fin 51 × K) ⊕ Kˣ) := by
    simp only [Fintype.card_fin, Fintype.card_sum, Fintype.card_prod, hu, hK, n]
    have : 0 < 2 ^ (k - 1) := pow_pos (by decide) _
    omega
  let f := Fintype.equivOfCardEq hc
  have hcov (s : 𝔽₂ 10 × K × K) : ∃ i j, columns slope (f i) + columns slope (f j) = s := by
    obtain ⟨u, v, huv⟩ := columns_cover slope s
    exact ⟨f.symm u, f.symm v, by simpa using huv⟩
  obtain ⟨V, hV, hcV⟩ := code_of_columns (fun i => columns slope (f i)) hcov
  refine ⟨V, hV, ?_⟩
  have hdim : Module.finrank (ZMod 2) K = k - 1 := GaloisField.finrank 2 hp
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_fin_fun, hdim] at hcV
  convert hcV using 2
  omega

