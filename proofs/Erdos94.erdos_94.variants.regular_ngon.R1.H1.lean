import OMAReductions.R_Erdos94_erdos_94_variants_regular_ngon_R1

-- Step Erdos94.erdos_94.variants.regular_ngon.R1.H1: the regular n-gon attains B(n).
-- Explicit computation: distanceSet (regularNGon n) = (Icc 1 (n/2)).image (d n) with
-- d n j = 2 sin (pi j / n), each distance d n j has multiplicity n (n/2 for the diameter),
-- so the sum of squared multiplicities equals B(n) exactly.

open Erdos94 EuclideanGeometry

namespace Erdos94H1

noncomputable def v (n k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[Real.cos (2 * Real.pi * k / n), Real.sin (2 * Real.pi * k / n)]

theorem chord_sq (n k l : ℕ) :
    dist (v n k) (v n l) ^ 2 = 4 * Real.sin (Real.pi * ((k : ℝ) - l) / n) ^ 2 := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, v]
  simp
  have h1 : Real.cos (2 * Real.pi * k / n) - Real.cos (2 * Real.pi * l / n) =
      -2 * Real.sin (Real.pi * (k + l) / n) * Real.sin (Real.pi * (k - l) / n) := by
    rw [Real.cos_sub_cos]; ring_nf
  have h2 : Real.sin (2 * Real.pi * k / n) - Real.sin (2 * Real.pi * l / n) =
      2 * Real.cos (Real.pi * (k + l) / n) * Real.sin (Real.pi * (k - l) / n) := by
    rw [Real.sin_sub_sin]; ring_nf
  rw [h1, h2]
  ring_nf
  have h3 := Real.sin_sq_add_cos_sq (Real.pi * (k : ℝ) * (n : ℝ)⁻¹ + Real.pi * (l : ℝ) * (n : ℝ)⁻¹)
  nlinarith [h3]

theorem chord (n k l : ℕ) (hn : 0 < n) :
    dist (v n k) (v n l) = 2 * |Real.sin (Real.pi * ((k : ℝ) - l) / n)| := by
  rw [← Real.sqrt_sq dist_nonneg, chord_sq,
    show (4:ℝ) * Real.sin (Real.pi * ((k : ℝ) - l) / n) ^ 2 =
      (2 * Real.sin (Real.pi * ((k : ℝ) - l) / n)) ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]

theorem v_inj (n : ℕ) (hn : 0 < n) : Set.InjOn (v n) (Finset.range n : Set ℕ) := by
  intro k hk l hl hv
  rw [Finset.mem_coe, Finset.mem_range] at hk hl
  have hcos : Real.cos (2 * Real.pi * k / n) = Real.cos (2 * Real.pi * l / n) := by
    have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) hv; simpa [v] using this
  have hsin : Real.sin (2 * Real.pi * k / n) = Real.sin (2 * Real.pi * l / n) := by
    have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) hv; simpa [v] using this
  have hexp : Complex.exp ((2 * Real.pi * k / n : ℝ) * Complex.I) =
      Complex.exp ((2 * Real.pi * l / n : ℝ) * Complex.I) := by
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [hcos, hsin]
  obtain ⟨m, hm⟩ := (Complex.exp_eq_exp_iff_exists_int).mp hexp
  have him : (2 * Real.pi * (k : ℝ) / n : ℝ) = (2 * Real.pi * (l : ℝ) / n : ℝ) + m * (2 * Real.pi) := by
    have h := congrArg Complex.im hm
    simpa [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
      Complex.ofReal_im, Complex.ofReal_re] using h
  have hkn : (k : ℝ) = (l : ℝ) + m * n := by
    have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
    field_simp at him
    linarith
  have hkR : (k : ℝ) < n := by exact_mod_cast hk
  have hlR : (l : ℝ) < n := by exact_mod_cast hl
  have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast Nat.zero_le k
  have hnR : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
  rcases lt_trichotomy (m : ℝ) 0 with hm | hm | hm
  · have hm1 : (m : ℝ) ≤ -1 := by
      have hmz : (m : ℤ) < 0 := by exact_mod_cast hm
      have h1 : (m : ℤ) ≤ -1 := by omega
      exact_mod_cast h1
    nlinarith
  · have hm0 : m = 0 := by exact_mod_cast hm
    rw [hm0] at hkn
    simp at hkn
    exact_mod_cast hkn
  · have hm1 : (1 : ℝ) ≤ m := by
      have hmz : (0 : ℤ) < m := by exact_mod_cast hm
      have h1 : (1 : ℤ) ≤ m := by omega
      exact_mod_cast h1
    nlinarith

theorem regularNGon_eq (n : ℕ) : regularNGon n = (Finset.range n).image (v n) := rfl

theorem regularNGon_card (n : ℕ) (hn : 0 < n) : (regularNGon n).card = n := by
  rw [regularNGon_eq, Finset.card_image_of_injOn (v_inj n hn), Finset.card_range]

-- distance function on indices
noncomputable def d (n j : ℕ) : ℝ := 2 * Real.sin (Real.pi * j / n)
def md (k l : ℕ) : ℕ := (k - l) + (l - k)

theorem sin_abs_eq (n k l : ℕ) (hk : k < n) (hl : l < n) (hn : 0 < n) :
    |Real.sin (Real.pi * ((k : ℝ) - l) / n)| = Real.sin (Real.pi * (md k l : ℝ) / n) := by
  rcases le_total k l with h | h
  · have hmd : (md k l : ℝ) = (l : ℝ) - k := by
      have h1 : ((k - l : ℕ) : ℝ) = 0 := by exact_mod_cast Nat.sub_eq_zero_iff_le.mpr h
      have h2 : ((l - k : ℕ) : ℝ) = (l : ℝ) - k := Nat.cast_sub h
      unfold md
      rw [Nat.cast_add, h1, h2]
      ring
    have hsub : ((k : ℝ) - l) = -((l : ℝ) - k) := by ring
    have hsin : Real.sin (Real.pi * ((k : ℝ) - l) / n) =
        -Real.sin (Real.pi * ((l : ℝ) - k) / n) := by
      rw [hsub, show Real.pi * (-(↑l - ↑k)) / ↑n = -(Real.pi * (↑l - ↑k) / ↑n) by ring, Real.sin_neg]
    rw [hsin, abs_neg, hmd]
    have hpos : (0:ℝ) ≤ Real.pi * ((l : ℝ) - k) / n := by
      apply div_nonneg _ (by exact_mod_cast hn.le)
      exact mul_nonneg Real.pi_pos.le (by linarith)
    rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hpos ?_)]
    have hln : (l : ℝ) < n := by exact_mod_cast hl
    have hle : Real.pi * ((l : ℝ) - k) / n ≤ Real.pi := by
      rw [div_le_iff₀ (by exact_mod_cast hn)]
      nlinarith [Real.pi_pos]
    exact hle
  · have hmd : (md k l : ℝ) = (k : ℝ) - l := by
      have h1 : ((l - k : ℕ) : ℝ) = 0 := by exact_mod_cast Nat.sub_eq_zero_iff_le.mpr h
      have h2 : ((k - l : ℕ) : ℝ) = (k : ℝ) - l := Nat.cast_sub h
      unfold md
      rw [Nat.cast_add, h1, h2]
      ring
    rw [hmd]
    have hpos : (0:ℝ) ≤ Real.pi * ((k : ℝ) - l) / n := by
      apply div_nonneg _ (by exact_mod_cast hn.le)
      exact mul_nonneg Real.pi_pos.le (by linarith)
    rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hpos ?_)]
    have hkn : (k : ℝ) < n := by exact_mod_cast hk
    have hle : Real.pi * ((k : ℝ) - l) / n ≤ Real.pi := by
      rw [div_le_iff₀ (by exact_mod_cast hn)]
      nlinarith [Real.pi_pos]
    exact hle

theorem dist_v_eq (n k l : ℕ) (hk : k < n) (hl : l < n) (hn : 0 < n) :
    dist (v n k) (v n l) = d n (md k l) := by
  rw [chord n k l hn, sin_abs_eq n k l hk hl hn]
  rfl

theorem offDiag_image {α β : Type} [DecidableEq β] (s : Finset α) (f : α → β)
    (hf : Set.InjOn f ↑s) :
    (s.image f).offDiag = (s.offDiag).image (fun p => (f p.1, f p.2)) := by
  ext ⟨x, y⟩
  simp only [Finset.mem_offDiag, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, hne⟩
    have hab : a ≠ b := fun h => hne (by rw [h])
    exact ⟨(a, b), ⟨ha, hb, hab⟩, rfl⟩
  · rintro ⟨p, hp, hpq⟩
    obtain ⟨a, b⟩ := p
    simp only [Finset.mem_offDiag] at hp
    obtain ⟨ha, hb, hab⟩ := hp
    have hx : f a = x := congrArg Prod.fst hpq
    have hy : f b = y := congrArg Prod.snd hpq
    refine ⟨⟨a, ha, hx⟩, ⟨b, hb, hy⟩, ?_⟩
    intro h
    exact hab (hf ha hb (by rw [hx, hy, h]))

theorem distanceSet_regularNGon (n : ℕ) (hn : 0 < n) :
    distanceSet (regularNGon n) =
      ((Finset.range n).offDiag).image (fun p => d n (md p.1 p.2)) := by
  rw [regularNGon_eq, distanceSet, offDiag_image _ (v n) (v_inj n hn), Finset.image_image]
  apply Finset.image_congr
  intro p hp
  have hp' := Finset.mem_coe.mp hp
  rw [Finset.mem_offDiag] at hp'
  show dist (v n p.1) (v n p.2) = d n (md p.1 p.2)
  rw [dist_v_eq n p.1 p.2 (Finset.mem_range.mp hp'.1) (Finset.mem_range.mp hp'.2.1) hn]

theorem md_mem_Icc {n k l : ℕ} (hk : k < n) (hl : l < n) (hne : k ≠ l) :
    md k l ∈ Finset.Icc 1 (n - 1) := by
  unfold md
  rw [Finset.mem_Icc]
  have h1 : 1 ≤ (k - l) + (l - k) := by
    rcases le_total k l with h | h
    · rw [Nat.sub_eq_zero_iff_le.mpr h]; omega
    · rw [Nat.sub_eq_zero_iff_le.mpr h]; omega
  have h2 : (k - l) + (l - k) ≤ n - 1 := by
    rcases le_total k l with h | h
    · rw [Nat.sub_eq_zero_iff_le.mpr h]; omega
    · rw [Nat.sub_eq_zero_iff_le.mpr h]; omega
  exact ⟨h1, h2⟩

theorem md_image_offDiag (n : ℕ) (hn : 0 < n) :
    ((Finset.range n).offDiag).image (fun p => md p.1 p.2) = Finset.Icc 1 (n - 1) := by
  apply Finset.Subset.antisymm
  · intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨p, hp, rfl⟩ := hj
    rw [Finset.mem_offDiag] at hp
    exact md_mem_Icc (Finset.mem_range.mp hp.1) (Finset.mem_range.mp hp.2.1) hp.2.2
  · intro j hj
    rw [Finset.mem_Icc] at hj
    rw [Finset.mem_image]
    have hjn : j < n := by omega
    refine ⟨(j, 0), ?_, ?_⟩
    · rw [Finset.mem_offDiag, Finset.mem_range, Finset.mem_range]
      exact ⟨hjn, hn, by omega⟩
    · unfold md; omega

theorem sin_pi_div_inj (n j j' : ℕ) (hj : j ≤ n) (hj' : j' ≤ n) (hn : 0 < n) :
    Real.sin (Real.pi * j / n) = Real.sin (Real.pi * j' / n) ↔ j = j' ∨ j + j' = n := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hjR : (j:ℝ) ≤ n := by exact_mod_cast hj
  have hj'R : (j':ℝ) ≤ n := by exact_mod_cast hj'
  constructor
  · intro h
    rw [Real.sin_eq_sin_iff] at h
    obtain ⟨k, hk | hk⟩ := h
    · -- πj'/n = 2kπ + πj/n  →  j' - j = 2kn
      have h_eq : (j':ℝ) - j = 2 * (k:ℝ) * n := by
        field_simp at hk
        linarith [hk, Real.pi_pos]
      have hbound : -(n:ℝ) ≤ (j':ℝ) - j ∧ (j':ℝ) - j ≤ n := by
        constructor <;> linarith
      rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
      · have hk1 : (k:ℤ) ≤ -1 := by omega
        have hk1R : (k:ℝ) ≤ -1 := by exact_mod_cast hk1
        nlinarith
      · left
        have hk0R : (k:ℝ) = 0 := by exact_mod_cast hk0
        rw [hk0R] at h_eq
        simp at h_eq
        have : (j':ℝ) = j := by linarith
        exact_mod_cast this.symm
      · have hk1 : (1:ℤ) ≤ k := by omega
        have hk1R : (1:ℝ) ≤ k := by exact_mod_cast hk1
        nlinarith
    · -- πj'/n = (2k+1)π - πj/n  →  j' + j = (2k+1)n
      have h_eq : (j':ℝ) + j = (2 * (k:ℝ) + 1) * n := by
        field_simp at hk
        linarith [hk, Real.pi_pos]
      have hsum : (0:ℝ) ≤ (j:ℝ) + j' ∧ (j:ℝ) + j' ≤ 2 * n := by
        constructor <;> linarith
      rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
      · -- k < 0: 2k+1 ≤ -1, but (2k+1)n = j+j' ≥ 0 → contradiction unless... (2k+1)n ≥ 0 and n > 0 → 2k+1 ≥ 0, impossible for k < 0 (2k+1 ≤ -1)
        have hk1 : (k:ℤ) ≤ -1 := by omega
        have hk1R : (k:ℝ) ≤ -1 := by exact_mod_cast hk1
        nlinarith
      · -- k = 0: 2k+1 = 1 → j + j' = n
        right
        have hk0R : (k:ℝ) = 0 := by exact_mod_cast hk0
        rw [hk0R] at h_eq
        simp at h_eq
        have : (j:ℝ) + j' = n := by linarith
        exact_mod_cast this
      · -- k > 0: 2k+1 ≥ 3 → (2k+1)n ≥ 3n > 2n contradiction
        have hk1 : (1:ℤ) ≤ k := by omega
        have hk1R : (1:ℝ) ≤ k := by exact_mod_cast hk1
        nlinarith
  · rintro (h | h)
    · subst h
      rw [Real.sin_eq_sin_iff]
      exact ⟨0, Or.inl (by ring)⟩
    · have h' : (j':ℝ) = n - j := by exact_mod_cast (by omega : j' = n - j)
      rw [Real.sin_eq_sin_iff]
      refine ⟨0, Or.inr ?_⟩
      rw [h']
      field_simp
      ring

theorem d_eq_iff (n j j' : ℕ) (hj : j ≤ n) (hj' : j' ≤ n) (hn : 0 < n) :
    d n j = d n j' ↔ j = j' ∨ j + j' = n := by
  unfold d
  constructor
  · intro h
    exact (sin_pi_div_inj n j j' hj hj' hn).mp (by linarith)
  · intro h
    rw [(sin_pi_div_inj n j j' hj hj' hn).mpr h]

theorem d_injOn_half (n : ℕ) (hn : 0 < n) :
    Set.InjOn (d n) (Finset.Icc 1 (n / 2) : Set ℕ) := by
  intro j hj j' hj' h
  rw [Finset.mem_coe, Finset.mem_Icc] at hj hj'
  have hjle : j ≤ n := by omega
  have hj'le : j' ≤ n := by omega
  rcases (d_eq_iff n j j' hjle hj'le hn).mp h with h | h
  · exact h
  · have : j + j' ≤ n := by omega
    omega

theorem distanceSet_regularNGon' (n : ℕ) (hn : 0 < n) :
    distanceSet (regularNGon n) = (Finset.Icc 1 (n / 2)).image (d n) := by
  rw [distanceSet_regularNGon n hn]
  ext u
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [Finset.mem_offDiag] at hp
    have hmd := md_mem_Icc (Finset.mem_range.mp hp.1) (Finset.mem_range.mp hp.2.1) hp.2.2
    rw [Finset.mem_Icc] at hmd
    have hdiv : 2 * (n / 2) ≤ n := by simpa [mul_comm] using Nat.div_mul_le_self n 2
    by_cases h : md p.1 p.2 ≤ n / 2
    · exact ⟨md p.1 p.2, Finset.mem_Icc.mpr ⟨hmd.1, h⟩, rfl⟩
    · refine ⟨n - md p.1 p.2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      rw [d_eq_iff n (n - md p.1 p.2) (md p.1 p.2) (by omega) (by omega) hn]
      right; omega
  · rintro ⟨j, hj, rfl⟩
    rw [Finset.mem_Icc] at hj
    have hjn : j < n := by omega
    refine ⟨(j, 0), ?_, ?_⟩
    · rw [Finset.mem_offDiag, Finset.mem_range, Finset.mem_range]
      exact ⟨hjn, hn, by omega⟩
    · unfold md; congr 1; omega

def Am (n m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range n).offDiag.filter (fun p => md p.1 p.2 = m)

theorem card_Am (n m : ℕ) (hn : 0 < n) (hm : m ∈ Finset.Icc 1 (n - 1)) :
    (Am n m).card = 2 * (n - m) := by
  rw [Finset.mem_Icc] at hm
  have hinj1 : Set.InjOn (fun l : ℕ => (l + m, l)) (Finset.range (n - m) : Set ℕ) := by
    intro a _ b _ h; exact congrArg Prod.snd h
  have hinj2 : Set.InjOn (fun k : ℕ => (k, k + m)) (Finset.range (n - m) : Set ℕ) := by
    intro a _ b _ h; exact congrArg Prod.fst h
  have hsplit : Am n m = ((Finset.range (n - m)).image (fun l => (l + m, l))) ∪
      ((Finset.range (n - m)).image (fun k => (k, k + m))) := by
    ext ⟨k, l⟩
    simp only [Am, Finset.mem_filter, Finset.mem_offDiag, Finset.mem_image, Finset.mem_range, Finset.mem_union]
    constructor
    · rintro ⟨⟨hk, hl, hne⟩, hmd⟩
      unfold md at hmd
      rcases le_total k l with h | h
      · right
        refine ⟨k, by omega, ?_⟩
        have hkl : l = k + m := by omega
        exact Prod.ext rfl hkl.symm
      · left
        refine ⟨l, by omega, ?_⟩
        have hkl : k = l + m := by omega
        exact Prod.ext hkl.symm rfl
    · rintro (⟨a, ha, hp⟩ | ⟨a, ha, hp⟩)
      · have h1 : a + m = k := congrArg Prod.fst hp
        have h2 : a = l := congrArg Prod.snd hp
        subst h1; subst h2
        refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
        unfold md; omega
      · have h1 : a = k := congrArg Prod.fst hp
        have h2 : a + m = l := congrArg Prod.snd hp
        subst h1; subst h2
        refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
        unfold md; omega
  have hdisj : Disjoint ((Finset.range (n - m)).image (fun l => (l + m, l)))
      ((Finset.range (n - m)).image (fun k => (k, k + m))) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb hab
    rw [Finset.mem_image] at ha hb
    obtain ⟨l, hl, rfl⟩ := ha
    obtain ⟨k, hk, rfl⟩ := hb
    have h1 : l + m = k := congrArg Prod.fst hab
    have h2 : l = k + m := congrArg Prod.snd hab
    omega
  rw [hsplit, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injOn hinj1, Finset.card_image_of_injOn hinj2,
    Finset.card_range]
  omega

noncomputable def fiberD (n j : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range n).offDiag.filter (fun p => d n (md p.1 p.2) = d n j)

theorem fiberD_eq (n j : ℕ) (hn : 0 < n) (hj : j ∈ Finset.Icc 1 (n - 1)) :
    fiberD n j = Am n j ∪ Am n (n - j) := by
  rw [Finset.mem_Icc] at hj
  ext p
  simp only [fiberD, Am, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hp, h⟩
    have hp' := Finset.mem_offDiag.mp hp
    have hmd := md_mem_Icc (Finset.mem_range.mp hp'.1) (Finset.mem_range.mp hp'.2.1) hp'.2.2
    rw [Finset.mem_Icc] at hmd
    rcases (d_eq_iff n (md p.1 p.2) j (by omega) (by omega) hn).mp h with h | h
    · exact Or.inl ⟨hp, h⟩
    · exact Or.inr ⟨hp, by omega⟩
  · rintro (⟨hp, h⟩ | ⟨hp, h⟩)
    · refine ⟨hp, ?_⟩
      have hp' := Finset.mem_offDiag.mp hp
      have hmd := md_mem_Icc (Finset.mem_range.mp hp'.1) (Finset.mem_range.mp hp'.2.1) hp'.2.2
      rw [Finset.mem_Icc] at hmd
      exact (d_eq_iff n (md p.1 p.2) j (by omega) (by omega) hn).mpr (Or.inl h)
    · refine ⟨hp, ?_⟩
      have hp' := Finset.mem_offDiag.mp hp
      have hmd := md_mem_Icc (Finset.mem_range.mp hp'.1) (Finset.mem_range.mp hp'.2.1) hp'.2.2
      rw [Finset.mem_Icc] at hmd
      exact (d_eq_iff n (md p.1 p.2) j (by omega) (by omega) hn).mpr (Or.inr (by omega))

theorem card_fiber_regularNGon (n j : ℕ) (hn : 0 < n) (hj : j ∈ Finset.Icc 1 (n - 1)) :
    ((regularNGon n).offDiag.filter (fun p => dist p.1 p.2 = d n j)).card = (fiberD n j).card := by
  rw [regularNGon_eq, offDiag_image _ (v n) (v_inj n hn), Finset.filter_image]
  have hinj : Set.InjOn (fun p : ℕ × ℕ => (v n p.1, v n p.2))
      ↑((Finset.range n).offDiag.filter (fun p => dist (v n p.1) (v n p.2) = d n j)) := by
    intro p hp q hq h
    rw [Finset.mem_coe, Finset.mem_filter] at hp hq
    obtain ⟨hp1, _⟩ := hp
    obtain ⟨hq1, _⟩ := hq
    rw [Finset.mem_offDiag] at hp1 hq1
    have h1 : v n p.1 = v n q.1 := congrArg Prod.fst h
    have h2 : v n p.2 = v n q.2 := congrArg Prod.snd h
    have e1 : p.1 = q.1 := v_inj n hn
      (Finset.mem_coe.mpr (Finset.mem_range.mpr (Finset.mem_range.mp hp1.1)))
      (Finset.mem_coe.mpr (Finset.mem_range.mpr (Finset.mem_range.mp hq1.1))) h1
    have e2 : p.2 = q.2 := v_inj n hn
      (Finset.mem_coe.mpr (Finset.mem_range.mpr (Finset.mem_range.mp hp1.2.1)))
      (Finset.mem_coe.mpr (Finset.mem_range.mpr (Finset.mem_range.mp hq1.2.1))) h2
    exact Prod.ext e1 e2
  rw [Finset.card_image_of_injOn hinj]
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter, fiberD]
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    have hp' := Finset.mem_offDiag.mp hp
    rw [← dist_v_eq n p.1 p.2 (Finset.mem_range.mp hp'.1) (Finset.mem_range.mp hp'.2.1) hn]
    exact h
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    have hp' := Finset.mem_offDiag.mp hp
    rw [dist_v_eq n p.1 p.2 (Finset.mem_range.mp hp'.1) (Finset.mem_range.mp hp'.2.1) hn]
    exact h

theorem mult_regularNGon (n j : ℕ) (hn : 0 < n) (hj : j ∈ Finset.Icc 1 (n / 2)) :
    distanceMultiplicity (regularNGon n) (d n j) = if 2 * j = n then n / 2 else n := by
  rw [Finset.mem_Icc] at hj
  have hj' : j ∈ Finset.Icc 1 (n - 1) := Finset.mem_Icc.mpr ⟨hj.1, by omega⟩
  have hj'' : n - j ∈ Finset.Icc 1 (n - 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  unfold distanceMultiplicity
  rw [card_fiber_regularNGon n j hn hj', fiberD_eq n j hn hj']
  by_cases h2 : 2 * j = n
  · rw [if_pos h2]
    have hnj : n - j = j := by omega
    rw [hnj, Finset.union_self, card_Am n j hn hj']
    omega
  · rw [if_neg h2]
    have hdisj : Disjoint (Am n j) (Am n (n - j)) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Am, Finset.mem_filter] at hp1 hp2
      rw [hp1.2] at hp2
      omega
    rw [Finset.card_union_of_disjoint hdisj, card_Am n j hn hj', card_Am n (n - j) hn hj'']
    have hnn : n - (n - j) = j := by omega
    rw [hnn]
    omega

theorem sum_sq_regularNGon (n : ℕ) (hn : 0 < n) :
    ∑ u ∈ distanceSet (regularNGon n), (distanceMultiplicity (regularNGon n) u : ℝ) ^ 2 =
      if n % 2 = 1 then (n:ℝ)^2 * ((n:ℝ)-1)/2 else (n:ℝ)^3/2 - 3*(n:ℝ)^2/4 := by
  rw [distanceSet_regularNGon' n hn, Finset.sum_image (d_injOn_half n hn)]
  have hsum : ∀ j ∈ Finset.Icc 1 (n / 2),
      ((distanceMultiplicity (regularNGon n) (d n j) : ℕ) : ℝ) ^ 2 =
        if 2 * j = n then (((n / 2 : ℕ) : ℝ)) ^ 2 else (n:ℝ) ^ 2 := by
    intro j hj
    rw [mult_regularNGon n j hn hj]
    split_ifs with h2
    · have hd : 2 ∣ n := ⟨j, by omega⟩
      push_cast [Nat.cast_div hd]
      rfl
    · push_cast
      rfl
  rw [Finset.sum_congr rfl hsum]
  have hdiv : 2 * (n / 2) ≤ n := by simpa [mul_comm] using Nat.div_mul_le_self n 2
  by_cases hodd : n % 2 = 1
  · rw [if_pos hodd]
    have h2 : ∀ j ∈ Finset.Icc 1 (n / 2), 2 * j ≠ n := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      omega
    have hconst : ∀ j ∈ Finset.Icc 1 (n / 2),
        (if 2 * j = n then (((n / 2 : ℕ) : ℝ)) ^ 2 else (n:ℝ) ^ 2) = (n:ℝ) ^ 2 := by
      intro j hj
      rw [if_neg (h2 j hj)]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel]
    simp only [nsmul_eq_mul]
    have hn1 : (n : ℝ) = 2 * (n / 2 : ℕ) + 1 := by
      exact_mod_cast (by have := Nat.div_add_mod n 2; omega : n = 2 * (n / 2) + 1)
    rw [hn1]
    ring
  · rw [if_neg hodd]
    have h2 : 2 * (n / 2) = n := by
      have := Nat.div_add_mod n 2
      omega
    have hmem : n / 2 ∈ Finset.Icc 1 (n / 2) := Finset.mem_Icc.mpr ⟨by omega, le_refl _⟩
    rw [← Finset.sum_erase_add _ _ hmem]
    have hrest : ∀ j ∈ (Finset.Icc 1 (n / 2)).erase (n / 2),
        (if 2 * j = n then (((n / 2 : ℕ) : ℝ)) ^ 2 else (n:ℝ) ^ 2) = (n:ℝ)^2 := by
      intro j hj
      rw [Finset.mem_erase] at hj
      rw [Finset.mem_Icc] at hj
      rw [if_neg (by omega)]
    rw [Finset.sum_congr rfl hrest, Finset.sum_const, Finset.card_erase_of_mem hmem,
      Nat.card_Icc, Nat.add_sub_cancel]
    simp only [nsmul_eq_mul]
    rw [if_pos h2]
    have hd : 2 ∣ n := ⟨n / 2, by omega⟩
    have hle : (1:ℕ) ≤ n / 2 := (Finset.mem_Icc.mp hmem).1
    have hsub : ((n / 2 - 1 : ℕ) : ℝ) = ((n / 2 : ℕ) : ℝ) - 1 := by
      rw [Nat.cast_sub hle]; norm_num
    rw [hsub]
    push_cast [Nat.cast_div hd]
    have hnR : (n:ℝ) = 2 * (n / 2 : ℕ) := by
      exact_mod_cast (by omega : n = 2 * (n / 2))
    rw [hnR]
    ring


end Erdos94H1

theorem OMA.solution : OMA.R_Erdos94_erdos_94_variants_regular_ngon_R1.H1 := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hempty : distanceSet (regularNGon 0) = ∅ := by simp [regularNGon, distanceSet]
    rw [hempty, Finset.sum_empty]
    norm_num
  · rw [Erdos94H1.sum_sq_regularNGon n hn]
