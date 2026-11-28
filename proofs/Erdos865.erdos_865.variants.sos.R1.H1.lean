import OMAReductions.R_Erdos865_erdos_865_variants_sos_R1

-- Step Erdos865.erdos_865.variants.sos.R1.H1: hypothesis H1 of reduction Erdos865.erdos_865.variants.sos.R1
-- Credit: @Raimo33

namespace RaimoE865

open Finset

lemma upper (N : ℕ) : ∀ A ⊆ Icc 1 N, A.card ≥ N / 2 + 2 →
    ∃ S ⊆ A, S.card = 2 ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + y ∈ A := by
  intro A hA hcard
  by_contra hno
  have hne : A.Nonempty := card_pos.mp (by omega)
  set M := A.max' hne with hMdef
  have hMA : M ∈ A := max'_mem _ _
  have hMr := mem_Icc.mp (hA hMA)
  set A' := A.erase M with hA'def
  have hA'sub : A' ⊆ Icc 1 (M - 1) := by
    intro x hx
    obtain ⟨hxM, hxA⟩ := mem_erase.mp hx
    have h1 := le_max' A x hxA
    have h2 := (mem_Icc.mp (hA hxA)).1
    rw [mem_Icc]
    omega
  set B := A'.image (fun x => M - x) with hBdef
  have hBsub : B ⊆ Icc 1 (M - 1) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    have := mem_Icc.mp (hA'sub hx)
    rw [mem_Icc]
    omega
  have hBcard : B.card = A'.card := by
    apply card_image_of_injOn
    intro x hx y hy h
    have h1 := mem_Icc.mp (hA'sub (Finset.mem_coe.mp hx))
    have h2 := mem_Icc.mp (hA'sub (Finset.mem_coe.mp hy))
    simp only at h
    omega
  have hinter : A' ∩ B ⊆ {M / 2} := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := mem_inter.mp hy
    obtain ⟨x, hx, hxy⟩ := mem_image.mp hy2
    have hxr := mem_Icc.mp (hA'sub hx)
    have hyr := mem_Icc.mp (hA'sub hy1)
    rw [mem_singleton]
    by_contra hne'
    have hxy' : x ≠ y := by omega
    apply hno
    refine ⟨{x, y}, ?_, card_pair hxy', ?_⟩
    · intro z hz
      rw [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact mem_of_mem_erase hx
      · exact mem_of_mem_erase hy1
    · intro a ha b hb hab
      rw [mem_insert, mem_singleton] at ha hb
      have hsum : x + y = M := by omega
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · rw [hsum]; exact hMA
      · rw [add_comm, hsum]; exact hMA
      · exact absurd rfl hab
  have h1 := card_union_add_card_inter A' B
  have h2 : (A' ∪ B).card ≤ M - 1 := by
    simpa using card_le_card (union_subset hA'sub hBsub)
  have h3 : (A' ∩ B).card ≤ 1 := by simpa using card_le_card hinter
  have h4 : A'.card = A.card - 1 := card_erase_of_mem hMA
  omega

lemma lower (N m : ℕ) (hm : ∀ A ⊆ Icc 1 N, A.card ≥ m →
    ∃ S ⊆ A, S.card = 2 ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + y ∈ A) : N - N / 2 + 1 ≤ m := by
  by_contra h
  rw [not_le] at h
  obtain ⟨S, hS, hS2, hsum⟩ := hm (Icc (N / 2 + 1) N)
    (by intro x hx; rw [mem_Icc] at hx ⊢; omega) (by rw [Nat.card_Icc]; omega)
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hS2
  have hx := mem_Icc.mp (hS (mem_insert_self x {y}))
  have hy := mem_Icc.mp (hS (by simp : y ∈ ({x, y} : Finset ℕ)))
  have := mem_Icc.mp (hsum x (by simp) y (by simp) hxy)
  omega

lemma bounds (N : ℕ) : N - N / 2 + 1 ≤ Erdos865.f N 2 ∧ Erdos865.f N 2 ≤ N / 2 + 2 := by
  have hmem : N / 2 + 2 ∈ {m | ∀ A ⊆ Icc 1 N, A.card ≥ m →
      ∃ S ⊆ A, S.card = 2 ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + y ∈ A} := upper N
  refine ⟨lower N _ (Nat.sInf_mem ⟨_, hmem⟩), Nat.sInf_le hmem⟩

end RaimoE865

open Filter Asymptotics in
theorem OMA.solution : OMA.R_Erdos865_erdos_865_variants_sos_R1.H1 := by
  unfold OMA.R_Erdos865_erdos_865_variants_sos_R1.H1
  have hsimp : (fun N : ℕ ↦ (1 / 2 : ℝ) * (1 + ∑ r ∈ Finset.Icc 1 (2 - 2), (1 / 4 : ℝ) ^ r) * N)
      = fun N : ℕ ↦ (1 / 2 : ℝ) * N := by
    funext N; simp
  rw [hsimp]
  unfold IsEquivalent
  have hO : (fun N : ℕ ↦ (Erdos865.f N 2 : ℝ) - (1 / 2 : ℝ) * N) =O[atTop] (fun _ ↦ (1 : ℝ)) := by
    refine IsBigO.of_bound 2 (Eventually.of_forall fun N => ?_)
    obtain ⟨h1, h2⟩ := RaimoE865.bounds N
    have e1 : 2 * (N / 2) ≤ N := Nat.mul_div_le N 2
    have e2 : N ≤ 2 * (N / 2) + 1 := by omega
    have e3 : N - N / 2 = N - N / 2 := rfl
    have r1 : ((N - N / 2 + 1 : ℕ) : ℝ) ≤ (Erdos865.f N 2 : ℝ) := by exact_mod_cast h1
    have r2 : (Erdos865.f N 2 : ℝ) ≤ ((N / 2 + 2 : ℕ) : ℝ) := by exact_mod_cast h2
    have r3 : (2 : ℝ) * ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast e1
    have r4 : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast e2
    have r5 : ((N - N / 2 : ℕ) : ℝ) = (N : ℝ) - ((N / 2 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (Nat.div_le_self N 2)]
    push_cast at r1 r2
    rw [r5] at r1
    rw [Real.norm_eq_abs, abs_le]
    simp only [norm_one, mul_one]
    constructor <;> linarith
  refine hO.trans_isLittleO ?_
  rw [isLittleO_const_left]
  right
  have : Tendsto (fun N : ℕ ↦ (1 / 2 : ℝ) * N) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  exact tendsto_norm_atTop_atTop.comp this
