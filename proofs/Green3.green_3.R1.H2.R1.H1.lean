import OMAReductions.R_Green3_green_3_R1_H2_R1

/-! The two disjoint integer packings associated to the largest occupied cell.
One uses blocks of the original grid width and the other uses a scaled copy.
Lean proof by @Deldor14. -/

open Finset

private lemma block_step {i j t r : ℕ} (hr : r<t) (hij : i<j) : i*t+r < j*t := calc
  _ < (i+1)*t := by nlinarith
  _ ≤ j*t := Nat.mul_le_mul_right _ hij

theorem OMA.solution : OMA.R_Green3_green_3_R1_H2_R1.H1 := by
  intro N m M S hpM hMN hM hrange hno
  let B (t : ℕ) := (S ×ˢ range t).image (fun x => x.1*t+x.2)
  have hcard (t : ℕ) : (B t).card = S.card*t := by
    dsimp [B]
    rw [card_image_of_injOn]
    · simp
    · intro ⟨i,r⟩ hi ⟨j,u⟩ hj he
      have hr := mem_range.mp (mem_product.mp hi).2
      have hu := mem_range.mp (mem_product.mp hj).2
      change i*t+r = j*t+u at he
      rcases lt_trichotomy i j with hij | rfl | hji
      · have hh := block_step hr hij
        omega
      · have hru : r=u := by omega
        simp [hru]
      · have hh := block_step hu hji
        omega
  have hb {t z : ℕ} (hz : z ∈ B t) : ∃ i ∈ S, i*t ≤ z ∧ z < (i+1)*t := by
    obtain ⟨⟨i,r⟩,hi,rfl⟩ := mem_image.mp hz
    have hr := mem_range.mp (mem_product.mp hi).2
    exact ⟨i,(mem_product.mp hi).1,Nat.le_add_right ..,block_step hr (Nat.lt_succ_self i)⟩
  have hd : Disjoint (B N) (B M) := by
    apply disjoint_left.mpr
    intro z hzN hzM
    obtain ⟨l,hl,hl₁,hl₂⟩ := hb hzN
    obtain ⟨j,hj,hj₁,hj₂⟩ := hb hzM
    have hle : (M-1)*j ≤ j*M := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left _ (Nat.sub_le ..)
    apply hno (M-1) hM j hj l hl
    refine ⟨(hle.trans hj₁).trans_lt hl₂,?_⟩
    rw [Nat.sub_add_cancel hpM,Nat.mul_comm M (j+1)]
    exact hl₁.trans_lt hj₂
  have hsub : B N ∪ B M ⊆ Ico (m*M) (M*N) := by
    intro z hz
    rcases mem_union.mp hz with hz | hz
    · obtain ⟨i,hi,hlo,hhi⟩ := hb hz
      obtain ⟨hl,hh⟩ := hrange i hi
      exact mem_Ico.mpr ⟨(Nat.mul_le_mul hl hMN).trans hlo,
        hhi.trans_le (Nat.mul_le_mul_right _ hh)⟩
    · obtain ⟨i,hi,hlo,hhi⟩ := hb hz
      obtain ⟨hl,hh⟩ := hrange i hi
      exact mem_Ico.mpr ⟨(Nat.mul_le_mul_right _ hl).trans hlo,
        hhi.trans_le (Nat.mul_le_mul hh hMN)⟩
  have hcount := card_le_card hsub
  rw [card_union_of_disjoint hd,hcard,hcard,Nat.card_Ico] at hcount
  calc
    (N+M)*S.card = S.card*N+S.card*M := by ring
    _ ≤ M*N-m*M := hcount
    _ = M*(N-m) := by rw [Nat.mul_sub, Nat.mul_comm m M]
