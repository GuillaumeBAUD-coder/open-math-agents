import OMAReductions.R_Erdos667_erdos_667_variants_ramsey_bounds_R1

/-! Apply the off-diagonal Ramsey recurrence with singleton base cases. -/

open Combinatorics.Diagonal Finset SimpleGraph Filter Real

namespace OMA.RamseyLower

lemma binomial (s t : ℕ) : HasRamseyProperty ((s+t).choose s) (s+1) (t+1) := by
  induction s generalizing t with
  | zero => rw [Nat.choose_zero_right]; exact hasRamseyProperty_one_left (t+1)
  | succ s ih =>
    induction t with
    | zero => rw [Nat.add_zero, Nat.choose_self]; exact hasRamseyProperty_one_right (s+2)
    | succ t iht =>
      have h : HasRamseyProperty (((s+(t+1)).choose s) + ((s+1+t).choose (s+1))) (s+2) (t+2) :=
        HasRamseyProperty.step (ih (t+1)) iht (Nat.choose_pos (by omega))
      rw [show s+1+(t+1) = (s+(t+1))+1 by omega, Nat.choose_succ_succ]
      rw [show s+1+t = s+(t+1) by omega] at h
      intro m c V hV
      exact h c V hV

lemma clique {s t n : ℕ} (h : (s+t).choose s ≤ n) (G : SimpleGraph (Fin n))
    (hd : Erdos667.LocallyDense (s+1) 1 G) : ¬ G.CliqueFree (t+1) := by
  classical
  let c (e : Finset (Fin n)) := decide (G.IsClique (e : Set (Fin n)))
  have cp (x y : Fin n) (hne : x ≠ y) : c {x,y} = true ↔ G.Adj x y := by
    simp [c, hne]
  rcases binomial s t c univ (by simpa using h) with ⟨S,_,hS,hcol⟩ | ⟨S,_,hS,hcol⟩
  · have hempty : G.induce (S : Set (Fin n)) = ⊥ := by
      apply le_bot_iff.mp
      intro x y hxy
      have ha : G.Adj x.val y.val := hxy
      have hh := (cp _ _ ha.ne).mpr ha
      have hfalse := hcol {x.val,y.val} (Finset.insert_subset x.property (Finset.singleton_subset_iff.mpr y.property)) (by simp [ha.ne])
      simp [hh] at hfalse
    have hb := hd S hS
    simp [hempty] at hb
  · apply IsNClique.not_cliqueFree (s := S)
    refine ⟨?_,hS⟩
    intro x hx y hy hne
    exact (cp _ _ hne).mp (hcol {x,y} (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy)) (by simp [hne]))

end OMA.RamseyLower

theorem OMA.solution : OMA.R_Erdos667_erdos_667_variants_ramsey_bounds_R1.H1 := by
  intro p hp a ha
  obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  let b := 1 / (s : ℝ)
  have hs : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
  have hb : 0 < b := by dsimp [b]; positivity
  have hba : a < b := by simpa [b] using ha
  have tend (d : ℝ) (hd : 0 < d) : Tendsto (fun n : ℕ => (n : ℝ)^d) atTop atTop :=
    (tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop
  filter_upwards [(tend b hb).eventually_ge_atTop 2,
    (tend (b-a) (by linarith)).eventually_ge_atTop 2, eventually_ge_atTop 1] with n hn hd hn1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  let t := ⌊(n : ℝ)^b / 2⌋₊
  have ht : (t : ℝ) ≤ (n : ℝ)^b / 2 := Nat.floor_le (by positivity)
  have ht' : (n : ℝ)^b / 2 < (t : ℝ)+1 := Nat.lt_floor_add_one _
  have hmul : (n : ℝ)^a * (n : ℝ)^(b-a) = (n : ℝ)^b := by
    rw [← Real.rpow_add hnpos]; congr 1; ring
  have hlow : (n : ℝ)^a ≤ (t+1 : ℕ) := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hd (Real.rpow_nonneg hnpos.le a)]
  have hu : ((t+1 : ℕ) : ℝ) ≤ (n : ℝ)^b := by push_cast; linarith
  have hun : t+1 ≤ n := by
    exact_mod_cast hu.trans ((Real.rpow_le_rpow_of_exponent_le hnreal (by
      dsimp [b]; exact (div_le_one (by linarith)).mpr hs)).trans_eq (Real.rpow_one _))
  refine ⟨t+1,hun,hlow,fun G hg => OMA.RamseyLower.clique ?_ G hg⟩
  have he : ((n : ℝ)^b) ^ (s : ℕ) = n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
    have : b * s = 1 := by dsimp [b]; field_simp
    rw [this, Real.rpow_one]
  have hpow : (t+1)^s ≤ n := by
    exact_mod_cast (pow_le_pow_left₀ (by positivity) hu s).trans_eq he
  exact (Nat.add_comm s t ▸ Nat.choose_add_le_add_one_pow t s).trans hpow
