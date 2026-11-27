import OMAReductions.R_Erdos1191_erdos_1191_parts_i_R1

-- Credit: @kenanwienberg

/-!
# A finite counting estimate for Sidon sets

Distinct positive differences bound the sum of the squared block counts.
Cauchy–Schwarz on successive groups of blocks bounds the sum of the
squared normalized prefix counts at geometrically spaced scales.
-/

namespace FiniteSidon1191

open Finset

lemma sidon_ordered_pairs_le {S : Finset ℕ} {D : ℕ} (hSid : IsSidon (↑S : Set ℕ))
    (hD : 1 ≤ D) :
    ((S ×ˢ S).filter (fun p => p.1 < p.2 ∧ p.2 - p.1 < D)).card ≤ D - 1 := by
  let P := (S ×ˢ S).filter (fun p => p.1 < p.2 ∧ p.2 - p.1 < D)
  have hmaps : ∀ p ∈ P, p.2 - p.1 ∈ Finset.Icc 1 (D - 1) := by
    intro p hp
    simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
    omega
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.2 - p.1) (↑P : Set (ℕ × ℕ)) := by
    intro p₁ hp₁ p₂ hp₂ heq
    simp only [P, Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq] at hp₁ hp₂
    have h := Finset.IsSidon.eq_of_tsub hSid hp₁.1.2 hp₁.1.1 hp₂.1.2 hp₂.1.1 hp₁.2.1 hp₂.2.1 heq
    exact Prod.ext h.2 h.1
  calc
    P.card ≤ (Finset.Icc 1 (D - 1)).card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ = D - 1 := by simp

lemma card_mul_sub_one_eq_two_ordered {T : Finset ℕ} :
    T.card * (T.card - 1) = 2 * ((T ×ˢ T).filter (fun p => p.1 < p.2)).card := by
  let L := (T ×ˢ T).filter (fun p => p.1 < p.2)
  let U := (T ×ˢ T).filter (fun p => p.2 < p.1)
  have hdisj : Disjoint L U := by
    rw [Finset.disjoint_left]
    intro p hpL hpU
    simp only [L, U, Finset.mem_filter] at hpL hpU
    omega
  have hunion : T.offDiag = L ∪ U := by
    ext p
    simp only [Finset.mem_offDiag, Finset.mem_union, L, U, Finset.mem_filter, Finset.mem_product]
    grind
  have hswap : U.card = L.card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp
      simp only [U, L, Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
    · intro p₁ _ p₂ _ h
      exact Prod.ext (Prod.mk.inj h).2 (Prod.mk.inj h).1
    · intro p hp
      refine ⟨(p.2, p.1), ?_, rfl⟩
      simp only [U, L, Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
  have hoff : T.offDiag.card = T.card * T.card - T.card := Finset.offDiag_card T
  have hcard : T.offDiag.card = 2 * L.card := by
    rw [hunion, Finset.card_union_of_disjoint hdisj, hswap]
    ring
  change T.card * (T.card - 1) = 2 * L.card
  rw [Nat.mul_sub_left_distrib, Nat.mul_one, ← hoff, hcard]

lemma block_energy (S : Finset ℕ) (hS : IsSidon (↑S : Set ℕ))
    (hpos : ∀ a ∈ S, 0 < a) {D : ℕ} (hD : 0 < D)
    (M : ℕ) :
    ∑ b ∈ range M, ((S.filter (fun x => (x - 1) / D = b)).card)^2 ≤ 4 * D + M := by
  let P := (S ×ˢ S).filter (fun p => p.1 < p.2 ∧ p.2 - p.1 < D)
  let T (b : ℕ) := S.filter (fun x => (x - 1) / D = b)
  have single (b : ℕ) :
      (T b).card ^ 2 ≤ 4 * (P.filter (fun p => (p.1 - 1) / D = b)).card + 1 := by
    let U := ((T b) ×ˢ (T b)).filter (fun p => p.1 < p.2)
    have incl : U ⊆ P.filter (fun p => (p.1 - 1) / D = b) := by
      intro p hp
      simp only [U, T, mem_filter, mem_product] at hp
      simp only [P, mem_filter, mem_product]
      have hp1 := hpos _ hp.1.1.1
      have ha : b * D ≤ p.1 - 1 ∧ p.1 - 1 ≤ b * D + D - 1 := (Nat.div_eq_iff hD).mp hp.1.1.2
      have hc : b * D ≤ p.2 - 1 ∧ p.2 - 1 ≤ b * D + D - 1 := (Nat.div_eq_iff hD).mp hp.1.2.2
      refine ⟨⟨⟨hp.1.1.1, hp.1.2.1⟩, hp.2, ?_⟩, hp.1.1.2⟩
      omega
    have hcard := Finset.card_le_card incl
    have hpairs : (T b).card * ((T b).card - 1) = 2 * U.card := card_mul_sub_one_eq_two_ordered
    rcases hx : (T b).card with _ | n
    · simp
    · rw [hx, Nat.succ_sub_one] at hpairs
      nlinarith [Nat.zero_le (n * n)]
  calc
    _ ≤ ∑ b ∈ range M, (4 * (P.filter (fun p => (p.1 - 1) / D = b)).card + 1) :=
      sum_le_sum (fun b _ => single b)
    _ ≤ _ := by
      rw [sum_add_distrib, ← mul_sum, sum_card_fiberwise_eq_card_filter]
      have h := (card_filter_le P (fun p => (p.1 - 1) / D ∈ range M)).trans (sidon_ordered_pairs_le hS hD)
      simpa using (show 4 * (P.filter (fun p => (p.1 - 1) / D ∈ range M)).card + M ≤
        4 * D + M by omega)

lemma prefix_energy (f : ℕ → ℝ) (J : ℕ) :
    let X := fun j : ℕ => (∑ b ∈ range (4^j), f b) / (2:ℝ)^j
    (∑ j ∈ range (J+1), (X j)^2) + (X J)^2 ≤
      4 * ∑ b ∈ range (4^J), (f b)^2 := by
  let X := fun j : ℕ => (∑ b ∈ range (4^j), f b) / (2:ℝ)^j
  change (∑ j ∈ range (J+1), (X j)^2) + (X J)^2 ≤ _
  induction J with
  | zero => simp [X]; nlinarith [sq_nonneg (f 0)]
  | succ j ih =>
    let I := Ico (4^j) (4^(j+1))
    let a := (∑ b ∈ I, f b) / (2:ℝ)^(j+1)
    have hp : (4:ℕ)^j ≤ 4^(j+1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hp' : ((4^(j+1):ℕ):ℝ) = ((2:ℝ)^(j+1))^2 := by
      push_cast
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    have hX : X (j+1) = X j / 2 + a := by
      dsimp only [X, a, I]
      rw [← sum_range_add_sum_Ico f hp, pow_succ (2:ℝ)]
      field_simp
    have hI : (I.card : ℝ) ≤ ((2:ℝ)^(j+1))^2 := by
      rw [← hp']
      exact_mod_cast (show I.card ≤ 4^(j+1) by simp [I])
    have ha : a^2 ≤ ∑ b ∈ I, (f b)^2 := by
      dsimp only [a]
      rw [div_pow, div_le_iff₀ (by positivity)]
      calc
        _ ≤ (I.card : ℝ) * ∑ b ∈ I, (f b)^2 := sq_sum_le_card_mul_sum_sq
        _ ≤ _ := by
          rw [mul_comm (∑ b ∈ I, (f b)^2)]
          exact mul_le_mul_of_nonneg_right hI (sum_nonneg fun b _ => sq_nonneg (f b))
    have hE := sum_range_add_sum_Ico (fun b => (f b)^2) hp
    change (∑ b ∈ range (4^j), (f b)^2) + (∑ b ∈ I, (f b)^2) = _ at hE
    rw [sum_range_succ _ (j+1), hX, ← hE]
    nlinarith [sq_nonneg (X j / 2 - a)]

lemma finite_scale (R : ℕ) (S : Finset ℕ) (hR : 16 ≤ R)
    (hsub : (↑S : Set ℕ) ⊆ Set.Icc 1 (2^(2*R))) (hS : IsSidon (↑S : Set ℕ)) :
    ∃ k ∈ Set.Icc R (2*R), (S.filter (· ≤ 2^k)).card^2 * k ≤ 512 * 2^k := by
  let D : ℕ := 2^R
  let J : ℕ := R/2
  let f (b : ℕ) := (S.filter (fun x => (x - 1) / D = b)).card
  let X (j : ℕ) := (∑ b ∈ range (4^j), (f b : ℝ)) / (2:ℝ)^j
  have hD : 0 < D := by dsimp [D]; positivity
  have hpos (a : ℕ) (ha : a ∈ S) : 0 < a := (hsub ha).1
  have pow4 (j : ℕ) : (4:ℕ)^j = 2^(2*j) := by rw [pow_mul]; norm_num
  have hdscale (j : ℕ) : 4^j * D = 2^(R+2*j) := by rw [pow4, pow_add]; dsimp [D]; ring
  have hM : 4^J ≤ D := by rw [pow4]; exact Nat.pow_le_pow_right (by decide) (by dsimp [J]; omega)
  have hE : ∑ b ∈ range (4^J), (f b : ℝ)^2 ≤ 5*(D : ℝ) := by
    have h := block_energy S hS hpos hD (4^J)
    have h' : ∑ b ∈ range (4^J), (f b)^2 ≤ 5*D := by dsimp [f]; omega
    exact_mod_cast h'
  have hX : ∑ j ∈ range (J+1), (X j)^2 ≤ 20*(D:ℝ) := by
    have h := prefix_energy (fun b => (f b:ℝ)) J
    change (∑ j ∈ range (J+1), (X j)^2) + (X J)^2 ≤ _ at h
    linarith [sq_nonneg (X J)]
  have hprefix (j : ℕ) : (S.filter (· ≤ 2^(R+2*j))).card = ∑ b ∈ range (4^j), f b := by
    dsimp [f]
    rw [sum_card_fiberwise_eq_card_filter]
    apply congrArg Finset.card
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨ha, h⟩
      exact ⟨ha, (Nat.div_lt_iff_lt_mul hD).mpr (by rw [hdscale]; have := hpos a ha; omega)⟩
    · rintro ⟨ha, h⟩
      have h' := (Nat.div_lt_iff_lt_mul hD).mp h
      rw [hdscale] at h'
      exact ⟨ha, by omega⟩
  by_contra! hbad
  have hlarge (j : ℕ) (hj : j ∈ range (J+1)) : 512*(D:ℝ) ≤ (X j)^2 * (2*R:ℕ) := by
    have hjR : R + 2*j ≤ 2*R := by have := mem_range.mp hj; dsimp [J] at this; omega
    have hb := hbad (R+2*j) (show R+2*j ∈ Set.Icc R (2*R) from ⟨by omega, hjR⟩)
    rw [hprefix, ← hdscale] at hb
    have hb' : 512*((4:ℝ)^j * (D:ℝ)) ≤ (∑ b ∈ range (4^j), (f b:ℝ))^2 * (2*R:ℕ) := by
      exact_mod_cast hb.le.trans (Nat.mul_le_mul_left _ hjR)
    have pow4' : (4:ℝ)^j = ((2:ℝ)^j)^2 := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
    dsimp [X]
    rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    rw [pow4'] at hb'
    linarith
  have hsum := sum_le_sum hlarge
  rw [← sum_mul (range (J+1)) (fun j => (X j)^2)] at hsum
  simp only [sum_const, card_range, nsmul_eq_mul] at hsum
  have hupper := mul_le_mul_of_nonneg_right hX (show (0:ℝ) ≤ (2*R:ℕ) by positivity)
  have hJR : R ≤ 2*(J+1) := by dsimp [J]; omega
  have hJR' : (R:ℝ) ≤ 2*((J:ℝ)+1) := by exact_mod_cast hJR
  push_cast at hsum hupper
  have hD' : (0:ℝ) < D := by exact_mod_cast hD
  have he := mul_le_mul_of_nonneg_right hJR' hD'.le
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) J) hD'.le]

end FiniteSidon1191

theorem OMA.solution : OMA.R_Erdos1191_erdos_1191_parts_i_R1.H1 := by
  exact FiniteSidon1191.finite_scale
