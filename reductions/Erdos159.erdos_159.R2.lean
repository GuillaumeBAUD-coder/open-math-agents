import FormalConjectures.ErdosProblems.«159»

/-!
# Triangle-degree pruning for the four-cycle versus clique Ramsey problem

Bad graphs (no four-cycle, no independent `n`-set) are pruned in two ways at once:
vertices of low ordinary degree (closed neighbourhood deleted, charged to an
independent set of witnesses) and vertices lying in few triangles (charged to the
triangles they kill). The pruned triangle-sparse part is bounded by averaging a
triangle-free cap over random samples (each sample of size `2L` must contain many
triangles). So a power saving follows from a triangle-free bound (H1, same as R1.H1)
plus a bound for cores of large minimum ordinary degree and minimum triangle degree
above `n ^ ε` (H2), for all small `ε`.
-/

-- Credit: @mucoucah

namespace OMA.R_Erdos159_erdos_159_R2

open scoped BigOperators Classical
open Finset SimpleGraph


open scoped BigOperators Classical
open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- Delete one representative of each forbidden set that lies in the sample. -/
private lemma avoid_family (S : Finset V) (F : Finset (Finset V))
    (hne : ∀ B ∈ F, B.Nonempty) :
    ∃ U ⊆ S, (∀ B ∈ F, ¬ B ⊆ U) ∧
      S.card ≤ U.card + (F.filter (· ⊆ S)).card := by
  classical
  let Q := F.filter (· ⊆ S)
  let pick : Q → V := fun B => (hne B.1 (Finset.mem_filter.mp B.2).1).choose
  let R := Q.attach.image (fun B => pick B)
  let U := S \ R
  refine ⟨U, Finset.sdiff_subset, ?_, ?_⟩
  · intro B hB hBU
    have hBS : B ⊆ S := hBU.trans Finset.sdiff_subset
    let b : Q := ⟨B, Finset.mem_filter.mpr ⟨hB, hBS⟩⟩
    have hpB : pick b ∈ B := (hne b.1 (Finset.mem_filter.mp b.2).1).choose_spec
    have hpR : pick b ∈ R := Finset.mem_image_of_mem _ (Finset.mem_attach _ _)
    exact (Finset.mem_sdiff.mp (hBU hpB)).2 hpR
  · have hR : R.card ≤ Q.card := Finset.card_image_le.trans_eq Finset.card_attach
    exact Finset.card_le_card_sdiff_add_card.trans (Nat.add_le_add_left hR _)

/-- Average the vertex deletion bound over all samples of size `k`. -/
private lemma fixed_sample_bound (S : Finset V) (F : Finset (Finset V))
    (hF : ∀ B ∈ F, B ⊆ S ∧ B.card = 3) (L k : ℕ) (hk : 3 ≤ k)
    (hcap : ∀ U ⊆ S, (∀ B ∈ F, ¬ B ⊆ U) → U.card ≤ L) :
    k * S.card.choose k ≤ L * S.card.choose k + F.card * (S.card - 3).choose (k - 3) := by
  classical
  let P := S.powersetCard k
  have hsample (A : Finset V) (hA : A ∈ P) : k ≤ L + (F.filter (· ⊆ A)).card := by
    obtain ⟨hAS, hAk⟩ := Finset.mem_powersetCard.mp hA
    obtain ⟨U, hUA, hUF, hcount⟩ := avoid_family A F (fun B hB => by
      apply Finset.card_pos.mp
      rw [(hF B hB).2]
      decide)
    rw [← hAk]
    exact hcount.trans (Nat.add_le_add_right (hcap U (hUA.trans hAS) hUF) _)
  have card_filter_eq_sum (Q : Finset (Finset V)) (p : Finset V → Prop)
      [DecidablePred p] :
      (Q.filter p).card = ∑ B ∈ Q, if p B then 1 else 0 :=
    (Finset.sum_boole (R := ℕ) p Q).symm
  have hcount :
      (∑ A ∈ P, (F.filter (· ⊆ A)).card) = F.card * (S.card - 3).choose (k - 3) := by
    calc
      _ = ∑ B ∈ F, ((S.powersetCard k).filter (B ⊆ ·)).card := by
        simp only [card_filter_eq_sum, P]
        exact Finset.sum_comm
      _ = F.card * (S.card - 3).choose (k - 3) := by
        apply Finset.sum_const_nat
        intro B hB
        obtain ⟨hBS, hB3⟩ := hF B hB
        rw [Finset.card_filter_powersetCard_subset B S k hBS (hB3 ▸ hk), hB3]
  have hsum := Finset.sum_le_sum hsample
  rw [Finset.sum_add_distrib, hcount] at hsum
  simpa [P, Finset.card_powersetCard, mul_comm] using hsum

/-- A bound on triangle-free induced subsets forces a cubic lower bound on the
number of triangles, once the vertex set is more than twice the bound. -/
lemma triangle_count_of_induced_cap (G : SimpleGraph V) (S : Finset V) (L : ℕ)
    (hL : 2 ≤ L)
    (hcap : ∀ U ⊆ S, (∀ B ⊆ U, ¬ G.IsNClique 3 B) → U.card ≤ L) :
    S.card ≤ 2 * L ∨
      S.card ^ 3 ≤ 32 * ((S.powersetCard 3).filter (G.IsNClique 3)).card * L ^ 2 := by
  classical
  let F := (S.powersetCard 3).filter (G.IsNClique 3)
  let m := S.card
  by_cases hm : m ≤ 2 * L
  · exact Or.inl hm
  right
  have hLk : 3 ≤ 2 * L := by omega
  have hkm : 2 * L ≤ m := by omega
  have hm4 : 4 ≤ m := by omega
  have hsample := fixed_sample_bound S F
    (fun B hB => Finset.mem_powersetCard.mp (Finset.mem_filter.mp hB).1) L (2 * L) hLk
    (fun U hUS hUF => hcap U hUS (fun B hBU hB =>
      hUF B (Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨hBU.trans hUS, hB.card_eq⟩, hB⟩) hBU))
  change 2 * L * m.choose (2 * L) ≤
    L * m.choose (2 * L) + F.card * (m - 3).choose (2 * L - 3) at hsample
  have hcancel : L * m.choose (2 * L) ≤ F.card * (m - 3).choose (2 * L - 3) := by
    rw [show 2 * L * m.choose (2 * L) =
      L * m.choose (2 * L) + L * m.choose (2 * L) by ring] at hsample
    exact Nat.le_of_add_le_add_left hsample
  have hp : 0 < m.choose (2 * L) := Nat.choose_pos hkm
  have hchoose : L * m.choose 3 ≤ F.card * (2 * L).choose 3 := by
    apply Nat.le_of_mul_le_mul_right (c := m.choose (2 * L)) _ hp
    calc
      (L * m.choose 3) * m.choose (2 * L) =
          (L * m.choose (2 * L)) * m.choose 3 := by ring
      _ ≤ (F.card * (m - 3).choose (2 * L - 3)) * m.choose 3 :=
        Nat.mul_le_mul_right _ hcancel
      _ = F.card * (m.choose 3 * (m - 3).choose (2 * L - 3)) := by ring
      _ = (F.card * (2 * L).choose 3) * m.choose (2 * L) := by
        rw [← Nat.choose_mul hLk]
        ring
  have three_choose (a : ℕ) : 6 * a.choose 3 = a * (a - 1) * (a - 2) := by
    calc
      _ = a.descFactorial 3 := (Nat.descFactorial_eq_factorial_mul_choose a 3).symm
      _ = _ := by simp [Nat.descFactorial_succ, Nat.mul_comm]
  have htriple : L * (m * (m - 1) * (m - 2)) ≤
      F.card * (2 * L * (2 * L - 1) * (2 * L - 2)) := by
    rw [← three_choose, ← three_choose]
    simpa only [Nat.mul_left_comm] using Nat.mul_le_mul_left 6 hchoose
  have hleft : m ^ 3 ≤ 4 * (m * (m - 1) * (m - 2)) := by
    calc
      m ^ 3 = m * m * m := by ring
      _ ≤ m * (2 * (m - 1)) * (2 * (m - 2)) := by
        gcongr <;> omega
      _ = _ := by ring
  have hright : 2 * L * (2 * L - 1) * (2 * L - 2) ≤ 8 * L ^ 3 := by
    calc
      _ ≤ 2 * L * (2 * L) * (2 * L) := by gcongr <;> omega
      _ = _ := by ring
  change m ^ 3 ≤ 32 * F.card * L ^ 2
  apply Nat.le_of_mul_le_mul_right (c := L) _ (by omega)
  calc
    m ^ 3 * L ≤ (4 * (m * (m - 1) * (m - 2))) * L :=
      Nat.mul_le_mul_right _ hleft
    _ = 4 * (L * (m * (m - 1) * (m - 2))) := by ring
    _ ≤ 4 * (F.card * (2 * L * (2 * L - 1) * (2 * L - 2))) :=
      Nat.mul_le_mul_left _ htriple
    _ ≤ 4 * (F.card * (8 * L ^ 3)) := by gcongr
    _ = (32 * F.card * L ^ 2) * L := by ring


/-- A triangle-free induced cap of `L` gives a cap of `6 * D * L` on vertex sets
having at most `D ^ 2` triangles per vertex. -/
lemma card_le_of_sparse_triangles (G : SimpleGraph V) (S : Finset V)
    {L : ℕ} (hL : 2 ≤ L) {D : ℝ} (hD : 1 ≤ D)
    (hcap : ∀ U ⊆ S, (∀ B ⊆ U, ¬ G.IsNClique 3 B) → U.card ≤ L)
    (htri : (((S.powersetCard 3).filter (G.IsNClique 3)).card : ℝ) ≤ (S.card : ℝ) * D ^ 2) :
    (S.card : ℝ) ≤ 6 * D * L := by
  let m : ℝ := S.card
  change m ≤ 6 * D * (L : ℝ)
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hL₀ : 0 ≤ (L : ℝ) := Nat.cast_nonneg _
  rcases triangle_count_of_induced_cap G S L hL hcap with hsmall | hcubic
  · have hle : m ≤ 2 * (L : ℝ) := by
      change (S.card : ℝ) ≤ 2 * (L : ℝ)
      exact_mod_cast hsmall
    nlinarith only [hle, hL₀, mul_nonneg (sub_nonneg.mpr hD) hL₀]
  by_cases hm₀ : m = 0
  · rw [hm₀]
    positivity
  have hmpos : 0 < m := lt_of_le_of_ne hm (fun h => hm₀ h.symm)
  change S.card ^ 3 ≤ 32 * ((S.powersetCard 3).filter (G.IsNClique 3)).card * L ^ 2 at hcubic
  have hcubic' : m ^ 3 ≤ 32 * (((S.powersetCard 3).filter (G.IsNClique 3)).card : ℝ) * (L : ℝ) ^ 2 := by
    change (S.card : ℝ) ^ 3 ≤ 32 * (((S.powersetCard 3).filter (G.IsNClique 3)).card : ℝ) * (L : ℝ) ^ 2
    exact_mod_cast hcubic
  have hsq : m ^ 2 ≤ 32 * (D * (L : ℝ)) ^ 2 := by
    apply le_of_mul_le_mul_of_pos_left _ hmpos
    calc
      m * m ^ 2 = m ^ 3 := by ring
      _ ≤ 32 * (((S.powersetCard 3).filter (G.IsNClique 3)).card : ℝ) * (L : ℝ) ^ 2 := hcubic'
      _ ≤ 32 * (m * D ^ 2) * (L : ℝ) ^ 2 := by gcongr
      _ = m * (32 * (D * (L : ℝ)) ^ 2) := by ring
  apply (sq_le_sq₀ hm (by positivity : 0 ≤ 6 * D * (L : ℝ))).mp
  nlinarith only [hsq, sq_nonneg (D * (L : ℝ))]


private lemma triangle_count_insert_le (G : SimpleGraph V) {R S : Finset V} {x : V}
    (hinc : insert x R ⊆ S) :
    (((insert x R).powersetCard 3).filter (G.IsNClique 3)).card ≤ ((R.powersetCard 3).filter (G.IsNClique 3)).card + ((S.powersetCard 3).filter (fun B => G.IsNClique 3 B ∧ x ∈ B)).card := by
  classical
  let F := (R.powersetCard 3).filter (G.IsNClique 3)
  let Q := (S.powersetCard 3).filter (fun B => G.IsNClique 3 B ∧ x ∈ B)
  have hsubset : ((insert x R).powersetCard 3).filter (G.IsNClique 3) ⊆ F ∪ Q := by
    intro B hB
    obtain ⟨hb, htri⟩ := Finset.mem_filter.mp hB
    obtain ⟨hBsub, hB3⟩ := Finset.mem_powersetCard.mp hb
    apply Finset.mem_union.mpr
    by_cases hxb : x ∈ B
    · exact Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨hBsub.trans hinc, hB3⟩, htri, hxb⟩)
    · have hBR : B ⊆ R := by
        intro y hy
        rcases Finset.mem_insert.mp (hBsub hy) with h | h
        · exact (hxb (h ▸ hy)).elim
        · exact h
      exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hBR, hB3⟩, htri⟩)
  exact (Finset.card_le_card hsubset).trans (Finset.card_union_le F Q)

/-- Iteratively peel vertices with few incident triangles. The triangles in the
removed set can each be charged to their first vertex removed. -/
lemma split_at_triangle_degree (G : SimpleGraph V) (S : Finset V) (d : ℝ) :
    ∃ R U : Finset V, Disjoint R U ∧ R ∪ U = S ∧
      (((R.powersetCard 3).filter (G.IsNClique 3)).card : ℝ) ≤ (R.card : ℝ) * d ∧
      ∀ x ∈ U, d < (((U.powersetCard 3).filter (fun B => G.IsNClique 3 B ∧ x ∈ B)).card : ℝ) := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hdense : ∀ x ∈ S, d < (((S.powersetCard 3).filter (fun B => G.IsNClique 3 B ∧ x ∈ B)).card : ℝ)
    · have hempty : (∅ : Finset V).powersetCard 3 = ∅ :=
        Finset.powersetCard_eq_empty.mpr (by simp)
      exact ⟨∅, S, by simp, by simp, by simp [hempty], hdense⟩
    push Not at hdense
    obtain ⟨x, hx, hdeg⟩ := hdense
    obtain ⟨R, U, hdisj, hsplit, hRc, hUd⟩ := ih (S.erase x) (Finset.erase_ssubset hx)
    have hRsub : R ⊆ S.erase x := hsplit ▸ Finset.subset_union_left
    have hUsub : U ⊆ S.erase x := hsplit ▸ Finset.subset_union_right
    have hxR : x ∉ R := fun h => Finset.notMem_erase x S (hRsub h)
    have hxU : x ∉ U := fun h => Finset.notMem_erase x S (hUsub h)
    refine ⟨insert x R, U, Finset.disjoint_insert_left.mpr ⟨hxU, hdisj⟩, ?_, ?_, hUd⟩
    · rw [Finset.insert_union, hsplit, Finset.insert_erase hx]
    have hinc : insert x R ⊆ S := Finset.insert_subset hx (hRsub.trans (Finset.erase_subset _ _))
    have hcount := triangle_count_insert_le G hinc
    have hcount' : ((((insert x R).powersetCard 3).filter (G.IsNClique 3)).card : ℝ) ≤
        (((R.powersetCard 3).filter (G.IsNClique 3)).card : ℝ) + (((S.powersetCard 3).filter (fun B => G.IsNClique 3 B ∧ x ∈ B)).card : ℝ) := by exact_mod_cast hcount
    rw [Finset.card_insert_of_notMem hxR, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact hcount'.trans (add_le_add hRc hdeg)

/-- Combine the sparse bound and a bound for sets of large minimum triangle degree. -/
lemma card_le_of_triangle_degree_caps (G : SimpleGraph V) (S : Finset V)
    {L : ℕ} (hL : 2 ≤ L) {D M : ℝ} (hD : 1 ≤ D)
    (hcap : ∀ U ⊆ S, (∀ B ⊆ U, ¬ G.IsNClique 3 B) → U.card ≤ L)
    (hcore : ∀ U ⊆ S, (∀ x ∈ U, D ^ 2 < (((U.powersetCard 3).filter (fun B => G.IsNClique 3 B ∧ x ∈ B)).card : ℝ)) →
      (U.card : ℝ) ≤ M) :
    (S.card : ℝ) ≤ 6 * D * L + M := by
  obtain ⟨R, U, hdisj, hsplit, hR, hU⟩ := split_at_triangle_degree G S (D ^ 2)
  have hRsub : R ⊆ S := hsplit ▸ Finset.subset_union_left
  have hUsub : U ⊆ S := hsplit ▸ Finset.subset_union_right
  have hsparse := card_le_of_sparse_triangles G R hL hD
    (fun T hTR => hcap T (hTR.trans hRsub)) hR
  rw [← hsplit, Finset.card_union_of_disjoint hdisj, Nat.cast_add]
  exact add_le_add hsparse (hcore U hUsub hU)



/-- A power saving for triangle-free subsets, together with one for subsets of
minimum triangle degree above `n ^ ε`, gives an exponent of `2 - ε / 2`. -/
theorem ramsey_of_triangle_degree_bounds {ε A B : ℝ}
    (hε : 0 < ε) (hεone : ε ≤ 1) (hA : 1 ≤ A) (hB : 0 ≤ B)
    (hfree : ∀ (n m : ℕ) (G : SimpleGraph (Fin m)) (S : Finset (Fin m)),
      1 ≤ n → (¬ (cycleGraph 4).IsContained G ∧ ¬ (completeGraph (Fin n)).IsContained Gᶜ) →
      (∀ T ⊆ S, ¬ G.IsNClique 3 T) → (S.card : ℝ) ≤ A * (n : ℝ) ^ (2 - ε))
    (hcore : (∀ (n m : ℕ) (G : SimpleGraph (Fin m)) (S : Finset (Fin m)),
      1 ≤ n → (¬ (cycleGraph 4).IsContained G ∧ ¬ (completeGraph (Fin n)).IsContained Gᶜ) →
      (∀ x ∈ S, (n : ℝ) ^ ε < (((S.powersetCard 3).filter (fun B => G.IsNClique 3 B ∧ x ∈ B)).card : ℝ)) →
      (S.card : ℝ) ≤ B * (n : ℝ) ^ (2 - ε / 2))) :
    ∀ n : ℕ, 1 ≤ n → (graphRamsey (cycleGraph 4) (completeGraph (Fin n)) : ℝ) ≤
      (6 * (A + 3) + B + 1) * (n : ℝ) ^ (2 - ε / 2) := by
  intro n hn
  let D : ℝ := (n : ℝ) ^ (ε / 2)
  let Y : ℝ := (n : ℝ) ^ (2 - ε)
  let X : ℝ := (n : ℝ) ^ (2 - ε / 2)
  let L := ⌈A * Y⌉₊ + 2
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hD : 1 ≤ D := Real.one_le_rpow hnreal (by linarith)
  have hY : 1 ≤ Y := Real.one_le_rpow hnreal (by linarith)
  have hX : 1 ≤ X := Real.one_le_rpow hnreal (by linarith)
  have hApos : 0 ≤ A := by linarith
  have hYpos : 0 ≤ Y := by linarith
  have hXpos : 0 ≤ X := by linarith
  have hL : 2 ≤ L := by dsimp [L]; omega
  have hceil : (⌈A * Y⌉₊ : ℝ) ≤ A * Y + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hApos hYpos)).le
  have hLupper : (L : ℝ) ≤ (A + 3) * Y := by
    dsimp [L]
    push_cast
    linarith only [hY, hceil]
  have hDY : D * Y = X := by
    dsimp [D, Y, X]
    rw [← Real.rpow_add hnpos, show ε / 2 + (2 - ε) = 2 - ε / 2 by ring]
  have hDsq : D ^ 2 = (n : ℝ) ^ ε := by
    dsimp [D]
    rw [pow_two, ← Real.rpow_add hnpos, show ε / 2 + ε / 2 = ε by ring]
  let P := (6 * (A + 3) + B) * X
  have hP : 0 ≤ P := by
    exact mul_nonneg (by linarith) hXpos
  have hbad_cap (m : ℕ) (G : SimpleGraph (Fin m)) (hbad : (¬ (cycleGraph 4).IsContained G ∧ ¬ (completeGraph (Fin n)).IsContained Gᶜ)) : (m : ℝ) ≤ P := by
    have hc (U : Finset (Fin m)) (_ : U ⊆ Finset.univ)
        (hU : ∀ T ⊆ U, ¬ G.IsNClique 3 T) : U.card ≤ L := by
      have hcU : U.card ≤ ⌈A * Y⌉₊ := by
        exact_mod_cast (hfree n m G U hn hbad hU).trans (Nat.le_ceil (A * Y))
      dsimp [L]
      omega
    have hd (U : Finset (Fin m)) (_ : U ⊆ Finset.univ)
        (hU : ∀ x ∈ U, D ^ 2 < (((U.powersetCard 3).filter (fun B => G.IsNClique 3 B ∧ x ∈ B)).card : ℝ)) : (U.card : ℝ) ≤ B * X := by
      rw [hDsq] at hU
      exact hcore n m G U hn hbad hU
    have hbound : (m : ℝ) ≤ 6 * D * L + B * X := by
      simpa using card_le_of_triangle_degree_caps G Finset.univ hL hD hc hd
    calc
      _ ≤ 6 * D * L + B * X := hbound
      _ ≤ 6 * D * ((A + 3) * Y) + B * X := by
        gcongr
      _ = P := by
        dsimp [P]
        rw [← hDY]
        ring
  let N := ⌊P⌋₊ + 1
  have hN : P < (N : ℝ) := by simpa [N] using Nat.lt_floor_add_one P
  have hit (G : SimpleGraph (Fin N)) :
      (cycleGraph 4).IsContained G ∨ (completeGraph (Fin n)).IsContained Gᶜ := by
    by_contra h
    rw [not_or] at h
    exact hN.not_ge (hbad_cap N G h)
  have hRamsey : graphRamsey (cycleGraph 4) (completeGraph (Fin n)) ≤ N := Nat.sInf_le hit
  calc
    _ ≤ (N : ℝ) := by exact_mod_cast hRamsey
    _ ≤ P + 1 := by simpa [N] using add_le_add_right (Nat.floor_le hP) (1 : ℝ)
    _ ≤ _ := by change P + 1 ≤ (6 * (A + 3) + B + 1) * X; linarith only [hX, show P = _ from rfl]

private lemma indep_budget_after_neighborhood (G : SimpleGraph V) {r : ℕ} {S : Finset V}
    {x : V} (hx : x ∈ S)
    (hind : ∀ I ⊆ S, G.IsIndepSet (I : Set V) → I.card ≤ r + 1)
    (I : Finset V) (hIR : I ⊆ S \ insert x (S.filter (G.Adj x)))
    (hI : G.IsIndepSet (I : Set V)) : I.card ≤ r := by
  classical
  have hRsub : S \ insert x (S.filter (G.Adj x)) ⊆ S := Finset.sdiff_subset
  have hxN : x ∈ insert x (S.filter (G.Adj x)) := Finset.mem_insert_self _ _
  have hxI : x ∉ I := fun h => (Finset.mem_sdiff.mp (hIR h)).2 hxN
  have hi : G.IsIndepSet (↑(insert x I) : Set V) := by
    rw [Finset.coe_insert, isIndepSet_iff, Set.pairwise_insert_of_notMem hxI]
    refine ⟨hI, ?_⟩
    intro y hy
    have hyR := Finset.mem_sdiff.mp (hIR hy)
    have hxy : ¬ G.Adj x y := fun h =>
      hyR.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hyR.1, h⟩))
    exact ⟨hxy, fun hyx => hxy hyx.symm⟩
  have hiBound := hind (insert x I) (Finset.insert_subset hx (hIR.trans hRsub)) hi
  rw [Finset.card_insert_of_notMem hxI] at hiBound
  omega

/-- A low-degree vertex and its neighbours cost at most `d` vertices and one
unit of the independence budget. -/
private lemma minimum_degree_core (G : SimpleGraph V) (d r : ℕ) (S : Finset V)
    (hind : ∀ I ⊆ S, G.IsIndepSet (I : Set V) → I.card ≤ r) :
    ∃ U ⊆ S, S.card ≤ U.card + r * d ∧
      ∀ x ∈ U, d ≤ (U.filter (G.Adj x)).card := by
  classical
  induction r generalizing S with
  | zero =>
    have hempty : S = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hs
      obtain ⟨x, hx⟩ := hs
      have hc := hind {x} (Finset.singleton_subset_iff.mpr hx) (by simp)
      simp at hc
    subst S
    exact ⟨∅, by simp, by simp, by simp⟩
  | succ r ih =>
    by_cases hmin : ∀ x ∈ S, d ≤ (S.filter (G.Adj x)).card
    · exact ⟨S, le_rfl, Nat.le_add_right _ _, hmin⟩
    push Not at hmin
    obtain ⟨x, hx, hdeg⟩ := hmin
    let N := insert x (S.filter (G.Adj x))
    let R := S \ N
    have hRsub : R ⊆ S := Finset.sdiff_subset
    have hR : ∀ I ⊆ R, G.IsIndepSet (I : Set V) → I.card ≤ r :=
      indep_budget_after_neighborhood G hx hind
    obtain ⟨U, hUR, hcard, hU⟩ := ih R hR
    have hN : N.card ≤ d := (Finset.card_insert_le _ _).trans (by omega)
    have hS : S.card ≤ R.card + N.card := Finset.card_le_card_sdiff_add_card
    refine ⟨U, hUR.trans hRsub, ?_, hU⟩
    rw [Nat.succ_mul]
    omega

private lemma indep_card_le {m n : ℕ} {G : SimpleGraph (Fin m)}
    (hbad : (¬ (cycleGraph 4).IsContained G ∧ ¬ (completeGraph (Fin n)).IsContained Gᶜ)) (I : Finset (Fin m)) (hI : G.IsIndepSet (I : Set (Fin m))) :
    I.card ≤ n - 1 := by
  classical
  have hlt : I.card < n := by
    by_contra! hge
    obtain ⟨J, hJI, hJ⟩ := Finset.exists_subset_card_eq hge
    apply hbad.2
    apply ((Gᶜ).not_cliqueFree_iff_top_isContained n).mp
    intro hfree
    have hclique : Gᶜ.IsClique (I : Set (Fin m)) := by
      simpa only [isClique_compl] using hI
    exact hfree J ⟨hclique.subset hJI, hJ⟩
  omega


private lemma budget_le_quarter (m n : ℕ) :
    4 * ((n - 1) * (m / (4 * n))) ≤ m := by
  let d := m / (4 * n)
  change 4 * ((n - 1) * d) ≤ m
  calc
    _ = (4 * (n - 1)) * d := by ring
    _ ≤ (4 * n) * d := by gcongr; omega
    _ ≤ m := by simpa [d, Nat.mul_comm] using Nat.div_mul_le_self m (4 * n)

private lemma lower_degree_window {n m s k : ℕ} (hn : 1 ≤ n) (hs : s ≤ m)
    (hk : m / (4 * n) ≤ k) : s ≤ 16 * n * (k + 1) := by
  have hlarge : m < (k + 1) * (4 * n) :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < 4 * n)).mp (Nat.lt_succ_of_le hk)
  calc
    s ≤ m := hs
    _ ≤ (k + 1) * (4 * n) := hlarge.le
    _ ≤ (k + 1) * (16 * n) := by gcongr; omega
    _ = _ := Nat.mul_comm _ _

/-- The triangle-free hypothesis of the Ramsey transfer follows from a bound
on the degree window used by the existing R1 reduction. -/
lemma triangle_free_cap_of_degree_window {ε A : ℝ}
    (hwindow : (∀ (n m : ℕ) (G : SimpleGraph (Fin m)) (S : Finset (Fin m)),
      1 ≤ n → (¬ (cycleGraph 4).IsContained G ∧ ¬ (completeGraph (Fin n)).IsContained Gᶜ) →
      (∀ x ∈ S, S.card ≤ 16 * n * ((S.filter (G.Adj x)).card + 1) ∧
        (S.filter (G.Adj x)).card ≤ 2 * (n - 1)) →
      (∀ T ⊆ S, ¬ G.IsNClique 3 T) → (S.card : ℝ) ≤ A * (n : ℝ) ^ (2 - ε))) :
    ∀ (n m : ℕ) (G : SimpleGraph (Fin m)) (S : Finset (Fin m)),
      1 ≤ n → (¬ (cycleGraph 4).IsContained G ∧ ¬ (completeGraph (Fin n)).IsContained Gᶜ) →
      (∀ T ⊆ S, ¬ G.IsNClique 3 T) → (S.card : ℝ) ≤ (2 * A) * (n : ℝ) ^ (2 - ε) := by
  classical
  intro n m G S hn hbad hfree
  let d := S.card / (4 * n)
  obtain ⟨U, hUS, hsize, hdeg⟩ :=
    minimum_degree_core G d (n - 1) S (fun I _ hI => indep_card_le hbad I hI)
  have hbudget : 4 * ((n - 1) * d) ≤ S.card := budget_le_quarter S.card n
  have hcompare : S.card ≤ 2 * U.card := by omega
  have hcompare' : (S.card : ℝ) ≤ 2 * (U.card : ℝ) := by exact_mod_cast hcompare
  have hUfree (T : Finset (Fin m)) (hTU : T ⊆ U) : ¬ G.IsNClique 3 T := hfree T (hTU.trans hUS)
  have hUwindow (x : Fin m) (hx : x ∈ U) :
      U.card ≤ 16 * n * ((U.filter (G.Adj x)).card + 1) ∧
        (U.filter (G.Adj x)).card ≤ 2 * (n - 1) := by
    constructor
    · exact lower_degree_window hn (Finset.card_le_card hUS) (hdeg x hx)
    · have hi : G.IsIndepSet (↑(U.filter (G.Adj x)) : Set (Fin m)) := by
        intro y hy z hz hyz hadj
        obtain ⟨hyU, hxy⟩ := Finset.mem_filter.mp hy
        obtain ⟨hzU, hxz⟩ := Finset.mem_filter.mp hz
        have hsub : ({x, y, z} : Finset (Fin m)) ⊆ U :=
          Finset.insert_subset hx (Finset.insert_subset hyU (Finset.singleton_subset_iff.mpr hzU))
        exact hUfree _ hsub (is3Clique_triple_iff.mpr ⟨hxy, hxz, hadj⟩)
      have b := indep_card_le hbad (U.filter (G.Adj x)) hi
      omega
  have hu := hwindow n m G U hn hbad hUwindow hUfree
  linarith only [hcompare', hu]

/-- Prune vertices of low ordinary degree and low triangle degree in the same
process. The ordinary-degree deletions have an independent set of witnesses. -/
lemma split_at_both_degrees (G : SimpleGraph V) (d : ℕ) (τ : ℝ)
    (S : Finset V) (r : ℕ)
    (hind : ∀ I ⊆ S, G.IsIndepSet (I : Set V) → I.card ≤ r) :
    ∃ R U : Finset V, R ⊆ S ∧ U ⊆ S ∧
      S.card ≤ R.card + U.card + r * d ∧
      (((R.powersetCard 3).filter (G.IsNClique 3)).card : ℝ) ≤ (R.card : ℝ) * τ ∧
      ∀ x ∈ U, d ≤ (U.filter (G.Adj x)).card ∧ τ < (((U.powersetCard 3).filter (fun B => G.IsNClique 3 B ∧ x ∈ B)).card : ℝ) := by
  classical
  induction S using Finset.strongInductionOn generalizing r with
  | _ S ih =>
    by_cases hdeg : ∀ x ∈ S, d ≤ (S.filter (G.Adj x)).card
    · by_cases htri : ∀ x ∈ S, τ < (((S.powersetCard 3).filter (fun B => G.IsNClique 3 B ∧ x ∈ B)).card : ℝ)
      · have hempty : (∅ : Finset V).powersetCard 3 = ∅ :=
          Finset.powersetCard_eq_empty.mpr (by simp)
        exact ⟨∅, S, by simp, le_rfl, by simp, by simp [hempty],
          fun x hx => ⟨hdeg x hx, htri x hx⟩⟩
      push Not at htri
      obtain ⟨x, hx, hxd⟩ := htri
      have hsub := Finset.erase_subset x S
      obtain ⟨R, U, hR, hU, hsize, hcount, hwin⟩ :=
        ih (S.erase x) (Finset.erase_ssubset hx) r (fun I hI => hind I (hI.trans hsub))
      have hxR : x ∉ R := fun h => Finset.notMem_erase x S (hR h)
      have hinc := Finset.insert_subset hx (hR.trans hsub)
      refine ⟨insert x R, U, hinc, hU.trans hsub, ?_, ?_, hwin⟩
      · have herase := Finset.card_erase_add_one hx
        rw [Finset.card_insert_of_notMem hxR]
        omega
      · have hstep : ((((insert x R).powersetCard 3).filter (G.IsNClique 3)).card : ℝ) ≤
            (((R.powersetCard 3).filter (G.IsNClique 3)).card : ℝ) + (((S.powersetCard 3).filter (fun B => G.IsNClique 3 B ∧ x ∈ B)).card : ℝ) := by
          exact_mod_cast triangle_count_insert_le G hinc
        rw [Finset.card_insert_of_notMem hxR, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
        exact hstep.trans (add_le_add hcount hxd)
    push Not at hdeg
    obtain ⟨x, hx, hxd⟩ := hdeg
    have hr : 1 ≤ r := by simpa using hind {x} (Finset.singleton_subset_iff.mpr hx) (by simp)
    let N := insert x (S.filter (G.Adj x))
    let S' := S \ N
    have hsub : S' ⊆ S := Finset.sdiff_subset
    have hxnot : x ∉ S' := fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_insert_self _ _)
    have hprop : S' ⊂ S :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun he => hxnot (he ▸ hx)⟩
    have hind' : ∀ I ⊆ S, G.IsIndepSet (I : Set V) → I.card ≤ r - 1 + 1 :=
      fun I hI hi => (hind I hI hi).trans (by omega)
    obtain ⟨R, U, hR, hU, hsize, hcount, hwin⟩ :=
      ih S' hprop (r - 1) (indep_budget_after_neighborhood G hx hind')
    have hN : N.card ≤ d := (Finset.card_insert_le _ _).trans (by omega)
    have hsplit : S.card ≤ S'.card + N.card := Finset.card_le_card_sdiff_add_card
    have hprod : (r - 1) * d + d = r * d := by
      calc
        _ = (r - 1) * d + 1 * d := by simp
        _ = _ := by rw [← Nat.add_mul, Nat.sub_add_cancel hr]
    exact ⟨R, U, hR.trans hsub, hU.trans hsub, by omega, hcount, hwin⟩


/-- With a triangle-free power bound, it suffices to bound the core with both
ordinary and triangle minimum degree constraints. -/
lemma large_triangle_degree_cap_of_windows {ε A B : ℝ}
    (hε : 0 < ε) (hεone : ε ≤ 1) (hA : 1 ≤ A)
    (hfree : (∀ (n m : ℕ) (G : SimpleGraph (Fin m)) (S : Finset (Fin m)),
      1 ≤ n → (¬ (cycleGraph 4).IsContained G ∧ ¬ (completeGraph (Fin n)).IsContained Gᶜ) →
      (∀ x ∈ S, S.card ≤ 16 * n * ((S.filter (G.Adj x)).card + 1) ∧
        (S.filter (G.Adj x)).card ≤ 2 * (n - 1)) →
      (∀ T ⊆ S, ¬ G.IsNClique 3 T) → (S.card : ℝ) ≤ A * (n : ℝ) ^ (2 - ε))) (hcore : (∀ (n m : ℕ) (G : SimpleGraph (Fin m)) (S : Finset (Fin m)),
    1 ≤ n → (¬ (cycleGraph 4).IsContained G ∧ ¬ (completeGraph (Fin n)).IsContained Gᶜ) →
    (∀ x ∈ S, S.card ≤ 16 * n * ((S.filter (G.Adj x)).card + 1) ∧
      (n : ℝ) ^ ε < (((S.powersetCard 3).filter (fun B => G.IsNClique 3 B ∧ x ∈ B)).card : ℝ)) →
    (S.card : ℝ) ≤ B * (n : ℝ) ^ (2 - ε / 2))) :
    (∀ (n m : ℕ) (G : SimpleGraph (Fin m)) (S : Finset (Fin m)),
      1 ≤ n → (¬ (cycleGraph 4).IsContained G ∧ ¬ (completeGraph (Fin n)).IsContained Gᶜ) →
      (∀ x ∈ S, (n : ℝ) ^ ε < (((S.powersetCard 3).filter (fun B => G.IsNClique 3 B ∧ x ∈ B)).card : ℝ)) →
      (S.card : ℝ) ≤ (24 * A + 2 * B) * (n : ℝ) ^ (2 - ε / 2)) := by
  classical
  intro n m G S hn hbad _
  let d := S.card / (4 * n)
  let D : ℝ := (n : ℝ) ^ (ε / 2)
  let Y : ℝ := (n : ℝ) ^ (2 - ε)
  let X : ℝ := (n : ℝ) ^ (2 - ε / 2)
  let L := ⌊2 * A * Y⌋₊
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hD : 1 ≤ D := Real.one_le_rpow hnreal (by linarith)
  have hY : 1 ≤ Y := Real.one_le_rpow hnreal (by linarith)
  have hAY : 2 ≤ 2 * A * Y := by nlinarith only [hA, hY, mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hY)]
  have hApos : 0 ≤ 2 * A * Y := by linarith
  have hL : 2 ≤ L := (Nat.le_floor_iff' (by decide : 2 ≠ 0)).mpr (by simpa using hAY)
  have hDY : D * Y = X := by
    dsimp [D, Y, X]
    rw [← Real.rpow_add hnpos, show ε / 2 + (2 - ε) = 2 - ε / 2 by ring]
  have hDsq : D ^ 2 = (n : ℝ) ^ ε := by
    dsimp [D]
    rw [pow_two, ← Real.rpow_add hnpos, show ε / 2 + ε / 2 = ε by ring]
  obtain ⟨R, U, _, hU, hsize, hRtri, hUwin⟩ :=
    split_at_both_degrees G d ((n : ℝ) ^ ε) S (n - 1) (fun I _ hi => indep_card_le hbad I hi)
  have hbudget : 4 * ((n - 1) * d) ≤ S.card := budget_le_quarter S.card n
  have hall : S.card ≤ 2 * (R.card + U.card) := by omega
  have hall' : (S.card : ℝ) ≤ 2 * ((R.card : ℝ) + U.card) := by exact_mod_cast hall
  have hRcap (T : Finset (Fin m)) (_ : T ⊆ R) (hT : ∀ W ⊆ T, ¬ G.IsNClique 3 W) : T.card ≤ L := by
    by_cases hzero : T.card = 0
    · simp [hzero]
    exact (Nat.le_floor_iff' hzero).mpr (triangle_free_cap_of_degree_window hfree n m G T hn hbad hT)
  have hsparse := card_le_of_sparse_triangles G R hL hD hRcap (by simpa only [hDsq] using hRtri)
  have hsparse' : (R.card : ℝ) ≤ 12 * A * X := by
    calc
      _ ≤ 6 * D * L := hsparse
      _ ≤ 6 * D * (2 * A * Y) := by gcongr; exact Nat.floor_le hApos
      _ = _ := by rw [← hDY]; ring
  have hdense := hcore n m G U hn hbad (fun x hx => ⟨
    lower_degree_window hn (Finset.card_le_card hU) (hUwin x hx).1, (hUwin x hx).2⟩)
  change (S.card : ℝ) ≤ (24 * A + 2 * B) * X
  change (U.card : ℝ) ≤ B * X at hdense
  linarith only [hall', hsparse', hdense]


private lemma tfw_mono {ε ε' A : ℝ} (hle : ε' ≤ ε) (hA : 0 ≤ A)
    (h : ∀ (n m : ℕ) (G : SimpleGraph (Fin m)) (S : Finset (Fin m)), 1 ≤ n →
      ¬ (cycleGraph 4).IsContained G → ¬ (completeGraph (Fin n)).IsContained Gᶜ →
      (∀ x ∈ S, S.card ≤ 16*n*((S.filter (G.Adj x)).card+1) ∧
        (S.filter (G.Adj x)).card ≤ 2*(n-1)) →
      (∀ B ⊆ S, ¬ G.IsNClique 3 B) →
      (S.card : ℝ) ≤ A*(n:ℝ)^(2-ε)) :
    ∀ (n m : ℕ) (G : SimpleGraph (Fin m)) (S : Finset (Fin m)),
      1 ≤ n → (¬ (cycleGraph 4).IsContained G ∧ ¬ (completeGraph (Fin n)).IsContained Gᶜ) →
      (∀ x ∈ S, S.card ≤ 16 * n * ((S.filter (G.Adj x)).card + 1) ∧
        (S.filter (G.Adj x)).card ≤ 2 * (n - 1)) →
      (∀ T ⊆ S, ¬ G.IsNClique 3 T) → (S.card : ℝ) ≤ A * (n : ℝ) ^ (2 - ε') := by
  intro n m G S hn hbad hw hf
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine (h n m G S hn hbad.1 hbad.2 hw hf).trans ?_
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hnreal (by linarith)) hA

/-- Power saving for triangle-free subsets of bad graphs inside the degree window
(identical to R1.H1). -/
def H1 : Prop :=
  ∃ ε A : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 1 ≤ A ∧
    ∀ (n m : ℕ) (G : SimpleGraph (Fin m)) (S : Finset (Fin m)), 1 ≤ n →
      ¬ (cycleGraph 4).IsContained G → ¬ (completeGraph (Fin n)).IsContained Gᶜ →
      (∀ x ∈ S, S.card ≤ 16*n*((S.filter (G.Adj x)).card+1) ∧
        (S.filter (G.Adj x)).card ≤ 2*(n-1)) →
      (∀ B ⊆ S, ¬ G.IsNClique 3 B) →
      (S.card : ℝ) ≤ A*(n:ℝ)^(2-ε)

/-- For every small `ε`, sets of large minimum degree in which every vertex lies in
more than `n ^ ε` triangles have size `O(n ^ (2 - ε / 2))`. -/
def H2 : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ B : ℝ, 0 ≤ B ∧
    ∀ (n m : ℕ) (G : SimpleGraph (Fin m)) (S : Finset (Fin m)), 1 ≤ n →
      ¬ (cycleGraph 4).IsContained G → ¬ (completeGraph (Fin n)).IsContained Gᶜ →
      (∀ x ∈ S, S.card ≤ 16*n*((S.filter (G.Adj x)).card+1) ∧
        (n:ℝ)^ε < (((S.powersetCard 3).filter (fun T => G.IsNClique 3 T ∧ x ∈ T)).card : ℝ)) →
      (S.card : ℝ) ≤ B*(n:ℝ)^(2-ε/2)

theorem main : H1 → H2 → type_of% @Erdos159.erdos_159 := by
  rintro ⟨ε₁, A, hε₁, hε₁one, hA, hfree₁⟩ ⟨ε₀, hε₀, h2⟩
  set ε := min ε₁ ε₀ with hεdef
  have hε : 0 < ε := lt_min hε₁ hε₀
  have hεone : ε ≤ 1 := (min_le_left _ _).trans hε₁one
  obtain ⟨B, hB, hcore₀⟩ := h2 ε hε (min_le_right _ _)
  have hfree := tfw_mono (min_le_left ε₁ ε₀) (by linarith) hfree₁
  have hcore : ∀ (n m : ℕ) (G : SimpleGraph (Fin m)) (S : Finset (Fin m)),
      1 ≤ n → (¬ (cycleGraph 4).IsContained G ∧ ¬ (completeGraph (Fin n)).IsContained Gᶜ) →
      (∀ x ∈ S, S.card ≤ 16 * n * ((S.filter (G.Adj x)).card + 1) ∧
        (n : ℝ) ^ ε < (((S.powersetCard 3).filter (fun B => G.IsNClique 3 B ∧ x ∈ B)).card : ℝ)) →
      (S.card : ℝ) ≤ B * (n : ℝ) ^ (2 - ε / 2) :=
    fun n m G S hn hbad hw => hcore₀ n m G S hn hbad.1 hbad.2 hw
  have hA' : 1 ≤ 2 * A := by linarith
  have hB' : 0 ≤ 24 * A + 2 * B := by linarith
  exact ⟨ε / 2, by positivity, 6 * (2 * A + 3) + (24 * A + 2 * B) + 1,
    ramsey_of_triangle_degree_bounds hε hεone hA' hB'
      (triangle_free_cap_of_degree_window hfree)
      (large_triangle_degree_cap_of_windows hε hεone hA hfree hcore)⟩

end OMA.R_Erdos159_erdos_159_R2
