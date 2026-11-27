import FormalConjectures.ErdosProblems.«319»

/-! Croot's short-interval theorem supplies Egyptian fractions with a left
endpoint asymptotic to N/e. Each omitted denominator costs at least 1/N
in harmonic mass, giving the near-full cardinality. Adjoining the negative
unit term turns the expansion into a minimal signed relation. The last
observation is adapted from @marcusbuffett, project PR 2025. -/

open Filter Finset
open scoped Topology
namespace OMA.R_Erdos319_erdos_319_variants_lb_R1

/-- Upper-endpoint form of Croot's short-interval Egyptian fraction theorem. -/
def H1 : Prop := ∃ (B : ℕ → ℕ) (S : ℕ → Finset ℕ),
    Tendsto (fun N => (B N : ℝ) / N) atTop (𝓝 (1/Real.exp 1)) ∧
    ∀ᶠ N in atTop, 2 ≤ B N ∧ B N ≤ N ∧ S N ⊆ Icc (B N) N ∧
      (∑ i ∈ S N, (1:ℚ)/i) = 1

/-- Finite harmonic deficit bound for every expansion of one in an interval. -/
def H2 : Prop := ∀ (B N : ℕ) (S : Finset ℕ), 2 ≤ B → B ≤ N →
    S ⊆ Icc B N → (∑ i ∈ S, (1:ℚ)/i) = 1 →
    (((Icc B N).card : ℝ) - S.card) / N ≤ Real.log ((N : ℝ) / (B-1 : ℝ)) - 1


lemma minimal_of_one {S : Finset ℕ} (hm : ∀ n ∈ S, 2≤n)
    (h : (∑ n ∈ S, (1:ℚ)/n)=1) : ∃ δ : ℕ → ℤˣ, (∑ n ∈ insert 1 S, (δ n:ℚ)/n) = 0 ∧
      ∀ B' ⊂ insert 1 S, B'.Nonempty → (∑ n ∈ B', (δ n:ℚ)/n) ≠ 0 := by
  let δ (n : ℕ) : ℤˣ := if n=1 then -1 else 1
  have hs : 1∉S := fun hn => by have := hm 1 hn; omega
  have val {n : ℕ} (hn : n≠1) : (δ n:ℚ) = 1 := by simp [δ,hn]
  have good {n : ℕ} (hn : n∈insert 1 S) (h' : n≠1) : 0 < (δ n:ℚ)/n := by
    rw [val h']; have := hm n (mem_of_mem_insert_of_ne hn h')
    positivity
  have total : (∑ n ∈ insert 1 S, (δ n:ℚ)/n) = 0 := by
    rw [sum_insert hs]
    have e : (∑ n ∈ S, (δ n:ℚ)/n) = ∑ n ∈ S, (1:ℚ)/n :=
      sum_congr rfl fun n hn => by rw [val (fun h => hs (h ▸ hn))]
    rw [e,h]; norm_num [δ]
  refine ⟨δ,total,?_⟩
  intro B hB hne
  by_cases h1 : 1∈B
  · have hpos : 0 < ∑ n ∈ (insert 1 S) \ B, (δ n:ℚ)/n := by
      apply sum_pos _ (sdiff_nonempty.mpr hB.not_ge)
      intro n hn
      obtain ⟨hx,hy⟩ := mem_sdiff.mp hn
      exact good hx (by rintro rfl; exact hy h1)
    have he := sum_sdiff hB.subset (f:=fun n => (δ n:ℚ)/n)
    rw [total] at he
    linarith
  · exact (sum_pos (fun n hn => good (hB.subset hn) (by rintro rfl; exact h1 hn)) hne).ne'

theorem main : H1 → H2 → type_of% @Erdos319.erdos_319.variants.lb := by
  rintro ⟨B, S, hB, hS⟩ hbound
  let a : ℝ := 1/Real.exp 1
  have ha : 0 < a := by dsimp [a]; positivity
  let r (N : ℕ) : ℝ := (B N : ℝ)/N - 1/N
  have hrec : Tendsto (fun N : ℕ => (1:ℝ)/N) atTop (𝓝 0) := by
    simp only [one_div]
    exact (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp tendsto_natCast_atTop_atTop
  have hr : Tendsto r atTop (𝓝 a) := by simpa [r,a] using hB.sub hrec
  have hinv := hr.inv₀ ha.ne'
  have hlog : Tendsto (fun N => Real.log ((r N)⁻¹)-1) atTop (𝓝 0) := by
    have h := (hinv.log (inv_ne_zero ha.ne')).sub (tendsto_const_nhds (x := (1:ℝ)) (f := atTop))
    simpa [a] using h
  have hupper : Tendsto (fun N => 1-r N) atTop (𝓝 (1-a)) := tendsto_const_nhds.sub hr
  have hlower : Tendsto (fun N => (1-r N) - (Real.log ((r N)⁻¹)-1)) atTop (𝓝 (1-a)) := by
    simpa using hupper.sub hlog
  have hineq : ∀ᶠ N in atTop, (1-r N) - (Real.log ((r N)⁻¹)-1) ≤ (S N).card/(N:ℝ) ∧
      (S N).card/(N:ℝ) ≤ 1-r N := by
    filter_upwards [hS] with N ⟨hb, hbn, hsub, hsum⟩
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0<N by omega)
    have eqr : r N = ((B N : ℝ)-1)/N := by dsimp [r]; ring
    have hcard : ((Icc (B N) N).card : ℝ) / N = 1-r N := by
      rw [Nat.card_Icc, Nat.cast_sub (show B N ≤ N+1 by omega), Nat.cast_add, Nat.cast_one, eqr]
      field_simp
      <;> ring
    have hle := hbound _ _ _ hb hbn hsub hsum
    have hin : (N:ℝ)/((B N:ℝ)-1) = (r N)⁻¹ := by rw [eqr, inv_div]
    rw [hin, sub_div, hcard] at hle
    refine ⟨by linarith, ?_⟩
    rw [← hcard]
    exact div_le_div_of_nonneg_right (by exact_mod_cast card_le_card hsub) hNp.le
  have hlim := tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
    (hineq.mono fun _ h => h.1) (hineq.mono fun _ h => h.2)
  refine ⟨fun N => (S N).card / (N:ℝ) - (1-a),
    (Asymptotics.isLittleO_one_iff ℝ).mpr (tendsto_sub_nhds_zero_iff.mpr hlim), ?_⟩
  filter_upwards [hS] with N ⟨h2, hbn, hsub, hsum⟩
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hleft : (1-1/Real.exp 1+((S N).card/(N:ℝ)-(1-a)))*N = (S N).card := by
    dsimp [a]; field_simp <;> ring
  rw [hleft]
  have hpos (i : ℕ) (hi : i ∈ S N) : 2 ≤ i := h2.trans (mem_Icc.mp (hsub hi)).1
  have hmin := minimal_of_one hpos hsum
  have hmem : insert 1 (S N) ⊆ Icc 1 N := by
    intro i hi
    rcases mem_insert.mp hi with rfl | hi
    · exact mem_Icc.mpr ⟨le_rfl, by omega⟩
    · exact mem_Icc.mpr ⟨by have := hpos i hi; omega, (mem_Icc.mp (hsub hi)).2⟩
  apply le_trans (show ((S N).card : ℝ) ≤ (insert 1 (S N)).card by exact_mod_cast card_le_card (subset_insert 1 (S N)))
  apply le_csSup
  · refine ⟨(N:ℝ), ?_⟩
    rintro _ ⟨A,hA,_,rfl⟩
    exact_mod_cast (card_le_card hA).trans (by simp : (Icc 1 N).card ≤ N)
  · exact ⟨insert 1 (S N), hmem, hmin, rfl⟩

end OMA.R_Erdos319_erdos_319_variants_lb_R1
