import OMAReductions.R_Green3_green_3_R1_H2_R1_H2_R1

/-! Three deadline families and the generating polynomial. Original Lean proof by @Deldor14.
The three-prefix inequality is from Franchi–Gowers–Yip, arXiv:2607.06073, Lemma 2.1. -/

open Finset

private lemma matching_of_prefix {ι : Type} [Fintype ι] (w : ι → ℕ)
    (h : ∀ n : ℕ, (univ.filter (fun z => w z<n)).card ≤ n) :
    ∃ f : ι → ℕ, Function.Injective f ∧ ∀ z, f z ≤ w z := by
  classical
  obtain ⟨f,hf,hw⟩ := (all_card_le_biUnion_card_iff_exists_injective (fun z => range (w z+1))).mp (by
    intro s
    by_cases hne : s.Nonempty
    · obtain ⟨z,hz,hmax⟩ := s.exists_max_image w hne
      have hs : s ⊆ univ.filter (fun i => w i < w z+1) := by
        intro i hi
        exact mem_filter.mpr ⟨mem_univ _,Nat.lt_succ_of_le (hmax i hi)⟩
      have hb : range (w z+1) ⊆ s.biUnion (fun i => range (w i+1)) :=
        fun _ hi => mem_biUnion.mpr ⟨z,hz,hi⟩
      have hcard := card_le_card hb
      rw [card_range] at hcard
      exact (card_le_card hs).trans ((h _).trans hcard)
    · simp [Finset.not_nonempty_iff_eq_empty.mp hne])
  exact ⟨f,hf,fun z => Nat.le_of_lt_succ (mem_range.mp (hw z))⟩

private lemma shifted_matching (T : Finset ℕ) (a : ℕ) (ha : ∀ i ∈ T, a ≤ i)
    (hcum : ∀ n : ℕ, (T.filter (·<n-a)).card + (T.filter (·<n)).card +
        (T.filter (·<n+a)).card ≤ n) :
    ∃ f : T ⊕ (T ⊕ T) → ℕ, Function.Injective f ∧
      ∀ z : T, f (.inl z) ≤ z.val+a ∧ f (.inr (.inl z)) ≤ z.val ∧ f (.inr (.inr z)) ≤ z.val-a := by
  classical
  let w : T ⊕ (T ⊕ T) → ℕ := Sum.elim (fun z => z.val+a)
      (Sum.elim (fun z => z.val) (fun z => z.val-a))
  have hp (n : ℕ) : (univ.filter (fun z => w z<n)).card ≤ n := by
    have hc (g : ℕ → Prop) [DecidablePred g] :
        (∑ z : T, if g z.val then 1 else 0) = (T.filter g).card := by
      change (∑ z ∈ T.attach, if g z.val then 1 else 0) = _
      rw [Finset.sum_attach T (fun z => if g z then 1 else 0),Finset.card_filter]
    have hswap (z : T) : z.val+a < n ↔ z.val < n-a := by omega
    have hsub (z : T) : z.val-a < n ↔ z.val < n+a := by have := ha z.val z.property; omega
    rw [Finset.card_filter]
    simp only [Fintype.sum_sum_type, w, Sum.elim_inl, Sum.elim_inr, hswap, hsub]
    change (∑ z : T, if z.val < n-a then 1 else 0) + ((∑ z : T, if z.val < n then 1 else 0) + (∑ z : T, if z.val < n+a then 1 else 0)) ≤ n
    rw [hc (fun i => i<n-a), hc (fun i => i<n), hc (fun i => i<n+a)]
    simpa [add_assoc] using hcum n
  obtain ⟨f,hf,hw⟩ := matching_of_prefix w hp
  exact ⟨f,hf,fun z => ⟨hw (.inl z),hw (.inr (.inl z)),hw (.inr (.inr z))⟩⟩

private lemma matched_sum {ι : Type} [Fintype ι] (f : ι → ℕ) (hf : Function.Injective f)
    (q : ℝ) (hq : 0<q) (hq1 : q<1) : (1-q)*(∑ z, q^(f z)) ≤ 1 := by
  classical
  let A := univ.image f
  obtain ⟨n,hn⟩ := A.exists_nat_subset_range
  have hs : (∑ z, q^(f z)) = ∑ i ∈ A, q^i := by
    dsimp [A]
    rw [sum_image (fun _ _ _ _ he => hf he)]
  have hbound : (∑ i ∈ A, q^i) ≤ ∑ i ∈ range n, q^i :=
    sum_le_sum_of_subset_of_nonneg hn (fun _ _ _ => by positivity)
  have hgeom := geom_sum_mul_neg q n
  have hqN : 0 ≤ q^n := by positivity
  rw [hs]
  nlinarith only [mul_le_mul_of_nonneg_left hbound (sub_nonneg.mpr hq1.le),hgeom,hqN]

private lemma weighted_bound (T : Finset ℕ) (a : ℕ) (ha : ∀ j ∈ T, a ≤ j)
    (q : ℝ) (hq : 0<q) (hq1 : q<1)
    (f : T ⊕ (T ⊕ T) → ℕ) (hf : Function.Injective f)
    (hw : ∀ z : T, f (.inl z) ≤ z.val+a ∧ f (.inr (.inl z)) ≤ z.val ∧
      f (.inr (.inr z)) ≤ z.val-a) :
    (1-q)*(∑ j ∈ T, q^j) ≤ 1/3 := by
  let w : T ⊕ (T ⊕ T) → ℕ := Sum.elim (fun z => z.val+a)
    (Sum.elim (fun z => z.val) (fun z => z.val-a))
  have hpoint (z) : f z ≤ w z := by
    rcases z with z | z | z
    · exact (hw z).1
    · exact (hw z).2.1
    · exact (hw z).2.2
  have hs := Finset.sum_le_sum (s:=univ) (fun z _ =>
    pow_le_pow_of_le_one hq.le hq1.le (hpoint z))
  have hsel := (mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hq1.le)).trans (matched_sum f hf q hq hq1)
  have hqa : 0 < q^a := by positivity
  have hsub (z : T) : q^(z.val-a) = q^z.val * (q^a)⁻¹ := by
    rw [← div_eq_mul_inv,eq_div_iff hqa.ne',←pow_add,Nat.sub_add_cancel (ha z.val z.property)]
  have hTs : (∑ z : T, q^z.val) = ∑ j ∈ T, q^j := Finset.sum_attach T (fun j => q^j)
  have he : (∑ z, q^(w z)) = (q^a+1+(q^a)⁻¹)*(∑ j ∈ T, q^j) := by
    simp only [Fintype.sum_sum_type,w,Sum.elim_inl,Sum.elim_inr,pow_add,hsub,←sum_mul,hTs]
    ring
  rw [he] at hsel
  have hcoef : 3 ≤ q^a+1+(q^a)⁻¹ := by
    apply (le_of_mul_le_mul_right _ hqa)
    nlinarith only [sq_nonneg (q^a-1),inv_mul_cancel₀ hqa.ne']
  have hprod : 0 ≤ (1-q)*(∑ i ∈ T, q^i) := by positivity
  nlinarith only [mul_le_mul_of_nonneg_right hcoef hprod,hsel]

theorem OMA.solution : OMA.R_Green3_green_3_R1_H2_R1_H2_R1.H3 := by
  intro T a hmin hcum q hq hq1
  obtain ⟨f,hf,hw⟩ := shifted_matching T a hmin hcum
  exact weighted_bound T a hmin q hq hq1 f hf hw
