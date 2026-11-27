import FormalConjectures.ErdosProblems.«12»

/-! Refine a period so that each occupied residue class loses at least half
of its lifts: reflection about an element of the class pairs its lifts. -/
open Finset Filter Erdos12
open scoped Classical

namespace Residue12
def Live (A : Set ℕ) (q r : ℕ) := ∀ M : ℕ, ∃ a > M, a ∈ A ∧ a ≡ r [MOD q]
noncomputable def occupied (A : Set ℕ) (q : ℕ) := (range q).filter (Live A q)
lemma lower_live {A : Set ℕ} {q L x : ℕ} (h : q ∣ L) (hx : Live A L x) : Live A q (x%q) := by
  intro M
  obtain ⟨a,ha,haA,he⟩ := hx M
  exact ⟨a,ha,haA,(he.of_dvd h).trans (Nat.mod_modEq _ _).symm⟩

lemma encode {S R : Finset ℕ} (q m : ℕ) (hq : 0<q)
    (hs : ∀ x ∈ S, x%q ∈ R ∧ x < m*q) : S.card ≤ R.card*m := by
  have h : S.card ≤ (R ×ˢ range m).card := by
    apply card_le_card_of_injOn (fun x => (x%q,x/q))
    · intro x hx
      exact mem_product.mpr ⟨(hs x hx).1,mem_range.mpr ((Nat.div_lt_iff_lt_mul hq).mpr (hs x hx).2)⟩
    · intro x _ y _ he
      obtain ⟨h₁,h₂⟩ := Prod.mk.inj he
      calc
        x = _ := (Nat.mod_add_div x q).symm
        _ = y%q+q*(y/q) := by rw [h₁,h₂]
        _ = y := Nat.mod_add_div y q
  simpa using h

lemma halve {A : Set ℕ} (ha : IsGood A) (q : ℕ) (hq : 0<q) :
    ∃ m : ℕ, 0 < m ∧ 2*(occupied A (m*q)).card ≤ (occupied A q).card*m := by
  let R := occupied A q
  have choose_r (r : ℕ) : ∃ a : ℕ, r ∈ R → 0<a ∧ a∈A ∧ a ≡ r [MOD q] := by
    by_cases h : r ∈ R
    · obtain ⟨a,ha',hA',hr⟩ := (mem_filter.mp h).2 0
      exact ⟨a,fun _ => ⟨ha',hA',hr⟩⟩
    · exact ⟨1,fun h' => (h h').elim⟩
  choose a hA using choose_r
  let m := (R.sup a).factorial
  let L := m*q
  have hm : 0 < m := Nat.factorial_pos _
  have hl : 0 < L := Nat.mul_pos hm hq
  let _ : NeZero L := ⟨hl.ne'⟩
  have dq : q ∣ L := dvd_mul_left _ _
  let S := occupied A L
  have prop {x} (h : x ∈ S) : x < L ∧ Live A L x := ⟨mem_range.mp (mem_filter.mp h).1,(mem_filter.mp h).2⟩
  have down {x} (h : x ∈ S) : x%q ∈ R := mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ hq),lower_live dq (prop h).2⟩
  let mirror (x : ℕ) := ((2*(a (x%q):ZMod L) - x).val)
  have reflect (x : ℕ) : x+mirror x ≡ a (x%q)+a (x%q) [MOD L] := by
    apply (ZMod.natCast_eq_natCast_iff ..).mp
    dsimp [mirror]; push_cast; rw [ZMod.natCast_zmod_val]; ring
  have fixed {x} (hx : x ∈ S) : mirror x % q = x%q := by
    have ha' := ((hA (x%q) (down hx)).2.2).trans (Nat.mod_modEq _ _)
    exact (Nat.ModEq.add_left_cancel ha'.symm ((reflect x).of_dvd dq)).trans ha'
  have hinj : Set.InjOn mirror (↑S : Set ℕ) := by
    intro x hx y hy he
    have hxy : x%q=y%q := (fixed hx).symm.trans ((congrArg (·%q) he).trans (fixed hy))
    have hh : (2*(a (x%q):ZMod L) - x) = (2*(a (y%q):ZMod L) - y) := ZMod.val_injective L he
    rw [hxy] at hh
    have eq' := (ZMod.natCast_eq_natCast_iff x y L).mp (sub_right_inj.mp hh)
    simpa [Nat.ModEq,Nat.mod_eq_of_lt (prop hx).1,Nat.mod_eq_of_lt (prop hy).1] using eq'
  have dis : Disjoint S (S.image mirror) := by
    apply disjoint_left.mpr
    intro y hy hy'
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy'
    let t := a (x%q)
    obtain ⟨ht,htA,_⟩ := hA _ (down hx)
    have hd : t ∣ L := (Nat.dvd_factorial ht (le_sup (down hx))).trans (dvd_mul_right m q)
    obtain ⟨b,hb,hbA,hbx⟩ := (prop hx).2 t
    obtain ⟨c,hc,hcA,hcy⟩ := (prop hy).2 b
    have hsum := (hbx.add hcy).trans (reflect x)
    have hd' : t ∣ b+c := (hsum.dvd_iff hd).mpr (dvd_add dvd_rfl dvd_rfl)
    exact hc.ne' (ha.2 t htA b hbA c hcA hd' hb (hb.trans hc)).symm
  have bound := encode (S := S ∪ S.image mirror) (R:=R) q m hq (by
    intro x hx
    rcases mem_union.mp hx with h|h
    · exact ⟨down h,(prop h).1⟩
    · obtain ⟨z,hz,rfl⟩ := mem_image.mp h
      exact ⟨fixed hz ▸ down hz,ZMod.val_lt _⟩)
  rw [card_union_of_disjoint dis,card_image_of_injOn hinj] at bound
  exact ⟨m,hm,by simpa only [two_mul] using bound⟩

lemma small_period {A : Set ℕ} (ha : IsGood A) (k : ℕ) :
    ∃ q : ℕ, 0<q ∧ 2^k*(occupied A q).card ≤ q := by
  induction k with
  | zero =>
    refine ⟨1,by decide,?_⟩
    simpa [occupied] using card_filter_le (range 1) (Live A 1)
  | succ k ih =>
    obtain ⟨q,hq,hh⟩ := ih
    obtain ⟨m,hm,h⟩ := halve ha q hq
    refine ⟨m*q,Nat.mul_pos hm hq,?_⟩
    calc
      _ = 2^k*(2*(occupied A (m*q)).card) := by rw [pow_succ]; ring
      _ ≤ 2^k*((occupied A q).card*m) := Nat.mul_le_mul_left _ h
      _ ≤ m*q := by rw [← mul_assoc,Nat.mul_comm m]; exact Nat.mul_le_mul_right _ hh

lemma count_bound (A : Set ℕ) (q : ℕ) (hq : 0<q) :
    ∃ M : ℕ, ∀ n : ℕ, ((range n).filter (· ∈ A)).card ≤ M+(occupied A q).card*(n/q+1) := by
  have he : ∀ᶠ x : ℕ in atTop, ∀ r ∈ range q, x ∈ A → x ≡ r [MOD q] → Live A q r := by
    apply (eventually_all_finset _).mpr
    intro r _
    by_cases h : Live A q r
    · exact Eventually.of_forall fun _ _ _ => h
    · unfold Live at h
      push Not at h
      obtain ⟨M,hM⟩ := h
      filter_upwards [eventually_ge_atTop (M+1)] with x hx hxA hxr
      exact (hM x (by omega) hxA hxr).elim
  obtain ⟨M,hM⟩ := eventually_atTop.mp he
  refine ⟨M,fun n => ?_⟩
  let S := (range n).filter fun x => x%q ∈ occupied A q
  have hsub : (range n).filter (· ∈ A) ⊆ range M ∪ S := by
    intro x hx
    obtain ⟨hxn,hxA⟩ := mem_filter.mp hx
    by_cases hxM : x<M
    · exact mem_union_left _ (mem_range.mpr hxM)
    · exact mem_union_right _ (mem_filter.mpr ⟨hxn,mem_filter.mpr
        ⟨mem_range.mpr (Nat.mod_lt _ hq),hM x (by omega) _ (mem_range.mpr (Nat.mod_lt _ hq)) hxA (Nat.mod_modEq _ _).symm⟩⟩)
  have hS := encode (S:=S) (R:=occupied A q) q (n/q+1) hq (by
    intro x hx
    obtain ⟨hx,hr⟩ := mem_filter.mp hx
    refine ⟨hr,(mem_range.mp hx).trans ?_⟩
    exact (Nat.div_lt_iff_lt_mul hq).mp (Nat.lt_succ_self _))
  have h := (card_le_card hsub).trans (card_union_le _ _)
  rw [card_range] at h
  omega

end Residue12

open Residue12 in
theorem OMA.solution : type_of% @Erdos12.erdos_12.variants.erdos_sarkozy_density_0 := by
  intro A hA
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (2/ε) (by norm_num : (1:ℝ)<2)
  obtain ⟨q,hq,hcap⟩ := small_period hA k
  obtain ⟨M,hM⟩ := count_bound A q hq
  let R := (occupied A q).card
  have hcap' : (2:ℝ)^k * R ≤ q := by exact_mod_cast hcap
  have hR : (R:ℝ) ≤ ε/2*q := by
    have hp := (div_lt_iff₀ hε).mp hk
    nlinarith only [mul_le_mul_of_nonneg_left hcap' hε.le,
      mul_le_mul_of_nonneg_right hp.le (Nat.cast_nonneg R)]
  obtain ⟨n₀,h₀⟩ := exists_nat_gt (((M:ℝ)+R)/(ε/2))
  filter_upwards [eventually_ge_atTop n₀,eventually_ge_atTop 1] with n hn hn'
  have hn0 : 0<(n:ℝ) := by exact_mod_cast hn'
  have hq0 : 0<(q:ℝ) := by exact_mod_cast hq
  have h₁ := (div_lt_iff₀ (by positivity : 0<ε/2)).mp (h₀.trans_le (show (n₀:ℝ)≤n by exact_mod_cast hn))
  let T := (range n).filter (· ∈ A)
  have h₂ : (T.card:ℝ) ≤ M+R*((n/q:ℕ)+1) := by exact_mod_cast hM n
  have h₃ : ((n/q:ℕ):ℝ)*q ≤ n := by exact_mod_cast Nat.div_mul_le_self n q
  have h₄ : (R:ℝ)*((n/q:ℕ):ℝ) ≤ ε/2*n := calc
    _ ≤ (ε/2*q)*((n/q:ℕ):ℝ) := mul_le_mul_of_nonneg_right hR (by positivity)
    _ = ε/2*(((n/q:ℕ):ℝ)*q) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h₃ (by positivity)
  have heq : A ∩ Set.Iio n = (T:Set ℕ) := by ext x; simp [T,and_comm]
  change dist (A.partialDensity Set.univ n) 0 < ε
  simp only [Set.partialDensity,Set.inter_univ,Set.univ_inter,heq,Set.ncard_coe_finset,Nat.ncard_Iio,
    Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hn0.le)]
  apply (div_lt_iff₀ hn0).mpr
  nlinarith only [h₁,h₂,h₄]
