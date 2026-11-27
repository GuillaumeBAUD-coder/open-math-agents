import FormalConjectures.ErdosProblems.«263»
/-! A rational reciprocal tail eventually determines all its denominators. -/
open Filter Finset Erdos263
open scoped Topology
namespace ReciprocalTails

noncomputable def X (a : ℝ) (n : ℕ) := a^(2^n)

lemma Xsucc (a : ℝ) (n : ℕ) : X a (n+1) = X a n ^2 := by simp [X,pow_succ, pow_mul]
lemma Xtop {a : ℝ} (ha : 1<a) : Tendsto (X a) atTop atTop :=
  (tendsto_pow_atTop_atTop_of_one_lt ha).comp (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1<(2:ℕ)))

lemma positive_floor {a : ℝ} (ha : 1<a) (n : ℕ) : 0 < ⌊X a n⌋₊ :=
  Nat.floor_pos.mpr (one_le_pow₀ ha.le)

lemma compare {a : ℝ} (ha : 1<a) {b : ℕ → ℕ}
    (h : Tendsto (fun n => (⌊X a n⌋₊:ℝ)/b n) atTop (𝓝 1)) :
    Tendsto (fun n => X a n/b n) atTop (𝓝 1) := by
  have hh := tendsto_nat_floor_div_atTop.comp (Xtop ha)
  have H := h.div hh (by norm_num : (1:ℝ)≠0)
  rw [div_one] at H
  apply H.congr
  intro n
  change (⌊X a n⌋₊:ℝ)/b n / ((⌊X a n⌋₊:ℝ)/X a n) = _
  have hn : (⌊X a n⌋₊:ℝ) ≠ 0 := by exact_mod_cast (positive_floor ha n).ne'
  have hX : 0<X a n := pow_pos (by linarith) _
  field_simp

noncomputable def term (b : ℕ → ℕ) (n : ℕ) : ℝ := 1/b n
noncomputable def tail (b : ℕ → ℕ) (n : ℕ) := ∑' j,term b (j+n)

lemma expansion {b : ℕ → ℕ} (hs : Summable (term b)) (n : ℕ) :
    tail b n = term b n + tail b (n+1) := by
  have H := ((summable_nat_add_iff n).mpr hs).tsum_eq_zero_add
  simpa [tail,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using H

lemma tail_info {a : ℝ} (ha : 1<a) {b : ℕ → ℕ} (hb : ∀ n, 0<b n)
    (h : Tendsto (fun n => X a n/b n) atTop (𝓝 1)) :
    Summable (term b) ∧ Tendsto (fun n => X a n*tail b n) atTop (𝓝 1) := by
  have Xpos (n) : 0<X a n := pow_pos (by linarith) _
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((h.eventually_le_const (by norm_num : (1:ℝ)<2)).and
    ((Xtop ha).eventually_ge_atTop 2))
  have estimate {n} (hn : N≤n) (j : ℕ) : term b (j+n) ≤ (2/X a n)*(1/2)^j := by
    have hh : 2^j*X a n ≤ X a (j+n) := by
      induction j with
      | zero => simp
      | succ j ih =>
        rw [Nat.succ_add,Xsucc,pow_succ]
        have hm := mul_le_mul ih (hN (j+n) (by omega)).2 (by norm_num : (0:ℝ)≤2) (Xpos _).le
        nlinarith only [hm]
    have hp := (div_le_iff₀ (by exact_mod_cast hb (j+n) : (0:ℝ)<b (j+n))).mp (hN (j+n) (by omega)).1
    dsimp [term]
    rw [div_pow,one_pow,div_mul_div_comm]
    have hh₁ := hb (j+n)
    have hh₂ := Xpos n
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [hh,hp]
  have sumge (n : ℕ) := hasSum_geometric_two.mul_left (2/X a n)
  have hs : Summable (term b) := (summable_nat_add_iff N).mp (Summable.of_nonneg_of_le
    (fun j => by dsimp [term]; positivity) (estimate le_rfl) (sumge N).summable)
  have bound {n} (hn : N≤n) : tail b n ≤ 4/X a n := by
    have H := ((summable_nat_add_iff n).mpr hs).tsum_le_tsum (estimate hn) (sumge n).summable
    rw [(sumge n).tsum_eq] at H; exact H.trans_eq (by ring)
  have rem : Tendsto (fun n => X a n * tail b (n+1)) atTop (𝓝 0) := by
    have hn (n : ℕ) : 0 ≤ tail b n := tsum_nonneg (fun j => by dsimp [term]; positivity)
    apply squeeze_zero' (g := fun n => 4/X a n) (Eventually.of_forall (fun n => mul_nonneg (Xpos n).le (hn _))) _
      (tendsto_const_nhds.div_atTop (Xtop ha))
    filter_upwards [eventually_ge_atTop N] with n hn
    have H := mul_le_mul_of_nonneg_left (bound (n := n+1) (by omega)) (Xpos n).le
    rw [Xsucc] at H
    exact H.trans_eq (by field_simp)
  refine ⟨hs,?_⟩
  have H := h.add rem
  rw [add_zero] at H
  apply H.congr
  intro n; rw [expansion hs n]; dsimp [term]; ring

lemma recovery {a : ℝ} (ha : 1<a) {b : ℕ → ℕ} (hb : ∀ n, 0<b n)
    (h : Tendsto (fun n => X a n/b n) atTop (𝓝 1)) :
    Tendsto (fun n => (b n:ℝ)-(tail b n)⁻¹) atTop (𝓝 1) := by
  obtain ⟨hs,ht⟩ := tail_info ha hb h
  have hh : Tendsto (fun n => (b n:ℝ)/X a n) atTop (𝓝 1) := by simpa using h.inv₀ (by norm_num)
  have hn := (hh.pow 2).mul (ht.comp (tendsto_add_atTop_nat 1))
  have hd := hh.mul ht
  simp only [one_pow,one_mul] at hn hd
  have H := hn.div hd (by norm_num : (1:ℝ)≠0)
  rw [div_one] at H
  apply H.congr
  intro n
  change ((b n:ℝ)/X a n)^2*(X a (n+1)*tail b (n+1)) / ((b n/X a n)*(X a n*tail b n)) = _
  have hp : 0<X a n := pow_pos (by linarith) _
  have hb' : (0:ℝ)<b n := by exact_mod_cast hb n
  have ht' : 0<tail b n := by
    rw [expansion hs]; apply add_pos_of_pos_of_nonneg (by dsimp [term]; positivity)
    exact tsum_nonneg fun j => by dsimp [term]; positivity
  rw [Xsucc]
  have he := expansion hs n
  change tail b n = 1/(b n:ℝ)+tail b (n+1) at he
  field_simp at he ⊢
  nlinarith only [congrArg (fun x : ℝ => x*(b n:ℝ)) he,he]

def valid (a : ℝ) (N : ℕ) (q : ℚ) := 1<a ∧ ∃ b : ℕ → ℕ, (∀ n,0<b n) ∧
    Tendsto (fun n => X a n/b n) atTop (𝓝 1) ∧ tail b N = q ∧
    ∀ n ≥ N, 1/2 < (b n:ℝ)-(tail b n)⁻¹ ∧ (b n:ℝ)-(tail b n)⁻¹ < 3/2

lemma code_exists {a : ℝ} (hbad : ¬(a>1 → IsWeakIrrationalitySequence (fun n => ⌊X a n⌋₊))) :
    ∃ c : ℕ × ℚ, valid a c.1 c.2 := by
  classical
  obtain ⟨ha,hnot⟩ := _root_.not_imp.mp hbad
  have hm : Monotone (fun n => ⌊X a n⌋₊) := fun i j hij => Nat.floor_mono
    (pow_le_pow_right₀ ha.le (Nat.pow_le_pow_right (by decide) hij))
  have bad : ¬∀ b : ℕ → ℕ, (∀ n,0<b n) ∧ Tendsto (fun n => (⌊X a n⌋₊:ℝ)/b n) atTop (𝓝 1) →
      Irrational (∑' n,term b n) := fun h => hnot ⟨positive_floor ha,hm,h⟩
  push_neg at bad
  obtain ⟨b,⟨hb,hb'⟩,hr⟩ := bad
  have h := compare ha hb'
  obtain ⟨q,hq⟩ : ∃ q : ℚ,(q:ℝ) = ∑' n,term b n := not_not.mp hr
  have recov := recovery ha hb h
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((recov.eventually (lt_mem_nhds (by norm_num : (1:ℝ)/2<1))).and
      (recov.eventually (gt_mem_nhds (by norm_num : (1:ℝ)<3/2))))
  refine ⟨(N,q-∑ i ∈ range N,1/(b i:ℚ)),ha,b,hb,h,?_,hN⟩
  have hs := ((tail_info ha hb h).1).sum_add_tsum_nat_add N
  change (∑ i ∈ range N,term b i)+tail b N = _ at hs
  change tail b N = ((q-∑ i ∈ range N,1/(b i:ℚ) : ℚ):ℝ)
  push_cast; rw [hq,← hs]; dsimp [term]; ring

lemma unique_base {a c : ℝ} (ha : 1<a) (hc : 1<c) {b : ℕ → ℕ} (hb : ∀ n,0<b n)
    (h : Tendsto (fun n => X a n/b n) atTop (𝓝 1))
    (h' : Tendsto (fun n => X c n/b n) atTop (𝓝 1)) : ¬a<c := by
  intro hlt
  have hz : Tendsto (fun n : ℕ => (a/c)^(2^n)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ((div_lt_one (by linarith)).mpr hlt)).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1<(2:ℕ)))
  have hh := h.div h' (by norm_num : (1:ℝ)≠0)
  rw [div_one] at hh
  have h1 : Tendsto (fun n : ℕ => (a/c)^(2^n)) atTop (𝓝 1) := by
    apply hh.congr
    intro n
    change (X a n/b n)/(X c n/b n) = _
    have hbn := hb n; dsimp only [X]; rw [div_pow]; field_simp
  exact zero_ne_one (tendsto_nhds_unique hz h1)

lemma valid_unique {a c : ℝ} {N : ℕ} {q : ℚ} (ha : valid a N q) (hc : valid c N q) : a=c := by
  obtain ⟨ha,b,hb,ht,hr,h⟩ := ha
  obtain ⟨hc,d,hd,ht',hr',h'⟩ := hc
  have next {n} (hn : N≤n) (he : tail b n = tail d n) : b n = d n := by
    obtain ⟨h₁,h₂⟩ := h n hn
    obtain ⟨h₃,h₄⟩ := h' n hn
    rw [he] at h₁ h₂
    have hbd : (b n:ℝ) < d n + 1 := by linarith
    have hdb : (d n:ℝ) < b n + 1 := by linarith
    exact Nat.le_antisymm (Nat.lt_succ_iff.mp (by exact_mod_cast hbd)) (Nat.lt_succ_iff.mp (by exact_mod_cast hdb))
  have heq (n) (hn : N≤n) : tail b n = tail d n := by
    induction n,hn using Nat.le_induction with
    | base => exact hr.trans hr'.symm
    | succ i hi ih =>
      have hi' := next hi ih
      have Hb := expansion (tail_info ha hb ht).1 i
      have Hd := expansion (tail_info hc hd ht').1 i
      dsimp only [term] at Hb Hd
      rw [hi',ih] at Hb; linarith
  have tt : Tendsto (fun n => X c n/b n) atTop (𝓝 1) := ht'.congr' (by
    filter_upwards [eventually_ge_atTop N] with n hn; rw [next hn (heq n hn)])
  exact le_antisymm (le_of_not_gt (unique_base hc ha hb tt ht)) (le_of_not_gt (unique_base ha hc hb ht tt))

end ReciprocalTails

theorem OMA.solution : type_of% @Erdos263.erdos_263.variants.doubly_exponential_all_but_countable := by
  classical
  let B := {a : ℝ | ¬(a>1 → IsWeakIrrationalitySequence (fun n => ⌊ReciprocalTails.X a n⌋₊))}
  apply mem_cocountable.mpr
  change B.Countable
  apply Set.countable_coe_iff.mp
  choose f hf using (fun a : B => ReciprocalTails.code_exists a.property)
  apply Function.Injective.countable (f := f)
  intro a c h
  exact Subtype.ext (ReciprocalTails.valid_unique (hf a) (h ▸ hf c))
