import FormalConjectures.GreensOpenProblems.«31»

/-!
# The Hou–Zhao upper bound for finite Sidon sets

This proves the bound of Jianfeng Hou and Hongbin Zhao (arXiv:2607.01169v3,
Theorems 1.2 and 2.1) using their exact certificate from Lemma 4.1. The energy
estimate counts pairs of translates directly. The kernel verifies the rational
certificate after clearing denominators.
-/

open Finset Filter
open scoped Topology BigOperators

namespace Green31Proof
noncomputable section

private def spread (A : Finset ℕ) (H : ℕ) (K : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ x ∈ A, ∑ s ∈ range H, if x + s = j then K s else 0

private lemma sidon_difference {A : Finset ℕ} (hA : IsSidon (A : Set ℕ))
    {a b c d : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : a ≠ b) (he : a + d = c + b) : a = c ∧ b = d := by
  rcases hA a ha c hc d hd b hb he with h | h
  · exact ⟨h.1, h.2.symm⟩
  · exact False.elim (hab h.1)

private lemma spread_energy {N H J : ℕ} {A : Finset ℕ} (hA : IsSidon (A : Set ℕ))
    (hbound : ∀ x ∈ A, x < N) (hJ : N + H - 1 ≤ J)
    (K : ℕ → ℝ) (hK : ∀ s ∈ range H, 0 ≤ K s)
    (hmass : ∑ s ∈ range H, K s = 1) :
    (∑ j ∈ range J, (spread A H K j) ^ 2) ≤
      1 + ((A.card : ℝ) - 1) * ∑ s ∈ range H, (K s) ^ 2 := by
  classical
  let count (s t : ℕ) := ((A ×ˢ A).filter fun z => z.1 + s = z.2 + t).card
  have hd (s : ℕ) : count s s = A.card := by
    apply Finset.card_bij (fun z _ => z.1)
    · intro z hz
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).1
    · intro z hz w hw e
      have hz' := (Finset.mem_filter.mp hz).2
      have hw' := (Finset.mem_filter.mp hw).2
      apply Prod.ext <;> omega
    · intro z hz
      exact ⟨(z,z), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hz,hz⟩, rfl⟩, rfl⟩
  have ho {s t : ℕ} (h : s ≠ t) : count s t ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro z hz w hw
    obtain ⟨hz', hzsum⟩ := Finset.mem_filter.mp hz
    obtain ⟨hw', hwsum⟩ := Finset.mem_filter.mp hw
    obtain ⟨hza,hzb⟩ := Finset.mem_product.mp hz'
    obtain ⟨hwa,hwb⟩ := Finset.mem_product.mp hw'
    exact Prod.ext_iff.mpr (sidon_difference hA hza hzb hwa hwb (by omega) (by omega))
  have hexpand :
      (∑ j ∈ range J, (spread A H K j) ^ 2) =
        ∑ s ∈ range H, ∑ t ∈ range H, (count s t : ℝ) * (K s * K t) := by
    simp only [spread, pow_two, Finset.sum_mul, Finset.mul_sum]
    have hchange (s t : ℕ) (hs : s ∈ range H) (ht : t ∈ range H) :
        (∑ x ∈ A, ∑ y ∈ A, ∑ j ∈ range J,
          (if x + s = j then K s else 0) * (if y + t = j then K t else 0)) =
        (count s t : ℝ) * (K s * K t) := by
      have hj (x : ℕ) (hx : x ∈ A) : x + s ∈ range J := by
        rw [Finset.mem_range] at hs ⊢
        have := hbound x hx
        omega
      calc
        _ = ∑ x ∈ A, ∑ y ∈ A, if x + s = y + t then K s * K t else 0 := by
          refine sum_congr rfl fun x hx => sum_congr rfl fun y _ => ?_
          simp only [ite_mul, zero_mul]
          rw [Finset.sum_ite_eq_of_mem (range J) _ _ (hj x hx)]
          by_cases h : x + s = y + t <;> simp [h, eq_comm]
        _ = _ := by
          rw [← Finset.sum_product', ← Finset.sum_filter]
          simp [count, nsmul_eq_mul]
    calc
      _ = ∑ s ∈ range H, ∑ t ∈ range H, ∑ x ∈ A, ∑ y ∈ A, ∑ j ∈ range J,
          (if x + s = j then K s else 0) * (if y + t = j then K t else 0) := by
        simp only [Finset.sum_comm (s := range J) (t := A),
          Finset.sum_comm (s := range J) (t := range H),
          Finset.sum_comm (s := A) (t := range H)]
        rw [Finset.sum_comm (s := range H) (t := range H)]
        refine sum_congr rfl fun s _ => sum_congr rfl fun t _ => ?_
        rw [Finset.sum_comm (s := A) (t := A)]
      _ = _ := sum_congr rfl fun s hs => sum_congr rfl fun t ht => hchange s t hs ht
  rw [hexpand]
  have hsum (s : ℕ) (hs : s ∈ range H) :
      (∑ t ∈ range H, (count s t : ℝ) * (K s * K t)) ≤
        K s + ((A.card : ℝ) - 1) * (K s)^2 := by
    calc
      _ ≤ ∑ t ∈ range H, (K s * K t +
          (if s = t then ((A.card : ℝ)-1) * (K s)^2 else 0)) := by
        refine sum_le_sum fun t ht => ?_
        split_ifs with h
        · subst t
          rw [hd]
          ring_nf
          exact le_rfl
        · have hcnt : (count s t : ℝ) ≤ 1 := by exact_mod_cast ho h
          simpa using mul_le_mul_of_nonneg_right hcnt (mul_nonneg (hK s hs) (hK t ht))
      _ = _ := by rw [sum_add_distrib, ← mul_sum, hmass, mul_one, sum_ite_eq_of_mem (range H) _ _ hs]
  calc
    _ ≤ ∑ s ∈ range H, (K s + ((A.card : ℝ) - 1) * (K s)^2) := sum_le_sum hsum
    _ = _ := by rw [sum_add_distrib, ← mul_sum, hmass]

private lemma sum_blocks {R : Type*} [AddCommMonoid R] (f : ℕ → R) {m h : ℕ} (hh : 0 < h) :
    (∑ s ∈ range (m*h), f s) = ∑ i ∈ range m, ∑ t ∈ range h, f (i*h+t) := by
  rw [← Finset.sum_product']
  apply Finset.sum_bij (fun s _ => (s/h,s%h))
  · intro s hs
    rw [Finset.mem_range] at hs
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul hh).mpr (by simpa [mul_comm] using hs)),
       Finset.mem_range.mpr (Nat.mod_lt _ hh)⟩
  · intro s hs t ht e
    have e₁ := congrArg Prod.fst e
    have e₂ := congrArg Prod.snd e
    dsimp at e₁ e₂
    calc s = h * (s/h) + s%h := (Nat.div_add_mod s h).symm
      _ = h * (t/h) + t%h := by rw [e₁,e₂]
      _ = t := Nat.div_add_mod t h
  · rintro ⟨i,t⟩ hz
    obtain ⟨hi,ht⟩ := Finset.mem_product.mp hz
    rw [Finset.mem_range] at hi ht
    have hd : (i*h+t)/h = i := by
      rw [Nat.mul_comm i h, Nat.mul_add_div hh, Nat.div_eq_of_lt ht, Nat.add_zero]
    have hm : (i*h+t)%h = t := by rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt ht]
    refine ⟨i*h+t, Finset.mem_range.mpr ?_, Prod.ext hd hm⟩
    rw [← Nat.div_lt_iff_lt_mul hh]
    simpa [hd]
  · intro s hs
    congr 1
    simpa [mul_comm] using (Nat.div_add_mod s h).symm

private lemma stretch_div {i t h : ℕ} (hh : 0 < h) (ht : t < h) :
    (i*h+t)/h = i := by
  rw [Nat.mul_comm i h, Nat.mul_add_div hh, Nat.div_eq_of_lt ht, Nat.add_zero]

private lemma sum_step (f : ℕ → ℝ) {m h : ℕ} (hh : 0 < h) :
    (∑ s ∈ range (m*h), f (s/h)) = (h : ℝ) * ∑ i ∈ range m, f i := by
  rw [sum_blocks _ hh, Finset.mul_sum]
  refine sum_congr rfl fun i hi => ?_
  calc
    (∑ t ∈ range h, f ((i*h+t)/h)) = ∑ _t ∈ range h, f i := by
      exact sum_congr rfl fun t ht => congrArg f (stretch_div hh (Finset.mem_range.mp ht))
    _ = _ := by simp [nsmul_eq_mul]

private lemma interpolate (p w : ℕ → ℝ) {m h x : ℕ} (hh : 0 < h) :
    (∑ s ∈ range (m*h), (p (s/h) / h) * w ((x+s)/h)) =
      (1-((x%h : ℕ) : ℝ)/h) * (∑ i ∈ range m, p i * w (x/h+i)) +
      (((x%h : ℕ) : ℝ)/h) * (∑ i ∈ range m, p i * w (x/h+i+1)) := by
  have ht : x%h < h := Nat.mod_lt x hh
  have hhnz : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  rw [sum_blocks _ hh, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine sum_congr rfl fun i hi => ?_
  rw [← Finset.sum_range_add_sum_Ico _ (show h - x%h ≤ h from Nat.sub_le ..)]
  have hd (t : ℕ) (ht' : t < h) :
      (x+(i*h+t))/h = x/h+i+(x%h+t)/h := by
    have heq : x+(i*h+t) = h*(x/h+i)+(x%h+t) := by
      linear_combination (Nat.div_add_mod x h).symm
    rw [heq, Nat.mul_add_div hh]
  have hsmall : (∑ t ∈ range (h-x%h), (p ((i*h+t)/h) / ↑h) * w ((x+(i*h+t))/h)) =
      (h-x%h : ℕ) * ((p i / ↑h) * w (x/h+i)) := by
    conv_rhs => rw [← Finset.card_range (n := h-x%h), ← nsmul_eq_mul, ← Finset.sum_const]
    refine sum_congr rfl fun t htm => ?_
    have ht' := Finset.mem_range.mp htm
    rw [stretch_div hh (by omega : t < h), hd t (by omega),
      Nat.div_eq_of_lt (show x%h+t < h by omega), Nat.add_zero]
  have hlarge : (∑ t ∈ Ico (h-x%h) h, (p ((i*h+t)/h) / ↑h) * w ((x+(i*h+t))/h)) =
      ((x%h : ℕ) : ℝ) * ((p i / ↑h) * w (x/h+i+1)) := by
    have hlen : #(Ico (h-x%h) h) = x%h := by simp [Nat.card_Ico, Nat.sub_sub_self ht.le]
    conv_rhs => rw [← hlen, ← nsmul_eq_mul, ← Finset.sum_const]
    refine sum_congr rfl fun t htm => ?_
    obtain ⟨htlo,hthi⟩ := Finset.mem_Ico.mp htm
    have hdiv : (x%h+t)/h = 1 := by
      apply le_antisymm
      · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hh).mpr (by omega))
      · exact (Nat.le_div_iff_mul_le hh).mpr (by omega)
    rw [stretch_div hh hthi, hd t hthi, hdiv]
  rw [hsmall,hlarge, Nat.cast_sub ht.le]
  field_simp

private def boundaryProfile (w : ℕ → ℝ) (h J j : ℕ) : ℝ :=
  w (j/h) + w ((J-1-j)/h) - 1

private lemma reflect_block {m h s : ℕ} (hh : 0 < h) (hs : s < m*h) :
    (m*h-1-s)/h = m-1-s/h := by
  have hsdiv : s / h < m := (Nat.div_lt_iff_lt_mul hh).mpr (by simpa [mul_comm] using hs)
  have hsmod := Nat.mod_lt s hh
  have h1 : s + ((m-1-s/h)*h+(h-1-s%h)) = m*h-1 := by
    have hm : (m-1-s/h) + (s/h) + 1 = m := by omega
    have ht : (h-1-s%h) + s%h + 1 = h := by omega
    have hsrep : s = h*(s/h)+s%h := (Nat.div_add_mod s h).symm
    have hm' := congrArg (· * h) hm
    rw [Nat.mul_comm h (s/h)] at hsrep
    rw [Nat.add_mul, Nat.add_mul, one_mul] at hm'
    omega
  rw [show m*h-1-s = (m-1-s/h)*h+(h-1-s%h) by omega]
  exact stretch_div hh (by omega)

private lemma boundary_norm (w : ℕ → ℝ) {L m h J : ℕ} (hh : 0 < h)
    (hJ : 2 * ((L*m)*h) ≤ J) (hw : ∀ j, L*m ≤ j → w j = 1) :
    (∑ j ∈ range J, boundaryProfile w h J j ^ 2) =
      (J : ℝ) + 2*(h : ℝ)*((∑ i ∈ range (L*m), w i ^ 2) - (L*m : ℕ)) := by
  let B := (L*m)*h
  have hb (j : ℕ) (hj : B ≤ j) : w (j/h) = 1 := by
    apply hw
    exact (Nat.le_div_iff_mul_le hh).mpr (by simpa [B,mul_comm] using hj)
  have hpoint (j : ℕ) (hj : j ∈ range J) :
      boundaryProfile w h J j ^ 2 = w (j/h)^2 + w ((J-1-j)/h)^2 - 1 := by
    unfold boundaryProfile
    by_cases h : B ≤ j
    · rw [hb j h]
      ring
    · have hj' := Finset.mem_range.mp hj
      rw [hb (J-1-j) (by omega)]
      ring
  have hsum : (∑ j ∈ range J, w (j/h)^2) =
      (h : ℝ) * (∑ i ∈ range (L*m), w i^2) + ((J-B : ℕ) : ℝ) := by
    rw [← Finset.sum_range_add_sum_Ico _ (show B ≤ J by omega), sum_step (fun i => w i ^ 2) hh]
    congr 1
    calc
      (∑ j ∈ Ico B J, w (j/h)^2) = ∑ _j ∈ Ico B J, (1 : ℝ) := by
        refine sum_congr rfl fun j hj => ?_
        rw [hb j (Finset.mem_Ico.mp hj).1, one_pow]
      _ = _ := by simp [Nat.card_Ico]
  rw [sum_congr rfl hpoint, sum_sub_distrib, sum_add_distrib,
    sum_range_reflect (fun j => w (j/h)^2) J, hsum]
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one, Nat.cast_sub (show B ≤ J by omega)]
  dsimp [B]
  push_cast
  ring

private lemma weighted_cover {ι : Type*} [Fintype ι] (mix : ι → ℝ)
    (p w : ι → ℕ → ℝ) {L m h N x : ℕ} (hh : 0 < h) (hm : 0 < m) (hx : x < N)
    (hN : 2 * ((L*m)*h) ≤ N)
    (hmix : ∑ r, mix r = 1) (hmass : ∀ r, ∑ i ∈ range m, p r i = 1)
    (hpsym : ∀ r i, i < m → p r (m-1-i) = p r i)
    (hw : ∀ r j, L*m ≤ j → w r j = 1)
    (hcover : ∀ q, q ≤ L*m →
      1 ≤ ∑ r, mix r * ∑ i ∈ range m, p r i * w r (q+i)) :
    1 ≤ ∑ r, mix r * ∑ s ∈ range (m*h), (p r (s/h)/h) *
      boundaryProfile (w r) h (N + m*h - 1) (x+s) := by
  let B := (L*m)*h
  let H := m*h
  let J := N+H-1
  have hp (q : ℕ) : 1 ≤ ∑ r, mix r * ∑ i ∈ range m, p r i * w r (q+i) := by
    by_cases hq : q ≤ L*m
    · exact hcover q hq
    · have he (r : ι) :
          (∑ i ∈ range m, p r i * w r (q+i)) = ∑ i ∈ range m, p r i := by
        exact sum_congr rfl fun i _ => by rw [hw r _ (by omega), mul_one]
      simp_rw [he, hmass, mul_one, hmix, le_rfl]
  have hLeft (x : ℕ) :
      1 ≤ ∑ r, mix r * ∑ s ∈ range H, (p r (s/h)/h) * w r ((x+s)/h) := by
    let z : ℝ := ((x % h : ℕ) : ℝ) / (h : ℝ)
    have hz : 0 ≤ z := by dsimp [z]; positivity
    have hz' : z ≤ 1 := by
      dsimp [z]
      rw [div_le_one (by exact_mod_cast hh)]
      exact_mod_cast (Nat.mod_lt x hh).le
    have hinter (r : ι) := interpolate (p r) (w r) (m := m) (x := x) hh
    have h' (r : ι) :
        (∑ s ∈ range H, (p r (s/h)/h) * w r ((x+s)/h)) =
        (1-z)*(∑ i ∈ range m, p r i * w r (x/h+i)) +
        z*(∑ i ∈ range m, p r i * w r (x/h+1+i)) := by
      simpa [H,z,add_assoc,add_comm,add_left_comm] using hinter r
    simp_rw [h', mul_add, mul_left_comm (mix _) (1-z), mul_left_comm (mix _) z, sum_add_distrib, ← mul_sum]
    have ha := mul_le_mul_of_nonneg_left (hp (x/h)) (sub_nonneg.mpr hz')
    have hb := mul_le_mul_of_nonneg_left (hp (x/h+1)) hz
    linarith
  have hbound (r : ι) (j : ℕ) (hj : B ≤ j) : w r (j/h) = 1 := by
    apply hw
    exact (Nat.le_div_iff_mul_le hh).mpr (by simpa [B,mul_comm] using hj)
  have hH : 0 < H := Nat.mul_pos hm hh
  change 1 ≤ ∑ r, mix r * ∑ s ∈ range H, (p r (s/h)/h) * boundaryProfile (w r) h J (x+s)
  by_cases hxB : x < B
  · have he (r : ι) (s : ℕ) (hs : s ∈ range H) :
        boundaryProfile (w r) h J (x+s) = w r ((x+s)/h) := by
      have hs' := Finset.mem_range.mp hs
      unfold boundaryProfile
      rw [hbound r (J-1-(x+s)) (by dsimp only [J]; omega), add_sub_cancel_right]
    convert hLeft x using 1
    refine sum_congr rfl fun r _ => congrArg (mix r * ·) (sum_congr rfl fun s hs => ?_)
    rw [he r s hs]
  · have he (r : ι) :
        (∑ s ∈ range H, (p r (s/h)/h) * boundaryProfile (w r) h J (x+s)) =
        ∑ s ∈ range H, (p r (s/h)/h) * w r (((N-1-x)+s)/h) := by
      rw [← sum_range_reflect (fun s => (p r (s/h)/h) *
        boundaryProfile (w r) h J (x+s)) H]
      refine sum_congr rfl fun s hs => ?_
      have hs' := Finset.mem_range.mp hs
      have hr := reflect_block (m := m) hh (show s < m*h from hs')
      have hi : s / h < m := (Nat.div_lt_iff_lt_mul hh).mpr (by simpa [H,mul_comm] using hs')
      unfold boundaryProfile
      rw [show (H-1-s)/h = m-1-s/h from hr, hpsym r _ hi]
      rw [hbound r (x+(H-1-s)) (by omega), add_comm (1 : ℝ), add_sub_cancel_right]
      have e : J-1-(x+(H-1-s)) = (N-1-x)+s := by dsimp [J]; omega
      rw [e]
    simpa only [he] using hLeft (N-1-x)

private def energyCoeff {ι : Type*} [Fintype ι] (mix : ι → ℝ) (p : ι → ℕ → ℝ)
    (m : ℕ) : ℝ :=
  m * ∑ r, mix r * ∑ i ∈ range m, (p r i)^2

private def normCoeff {ι : Type*} [Fintype ι] (mix : ι → ℝ) (w : ι → ℕ → ℝ)
    (L m : ℕ) : ℝ :=
  1 + 2 / m * ((∑ r, mix r * ∑ i ∈ range (L*m), (w r i)^2) - (L*m : ℕ))

private lemma smoothing_inequality {ι : Type*} [Fintype ι] (mix : ι → ℝ)
    (p w : ι → ℕ → ℝ) {L m h N : ℕ} (hm : 0 < m) (hh : 0 < h)
    (hN : 2 * ((L*m)*h) ≤ N)
    (hmix : ∑ r, mix r = 1) (hmixpos : ∀ r, 0 ≤ mix r)
    (hmass : ∀ r, ∑ i ∈ range m, p r i = 1) (hppos : ∀ r i, 0 ≤ p r i)
    (hpsym : ∀ r i, i < m → p r (m-1-i) = p r i)
    (hw : ∀ r j, L*m ≤ j → w r j = 1)
    (hcover : ∀ q, q ≤ L*m →
      1 ≤ ∑ r, mix r * ∑ i ∈ range m, p r i * w r (q+i))
    (A : Finset ℕ) (hA : IsSidon (A : Set ℕ)) (hA_range : ∀ x ∈ A, x < N) :
    (A.card : ℝ)^2 ≤
      ((N : ℝ) + normCoeff mix w L m * ((m*h : ℕ) : ℝ)) *
        (1 + energyCoeff mix p m * (A.card : ℝ) / ((m*h : ℕ) : ℝ)) := by
  classical
  let H := m*h
  let J := N+H-1
  let K (r : ι) (s : ℕ) : ℝ := p r (s/h)/h
  let Q (r : ι) := boundaryProfile (w r) h J
  let U (r : ι) := spread A H (K r)
  let s : Finset (ι × ℕ) := univ ×ˢ range J
  have hH : 0 < H := Nat.mul_pos hm hh
  have hhr : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hK0 (r : ι) (j : ℕ) : 0 ≤ K r j := div_nonneg (hppos r _) (Nat.cast_nonneg _)
  have hKsum (r : ι) : (∑ j ∈ range H, K r j) = 1 := by
    simp only [H,K, ← Finset.sum_div, sum_step _ hh, hmass, mul_one, div_self hhr]
  have hKsq (r : ι) : (∑ j ∈ range H, (K r j)^2) = (∑ i ∈ range m, (p r i)^2) / h := by
    simp only [H,K, div_pow, ← Finset.sum_div, sum_step (fun i => (p r i)^2) hh]
    field_simp
  have hQsq (r : ι) := boundary_norm (w r) (L := L) (m := m) (J := J) hh
    (by dsimp [J]; omega) (hw r)
  have hu (r : ι) := spread_energy hA hA_range (show N+H-1 ≤ J by rfl) (K r)
    (fun j _ => hK0 r j) (hKsum r)
  have hQbound : (∑ v ∈ s, mix v.1 * (Q v.1 v.2)^2) ≤
      (N : ℝ) + normCoeff mix w L m * (H : ℝ) := by
    simp only [s, Finset.sum_product, ← Finset.mul_sum, Q, hQsq]
    have hcast : (J : ℝ) = (N : ℝ)+(H : ℝ)-1 := by
      dsimp [J]
      push_cast [Nat.cast_sub (by omega : 1 ≤ N + H)]
      rfl
    rw [show (∑ r, mix r * ((J : ℝ) + 2 * ↑h * ((∑ i ∈ range (L*m), (w r i)^2) - ↑(L*m)))) =
        (J : ℝ) + 2*(h : ℝ)*((∑ r, mix r * ∑ i ∈ range (L*m), (w r i)^2) - (L*m : ℕ)) by
      simp_rw [mul_add, mul_sub, mul_comm (mix _) (J : ℝ),
        mul_left_comm (mix _) (2 * (h : ℝ)), mul_comm (mix _) ((L*m : ℕ) : ℝ),
        sum_add_distrib, sum_sub_distrib, ← mul_sum, hmix, mul_one]]
    rw [show normCoeff mix w L m * (H : ℝ) = (H : ℝ) +
        2*(h : ℝ)*((∑ r, mix r * ∑ i ∈ range (L*m), (w r i)^2) - (L*m : ℕ)) by
      unfold normCoeff
      dsimp [H]
      push_cast
      field_simp]
    linarith only [hcast]
  have hUbound : (∑ v ∈ s, mix v.1 * (U v.1 v.2)^2) ≤
      1 + energyCoeff mix p m * (A.card : ℝ) / (H : ℝ) := by
    simp only [s, Finset.sum_product, ← Finset.mul_sum]
    calc
      _ ≤ ∑ r, mix r * (1 + (A.card - 1 : ℝ) * ∑ j ∈ range H, (K r j)^2) := by
        refine sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (hu r) (hmixpos r)
      _ ≤ ∑ r, mix r * (1 + (A.card : ℝ) * ((∑ i ∈ range m, (p r i)^2) / h)) := by
        simp_rw [hKsq]
        refine sum_le_sum fun r _ => mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (mul_le_mul_of_nonneg_right (show (A.card : ℝ) - 1 ≤ A.card by linarith) ?_)) (hmixpos r)
        exact div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)
      _ = 1 + (A.card / (h : ℝ)) * ∑ r, mix r * ∑ i ∈ range m, (p r i)^2 := by
        have he (r : ι) : mix r * (1 + A.card * ((∑ i ∈ range m, (p r i)^2) / h)) =
            mix r + (A.card / (h : ℝ)) * (mix r * ∑ i ∈ range m, (p r i)^2) := by ring
        simp_rw [he, sum_add_distrib, ← mul_sum, hmix]
      _ = _ := by
        unfold energyCoeff
        dsimp [H]
        push_cast
        field_simp
  have hcoverSum : (A.card : ℝ) ≤ ∑ v ∈ s, mix v.1 * U v.1 v.2 * Q v.1 v.2 := by
    have hs (r : ι) :
        (∑ j ∈ range J, U r j * Q r j) =
          ∑ x ∈ A, ∑ t ∈ range H, K r t * Q r (x+t) := by
      simp only [U, spread, sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      refine sum_congr rfl fun x hx => ?_
      rw [Finset.sum_comm]
      refine sum_congr rfl fun t ht => ?_
      rw [Finset.sum_ite_eq_of_mem (range J) _ _ (by
        have := hA_range x hx
        have := Finset.mem_range.mp ht
        dsimp [J]
        simp only [Finset.mem_range]
        omega)]
    simp only [s, Finset.sum_product, mul_assoc, ← Finset.mul_sum, hs]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ _x ∈ A, (1 : ℝ) := by simp
      _ ≤ _ := by
        refine sum_le_sum fun x hx => ?_
        simpa only [← Finset.mul_sum] using weighted_cover mix p w hh hm (hA_range x hx) hN hmix hmass hpsym hw hcover
  have hC := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (r := fun v => mix v.1 * U v.1 v.2 * Q v.1 v.2)
    (f := fun v => mix v.1 * (Q v.1 v.2)^2)
    (g := fun v => mix v.1 * (U v.1 v.2)^2)
    (fun v _ => mul_nonneg (hmixpos _) (sq_nonneg _))
    (fun v _ => mul_nonneg (hmixpos _) (sq_nonneg _))
    (fun _ _ => by ring_nf; exact le_rfl)
  have hQnonneg : 0 ≤ ∑ v ∈ s, mix v.1 * (Q v.1 v.2)^2 :=
    sum_nonneg fun v _ => mul_nonneg (hmixpos _) (sq_nonneg _)
  have hUnonneg : 0 ≤ ∑ v ∈ s, mix v.1 * (U v.1 v.2)^2 :=
    sum_nonneg fun v _ => mul_nonneg (hmixpos _) (sq_nonneg _)
  refine (pow_le_pow_left₀ (Nat.cast_nonneg _) hcoverSum 2).trans (hC.trans ?_)
  exact mul_le_mul hQbound hUbound hUnonneg (hQnonneg.trans hQbound)

private lemma large_scale {a b lo hi beta : ℝ} {L m : ℕ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hlo : 0 < lo) (hhi : lo < hi)
    (hbeta : 0 ≤ beta) (hgap : 0 < 2*beta - b*hi - a/lo)
    (hm : 0 < m) :
    ∀ᶠ N : ℕ in atTop, ∃ h : ℕ, 0 < h ∧ 2 * ((L*m)*h) ≤ N ∧
      ∀ k : ℝ, 0 ≤ k →
        k^2 ≤ ((N : ℝ) + b * ((m*h : ℕ) : ℝ)) * (1 + a*k / ((m*h : ℕ) : ℝ)) →
        k ≤ Real.sqrt N + beta * (N : ℝ) ^ (4⁻¹ : ℝ) := by
  let X (N : ℕ) : ℝ := Real.sqrt (Real.sqrt N)
  let c := a/lo
  let d := b*hi*c
  let e := 2*beta-b*hi-c
  have hc : 0 ≤ c := div_nonneg ha hlo.le
  have hhip : 0 < hi := hlo.trans hhi
  have hd : 0 ≤ d := mul_nonneg (mul_nonneg hb hhip.le) hc
  have he : 0 < e := by dsimp [e,c]; linarith
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hxlim : Tendsto X atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hxlim.eventually_ge_atTop (1 : ℝ),
    hxlim.eventually_ge_atTop ((m : ℝ)/(hi-lo)), hxlim.eventually_ge_atTop (2*(L : ℝ)*hi),
    hxlim.eventually_ge_atTop (c+d), hxlim.eventually_ge_atTop ((c*beta+d+d*beta)/e)]
    with N hx1 hxfloor hxcap hxslope hxgap
  let x := X N
  change 1 ≤ x at hx1
  have hxp : 0 < x := by linarith
  have hxSq : x^2 = Real.sqrt N := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hx4 : x^4 = (N : ℝ) := by rw [show x^4 = (x^2)^2 by ring, hxSq, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hxpow : (N : ℝ) ^ (4⁻¹ : ℝ) = x := by
    dsimp [x,X]
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg N)]
    norm_num
  let h := ⌊hi*x^3/m⌋₊
  let H : ℝ := ((m*h : ℕ) : ℝ)
  have hx3 : x ≤ x^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (show 0 ≤ x*x+x by positivity)]
  have hf := Nat.lt_floor_add_one (hi*x^3/m)
  have hupper : H ≤ hi*x^3 := by
    have hh := Nat.floor_le (show 0 ≤ hi*x^3/m by positivity)
    dsimp [H,h]
    push_cast
    nlinarith only [(le_div_iff₀ hmr).mp hh]
  have hlower : lo*x^3 ≤ H := by
    have he' : (m : ℝ) ≤ (hi-lo)*x^3 := by
      have h₁ := (div_le_iff₀ (sub_pos.mpr hhi)).mp hxfloor
      exact h₁.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hx3 (sub_nonneg.mpr hhi.le))
    have hf' := (div_lt_iff₀ hmr).mp hf

    change hi*x^3 < ((h : ℝ)+1)*m at hf'
    dsimp [H]
    push_cast
    nlinarith only [he',hf']
  have hH : 0 < H := (mul_pos hlo (pow_pos hxp _)).trans_le hlower
  have hh : 0 < h := by
    by_contra! hn
    have h0 : h = 0 := by omega
    simp [H,h0] at hH
  refine ⟨h, hh, ?_, ?_⟩
  · rw [mul_assoc L m h]
    have h₁ := mul_le_mul_of_nonneg_left hupper (show 0 ≤ (2 : ℝ)*L by positivity)
    have h₂ := mul_le_mul_of_nonneg_right (show 2*(L : ℝ)*hi ≤ x from hxcap) (pow_nonneg hxp.le 3)
    have h₃ : (2 : ℝ)*((L : ℝ)*H) ≤ (N : ℝ) := by nlinarith only [h₁,h₂,hx4]
    dsimp [H] at h₃
    exact_mod_cast h₃
  · intro k hk hineq
    change k^2 ≤ ((N : ℝ)+b*H)*(1+a*k/H) at hineq
    have hcoef : a*k/H ≤ c*k/x^3 := by
      rw [show c*k/x^3 = a*k/(lo*x^3) by dsimp [c]; field_simp]
      exact div_le_div_of_nonneg_left (mul_nonneg ha hk) (mul_pos hlo (pow_pos hxp _)) hlower
    have hg : (N : ℝ)+b*H ≤ x^4+b*hi*x^3 := by
      rw [hx4]
      simpa [mul_assoc] using add_le_add_left (mul_le_mul_of_nonneg_left hupper hb) (N : ℝ)
    have hprod := mul_le_mul hg (add_le_add (le_refl (1 : ℝ)) hcoef)
      (by positivity : 0 ≤ 1+a*k/H) (by positivity : 0 ≤ x^4+b*hi*x^3)
    have hpoly : k^2 ≤ x^4+b*hi*x^3+(c*x+d)*k := by
      refine hineq.trans (hprod.trans_eq ?_)
      dsimp [d]
      field_simp
    rw [← hxSq, hxpow]
    by_contra! hkgt
    let T := x^2+beta*x
    have hkT : T ≤ k := hkgt.le
    have hT : c*x+d ≤ T := by
      have h₁ : c+d ≤ x := hxslope
      have h₂ := mul_le_mul_of_nonneg_right h₁ hxp.le
      have h₃ := mul_le_mul_of_nonneg_right hx1 hd
      have h₄ := mul_nonneg hbeta hxp.le
      dsimp [T]
      nlinarith only [h₂,h₃,h₄]
    have hcompare := mul_nonneg (sub_nonneg.mpr hkT)
      (show 0 ≤ k+T-(c*x+d) by linarith)
    have hfirst := (div_le_iff₀ he).mp hxgap
    have hsecond := mul_le_mul_of_nonneg_right hfirst (sq_nonneg x)
    have hthird := mul_le_mul_of_nonneg_left hx1 (show 0 ≤ d*beta*x by positivity)
    have hbeta' : 0 ≤ beta^2*x^2 := by positivity
    dsimp [T] at hcompare
    dsimp [e] at hsecond
    have hstrict := mul_pos (sub_pos.mpr hkgt) (show 0 < k+T-(c*x+d) by
      have : 0 < k := by nlinarith [mul_nonneg hbeta hxp.le]
      linarith)
    dsimp [T] at hstrict
    nlinarith only [hpoly,hsecond,hthird,hbeta',hstrict]

/- The certificate uses eight kernels of length 32 and boundary profiles of
length 128. Kernel numerators are packed into 37-bit digits, and boundary
numerators into 32-bit digits in blocks of 16. Digit zero is the least
significant digit. The boundary correction adds 17 to the numerator after
multiplying the packed entry by 250. -/
private def mixingNumbers : Array ℕ :=
  #[39490874, 8624912, 135342, 12911860, 20451562, 2832639, 9217142, 6335669]
private def kernelHalfPacked : Array ℕ :=
  #[0xc376f2720b4b33d0d89a1bd51fd894ec5add74a3045d429c180b7810e0eca30e65683cbe642ba38952510a316434888d1d2c8c31f800cca1b13e248f07f01efd885f1720acc25bc4dd28,
    0x3a35294401d1a94a200e8d4a5100746a528803a35294401d1a94a200e8d4a5100746a528803a35294401d1a94a200e8d4a5100746a528803a35294401d1a94a200e8d4a5100746a52880,
    0x3b3548ead93c440848ce36917d6e7c9e8f1245994c0a0929f27e921d5f3d02a1881019b0753ff52b9299abd9fe7390784cfd10707cb9bd33d5f13abd8f0bea3668893f760862c955e1b9,
    0x468264b00228759b73106edb6dba7d1538e053f46a0461a2a0692aad2ed6a620895cf244a344970146a21c0204451340459646a652a4589390d2b1990a146e3b68141c7adb003afe62c5,
    0x33d24d377987d0636a0c6691bd2a75455565a4a36dc4a3a987baf5692a2e2934a772ec01463415053631b8c0727d901bc8ba2e8b597caf63f3aa3ad9194c973b24a18459d1846c45e11e,
    0x386f234499ed5a464cd0fe190ace8c1cfd98243c41537720e49530790cf266d5c8d1c85d3247166d5da2127831d54ea968d92e670293c5e2dbebbc7314567c89d0911aec2ce4334b07a6,
    0x363aaf9ef9ccfce1ca4f801d2246804a6be8f3f2339a6b9e8d412be4f19e82e2c7ab385c973e454b0629ea63c1cd8e957e58266df1910a534c129f4d1a0f60a3f0d217bf28e6a1a3c439,
    0x35f2d99421a45c93974d8ddc90467dd5784e74d9a8f3b4ac3a3feb59539042a248f94c3b3d3d9a39d851dafeb22f8f91badc627c854c53e34f421bf213354d00506b592a25c2a77a072a]
private def boundaryPacked : Array (Array ℕ) :=
  #[#[0x7a0f55ac453482d4437af38b30c9bf352fac295a244fe22723c7e7d31b8c9cd81b01c2a91486c8b0149b94520f5f91ea0fcad5aa090165e10d5d22650a9b478e,
      0x37edd6ab3aceeea135b399503a111b9f36d84483395dff2f37af03363bf3ce583a608c2f3e1561d93c6d0344441f8ae34499c0134fe8f5ae4d345ff47b5bad15,
      0x423da5633e2e7d4d3ff6bb3a3f8308a33ea1f47f3d80f0243d24e2503b6b640e3a25ab5939291f8838f14cb236f6428835b0de3332e3a7ed34d7ae9533547246,
      0x3a72965b3a9f26ea3aea5ceb3a88020a3a746bf53a8009703a7378b63a9064cd3a91293b3abb5b1d3ab632d53b4b14dc3bac3e6f3cb346eb3cb9d2ea40eb76e2,
      0x3c01d6723bd90bef3c1ce83a3c34346e3c346d803c3433213c468e063c2961ae3bfa1e7d3bf366cf3be8e52e3baf13d73b608b303aff0c043b1250e93b3273e0,
      0x3b8564bc3b846d3c3b9b58003b7714193b7202403b73e8bd3b6b01273b5d19493b5c2d673b6059ef3b5371dc3b56c9d43b5e97f53b79a72f3b80fb213bd53b07,
      0x3b8f888e3b97c5ab3b9e9ed73b9dccb03baa51903bab40c83bb0fa543bb319293bb460923bb695303bb7860d3bb6686b3bafc4da3ba4f8083ba41ecd3bb01f23,
      0x3b9beb413b9dde9d3b9f97313b9a5b003b9a34d83b986a693b97a6933b9345163b923da63b9139623b8d54f53b8af6823b89bf883b8ac5673b8c52e33b8f8657],
    #[0x30ef02f030ef02f02e899dda2da485fd2b6747c82af827462957ad4a28b5d83b267114f125f01893248f9151247ba28b226abdfd20f8810720b8b79e20b8b79e,
      0x4ed67d934daa5da54b53aad7495f41534680d192454be1bb4271088740fbad143e9219823dc422543b0b215d39c167f33733cd1036cf3a00352eabe43277b447,
      0x3b6da9113afa19393a7447ae3a35ab873a091069397357de3882972a3833f29337fbf50837817ea23666a34635aa9e9b3551de3635d0662133a29cf832f2efe8,
      0x3c01a6403c2dfaa93bc437ff3ca814cf3ccec0793cea512b3d0d13983d5dff1d3d17cdf13cd8ad483cd5eaec3d0059523cd649653c38b2b13b51331f3cb160ef,
      0x3c0d297f3b8bc1943bb81ddb3bd009e93b9207f13b8c5d4b3b6d5eaa3b573e7d3b2f223a3b200a123af015043ac1684c3a88c61d3a7ba6033a41b75439f05c51,
      0x3b7be7be3b7769583b80ca323b8dae0a3b945d0b3ba166ae3ba98be33bc2a0ee3bc14f2d3bc2383e3bccd23a3bdf9ba43be3d7ba3bdaa8873bb634ec3bf95337,
      0x3ba5e5713b9cd5d13ba59a923bab59b83ba19afd3ba3a2763ba2b67e3ba04d3f3b9620143b96d96c3b9226573b893eb53b7d48fa3b75cc363b6ebee83b67db3d,
      0x3b9974213b97fc7a3b96a7a63b985e093b98e3613b99c1883b9d06bc3b9e237f3ba02a5b3b9f0def3ba38bf33ba3ac373ba4b14f3ba186f43ba437813ba37ef4],
    #[0x3292c2542552c2fb2e6337bd2e978b7f3c915604370b1d0b38ab948e2a151db428db4c6c2178c04d274ae0072163d76423336746110326ca1349de040c88060a,
      0x3beaa4ab40f4fe8a3d09dfd84bb5149c46dfe14c49860dce416ccd4f445327cf4364d9364cab3031495ddc5e49a7786d3a2b59ca345177602a95aa503211f252,
      0x3c5cd01e39fa1aea3b32cd1e3a96c2023b4f53d03a76416f3a88d26e39490dac395157623845b2033868298936c66af03677c36034689095342c487432b31603,
      0x3aa98ec13b07c75b3ad6e3b93bf673433c13ad423c23f8f23c49db853ca467bf3cffedfb3d998c253dd72cb93dfbb51d3d500d6d3cb6c1b53c1552b83ca0245f,
      0x3bfde6153ba808b23bca30e63be3fafb3ba71bcb3bae8ec23baaabf33b8a4b9e3b79749d3b61a3053b48738f3b104a2d3adc495b3aa8432a3a8e27ec3a4d444b,
      0x3b72adce3b6f83293b7610243b7d84123b7b6e133b8709113b89c7993b9747ef3ba6cc493bb78bf43bc84ea73bd6fc593bd9aa803bdb58313bd7056d3be9b2af,
      0x3ba43f553b9f47fe3ba54aa23ba9b97d3ba2e87e3ba668133ba6f4fe3ba45bdf3ba224b93ba093143b9de8503b9633423b8e96df3b86df5a3b81b6d73b792157,
      0x3b9898793b9d65633b9a9d813ba14d5d3b9a2b833b9dd8a63b97678f3b98f7413b9892ee3b9b30473b9b9bf43b9e02c13b9bdc413b9ac3fe3ba0f6593b9dc99e],
    #[0x372402a834bb398b31cef1562ee1bef52d6b42ab2ecebf84311d9acd2fee263b2b240020287c351e2c36d07e2f06a83220238f6a0b57356602d38e9a01094eb0,
      0x322e02fe321cd32937972a8149457c2f55b3fe78509e720e490ecd1c46d3c7a547d2f3d346c996a741f4eb073c3ce210393b87db39b814933a58130b393e6c9d,
      0x3c4be78c3badfccf3bfb82703c027db63ae9141f3a35c1cf3a51a31b3a598c7039ab6fc238b3dede38721a8c38a4a4b63759657a34df4a3433097984320b5f74,
      0x3a18890939f59afe3a26942f3b551c923c5db6a83c4fc8603c64e2ec3ce4c9113d4568e93d80ba333d9062033d32db573cab8a2c3cce30d43d31749d3d0ae681,
      0x3bdf27ab3bce4a833beaa98b3c042eb73bc680433b9e6c583bbe73c93bba99663b942c433b74656e3b5d0ede3b47ff5a3b21e9543ae8a3263a9679d53a41cb3b,
      0x3b6fcb4e3b67f4293b65c3793b6df6ce3b75b71b3b7c63b03b87d5c13b92d2513ba02bb03bb096a33bc25ea93bc6e6ea3bbff18c3bcd875a3be3cbcb3beb04fa,
      0x3ba0bf003ba11e2a3ba634ca3babc66c3ba676ec3ba439e03ba9e2db3ba918b83ba5e8903ba5014a3ba2a6643b9d23683b98cc733b9608803b8a53c73b7a468b,
      0x3b9d21003b9b9e983b9ace153b9afaf53b9a587b3b9b566b3b9c33cf3b9a55c13b9931f23b990d433b9b9b133b99ff4f3b9394d13b9508103b9a7ff63b9e4a54],
    #[0x2da585af2bd3558b2a35cce42db1c30e33f9b7c337e0e85531c5015528d1c11122dbc6e32387079f273aea8e29a4c0a12498a9b21c986e7d16b303ab13e4136f,
      0x4329e34c445d5b48477f4dda4c4987804d4941ea48cef755413faeba3dedd2a23f8389e44636ea5c486f920341ffdb8e3743a4a731833bdc2f922a722ef0d062,
      0x3b5e33523aa8aa993a3123cf3a404e703a7d27993a3ffba0393fbda6388648b4384d1eaf3810d93d373bfb9b368a2b2835e32a2a3582a0a333a1096832b797aa,
      0x3b2f48af3b5c8e343b6dc8173c6db7123cd319bc3cbf49e03c9adf1c3ce4b3c93d16519d3d796e723dcf24293d9384fb3cf27e0b3c6b60583bdec2583c80ec38,
      0x3bf952ac3ba59b263bbd77ae3bcc89af3ba261c03b959a293b7e2cbb3b6aa9b93b4f30213b43a6be3b0fb79d3ad920f03ab23ab33a9d0b853a5b5e1c3a0c16a6,
      0x3b73cd463b6f83993b77e03d3b8614143b8e808d3b946b753b9878103badb2c83bb7366b3bc3d0d93bd3ecf73be09fc83be1a1e13bdf63673bcf2f9b3bf58b35,
      0x3ba4c11e3b9fff1e3ba623e13baa33473ba3b35c3ba3e8a53ba3d0c93ba249493b9b964f3b9bf19a3b964a5c3b8cfbd93b8549e63b7f4a053b75feaf3b6c610e,
      0x3b99fad73b9946883b9906c83b9b55c43b9c8e2f3b9af34f3b9a02373b9a59a93b9ce38e3b9e1e413ba20c033ba1b10a3ba0f6583b9ea41e3ba182e33ba2af7a],
    #[0x2fd7ddab31de3d893335bff03336f2fd3011e3e72e03ca0d2d1cd7642de118092c51e76e28eb7ad22381ec951f38c7031ab4b39017027f3e14648dd412e3d339,
      0x41fc400c4219d4a04271db32434b53fe43e986324623e79947b613de48815af745da03d2429c3f803f54d5fc3ebbce0a3d9f125f3b7302d33671418431733630,
      0x3bcd18fb3b9d631e3b5f16073b17826c3abe84233a4d39f639cc4a3039944d7e393822093891aa623787d21336aa987935dfa7e53570a72a33867163327e0235,
      0x3b3a36e33b4946d43b1339923ba309a13bdf73de3c371aad3ca400903d1813423d0cb7603cf28eb53d0a5f3b3d4be4523d512da03ce3b76b3c1a54ae3c9ba761,
      0x3bf7dcdf3bb46e403bcf98ed3bd9e8893bb3d1023bb12ef83ba035a63b8e3cc33b6dcf093b5cd5193b3915913b1098d13ad946d13ab309963a7447af3a2983d7,
      0x3b7ce1173b760e203b7723733b7b079d3b7e79a23b8903f13b92797c3ba57f053ba95a6f3baf4e313bbc3a553bceb93a3bd87eee3bd811c13bc496f93bea060d,
      0x3ba256513b9ec3583ba4be003ba8a3f33ba40a023ba63ad23ba66fe33ba536e33b9f4bba3b9fa5173b9cac403b969ae13b8db7933b860aab3b7e12343b76020f,
      0x3b9cf26f3b9c91e73b9b6a713b9b18a33b9a33033b9a0c423b9b861d3b9b8f7c3b9b8dc53b99b0253b9ba3663b9bfe113b9d54883b9c5bbd3b9ecd893b9f8a16],
    #[0x2ec0c341306ce1573071513a30a47ce62de8e22f2c41341a2a36786029fa2c352843dd82272e3616243fe688225047aa1f32f3b91d86cad01d86a8f11dd2a6f7,
      0x4c1e40744aabf1f94839dc0846a4fbd345093ab2458d8b81445b864e435f8bbb4079b6de3eff443b3ca219763c51d5bb3a55925638aab4f534b4165d3049747f,
      0x3b709dd03b157bae3ab013473a7cde923a49638339b7805538dcbe4a38991daa3862636e37df100c36bac84a35e654a23569ff5a35b54c4733950dde32d42445,
      0x3bdbfacc3bf6df013b87ad533c51d8c33c7ffa373cb3e9da3cf01a793d490d313d0af5883cd67caa3ce8f4313d2e134d3d17a2643c767c363b7c64843c9fe31b,
      0x3c0854fd3b931d243bbd41b93bd41afa3b9bc6b33b9726b33b7b031c3b6641fb3b4145be3b335c633b0632213ad7cf3f3a9d8dc33a8a57b73a4ff5453a008a45,
      0x3b7d64923b778cc53b7e14c73b8818a03b8d9f583b9a3de93ba2ab313bba2cda3bb96f7d3bbb7eaa3bc7c41e3bdc547c3be2c6d03bdafbb53bb8f8e03bf5e21f,
      0x3ba4f77f3b9cea5f3ba5368e3baabfb93ba229ab3ba45b643ba3ba9d3ba1a6c63b988e0f3b9980733b9560be3b8d1d563b81a85b3b7a1e253b7322d73b6c3876,
      0x3b9aac2b3b99d30a3b9893a03b9985af3b9943583b999e5a3b9c6ca53b9d474c3b9eca633b9d4b763ba11d453ba158603ba2a9e73ba034bf3ba306703ba2982a],
    #[0x2e9bb7cf2d1c53412c512e0a2f85f94835709af63a113a1c369db7282e68792c27316c4624dc84af252bd8ea2495ad9e1e69134915afcf410f1625d50befc0d5,
      0x3bc3b20c3d3c0f8241458a80471dd79e49f7ff1a4840afcf443ee8f74360feb34673dc644bd4ca204b78bf1f43b6535e399118d733a4fc6f312b06b830014058,
      0x3bb4b5713b199c683abdea963ac3f1ee3aed58a03ad313823a2f93873995a841393a1f4338c496ae37e6ad8e371dd405363a546c3550188333822d153264a3e4,
      0x3ac0cd783ad3b1b13af3aa1a3bb55a013c1bb2fd3c3289df3c448a273cacfdad3d22e3b83dab8cec3df0b9973db2057d3d3396f03ccd752d3c62dd5d3c972ec9,
      0x3beec29c3bbcb0fe3bcb38b13bd3b1643bb8640a3baf305f3b9ff2783b9211503b7e410f3b6b49a23b3ba96f3b0f59d43ae9ad8c3ac3a8593a7e67563a30ee02,
      0x3b75d9603b6f903b3b72635b3b79e4f33b7ea9e53b83033a3b87cc833b997d6e3ba799023bb7c4803bc818303bd4a0ee3bd91d983bdc0eca3bd6bee13bee309e,
      0x3ba274f93ba0ab1c3ba556853ba8792e3ba50fe93ba5b8453ba62af43ba5bd083ba237fc3ba1a23f3b9cd22a3b965b9a3b905fd03b8a01603b80a46b3b7651bb,
      0x3b9c663c3b9c1e303b9c08bc3b9d27333b9d74903b9bc6293b999ac03b9850ed3b9949363b99ebf03b9c70463b9c84dd3b9c0faf3b9b33a03b9e32593ba03689]]

private def mixNum (r : Fin 8) : ℕ := mixingNumbers[r.val]?.getD 0

private def extractDigit (packed width i : ℕ) : ℕ :=
  packed / ((2^width)^i) % (2^width)

private def kernelNum (r : Fin 8) (i : ℕ) : ℕ :=
  extractDigit (kernelHalfPacked[r.val]?.getD 0) 37 (min i (31-i))

private def boundaryNum (r : Fin 8) (i : ℕ) : ℕ :=
  if i < 128 then
    250 * extractDigit (((boundaryPacked[r.val]?.getD #[])[i/16]?).getD 0) 32 (i%16) + 17
  else 250000000000

private lemma mixNum_sum : (∑ r : Fin 8, mixNum r) = 100000000 := by decide

private lemma kernelNum_sum (r : Fin 8) : (∑ i ∈ range 32, kernelNum r i) = 1000000000000 := by
  fin_cases r <;> decide

private def certCover (q : ℕ) : ℕ :=
  (List.ofFn fun r : Fin 8 => (List.ofFn fun i : Fin 32 =>
      mixNum r * kernelNum r i * boundaryNum r (q+i)).sum).sum

private lemma certCover_eq (q : ℕ) :
    certCover q = ∑ r : Fin 8, ∑ i ∈ range 32, mixNum r * kernelNum r i * boundaryNum r (q+i) := by
  simp only [certCover, List.sum_ofFn]
  exact Finset.sum_congr rfl fun r _ =>
    Fin.sum_univ_eq_sum_range (fun i => mixNum r * kernelNum r i * boundaryNum r (q+i)) 32

/- Check eight offsets at a time to keep kernel normalization bounded. The
last chunk beyond offset 128 has only constant boundary weights. -/
private abbrev coverChunk (c : ℕ) : Prop :=
  ∀ t : Fin 8, 25000000000000000000000000000000 ≤ certCover (8*c+t.val)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma coverChunk0 : coverChunk 0 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma coverChunk1 : coverChunk 1 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma coverChunk2 : coverChunk 2 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma coverChunk3 : coverChunk 3 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma coverChunk4 : coverChunk 4 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma coverChunk5 : coverChunk 5 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma coverChunk6 : coverChunk 6 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma coverChunk7 : coverChunk 7 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma coverChunk8 : coverChunk 8 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma coverChunk9 : coverChunk 9 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma coverChunk10 : coverChunk 10 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma coverChunk11 : coverChunk 11 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma coverChunk12 : coverChunk 12 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma coverChunk13 : coverChunk 13 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma coverChunk14 : coverChunk 14 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma coverChunk15 : coverChunk 15 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma coverChunk16 : coverChunk 16 := by decide +kernel

private lemma allChunks (i : Fin 17) : coverChunk i.val := by
  fin_cases i
  · exact coverChunk0
  · exact coverChunk1
  · exact coverChunk2
  · exact coverChunk3
  · exact coverChunk4
  · exact coverChunk5
  · exact coverChunk6
  · exact coverChunk7
  · exact coverChunk8
  · exact coverChunk9
  · exact coverChunk10
  · exact coverChunk11
  · exact coverChunk12
  · exact coverChunk13
  · exact coverChunk14
  · exact coverChunk15
  · exact coverChunk16

private lemma numericCoverAux (q : Fin 129) :
    25000000000000000000000000000000 ≤
    ∑ r : Fin 8, ∑ i ∈ range 32, mixNum r * kernelNum r i * boundaryNum r (q.val+i) := by
  rw [← certCover_eq]
  have h : q.val / 8 < 17 := by omega
  have ht : q.val % 8 < 8 := Nat.mod_lt _ (by decide)
  have hv := allChunks ⟨q.val / 8, h⟩ ⟨q.val % 8, ht⟩
  change 25000000000000000000000000000000 ≤ certCover (8*(q.val / 8)+q.val % 8) at hv
  rwa [Nat.div_add_mod] at hv

private def hzMix (r : Fin 8) : ℝ := (mixNum r : ℝ) / 100000000
private def hzP (r : Fin 8) (i : ℕ) : ℝ := (kernelNum r i : ℝ) / 1000000000000
private def hzW (r : Fin 8) (i : ℕ) : ℝ := (boundaryNum r i : ℝ) / 250000000000

private lemma hzMix_sum : ∑ r, hzMix r = 1 := by
  simp only [hzMix, ← Finset.sum_div, ← Nat.cast_sum, mixNum_sum, Nat.cast_ofNat]
  norm_num

private lemma hzP_sum (r : Fin 8) : (∑ i ∈ range 32, hzP r i) = 1 := by
  simp only [hzP, ← Finset.sum_div, ← Nat.cast_sum, kernelNum_sum, Nat.cast_ofNat]
  norm_num

private lemma hzP_sym (r : Fin 8) (i : ℕ) (hi : i < 32) : hzP r (32-1-i) = hzP r i := by
  have h : 31 - (31-i) = i := by omega
  simp [hzP, kernelNum, h, min_comm]

private lemma hzW_tail (r : Fin 8) (i : ℕ) (hi : 4*32 ≤ i) : hzW r i = 1 := by
  simp [hzW, boundaryNum, show ¬ i < 128 by omega]

private lemma hzCover (q : ℕ) (hq : q ≤ 128) :
    1 ≤ ∑ r, hzMix r * ∑ i ∈ range 32, hzP r i * hzW r (q+i) := by
  have hn := numericCoverAux ⟨q, by omega⟩
  change 25000000000000000000000000000000 ≤
    ∑ r : Fin 8, ∑ i ∈ range 32, mixNum r * kernelNum r i * boundaryNum r (q+i) at hn
  have hr : (25000000000000000000000000000000 : ℝ) ≤
    ∑ r : Fin 8, ∑ i ∈ range 32, (mixNum r : ℝ) * kernelNum r i * boundaryNum r (q+i) := by
    exact_mod_cast hn
  simp only [hzMix, hzP, hzW, Finset.mul_sum, div_mul_div_comm, ← Finset.sum_div]
  refine (le_div_iff₀ (by positivity)).2 ?_
  norm_num
  simpa only [mul_assoc] using hr

private def hzA : ℝ := 497329054138522113993707809619 / 390625000000000000000000000000
private def hzB : ℝ := 69918675237166718360455326217 / 100000000000000000000000000000

private lemma hzA_integer :
    (∑ r : Fin 8, mixNum r * ∑ i ∈ range 32, (kernelNum r i)^2) = 3978632433108176911949662476952 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma hzB_integer :
    (∑ r : Fin 8, mixNum r * ∑ i ∈ range 128, (boundaryNum r i)^2) = 769918675237166718360455326217000 := by decide

private lemma hzA_eq : energyCoeff hzMix hzP 32 = hzA := by
  simp only [energyCoeff, hzMix, hzP, div_pow, ← Finset.sum_div, div_mul_div_comm,
    ← Nat.cast_pow, ← Nat.cast_sum, ← Nat.cast_mul, hzA_integer, Nat.cast_ofNat, hzA]
  norm_num

private lemma hzB_eq : normCoeff hzMix hzW 4 32 = hzB := by
  norm_num [normCoeff]
  simp only [hzMix, hzW, div_pow, ← Finset.sum_div, div_mul_div_comm,
    ← Nat.cast_pow, ← Nat.cast_sum, ← Nat.cast_mul, hzB_integer, Nat.cast_ofNat, hzB]
  norm_num

private lemma move_to_zero {N : ℕ} {B : Finset ℕ}
    (hB : B ⊆ Icc 1 N) (hs : IsSidon (B : Set ℕ)) :
    ∃ A : Finset ℕ, A.card = B.card ∧ IsSidon (A : Set ℕ) ∧ ∀ x ∈ A, x < N := by
  let A := B.image (· - 1)
  have hpos (x : ℕ) (hx : x ∈ B) : 1 ≤ x := (Finset.mem_Icc.mp (hB hx)).1
  refine ⟨A, Finset.card_image_iff.mpr ?_, ?_, ?_⟩
  · intro x hx y hy e
    change x - 1 = y - 1 at e
    have hx' := hpos x hx
    have hy' := hpos y hy
    omega
  · intro a ha c hc d hd b hb eq
    obtain ⟨a',ha',rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨c',hc',rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨d',hd',rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨b',hb',rfl⟩ := Finset.mem_image.mp hb
    have he : a'+d' = c'+b' := by
      have := hpos a' ha'
      have := hpos b' hb'
      have := hpos c' hc'
      have := hpos d' hd'
      omega
    rcases hs a' ha' c' hc' d' hd' b' hb' he with h | h
    · exact Or.inl ⟨congrArg (· - 1) h.1, congrArg (· - 1) h.2⟩
    · exact Or.inr ⟨congrArg (· - 1) h.1, congrArg (· - 1) h.2⟩
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    have := Finset.mem_Icc.mp (hB hy)
    omega

end
end Green31Proof

open Green31 Green31Proof in
theorem OMA.solution : type_of% @Green31.green_31.variants.upper_hz26 := by
  classical
  have haux := large_scale (a := hzA) (b := hzB) (L := 4) (m := 32)
    (lo := (1.349410 : ℝ)) (hi := (1.349415 : ℝ)) (beta := (0.9435 : ℝ))
    (by norm_num [hzA]) (by norm_num [hzB]) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [hzA,hzB]) (by decide)
  refine ⟨0, haux.mono fun N hN => ?_⟩
  obtain ⟨h,hh,hn,hineq⟩ := hN
  let S := ((Icc 1 N).powerset.filter fun B : Finset ℕ => IsSidon (B : Set ℕ))
  have hS : S.Nonempty := ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, by intro a ha; simp at ha⟩⟩
  obtain ⟨B,hB,hmax⟩ := Finset.exists_mem_eq_sup S hS Finset.card
  obtain ⟨hsub,hSidon⟩ := Finset.mem_filter.mp hB
  obtain ⟨A,hcard,hAs,hAr⟩ := move_to_zero (Finset.mem_powerset.mp hsub) hSidon
  have he := smoothing_inequality hzMix hzP hzW (by decide : 0 < 32) hh hn
    hzMix_sum (by intro r; unfold hzMix; positivity)
    hzP_sum (by intro r i; unfold hzP; positivity) hzP_sym hzW_tail
    (by intro q hq; exact hzCover q (by omega)) A hAs hAr
  rw [hzA_eq,hzB_eq] at he
  have hbound := hineq A.card (Nat.cast_nonneg _) he
  change ((S.sup Finset.card : ℕ) : ℝ) ≤ _
  rw [hmax]
  simpa only [hcard, add_zero] using hbound