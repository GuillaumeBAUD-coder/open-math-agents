import OMAReductions.R_erdos_132_R1_H2_R1_H2_R1
import Mathlib

open Finset
open scoped Classical

namespace E132Count

abbrev Pt := EuclideanSpace ℝ (Fin 2)

noncomputable def pr (u x : Pt) : ℝ := inner ℝ x u

noncomputable def maxProj (u : Pt) (S : Finset Pt) : ℝ :=
  if h : S.Nonempty then S.sup' h (fun x => pr u x) else 0

noncomputable def minProj (u : Pt) (S : Finset Pt) : ℝ :=
  if h : S.Nonempty then S.inf' h (fun x => pr u x) else 0

lemma maxProj_of_nonempty {u : Pt} {S : Finset Pt} (h : S.Nonempty) :
    maxProj u S = S.sup' h (fun x => pr u x) := dif_pos h

lemma minProj_of_nonempty {u : Pt} {S : Finset Pt} (h : S.Nonempty) :
    minProj u S = S.inf' h (fun x => pr u x) := dif_pos h

noncomputable def hiProj (A : Finset Pt) (m : ℕ) (hm : m+1 ≤ A.card) (u : Pt) : ℝ :=
  ((A.powersetCard (m+1)).image (fun S => minProj u S)).max' (by
    obtain ⟨S, hS⟩ := Finset.powersetCard_nonempty.mpr hm
    exact ⟨_, Finset.mem_image_of_mem _ hS⟩)

noncomputable def loProj (A : Finset Pt) (m : ℕ) (hm : m+1 ≤ A.card) (u : Pt) : ℝ :=
  ((A.powersetCard (m+1)).image (fun S => maxProj u S)).min' (by
    obtain ⟨S, hS⟩ := Finset.powersetCard_nonempty.mpr hm
    exact ⟨_, Finset.mem_image_of_mem _ hS⟩)

lemma le_hiProj {A : Finset Pt} {m : ℕ} {hm : m+1 ≤ A.card} {u : Pt}
    {S : Finset Pt} (hS : S ∈ A.powersetCard (m+1)) :
    minProj u S ≤ hiProj A m hm u :=
  Finset.le_max' _ _ (Finset.mem_image_of_mem _ hS)

lemma loProj_le {A : Finset Pt} {m : ℕ} {hm : m+1 ≤ A.card} {u : Pt}
    {S : Finset Pt} (hS : S ∈ A.powersetCard (m+1)) :
    loProj A m hm u ≤ maxProj u S :=
  Finset.min'_le _ _ (Finset.mem_image_of_mem _ hS)

lemma minProj_le_maxProj {u : Pt} {S : Finset Pt} :
    minProj u S ≤ maxProj u S := by
  rcases S.eq_empty_or_nonempty with rfl | h
  · simp [minProj, maxProj]
  · rw [minProj_of_nonempty h, maxProj_of_nonempty h]
    obtain ⟨x, hx⟩ := h
    exact le_trans (Finset.inf'_le (fun x => pr u x) hx) (Finset.le_sup' (fun x => pr u x) hx)

section Fix

variable {A : Finset Pt} {m : ℕ} (hm : m+1 ≤ A.card)

lemma hiProj_witness (u : Pt) :
    ∃ S ∈ A.powersetCard (m+1), minProj u S = hiProj A m hm u := by
  have hmem : hiProj A m hm u ∈ (A.powersetCard (m+1)).image (fun S => minProj u S) :=
    Finset.max'_mem _ _
  obtain ⟨S, hS, hval⟩ := Finset.mem_image.mp hmem
  exact ⟨S, hS, hval⟩

lemma loProj_witness (u : Pt) :
    ∃ S ∈ A.powersetCard (m+1), maxProj u S = loProj A m hm u := by
  have hmem : loProj A m hm u ∈ (A.powersetCard (m+1)).image (fun S => maxProj u S) :=
    Finset.min'_mem _ _
  obtain ⟨S, hS, hval⟩ := Finset.mem_image.mp hmem
  exact ⟨S, hS, hval⟩

lemma card_ge_hiProj (u : Pt) :
    m+1 ≤ (A.filter (fun x => hiProj A m hm u ≤ pr u x)).card := by
  obtain ⟨S, hS, hval⟩ := hiProj_witness hm u
  have hSA : S ⊆ A := (Finset.mem_powersetCard.mp hS).1
  have hScard : S.card = m+1 := (Finset.mem_powersetCard.mp hS).2
  have hsub : S ⊆ A.filter (fun x => hiProj A m hm u ≤ pr u x) := by
    intro x hx
    have hne : S.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro h; rw [h] at hScard; simp at hScard
    have : pr u x ≥ minProj u S := by
      rw [minProj_of_nonempty hne]
      exact Finset.inf'_le _ hx
    exact Finset.mem_filter.mpr ⟨hSA hx, by rw [← hval]; exact this⟩
  calc m+1 = S.card := hScard.symm
    _ ≤ _ := Finset.card_le_card hsub

lemma card_ge_loProj (u : Pt) :
    m+1 ≤ (A.filter (fun x => pr u x ≤ loProj A m hm u)).card := by
  obtain ⟨S, hS, hval⟩ := loProj_witness hm u
  have hSA : S ⊆ A := (Finset.mem_powersetCard.mp hS).1
  have hScard : S.card = m+1 := (Finset.mem_powersetCard.mp hS).2
  have hsub : S ⊆ A.filter (fun x => pr u x ≤ loProj A m hm u) := by
    intro x hx
    have hne : S.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro h; rw [h] at hScard; simp at hScard
    have : pr u x ≤ maxProj u S := by
      rw [maxProj_of_nonempty hne]
      exact Finset.le_sup' _ hx
    exact Finset.mem_filter.mpr ⟨hSA hx, by rw [← hval]; exact this⟩
  calc m+1 = S.card := hScard.symm
    _ ≤ _ := Finset.card_le_card hsub

lemma card_lt_hiProj (u : Pt) :
    (A.filter (fun x => hiProj A m hm u < pr u x)).card ≤ m := by
  by_contra hcon
  push Not at hcon
  obtain ⟨S, hSA, hScard⟩ := Finset.exists_subset_card_eq hcon
  have hS : S ∈ A.powersetCard (m+1) := Finset.mem_powersetCard.mpr ⟨hSA.trans (Finset.filter_subset _ _), hScard⟩
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h; rw [h] at hScard; simp at hScard
  have hlt : hiProj A m hm u < minProj u S := by
    rw [minProj_of_nonempty hne, Finset.lt_inf'_iff hne]
    intro x hx
    exact (Finset.mem_filter.mp (hSA hx)).2
  exact absurd (le_hiProj hS) (not_le.mpr hlt)

lemma card_lt_loProj (u : Pt) :
    (A.filter (fun x => pr u x < loProj A m hm u)).card ≤ m := by
  by_contra hcon
  push Not at hcon
  obtain ⟨S, hSA, hScard⟩ := Finset.exists_subset_card_eq hcon
  have hS : S ∈ A.powersetCard (m+1) := Finset.mem_powersetCard.mpr ⟨hSA.trans (Finset.filter_subset _ _), hScard⟩
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h; rw [h] at hScard; simp at hScard
  have hlt : maxProj u S < loProj A m hm u := by
    rw [maxProj_of_nonempty hne, Finset.sup'_lt_iff hne]
    intro x hx
    exact (Finset.mem_filter.mp (hSA hx)).2
  exact absurd (loProj_le hS) (not_le.mpr hlt)

end Fix

end E132Count

namespace E132Count

/-- All displacement vectors `x - y` of ordered pairs of distinct points of `A`. -/
noncomputable def dispSet (A : Finset Pt) : Finset Pt :=
  A.offDiag.image (fun z => z.1 - z.2)

/-- Unit directions of the displacement vectors of `A`. -/
noncomputable def dirSet (A : Finset Pt) : Finset Pt :=
  (dispSet A).image (fun v => (‖v‖)⁻¹ • v)

lemma dirSet_nonempty {A : Finset Pt} (h : 2 ≤ A.card) : (dirSet A).Nonempty := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
  have hmem : x - y ∈ dispSet A :=
    Finset.mem_image.mpr ⟨(x,y), Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩, rfl⟩
  exact ⟨_, Finset.mem_image.mpr ⟨_, hmem, rfl⟩⟩

lemma dispSet_ne_zero {A : Finset Pt} {v : Pt} (hv : v ∈ dispSet A) : v ≠ 0 := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨h1, h2, hne⟩ := Finset.mem_offDiag.mp hz
  exact sub_ne_zero.mpr hne

lemma dirSet_unit {A : Finset Pt} {v : Pt} (hv : v ∈ dispSet A) :
    (‖v‖)⁻¹ • v ∈ dirSet A :=
  Finset.mem_image.mpr ⟨v, hv, rfl⟩

lemma norm_dir {v : Pt} (hv : v ≠ 0) : ‖(‖v‖)⁻¹ • v‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

lemma inner_dir {v : Pt} (hv : v ≠ 0) : inner ℝ v ((‖v‖)⁻¹ • v) = ‖v‖ := by
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp

end E132Count

namespace E132Count

noncomputable def gapFun (A : Finset Pt) (m : ℕ) (hm : m+1 ≤ A.card) (u : Pt) : ℝ :=
  hiProj A m hm u - loProj A m hm u

/-- For a non-zero displacement `v` with `‖v‖ > W` (where `W` bounds the gap in every
displacement direction), at most `2m` points `y` have both `y` and `y + v` in `A`. -/
lemma card_add_le_two_mul (A : Finset Pt) (m : ℕ) (hm : m+1 ≤ A.card)
    {v : Pt} (hv : v ≠ 0) {W : ℝ}
    (hWmax : gapFun A m hm ((‖v‖)⁻¹ • v) ≤ W) (hWlt : W < ‖v‖) :
    (A.filter (fun y => y + v ∈ A)).card ≤ 2*m := by
  set w : Pt := (‖v‖)⁻¹ • v with hwdef
  have hw : ‖w‖ = 1 := norm_dir hv
  have hinner : inner ℝ v w = ‖v‖ := inner_dir hv
  set B := A.filter (fun y => y + v ∈ A) with hBdef
  have hsplit : B.card = (B.filter (fun y => pr w y < loProj A m hm w)).card +
      (B.filter (fun y => ¬ (pr w y < loProj A m hm w))).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := B) (p := fun y => pr w y < loProj A m hm w)]
  have h1 : (B.filter (fun y => pr w y < loProj A m hm w)).card ≤ m := by
    apply le_trans _ (card_lt_loProj hm w)
    apply Finset.card_le_card
    intro y hy
    have hyB : y ∈ B := (Finset.mem_filter.mp hy).1
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hyB).1, (Finset.mem_filter.mp hy).2⟩
  have h2 : (B.filter (fun y => ¬ (pr w y < loProj A m hm w))).card ≤ m := by
    have hT : (A.filter (fun x => hiProj A m hm w < pr w x)).card ≤ m := card_lt_hiProj hm w
    have hmaps : Set.MapsTo (fun y => y + v)
        ↑(B.filter (fun y => ¬ (pr w y < loProj A m hm w)))
        ↑(A.filter (fun x => hiProj A m hm w < pr w x)) := by
      intro y hy
      have hyB : y ∈ B := (Finset.mem_filter.mp hy).1
      have hnot : ¬ (pr w y < loProj A m hm w) := (Finset.mem_filter.mp hy).2
      have hyA : y ∈ A := (Finset.mem_filter.mp hyB).1
      have hyv : y + v ∈ A := (Finset.mem_filter.mp hyB).2
      refine Finset.mem_filter.mpr ⟨hyv, ?_⟩
      have hle : loProj A m hm w ≤ pr w y := le_of_not_gt hnot
      have hpr : pr w (y + v) = pr w y + ‖v‖ := by
        simp only [pr, inner_add_left]
        rw [hinner]
      rw [hpr]
      have hgap : gapFun A m hm w ≤ W := hWmax
      have : loProj A m hm w + ‖v‖ > hiProj A m hm w := by
        have : ‖v‖ > gapFun A m hm w := lt_of_le_of_lt hWmax hWlt
        simp only [gapFun] at this
        linarith
      linarith
    have hinj : Set.InjOn (fun y => y + v)
        ↑(B.filter (fun y => ¬ (pr w y < loProj A m hm w))) := by
      intro a _ b _ h
      simpa using h
    exact le_trans (Finset.card_le_card_of_injOn _ hmaps hinj) hT
  rw [hsplit]
  omega

end E132Count

namespace E132Count

open OMA.S_erdos_132 in
/-- A distance strictly larger than the maximal projection gap is rare. -/
lemma pairMultiplicity_le_card (A : Finset Pt) (m L : ℕ) (hm : m+1 ≤ A.card)
    (hL : ∀ d : ℝ, ((A.offDiag.filter (fun p => dist p.1 p.2 = d)).image
      (fun p => p.1 - p.2)).card ≤ L)
    (hLm : L * m ≤ A.card) {W : ℝ}
    (hWmax : ∀ v ∈ dispSet A, gapFun A m hm ((‖v‖)⁻¹ • v) ≤ W)
    {d : ℝ} (hd : W < d) :
    OMA.S_erdos_132.pairMultiplicity A d ≤ A.card := by
  classical
  set F := A.offDiag.filter (fun p => dist p.1 p.2 = d) with hF
  set Vd := F.image (fun p => p.1 - p.2) with hVd
  have hVdL : Vd.card ≤ L := hL d
  have hfiber : ∀ v ∈ Vd, (F.filter (fun p => p.1 - p.2 = v)).card ≤ 2*m := by
    intro v hv
    have hvdisp : v ∈ dispSet A := by
      obtain ⟨p, hp, hval⟩ := Finset.mem_image.mp hv
      refine Finset.mem_image.mpr ⟨p, ?_, hval⟩
      exact Finset.mem_filter.mp hp |>.1
    have hvne : v ≠ 0 := dispSet_ne_zero hvdisp
    have hnorm : ‖v‖ = d := by
      obtain ⟨p, hp, hval⟩ := Finset.mem_image.mp hv
      have hp' := Finset.mem_filter.mp hp
      rw [← hval, ← dist_eq_norm]
      exact hp'.2
    have hbound : (F.filter (fun p => p.1 - p.2 = v)).card ≤
        (A.filter (fun y => y + v ∈ A)).card := by
      apply Finset.card_le_card_of_injOn (fun p : Pt × Pt => p.2)
      · intro p hp
        have hpF : p ∈ F := (Finset.mem_filter.mp hp).1
        have hval : p.1 - p.2 = v := (Finset.mem_filter.mp hp).2
        have hpA := Finset.mem_offDiag.mp (Finset.mem_filter.mp hpF).1
        refine Finset.mem_filter.mpr ⟨hpA.2.1, ?_⟩
        have : p.2 + v = p.1 := by rw [← hval]; abel
        rw [this]; exact hpA.1
      · intro a ha b hb hab
        have haF : a ∈ F := (Finset.mem_filter.mp ha).1
        have hbF : b ∈ F := (Finset.mem_filter.mp hb).1
        have hva : a.1 - a.2 = v := (Finset.mem_filter.mp ha).2
        have hvb : b.1 - b.2 = v := (Finset.mem_filter.mp hb).2
        have h2 : a.2 = b.2 := hab
        have ha1 : a.1 = v + a.2 := by rw [← hva]; abel
        have hb1 : b.1 = v + b.2 := by rw [← hvb]; abel
        have h1 : a.1 = b.1 := by rw [ha1, hb1, h2]
        exact Prod.ext h1 h2
    have htwo := card_add_le_two_mul A m hm hvne
      (W := W) (by simpa [gapFun] using hWmax v hvdisp) (by rw [hnorm]; exact hd)
    omega
  have hcard : F.card ≤ 2 * (L * m) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p : Pt × Pt => p.1 - p.2) (t := Vd)
      (fun p hp => Finset.mem_image_of_mem _ hp)]
    calc ∑ v ∈ Vd, (F.filter (fun p => p.1 - p.2 = v)).card
        ≤ ∑ v ∈ Vd, 2*m := Finset.sum_le_sum hfiber
      _ = Vd.card * (2*m) := by simp [Finset.sum_const, smul_eq_mul]
      _ ≤ L * (2*m) := Nat.mul_le_mul_right _ hVdL
      _ = 2 * (L*m) := by ring
  have htwo : F.card ≤ 2 * A.card := by
    have : 2 * (L*m) ≤ 2 * A.card := Nat.mul_le_mul_left 2 hLm
    omega
  show F.card / 2 ≤ A.card
  omega

end E132Count

namespace E132Count

lemma eq_smul_of_inner_eq_norm {v u : Pt} (hu : ‖u‖ = 1) (h : inner ℝ v u = ‖v‖) :
    v = ‖v‖ • u := by
  have hw : ‖v - ‖v‖ • u‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      h, real_inner_comm v u, real_inner_self_eq_norm_sq]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg v), hu, mul_one]
    ring
  have hw0 : ‖v - ‖v‖ • u‖ = 0 := sq_eq_zero_iff.mp hw
  have hz : v - ‖v‖ • u = 0 := norm_eq_zero.mp hw0
  exact sub_eq_zero.mp hz

lemma pr_sub_le_dist {u p y : Pt} (hu : ‖u‖ = 1) : pr u p - pr u y ≤ dist p y := by
  have h1 : pr u p - pr u y = inner ℝ (p - y) u := by simp [pr, inner_sub_left]
  rw [h1, dist_eq_norm]
  calc inner ℝ (p - y) u ≤ |inner ℝ (p - y) u| := le_abs_self _
    _ ≤ ‖p - y‖ * ‖u‖ := abs_real_inner_le_norm _ _
    _ = ‖p - y‖ := by rw [hu, mul_one]

lemma eq_of_le_pr_sub {u p y : Pt} (hu : ‖u‖ = 1) {W : ℝ}
    (hle : W ≤ pr u p - pr u y) (hdist : dist p y = W) : y = p - W • u := by
  have h1 : pr u p - pr u y = inner ℝ (p - y) u := by simp [pr, inner_sub_left]
  have h2 : ‖p - y‖ = W := by rw [← dist_eq_norm, hdist]
  have hge : inner ℝ (p - y) u ≥ ‖p - y‖ := by
    rw [h2]
    linarith [h1, hle]
  have hle2 : inner ℝ (p - y) u ≤ ‖p - y‖ := by
    calc inner ℝ (p - y) u ≤ |inner ℝ (p - y) u| := le_abs_self _
      _ ≤ ‖p - y‖ * ‖u‖ := abs_real_inner_le_norm _ _
      _ = ‖p - y‖ := by rw [hu, mul_one]
  have heq : inner ℝ (p - y) u = ‖p - y‖ := le_antisymm hle2 hge
  have hsmul : p - y = ‖p - y‖ • u := eq_smul_of_inner_eq_norm hu heq
  rw [h2] at hsmul
  have := congrArg (fun z => p - z) hsmul
  simpa using this

end E132Count

namespace E132Count

open OMA.S_erdos_132 in
/-- Distances from one point give many distinct distances overall. -/
lemma card_dist_image_ge (A : Finset Pt) (G : ℕ) (hcard : 2 ≤ A.card)
    (hG : ∀ p ∈ A, ∀ d : ℝ, (A.filter (fun q => dist p q = d)).card ≤ G)
    {p : Pt} (hp : p ∈ A) :
    (A.card - 1) / G ≤ (A.offDiag.image (fun z => dist z.1 z.2)).card := by
  classical
  set T := (A.erase p).image (fun y => dist p y) with hT
  have hfib : ∀ d ∈ T, ((A.erase p).filter (fun y => dist p y = d)).card ≤ G := by
    intro d hd
    have hsub : (A.erase p).filter (fun y => dist p y = d) ⊆ A.filter (fun y => dist p y = d) := by
      intro y hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase (Finset.mem_filter.mp hy).1,
        (Finset.mem_filter.mp hy).2⟩
    exact le_trans (Finset.card_le_card hsub) (hG p hp d)
  have hsum : (A.erase p).card = ∑ d ∈ T, ((A.erase p).filter (fun y => dist p y = d)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun y => dist p y) (t := T)
      (fun y hy => Finset.mem_image_of_mem _ hy)]
  have hle : (A.erase p).card ≤ T.card * G := by
    rw [hsum]
    calc ∑ d ∈ T, ((A.erase p).filter (fun y => dist p y = d)).card
        ≤ ∑ d ∈ T, G := Finset.sum_le_sum hfib
      _ = T.card * G := by simp [Finset.sum_const, smul_eq_mul]
  have herase : (A.erase p).card = A.card - 1 := by
    rw [Finset.card_erase_of_mem hp]
  have hTle : T.card ≤ (A.offDiag.image (fun z => dist z.1 z.2)).card := by
    apply Finset.card_le_card
    intro d hd
    obtain ⟨y, hy, hval⟩ := Finset.mem_image.mp hd
    have hyA : y ∈ A := Finset.mem_of_mem_erase hy
    have hyp : y ≠ p := Finset.ne_of_mem_erase hy
    refine Finset.mem_image.mpr ⟨(p, y), Finset.mem_offDiag.mpr ⟨hp, hyA, (Ne.symm hyp)⟩, ?_⟩
    exact hval
  have : (A.card - 1) / G ≤ T.card := by
    rw [← herase]
    exact Nat.div_le_of_le_mul (le_trans hle (le_of_eq (Nat.mul_comm _ _)))
  exact le_trans this hTle

end E132Count

namespace E132Count

open OMA.S_erdos_132 in
/-- If every distance has at most two displacement vectors, every distance is rare. -/
lemma all_rare_of_two (A : Finset Pt) (hcard : 2 ≤ A.card)
    (hL : ∀ d : ℝ, ((A.offDiag.filter (fun p => dist p.1 p.2 = d)).image
      (fun p => p.1 - p.2)).card ≤ 2) :
    rareDistances A = A.offDiag.image (fun z => dist z.1 z.2) := by
  classical
  ext d
  simp only [rareDistances, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨h, _⟩; exact h
  · rintro ⟨z, hz, rfl⟩
    refine ⟨⟨z, hz, rfl⟩, ?_, ?_⟩
    · -- multiplicity at least one
      have hmem : (z.1, z.2) ∈ A.offDiag.filter (fun p => dist p.1 p.2 = dist z.1 z.2) :=
        Finset.mem_filter.mpr ⟨hz, rfl⟩
      have hmem' : (z.2, z.1) ∈ A.offDiag.filter (fun p => dist p.1 p.2 = dist z.1 z.2) := by
        obtain ⟨h1, h2, hne⟩ := Finset.mem_offDiag.mp hz
        exact Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨h2, h1, (Ne.symm hne)⟩,
          dist_comm z.2 z.1⟩
      have hcard2 : 2 ≤ (A.offDiag.filter (fun p => dist p.1 p.2 = dist z.1 z.2)).card := by
        have hpair : ({(z.1,z.2), (z.2,z.1)} : Finset (Pt × Pt)).card = 2 := by
          apply Finset.card_pair
          intro h
          exact (Finset.mem_offDiag.mp hz).2.2 (Prod.mk.injEq .. ▸ h).1
        have hsub : ({(z.1,z.2), (z.2,z.1)} : Finset (Pt × Pt)) ⊆
            A.offDiag.filter (fun p => dist p.1 p.2 = dist z.1 z.2) := by
          intro p hp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl
          · exact hmem
          · exact hmem'
        calc (2 : ℕ) = ({(z.1,z.2), (z.2,z.1)} : Finset (Pt × Pt)).card := hpair.symm
          _ ≤ _ := Finset.card_le_card hsub
      show 1 ≤ (A.offDiag.filter (fun p => dist p.1 p.2 = dist z.1 z.2)).card / 2
      omega
    · -- multiplicity at most card
      set F := A.offDiag.filter (fun p => dist p.1 p.2 = dist z.1 z.2) with hF
      set Vd := F.image (fun p => p.1 - p.2) with hVd
      have hVd2 : Vd.card ≤ 2 := hL (dist z.1 z.2)
      have hmaps : Set.MapsTo (fun p : Pt × Pt => (p.1 - p.2, p.1))
          ↑F ↑(Vd ×ˢ A) := by
        intro p hp
        exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp,
          (Finset.mem_offDiag.mp (Finset.mem_filter.mp hp).1).1⟩
      have hinj : Set.InjOn (fun p : Pt × Pt => (p.1 - p.2, p.1)) ↑F := by
        intro a ha b hb hab
        simp only [Prod.mk.injEq] at hab
        have ha' := (Finset.mem_filter.mp ha).1
        have hbv := (Finset.mem_filter.mp hb).2
        have hav := (Finset.mem_filter.mp ha).2
        have h1 : a.1 = b.1 := hab.2
        have h2 : a.2 = b.2 := by
          have hh : a.1 - a.2 = b.1 - b.2 := hab.1
          rw [h1] at hh
          exact sub_right_injective hh
        exact Prod.ext h1 h2
      have hFle : F.card ≤ 2 * A.card := by
        calc F.card ≤ (Vd ×ˢ A).card := Finset.card_le_card_of_injOn _ hmaps hinj
          _ = Vd.card * A.card := Finset.card_product _ _
          _ ≤ 2 * A.card := Nat.mul_le_mul_right _ hVd2
      show F.card / 2 ≤ A.card
      omega

open OMA.S_erdos_132 in
/-- If every pinned circle has at most one point, every distance is rare. -/
lemma all_rare_of_one (A : Finset Pt) (hcard : 2 ≤ A.card)
    (hG : ∀ p ∈ A, ∀ d : ℝ, (A.filter (fun q => dist p q = d)).card ≤ 1) :
    rareDistances A = A.offDiag.image (fun z => dist z.1 z.2) := by
  classical
  ext d
  simp only [rareDistances, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨h, _⟩; exact h
  · rintro ⟨z, hz, rfl⟩
    refine ⟨⟨z, hz, rfl⟩, ?_, ?_⟩
    · have hmem : (z.1, z.2) ∈ A.offDiag.filter (fun p => dist p.1 p.2 = dist z.1 z.2) :=
        Finset.mem_filter.mpr ⟨hz, rfl⟩
      obtain ⟨h1, h2, hne⟩ := Finset.mem_offDiag.mp hz
      have hmem' : (z.2, z.1) ∈ A.offDiag.filter (fun p => dist p.1 p.2 = dist z.1 z.2) :=
        Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨h2, h1, (Ne.symm hne)⟩, dist_comm z.2 z.1⟩
      have hcard2 : 2 ≤ (A.offDiag.filter (fun p => dist p.1 p.2 = dist z.1 z.2)).card := by
        have hpair : ({(z.1,z.2), (z.2,z.1)} : Finset (Pt × Pt)).card = 2 := by
          apply Finset.card_pair
          intro h
          exact (Finset.mem_offDiag.mp hz).2.2 (Prod.mk.injEq .. ▸ h).1
        have hsub : ({(z.1,z.2), (z.2,z.1)} : Finset (Pt × Pt)) ⊆
            A.offDiag.filter (fun p => dist p.1 p.2 = dist z.1 z.2) := by
          intro p hp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl
          · exact hmem
          · exact hmem'
        calc (2 : ℕ) = ({(z.1,z.2), (z.2,z.1)} : Finset (Pt × Pt)).card := hpair.symm
          _ ≤ _ := Finset.card_le_card hsub
      show 1 ≤ (A.offDiag.filter (fun p => dist p.1 p.2 = dist z.1 z.2)).card / 2
      omega
    · set F := A.offDiag.filter (fun p => dist p.1 p.2 = dist z.1 z.2) with hF
      have hFle : F.card ≤ A.card := by
        apply Finset.card_le_card_of_injOn (fun p : Pt × Pt => p.1)
        · intro p hp
          exact (Finset.mem_offDiag.mp (Finset.mem_filter.mp hp).1).1
        · intro a ha b hb hab
          have ha' := Finset.mem_filter.mp ha
          have hb' := Finset.mem_filter.mp hb
          have hmem1 : a.2 ∈ A.filter (fun q => dist a.1 q = dist z.1 z.2) :=
            Finset.mem_filter.mpr ⟨(Finset.mem_offDiag.mp ha'.1).2.1, ha'.2⟩
          have hab1 : a.1 = b.1 := hab
          have hmem2 : b.2 ∈ A.filter (fun q => dist a.1 q = dist z.1 z.2) := by
            refine Finset.mem_filter.mpr ⟨(Finset.mem_offDiag.mp hb'.1).2.1, ?_⟩
            rw [hab1]; exact hb'.2
          have hone := hG a.1 (Finset.mem_offDiag.mp ha'.1).1 (dist z.1 z.2)
          have h22 := Finset.card_le_one.mp hone a.2 hmem1 b.2 hmem2
          exact Prod.ext hab1 h22
      show F.card / 2 ≤ A.card
      omega

end E132Count

namespace E132Count

open OMA.S_erdos_132 in
lemma one_le_pairMultiplicity {A : Finset Pt} {d : ℝ}
    (h : ∃ z ∈ A.offDiag, dist z.1 z.2 = d) : 1 ≤ pairMultiplicity A d := by
  obtain ⟨z, hz, hval⟩ := h
  obtain ⟨h1, h2, hne⟩ := Finset.mem_offDiag.mp hz
  have hmem : (z.1, z.2) ∈ A.offDiag.filter (fun p => dist p.1 p.2 = d) :=
    Finset.mem_filter.mpr ⟨hz, hval⟩
  have hmem' : (z.2, z.1) ∈ A.offDiag.filter (fun p => dist p.1 p.2 = d) :=
    Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨h2, h1, (Ne.symm hne)⟩, by rw [dist_comm]; exact hval⟩
  have hpair : ({(z.1,z.2), (z.2,z.1)} : Finset (Pt × Pt)).card = 2 := by
    apply Finset.card_pair
    intro hh
    exact hne (Prod.mk.injEq .. ▸ hh).1
  have hsub : ({(z.1,z.2), (z.2,z.1)} : Finset (Pt × Pt)) ⊆
      A.offDiag.filter (fun p => dist p.1 p.2 = d) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact hmem
    · exact hmem'
  have h2le : 2 ≤ (A.offDiag.filter (fun p => dist p.1 p.2 = d)).card := by
    calc (2:ℕ) = ({(z.1,z.2), (z.2,z.1)} : Finset (Pt × Pt)).card := hpair.symm
      _ ≤ _ := Finset.card_le_card hsub
  show 1 ≤ (A.offDiag.filter (fun p => dist p.1 p.2 = d)).card / 2
  omega

end E132Count

namespace E132Count

open OMA.S_erdos_132 in
lemma main_case (A : Finset Pt) (G L k m : ℕ)
    (hcard : 6 ≤ A.card)
    (hG : ∀ p ∈ A, ∀ d : ℝ, (A.filter (fun q => dist p q = d)).card ≤ G)
    (hL : ∀ d : ℝ, ((A.offDiag.filter (fun p => dist p.1 p.2 = d)).image
      (fun p => p.1 - p.2)).card ≤ L)
    (hL3 : 3 ≤ L) (hk1 : 1 ≤ k) (hkG : k * G ≤ m)
    (hmdef : m = A.card / L) (hLm : L * m ≤ A.card) :
    k ≤ (rareDistances A).card := by
  classical
  have hGpos : 0 < G := by
    obtain ⟨p', hp', q', hq', hpq'⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
    have h1 : 1 ≤ (A.filter (fun r => dist p' r = dist p' q')).card :=
      Finset.card_pos.mpr ⟨q', Finset.mem_filter.mpr ⟨hq', rfl⟩⟩
    have h2 := hG p' hp' (dist p' q')
    omega
  have hmle : m ≤ A.card / 3 := by
    rw [hmdef]
    exact Nat.div_le_div_left hL3 (by norm_num)
  have hm : m + 1 ≤ A.card := by omega
  have hm2 : 2 * (m + 1) ≤ A.card := by omega
  -- the direction set and the maximal gap
  set D := dirSet A with hD
  have hDne : D.Nonempty := dirSet_nonempty (by omega)
  set gap : Pt → ℝ := fun u => gapFun A m hm u with hgap
  set W : ℝ := (D.image gap).max' (hDne.image gap) with hW
  obtain ⟨u, huD, huW⟩ := Finset.mem_image.mp (Finset.max'_mem (D.image gap) (hDne.image gap))
  have hunit : ‖u‖ = 1 := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp huD
    exact norm_dir (dispSet_ne_zero hv)
  have hWmax : ∀ v ∈ dispSet A, gap ((‖v‖)⁻¹ • v) ≤ W := by
    intro v hv
    exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨_, dirSet_unit hv, rfl⟩)
  -- witnesses for the two order statistics
  obtain ⟨Sp, hSp, hSpval⟩ := hiProj_witness hm u
  have hSpne : Sp.Nonempty :=
    Finset.card_pos.mp (by rw [(Finset.mem_powersetCard.mp hSp).2]; omega)
  obtain ⟨p, hpSp, hpval⟩ := Finset.exists_mem_eq_inf' hSpne (fun x => pr u x)
  have hpA : p ∈ A := (Finset.mem_powersetCard.mp hSp).1 hpSp
  have hppr : pr u p = hiProj A m hm u := by
    rw [← hpval, ← minProj_of_nonempty hSpne]; exact hSpval
  obtain ⟨Sq, hSq, hSqval⟩ := loProj_witness hm u
  have hSqne : Sq.Nonempty :=
    Finset.card_pos.mp (by rw [(Finset.mem_powersetCard.mp hSq).2]; omega)
  obtain ⟨q, hqSq, hqval⟩ := Finset.exists_mem_eq_sup' hSqne (fun x => pr u x)
  have hqA : q ∈ A := (Finset.mem_powersetCard.mp hSq).1 hqSq
  have hqqr : pr u q = loProj A m hm u := by
    rw [← hqval, ← maxProj_of_nonempty hSqne]; exact hSqval
  have hlo_le_hi : loProj A m hm u ≤ hiProj A m hm u := by
    by_contra hcon
    push Not at hcon
    have h1 : (A.filter (fun x => pr u x < loProj A m hm u)).card ≤ m := card_lt_loProj hm u
    have h2 : (A.filter (fun x => hiProj A m hm u < pr u x)).card ≤ m := card_lt_hiProj hm u
    have hcover : A ⊆ A.filter (fun x => pr u x < loProj A m hm u) ∪
        A.filter (fun x => hiProj A m hm u < pr u x) := by
      intro x hx
      by_cases h : pr u x < loProj A m hm u
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, h⟩)
      · push Not at h
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, by linarith⟩)
    have hle := Finset.card_le_card hcover
    have hunion : (A.filter (fun x => pr u x < loProj A m hm u) ∪
        A.filter (fun x => hiProj A m hm u < pr u x)).card ≤ 2*m := by
      have h := Finset.card_union_le (A.filter (fun x => pr u x < loProj A m hm u))
        (A.filter (fun x => hiProj A m hm u < pr u x))
      omega
    omega
  by_cases hWnonpos : W ≤ 0
  · -- all distances are rare
    have hrare : rareDistances A = A.offDiag.image (fun z => dist z.1 z.2) := by
      ext d
      change d ∈ (A.offDiag.image (fun z => dist z.1 z.2)).filter
          (fun d => 1 ≤ pairMultiplicity A d ∧ pairMultiplicity A d ≤ A.card) ↔
        d ∈ A.offDiag.image (fun z => dist z.1 z.2)
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨h, _⟩; exact h
      · intro hd
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hd
        obtain ⟨h1, h2, hne⟩ := Finset.mem_offDiag.mp hz
        have hpos : 0 < dist z.1 z.2 := dist_pos.mpr hne
        have hgt : W < dist z.1 z.2 := lt_of_le_of_lt hWnonpos hpos
        refine ⟨Finset.mem_image.mpr ⟨z, hz, rfl⟩, one_le_pairMultiplicity ⟨z, hz, rfl⟩,
          pairMultiplicity_le_card A m L hm hL hLm hWmax hgt⟩
    obtain ⟨pp, hpp⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
    have hge := card_dist_image_ge A G (by omega) hG hpp
    have hkg_le : k * G ≤ A.card - 1 := by
      have h1 : k * G ≤ A.card / 3 := le_trans hkG hmle
      have h3 : A.card / 3 ≤ A.card - 1 := by
        rw [Nat.div_le_iff_le_mul (by norm_num : 0 < 3)]
        omega
      omega
    have hk_le : k ≤ (A.card - 1) / G := by
      rw [Nat.le_div_iff_mul_le hGpos]
      exact hkg_le
    rw [hrare]
    exact le_trans hk_le hge
  · -- the main case
    push Not at hWnonpos
    have hWval : W = hiProj A m hm u - loProj A m hm u :=
      huW.symm.trans rfl
    -- the block B of the `m+1` lowest points
    set B := A.filter (fun y => pr u y ≤ pr u q) with hB
    have hBcard : m + 1 ≤ B.card := by
      have h := card_ge_loProj hm u
      have hB' : B = A.filter (fun x => pr u x ≤ loProj A m hm u) := by
        ext x; simp only [hB, Finset.mem_filter, hqqr]
      rw [hB']; exact h
    have hBge : ∀ y ∈ B, W ≤ pr u p - pr u y := by
      intro y hy
      have hypr : pr u y ≤ loProj A m hm u := by
        rw [← hqqr]; exact (Finset.mem_filter.mp hy).2
      rw [hppr, hWval]
      linarith
    have hBdist : ∀ y ∈ B, W ≤ dist p y := by
      intro y hy
      exact le_trans (hBge y hy) (pr_sub_le_dist hunit)
    have hpB : p ∉ B := by
      intro hpB'
      have hpr : pr u p ≤ pr u q := (Finset.mem_filter.mp hpB').2
      rw [hppr, hqqr] at hpr
      linarith
    have huniq : ∀ y₁ ∈ B, ∀ y₂ ∈ B, dist p y₁ = W → dist p y₂ = W → y₁ = y₂ := by
      intro y₁ hy₁ y₂ hy₂ hd₁ hd₂
      have e₁ : y₁ = p - W • u := eq_of_le_pr_sub hunit (hBge y₁ hy₁) hd₁
      have e₂ : y₂ = p - W • u := eq_of_le_pr_sub hunit (hBge y₂ hy₂) hd₂
      rw [e₁, e₂]
    set Bgood := B.filter (fun y => W < dist p y) with hBgood
    have hBgoodcard : m ≤ Bgood.card := by
      have hsplit : B.card = Bgood.card + (B.filter (fun y => ¬ W < dist p y)).card := by
        rw [hBgood, ← Finset.card_filter_add_card_filter_not (s := B) (p := fun y => W < dist p y)]
      have hsmall : (B.filter (fun y => ¬ W < dist p y)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro y₁ hy₁ y₂ hy₂
        have h1 : y₁ ∈ B := (Finset.mem_filter.mp hy₁).1
        have h2 : y₂ ∈ B := (Finset.mem_filter.mp hy₂).1
        have hd₁ : dist p y₁ = W := by
          have hge := hBdist y₁ h1
          have hnot : ¬ W < dist p y₁ := (Finset.mem_filter.mp hy₁).2
          linarith
        have hd₂ : dist p y₂ = W := by
          have hge := hBdist y₂ h2
          have hnot : ¬ W < dist p y₂ := (Finset.mem_filter.mp hy₂).2
          linarith
        exact huniq y₁ h1 y₂ h2 hd₁ hd₂
      omega
    set Sdist := Bgood.image (fun y => dist p y) with hSdist
    have hSdist_card : k ≤ Sdist.card := by
      have hfib : ∀ d ∈ Sdist, (Bgood.filter (fun y => dist p y = d)).card ≤ G := by
        intro d hd
        have hsub : Bgood.filter (fun y => dist p y = d) ⊆ A.filter (fun y => dist p y = d) := by
          intro y hy
          have hyB : y ∈ Bgood := (Finset.mem_filter.mp hy).1
          have hyA : y ∈ B := (Finset.mem_filter.mp hyB).1
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hyA).1, (Finset.mem_filter.mp hy).2⟩
        exact le_trans (Finset.card_le_card hsub) (hG p hpA d)
      have hsum : Bgood.card = ∑ d ∈ Sdist, (Bgood.filter (fun y => dist p y = d)).card :=
        Finset.card_eq_sum_card_fiberwise (f := fun y => dist p y) (t := Sdist)
          (fun y hy => Finset.mem_image_of_mem _ hy)
      have hb : Bgood.card ≤ Sdist.card * G := by
        rw [hsum]
        calc ∑ d ∈ Sdist, (Bgood.filter (fun y => dist p y = d)).card
            ≤ ∑ d ∈ Sdist, G := Finset.sum_le_sum hfib
          _ = Sdist.card * G := by simp [Finset.sum_const, smul_eq_mul]
      have : k * G ≤ Sdist.card * G := by omega
      exact Nat.le_of_mul_le_mul_right this hGpos
    have hSdist_rare : Sdist ⊆ rareDistances A := by
      intro d hd
      obtain ⟨y, hyBgood, rfl⟩ := Finset.mem_image.mp hd
      have hyB : y ∈ B := (Finset.mem_filter.mp hyBgood).1
      have hyA : y ∈ A := (Finset.mem_filter.mp hyB).1
      have hgt : W < dist p y := (Finset.mem_filter.mp hyBgood).2
      have hyp : y ≠ p := by
        intro h; rw [h] at hgt; simp at hgt; linarith
      show dist p y ∈ rareDistances A
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(p, y),
        Finset.mem_offDiag.mpr ⟨hpA, hyA, (Ne.symm hyp)⟩, rfl⟩, ?_, ?_⟩
      · exact one_le_pairMultiplicity ⟨(p, y), Finset.mem_offDiag.mpr ⟨hpA, hyA, (Ne.symm hyp)⟩, rfl⟩
      · exact pairMultiplicity_le_card A m L hm hL hLm hWmax hgt
    calc k ≤ Sdist.card := hSdist_card
      _ ≤ (rareDistances A).card := Finset.card_le_card hSdist_rare

end E132Count

namespace E132Count

open OMA.S_erdos_132 in
/-- The counting lemma: `k * G * L ≤ |A|` forces at least `k` rare distances. -/
theorem key (A : Finset Pt) (G L k : ℕ) (hcard : 2 ≤ A.card)
    (hG : ∀ p ∈ A, ∀ d : ℝ, (A.filter (fun q => dist p q = d)).card ≤ G)
    (hL : ∀ d : ℝ, ((A.offDiag.filter (fun p => dist p.1 p.2 = d)).image
      (fun p => p.1 - p.2)).card ≤ L)
    (hk : k * G * L ≤ A.card) :
    k ≤ (rareDistances A).card := by
  classical
  by_cases hk0 : k = 0
  · simp [hk0]
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
  obtain ⟨x0, hx0, y0, hy0, hx0y0⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
  have hGpos : 0 < G := by
    have h1 : 1 ≤ (A.filter (fun r => dist x0 r = dist x0 y0)).card :=
      Finset.card_pos.mpr ⟨y0, Finset.mem_filter.mpr ⟨hy0, rfl⟩⟩
    have h2 := hG x0 hx0 (dist x0 y0)
    omega
  have hL2 : 2 ≤ L := by
    set IMG := (A.offDiag.filter (fun p => dist p.1 p.2 = dist x0 y0)).image
      (fun p => p.1 - p.2) with hIMG
    have hmem1 : x0 - y0 ∈ IMG := Finset.mem_image.mpr ⟨(x0, y0),
      Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hx0, hy0, hx0y0⟩, rfl⟩, rfl⟩
    have hmem2 : y0 - x0 ∈ IMG := Finset.mem_image.mpr ⟨(y0, x0),
      Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hy0, hx0, (Ne.symm hx0y0)⟩,
        dist_comm y0 x0⟩, rfl⟩
    have hne : x0 - y0 ≠ y0 - x0 := by
      intro h
      have h2 : (2:ℝ) • (x0 - y0) = 0 := by
        rw [two_smul]
        nth_rewrite 2 [h]
        abel
      have h3 : x0 - y0 = 0 := by
        rcases smul_eq_zero.mp h2 with h4 | h4
        · exact absurd h4 (by norm_num)
        · exact h4
      exact hx0y0 (sub_eq_zero.mp h3)
    have hpair : ({x0 - y0, y0 - x0} : Finset Pt).card = 2 := Finset.card_pair hne
    have hsub : ({x0 - y0, y0 - x0} : Finset Pt) ⊆ IMG := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hmem1
      · exact hmem2
    calc (2:ℕ) = ({x0 - y0, y0 - x0} : Finset Pt).card := hpair.symm
      _ ≤ IMG.card := Finset.card_le_card hsub
      _ ≤ L := hL (dist x0 y0)
  -- the two easy cases where all distances are rare
  by_cases hL2eq : L = 2
  · have hrare := all_rare_of_two A hcard (by simpa [hL2eq] using hL)
    rw [hrare]
    have hge := card_dist_image_ge A G hcard hG hx0
    have hkg : k * G ≤ A.card - 1 := by
      have h2 : k * G * 2 ≤ A.card := by rw [← hL2eq]; exact hk
      omega
    have hk_le : k ≤ (A.card - 1) / G := by
      rw [Nat.le_div_iff_mul_le hGpos]
      exact hkg
    exact le_trans hk_le hge
  by_cases hG1 : G = 1
  · have hrare := all_rare_of_one A hcard (by simpa [hG1] using hG)
    rw [hrare]
    have hge := card_dist_image_ge A G hcard hG hx0
    have hkg : k * 1 ≤ A.card - 1 := by
      have h2 : k * 1 * L ≤ A.card := by rw [← hG1]; exact hk
      have h3 : 2 ≤ L := hL2
      have h4 : k * 2 ≤ A.card := le_trans (Nat.mul_le_mul_left k h3) (by simpa using h2)
      omega
    have hk_le : k ≤ (A.card - 1) / G := by
      rw [Nat.le_div_iff_mul_le hGpos]
      simpa [hG1] using hkg
    exact le_trans hk_le hge
  · -- main case: L ≥ 3 and G ≥ 2
    have hL3 : 3 ≤ L := by omega
    have hG2 : 2 ≤ G := by omega
    have hcard6 : 6 ≤ A.card := by
      have h1 : 1 * 2 ≤ k * G := Nat.mul_le_mul hk1 hG2
      have h2 : (1 * 2) * 3 ≤ k * G * L := Nat.mul_le_mul h1 hL3
      omega
    set m := A.card / L with hmdef
    have hLm : L * m ≤ A.card := by
      rw [hmdef, Nat.mul_comm]
      exact Nat.div_mul_le_self _ _
    have hkG : k * G ≤ m := by
      rw [hmdef, Nat.le_div_iff_mul_le (by omega : 0 < L)]
      exact hk
    exact main_case A G L k m hcard6 hG hL hL3 hk1 hkG hmdef hLm

end E132Count

theorem OMA.solution : OMA.R_erdos_132_R1_H2_R1_H2_R1.H1 := by
  intro A G L k hcard hG hL hk
  exact E132Count.key A G L k hcard hG hL hk
