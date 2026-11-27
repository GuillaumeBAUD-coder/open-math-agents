import FormalConjectures.ErdosProblems.«725»
import Mathlib

-- Credit: @ivillar for the corollary below. The counting part (namespace LatinCount) is the merged proof
-- of Erdos725.erdos_725.variants.yamamoto by @marcusbuffett (PR #3568), reused verbatim.
-- Erdos-Kaplansky follows from asymptotic_of_sparse: k = o((log n)^(3/2 - eps)) and
-- (log n)^a = o(n^(1/3)), so k(n)/n^(1/3) tends to 0.

/-!
# Asymptotic enumeration of sparse Latin rectangles

Credit: @marcusbuffett. Two switches on permutations bound the effect of forbidding a cell.
Multiplying these bounds over the occupied cells and the rows gives a uniform error estimate.
-/

namespace LatinCount

open Finset
open scoped Classical

private abbrev Perm (n : ℕ) := Equiv.Perm (Fin n)
private abbrev Board (n : ℕ) := Finset (Fin n × Fin n)

private noncomputable def row {n} (F : Board n) (i : Fin n) := univ.filter fun j => (i,j) ∈ F
private noncomputable def col {n} (F : Board n) (j : Fin n) := univ.filter fun i => (i,j) ∈ F
private def Sparse {n} (F : Board n) (r : ℕ) := (∀ i, (row F i).card ≤ r) ∧ ∀ j, (col F j).card ≤ r
private noncomputable def avoids {n} (F : Board n) := (univ : Finset (Perm n)).filter
  fun p => ∀ i, (i,p i) ∉ F

private noncomputable def safe {n} (F : Board n) (p : Perm n) (i j : Fin n) :=
  univ \ ((univ.filter fun z => (i,p z) ∈ F) ∪ col F j)

private lemma mem_safe {n} {F : Board n} {p : Perm n} {i j z : Fin n} :
    z ∈ safe F p i j ↔ (i,p z) ∉ F ∧ (z,j) ∉ F := by
  simp [safe,col]

private lemma safe_card {n r} {F : Board n} (h : Sparse F r) (p : Perm n) (i j : Fin n) :
    n-2*r ≤ (safe F p i j).card := by
  let B := univ.filter fun z => (i,p z) ∈ F
  have hb : B.card ≤ (row F i).card :=
    card_le_card_of_injOn p (fun x hx => by simpa [B,row] using hx) p.injective.injOn
  have hc := card_union_le B (col F j)
  have hu : (safe F p i j).card = n-(B ∪ col F j).card := by
    unfold safe
    rw [card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin]
  rw [hu]
  have h1 := h.1 i
  have h2 := h.2 j
  omega

private lemma count_choices {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (t : α → Finset β) (u : Finset γ) (k : ℕ)
    (ht : ∀ a ∈ s, k ≤ (t a).card) (f : (Σ _ : α, β) → γ)
    (hf : ∀ a ∈ s, ∀ b ∈ t a, f ⟨a,b⟩ ∈ u)
    (hinj : ∀ a ∈ s, ∀ b ∈ t a, ∀ a' ∈ s, ∀ b' ∈ t a',
      f ⟨a,b⟩ = f ⟨a',b'⟩ → a = a' ∧ b = b') : s.card*k ≤ u.card := by
  calc
    _ = ∑ _ ∈ s, k := by simp
    _ ≤ (s.sigma t).card := by rw [card_sigma]; exact sum_le_sum ht
    _ ≤ _ := by
      apply card_le_card_of_injOn f
      · rintro ⟨a,b⟩ hab
        exact hf a (mem_sigma.mp hab).1 b (mem_sigma.mp hab).2
      · rintro ⟨a,b⟩ hab ⟨a',b'⟩ hab' he
        obtain ⟨rfl,rfl⟩ := hinj a (mem_sigma.mp hab).1 b (mem_sigma.mp hab).2
          a' (mem_sigma.mp hab').1 b' (mem_sigma.mp hab').2 he
        rfl

private lemma switches {n r : ℕ} (F : Board n) (hF : Sparse F r) (i j : Fin n)
    (hij : (i,j) ∉ F) :
    let U := (avoids F).filter (fun p => p i = j)
    let B := (avoids F).filter (fun p => p i ≠ j)
    U.card*(n-2*r) ≤ (avoids F).card ∧ B.card*(n-2*r-2) ≤ U.card*n^2 := by
  classical
  dsimp only
  let U := (avoids F).filter (fun p => p i = j)
  let B := (avoids F).filter (fun p => p i ≠ j)
  change U.card * _ ≤ _ ∧ B.card * _ ≤ U.card * _
  constructor
  · apply count_choices U (fun p => safe F p i j) (avoids F) _ (fun p _ => safe_card hF p i j)
      (fun v => v.1 * Equiv.swap i v.2)
    · intro p hp z hz
      obtain ⟨hal,he⟩ := mem_filter.mp hp
      obtain ⟨hs,ht⟩ := mem_safe.mp hz
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      intro a
      change (a,p (Equiv.swap i z a)) ∉ F
      by_cases h : a = i
      · simpa [h] using hs
      by_cases h' : a = z
      · simpa [h',he] using ht
      simpa [Equiv.swap_apply_of_ne_of_ne h h'] using (mem_filter.mp hal).2 a
    · intro p hp z _ q hq w _ e
      have hpj := (mem_filter.mp hp).2
      have hqj := (mem_filter.mp hq).2
      change p*Equiv.swap i z = q*Equiv.swap i w at e
      have hz : (p*Equiv.swap i z) z = j := by simp [Equiv.Perm.mul_apply,hpj]
      have hw : (q*Equiv.swap i w) w = j := by simp [Equiv.Perm.mul_apply,hqj]
      rw [e] at hz
      have eq := (q*Equiv.swap i w).injective (hz.trans hw.symm)
      subst w
      exact ⟨mul_right_cancel e,rfl⟩
  · let good (p : Perm n) := ((safe F p (p.symm j) (p i)).erase i).erase (p.symm j)
    let cycle (y z : Fin n) : Perm n := Equiv.swap i y * Equiv.swap y z
    let target := (U ×ˢ (univ : Finset (Fin n))) ×ˢ (univ : Finset (Fin n))
    have hcard : target.card = U.card*n^2 := by simp [target,pow_two,Nat.mul_assoc]
    rw [← hcard]
    refine count_choices B good target (n-2*r-2) ?_ (fun v => ((v.1 * cycle (v.1.symm j) v.2, v.1.symm j),v.2)) ?_ ?_
    · intro p _
      have h := safe_card hF p (p.symm j) (p i)
      have h' := Finset.pred_card_le_card_erase (s := safe F p (p.symm j) (p i)) (a := i)
      have h'' := Finset.pred_card_le_card_erase (s := (safe F p (p.symm j) (p i)).erase i) (a := p.symm j)
      dsimp [good]
      omega
    · intro p hp z hz
      let y := p.symm j
      have py : p y = j := p.apply_symm_apply _
      have yi : y ≠ i := fun e => (mem_filter.mp hp).2 (e ▸ py)
      obtain ⟨zy,hz⟩ := mem_erase.mp hz
      obtain ⟨zi,hz⟩ := mem_erase.mp hz
      obtain ⟨hy,hz'⟩ := mem_safe.mp hz
      change z ≠ y at zy
      change (y,p z) ∉ F at hy
      have consume : (p * cycle y z) i = j := by
        simp [cycle, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne yi.symm zi.symm,py]
      change ((p * cycle y z,y),z) ∈ (U ×ˢ univ) ×ˢ univ
      refine mem_product.mpr ⟨mem_product.mpr ⟨?_,mem_univ _⟩,mem_univ _⟩
      change p * cycle y z ∈ (avoids F).filter (fun q => q i = j)
      refine mem_filter.mpr ⟨?_,consume⟩
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      intro a
      by_cases ai : a=i
      · simpa only [ai,consume] using hij
      by_cases ay : a=y
      · subst a
        simpa [cycle,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne zi zy] using hy
      by_cases az : a=z
      · subst a
        simpa [cycle,Equiv.Perm.mul_apply] using hz'
      simpa [cycle,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne ay az,
        Equiv.swap_apply_of_ne_of_ne ai ay] using (mem_filter.mp (mem_filter.mp hp).1).2 a
    · intro p _ z _ q _ w _ e
      have hz : z=w := congrArg Prod.snd e
      have hy : p.symm j=q.symm j := congrArg (fun v => v.1.2) e
      have hm : p*cycle (p.symm j) z = q*cycle (q.symm j) w := congrArg (fun v => v.1.1) e
      rw [hz,hy] at hm
      exact ⟨mul_right_cancel hm,hz⟩


private noncomputable def lo (n r : ℕ) : ℝ := 1-1/(n-2*(r:ℝ))
private noncomputable def hi (n r : ℕ) : ℝ := 1-(n-2*(r:ℝ)-2)/((n:ℝ)^2+n)

private lemma lo_nonneg {n r} (h : 10*(r+1) ≤ n) : 0 ≤ lo n r := by
  have h' : 10*((r:ℝ)+1) ≤ n := by exact_mod_cast h
  dsimp [lo]
  have hp : 0 < (n:ℝ)-2*r := by linarith
  apply sub_nonneg.mpr
  exact (div_le_one hp).2 (by linarith)

private lemma hi_nonneg {n r} (h : 10*(r+1) ≤ n) : 0 ≤ hi n r := by
  have hn : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  dsimp [hi]
  apply sub_nonneg.mpr
  apply (div_le_one (by positivity : 0 < (n:ℝ)^2+n)).2
  nlinarith [sq_nonneg (n:ℝ),Nat.cast_nonneg (α:=ℝ) r]

private lemma sparse_mono {n r} {F G : Board n} (h : F ⊆ G) (hg : Sparse G r) : Sparse F r := by
  constructor
  · intro i
    exact (card_le_card (fun _ hx => mem_filter.mpr ⟨mem_univ _, h (mem_filter.mp hx).2⟩)).trans (hg.1 i)
  · intro j
    exact (card_le_card (fun _ hx => mem_filter.mpr ⟨mem_univ _, h (mem_filter.mp hx).2⟩)).trans (hg.2 j)

private lemma add_cell {n r : ℕ} (F : Board n) (hF : Sparse F r) (hn : 10*(r+1) ≤ n)
    (i j : Fin n) (fresh : (i,j) ∉ F) :
    lo n r * (avoids F).card ≤ ((avoids (insert (i,j) F)).card : ℝ) ∧
    ((avoids (insert (i,j) F)).card : ℝ) ≤ hi n r * (avoids F).card := by
  classical
  let U := (avoids F).filter (fun p => p i = j)
  let B := (avoids F).filter (fun p => p i ≠ j)
  have he : avoids (insert (i,j) F) = B := by
    ext p
    simp only [avoids,B,mem_filter,mem_univ,true_and,mem_insert,Prod.mk.injEq,not_or]
    constructor
    · intro h
      exact ⟨fun x => (h x).2, fun e => (h i).1 ⟨rfl,e⟩⟩
    · rintro ⟨h,h'⟩ x
      exact ⟨fun ⟨e,e'⟩ => h' (e ▸ e'),h x⟩
  rw [he]
  have hadd : (U.card:ℝ) + B.card = (avoids F).card := by
    exact_mod_cast (card_filter_add_card_filter_not (s := avoids F) (fun p => p i = j))
  obtain ⟨ha,hb⟩ := switches F hF i j fresh
  change U.card * _ ≤ _ at ha
  change B.card * _ ≤ U.card * _ at hb
  have h1 : 2*r ≤ n := by omega
  have h2 : 2 ≤ n-2*r := by omega
  have ha' : (U.card:ℝ) * (n-2*(r:ℝ)) ≤ (avoids F).card := by
    have hc : ((U.card*(n-2*r):ℕ):ℝ) ≤ (avoids F).card := by exact_mod_cast ha
    simpa [Nat.cast_sub h1] using hc
  have hb' : (B.card:ℝ) * (n-2*(r:ℝ)-2) ≤ U.card*(n:ℝ)^2 := by
    have hc : ((B.card*(n-2*r-2):ℕ):ℝ) ≤ ((U.card*n^2:ℕ):ℝ) := by exact_mod_cast hb
    simpa [Nat.cast_sub h1,Nat.cast_sub h2] using hc
  have hpos : 0 < (n:ℝ)-2*r := by
    have h3 : (2:ℝ)*r < n := by exact_mod_cast (show 2*r < n by omega)
    linarith
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  constructor
  · rw [lo,sub_mul,one_mul,one_div,inv_mul_eq_div]
    have := (le_div_iff₀ hpos).2 ha'
    linarith
  · rw [hi,sub_mul,one_mul,div_mul_eq_mul_div]
    apply (le_sub_comm.mp ?_)
    apply (div_le_iff₀ (by positivity : 0 < (n:ℝ)^2+n)).2
    rw [← hadd]
    nlinarith [show 0 ≤ (U.card:ℝ)*(2*r+2) by positivity]

private lemma board_bounds {n r : ℕ} (hn : 10*(r+1) ≤ n) (F : Board n) (h : Sparse F r) :
    (n.factorial:ℝ) * lo n r ^ F.card ≤ (avoids F).card ∧
    ((avoids F).card:ℝ) ≤ n.factorial * hi n r ^ F.card := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    simp [avoids,Fintype.card_perm]
  | @insert a F ha ih =>
    obtain ⟨i,j⟩ := a
    have hf := sparse_mono (subset_insert (i,j) F) h
    obtain ⟨h1,h2⟩ := ih hf
    obtain ⟨s1,s2⟩ := add_cell F hf hn i j ha
    rw [card_insert_of_notMem ha,pow_succ,pow_succ]
    constructor
    · calc
        _ = lo n r * ((n.factorial:ℝ) * lo n r ^ F.card) := by ring
        _ ≤ _ := (mul_le_mul_of_nonneg_left h1 (lo_nonneg hn)).trans s1
    · calc
        _ ≤ hi n r * ((n.factorial:ℝ) * hi n r ^ F.card) :=
          s2.trans (mul_le_mul_of_nonneg_left h2 (hi_nonneg hn))
        _ = _ := by ring



open Erdos725

private abbrev Rect (r n : ℕ) := {M : Fin r → Fin n → Fin n // IsLatinRectangle M}

private noncomputable def permRow {r n} (M : Rect r n) (a : Fin r) : Perm n :=
  Equiv.ofBijective (M.val a) (Finite.injective_iff_bijective.1 (M.property.1 a))

private noncomputable def used {r n} (M : Rect r n) : Board n :=
  univ.image fun x : Fin r × Fin n => (x.2,M.val x.1 x.2)

private lemma mem_used {r n} {M : Rect r n} {i j : Fin n} :
    (i,j) ∈ used M ↔ ∃ a, M.val a i = j := by
  classical
  simp only [used,mem_image,mem_univ,true_and,Prod.exists,Prod.mk.injEq]
  aesop

private lemma used_card {r n} (M : Rect r n) : (used M).card = n*r := by
  classical
  unfold used
  rw [card_image_of_injective]
  · simp [Nat.mul_comm]
  · rintro ⟨a,i⟩ ⟨b,j⟩ h
    obtain ⟨rfl,he⟩ := Prod.mk.inj h
    obtain rfl := M.property.2 i he
    rfl

private lemma used_sparse {r n} (M : Rect r n) : Sparse (used M) r := by
  classical
  constructor
  · intro i
    have h : row (used M) i ⊆ univ.image (fun a => M.val a i) := by
      intro j hj
      obtain ⟨a,ha⟩ := mem_used.mp (mem_filter.mp hj).2
      exact mem_image.mpr ⟨a,mem_univ _,ha⟩
    exact (card_le_card h).trans (by simpa using (card_image_le (s := univ) (f := fun a => M.val a i)))
  · intro j
    have h : col (used M) j ⊆ univ.image (fun a => (permRow M a).symm j) := by
      intro i hi
      obtain ⟨a,ha⟩ := mem_used.mp (mem_filter.mp hi).2
      exact mem_image.mpr ⟨a,mem_univ _,(permRow M a).symm_apply_eq.mpr ha.symm⟩
    exact (card_le_card h).trans (by simpa using (card_image_le (s := univ) (f := fun a => (permRow M a).symm j)))

private def tailRect {r n} (M : Rect (r+1) n) : Rect r n :=
  ⟨fun a => M.val a.succ,fun a => M.property.1 _,fun i => (M.property.2 i).comp (Fin.succ_injective _)⟩

private noncomputable def splitRect {r n} (M : Rect (r+1) n) :
    Σ T : Rect r n, ↥(avoids (used T)) := by
  refine ⟨tailRect M, permRow M 0,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
  intro i h
  obtain ⟨a,ha⟩ := mem_used.mp h
  have he : M.val a.succ i = M.val 0 i := ha
  exact Fin.succ_ne_zero a (M.property.2 i he)

private def joinRect {r n} (x : Σ T : Rect r n, ↥(avoids (used T))) : Rect (r+1) n := by
  rcases x with ⟨M,p,hp⟩
  refine ⟨Fin.cons (α := fun _ => Fin n → Fin n) (p : Fin n → Fin n) M.val,?_,?_⟩
  · intro a
    cases a using Fin.cases with
    | zero => exact p.injective
    | succ a => exact M.property.1 a
  · intro i
    have he : (fun a => Fin.cons (α := fun _ => Fin n → Fin n) (p : Fin n → Fin n) M.val a i) =
        Fin.cons (p i) (fun a => M.val a i) := by
      funext a
      cases a using Fin.cases <;> rfl
    rw [he,Fin.cons_injective_iff]
    exact ⟨fun ⟨a,ha⟩ => (mem_filter.mp hp).2 i (mem_used.mpr ⟨a,ha⟩),M.property.2 i⟩

private noncomputable def extendEquiv (r n : ℕ) :
    Rect (r+1) n ≃ Σ T : Rect r n, ↥(avoids (used T)) where
  toFun := splitRect
  invFun := joinRect
  left_inv := by
    intro M
    apply Subtype.ext
    funext a
    cases a using Fin.cases <;> rfl
  right_inv := by
    rintro ⟨T,p,hp⟩
    apply Sigma.ext (by rfl)
    apply heq_of_eq
    apply Subtype.ext
    exact Equiv.ext fun _ => rfl

private lemma recurrence (r n : ℕ) :
    (L (r+1) n : ℝ) = ∑ M : Rect r n, ((avoids (used M)).card:ℝ) := by
  classical
  unfold L
  rw [Nat.card_congr (extendEquiv r n),Nat.card_eq_fintype_card,Fintype.card_sigma,Nat.cast_sum]
  simp

private lemma zero_rows (n : ℕ) : L 0 n = 1 := by
  let e : Rect 0 n ≃ Unit := {
    toFun := fun _ => ()
    invFun := fun _ => ⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i,fun _ a => Fin.elim0 a⟩
    left_inv := fun _ => Subtype.ext (funext fun i => Fin.elim0 i)
    right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (by simp)



private lemma rectangle_bounds {n k : ℕ} (hn : 10*(k+1) ≤ n) (r : ℕ) (hr : r ≤ k) :
    (n.factorial:ℝ)^r * lo n k ^ (n*r.choose 2) ≤ L r n ∧
    (L r n:ℝ) ≤ (n.factorial:ℝ)^r * hi n k ^ (n*r.choose 2) := by
  classical
  induction r with
  | zero => simp [zero_rows]
  | succ r ih =>
    have hr' : r ≤ k := by omega
    obtain ⟨lh,uh⟩ := ih hr'
    have bounds (M : Rect r n) := board_bounds hn (used M)
      (show Sparse (used M) k from
        ⟨fun i => ((used_sparse M).1 i).trans hr', fun j => ((used_sparse M).2 j).trans hr'⟩)
    simp only [used_card] at bounds
    have cardR : (Fintype.card (Rect r n):ℝ) = L r n := by
      rw [L,Nat.card_eq_fintype_card]
    have l : (L r n:ℝ) * (n.factorial * lo n k ^ (n*r)) ≤ L (r+1) n := by
      rw [recurrence,← cardR]
      simpa using (sum_le_sum (s := (univ : Finset (Rect r n))) (fun M _ => (bounds M).1))
    have u : (L (r+1) n:ℝ) ≤ L r n * (n.factorial * hi n k ^ (n*r)) := by
      rw [recurrence,← cardR]
      simpa using (sum_le_sum (s := (univ : Finset (Rect r n))) (fun M _ => (bounds M).2))
    have e : n*((r+1).choose 2) = n*r.choose 2+n*r := by
      rw [Nat.choose_succ_succ,Nat.choose_one_right]
      ring
    simp only [e,pow_add,pow_succ]
    constructor
    · calc
        _ = ((n.factorial:ℝ)^r * lo n k ^ (n*r.choose 2)) *
            (n.factorial * lo n k ^ (n*r)) := by ring
        _ ≤ _ := (mul_le_mul_of_nonneg_right lh (mul_nonneg (by positivity)
          (pow_nonneg (lo_nonneg hn) _))).trans l
    · calc
        _ ≤ ((n.factorial:ℝ)^r * hi n k ^ (n*r.choose 2)) *
            (n.factorial * hi n k ^ (n*r)) := u.trans
            (mul_le_mul_of_nonneg_right uh (mul_nonneg (by positivity) (pow_nonneg (hi_nonneg hn) _)))
        _ = _ := by ring



private lemma positive_rates {n k : ℕ} (hn : 10*(k+1) ≤ n) : 0 < lo n k ∧ 0 < hi n k := by
  have h : 10*((k:ℝ)+1) ≤ n := by exact_mod_cast hn
  have hk := Nat.cast_nonneg (α := ℝ) k
  have hp : 0 < (n:ℝ) := by linarith
  constructor
  · unfold lo
    exact sub_pos.mpr ((div_lt_one (by linarith : 0 < (n:ℝ)-2*k)).2 (by linarith))
  · unfold hi
    exact sub_pos.mpr ((div_lt_one (by positivity : 0 < (n:ℝ)^2+n)).2 (by nlinarith [sq_nonneg (n:ℝ)]))

private lemma log_rates {n k : ℕ} (hn : 10*(k+1) ≤ n) :
    -(4*((k:ℝ)+1)/n) ≤ 1+n*Real.log (lo n k) ∧
    1+n*Real.log (hi n k) ≤ 4*((k:ℝ)+1)/n := by
  have h : 10*((k:ℝ)+1) ≤ n := by exact_mod_cast hn
  have hk := Nat.cast_nonneg (α := ℝ) k
  have hp : 0 < (n:ℝ) := by linarith
  have d : 0 < (n:ℝ)-2*k-1 := by linarith
  have d' : 0 < (n:ℝ)-2*k := by linarith
  obtain ⟨pl,pu⟩ := positive_rates hn
  constructor
  · have e : 1-(lo n k)⁻¹ = -1/((n:ℝ)-2*k-1) := by
      unfold lo
      field_simp
      <;> nlinarith
    have lower := Real.one_sub_inv_le_log_of_pos pl
    rw [e] at lower
    have fac : (n:ℝ) ≤ 2*(n-2*(k:ℝ)-1) := by linarith
    have aux := mul_le_mul_of_nonneg_right fac (show 0 ≤ 2*(k:ℝ)+1 by positivity)
    calc
      _ ≤ -((2*(k:ℝ)+1)/(n-2*(k:ℝ)-1)) := by
        apply neg_le_neg
        apply (div_le_div_iff₀ d hp).2
        nlinarith
      _ = 1 + (n:ℝ) * (-1/(n-2*(k:ℝ)-1)) := by field_simp [d.ne']; ring
      _ ≤ _ := by gcongr
  · have upper := Real.log_le_sub_one_of_pos pu
    calc
      _ ≤ 1+(n:ℝ)*(hi n k-1) := by gcongr
      _ = (2*(k:ℝ)+3)/(n+1) := by
        unfold hi
        field_simp
        <;> ring
      _ ≤ _ := by
        apply (div_le_div_iff₀ (by positivity) hp).2
        nlinarith [mul_nonneg hp.le hk]

private lemma ratio_bounds {n k : ℕ} (hn : 10*(k+1) ≤ n) :
    let E := 4*((k:ℝ)+1)^3/n
    let R := (L k n:ℝ)/(Real.exp (-(k.choose 2:ℝ))*(n.factorial:ℝ)^k)
    Real.exp (-E) ≤ R ∧ R ≤ Real.exp E := by
  dsimp only
  let C : ℝ := k.choose 2
  let A : ℝ := (n.factorial:ℝ)^k
  have hA : 0 < A := by dsimp [A]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hp : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hk := Nat.cast_nonneg (α := ℝ) k
  have hc2 : C ≤ (k:ℝ)^2 := by dsimp [C]; exact_mod_cast Nat.choose_le_pow k 2
  have hE : C*(4*((k:ℝ)+1)/n) ≤ 4*((k:ℝ)+1)^3/n := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hp.le
    nlinarith [mul_le_mul_of_nonneg_right hc2 (show 0 ≤ 4*((k:ℝ)+1) by positivity),sq_nonneg (k:ℝ)]
  have power (x : ℝ) (hx : 0 < x) :
      Real.exp (C*(1+n*Real.log x)) = x^(n*k.choose 2)/Real.exp (-C) := by
    rw [show C*(1+n*Real.log x) = (n*k.choose 2:ℕ)*Real.log x + C by dsimp [C]; push_cast; ring,
      Real.exp_add,Real.exp_nat_mul,Real.exp_log hx,Real.exp_neg,div_inv_eq_mul]
  obtain ⟨l,u⟩ := rectangle_bounds hn k le_rfl
  obtain ⟨pl,pu⟩ := positive_rates hn
  obtain ⟨ll,lu⟩ := log_rates hn
  change Real.exp _ ≤ (L k n:ℝ)/(Real.exp (-C)*A) ∧ (L k n:ℝ)/(Real.exp (-C)*A) ≤ Real.exp _
  have denom := mul_pos (Real.exp_pos (-C)) hA
  constructor
  · calc
      _ ≤ Real.exp (C*(1+n*Real.log (lo n k))) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left ll hC]
      _ = _ := power _ pl
      _ ≤ _ := by
        apply (div_le_div_iff₀ (Real.exp_pos _) denom).2
        calc
          _ = (A*lo n k^(n*k.choose 2))*Real.exp (-C) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right l (Real.exp_pos _).le
  · calc
      _ ≤ hi n k^(n*k.choose 2)/Real.exp (-C) := by
        apply (div_le_div_iff₀ denom (Real.exp_pos _)).2
        calc
          _ ≤ (A*hi n k^(n*k.choose 2))*Real.exp (-C) := mul_le_mul_of_nonneg_right u (Real.exp_pos _).le
          _ = _ := by ring
      _ = _ := (power _ pu).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        exact (mul_le_mul_of_nonneg_left lu hC).trans hE



open Filter Asymptotics
open scoped Topology

theorem asymptotic_of_sparse (k : ℕ → ℕ)
    (hk : Tendsto (fun n : ℕ => (k n:ℝ)/(n:ℝ)^(1/3:ℝ)) atTop (𝓝 0)) :
    (fun n => (L (k n) n:ℝ)) ~[atTop] fun n =>
      Real.exp (-((k n).choose 2:ℝ))*(n.factorial:ℝ)^(k n) := by
  have hrec : Tendsto (fun n : ℕ => 1/(n:ℝ)^(1/3:ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def,Real.rpow_neg,one_div] using
      (tendsto_rpow_neg_atTop (by norm_num : 0 < (1/3:ℝ))).comp
        (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hc : Tendsto (fun n : ℕ => ((k n:ℝ)+1)^3/n) atTop (𝓝 0) := by
    have h3 := (hk.add hrec).pow 3
    rw [zero_add,show (0:ℝ)^3=0 by norm_num] at h3
    apply h3.congr'
    filter_upwards with n
    rw [← add_div,div_pow,← Real.rpow_natCast ((n:ℝ)^(1/3:ℝ)) 3,← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  have hsmall : ∀ᶠ n in atTop, 10*(k n+1) ≤ n := by
    filter_upwards [hc.eventually_lt_const (by norm_num : (0:ℝ)<1/10),
      eventually_ge_atTop 1] with n h hn
    have hp : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
    have h' := (div_lt_iff₀ hp).mp h
    have hk' := Nat.cast_nonneg (α := ℝ) (k n)
    have hs : (k n:ℝ)+1 ≤ ((k n:ℝ)+1)^3 := by
      nlinarith [sq_nonneg (k n:ℝ),pow_nonneg hk' 3]
    exact_mod_cast (show 10*((k n:ℝ)+1) ≤ n by linarith)
  have hE : Tendsto (fun n : ℕ => 4*((k n:ℝ)+1)^3/n) atTop (𝓝 0) := by
    simpa only [mul_zero,mul_div_assoc] using hc.const_mul 4
  apply (isEquivalent_iff_tendsto_one (Eventually.of_forall fun n => by positivity)).2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (show Tendsto (fun n : ℕ => Real.exp (-(4*((k n:ℝ)+1)^3/n))) atTop (𝓝 1) by
      simpa [Function.comp_def] using (Real.continuous_exp.tendsto _).comp hE.neg)
    (show Tendsto (fun n : ℕ => Real.exp (4*((k n:ℝ)+1)^3/n)) atTop (𝓝 1) by
      simpa [Function.comp_def] using (Real.continuous_exp.tendsto _).comp hE)
  · exact hsmall.mono fun n hn => (ratio_bounds hn).1
  · exact hsmall.mono fun n hn => (ratio_bounds hn).2

theorem yamamoto : type_of% @Erdos725.erdos_725.variants.yamamoto := by
  intro δ hδ k hk
  apply asymptotic_of_sparse k
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hδ
  · filter_upwards with n
    positivity
  · filter_upwards [hk,eventually_ge_atTop 1] with n h hn
    have hp : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hp _)).2
    rw [sub_eq_add_neg,Real.rpow_add hp] at h
    simpa [mul_comm] using h.le


end LatinCount

open Filter Asymptotics in
theorem OMA.solution : type_of% @Erdos725.erdos_725.variants.erdos_kaplansky := by
  intro ε hε k hk
  apply LatinCount.asymptotic_of_sparse k
  have h1 : (fun n : ℕ => Real.log (n:ℝ) ^ (3/2 - ε)) =o[atTop] fun n : ℕ => (n:ℝ) ^ (1/3:ℝ) :=
    (isLittleO_log_rpow_rpow_atTop (3/2 - ε) (by norm_num : (0:ℝ) < 1/3)).comp_tendsto
      tendsto_natCast_atTop_atTop
  exact (hk.trans h1).tendsto_div_nhds_zero
