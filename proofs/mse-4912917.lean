import OMAStatements.S_mse_4912917

/-!
We use Saúl RM's dyadic coloring and back-and-forth construction
(https://mathoverflow.net/a/471059). The set consists of the irrational
pairs and the rational pairs of opposite dyadic type. For the absence
of straight segments we use an equally spaced triple on a rational
affine line, with both coordinate steps outside the dyadic subgroup.
-/

namespace AntiConvex

open Order

private def Colored {α β : Type*} [LinearOrder α] [LinearOrder β] (R : α → β → Prop) :=
  {f : PartialIso α β // ∀ p ∈ f.val, R p.1 p.2}

private instance {α β : Type*} [LinearOrder α] [LinearOrder β] (R : α → β → Prop) :
    Preorder (Colored R) := inferInstanceAs (Preorder {_f : PartialIso α β // _})

private def Colored.empty {α β : Type*} [LinearOrder α] [LinearOrder β] (R : α → β → Prop) :
    Colored R :=
  ⟨⟨∅, by simp⟩, by simp⟩

section
variable {α β : Type*} [LinearOrder α] [LinearOrder β] (R : α → β → Prop)

private theorem extend_left [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β]
    (denseR : ∀ a l u, l < u → ∃ b, l < b ∧ b < u ∧ R a b)
    (f : Colored R) (a : α) :
    ∃ g : Colored R, f ≤ g ∧ ∃ b : β, (a, b) ∈ g.val.val := by
  classical
  by_cases ha : ∃ b, (a, b) ∈ f.val.val
  · exact ⟨f, le_rfl, ha⟩
  let L := (f.val.val.filter (fun p => p.1 < a)).image Prod.snd
  let U := (f.val.val.filter (fun p => a < p.1)).image Prod.snd
  have hlu : ∀ l ∈ L, ∀ u ∈ U, l < u := by
    intro l hl u hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hu
    rw [Finset.mem_filter] at hp hq
    exact (lt_iff_lt_of_cmp_eq_cmp (f.val.prop _ hp.1 _ hq.1)).mp (hp.2.trans hq.2)
  obtain ⟨l, hlL, hlU⟩ := exists_between_finsets L U hlu
  obtain ⟨u, huL, huU⟩ := exists_between_finsets (insert l L) U (by
    intro x hx y hy
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hlU _ hy
    · exact hlu _ hx _ hy)
  obtain ⟨b, hlb, hbu, hab⟩ := denseR a l u (huL _ (Finset.mem_insert_self _ _))
  have hcmp : ∀ p ∈ f.val.val, cmp p.1 a = cmp p.2 b := by
    intro p hp
    have hpne : p.1 ≠ a := fun he => ha ⟨p.2, by simpa only [← he] using hp⟩
    rcases lt_or_gt_of_ne hpne with h | h
    · have hb : p.2 < b := (hlL _ (Finset.mem_image.mpr
          ⟨p, Finset.mem_filter.mpr ⟨hp, h⟩, rfl⟩)).trans hlb
      rw [← cmp_eq_lt_iff] at h hb
      exact h.trans hb.symm
    · have hb : b < p.2 := hbu.trans (huU _ (Finset.mem_image.mpr
          ⟨p, Finset.mem_filter.mpr ⟨hp, h⟩, rfl⟩))
      rw [← cmp_eq_gt_iff] at h hb
      exact h.trans hb.symm
  refine ⟨⟨⟨insert (a,b) f.val.val, ?_⟩, ?_⟩, ?_, ⟨b, Finset.mem_insert_self _ _⟩⟩
  · intro p hp q hq
    rcases Finset.mem_insert.mp hp with rfl | hp <;>
      rcases Finset.mem_insert.mp hq with rfl | hq
    · simp
    · exact cmp_eq_cmp_symm.mpr (hcmp _ hq)
    · exact hcmp _ hp
    · exact f.val.prop _ hp _ hq
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hab
    · exact f.prop _ hp
  · exact Finset.subset_insert _ _

private def Colored.flip (f : Colored R) : Colored (fun b a => R a b) :=
  ⟨f.val.comm, by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact f.prop _ hq⟩

private theorem extend_right [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α] [Nonempty α]
    (denseR : ∀ b l u, l < u → ∃ a, l < a ∧ a < u ∧ R a b)
    (f : Colored R) (b : β) :
    ∃ g : Colored R, f ≤ g ∧ ∃ a : α, (a, b) ∈ g.val.val := by
  classical
  obtain ⟨g, hfg, a, ha⟩ := extend_left (fun b a => R a b) denseR (f.flip R) b
  refine ⟨g.flip _, ?_, ⟨a, Finset.mem_image.mpr ⟨(b,a), ha, rfl⟩⟩⟩
  intro p hp
  have hp' : p.swap ∈ (f.flip R).val.val := Finset.mem_image.mpr ⟨p, hp, rfl⟩
  exact Finset.mem_image.mpr ⟨p.swap, hfg hp', by cases p; rfl⟩

private theorem colored_iso [Countable α] [Countable β] [DenselyOrdered α] [DenselyOrdered β]
    [NoMinOrder α] [NoMaxOrder α] [NoMinOrder β] [NoMaxOrder β] [Nonempty α] [Nonempty β]
    (left : ∀ a l u, l < u → ∃ b, l < b ∧ b < u ∧ R a b)
    (right : ∀ b l u, l < u → ∃ a, l < a ∧ a < u ∧ R a b) :
    ∃ e : α ≃o β, ∀ a, R a (e a) := by
  classical
  let := (nonempty_encodable α).some
  let := (nonempty_encodable β).some
  let dl (a : α) : Cofinal (Colored R) :=
    ⟨{f | ∃ b, (a,b) ∈ f.val.val}, fun f => by
      obtain ⟨g, hf, hg⟩ := extend_left R left f a
      exact ⟨g, hg, hf⟩⟩
  let dr (b : β) : Cofinal (Colored R) :=
    ⟨{f | ∃ a, (a,b) ∈ f.val.val}, fun f => by
      obtain ⟨g, hf, hg⟩ := extend_right R right f b
      exact ⟨g, hg, hf⟩⟩
  let C : α ⊕ β → Cofinal (Colored R) := Sum.elim dl dr
  let I := idealOfCofinals (Colored.empty R) C
  have hF (a : α) : ∃ b, ∃ f ∈ I, (a,b) ∈ f.val.val := by
    obtain ⟨f, ⟨b,hb⟩, hf⟩ := cofinal_meets_idealOfCofinals (Colored.empty R) C (Sum.inl a)
    exact ⟨b, f, hf, hb⟩
  have hG (b : β) : ∃ a, ∃ f ∈ I, (a,b) ∈ f.val.val := by
    obtain ⟨f, ⟨a,ha⟩, hf⟩ := cofinal_meets_idealOfCofinals (Colored.empty R) C (Sum.inr b)
    exact ⟨a, f, hf, ha⟩
  choose F hF using hF
  choose G hG using hG
  have hcmp (a : α) (b : β) : cmp a (G b) = cmp (F a) b := by
    obtain ⟨f,hf,ha⟩ := hF a
    obtain ⟨g,hg,hb⟩ := hG b
    obtain ⟨m,_,hmf,hmg⟩ := I.directed _ hf _ hg
    exact m.val.prop _ (hmf ha) _ (hmg hb)
  refine ⟨OrderIso.ofCmpEqCmp F G hcmp, fun a => ?_⟩
  obtain ⟨f,_,ha⟩ := hF a
  exact f.prop _ ha

end

end AntiConvex

namespace AntiConvex

open Set

private structure Strip (ι : Type*) where
  lo : ℝ
  hi : ℝ
  f : ι → ℝ
  inside : ∀ i, lo < f i ∧ f i < hi
  dense : ∀ u v, lo ≤ u → u < v → v ≤ hi → ∃ i, u < f i ∧ f i < v

namespace Strip

variable {ι : Type*}

private def compatible (A B : Strip ι) : Prop :=
  ∀ i j, A.f i < A.f j ↔ B.f i < B.f j

private theorem compatible_symm {A B : Strip ι} (h : A.compatible B) :
    B.compatible A := fun i j => (h i j).symm

private noncomputable def fill (A B : Strip ι) (x : ℝ) : ℝ :=
  sSup ({B.lo} ∪ {z | ∃ i, A.f i ≤ x ∧ B.f i = z})

private theorem fill_nonempty (A B : Strip ι) (x : ℝ) :
    ({B.lo} ∪ {z | ∃ i, A.f i ≤ x ∧ B.f i = z} : Set ℝ).Nonempty :=
  ⟨B.lo, Or.inl rfl⟩

private theorem fill_bdd (A B : Strip ι) (x : ℝ) (hB : B.lo ≤ B.hi) :
    BddAbove ({B.lo} ∪ {z | ∃ i, A.f i ≤ x ∧ B.f i = z} : Set ℝ) := by
  refine ⟨B.hi, ?_⟩
  rintro z (rfl | ⟨i, _, rfl⟩)
  · exact hB
  · exact (B.inside i).2.le

private theorem fill_mem (A B : Strip ι) (x : ℝ) (hB : B.lo ≤ B.hi) :
    A.fill B x ∈ Icc B.lo B.hi := by
  constructor
  · exact le_csSup (fill_bdd A B x hB) (Or.inl rfl)
  · apply csSup_le (fill_nonempty A B x)
    rintro z (rfl | ⟨i, _, rfl⟩)
    · exact hB
    · exact (B.inside i).2.le

private theorem fill_le (A B : Strip ι) (h : A.compatible B) {x : ℝ}
    (hx : x ∈ Icc A.lo A.hi) (i : ι) :
    A.fill B x ≤ B.f i ↔ x ≤ A.f i := by
  have hB := (B.inside i).1.le.trans (B.inside i).2.le
  constructor
  · intro hxi
    by_contra! hi
    obtain ⟨j, hij, hjx⟩ := A.dense _ _ (A.inside i).1.le hi hx.2
    exact ((h i j).mp hij).not_ge ((le_csSup (fill_bdd A B x hB)
      (Or.inr ⟨j, hjx.le, rfl⟩)).trans hxi)
  · intro hi
    apply csSup_le (fill_nonempty A B x)
    rintro z (rfl | ⟨j, hj, rfl⟩)
    · exact (B.inside i).1.le
    · exact le_of_not_gt (fun hji => ((h i j).mpr hji).not_ge (hj.trans hi))

private theorem eq_of_threshold (A : Strip ι) {x y : ℝ}
    (hx : x ∈ Icc A.lo A.hi) (hy : y ∈ Icc A.lo A.hi)
    (h : ∀ i, x ≤ A.f i ↔ y ≤ A.f i) : x = y := by
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · obtain ⟨i, hi, hi'⟩ := A.dense _ _ hx.1 hxy hy.2
    exact False.elim (hi'.not_ge ((h i).mp hi.le))
  · exact hxy
  · obtain ⟨i, hi, hi'⟩ := A.dense _ _ hy.1 hyx hx.2
    exact False.elim (hi'.not_ge ((h i).mpr hi.le))

private theorem fill_inv (A B : Strip ι) (h : A.compatible B)
    {x : ℝ} (hx : x ∈ Icc A.lo A.hi) (hB : B.lo ≤ B.hi) :
    B.fill A (A.fill B x) = x := by
  apply eq_of_threshold A (fill_mem B A _ (hx.1.trans hx.2)) hx
  intro i
  rw [fill_le B A (compatible_symm h) (fill_mem A B x hB) i, fill_le A B h hx i]

private theorem fill_strictMono (A B : Strip ι) (h : A.compatible B) :
    StrictMono (fun x : Icc A.lo A.hi => A.fill B x) := by
  intro x y hxy
  obtain ⟨i, hxi, hiy⟩ := A.dense _ _ x.2.1 hxy y.2.2
  exact (fill_le A B h x.2 i).2 hxi.le |>.trans_lt
    (lt_of_not_ge (fun hh => hiy.not_ge ((fill_le A B h y.2 i).1 hh)))

private noncomputable def fillIso (A B : Strip ι) (h : A.compatible B)
    (hA : A.lo ≤ A.hi) (hB : B.lo ≤ B.hi) : Icc A.lo A.hi ≃o Icc B.lo B.hi :=
  { toFun := fun x => ⟨A.fill B x, fill_mem A B _ hB⟩
    invFun := fun y => ⟨B.fill A y, fill_mem B A _ hA⟩
    left_inv := fun x => Subtype.ext (fill_inv A B h x.2 hB)
    right_inv := fun y => Subtype.ext (fill_inv B A (compatible_symm h) y.2 hA)
    map_rel_iff' := (fill_strictMono A B h).le_iff_le }

private theorem fill_node (A B : Strip ι) (h : A.compatible B) (i : ι) :
    A.fill B (A.f i) = B.f i := by
  have hx : A.f i ∈ Icc A.lo A.hi := ⟨(A.inside i).1.le, (A.inside i).2.le⟩
  have hB := (B.inside i).1.le.trans (B.inside i).2.le
  exact le_antisymm ((fill_le A B h hx i).2 le_rfl)
    (le_csSup (fill_bdd A B _ hB) (Or.inr ⟨i, le_rfl, rfl⟩))

private theorem fill_low (A B : Strip ι) (hB : B.lo ≤ B.hi) : A.fill B A.lo = B.lo := by
  apply le_antisymm _ (fill_mem A B _ hB).1
  apply csSup_le (fill_nonempty A B _)
  rintro z (rfl | ⟨i,hi,rfl⟩)
  · exact le_rfl
  · exact False.elim ((A.inside i).1.not_ge hi)

private theorem fill_high (A B : Strip ι) (h : A.compatible B)
    (hA : A.lo ≤ A.hi) (hB : B.lo ≤ B.hi) :
    A.fill B A.hi = B.hi := by
  apply eq_of_threshold B (fill_mem A B _ hB) ⟨hB, le_rfl⟩
  intro i
  rw [fill_le A B h ⟨hA, le_rfl⟩ i]
  exact ⟨fun ha => False.elim ((A.inside i).2.not_ge ha),
    fun hb => False.elim ((B.inside i).2.not_ge hb)⟩

end Strip

end AntiConvex

namespace AntiConvex

private def dyadic : AddSubgroup ℚ where
  carrier := {q | ∃ z : ℤ, ∃ n : ℕ, q = (z : ℚ) / 2 ^ n}
  zero_mem' := ⟨0, 0, by norm_num⟩
  add_mem' := by
    rintro x y ⟨u,m,rfl⟩ ⟨v,n,rfl⟩
    refine ⟨u*2^n + v*2^m,m+n, ?_⟩
    push_cast
    rw [pow_add]
    field_simp
  neg_mem' := by
    rintro x ⟨u,n,rfl⟩
    exact ⟨-u,n,by simp [neg_div]⟩

private theorem third_not_dyadic : (1 / 3 : ℚ) ∉ dyadic := by
  rintro ⟨z,n,h⟩
  have hp : (2 : ℚ)^n ≠ 0 := by positivity
  have he : (2 : ℚ)^n = 3 * z := by
    field_simp [hp] at h
    linarith
  have hi : (2 : ℤ)^n = 3 * z := by exact_mod_cast he
  have hd : (3 : ℤ) ∣ 2 ^ n := ⟨z,hi⟩
  have h3 : Prime (3 : ℤ) := by norm_num
  have heven := h3.dvd_of_dvd_pow hd
  norm_num at heven

private theorem dyadic_div_pow_iff (q : ℚ) (n : ℕ) :
    q / 2 ^ n ∈ dyadic ↔ q ∈ dyadic := by
  constructor
  · rintro ⟨z,m,hm⟩
    have hmul : q = (2 : ℚ) ^ n * (q / 2 ^ n) := by field_simp
    rw [hm] at hmul
    by_cases hnm : n ≤ m
    · obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le hnm
      refine ⟨z,s,?_⟩
      rw [hmul,pow_add]
      field_simp
    · obtain ⟨s,hs⟩ := Nat.exists_eq_add_of_le (by omega : m ≤ n)
      refine ⟨(2 : ℤ) ^ s * z,0,?_⟩
      rw [hmul,hs,pow_add]
      push_cast
      field_simp
  · rintro ⟨z,m,rfl⟩
    exact ⟨z,m+n,by rw [div_div,pow_add]⟩

private theorem twice_dyadic_iff (q : ℚ) :
    2*q ∈ dyadic ↔ q ∈ dyadic := by
  have h := dyadic_div_pow_iff (2*q) 1
  convert h.symm using 1
  rw [pow_one]
  ring

private theorem dyadic_dense {a b : ℝ} (h : a < b) :
    ∃ q : ℚ, a < (q : ℝ) ∧ (q : ℝ) < b ∧ q ∈ dyadic := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1/(b-a)) (by norm_num : (1 : ℝ)<2)
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hgap : 1 < (b - a) * 2 ^ n := by
    have hh := (div_lt_iff₀ (sub_pos.mpr h)).1 hn
    simpa [mul_comm] using hh
  let z : ℤ := ⌊a * (2 : ℝ)^n⌋ + 1
  refine ⟨(z : ℚ)/2^n, ?_, ?_, ⟨z,n,rfl⟩⟩
  · push_cast
    apply (lt_div_iff₀ hpow).2
    dsimp [z]
    push_cast
    exact Int.lt_floor_add_one _
  · push_cast
    apply (div_lt_iff₀ hpow).2
    have hf := Int.floor_le (a * (2 : ℝ)^n)
    dsimp [z]
    push_cast
    linarith [show (b-a)*(2:ℝ)^n = b*2^n-a*2^n by ring]

private theorem nondyadic_dense {a b : ℝ} (h : a < b) :
    ∃ q : ℚ, a < (q : ℝ) ∧ (q : ℝ) < b ∧ q ∉ dyadic := by
  let t : ℚ := 1/3
  obtain ⟨q,hq,hq',hd⟩ := dyadic_dense (show a - (t : ℝ) < b - (t : ℝ) by linarith)
  refine ⟨q+t, ?_, ?_, ?_⟩
  · push_cast; linarith
  · push_cast; linarith
  · intro hmem
    have hsub := dyadic.sub_mem hmem hd
    apply third_not_dyadic
    change t ∈ dyadic
    convert hsub using 1
    ring

private theorem choose_outside (m : ℚ) (hm : m ≠ 0) :
    ∃ d : ℚ, 0 < d ∧ d ∉ dyadic ∧ m*d ∉ dyadic := by
  let t : ℚ := 1/3
  have ht : t ∉ dyadic := third_not_dyadic
  have hnon : ∃ q : ℚ, q ∉ dyadic ∧ m*q ∉ dyadic := by
    by_cases hmt : m*t ∈ dyadic
    · let u := t/m
      have hu : m*u = t := by dsimp [u]; field_simp
      by_cases hdu : u ∈ dyadic
      · refine ⟨t+u, ?_, ?_⟩
        · intro hmem
          have hsub := dyadic.sub_mem hmem hdu
          apply ht
          convert hsub using 1
          ring
        · intro hmem
          have hsub := dyadic.sub_mem hmem hmt
          apply ht
          convert hsub using 1; linarith [show m * (t+u) = m*t+m*u by ring]
      · exact ⟨u, hdu, by simpa only [hu] using ht⟩
    · exact ⟨t, ht, hmt⟩
  obtain ⟨q,hq,hqm⟩ := hnon
  rcases lt_trichotomy q 0 with hqneg | hqzero | hqpos
  · exact ⟨-q, neg_pos.mpr hqneg, by simpa using hq, by simpa using hqm⟩
  · exact (hq (hqzero.symm ▸ dyadic.zero_mem)).elim
  · exact ⟨q, hqpos, hq, hqm⟩

end AntiConvex
namespace AntiConvex

open Set

private def S : Set (ℝ × ℝ) :=
  {p | (Irrational p.1 ∧ Irrational p.2) ∨
    ∃ x y : ℚ, p = (↑x, ↑y) ∧ (x ∈ dyadic ↔ y ∉ dyadic)}

private theorem mem_rational_fst {x : ℚ} {y : ℝ} (h : ((x : ℝ),y) ∈ S) :
    ∃ v : ℚ, y = v ∧ (x ∈ dyadic ↔ v ∉ dyadic) := by
  rcases h with h | ⟨u,v,he,hc⟩
  · exact (x.not_irrational h.1).elim
  · have hx : x = u := Rat.cast_injective (congrArg Prod.fst he)
    exact ⟨v, congrArg Prod.snd he, hx.symm ▸ hc⟩

private theorem mem_swap {p : ℝ × ℝ} (hp : p ∈ S) : p.swap ∈ S := by
  rcases hp with hp | ⟨x,y,rfl,h⟩
  · exact Or.inl hp.symm
  · exact Or.inr ⟨y,x,rfl,by tauto⟩

private abbrev RatI (a b : ℝ) := {q : ℚ // (q : ℝ) ∈ Ioo a b}

private theorem ratI_between {a b : ℝ} (u v : RatI a b) (h : u < v) :
    ∃ q : RatI a b, u < q ∧ q < v := by
  obtain ⟨q,hq,hq'⟩ := exists_rat_btwn (by exact_mod_cast h : (u.val : ℝ) < (v.val : ℝ))
  exact ⟨⟨q,u.2.1.trans hq,hq'.trans v.2.2⟩, by exact_mod_cast hq, by exact_mod_cast hq'⟩

private instance {a b : ℝ} : DenselyOrdered (RatI a b) := ⟨ratI_between⟩

private instance {a b : ℝ} : NoMinOrder (RatI a b) := ⟨fun u => by
  obtain ⟨q,hq,hq'⟩ := exists_rat_btwn u.2.1
  exact ⟨⟨q,hq,hq'.trans u.2.2⟩, by exact_mod_cast hq'⟩⟩

private instance {a b : ℝ} : NoMaxOrder (RatI a b) := ⟨fun u => by
  obtain ⟨q,hq,hq'⟩ := exists_rat_btwn u.2.2
  exact ⟨⟨q,u.2.1.trans hq,hq'⟩, by exact_mod_cast hq⟩⟩

private theorem ratI_nonempty {a b : ℝ} (h : a < b) : Nonempty (RatI a b) := by
  obtain ⟨q,hq,hq'⟩ := exists_rat_btwn h
  exact ⟨⟨q,hq,hq'⟩⟩

private theorem ratI_color {a b : ℝ} (lo hi : RatI a b) (h : lo < hi)
    (col : Prop) : ∃ q : RatI a b, lo < q ∧ q < hi ∧ (q.val ∈ dyadic ↔ col) := by
  classical
  have hl : (lo.val : ℝ) < (hi.val : ℝ) := by exact_mod_cast h
  by_cases hc : col
  · obtain ⟨q,hq,hq',hqD⟩ := dyadic_dense hl
    exact ⟨⟨q,lo.2.1.trans hq,hq'.trans hi.2.2⟩,
      by exact_mod_cast hq, by exact_mod_cast hq', iff_of_true hqD hc⟩
  · obtain ⟨q,hq,hq',hqD⟩ := nondyadic_dense hl
    exact ⟨⟨q,lo.2.1.trans hq,hq'.trans hi.2.2⟩,
      by exact_mod_cast hq, by exact_mod_cast hq', iff_of_false hqD hc⟩

private theorem graph_join {p q : ℝ × ℝ} (hp : p ∈ S) (hq : q ∈ S)
    (h₁ : p.1 < q.1) (h₂ : p.2 < q.2) : JoinedIn S p q := by
  let α := RatI p.1 q.1
  let β := RatI p.2 q.2
  have : Nonempty α := ratI_nonempty h₁
  have : Nonempty β := ratI_nonempty h₂
  obtain ⟨e, he⟩ := colored_iso (fun (a : α) (b : β) => a.val ∈ dyadic ↔ b.val ∉ dyadic)
    (fun a lo hi h => by
      obtain ⟨b,hb,hb',hcol⟩ := ratI_color lo hi h (a.val ∉ dyadic)
      exact ⟨b,hb,hb',by tauto⟩)
    (fun b lo hi h => ratI_color lo hi h (b.val ∉ dyadic))
  let A : Strip α := ⟨p.1, q.1, (fun a => (a.val : ℝ)), (fun a => a.2),
    fun u v hu huv hv => by
      obtain ⟨a,ha,ha'⟩ := exists_rat_btwn huv
      exact ⟨⟨a,hu.trans_lt ha,ha'.trans_le hv⟩,ha,ha'⟩⟩
  let B : Strip α := ⟨p.2, q.2, (fun a => ((e a).val : ℝ)), (fun a => (e a).2),
    fun u v hu huv hv => by
      obtain ⟨b,hb,hb'⟩ := exists_rat_btwn huv
      obtain ⟨a,ha⟩ := e.surjective ⟨b, hu.trans_lt hb,hb'.trans_le hv⟩
      exact ⟨a, by simpa [ha], by simpa [ha]⟩⟩
  have hAB : A.compatible B := by
    intro a b
    change (a.val : ℝ) < b.val ↔ ((e a).val : ℝ) < (e b).val
    simp only [Rat.cast_lt]
    exact (e.lt_iff_lt).symm
  let F := A.fillIso B hAB h₁.le h₂.le
  have byF (u : Icc p.1 q.1) : (F u : ℝ) = A.fill B u := rfl
  have hFlo : (F ⟨p.1, le_rfl, h₁.le⟩ : ℝ) = p.2 :=
    A.fill_low B h₂.le
  have hFhi : (F ⟨q.1, h₁.le, le_rfl⟩ : ℝ) = q.2 :=
    A.fill_high B hAB h₁.le h₂.le
  have hgraph : ∀ u : Icc p.1 q.1, (u.val, (F u).val) ∈ S := by
    intro u
    by_cases hl : u.val = p.1
    · have hu : u = ⟨p.1, le_rfl, h₁.le⟩ := Subtype.ext hl
      rw [hu]
      change (p.1, (F ⟨p.1, le_rfl, h₁.le⟩ : ℝ)) ∈ S
      rwa [hFlo]
    by_cases hh : u.val = q.1
    · have hu : u = ⟨q.1, h₁.le, le_rfl⟩ := Subtype.ext hh
      rw [hu]
      change (q.1, (F ⟨q.1, h₁.le, le_rfl⟩ : ℝ)) ∈ S
      rwa [hFhi]
    have hu : p.1 < u.val ∧ u.val < q.1 :=
      ⟨lt_of_le_of_ne u.2.1 (Ne.symm hl), lt_of_le_of_ne u.2.2 hh⟩
    by_cases hirr : Irrational u.val
    · left
      refine ⟨hirr, fun hbad => ?_⟩
      obtain ⟨v,hv⟩ := hbad
      have hv' : (F u : ℝ) = (v : ℝ) := hv.symm
      clear hv
      have hv := hv'
      have hvlo : p.2 < (v : ℝ) := by
        rw [← hv, ← hFlo]
        exact F.strictMono hu.1
      have hvhi : (v : ℝ) < q.2 := by
        rw [← hv, ← hFhi]
        exact F.strictMono hu.2
      obtain ⟨a,ha⟩ := e.surjective ⟨v,hvlo,hvhi⟩
      let u' : Icc p.1 q.1 := ⟨a.val,a.2.1.le,a.2.2.le⟩
      have hu' : (F u' : ℝ) = (v : ℝ) := by
        rw [byF]
        change A.fill B (A.f a) = _
        rw [A.fill_node B hAB a]
        change ((e a).val : ℝ) = _
        rw [ha]
      have hueq : u = u' := F.injective (Subtype.ext (hv.trans hu'.symm))
      exact hirr ⟨a.val, congrArg Subtype.val hueq.symm⟩
    · obtain ⟨a,ha⟩ := exists_rat_of_not_irrational hirr
      let a' : α := ⟨a, ha ▸ hu⟩
      right
      refine ⟨a,(e a').val,Prod.ext ha ?_,he a'⟩
      rw [byF,ha]
      exact A.fill_node B hAB a'
  let x (t : unitInterval) : ℝ := p.1 + (t : ℝ) * (q.1 - p.1)
  have hx (t : unitInterval) : x t ∈ Icc p.1 q.1 := by
    change p.1 ≤ x t ∧ x t ≤ q.1
    constructor
    · dsimp [x]
      linarith [mul_nonneg t.2.1 (sub_nonneg.mpr h₁.le)]
    · dsimp [x]
      linarith [mul_nonneg (sub_nonneg.mpr t.2.2) (sub_nonneg.mpr h₁.le)]
  let X (t : unitInterval) : Icc p.1 q.1 := ⟨x t,hx t⟩
  have hcont : Continuous X := Continuous.subtype_mk (by dsimp [x]; fun_prop) _
  refine ⟨⟨⟨fun t => ((X t).val,(F (X t)).val),
    continuous_subtype_val.comp hcont |>.prodMk
      (continuous_subtype_val.comp (F.continuous.comp hcont))⟩, ?_, ?_⟩,
    fun t => hgraph (X t)⟩
  · have hx0 : X 0 = ⟨p.1,le_rfl,h₁.le⟩ := Subtype.ext (by simp [X,x])
    simp only [hx0, hFlo, Prod.eta]
  · have hx1 : X 1 = ⟨q.1,h₁.le,le_rfl⟩ := Subtype.ext (by simp [X,x])
    simp only [hx1, hFhi, Prod.eta]

private theorem exists_irr_gt (x : ℝ) : ∃ u : ℝ, x < u ∧ Irrational u := by
  have hne : (Ioi x).Nonempty := ⟨x+1, by simp⟩
  obtain ⟨u,hui,hu⟩ := dense_irrational.exists_mem_open isOpen_Ioi hne
  exact ⟨u,hu,hui⟩

private theorem S_pathConnected : IsPathConnected S := by
  rw [isPathConnected_iff]
  constructor
  · obtain ⟨u,_,hu⟩ := exists_irr_gt 0
    exact ⟨(u,u), Or.inl ⟨hu,hu⟩⟩
  · intro p hp q hq
    obtain ⟨u,hu,hirr⟩ := exists_irr_gt (max p.1 q.1)
    obtain ⟨v,hv,hvirr⟩ := exists_irr_gt (max p.2 q.2)
    have hr : (u,v) ∈ S := Or.inl ⟨hirr,hvirr⟩
    exact (graph_join hp hr ((le_max_left _ _).trans_lt hu) ((le_max_left _ _).trans_lt hv)).trans
      (graph_join hq hr ((le_max_right _ _).trans_lt hu) ((le_max_right _ _).trans_lt hv)).symm

end AntiConvex
namespace AntiConvex

open Set

private theorem three_colors (q d : ℚ) (hd : d ∉ dyadic) :
    ¬ (q ∈ dyadic ∧ q+d ∈ dyadic) ∧
    ¬ (q ∈ dyadic ∧ q+2*d ∈ dyadic) ∧
    ¬ (q+d ∈ dyadic ∧ q+2*d ∈ dyadic) := by
  have hd2 := fun h => hd ((twice_dyadic_iff d).mp h)
  constructor
  · rintro ⟨h,h'⟩
    have hd' := dyadic.sub_mem h' h
    apply hd
    convert hd' using 1
    ring
  constructor
  · rintro ⟨h,h'⟩
    have hd' := dyadic.sub_mem h' h
    apply hd2
    convert hd' using 1
    ring
  · rintro ⟨h,h'⟩
    have hd' := dyadic.sub_mem h' h
    apply hd
    convert hd' using 1
    ring

set_option maxHeartbeats 800000 in
private theorem no_affine_graph {a b m c : ℝ} (hab : a < b)
    (h : ∀ x ∈ Ioo a b, (x,m*x+c) ∈ S) : False := by
  by_cases hm : m = 0
  · subst m
    obtain ⟨q,hq,hq',hqd⟩ := dyadic_dense hab
    obtain ⟨r,hr,hr',hrd⟩ := nondyadic_dense hab
    obtain ⟨u,hu,huD⟩ := mem_rational_fst (h q ⟨hq,hq'⟩)
    obtain ⟨v,hv,hvD⟩ := mem_rational_fst (h r ⟨hr,hr'⟩)
    simp only [zero_mul,zero_add] at hu hv
    have huv : u = v := Rat.cast_injective (hu.symm.trans hv)
    have hvD' : v ∈ dyadic := by tauto
    exact (huD.mp hqd) (by simpa [huv] using hvD')
  obtain ⟨q₀,hqa,hqb⟩ := exists_rat_btwn hab
  obtain ⟨q₁,hq01,hq1b⟩ := exists_rat_btwn hqb
  obtain ⟨y₀,hy₀,hcol₀⟩ := mem_rational_fst (h q₀ ⟨hqa,hqb⟩)
  obtain ⟨y₁,hy₁,_⟩ := mem_rational_fst (h q₁ ⟨hqa.trans hq01,hq1b⟩)
  let m' : ℚ := (y₁-y₀)/(q₁-q₀)
  have hm' : (m' : ℝ) = m := by
    dsimp [m']
    push_cast
    apply (div_eq_iff (sub_ne_zero.mpr hq01.ne.symm)).2
    linarith
  have hm'0 : m' ≠ 0 := by
    intro he
    apply hm
    simp [he] at hm'
    exact hm'.symm
  obtain ⟨d,hd,hdD,hdM⟩ := choose_outside m' hm'0
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (2*(d:ℝ)/(b-q₀)) (by norm_num : (1:ℝ)<2)
  let ε : ℚ := d / 2 ^ n
  have hεp : 0 < ε := by dsimp [ε]; positivity
  have hεD : ε ∉ dyadic := fun he => hdD ((dyadic_div_pow_iff d n).mp he)
  have hεM : m'*ε ∉ dyadic := by
    rw [show m'*ε = (m'*d)/2^n by dsimp [ε]; ring, dyadic_div_pow_iff]
    exact hdM
  have hε : (q₀:ℝ) + 2*(ε:ℝ) < b := by
    have h := (div_lt_iff₀ (sub_pos.mpr hqb)).mp hn
    have hpow : (0:ℝ) < 2^n := by positivity
    suffices hsmall : (2*(d:ℝ))/2^n < b-q₀ by
      dsimp [ε]
      push_cast
      linarith [show (2*(d:ℝ))/2^n = 2*((d:ℝ)/2^n) by ring]
    apply (div_lt_iff₀ hpow).2
    simpa [mul_comm] using h
  have hnode (k : ℕ) (hk : k ≤ 2) :
      q₀ + k * ε ∈ dyadic ↔ y₀ + k * (m'*ε) ∉ dyadic := by
    have hreal : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hεp
    have hkreal : (k:ℝ) ≤ 2 := by exact_mod_cast hk
    have hl : a < ((q₀+k*ε : ℚ) : ℝ) := by
      push_cast
      linarith [mul_nonneg (Nat.cast_nonneg k : 0 ≤ (k:ℝ)) hreal.le]
    have hr : ((q₀+k*ε : ℚ) : ℝ) < b := by
      push_cast
      calc
        (q₀:ℝ) + (k:ℝ)*(ε:ℝ) ≤ (q₀:ℝ) + 2*(ε:ℝ) := by gcongr
        _ < b := hε
    obtain ⟨v,hv,hc⟩ := mem_rational_fst (h _ ⟨hl,hr⟩)
    have hval : (v:ℝ) = ((y₀+k*(m'*ε) : ℚ):ℝ) := by
      rw [← hv]
      push_cast
      rw [hm']
      linear_combination hy₀
    have he : v = y₀+k*(m'*ε) := Rat.cast_injective hval
    simpa [he] using hc
  have he₁ := hnode 1 (by decide)
  have he₂ := hnode 2 (by decide)
  norm_num at he₁ he₂
  have hX := three_colors q₀ ε hεD
  have hY := three_colors y₀ (m'*ε) hεM
  clear * - hcol₀ he₁ he₂ hX hY
  tauto

private theorem no_forward {p q : ℝ × ℝ} (hlt : q.1 < p.1)
    (h : ∀ t ∈ Ioo (0 : ℝ) 1, q + t • (p-q) ∈ S) : False := by
  let m := (p.2-q.2)/(p.1-q.1)
  apply no_affine_graph (m := m) (c := q.2-m*q.1) hlt
  intro x hx
  let t := (x-q.1)/(p.1-q.1)
  have hden : 0 < p.1-q.1 := sub_pos.mpr hlt
  have ht : t ∈ Ioo (0:ℝ) 1 :=
    ⟨div_pos (sub_pos.mpr hx.1) hden,
     (div_lt_one hden).2 (sub_lt_sub_right hx.2 _)⟩
  have he : q + t • (p-q) = (x,m*x+(q.2-m*q.1)) := by
    apply Prod.ext
    · change q.1+t*(p.1-q.1) = x
      dsimp [t]
      field_simp [hden.ne']
      ring
    · change q.2+t*(p.2-q.2) = _
      dsimp [t,m]
      field_simp [hden.ne']
      ring
  exact he ▸ h t ht

private theorem reverse_segment {p q : ℝ×ℝ}
    (h : ∀ t ∈ Ioo (0 : ℝ) 1, q + t • (p-q) ∈ S) :
    ∀ t ∈ Ioo (0 : ℝ) 1, p + t • (q-p) ∈ S := by
  intro t ht
  have ht' : 1-t ∈ Ioo (0:ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have he : q + (1-t) • (p-q) = p + t • (q-p) := by
    apply Prod.ext
    · change q.1+(1-t)*(p.1-q.1) = p.1+t*(q.1-p.1)
      ring
    · change q.2+(1-t)*(p.2-q.2) = p.2+t*(q.2-p.2)
      ring
  exact he ▸ h _ ht'

private theorem swap_segment {p q : ℝ×ℝ}
    (h : ∀ t ∈ Ioo (0 : ℝ) 1, q + t • (p-q) ∈ S) :
    ∀ t ∈ Ioo (0 : ℝ) 1, q.swap + t • (p.swap-q.swap) ∈ S :=
  fun t ht => mem_swap (h t ht)

private theorem S_noSegment (p q : ℝ×ℝ) (hne : p ≠ q) :
    ∃ t ∈ Ioo (0 : ℝ) 1, q + t • (p-q) ∉ S := by
  by_contra! h
  rcases lt_trichotomy q.1 p.1 with hlt|heq|hgt
  · exact no_forward hlt h
  · rcases lt_trichotomy q.2 p.2 with hlt|heq'|hgt
    · exact no_forward hlt (swap_segment h)
    · exact hne (Prod.ext heq.symm heq'.symm)
    · exact no_forward hgt (reverse_segment (swap_segment h))
  · exact no_forward hgt (reverse_segment h)

end AntiConvex

theorem OMA.solution : type_of% @OMA.S_mse_4912917.main := by
  refine ⟨AntiConvex.S, fun p hp => Or.inl hp, AntiConvex.S_pathConnected, ?_⟩
  exact fun p _ q _ hpq => AntiConvex.S_noSegment p q hpq
