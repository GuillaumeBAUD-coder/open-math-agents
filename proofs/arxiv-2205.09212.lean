import OMAStatements.S_arxiv_2205_09212

/-!
# A modulo-nine product class need not lift to a prescribed product

Source: https://arxiv.org/abs/2205.09212, Section 11.
Credit: @rleshner

Table 8 assigns the product of columns 2 and 5 to column 1. Its member 10 is
attained by 2 times 5. Its canonical member 1 cannot be attained, even allowing
signed integer representatives and disregarding the sign restriction on columns.
-/

open OMA.S_arxiv_2205_09212

/-- If the output may be chosen anywhere in its modulo-nine residue class
(§3.3), every compatible relation lifts. In the division case we keep the
denominator and quotient and choose the numerator. -/
theorem PrimalLifting.variableOutput (op : Operation) (a b c : ℤ)
    (h : compatible op a b c) :
    ∃ x y z : ℤ, x ≡ a [ZMOD 9] ∧ y ≡ b [ZMOD 9] ∧ z ≡ c [ZMOD 9] ∧ exactAt op x y z := by
  cases op with
  | add => exact ⟨a, b, a + b, .refl _, .refl _, h, rfl⟩
  | sub => exact ⟨a, b, a - b, .refl _, .refl _, h, rfl⟩
  | mul => exact ⟨a, b, a * b, .refl _, .refl _, h, rfl⟩
  | div => exact ⟨b * c, b, c, h.2.symm, .refl _, .refl _, h.1, rfl⟩

private theorem sameSign (u r : ℤ) (lo : -18 ≤ r) (hi : r ≤ 18) (hz : u = 0 → r = 0) :
    (90 * u + r).sign = u.sign := by
  rcases lt_trichotomy u 0 with hu | hu | hu
  · rw [Int.sign_eq_neg_one_of_neg hu, Int.sign_eq_neg_one_iff_neg]
    omega
  · simp [hu, hz hu]
  · rw [Int.sign_eq_one_of_pos hu, Int.sign_eq_one_iff_pos]
    omega

private theorem signedAdd (a b c u v : ℤ) (ha : label a) (hb : label b)
    (hu : u.sign = a.sign) (hv : v.sign = b.sign) (hw : (u+v).sign = c.sign)
    (h : a+b ≡ c [ZMOD 9]) :
    ∃ x y : ℤ, inColumn a x ∧ inColumn b y ∧ inColumn c (x+y) := by
  obtain ⟨alo, ahi⟩ := ha
  obtain ⟨blo, bhi⟩ := hb
  have hcol (s r : ℤ) (hs : s.sign = r.sign) (ll : -9 ≤ r) (rr : r ≤ 9) :
      inColumn r (90*s + r) := by
    constructor
    · exact (sameSign s r (by omega) (by omega) (fun hz => by simpa [hz] using hs.symm)).trans hs
    · unfold Int.ModEq
      omega
  have hx := hcol u a hu alo ahi
  have hy := hcol v b hv blo bhi
  by_cases hz : u + v = 0
  · have hc : c = 0 := by simpa [hz] using hw.symm
    have hvs : v = -u := by omega
    refine ⟨90*u+a, -(90*u+a), hx, ⟨?_, ?_⟩, ?_⟩
    · rw [Int.sign_neg, hx.1, ← hu]
      simpa [hvs] using hv
    · unfold Int.ModEq at h ⊢
      omega
    · simp [inColumn, hc]
  · refine ⟨90*u+a, 90*v+b, hx, hy, ⟨?_, ?_⟩⟩
    · rw [show 90*u+a+(90*v+b) = 90*(u+v)+(a+b) by ring]
      exact (sameSign _ _ (by omega) (by omega) (fun h0 => (hz h0).elim)).trans hw
    · simpa using (hx.2.add hy.2).trans h

/-- Within the paper's signed columns, compatibility of the ordinary signs is
also necessary. With that proviso the variable-output reading always holds.
The sign witnesses need satisfy no congruences. -/
theorem PrimalLifting.signedVariableOutput (op : Operation) (a b c : ℤ)
    (ha : label a) (hb : label b) (h : compatible op a b c)
    (hs : signsCompatible op a b c) :
    ∃ x y z : ℤ, inColumn a x ∧ inColumn b y ∧ inColumn c z ∧ exactAt op x y z := by
  obtain ⟨u,v,w,hu,hv,hw,he⟩ := hs
  have selfcol (r : ℤ) : inColumn r r := ⟨rfl, .refl _⟩
  cases op with
  | add =>
    obtain ⟨x,y,hx,hy,hz⟩ := signedAdd a b c u v ha hb hu hv (he ▸ hw) h
    exact ⟨x,y,x+y,hx,hy,hz,rfl⟩
  | sub =>
    have hh : u + -v = w := by simpa [sub_eq_add_neg] using (show u-v = w from he)
    have hnb : label (-b) := by obtain ⟨hl,hr⟩ := hb; constructor <;> omega
    obtain ⟨x,t,hx,ht,hz⟩ := signedAdd a (-b) c u (-v) ha hnb hu
      (by simpa only [Int.sign_neg] using congrArg Neg.neg hv) (hh ▸ hw)
      (by simpa [sub_eq_add_neg] using (show a-b ≡ c [ZMOD 9] from h))
    refine ⟨x,-t,x+t,hx,⟨?_,?_⟩,hz,by simp [exactAt]⟩
    · simpa only [Int.sign_neg, neg_neg] using congrArg Neg.neg ht.1
    · simpa using ht.2.neg
  | mul =>
    refine ⟨a,b,a*b,selfcol _, selfcol _,⟨?_,h⟩,rfl⟩
    calc
      (a*b).sign = (u*v).sign := by simp only [Int.sign_mul,hu,hv]
      _ = c.sign := (show u*v = w from he) ▸ hw
  | div =>
    refine ⟨b*c,b,c,⟨?_,h.2.symm⟩,selfcol _,selfcol _,h.1,rfl⟩
    calc
      (b*c).sign = (v*w).sign := by simp only [Int.sign_mul,hv,hw]
      _ = a.sign := (show u = v*w from he.2) ▸ hu

/-- The same witness exhibits a realizable output if the target may vary. -/
private theorem output_ten : inColumn 2 2 ∧ inColumn 5 5 ∧ inColumn 1 10 ∧
    exactAt .mul 2 5 10 := by
  unfold inColumn exactAt
  decide

/-- The obstruction holds even in the full modulo-nine residue classes. -/
private theorem product_one_impossible (x y : ℤ) (hx : x ≡ 2 [ZMOD 9]) :
    x * y ≠ 1 := by
  intro h
  have hd : x ∣ (1 : ℤ) := ⟨y, h.symm⟩
  have hu := Int.isUnit_iff.mp (isUnit_of_dvd_one hd)
  rcases hu with rfl | rfl <;> revert hx <;> decide

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2205_09212.main) := by
  intro all
  obtain ⟨x, y, hx, _, hxy⟩ := all .mul 2 5 1 1
    (by norm_num [label]) (by norm_num [label]) (by norm_num [label])
    (by decide : (2 : ℤ) * 5 ≡ 1 [ZMOD 9])
    (by exact ⟨2,5,10,rfl,rfl,rfl,rfl⟩)
    (by exact ⟨rfl, Int.ModEq.refl _⟩)
  exact product_one_impossible x y hx.2 hxy
