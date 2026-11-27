import OMAReductions.R_Erdos170_erdos170_existing_bounds_R1

/-! B. A. Wichmann, A Note on Restricted Difference Bases (1963).
The marks in this ruler form five arithmetic progressions. We express each mark in base 2r+1. In these coordinates, finding two
marks with a prescribed difference reduces to linear integer inequalities. -/

open Finset Filter Real Erdos170
namespace Wichmann

private inductive Mark (r : ℤ) : ℤ → ℤ → Prop
  | a (i : ℤ) : 0 ≤ i → i ≤ r → Mark r 0 i
  | b (i : ℤ) : 1 ≤ i → i ≤ r+1 → Mark r i 0
  | c (i : ℤ) : 0 ≤ i → i ≤ 2*r → Mark r (r+1+2*i) i
  | d (i : ℤ) : 0 ≤ i → i ≤ r+1 → Mark r (5*r+1+i) (2*r+i)
  | e (i : ℤ) : 0 ≤ i → i ≤ r → Mark r (6*r+2) (3*r+1+i)


private lemma digits1 (r q s : ℤ) (_hr : 1 ≤ r) (_hq : 0 ≤ q) (_hq' : q ≤ 6*r+3)
    (_hs : 0 ≤ s) (_hs' : s ≤ 2*r) (h : q = 0 ∧ r > 0 ∧ (0 ≤ s  ∧ s ≤ r)) :
    ∃ a b c d t : ℤ, Mark r a b ∧ Mark r c d ∧ c-a+t=q ∧ d-b-t*(2*r+1)=s := by
  refine ⟨_, _, _, _, 0, Mark.a (0) (by omega) (by omega),
    Mark.a (s) (by omega) (by omega), ?_, ?_⟩ <;> omega

private lemma digits2 (r q s : ℤ) (_hr : 1 ≤ r) (_hq : 0 ≤ q) (_hq' : q ≤ 6*r+3)
    (_hs : 0 ≤ s) (_hs' : s ≤ 2*r) (h : s = 0 ∧ r > 0 ∧ (0 < q  ∧ q ≤ 1 + r)) :
    ∃ a b c d t : ℤ, Mark r a b ∧ Mark r c d ∧ c-a+t=q ∧ d-b-t*(2*r+1)=s := by
  refine ⟨_, _, _, _, 0, Mark.a (0) (by omega) (by omega),
    Mark.b (q) (by omega) (by omega), ?_, ?_⟩ <;> omega

private lemma digits3 (r q s : ℤ) (_hr : 1 ≤ r) (_hq : 0 ≤ q) (_hq' : q ≤ 6*r+3)
    (_hs : 0 ≤ s) (_hs' : s ≤ 2*r) (h : (0 ≤ q  ∧ q ≤ r) ∧ (r < s  ∧ s ≤ 2*r)) :
    ∃ a b c d t : ℤ, Mark r a b ∧ Mark r c d ∧ c-a+t=q ∧ d-b-t*(2*r+1)=s := by
  refine ⟨_, _, _, _, -1, Mark.a (1 + 2*r - s) (by omega) (by omega),
    Mark.b (1 + q) (by omega) (by omega), ?_, ?_⟩ <;> omega

private lemma digits4 (r q s : ℤ) (_hr : 1 ≤ r) (_hq : 0 ≤ q) (_hq' : q ≤ 6*r+3)
    (_hs : 0 ≤ s) (_hs' : s ≤ 2*r) (h : (r + q) % 2 = 0 ∧ q > r ∧ s ≤ 2*r ∧ 2*s ≥ 2 + r + q) :
    ∃ a b c d t : ℤ, Mark r a b ∧ Mark r c d ∧ c-a+t=q ∧ d-b-t*(2*r+1)=s := by
  refine ⟨_, _, _, _, -1, Mark.a (1 + r - s + ((r + q) / 2)) (by omega) (by omega),
    Mark.c (-r + ((r + q) / 2)) (by omega) (by omega), ?_, ?_⟩ <;> omega

private lemma digits5 (r q s : ℤ) (_hr : 1 ≤ r) (_hq : 0 ≤ q) (_hq' : q ≤ 6*r+3)
    (_hs : 0 ≤ s) (_hs' : s ≤ 2*r) (h : (1 + r + q) % 2 = 0 ∧ (2 + r ≤ q  ∧ q ≤ 1 + 5*r) ∧ s ≥ 0 ∧ (-1 - 3*r + q ≤ 2*s  ∧ 2*s < -r + q)) :
    ∃ a b c d t : ℤ, Mark r a b ∧ Mark r c d ∧ c-a+t=q ∧ d-b-t*(2*r+1)=s := by
  refine ⟨_, _, _, _, 0, Mark.a (-1 - r - s + ((1 + r + q) / 2)) (by omega) (by omega),
    Mark.c (-1 - r + ((1 + r + q) / 2)) (by omega) (by omega), ?_, ?_⟩ <;> omega

private lemma digits6 (r q s : ℤ) (_hr : 1 ≤ r) (_hq : 0 ≤ q) (_hq' : q ≤ 6*r+3)
    (_hs : 0 ≤ s) (_hs' : s ≤ 2*r) (h : r > 0 ∧ q ≤ 3 + 6*r ∧ (0 ≤ s  ∧ s ≤ -3 - 5*r + q)) :
    ∃ a b c d t : ℤ, Mark r a b ∧ Mark r c d ∧ c-a+t=q ∧ d-b-t*(2*r+1)=s := by
  refine ⟨_, _, _, _, 1, Mark.a (-3 - 5*r + q - s) (by omega) (by omega),
    Mark.d (-2 - 5*r + q) (by omega) (by omega), ?_, ?_⟩ <;> omega

private lemma digits7 (r q s : ℤ) (_hr : 1 ≤ r) (_hq : 0 ≤ q) (_hq' : q ≤ 6*r+3)
    (_hs : 0 ≤ s) (_hs' : s ≤ 2*r) (h : q > 5*r ∧ (-1 - 4*r + q ≤ s  ∧ s ≤ 2*r) ∧ (((1 + r + q) % 2 = 0 ∧ q ≥ 2 + 5*r) ∨ ((r + q) % 2 = 0 ∧ r > 0))) :
    ∃ a b c d t : ℤ, Mark r a b ∧ Mark r c d ∧ c-a+t=q ∧ d-b-t*(2*r+1)=s := by
  refine ⟨_, _, _, _, 0, Mark.a (-1 - 3*r + q - s) (by omega) (by omega),
    Mark.d (-1 - 5*r + q) (by omega) (by omega), ?_, ?_⟩ <;> omega

private lemma digits8 (r q s : ℤ) (_hr : 1 ≤ r) (_hq : 0 ≤ q) (_hq' : q ≤ 6*r+3)
    (_hs : 0 ≤ s) (_hs' : s ≤ 2*r) (h : q = 3 + 6*r ∧ (r < s  ∧ s ≤ 2*r)) :
    ∃ a b c d t : ℤ, Mark r a b ∧ Mark r c d ∧ c-a+t=q ∧ d-b-t*(2*r+1)=s := by
  refine ⟨_, _, _, _, 1, Mark.a (0) (by omega) (by omega),
    Mark.e (-r + s) (by omega) (by omega), ?_, ?_⟩ <;> omega

private lemma digits9 (r q s : ℤ) (_hr : 1 ≤ r) (_hq : 0 ≤ q) (_hq' : q ≤ 6*r+3)
    (_hs : 0 ≤ s) (_hs' : s ≤ 2*r) (h : (0 < s  ∧ s ≤ 2*r) ∧ (-r + q ≤ 2*s  ∧ 2*s ≤ q)) :
    ∃ a b c d t : ℤ, Mark r a b ∧ Mark r c d ∧ c-a+t=q ∧ d-b-t*(2*r+1)=s := by
  refine ⟨_, _, _, _, 0, Mark.b (1 + r - q + 2*s) (by omega) (by omega),
    Mark.c (s) (by omega) (by omega), ?_, ?_⟩ <;> omega

private lemma digits10 (r q s : ℤ) (_hr : 1 ≤ r) (_hq : 0 ≤ q) (_hq' : q ≤ 6*r+3)
    (_hs : 0 ≤ s) (_hs' : s ≤ 2*r) (h : r > 0 ∧ s ≥ 0 ∧ (-2 - 5*r + q ≤ s  ∧ s ≤ -2 - 4*r + q) ∧ s ≤ r) :
    ∃ a b c d t : ℤ, Mark r a b ∧ Mark r c d ∧ c-a+t=q ∧ d-b-t*(2*r+1)=s := by
  refine ⟨_, _, _, _, 1, Mark.b (3 + 5*r - q + s) (by omega) (by omega),
    Mark.d (1 + s) (by omega) (by omega), ?_, ?_⟩ <;> omega

private lemma digits11 (r q s : ℤ) (_hr : 1 ≤ r) (_hq : 0 ≤ q) (_hq' : q ≤ 6*r+3)
    (_hs : 0 ≤ s) (_hs' : s ≤ 2*r) (h : q ≤ 2 + 6*r ∧ (r < s  ∧ s ≤ -2 - 4*r + q)) :
    ∃ a b c d t : ℤ, Mark r a b ∧ Mark r c d ∧ c-a+t=q ∧ d-b-t*(2*r+1)=s := by
  refine ⟨_, _, _, _, 1, Mark.b (3 + 6*r - q) (by omega) (by omega),
    Mark.e (-r + s) (by omega) (by omega), ?_, ?_⟩ <;> omega

private lemma digits12 (r q s : ℤ) (_hr : 1 ≤ r) (_hq : 0 ≤ q) (_hq' : q ≤ 6*r+3)
    (_hs : 0 ≤ s) (_hs' : s ≤ 2*r) (h : s ≤ q ∧ s ≤ 2*r ∧ (q < 2*s  ∧ 2*s ≤ 1 + r + q)) :
    ∃ a b c d t : ℤ, Mark r a b ∧ Mark r c d ∧ c-a+t=q ∧ d-b-t*(2*r+1)=s := by
  refine ⟨_, _, _, _, 0, Mark.c (2*r - q + s) (by omega) (by omega),
    Mark.d (-q + 2*s) (by omega) (by omega), ?_, ?_⟩ <;> omega

private lemma digits13 (r q s : ℤ) (_hr : 1 ≤ r) (_hq : 0 ≤ q) (_hq' : q ≤ 6*r+3)
    (_hs : 0 ≤ s) (_hs' : s ≤ 2*r) (h : s ≥ 0 ∧ s ≥ -1 - 4*r + q ∧ 2*s ≤ -2 - 3*r + q) :
    ∃ a b c d t : ℤ, Mark r a b ∧ Mark r c d ∧ c-a+t=q ∧ d-b-t*(2*r+1)=s := by
  refine ⟨_, _, _, _, 1, Mark.c (2 + 4*r - q + s) (by omega) (by omega),
    Mark.d (3 + 4*r - q + 2*s) (by omega) (by omega), ?_, ?_⟩ <;> omega

private lemma digits14 (r q s : ℤ) (_hr : 1 ≤ r) (_hq : 0 ≤ q) (_hq' : q ≤ 6*r+3)
    (_hs : 0 ≤ s) (_hs' : s ≤ 2*r) (h : (r + q) % 2 = 0 ∧ q ≤ 5*r ∧ s ≥ 0 ∧ (-1 - 3*r + q ≤ 2*s  ∧ 2*s ≤ -2 - r + q)) :
    ∃ a b c d t : ℤ, Mark r a b ∧ Mark r c d ∧ c-a+t=q ∧ d-b-t*(2*r+1)=s := by
  refine ⟨_, _, _, _, 1, Mark.c (1 + 2*r - q + ((r + q) / 2)) (by omega) (by omega),
    Mark.e (1 + r - q + s + ((r + q) / 2)) (by omega) (by omega), ?_, ?_⟩ <;> omega

private lemma digits15 (r q s : ℤ) (_hr : 1 ≤ r) (_hq : 0 ≤ q) (_hq' : q ≤ 6*r+3)
    (_hs : 0 ≤ s) (_hs' : s ≤ 2*r) (h : (1 + r + q) % 2 = 0 ∧ q > r ∧ s ≤ 2*r ∧ 2*s ≥ 2 + r + q) :
    ∃ a b c d t : ℤ, Mark r a b ∧ Mark r c d ∧ c-a+t=q ∧ d-b-t*(2*r+1)=s := by
  refine ⟨_, _, _, _, 0, Mark.c (2*r - q + ((1 + r + q) / 2)) (by omega) (by omega),
    Mark.e (-1 - r - q + s + ((1 + r + q) / 2)) (by omega) (by omega), ?_, ?_⟩ <;> omega

private lemma digits16 (r q s : ℤ) (_hr : 1 ≤ r) (_hq : 0 ≤ q) (_hq' : q ≤ 6*r+3)
    (_hs : 0 ≤ s) (_hs' : s ≤ 2*r) (h : q > 0 ∧ (q < s  ∧ s ≤ r)) :
    ∃ a b c d t : ℤ, Mark r a b ∧ Mark r c d ∧ c-a+t=q ∧ d-b-t*(2*r+1)=s := by
  refine ⟨_, _, _, _, 0, Mark.d (1 + r - q) (by omega) (by omega),
    Mark.e (-q + s) (by omega) (by omega), ?_, ?_⟩ <;> omega

private lemma cover_digits (r q s : ℤ) (hr : 1 ≤ r) (hq : 0 ≤ q) (hq' : q ≤ 6*r+3)
    (hs : 0 ≤ s) (hs' : s ≤ 2*r) :
    ∃ a b c d t : ℤ, Mark r a b ∧ Mark r c d ∧ c-a+t=q ∧ d-b-t*(2*r+1)=s := by
  by_cases h0 : 2*s < -r + q
  · by_cases h1 : -1 - 4*r + q ≤ s
    · by_cases h2 : q ≤ 1 + r
      · exact digits2 r q s hr hq hq' hs hs' (by omega)
      · by_cases h3 : q ≤ 1 + 5*r
        · by_cases h4 : -1 - 3*r + q ≤ 2*s
          · by_cases h5 : (r + q) % 2 = 0
            · exact digits14 r q s hr hq hq' hs hs' (by omega)
            · exact digits5 r q s hr hq hq' hs hs' (by omega)
          · exact digits13 r q s hr hq hq' hs hs' (by omega)
        · exact digits7 r q s hr hq hq' hs hs' (by omega)
    · by_cases h2 : r < s
      · by_cases h3 : q = 3 + 6*r
        · exact digits8 r q s hr hq hq' hs hs' (by omega)
        · exact digits11 r q s hr hq hq' hs hs' (by omega)
      · by_cases h3 : s ≤ -3 - 5*r + q
        · exact digits6 r q s hr hq hq' hs hs' (by omega)
        · exact digits10 r q s hr hq hq' hs hs' (by omega)
  · by_cases h1 : r < s
    · by_cases h2 : 2*s ≥ 2 + r + q
      · by_cases h3 : q > r
        · by_cases h4 : (r + q) % 2 = 0
          · exact digits4 r q s hr hq hq' hs hs' (by omega)
          · exact digits15 r q s hr hq hq' hs hs' (by omega)
        · exact digits3 r q s hr hq hq' hs hs' (by omega)
      · by_cases h3 : q < 2*s
        · exact digits12 r q s hr hq hq' hs hs' (by omega)
        · exact digits9 r q s hr hq hq' hs hs' (by omega)
    · by_cases h2 : q < 2*s
      · by_cases h3 : q = 0
        · exact digits1 r q s hr hq hq' hs hs' (by omega)
        · by_cases h4 : q < s
          · exact digits16 r q s hr hq hq' hs hs' (by omega)
          · exact digits12 r q s hr hq hq' hs hs' (by omega)
      · by_cases h3 : q = 0
        · exact digits1 r q s hr hq hq' hs hs' (by omega)
        · by_cases h4 : s = 0
          · exact digits2 r q s hr hq hq' hs hs' (by omega)
          · exact digits9 r q s hr hq hq' hs hs' (by omega)


private def base (r : ℤ) := 2*r+1
private def marks (r : ℤ) : Finset ℤ :=
  (Icc 0 r ∪ (Icc 1 (r+1)).image (fun i => i*base r)) ∪
  ((Icc 0 (2*r)).image (fun i => (r+1+2*i)*base r+i) ∪
  ((Icc 0 (r+1)).image (fun i => (5*r+1+i)*base r+(2*r+i)) ∪
    (Icc 0 r).image (fun i => (6*r+2)*base r+(3*r+1+i))))

private lemma mark_mem {r a b : ℤ} (h : Mark r a b) : a*base r+b ∈ marks r := by
  simp only [marks, mem_union, mem_image, mem_Icc]
  cases h with
  | a i hi hi' => exact Or.inl <| Or.inl <| by simpa using And.intro hi hi'
  | b i hi hi' => exact Or.inl <| Or.inr ⟨_, ⟨hi,hi'⟩, by simp⟩
  | c i hi hi' => exact Or.inr <| Or.inl ⟨_, ⟨hi,hi'⟩, rfl⟩
  | d i hi hi' => exact Or.inr <| Or.inr <| Or.inl ⟨i, ⟨hi,hi'⟩, rfl⟩
  | e i hi hi' => exact Or.inr <| Or.inr <| Or.inr ⟨i, ⟨hi,hi'⟩, rfl⟩

private lemma mark_bounds {r a b : ℤ} (hr : 1 ≤ r) (h : Mark r a b) :
    0 ≤ a*base r+b ∧ a*base r+b < (6*r+4)*base r := by
  have hcoords : 0 ≤ a ∧ a ≤ 6*r+2 ∧ 0 ≤ b ∧ b ≤ 4*r+1 := by
    cases h <;> omega
  obtain ⟨ha, ha', hb, hb'⟩ := hcoords
  have hb0 : 0 ≤ base r := by dsimp [base]; omega
  constructor
  · exact add_nonneg (mul_nonneg ha hb0) hb
  · have hm := mul_le_mul_of_nonneg_right ha' hb0
    dsimp [base] at *
    nlinarith

private lemma marks_card (r : ℕ) : (marks (r : ℤ)).card ≤ 6*r+7 := by
  have h (s t : Finset ℤ) := card_union_le s t
  have general (a b c d e : Finset ℤ) :
      ((a ∪ b) ∪ (c ∪ (d ∪ e))).card ≤ a.card+b.card+c.card+d.card+e.card := by
    have h₁ := h a b
    have h₂ := h d e
    have h₃ := h c (d∪e)
    have h₄ := h (a∪b) (c∪(d∪e))
    omega
  dsimp [marks]
  apply (general _ _ _ _ _).trans
  grw [card_image_le, card_image_le, card_image_le, card_image_le]
  simp only [Int.card_Icc]
  omega

private def length (r : ℕ) := (6*r+4)*(2*r+1)-1

private lemma short_ruler (r : ℕ) (hr : 1 ≤ r) :
    ∃ A : Finset ℕ, A.card ≤ 6*r+7 ∧ (∀ a ∈ A, a ≤ length r) ∧ PerfectRuler (length r) A := by
  let A := ((marks (r : ℤ)).image Int.toNat).filter (· ≤ length r)
  refine ⟨A, (card_filter_le ..).trans (card_image_le.trans (marks_card r)),
    fun _ h => (mem_filter.mp h).2, ?_⟩
  intro d hd
  have hd' := mem_range.mp hd
  have he : length r + 1 = (6*r+4)*(2*r+1) := Nat.sub_add_cancel (show 0 < (6*r+4)*(2*r+1) by positivity)
  rw [he] at hd'
  let Q := d / (2*r+1)
  let S := d % (2*r+1)
  have hu : 0 < 2*r+1 := by omega
  have hQ : Q < 6*r+4 := (Nat.div_lt_iff_lt_mul hu).mpr hd'
  have hS : S < 2*r+1 := Nat.mod_lt _ hu
  have hdiv : Q*(2*r+1)+S=d := by simpa [Q,S,Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div d (2*r+1)
  obtain ⟨a,b,c,e,t,hab,hce,hq,hs⟩ := cover_digits r Q S (by exact_mod_cast hr)
    (by positivity) (by exact_mod_cast (by omega : Q ≤ 6*r+3))
    (by positivity) (by exact_mod_cast (by omega : S ≤ 2*r))
  have mem {a b : ℤ} (h : Mark (r:ℤ) a b) : (a*base r+b).toNat ∈ A := by
    obtain ⟨_,hhi⟩ := mark_bounds (by exact_mod_cast hr) h
    refine mem_filter.mpr ⟨mem_image.mpr ⟨_, mark_mem h, rfl⟩, ?_⟩
    have hcast : (((6*r+4)*(2*r+1) : ℕ) : ℤ) = (6*(r:ℤ)+4)*base r := by simp [base]
    omega
  refine ⟨_,mem hab,_,mem hce,?_⟩
  have hval : (d : ℤ) = (c*base r+e)-(a*base r+b) := by
    have hdiv' : (Q : ℤ)*(2*(r:ℤ)+1)+S=d := by exact_mod_cast hdiv
    dsimp [base]
    linear_combination -hdiv' - (2*(r:ℤ)+1)*hq - hs
  have h₁ := (mark_bounds (by exact_mod_cast hr) hab).1
  have h₂ := (mark_bounds (by exact_mod_cast hr) hce).1
  omega

private lemma extend {n l : ℕ} (hl : l ≤ n) (A : Finset ℕ)
    (hbound : ∀ a ∈ A, a ≤ l) (hA : PerfectRuler l A) :
    F n ≤ A.card + 2*(Nat.sqrt (n-l)+2) := by
  let t := Nat.sqrt (n-l)+1
  let D := (range (t+1)).image (fun j => n-j*t)
  let B := (A ∪ range t ∪ D).filter (· ≤ n)
  have hab : A ⊆ B := by
    intro a ha
    exact mem_filter.mpr ⟨mem_union_left _ (mem_union_left _ ha), (hbound a ha).trans hl⟩
  have hB : B ∈ PerfectRulersLengthN n := by
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr (fun i hi => mem_range.mpr (by have := (mem_filter.mp hi).2; omega)), ?_⟩
    intro k hk
    have hkn : k ≤ n := by have := mem_range.mp hk; omega
    by_cases hkl : k ≤ l
    · obtain ⟨u,hu,v,hv,h⟩ := hA k (mem_range.mpr (by omega))
      exact ⟨u,hab hu,v,hab hv,h⟩
    · let j := (n-k)/t
      let a := (n-k)%t
      have ht : 0 < t := by dsimp [t]; omega
      have hj : j < t := (Nat.div_lt_iff_lt_mul ht).mpr (by
        have h := Nat.lt_succ_sqrt (n-l)
        change n-l < t*t at h
        omega)
      have ha : a < t := Nat.mod_lt _ ht
      have eqn : a+j*t=n-k := by simpa [a,j,Nat.mul_comm] using Nat.mod_add_div (n-k) t
      refine ⟨a,mem_filter.mpr ⟨mem_union_left _ (mem_union_right _ (mem_range.mpr ha)),by omega⟩,
        n-j*t,mem_filter.mpr ⟨mem_union_right _ (mem_image.mpr ⟨j,mem_range.mpr (by omega),rfl⟩),by omega⟩,by omega⟩
  have hmin : F n ≤ B.card := min'_le _ _ (mem_image.mpr ⟨B,hB,rfl⟩)
  apply hmin.trans
  have hsize := (card_filter_le .. : B.card ≤ (A ∪ range t ∪ D).card)
  have h₁ := card_union_le (A ∪ range t) D
  have h₂ := card_union_le A (range t)
  have h₃ : D.card ≤ t+1 := card_image_le.trans (card_range (t+1)).le
  simp only [card_range] at h₂
  apply hsize.trans
  change (A ∪ range t ∪ D).card ≤ A.card + 2*(t+1)
  omega

end Wichmann

theorem OMA.solution : OMA.R_Erdos170_erdos170_existing_bounds_R1.H3 := by
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (max (max (11/ε) (100/ε^2)) 100)
  filter_upwards [eventually_ge_atTop (12*(K+1)^2)] with n hn
  have hk : K+1 ≤ (n/12).sqrt := Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le (by decide)).mpr (by simpa [Nat.mul_comm] using hn))
  let r := (n/12).sqrt-1
  have hKr : K ≤ r := by dsimp [r]; omega
  have hKR : (K:ℝ) ≤ r := by exact_mod_cast hKr
  have hR : (100:ℝ) ≤ r := ((le_max_right _ _).trans hK.le).trans hKR
  have hr : 1 ≤ r := by exact_mod_cast (show (1:ℝ) ≤ r by linarith)
  have hr' : r+1 = (n/12).sqrt := by dsimp [r]; omega
  have hlow := Nat.sqrt_le' (n/12)
  have hhigh := Nat.lt_succ_sqrt' (n/12)
  rw [← hr'] at hlow hhigh
  have hlo : 12*(r+1)^2 ≤ n := by omega
  have hhi : n < 12*(r+2)^2 := by change n/12 < (r+2)^2 at hhigh; omega
  have hformula : Wichmann.length r = 12*r^2+14*r+3 := by
    unfold Wichmann.length
    have h : (6*r+4)*(2*r+1) = 12*r^2+14*r+4 := by ring
    omega
  have hlen : Wichmann.length r ≤ n := by rw [hformula]; nlinarith [hlo]
  have hdiff : n-Wichmann.length r ≤ 34*r+45 := by
    rw [hformula]; have h : n < 12*r^2+48*r+48 := by nlinarith [hhi]
    omega
  obtain ⟨A, hA, hab, hper⟩ := Wichmann.short_ruler r hr
  have hfin := Wichmann.extend hlen A hab hper
  let t := Nat.sqrt (n-Wichmann.length r)
  have ht : t^2 ≤ 34*r+45 := (Nat.sqrt_le' _).trans hdiff
  have hf : (F n : ℝ) ≤ 6*(r:ℝ)+11+2*t := by exact_mod_cast (show F n ≤ 6*r+11+2*t by dsimp [t]; omega)
  have h11 : 11/ε ≤ (r:ℝ) := ((le_max_left _ _).trans ((le_max_left _ _).trans hK.le)).trans hKR
  have h100 : 100/ε^2 ≤ (r:ℝ) := ((le_max_right _ _).trans ((le_max_left _ _).trans hK.le)).trans hKR
  have ha := (div_le_iff₀ hε).mp h11
  have hb := (div_le_iff₀ (sq_pos_of_pos hε)).mp h100
  have hb' := mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg r : (0:ℝ) ≤ r)
  have ht' : (t:ℝ)^2 ≤ 34*(r:ℝ)+45 := by exact_mod_cast ht
  have herr : (t:ℝ) ≤ ε*r := by
    apply le_of_sq_le_sq _ (mul_nonneg hε.le (Nat.cast_nonneg r))
    nlinarith only [ht', hb', hR]
  have hbase : 12*r^2 ≤ n := by nlinarith [hlo]
  have hbase' : 12*(r:ℝ)^2 ≤ n := by exact_mod_cast hbase
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by nlinarith [hlo] : 0 < n)
  have hsr := Real.sq_sqrt hnpos.le
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hsqrt : 3*(r:ℝ) ≤ Real.sqrt n := by
    apply le_of_sq_le_sq _ (Real.sqrt_nonneg _)
    nlinarith only [hsr,hbase',sq_nonneg (r:ℝ)]
  have hmain : 6*(r:ℝ) ≤ Real.sqrt 3 * Real.sqrt n := by
    have sq : (Real.sqrt 3 * Real.sqrt n)^2 = 3*n := by rw [mul_pow,h3,hsr]
    apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    nlinarith only [hbase',sq]
  apply (div_le_iff₀ (Real.sqrt_pos.2 hnpos)).mpr
  change (F n : ℝ) ≤ (Real.sqrt 3 + ε) * Real.sqrt n
  nlinarith only [hf,ha,herr,hmain,mul_le_mul_of_nonneg_left hsqrt hε.le]
