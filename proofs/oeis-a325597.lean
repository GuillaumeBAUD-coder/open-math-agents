import OMAStatements.S_oeis_a325597

/-!
# A325597: unbounded discrepancy, with infinitely many zeros

Credit: @CubeJerry. The canonical greedy definition and statement by
@eltociear are unchanged. The complementary-sequence description in
OEIS A325598 and the gap observation in A325599 are acknowledged background.
The state-return argument below refutes the boundedness conjecture;
a discrete crossing argument proves the infinitely-many-zeros conjecture.
-/

/- A325597Defs -/
section
namespace A325597

noncomputable def A (i : ℕ) : ℕ := OMA.S_oeis_a325597.a (i + 1)
noncomputable def B (i : ℕ) : ℕ := 2 * A (i + 1) + A i

end A325597
end

/- A325597Prefix -/
section
namespace A325597
open OMA.S_oeis_a325597

@[simp] theorem pref_length (k : ℕ) : (pref k).length = k + 2 := by
  induction k with
  | zero => simp [pref]
  | succ k ih => simp [pref, ih, Nat.add_assoc]

theorem pref_getD_succ (k i : ℕ) (hi : i < k + 2) :
    (pref (k + 1)).getD i 0 = (pref k).getD i 0 := by
  change ((pref k) ++ [sInf {x : ℕ | (pref k).getLastD 0 < x ∧
    ∀ i : ℕ, i + 1 < (pref k).length → x ≠ 2 * (pref k).getD (i + 1) 0 + (pref k).getD i 0}]).getD i 0 = _
  apply List.getD_append
  simpa only [pref_length] using hi

theorem pref_getD_mono (k m i : ℕ) (hkm : k ≤ m) (hi : i < k + 2) :
    (pref m).getD i 0 = (pref k).getD i 0 := by
  induction m, hkm using Nat.le_induction with
  | base => rfl
  | succ m hkm ih =>
    exact (pref_getD_succ m i (by omega)).trans ih

theorem A_eq_getD (k i : ℕ) (hi : i < k + 2) :
    A i = (pref k).getD i 0 := by
  simp only [A, a, Nat.add_sub_cancel]
  rcases le_total k (i + 1) with h | h
  · exact pref_getD_mono k (i + 1) i h hi
  · exact (pref_getD_mono (i + 1) k i h (by omega)).symm

theorem pref_last (k : ℕ) : (pref k).getLastD 0 = A (k + 1) := by
  rw [A_eq_getD k (k + 1) (by omega)]
  simp [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?,
    List.getD_eq_getElem?_getD]

noncomputable def next (l : List ℕ) : ℕ :=
  sInf {x : ℕ | l.getLastD 0 < x ∧
    ∀ i : ℕ, i + 1 < l.length → x ≠ 2 * l.getD (i + 1) 0 + l.getD i 0}

theorem getD_le_sum (l : List ℕ) (i : ℕ) : l.getD i 0 ≤ l.sum := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem l 0 hi]
    exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.getElem_mem hi)
  · rw [List.getD_eq_default l 0 (by omega)]
    exact Nat.zero_le _

theorem next_nonempty (l : List ℕ) :
    {x : ℕ | l.getLastD 0 < x ∧
      ∀ i : ℕ, i + 1 < l.length → x ≠ 2 * l.getD (i + 1) 0 + l.getD i 0}.Nonempty := by
  refine ⟨3 * l.sum + 1, ?_, ?_⟩
  · have h := getD_le_sum l (l.length - 1)
    simpa only [List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?,
      ← List.getLastD_eq_getLast?] using (show l.getD (l.length - 1) 0 < 3 * l.sum + 1 by omega)
  · intro i hi
    have h0 := getD_le_sum l i
    have h1 := getD_le_sum l (i + 1)
    omega

theorem next_spec (l : List ℕ) : l.getLastD 0 < next l ∧
    ∀ i : ℕ, i + 1 < l.length → next l ≠ 2 * l.getD (i + 1) 0 + l.getD i 0 :=
  csInf_mem (next_nonempty l)

theorem next_min (l : List ℕ) (x : ℕ) (hx : l.getLastD 0 < x)
    (hf : ∀ i : ℕ, i + 1 < l.length → x ≠ 2 * l.getD (i + 1) 0 + l.getD i 0) :
    next l ≤ x :=
  csInf_le (OrderBot.bddBelow _) ⟨hx, hf⟩

theorem A_next (k : ℕ) : A (k + 2) = next (pref k) := by
  rw [A_eq_getD (k + 1) (k + 2) (by omega)]
  change ((pref k) ++ [next (pref k)]).getD (k + 2) 0 = _
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem A_next_spec (k : ℕ) : A (k + 1) < A (k + 2) ∧
    ∀ i : ℕ, i < k + 1 → A (k + 2) ≠ B i := by
  have h := next_spec (pref k)
  rw [pref_last, ← A_next] at h
  refine ⟨h.1, ?_⟩
  intro i hi
  have h' := h.2 i (by simpa using (show i + 1 < k + 2 by omega))
  simpa only [B, A_eq_getD k i (by omega), A_eq_getD k (i + 1) (by omega)] using h'

theorem A_min (k x : ℕ) (hx : A (k + 1) < x)
    (hf : ∀ i : ℕ, i < k + 1 → x ≠ B i) : A (k + 2) ≤ x := by
  rw [A_next]
  apply next_min
  · simpa only [pref_last] using hx
  · intro i hi
    have hi' : i < k + 1 := by rw [pref_length] at hi; omega
    simpa only [B, A_eq_getD k i (by omega), A_eq_getD k (i + 1) (by omega)] using hf i hi'

@[simp] theorem A_zero : A 0 = 1 := by
  rw [A_eq_getD 0 0 (by omega)]
  rfl

@[simp] theorem A_one : A 1 = 2 := by
  rw [A_eq_getD 0 1 (by omega)]
  rfl

theorem A_strictMono : StrictMono A := by
  apply strictMono_nat_of_lt_succ
  intro i
  cases i with
  | zero => simp
  | succ i => simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using (A_next_spec i).1

theorem A_pos (i : ℕ) : 0 < A i := by
  have h := A_strictMono.monotone (Nat.zero_le i)
  simp only [A_zero] at h
  omega

theorem index_lt_A (i : ℕ) : i < A i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h := A_strictMono (Nat.lt_succ_self i)
    change i + 1 < A (i + 1)
    change A i < A (i + 1) at h
    omega

@[simp] theorem A_two : A 2 = 3 := by
  apply Nat.le_antisymm
  · apply A_min 0 3 (by simp)
    intro i hi
    have : i = 0 := by omega
    subst i
    norm_num [B]
  · have := (A_next_spec 0).1
    change A 1 < A 2 at this
    rw [A_one] at this
    omega

@[simp] theorem A_three : A 3 = 4 := by
  apply Nat.le_antisymm
  · apply A_min 1 4 (by simp)
    intro i hi
    interval_cases i <;> norm_num [B]
  · have := (A_next_spec 1).1
    change A 2 < A 3 at this
    rw [A_two] at this
    omega

@[simp] theorem A_four : A 4 = 6 := by
  apply Nat.le_antisymm
  · apply A_min 2 6 (by simp)
    intro i hi
    interval_cases i <;> norm_num [B]
  · have h := (A_next_spec 2).1
    have h' := (A_next_spec 2).2 0 (by omega)
    norm_num [B] at h h'
    omega

end A325597
end

/- A325597Complement -/
section
namespace A325597

theorem disjoint (i j : ℕ) : A i ≠ B j := by
  by_cases h : i ≤ j + 1
  · have hA := A_strictMono.monotone h
    have hp := A_pos j
    unfold B
    omega
  · have hi : i = (i - 2) + 2 := by omega
    have hj : j < (i - 2) + 1 := by omega
    have h' := (A_next_spec (i - 2)).2 j hj
    simpa only [← hi] using h'

theorem B_strictMono : StrictMono B := by
  intro i j hij
  have h0 := A_strictMono hij
  have h1 := A_strictMono (show i + 1 < j + 1 by omega)
  unfold B
  omega

theorem B_pos (i : ℕ) : 0 < B i := by
  have h := A_pos i
  unfold B
  omega

theorem complement (x : ℕ) (hx : 0 < x) :
    (∃ i : ℕ, A i = x) ∨ (∃ i : ℕ, B i = x) := by
  classical
  by_contra hn
  have hA : ∀ i : ℕ, A i ≠ x := by
    intro i hi
    exact hn (Or.inl ⟨i, hi⟩)
  have hB : ∀ i : ℕ, x ≠ B i := by
    intro i hi
    exact hn (Or.inr ⟨i, hi.symm⟩)
  have hx2 : 2 ≤ x := by
    have h := hA 0
    rw [A_zero] at h
    omega
  have hex : ∃ n : ℕ, x < A n := ⟨x, index_lt_A x⟩
  let n := Nat.find hex
  have htop : x < A n := Nat.find_spec hex
  have hn2 : 2 ≤ n := by
    by_contra h
    have hcases : n = 0 ∨ n = 1 := by omega
    rcases hcases with h | h
    · rw [h, A_zero] at htop
      omega
    · rw [h, A_one] at htop
      omega
  have hprev : A (n - 1) ≤ x := by
    exact Nat.not_lt.mp (Nat.find_min hex (show n - 1 < n by omega))
  have hprev' : A (n - 1) < x := lt_of_le_of_ne hprev (hA (n - 1))
  have hmin := A_min (n - 2) x (by simpa only [show n - 2 + 1 = n - 1 by omega] using hprev')
    (fun i _ => hB i)
  have heq : n - 2 + 2 = n := by omega
  rw [heq] at hmin
  omega

end A325597
end

/- A325597Rank -/
section
namespace A325597Rank

lemma auxiliary_strictMono {A B : ℕ → ℕ} (hA : StrictMono A)
    (hBdef : ∀ i, B i = 2 * A (i + 1) + A i) : StrictMono B := by
  intro i j hij
  have h₀ := hA hij
  have h₁ := hA (show i + 1 < j + 1 by omega)
  rw [hBdef i, hBdef j]
  omega

lemma rank_between {A B : ℕ → ℕ} (hA : StrictMono A) (hA0 : A 0 = 1)
    (hBdef : ∀ i, B i = 2 * A (i + 1) + A i)
    (hdisjoint : ∀ i j, A i ≠ B j)
    (hcover : ∀ x, 0 < x → (∃ i, A i = x) ∨ (∃ i, B i = x))
    {i x : ℕ} (hlo : B i < x) (hhi : x < B (i + 1)) :
    A (x - i - 2) = x := by
  have hB : StrictMono B := auxiliary_strictMono hA hBdef
  have hApos (k : ℕ) : 0 < A k := by
    have h := hA.monotone (Nat.zero_le k)
    omega
  have hBpos (k : ℕ) : 0 < B k := by
    have h := hApos k
    rw [hBdef]
    omega
  have hx : 0 < x := by omega
  have hxB : ¬ ∃ k, B k = x := by
    rintro ⟨k, hk⟩
    by_cases hki : k ≤ i
    · have h := hB.monotone hki
      omega
    · have h := hB.monotone (show i + 1 ≤ k by omega)
      omega
  obtain ⟨j, hj⟩ : ∃ j, A j = x := (hcover x hx).resolve_right hxB
  let sa := (Finset.range (j + 1)).image A
  let sb := (Finset.range (i + 1)).image B
  have hd : Disjoint sa sb := by
    apply Finset.disjoint_left.mpr
    intro y hya hyb
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hya
    obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hyb
    exact hdisjoint k l (hk.trans hl.symm)
  have hu : sa ∪ sb = Finset.Icc 1 x := by
    ext y
    constructor
    · intro hy
      rcases Finset.mem_union.mp hy with ha | hb
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
        have hk' : k ≤ j := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
        exact Finset.mem_Icc.mpr ⟨hApos k, by simpa only [hj] using hA.monotone hk'⟩
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hb
        have hk' : k ≤ i := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
        exact Finset.mem_Icc.mpr ⟨hBpos k, le_trans (hB.monotone hk') (Nat.le_of_lt hlo)⟩
    · intro hy
      obtain ⟨hypos, hyx⟩ := Finset.mem_Icc.mp hy
      rcases hcover y hypos with ⟨k, hk⟩ | ⟨k, hk⟩
      · apply Finset.mem_union_left
        apply Finset.mem_image.mpr
        refine ⟨k, ?_, hk⟩
        apply Finset.mem_range.mpr
        by_contra hn
        have h := hA (show j < k by omega)
        omega
      · apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨k, ?_, hk⟩
        apply Finset.mem_range.mpr
        by_contra hn
        have h := hB.monotone (show i + 1 ≤ k by omega)
        omega
  have hca : sa.card = j + 1 := by
    rw [Finset.card_image_of_injective _ hA.injective, Finset.card_range]
  have hcb : sb.card = i + 1 := by
    rw [Finset.card_image_of_injective _ hB.injective, Finset.card_range]
  have hc : j + 1 + (i + 1) = x := by
    have h := Finset.card_union_of_disjoint hd
    rw [hu, hca, hcb, Nat.card_Icc] at h
    omega
  have hindex : x - i - 2 = j := by omega
  simpa only [hindex] using hj

end A325597Rank
end

/- A325597Growth -/
section
namespace A325597Growth

def excluded (a : ℕ → ℕ) (i : ℕ) : ℕ := 2*a (i+1)+a i

def state (a : ℕ → ℕ) (i : ℕ) : Prop :=
  a (i+1)=a i+1 ∧ a (i+2)=a i+3

theorem state_return (a : ℕ → ℕ)
    (hindex : ∀ i, i+1 ≤ a i)
    (hgap : ∀ i, excluded a i+2 < excluded a (i+1))
    (hrank : ∀ i x, excluded a i < x → x < excluded a (i+1) → a (x-i-2)=x)
    {i : ℕ} (hs : state a i) :
    state a (i+6*a i+11) ∧ a (i+6*a i+11)=9*a i+15 := by
  have hia := hindex i
  obtain ⟨h1,h2⟩ := hs
  have eb0 : excluded a i=3*a i+2 := by simp only [excluded,h1]; omega
  have eb1 : excluded a (i+1)=3*a i+7 := by
    simp only [excluded,show i+1+1=i+2 by omega,h1,h2]; omega
  let j := 3*a i+2-i
  have aj : a j=3*a i+4 := by
    have h := hrank i (3*a i+4) (by omega) (by omega)
    have he : 3*a i+4-i-2=j := by dsimp [j]; omega
    rwa [he] at h
  have aj1 : a (j+1)=3*a i+5 := by
    have h := hrank i (3*a i+5) (by omega) (by omega)
    have he : 3*a i+5-i-2=j+1 := by dsimp [j]; omega
    rwa [he] at h
  have aj2 : a (j+2)=3*a i+6 := by
    have h := hrank i (3*a i+6) (by omega) (by omega)
    have he : 3*a i+6-i-2=j+2 := by dsimp [j]; omega
    rwa [he] at h
  have ej0 : excluded a j=9*a i+14 := by simp only [excluded,aj,aj1]; omega
  have ej1 : excluded a (j+1)=9*a i+17 := by
    simp only [excluded,show j+1+1=j+2 by omega,aj1,aj2]; omega
  have ar0 : a (i+6*a i+11)=9*a i+15 := by
    have h := hrank j (9*a i+15) (by omega) (by omega)
    have he : 9*a i+15-j-2=i+6*a i+11 := by dsimp [j]; omega
    rwa [he] at h
  have ar1 : a (i+6*a i+11+1)=9*a i+16 := by
    have h := hrank j (9*a i+16) (by omega) (by omega)
    have he : 9*a i+16-j-2=i+6*a i+11+1 := by dsimp [j]; omega
    rwa [he] at h
  have ar2 : a (i+6*a i+11+2)=9*a i+18 := by
    have hgj := hgap (j+1)
    have h := hrank (j+1) (9*a i+18) (by omega) (by omega)
    have he : 9*a i+18-(j+1)-2=i+6*a i+11+2 := by dsimp [j]; omega
    rwa [he] at h
  exact ⟨⟨by omega,by omega⟩,ar0⟩

theorem index_lower (a : ℕ → ℕ) (hmono : StrictMono a) (ha0 : a 0=1) (i : ℕ) :
    i+1 ≤ a i := by
  induction i with
  | zero => omega
  | succ i ih =>
    have h : a i < a (i+1) := hmono (by omega)
    simpa only [Nat.succ_eq_add_one] using (show i+1+1 ≤ a (i+1) by omega)

theorem later_negative (a : ℕ → ℕ) (hmono : StrictMono a) (ha0 : a 0=1)
    (hrank : ∀ i x, excluded a i < x → x < excluded a (i+1) → a (x-i-2)=x)
    {i : ℕ} (hs : state a i) :
    ∃ j : ℕ, i < j ∧ 3*(a j : ℤ)-4*(j+1)=-(3*(a i : ℤ)-4*(i+1))-4 := by
  have hia := index_lower a hmono ha0 i
  obtain ⟨h1,h2⟩ := hs
  have eb0 : excluded a i=3*a i+2 := by simp only [excluded,h1]; omega
  have eb1 : excluded a (i+1)=3*a i+7 := by
    simp only [excluded,show i+1+1=i+2 by omega,h1,h2]; omega
  have h := hrank i (3*a i+4) (by omega) (by omega)
  have he : 3*a i+4-i-2=3*a i+2-i := by omega
  rw [he] at h
  refine ⟨3*a i+2-i,by omega,?_⟩
  rw [h]
  have hj : 3*a i+2-i+i=3*a i+2 := by omega
  have hj' := congrArg (fun x : ℕ => (x : ℤ)) hj
  push_cast at hj' ⊢
  omega

theorem growth_witness (a : ℕ → ℕ) (hmono : StrictMono a) (ha0 : a 0=1)
    (hrank : ∀ i x, excluded a i < x → x < excluded a (i+1) → a (x-i-2)=x)
    (ha2 : a 2=3) (ha3 : a 3=4) (ha4 : a 4=6) (m : ℕ) :
    ∃ i : ℕ, m ≤ i ∧ state a i ∧ 3*(a i : ℤ)-4*(i+1)=(m : ℤ)-3 := by
  have hindex := index_lower a hmono ha0
  have hgap : ∀ i, excluded a i+2 < excluded a (i+1) := by
    intro i
    have h1 := hmono (show i < i+1 by omega)
    have h2 := hmono (show i+1 < i+1+1 by omega)
    simp only [excluded]
    omega
  induction m with
  | zero =>
    refine ⟨2,by omega,?_,?_⟩
    · exact ⟨by simpa [ha2] using ha3,by simpa [ha2] using ha4⟩
    · simp [ha2]
  | succ m ih =>
    obtain ⟨i,hmi,hs,hd⟩ := ih
    obtain ⟨hs',ha'⟩ := state_return a hindex hgap hrank hs
    refine ⟨i+6*a i+11,by omega,hs',?_⟩
    rw [ha']
    push_cast
    omega

theorem unbounded (a : ℕ → ℕ) (hmono : StrictMono a) (ha0 : a 0=1)
    (hrank : ∀ i x, excluded a i < x → x < excluded a (i+1) → a (x-i-2)=x)
    (ha2 : a 2=3) (ha3 : a 3=4) (ha4 : a 4=6) :
    ¬ ∃ C : ℤ, ∀ n : ℕ, |3*(a n : ℤ)-4*(n+1)| ≤ C := by
  rintro ⟨C,hC⟩
  obtain ⟨i,_,_,hd⟩ := growth_witness a hmono ha0 hrank ha2 ha3 ha4 (C.natAbs+4)
  have hb := hC i
  have ha := le_abs_self (3*(a i : ℤ)-4*(i+1))
  have hc : C ≤ (C.natAbs : ℤ) := Int.le_natAbs
  simp only [Nat.cast_add,Nat.cast_ofNat] at hd
  omega

end A325597Growth
end

/- A325597Final -/
section
namespace A325597Final
open A325597 OMA.S_oeis_a325597

theorem rank {i x : ℕ} (hlo : B i < x) (hhi : x < B (i + 1)) :
    A (x - i - 2) = x :=
  A325597Rank.rank_between A_strictMono A_zero (fun _ => rfl)
    A325597.disjoint complement hlo hhi

theorem growth_rank (i x : ℕ) (hlo : A325597Growth.excluded A i < x)
    (hhi : x < A325597Growth.excluded A (i + 1)) : A (x - i - 2) = x :=
  rank hlo hhi

theorem canonical_unbounded :
    ¬ ∃ C : ℤ, ∀ n : ℕ, 1 ≤ n → |d n| ≤ C := by
  rintro ⟨C, hC⟩
  apply A325597Growth.unbounded A A_strictMono A_zero growth_rank A_two A_three A_four
  refine ⟨C, fun n => ?_⟩
  simpa only [d, A, Nat.cast_add, Nat.cast_one] using hC (n + 1) (by omega)

theorem disproof : ¬ ((∃ C : ℤ, ∀ n : ℕ, 1 ≤ n → |d n| ≤ C) ∧
    {n : ℕ | 1 ≤ n ∧ d n = 0}.Infinite) := by
  intro h
  exact canonical_unbounded h.1

end A325597Final
end

/- A325597Zeros -/
section
namespace A325597Zeros

/-- An integer sequence whose downward steps have size at most one must cross
zero between a nonnegative value and a later negative value. -/
theorem zero_after (d : ℕ → ℤ)
    (hstep : ∀ k, d k - 1 ≤ d (k + 1)) {i : ℕ}
    (hi : 0 ≤ d i) (hneg : ∃ j, i ≤ j ∧ d j < 0) :
    ∃ k, i ≤ k ∧ d k = 0 := by
  classical
  let j := Nat.find hneg
  have hj : i ≤ j ∧ d j < 0 := Nat.find_spec hneg
  have hij : i < j := by
    by_contra h
    have he : j = i := by omega
    rw [he] at hj
    omega
  have hip : i ≤ j - 1 := by omega
  have hmin : ¬ (i ≤ j - 1 ∧ d (j - 1) < 0) :=
    Nat.find_min hneg (show j - 1 < j by omega)
  have hd : 0 ≤ d (j - 1) := by omega
  have hs : d (j - 1) - 1 ≤ d j := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ j by omega)] using hstep (j - 1)
  exact ⟨j - 1, hip, by omega⟩

/-- Arbitrarily late nonnegative-to-negative passages force infinitely many
zeros when every downward step has size at most one. -/
theorem infinite_zeros (d : ℕ → ℤ)
    (hstep : ∀ k, d k - 1 ≤ d (k + 1))
    (hpassage : ∀ N : ℕ, ∃ i, N ≤ i ∧ 0 ≤ d i ∧ ∃ j, i ≤ j ∧ d j < 0) :
    {n : ℕ | d n = 0}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨i, hi, hd, hj⟩ := hpassage (N + 1)
  obtain ⟨k, hk, hz⟩ := zero_after d hstep hd hj
  exact ⟨k, hz, by omega⟩

theorem infinite_zeros_of_rank (a : ℕ → ℕ)
    (hmono : StrictMono a) (ha0 : a 0 = 1)
    (hrank : ∀ i x, A325597Growth.excluded a i < x →
      x < A325597Growth.excluded a (i + 1) → a (x - i - 2) = x)
    (ha2 : a 2 = 3) (ha3 : a 3 = 4) (ha4 : a 4 = 6) :
    {i : ℕ | 3 * (a i : ℤ) - 4 * (i + 1) = 0}.Infinite := by
  apply infinite_zeros (fun i => 3 * (a i : ℤ) - 4 * (i + 1))
  · intro k
    have hm := hmono (show k < k + 1 by omega)
    have hmz : (a k : ℤ) < (a (k + 1) : ℤ) := Int.ofNat_lt.mpr hm
    push_cast
    omega
  · intro N
    obtain ⟨i, hmi, hs, hd⟩ :=
      A325597Growth.growth_witness a hmono ha0 hrank ha2 ha3 ha4 (N + 3)
    obtain ⟨j, hij, hj⟩ := A325597Growth.later_negative a hmono ha0 hrank hs
    simp only [Nat.cast_add, Nat.cast_ofNat] at hd
    refine ⟨i, by omega, by omega, j, by omega, ?_⟩
    omega

end A325597Zeros
end

/- A325597Complete -/
section
namespace A325597Complete
open A325597 OMA.S_oeis_a325597

/-- The second conjecture is true, despite the first conjecture being false. -/
theorem canonical_infinite_zeros : {n : ℕ | 1 ≤ n ∧ d n = 0}.Infinite := by
  have hz := A325597Zeros.infinite_zeros_of_rank A A_strictMono A_zero
    A325597Final.growth_rank A_two A_three A_four
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨i, hi, hNi⟩ := hz.exists_gt N
  refine ⟨i + 1, ⟨by omega, ?_⟩, by omega⟩
  simpa only [Set.mem_ofPred_eq, d, A, Nat.cast_add, Nat.cast_one] using hi

theorem disproof : ¬ ((∃ C : ℤ, ∀ n : ℕ, 1 ≤ n → |d n| ≤ C) ∧
    {n : ℕ | 1 ≤ n ∧ d n = 0}.Infinite) := A325597Final.disproof

end A325597Complete
end

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a325597.main) :=
  A325597Complete.disproof
