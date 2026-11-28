import OMAReductions.R_mse_4815847_R1

/-!
# Pascal cuts in the unbounded range

Credit: @YOHSUKE-TAKAHASHI

In barycentric coordinates x=k and y=r-k, each of the two regions x≤m≤y
and y≤m≤x has mass equal to half the total plus m, with m=⌊N/2⌋.
Thus opposite coefficients of x,y can never bisect. In the positive quadrant
a pivot in column m also excludes b≥(m-1)a. At the other end, the first
interior entry on the last row excludes a≥(N-3)b. Reflection and sign reversal
reduce all other cuts to the two parity cases below.
-/

namespace OMA.R_mse_4815847_R1_H2_R1
open OMA.S_mse_4815847

def H1 : Prop :=
  ∀ n : ℕ, 250 < n → n % 2 = 0 → ∀ a b d : ℤ,
    0 < a → 0 < b → a ≤ 2*(n:ℤ) → b ≤ 2*(n:ℤ) → |d| ≤ 4*(n:ℤ)^2+1 →
    a < ((n:ℤ)-3)*b → b < (((n/2:ℕ):ℤ)-1)*a →
    (∑ p ∈ (entries n).filter (fun p => d < a*(p.1:ℤ)+b*p.2), p.1.choose p.2) ≠
      ∑ p ∈ (entries n).filter (fun p => a*(p.1:ℤ)+b*p.2 ≤ d), p.1.choose p.2

def H2 : Prop :=
  ∀ n : ℕ, 250 < n → n % 2 = 1 → ∀ a b d : ℤ,
    0 < a → 0 < b → a ≤ 2*(n:ℤ) → b ≤ 2*(n:ℤ) → |d| ≤ 4*(n:ℤ)^2+1 →
    a < ((n:ℤ)-3)*b → b < (((n/2:ℕ):ℤ)-1)*a →
    (∑ p ∈ (entries n).filter (fun p => d < a*(p.1:ℤ)+b*p.2), p.1.choose p.2) ≠
      ∑ p ∈ (entries n).filter (fun p => a*(p.1:ℤ)+b*p.2 ≤ d), p.1.choose p.2

open Finset

set_option maxHeartbeats 4000000 in
theorem main : H1 → H2 → OMA.R_mse_4815847_R1.H2 := by
  let weight (p : (ℕ × ℕ)) := (p.1+p.2).choose p.1
  let mass (s : Finset (ℕ × ℕ)) := ∑ p ∈ s, weight p
  let tri (n : ℕ) := ((Icc 1 n) ×ˢ (Icc 1 n)).filter (fun p => p.1+p.2 ≤ n)
  let rect (a b : ℕ) := (Ioo 0 a) ×ˢ (Ioo 0 b : Finset ℕ)
  let wedge (n m : ℕ) := (tri n).filter (fun p => p.1 ≤ m ∧ m ≤ p.2)
  let mirror (n m : ℕ) := (tri n).filter (fun p => p.2 ≤ m ∧ m ≤ p.1)

  have mem_tri {n : ℕ} {p : (ℕ × ℕ)} :
      p ∈ tri n ↔ 0 < p.1 ∧ 0 < p.2 ∧ p.1+p.2 ≤ n := by
    simp only [tri, mem_filter,mem_product,mem_Icc]
    omega

  have mass_mono {s t : Finset (ℕ × ℕ)} (h : s ⊆ t) : mass s ≤ mass t :=
    sum_le_sum_of_subset h

  have stick (a b : ℕ) (hb : 0 < b) :
      (∑ j ∈ Ioo 0 b, (a+j).choose a) + 1 = (a+b).choose (a+1) := by
    obtain ⟨c,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
    have e : range (c+1) = insert 0 (Ioo 0 (c+1)) := by
      ext x
      simp only [mem_range,mem_insert,mem_Ioo]
      omega
    have h := Nat.sum_range_add_choose c a
    rw [e,sum_insert (by simp)] at h
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

  /- The interior rectangle has the weight of its far corner minus the two side lengths. -/
  have rectangle_mass (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
      mass (rect a b) + a + b = (a+b).choose a := by
    obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
    induction a with
    | zero =>
      have e : (Ioo 0 1 : Finset ℕ) = ∅ := by ext x; simp; omega
      simp [rect,mass,e]
    | succ a ih =>
      have e : Ioo 0 (a+1+1) = insert (a+1) (Ioo 0 (a+1)) := by
        ext x; simp only [mem_insert,mem_Ioo]; omega
      unfold mass rect at ih ⊢
      rw [sum_product] at ih ⊢
      rw [e,sum_insert (by simp)]
      have h := stick (a+1) b hb
      change (∑ j ∈ Ioo 0 b, weight (a+1,j)) + 1 = _ at h
      have step := Nat.choose_succ_succ (a+1+b) (a+1)
      rw [show a+1+1+b = (a+1+b)+1 by omega]
      simp only [Nat.succ_eq_add_one] at ih step h ⊢
      omega

  have swapped_mass (n m : ℕ) : mass (wedge n m) = mass (mirror n m) := by
    unfold mass
    apply sum_nbij' Prod.swap Prod.swap
    · intro p hp
      simpa [wedge,mirror,mem_tri,Nat.add_comm,and_comm,and_left_comm,and_assoc] using hp
    · intro p hp
      simpa [wedge,mirror,mem_tri,Nat.add_comm,and_comm,and_left_comm,and_assoc] using hp
    · intro p _; rfl
    · intro p _; rfl
    · intro p _
      change (p.1+p.2).choose p.1 = (p.2+p.1).choose p.2
      rw [Nat.add_comm p.2 p.1]
      exact Nat.choose_symm_of_eq_add rfl

  have middle_mass (n m : ℕ) (hm : 0 < m) (lo : 2*m ≤ n) (hi : n ≤ 2*m+1) :
      2 * mass (wedge n m) = mass (tri n) + 2*m := by
    have square : rect m m = (tri n).filter (fun p => p.1 < m ∧ p.2 < m) := by
      ext p
      simp only [rect,mem_product,mem_Ioo,mem_filter,mem_tri]
      omega
    have corner : {(m,m)} = (tri n).filter (fun p => p = (m,m)) := by
      ext p
      simp only [mem_singleton,mem_filter,mem_tri]
      constructor
      · rintro rfl
        exact ⟨⟨hm,hm,by omega⟩,rfl⟩
      · exact And.right
    have account : mass (wedge n m) + mass (mirror n m) + mass (rect m m) =
        mass (tri n) + mass {(m,m)} := by
      unfold mass wedge mirror
      rw [square,corner]
      simp only [sum_filter,← sum_add_distrib]
      apply sum_congr rfl
      intro p hp
      have h := (mem_tri.mp hp).2.2
      have eq : p = (m,m) ↔ p.1=m ∧ p.2=m := Prod.ext_iff
      simp only [eq]
      split_ifs <;> omega
    have hr := rectangle_mass m m hm hm
    rw [← swapped_mass] at account
    have hp : mass {(m,m)} = (m+m).choose m := by simp [mass,weight]
    rw [hp] at account
    omega

  let proj (A B : ℤ) (p : (ℕ × ℕ)) : ℤ := A*p.1 + B*p.2

  let high (n : ℕ) (A B d : ℤ) := (tri n).filter (fun p => d < proj A B p)
  let low (n : ℕ) (A B d : ℤ) := (tri n).filter (fun p => proj A B p ≤ d)

  have partition (n : ℕ) (A B d : ℤ) :
      mass (high n A B d) + mass (low n A B d) = mass (tri n) := by
    unfold mass high low
    simp only [sum_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro p _
    split_ifs <;> omega

  /- If both closed half-planes through a pivot have strict majorities, no parallel cut bisects. -/
  have pivot_majority {n : ℕ} (A B d : ℤ) (P : (ℕ × ℕ)) {L R : Finset (ℕ × ℕ)}
      (hl : mass (tri n) < 2*mass L) (hr : mass (tri n) < 2*mass R)
      (left : ∀ p ∈ L, p ∈ tri n ∧ proj A B p ≤ proj A B P)
      (right : ∀ p ∈ R, p ∈ tri n ∧ proj A B P ≤ proj A B p) :
      mass (high n A B d) ≠ mass (low n A B d) := by
    have total := partition n A B d
    by_cases h : proj A B P ≤ d
    · have hsub : L ⊆ low n A B d := by
        intro p hp
        obtain ⟨ht,hp'⟩ := left p hp
        exact mem_filter.mpr ⟨ht,hp'.trans h⟩
      have := mass_mono hsub
      omega
    · have hsub : R ⊆ high n A B d := by
        intro p hp
        obtain ⟨ht,hp'⟩ := right p hp
        exact mem_filter.mpr ⟨ht,(lt_of_not_ge h).trans_le hp'⟩
      have := mass_mono hsub
      omega

  have coord_compare {A B : ℤ} (ha : 0 ≤ A) (hb : B ≤ 0)
      {p q : (ℕ × ℕ)} (hx : p.1 ≤ q.1) (hy : q.2 ≤ p.2) : proj A B p ≤ proj A B q :=
    add_le_add (mul_le_mul_of_nonneg_left (by exact_mod_cast hx) ha)
      (mul_le_mul_of_nonpos_left (by exact_mod_cast hy) hb)

  have opposite_coefficients (n : ℕ) (hn : 2 ≤ n) (A B d : ℤ) (hab : A*B ≤ 0) :
      mass (high n A B d) ≠ mass (low n A B d) := by
    let m := n/2
    have wedge_major : mass (tri n) < 2*mass (wedge n m) := by
      rw [middle_mass n m (by dsimp [m]; omega) (by dsimp [m]; omega) (by dsimp [m]; omega)]
      dsimp [m]
      omega
    have mirror_major := wedge_major
    rw [swapped_mass] at mirror_major
    rcases mul_nonpos_iff.mp hab with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · apply pivot_majority A B d (m,m) wedge_major mirror_major
      · intro p hp
        obtain ⟨ht,hx,hy⟩ := mem_filter.mp hp
        exact ⟨ht,coord_compare ha hb hx hy⟩
      · intro p hp
        obtain ⟨ht,hy,hx⟩ := mem_filter.mp hp
        exact ⟨ht,coord_compare ha hb hx hy⟩
    · have cmp {p q : (ℕ × ℕ)} (hx : q.1 ≤ p.1) (hy : p.2 ≤ q.2) : proj A B p ≤ proj A B q :=
        add_le_add (mul_le_mul_of_nonpos_left (by exact_mod_cast hx) ha)
          (mul_le_mul_of_nonneg_left (by exact_mod_cast hy) hb)
      apply pivot_majority A B d (m,m) mirror_major wedge_major
      · intro p hp
        obtain ⟨ht,hy,hx⟩ := mem_filter.mp hp
        exact ⟨ht,cmp hx hy⟩
      · intro p hp
        obtain ⟨ht,hx,hy⟩ := mem_filter.mp hp
        exact ⟨ht,cmp hx hy⟩

  have mass_column (n m : ℕ) (hm : 0 < m) (hmn : m ≤ n) :
      mass ((tri n).filter (fun p => p.1 = m)) + 1 = (n+1).choose (m+1) := by
    have e : mass ((tri n).filter (fun p => p.1 = m)) =
        ∑ j ∈ Ioo 0 (n-m+1), (m+j).choose m := by
      unfold mass
      apply sum_nbij' Prod.snd (fun j => (m,j))
      · intro p hp
        obtain ⟨ht,hx⟩ := mem_filter.mp hp
        obtain ⟨_,_,_⟩ := mem_tri.mp ht
        simp only [mem_Ioo]
        omega
      · intro j hj
        obtain ⟨_,_⟩ := mem_Ioo.mp hj
        exact mem_filter.mpr ⟨mem_tri.mpr ⟨hm,by dsimp; omega,by dsimp; omega⟩,rfl⟩
      · intro p hp
        exact Prod.ext (mem_filter.mp hp).2.symm rfl
      · intro _ _; rfl
      · intro p hp
        simp only [weight,(mem_filter.mp hp).2]
    rw [e, ← show m+(n-m+1)=n+1 by omega]
    exact stick m (n-m+1) (by omega)

  have even_column (m : ℕ) :
      (tri (2*m)).filter (fun p => m ≤ p.1) = mirror (2*m) m := by
    ext p
    simp only [mirror,mem_filter,mem_tri]
    omega

  have even_steep (m : ℕ) (hm : 0 < m) (u v d : ℤ)
      (hu : 0 ≤ u) (hv : ((m:ℤ)-1)*u ≤ v) :
      mass (high (2*m) (u+v) u d) ≠ mass (low (2*m) (u+v) u d) := by
    let n := 2*m
    let P : (ℕ × ℕ) := (m,1)
    let L := (tri n).filter (fun p => p.1 < m ∨ p=P)
    let R := mirror n m
    have hP : P ∈ tri n := mem_tri.mpr ⟨hm,by change 0 < 1; decide,by dsimp [n,P]; omega⟩
    have balance : 2*mass R = mass (tri n)+2*m := by
      dsimp [R]
      rw [← swapped_mass]
      exact middle_mass n m hm (by rfl) (by dsimp [n]; omega)
    have account : mass L + mass R = mass (tri n) + weight P := by
      have he : {P} = (tri n).filter (fun p => p=P) := by
        ext p; simp only [mem_singleton,mem_filter]; exact ⟨fun e => ⟨e ▸ hP,e⟩,And.right⟩
      have hs : weight P = mass {P} := by simp [mass]
      rw [hs]
      unfold R L
      dsimp only [n]
      rw [← even_column,he]
      dsimp only [n]
      simp only [mass,sum_filter,← sum_add_distrib]
      apply sum_congr rfl
      intro p hp
      by_cases eqP : p = P
      · subst p
        simp [P]
      · simp only [eqP,or_false,ite_false,add_zero]
        split_ifs <;> omega
    have wp : weight P = m+1 := by
      change (m+1).choose m = m+1
      rw [Nat.choose_symm_of_eq_add (show m+1=m+1 by rfl),Nat.choose_one_right]
    have hv0 : 0 ≤ v := by
      have := mul_nonneg (show 0 ≤ (m:ℤ)-1 by omega) hu
      omega
    apply pivot_majority (n:=n) (u+v) u d P (L:=L) (R:=R) (by omega) (by omega)
    · intro p hp
      obtain ⟨ht,hx | rfl⟩ := mem_filter.mp hp
      · refine ⟨ht,?_⟩
        obtain ⟨_,_,hs⟩ := mem_tri.mp ht
        have h₁ : u*((p.1:ℤ)+p.2) ≤ u*(2*m) := mul_le_mul_of_nonneg_left (by dsimp [n] at hs; omega) hu
        have h₂ : v*(p.1:ℤ) ≤ v*(m-1) := mul_le_mul_of_nonneg_left (by omega) hv0
        dsimp [proj,P]
        nlinarith
      · exact ⟨ht,le_rfl⟩
    · intro p hp
      obtain ⟨ht,_,hx⟩ := mem_filter.mp hp
      obtain ⟨_,hy,_⟩ := mem_tri.mp ht
      exact ⟨ht,add_le_add (mul_le_mul_of_nonneg_left (by exact_mod_cast hx) (by omega))
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hy) hu)⟩

  have odd_steep (m : ℕ) (hm : 0 < m) (u v d : ℤ)
      (hu : 0 ≤ u) (hv : ((m:ℤ)-1)*u ≤ v) :
      mass (high (2*m+1) (u+v) u d) ≠ mass (low (2*m+1) (u+v) u d) := by
    let n := 2*m+1
    let P : (ℕ × ℕ) := (m,m+1)
    let L := wedge n m
    let R := (tri n).filter (fun p => m < p.1 ∨ p=P)
    let C := (tri n).filter (fun p => p.1=m)
    have hP : P ∈ tri n := mem_tri.mpr ⟨hm,by dsimp [P]; omega,by dsimp [P,n]; omega⟩
    have balance : 2*mass L = mass (tri n)+2*m :=
      middle_mass n m hm (by dsimp [n]; omega) le_rfl
    have account : mass R + mass C = mass (mirror n m) + (weight P + weight P) := by
      have he : {P} = (tri n).filter (fun p => p=P) := by
        ext p; simp only [mem_singleton,mem_filter]; exact ⟨fun e => ⟨e ▸ hP,e⟩,And.right⟩
      have hs : weight P = mass {P} := by simp [mass]
      rw [hs]
      unfold R C mirror mass
      rw [he]
      simp only [sum_filter,← sum_add_distrib]
      apply sum_congr rfl
      intro p hp
      have ht := (mem_tri.mp hp).2.2
      have eq : p=P ↔ p.1=m ∧ p.2=m+1 := Prod.ext_iff
      dsimp [n] at ht
      simp only [eq]
      split_ifs <;> omega
    have column := mass_column n m hm (by dsimp [n]; omega)
    change mass C + 1 = _ at column
    have wp : (n+1).choose (m+1) = weight P + weight P := by
      change (n+1).choose (m+1) = (m+(m+1)).choose m + (m+(m+1)).choose m
      rw [Nat.choose_succ_succ, ← show m+(m+1)=n by dsimp [n]; omega,
        ← Nat.choose_symm_of_eq_add (show m+(m+1)=m+(m+1) by rfl)]
    rw [wp] at column
    rw [← swapped_mass] at account
    change mass R + mass C = mass L + _ at account
    have hv0 : 0 ≤ v := by
      have := mul_nonneg (show 0 ≤ (m:ℤ)-1 by omega) hu
      omega
    apply pivot_majority (n:=n) (u+v) u d P (L:=L) (R:=R) (by omega) (by omega)
    · intro p hp
      obtain ⟨ht,hx,_⟩ := mem_filter.mp hp
      refine ⟨ht,?_⟩
      have ht' := (mem_tri.mp ht).2.2
      have h₁ : u*((p.1:ℤ)+p.2) ≤ u*(2*m+1) := mul_le_mul_of_nonneg_left (by dsimp [n] at ht'; omega) hu
      have h₂ : v*(p.1:ℤ) ≤ v*m := mul_le_mul_of_nonneg_left (by exact_mod_cast hx) hv0
      dsimp [proj,P]
      nlinarith
    · intro p hp
      obtain ⟨ht,hx | rfl⟩ := mem_filter.mp hp
      · refine ⟨ht,?_⟩
        have hy := (mem_tri.mp ht).2.1
        have h₁ : u*(m+2) ≤ u*((p.1:ℤ)+p.2) := mul_le_mul_of_nonneg_left (by omega) hu
        have h₂ : v*(m+1) ≤ v*(p.1:ℤ) := mul_le_mul_of_nonneg_left (by omega) hv0
        dsimp [proj,P]
        nlinarith
      · exact ⟨ht,le_rfl⟩

  have swap_filtered (n : ℕ) (A B : ℤ) (Q : ℤ → Prop) [DecidablePred Q] :
      mass ((tri n).filter (fun p => Q (proj A B p))) =
      mass ((tri n).filter (fun p => Q (proj B A p))) := by
    have flip (C D : ℤ) (p : (ℕ × ℕ)) :
        proj D C p.swap = proj C D p := by simp [proj,add_comm]
    have mem (C D : ℤ) (p : (ℕ × ℕ))
        (hp : p ∈ (tri n).filter (fun p => Q (proj C D p))) :
        p.swap ∈ (tri n).filter (fun p => Q (proj D C p)) := by
      obtain ⟨ht,hq⟩ := mem_filter.mp hp
      refine mem_filter.mpr ⟨?_,(flip C D p) ▸ hq⟩
      simpa [mem_tri,Nat.add_comm,and_left_comm] using ht
    unfold mass
    apply sum_nbij' Prod.swap Prod.swap (mem A B) (mem B A) (fun _ _ => rfl) (fun _ _ => rfl)
    intro p _
    change (p.1+p.2).choose p.1 = (p.2+p.1).choose p.2
    rw [Nat.add_comm p.2 p.1]
    exact Nat.choose_symm_of_eq_add rfl

  have swap_unequal (n : ℕ) (A B d : ℤ) :
      (mass (high n A B d) ≠ mass (low n A B d)) ↔
      (mass (high n B A d) ≠ mass (low n B A d)) := by
    unfold high low
    rw [swap_filtered n A B (fun z => d < z),swap_filtered n A B (fun z => z ≤ d)]

  have neg_unequal (n : ℕ) (A B d : ℤ) :
      (mass (high n A B d) ≠ mass (low n A B d)) ↔
      (mass (high n (-A) (-B) (-d-1)) ≠ mass (low n (-A) (-B) (-d-1))) := by
    have hi : high n (-A) (-B) (-d-1) = low n A B d := by
      apply filter_congr
      intro p _
      simp only [proj,neg_mul]
      omega
    have lo : low n (-A) (-B) (-d-1) = high n A B d := by
      apply filter_congr
      intro p _
      simp only [proj,neg_mul]
      omega
    rw [hi,lo]
    exact ne_comm

  let bary (p : (ℕ × ℕ)) : (ℕ × ℕ) := (p.2,p.1-p.2)
  let rowCol (p : (ℕ × ℕ)) : (ℕ × ℕ) := (p.1+p.2,p.1)

  have mem_entries {n : ℕ} {p : (ℕ × ℕ)} :
      p ∈ entries n ↔ 0 < p.2 ∧ p.2 < p.1 ∧ p.1 ≤ n := by
    simp only [entries,mem_filter,mem_product,mem_range]
    omega

  have reindex (n : ℕ) (f : (ℕ × ℕ) → ℕ) :
      (∑ p ∈ entries n, f (bary p)) = ∑ q ∈ tri n, f q := by
    apply sum_nbij' bary rowCol
    · intro p hp
      obtain ⟨_,_,_⟩ := mem_entries.mp hp
      simp only [mem_tri,bary]
      omega
    · intro q hq
      obtain ⟨_,_,_⟩ := mem_tri.mp hq
      simp only [mem_entries,rowCol]
      omega
    · intro p hp
      obtain ⟨_,_,_⟩ := mem_entries.mp hp
      apply Prod.ext <;> dsimp [bary,rowCol] <;> omega
    · intro q hq
      apply Prod.ext <;> dsimp [bary,rowCol] <;> omega
    · intro p _; rfl

  have mass_original (n : ℕ) (u v : ℤ) (Q : ℤ → Prop) [DecidablePred Q] :
      (∑ p ∈ (entries n).filter (fun p => Q (u*(p.1:ℤ)+v*p.2)), p.1.choose p.2) =
        mass ((tri n).filter (fun p => Q (proj (u+v) u p))) := by
    unfold mass
    rw [sum_filter,sum_filter,← reindex]
    apply sum_congr rfl
    intro p hp
    have h := (mem_entries.mp hp).2.1.le
    have hw : weight (bary p) = p.1.choose p.2 := by
      simp only [weight,bary,Nat.add_sub_of_le h]
    have he : proj (u+v) u (bary p) = u*p.1+v*p.2 := by
      simp only [proj,bary,Nat.cast_sub h]
      ring
    rw [he,hw]

  let Unequal (n : ℕ) (u v d : ℤ) : Prop :=
    (∑ p ∈ (entries n).filter (fun p => d < u*(p.1:ℤ)+v*p.2), p.1.choose p.2) ≠
      ∑ p ∈ (entries n).filter (fun p => u*(p.1:ℤ)+v*p.2 ≤ d), p.1.choose p.2

  have original_iff (n : ℕ) (u v d : ℤ) :
      Unequal n u v d ↔ mass (high n (u+v) u d) ≠ mass (low n (u+v) u d) := by
    unfold Unequal high low
    rw [mass_original n u v (fun z => d < z),mass_original n u v (fun z => z ≤ d)]

  have central_sector (n : ℕ) (hn : 2 ≤ n) (u v d : ℤ) (h : u*(u+v) ≤ 0) :
      Unequal n u v d :=
    (original_iff n u v d).mpr (opposite_coefficients n hn (u+v) u d (by simpa [mul_comm] using h))

  let cutMass (n : ℕ) (u v d : ℤ) : ℕ :=
    ∑ p ∈ (entries n).filter (fun p => u*(p.1:ℤ)+v*p.2 ≤ d), Nat.choose p.1 p.2

  let total (n : ℕ) := 2^(n+1) - 2*(n+1)

  let row (r : ℕ) (u v d : ℤ) : ℕ :=
    ∑ k ∈ Ioc 0 (r-1), if u*(r:ℤ)+v*k ≤ d then Nat.choose r k else 0

  have mass_rows (n : ℕ) (u v d : ℤ) :
      cutMass n u v d = ∑ r ∈ range (n+1), row r u v d := by
    unfold cutMass entries row
    rw [sum_filter, sum_filter, sum_product]
    refine sum_congr rfl fun r hr => ?_
    rw [mem_range] at hr
    have he : ((range (n+1)).filter (fun k => 1 ≤ k ∧ k+1 ≤ r)) = Ioc 0 (r-1) := by
      ext k
      simp only [mem_filter, mem_range, mem_Ioc]
      omega
    rw [← he, sum_filter]

  have mass_zero (u v d : ℤ) : cutMass 0 u v d = 0 := by simp [cutMass, entries]

  have mass_succ (n : ℕ) (u v d : ℤ) :
      cutMass (n+1) u v d = cutMass n u v d + row (n+1) u v d := by
    simp only [mass_rows, sum_range_succ _ (n+1)]

  let rowPrefix (r k : ℕ) := ∑ x ∈ Ioc 0 k, r.choose x

  have full_row (n : ℕ) : rowPrefix (n+1) n + 2 = 2^(n+1) := by
    have h := Nat.sum_range_choose (n+1)
    rw [sum_range_succ] at h
    have hh : ∑ x ∈ range (n+1), (n+1).choose x = 1 + rowPrefix (n+1) n := by
      have he : range (n+1) = insert 0 (Ioc 0 n) := by ext x; simp
      rw [he,
        sum_insert (by simp), Nat.choose_zero_right]
    rw [hh,Nat.choose_self] at h
    omega

  have total_eq (n : ℕ) : cutMass n 0 0 0 = total n := by
    induction n with
    | zero => simp [mass_zero,total]
    | succ n ih =>
      rw [mass_succ, ih]
      have h : row (n+1) 0 0 0 = rowPrefix (n+1) n := by simp [row,rowPrefix]
      rw [h]
      have h₁ := full_row n
      have h₂ : n+1 ≤ 2^n := Nat.lt_two_pow_self (n := n)
      unfold total
      rw [pow_succ 2 (n+1),pow_succ 2 n]
      omega

  have complement (n : ℕ) (u v d : ℤ) :
      cutMass n u v d + cutMass n (-u) (-v) (-d-1) = total n := by
    rw [← total_eq, mass_rows, mass_rows, mass_rows, ← sum_add_distrib]
    refine sum_congr rfl fun r hr => ?_
    unfold row
    rw [← sum_add_distrib]
    refine sum_congr rfl fun k hk => ?_
    simp only [neg_mul, zero_mul, zero_add, le_refl, if_true]
    split_ifs <;> omega

  have row_dominant (n : ℕ) (hn : 2 ≤ n) (u v d : ℤ) (hu : 0 ≤ u) (hv : 0 ≤ v)
      (slope : ((n:ℤ)-3)*v ≤ u) : cutMass n u v d ≠ cutMass n (-u) (-v) (-d-1) := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    change cutMass (k+1) u v d ≠ cutMass (k+1) (-u) (-v) (-d-1)
    have allmass : cutMass k u v d ≤ cutMass k 0 0 0 := by
      unfold cutMass
      apply sum_le_sum_of_subset
      intro p hp
      exact mem_filter.mpr ⟨(mem_filter.mp hp).1,by simp⟩
    have gap : total (k+1) = 2*total k + 2*k := by
      have kpow : k+1 ≤ 2^k := Nat.lt_two_pow_self
      unfold total
      rw [pow_succ 2 (k+1),pow_succ 2 k]
      omega
    have comp := complement (k+1) u v d
    rw [mass_succ,gap,← total_eq] at comp
    rw [mass_succ]
    by_cases cut : d < u*((k:ℤ)+1)+v
    · have empty : row (k+1) u v d = 0 := by
        unfold row
        apply sum_eq_zero
        intro j hj
        obtain ⟨hj,_⟩ := mem_Ioc.mp hj
        have hjv : v*1 ≤ v*(j:ℤ) := mul_le_mul_of_nonneg_left (by omega) hv
        simp only [Nat.cast_add,Nat.cast_one]
        rw [if_neg (by omega)]
      rw [empty] at comp ⊢
      omega
    · have prior : cutMass k u v d = cutMass k 0 0 0 := by
        unfold cutMass
        congr 1
        apply filter_congr
        intro p hp
        obtain ⟨box,_,hk⟩ := mem_filter.mp hp
        have hr := mem_range.mp (mem_product.mp box).1
        have h₁ : u*(p.1:ℤ) ≤ u*k := mul_le_mul_of_nonneg_left (by omega) hu
        have h₂ : v*(p.2:ℤ) ≤ v*(k-1) := mul_le_mul_of_nonneg_left (by omega) hv
        push_cast at slope
        simp only [zero_mul,zero_add,le_refl,iff_true]
        nlinarith
      have head : k+1 ≤ row (k+1) u v d := by
        unfold row
        have hj : 1 ∈ Ioc 0 (k+1-1) := mem_Ioc.mpr ⟨by decide,by omega⟩
        have hh := single_le_sum (f := fun j : ℕ => if u*((k+1:ℕ):ℤ)+v*j ≤ d then (k+1).choose j else 0)
          (fun _ _ => Nat.zero_le _) hj
        simpa only [Nat.cast_one,mul_one, Nat.cast_add, if_pos (by omega : u*((k:ℤ)+1)+v ≤ d),
          Nat.choose_one_right] using hh
      rw [prior] at comp ⊢
      omega

  have clamp_threshold {n : ℕ} {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b)
      (hau : a ≤ 2*(n:ℤ)) (hbu : b ≤ 2*(n:ℤ)) (d : ℤ) :
      ∃ t : ℤ, |t| ≤ 4*(n:ℤ)^2+1 ∧ (Unequal n a b d ↔ Unequal n a b t) := by
    let M := 4*(n:ℤ)^2
    let t := max (-1) (min M d)
    have hm : 0 ≤ M := by dsimp [M]; positivity
    have ht : |t| ≤ M+1 := by rw [abs_le]; dsimp [t]; omega
    have rng (p : (ℕ × ℕ)) (hp : p ∈ entries n) : 0 ≤ a*(p.1:ℤ)+b*p.2 ∧ a*(p.1:ℤ)+b*p.2 ≤ M := by
      obtain ⟨_,hk,hr⟩ := mem_entries.mp hp
      have h₁ : a*(p.1:ℤ) ≤ (2*(n:ℤ))*n := mul_le_mul hau (by exact_mod_cast hr) (by positivity) (by positivity)
      have h₂ : b*(p.2:ℤ) ≤ (2*(n:ℤ))*n := mul_le_mul hbu (by omega) (by positivity) (by positivity)
      exact ⟨by positivity, by dsimp [M]; nlinarith⟩
    have eqb (p : (ℕ × ℕ)) (hp : p ∈ entries n) : a*(p.1:ℤ)+b*p.2 ≤ d ↔ a*(p.1:ℤ)+b*p.2 ≤ t := by
      have := rng p hp
      dsimp [t]
      omega
    have hi : (entries n).filter (fun p => d < a*(p.1:ℤ)+b*p.2) =
        (entries n).filter (fun p => t < a*(p.1:ℤ)+b*p.2) :=
      filter_congr fun p hp => by have := eqb p hp; omega
    have lo := filter_congr (s := entries n) (fun p hp => eqb p hp)
    exact ⟨t,ht,by unfold Unequal; rw [hi,lo]⟩

  have normalize (n : ℕ) (hn : 2 ≤ n)
      (pos : ∀ a b t : ℤ, 0 < a → 0 ≤ b → a ≤ 2*(n:ℤ) → b ≤ 2*(n:ℤ) →
        |t| ≤ 4*(n:ℤ)^2+1 → Unequal n a b t)
      (u v d : ℤ) (hu : |u| ≤ 2*(n:ℤ)) (hv : |v| ≤ 2*(n:ℤ)) : Unequal n u v d := by
    have pos' (a b t : ℤ) (ha : 0 < a) (hb : 0 ≤ b) (hau : a ≤ 2*(n:ℤ)) (hbu : b ≤ 2*(n:ℤ)) :
        mass (high n (a+b) a t) ≠ mass (low n (a+b) a t) := by
      obtain ⟨s,hs,he⟩ := clamp_threshold ha.le hb hau hbu t
      exact (original_iff ..).mp (he.mpr (pos a b s ha hb hau hbu hs))
    have liftPos (A B t : ℤ) (ha : 0 < A) (hb : 0 < B) (hB : B ≤ 2*(n:ℤ))
        (hD : |A-B| ≤ 2*(n:ℤ)) : mass (high n A B t) ≠ mass (low n A B t) := by
      rw [abs_le] at hD
      rcases le_total B A with ord | ord
      · simpa only [show B+(A-B)=A by omega] using pos' B (A-B) t hb (by omega) hB (by omega)
      · apply (swap_unequal n A B t).mpr
        simpa only [show A+(B-A)=B by omega] using pos' A (B-A) t ha (by omega) (by omega) (by omega)
    by_cases hc : u*(u+v) ≤ 0
    · exact central_sector n hn u v d hc
    · apply (original_iff ..).mpr
      rw [abs_le] at hu hv
      rcases mul_pos_iff.mp (lt_of_not_ge hc) with hp | hp
      · exact liftPos _ _ _ hp.2 hp.1 hu.2 (by rw [abs_le]; omega)
      · apply (neg_unequal n (u+v) u d).mpr
        exact liftPos _ _ _ (by omega) (by omega) (by omega) (by rw [abs_le]; omega)

  have canonical_extremes {n : ℕ} (hn : 2 ≤ n) (a b d : ℤ) (ha : 0 < a) (hb : 0 ≤ b)
      (h : ((n/2:ℕ):ℤ)*a-a ≤ b ∨ ((n:ℤ)-3)*b ≤ a) : Unequal n a b d := by
    rcases h with h | h
    · let m := n/2
      have hm : 0 < m := by dsimp [m]; omega
      have slope : ((m:ℤ)-1)*a ≤ b := by rw [sub_mul,one_mul]; exact h
      apply (original_iff ..).mpr
      rcases (show n=2*m ∨ n=2*m+1 by dsimp [m]; omega) with he | he
      · rw [he]; exact even_steep m hm a b d ha.le slope
      · rw [he]; exact odd_steep m hm a b d ha.le slope
    · unfold Unequal
      have he : (entries n).filter (fun p => d < a*(p.1:ℤ)+b*p.2) =
          (entries n).filter (fun p => (-a)*(p.1:ℤ)+(-b)*p.2 ≤ -d-1) := by
        apply filter_congr
        intro p _
        simp only [neg_mul]
        omega
      rw [he]
      exact (row_dominant n hn a b d ha.le hb h).symm

  intro evenCase oddCase n hn u v d hu hv _
  apply normalize n (by omega) _ u v d hu hv
  intro a b t ha hb hau hbu ht
  by_cases h : ((n/2:ℕ):ℤ)*a-a ≤ b ∨ ((n:ℤ)-3)*b ≤ a
  · exact canonical_extremes (by omega) a b t ha hb h
  · have h₁ : a < ((n:ℤ)-3)*b := by omega
    have h₂ : b < (((n/2:ℕ):ℤ)-1)*a := by rw [sub_mul,one_mul]; omega
    have bp : 0 < b := by
      by_contra bad
      have bz : b=0 := by omega
      rw [bz,mul_zero] at h₁
      omega
    rcases (show n%2=0 ∨ n%2=1 by omega) with hp | hp
    · exact evenCase n hn hp a b t ha bp hau hbu ht h₁ h₂
    · exact oddCase n hn hp a b t ha bp hau hbu ht h₁ h₂

end OMA.R_mse_4815847_R1_H2_R1
