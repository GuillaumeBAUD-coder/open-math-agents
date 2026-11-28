import OMAReductions.R_mse_4815847_R1

/-!
# Pascal cuts in the unbounded range

Credit: @YOHSUKE-TAKAHASHI

In barycentric coordinates x=k and y=r-k, each of the two regions x≤m≤y
and y≤m≤x has mass equal to half the total plus m, with m=⌊N/2⌋.
Thus opposite coefficients of x,y can never bisect. For positive coefficients, comparison with a reference set of columns excludes
a≤b. A hockey-stick identity and a bound for the first third of a row exclude
a²+4Nab≥(Nb)² via telescoping adjacent binomial coefficients. Reflection and sign reversal
reduce all other cuts to the two parity cases below.
-/

namespace OMA.R_mse_4815847_R1_H2_R1
open OMA.S_mse_4815847

def H1 : Prop :=
  ∀ n : ℕ, 250 < n → n % 2 = 0 → ∀ a b d : ℤ,
    0 < a → 0 < b → a ≤ 2*(n:ℤ) → b ≤ 2*(n:ℤ) → |d| ≤ 4*(n:ℤ)^2+1 →
    b < a → a^2 + 4*n*a*b < ((n:ℤ)*b)^2 →
    (∑ p ∈ (entries n).filter (fun p => d < a*(p.1:ℤ)+b*p.2), p.1.choose p.2) ≠
      ∑ p ∈ (entries n).filter (fun p => a*(p.1:ℤ)+b*p.2 ≤ d), p.1.choose p.2

def H2 : Prop :=
  ∀ n : ℕ, 250 < n → n % 2 = 1 → ∀ a b d : ℤ,
    0 < a → 0 < b → a ≤ 2*(n:ℤ) → b ≤ 2*(n:ℤ) → |d| ≤ 4*(n:ℤ)^2+1 →
    b < a → a^2 + 4*n*a*b < ((n:ℤ)*b)^2 →
    (∑ p ∈ (entries n).filter (fun p => d < a*(p.1:ℤ)+b*p.2), p.1.choose p.2) ≠
      ∑ p ∈ (entries n).filter (fun p => a*(p.1:ℤ)+b*p.2 ≤ d), p.1.choose p.2

/-- All interior entries are at least their row index. -/
theorem entry_lower : ∀ n j : ℕ, 0 < j → j < n → n ≤ n.choose j
  | 0, j, _, _ => by omega
  | n+1, j, hj, hr => by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rw [Nat.choose_succ_succ']
    rcases Nat.eq_zero_or_pos j with rfl | h
    · simp
    · have := entry_lower n j h (by omega)
      have := Nat.choose_pos (show j+1 ≤ n by omega)
      omega

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

  let wt (p : ℕ × ℕ) := p.1.choose p.2
  let weightOf (s : Finset (ℕ × ℕ)) := ∑ p ∈ s, wt p
  let tailCols (t J : ℕ) := (entries t).filter (fun p => J ≤ p.2)
  let upper (t : ℕ) (a b d : ℤ) := (entries t).filter (fun p => d < a*(p.1:ℤ)+b*p.2)

  have entry_iff {t : ℕ} {p : ℕ × ℕ} :
      p ∈ entries t ↔ p.1 ≤ t ∧ 1 ≤ p.2 ∧ p.2 < p.1 := by
    simp only [entries,mem_filter,mem_product,mem_range]
    omega

  have wt_mono {s t : Finset (ℕ × ℕ)} (h : s ⊆ t) : weightOf s ≤ weightOf t :=
    sum_le_sum_of_subset h

  have prefix_step (r k : ℕ) : rowPrefix r (k+1) = rowPrefix r k + r.choose (k+1) :=
    sum_Ioc_succ_top (by omega) _

  have column_total (t j : ℕ) (hj : 0 < j) (hjt : j ≤ t) :
      weightOf ((entries t).filter (fun p => p.2 = j)) + 1 = (t+1).choose (j+1) := by
    have he : weightOf ((entries t).filter (fun p => p.2 = j)) = ∑ r ∈ Ioc j t, r.choose j := by
      unfold weightOf
      apply sum_nbij' Prod.fst (fun r => (r,j))
      · intro p hp
        obtain ⟨he,hy⟩ := mem_filter.mp hp
        obtain ⟨_,_,_⟩ := entry_iff.mp he
        exact mem_Ioc.mpr ⟨by omega,by omega⟩
      · intro r hr
        obtain ⟨lo,hi⟩ := mem_Ioc.mp hr
        exact mem_filter.mpr ⟨entry_iff.mpr ⟨hi,hj,lo⟩,rfl⟩
      · intro p hp
        exact Prod.ext rfl (mem_filter.mp hp).2.symm
      · intro _ _; rfl
      · intro p hp; simp [wt,(mem_filter.mp hp).2]
    rw [he, ← Nat.sum_Icc_choose t j]
    have hset : Icc j t = insert j (Ioc j t) := by
      ext r; simp only [mem_Icc,mem_insert,mem_Ioc]; omega
    rw [hset,sum_insert (by simp),Nat.choose_self,add_comm]

  /- Hockey-stick identity for comparison with a fixed column in every earlier row. -/
  have tail_prefix (t k : ℕ) (hk : k < t) :
      weightOf (tailCols t (t-k)) + k = rowPrefix (t+1) k := by
    induction k with
    | zero =>
      have he : tailCols t (t-0) = ∅ := by
        ext p; simp only [tailCols,mem_filter,entry_iff,notMem_empty,iff_false]; omega
      rw [he]; simp [weightOf,rowPrefix]
    | succ k ih =>
      let j := t-(k+1)
      have he : weightOf (tailCols t j) = weightOf (tailCols t (t-k)) +
          weightOf ((entries t).filter (fun p => p.2=j)) := by
        unfold weightOf tailCols
        simp only [sum_filter,← sum_add_distrib]
        apply sum_congr rfl
        intro p _
        dsimp [j]
        split_ifs <;> omega
      have col := column_total t j (by dsimp [j]; omega) (by dsimp [j]; omega)
      have sym : (t+1).choose (j+1) = (t+1).choose (k+1) :=
        Nat.choose_symm_of_eq_add (by dsimp [j]; omega)
      specialize ih (by omega)
      rw [sym] at col
      rw [prefix_step]
      change weightOf (tailCols t j) + (k+1) = _
      omega

  have prefix_pascal (t k : ℕ) :
      rowPrefix (t+1) (k+1) = rowPrefix t (k+1) + rowPrefix t k + 1 := by
    induction k with
    | zero => simp [rowPrefix]
    | succ k ih =>
      rw [prefix_step (t+1),ih,prefix_step t (k+1),Nat.choose_succ_succ]
      have e := prefix_step t k
      simp only [Nat.succ_eq_add_one]
      omega

  have double_choose (t j : ℕ) (h : 3*j+2 ≤ t) :
      2*t.choose j ≤ t.choose (j+1) := by
    refine Nat.le_of_mul_le_mul_right (c := j+1) ?_ (by omega)
    rw [Nat.choose_succ_right_eq]
    have := Nat.mul_le_mul_left (t.choose j) (show 2*(j+1) ≤ t-j by omega)
    rwa [show 2*t.choose j*(j+1) = t.choose j*(2*(j+1)) by ring]

  have prefix_bound (t k : ℕ) (h : 3*k ≤ t) :
      rowPrefix t k + 1 ≤ 2*t.choose k := by
    induction k with
    | zero => simp [rowPrefix]
    | succ k ih =>
      rw [prefix_step]
      specialize ih (by omega)
      have := double_choose t k (by omega)
      omega

  have two_rows_bound (t k : ℕ) (hk : 3*k ≤ t) :
      rowPrefix (t+1) k ≤ rowPrefix t (k+1) := by
    cases k with
    | zero => simp [rowPrefix]
    | succ k =>
      rw [prefix_pascal,prefix_step t (k+1)]
      have h₁ := prefix_bound t k (by omega)
      have h₂ := double_choose t k (by omega)
      have h₃ : t.choose (k+1) ≤ t.choose (k+1+1) := by
        refine Nat.le_of_mul_le_mul_right (c := k+1+1) ?_ (by omega)
        rw [Nat.choose_succ_right_eq]
        exact Nat.mul_le_mul_left _ (by omega)
      omega



  have upper_eq (n : ℕ) (a b d : ℤ) :
      weightOf (upper n a b d) = cutMass n (-a) (-b) (-d-1) := by
    unfold weightOf upper cutMass wt
    congr 1
    apply filter_congr
    intro p _
    simp only [neg_mul]
    omega

  have cut_prefix (t : ℕ) (a b d : ℤ) (hb : 0 < b) :
      ∃ k ≤ t, row (t+1) a b d = rowPrefix (t+1) k ∧
        (0 < k → a*((t:ℤ)+1)+b*k ≤ d) := by
    let s := (Ioc 0 t).filter (fun j : ℕ => a*((t:ℤ)+1)+b*j ≤ d)
    have hr : row (t+1) a b d = ∑ j ∈ s, (t+1).choose j := by
      simp [row,s,sum_filter]
    by_cases hs : s.Nonempty
    · let k := s.max' hs
      have hkm : k ∈ s := max'_mem .. 
      obtain ⟨hi,hd⟩ := mem_filter.mp hkm
      obtain ⟨_,hkt⟩ := mem_Ioc.mp hi
      have es : s = Ioc 0 k := by
        ext j
        constructor
        · intro hj
          exact mem_Ioc.mpr ⟨(mem_Ioc.mp (mem_filter.mp hj).1).1, le_max' _ _ hj⟩
        · intro hj
          have hp := mem_Ioc.mp hj
          have hm : b*(j:ℤ) ≤ b*k := mul_le_mul_of_nonneg_left (by exact_mod_cast hp.2) hb.le
          exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hp.1,hp.2.trans hkt⟩,by omega⟩
      exact ⟨k,hkt,by simpa only [es,rowPrefix] using hr,fun _ => hd⟩
    · have e := not_nonempty_iff_eq_empty.mp hs
      exact ⟨0,Nat.zero_le _,by simp [hr,e,rowPrefix],by omega⟩

  have balance_gap {t k : ℕ} (a b d : ℤ) (hr : row (t+1) a b d = rowPrefix (t+1) k)
      (eq : cutMass (t+1) a b d = weightOf (upper (t+1) a b d)) :
      rowPrefix (t+1) k = weightOf (upper t a b d) + t := by
    have gap : total (t+1) = 2*total t + 2*t := by
      have h : t+1 ≤ 2^t := Nat.lt_two_pow_self
      unfold total
      rw [pow_succ 2 (t+1),pow_succ 2 t]
      omega
    have cn := complement (t+1) a b d
    have ct := complement t a b d
    rw [upper_eq] at eq ⊢
    rw [← eq,mass_succ,hr,gap] at cn
    omega

  have earlier_anchor {t k : ℕ} (hk : k < t) (a b d : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (bal : rowPrefix (t+1) k = weightOf (upper t a b d) + t) :
      d < a*(t:ℤ)+b*((t:ℤ)-k-1) := by
    by_contra! hd
    let U := upper t a b d
    let C := tailCols t (t-k)
    have hsub : U ⊆ C := by
      intro p hp
      obtain ⟨he,hu⟩ := mem_filter.mp hp
      refine mem_filter.mpr ⟨he,?_⟩
      obtain ⟨hr,_,_⟩ := entry_iff.mp he
      by_contra! he'
      have h₁ : a*(p.1:ℤ) ≤ a*t := mul_le_mul_of_nonneg_left (by exact_mod_cast hr) ha
      have h₂ : b*(p.2:ℤ) ≤ b*((t:ℤ)-k-1) := mul_le_mul_of_nonneg_left (by omega) hb
      omega
    have gap := tail_prefix t k hk
    change weightOf C + k = _ at gap
    change _ = weightOf U + t at bal
    by_cases hrev : C ⊆ U
    · have := wt_mono hrev
      omega
    · obtain ⟨p,hp,hp'⟩ := Finset.not_subset.mp hrev
      have ins : insert p U ⊆ C := insert_subset hp hsub
      have hi := wt_mono ins
      have hsum : weightOf (insert p U) = wt p + weightOf U := by
        unfold weightOf; rw [sum_insert hp']
      rw [hsum] at hi
      obtain ⟨he,hj⟩ := mem_filter.mp hp
      obtain ⟨hr,hj',hjlt⟩ := entry_iff.mp he
      have hwt : p.1 ≤ wt p := entry_lower _ _ hj' hjlt
      omega

  have penultimate_bound {t k : ℕ} (hk : k+1 < t) (a b d : ℤ) (hb : 0 ≤ b)
      (hcut : d < a*(t:ℤ)+b*((t:ℤ)-k-1)) :
      rowPrefix t (k+1) ≤ weightOf (upper t a b d) := by
    let f (j : ℕ) : ℕ × ℕ := (t,t-j)
    have sub : (Ioc 0 (k+1)).image f ⊆ upper t a b d := by
      intro p hp
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hp
      obtain ⟨hjpos,hjle⟩ := mem_Ioc.mp hj
      have hle : b*((t:ℤ)-k-1) ≤ b*((t-j:ℕ):ℤ) :=
        mul_le_mul_of_nonneg_left (by omega) hb
      exact mem_filter.mpr ⟨entry_iff.mpr ⟨le_rfl,by dsimp [f]; omega,by dsimp [f]; omega⟩,
        by dsimp [f]; omega⟩
    have e : weightOf ((Ioc 0 (k+1)).image f) = rowPrefix t (k+1) := by
      unfold weightOf rowPrefix
      rw [sum_image]
      · apply sum_congr rfl
        intro j hj
        change t.choose (t-j) = t.choose j
        exact Nat.choose_symm (by have := mem_Ioc.mp hj; omega)
      · intro j hj l hl hh
        have eq : t-j = t-l := congrArg Prod.snd hh
        have := mem_Ioc.mp hj
        have := mem_Ioc.mp hl
        omega
    exact e ▸ wt_mono sub



  /- A hypothetical balanced positive cut must satisfy both bounds on its last-row prefix. -/
  have balanced_locus (t : ℕ) (ht : 3 ≤ t) (a b d : ℤ) (ha : 0 < a) (hb : 0 < b)
      (bal : cutMass (t+1) a b d = weightOf (upper (t+1) a b d)) :
      ∃ k : ℕ, t < 3*k ∧ k < t ∧ a*((t:ℤ)+1)+b*k ≤ d ∧
        d < a*(t:ℤ)+b*((t:ℤ)-k-1) ∧ rowPrefix (t+1) k = weightOf (upper t a b d)+t := by
    obtain ⟨k,hkt,hr,hd⟩ := cut_prefix t a b d hb
    have gap := balance_gap a b d hr bal
    have hk0 : 0 < k := by
      by_contra! hz
      have : k=0 := by omega
      simp [this,rowPrefix] at gap
      omega
    have hk : k < t := by
      by_contra! he
      have eqk : k=t := by omega
      have hprev := complement t a b d
      have htot : total t + 2*(t+1) = 2^(t+1) := by
        have h : t+1 ≤ 2^t := Nat.lt_two_pow_self
        unfold total; rw [pow_succ]; omega
      rw [eqk,upper_eq] at gap
      have hrow := full_row t
      omega
    have hc := earlier_anchor hk a b d ha.le hb.le gap
    refine ⟨k,?_,hk,hd hk0,hc,gap⟩
    by_contra! hsmall
    have h₁ := two_rows_bound t k hsmall
    have h₂ := penultimate_bound (show k+1<t by omega) a b d hb.le hc
    omega

  have three_row_slope (n : ℕ) (hn : 4 ≤ n) (a b d : ℤ) (ha : 0 < a) (hb : 0 < b)
      (h : ((n:ℤ)-6)*b ≤ 3*a) :
      (∑ p ∈ (entries n).filter (fun p => d < a*(p.1:ℤ)+b*p.2), p.1.choose p.2) ≠
        ∑ p ∈ (entries n).filter (fun p => a*(p.1:ℤ)+b*p.2 ≤ d), p.1.choose p.2 := by
    obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    intro eq
    obtain ⟨k,hl,_,hd,hc,_⟩ := balanced_locus t (by omega) a b d ha hb eq.symm
    have hv : b*((t:ℤ)+1) ≤ b*(3*k) := mul_le_mul_of_nonneg_left (by omega) hb.le
    push_cast at h
    nlinarith



  let capSet (R q : ℕ) := (entries R).filter (fun p => q ≤ p.2 ∧ p.1+(p.2-q) ≤ R)
  let baseline (n m q : ℕ) := (entries n).filter (fun p => p.2 < q ∧ p.1+p.2 ≤ 2*m+(q-1))
  let lowerSet (n : ℕ) (a b d : ℤ) := (entries n).filter (fun p => a*(p.1:ℤ)+b*p.2 ≤ d)

  have choose_decrease (r q : ℕ) (h : r ≤ 2*q+1) : r.choose (q+1) ≤ r.choose q := by
    apply Nat.le_of_mul_le_mul_right (c:=q+1) _ (by omega)
    rw [Nat.choose_succ_right_eq]
    exact Nat.mul_le_mul_left _ (by omega)

  /- Bound all additions to the right of the reference column by one binomial coefficient. -/
  have cap_bound (R q : ℕ) (hq : 0 < q) (h : R ≤ 2*q) :
      weightOf (capSet R q) ≤ (R+2).choose (q+2) := by
    induction R generalizing q with
    | zero =>
      have he : capSet 0 q = ∅ := by
        ext p; simp only [capSet,mem_filter,entry_iff,notMem_empty,iff_false]; omega
      simp [he,weightOf]
    | succ R ih =>
      by_cases hk : q ≤ R+1
      · have split : weightOf (capSet (R+1) q) =
            weightOf ((entries (R+1)).filter (fun p => p.2=q)) + weightOf (capSet R (q+1)) := by
          have lift : capSet R (q+1) = (entries (R+1)).filter
              (fun p => q+1 ≤ p.2 ∧ p.1+(p.2-(q+1)) ≤ R) := by
            ext p; simp only [capSet,mem_filter,entry_iff]; omega
          rw [lift]
          simp only [capSet,weightOf,sum_filter,←sum_add_distrib]
          apply sum_congr rfl
          intro p hp
          have hr := (entry_iff.mp hp).1
          split_ifs <;> omega
        have col := column_total (R+1) q hq hk
        have rest := ih (q+1) (by omega) (by omega)
        have dec := choose_decrease (R+2) (q+2) (by omega)
        have step := Nat.choose_succ_succ (R+2) (q+1)
        simp only [Nat.succ_eq_add_one] at step ⊢
        rw [split]
        change weightOf _ + 1 = (R+2).choose (q+1) at col
        change weightOf _ ≤ (R+2).choose (q+3) at rest
        change (R+2).choose (q+3) ≤ (R+2).choose (q+2) at dec
        change (R+3).choose (q+2) = (R+2).choose (q+1) + (R+2).choose (q+2) at step
        change _ ≤ (R+3).choose (q+2)
        omega
      · have he : capSet (R+1) q = ∅ := by
          ext p; simp only [capSet,mem_filter,entry_iff,notMem_empty,iff_false]; omega
        rw [he]; simp [weightOf]

  have total_add (n : ℕ) : weightOf (entries n) + 2*(n+1) = 2^(n+1) := by
    have he : cutMass n 0 0 0 = weightOf (entries n) := by simp [cutMass,weightOf,wt]
    rw [←he,total_eq]
    have hp : n+1 ≤ 2^n := Nat.lt_two_pow_self
    unfold total; rw [pow_succ]; omega

  have half_row (m : ℕ) : rowPrefix (2*m+1) m + 1 = 2^(2*m) := by
    have e : range (m+1) = insert 0 (Ioc 0 m) := by ext j; simp
    have h := Nat.sum_range_choose_halfway m
    rw [e,sum_insert (by simp),Nat.choose_zero_right] at h
    rw [pow_mul]
    simpa [rowPrefix,add_comm] using h

  have base_even (m : ℕ) (hm : 2 ≤ m) :
      2*weightOf (baseline (2*m) m m) + 2*m = weightOf (entries (2*m)) := by
    have account : weightOf (baseline (2*m) m m) + weightOf (tailCols (2*m) m) = weightOf (entries (2*m)) := by
      simp only [baseline,tailCols,weightOf,sum_filter,←sum_add_distrib]
      apply sum_congr rfl
      intro p hp
      have := (entry_iff.mp hp).1
      split_ifs <;> omega
    have c := tail_prefix (2*m) m (by omega)
    rw [show 2*m-m=m by omega] at c
    have ht := total_add (2*m)
    rw [pow_succ] at ht
    have := half_row m
    omega

  have base_odd (m : ℕ) (hm : 2 ≤ m) :
      2*weightOf (baseline (2*m+1) m (m+1)) + 2*(m+1) = weightOf (entries (2*m+1)) := by
    let n := 2*m+1
    let P : ℕ × ℕ := (n,m)
    have hP : P ∈ entries n := entry_iff.mpr ⟨le_rfl,by dsimp [P]; omega,by dsimp [P,n]; omega⟩
    have corner : {P} = (entries n).filter (fun p => p=P) := by
      ext p; simp only [mem_singleton,mem_filter]; exact ⟨fun e => ⟨e ▸ hP,e⟩,And.right⟩
    have account : weightOf (baseline n m (m+1)) + weightOf (tailCols n (m+1)) + wt P = weightOf (entries n) := by
      have s : wt P = weightOf {P} := by simp [weightOf]
      rw [s,corner]
      simp only [baseline,tailCols,weightOf,sum_filter,←sum_add_distrib]
      apply sum_congr rfl
      intro p hp
      have hr := (entry_iff.mp hp).1
      have e : p=P ↔ p.1=n ∧ p.2=m := Prod.ext_iff
      simp only [e]
      dsimp [n] at hr ⊢
      split_ifs <;> omega
    have c := tail_prefix n m (by dsimp [n]; omega)
    rw [show n-m=m+1 by dsimp [n]; omega] at c
    have half := half_row m
    change rowPrefix n m + 1 = _ at half
    have ht := total_add n
    rw [pow_succ] at ht
    have hz : 2^n = 2^(2*m)*2 := pow_succ 2 (2*m)
    have hrow : rowPrefix (n+1) m + wt P = 2^n-1 := by
      obtain ⟨j,hj⟩ : ∃ j, m=j+1 := ⟨m-1,by omega⟩
      have pas := prefix_pascal n j
      have st := prefix_step n j
      rw [←hj] at st pas
      change rowPrefix (n+1) m + n.choose m = _
      omega
    change 2*weightOf (baseline n m (m+1)) + 2*(m+1) = weightOf (entries n)
    dsimp only [n] at ht
    change weightOf (entries n) + 2*((2*m+1)+1) = 2^n*2 at ht
    omega



  have wt_union_le (s t : Finset (ℕ × ℕ)) : weightOf (s ∪ t) ≤ weightOf s + weightOf t := by
    classical
    have h : weightOf (s ∪ t) + weightOf (s ∩ t) = weightOf s + weightOf t := Finset.sum_union_inter
  
    omega

  have diagonal_sector_aux (m n q : ℕ) (hm : 2 ≤ m)
      (e : (n=2*m ∧ q=m) ∨ (n=2*m+1 ∧ q=m+1)) (a b d : ℤ) (ha : 0 < a) (hb : a ≤ b) :
      weightOf (upper n a b d) ≠ weightOf (lowerSet n a b d) := by
    let L := baseline n m q
    let D := lowerSet n a b d
    let P : ℕ × ℕ := (2*m,q-1)
    have hq : 0 < q := by omega
    have hP : P ∈ L := by
      apply mem_filter.mpr
      constructor
      · apply entry_iff.mpr; dsimp [P]; omega
      · dsimp [P]; omega
    have bg : 2*weightOf L + 2*q = weightOf (entries n) := by
      rcases e with ⟨hn,hq'⟩ | ⟨hn,hq'⟩
      · simpa only [L,hn,hq'] using base_even m hm
      · simpa only [L,hn,hq'] using base_odd m hm
    have both : weightOf (upper n a b d) + weightOf D = weightOf (entries n) := by
      simp only [D,upper,lowerSet,weightOf,sum_filter,←sum_add_distrib]
      apply sum_congr rfl
      intro p _
      split_ifs <;> omega
    intro eq
    change weightOf (upper n a b d) = weightOf D at eq
    by_cases hp : P ∈ D
    · have incl : L ⊆ D := by
        intro p hx
        obtain ⟨he,hk,hs⟩ := mem_filter.mp hx
        obtain ⟨_,hcmp⟩ := mem_filter.mp hp
        have hs' : a*((p.1:ℤ)+p.2) ≤ a*((P.1:ℤ)+P.2) :=
          mul_le_mul_of_nonneg_left (by dsimp [P]; omega) ha.le
        have hk' : (b-a)*(p.2:ℤ) ≤ (b-a)*P.2 :=
          mul_le_mul_of_nonneg_left (by dsimp [P]; omega) (by omega)
        exact mem_filter.mpr ⟨he,by nlinarith⟩
      by_cases rev : D ⊆ L
      · have := wt_mono rev
        omega
      · obtain ⟨p,hin,hout⟩ := Finset.not_subset.mp rev
        have he := (mem_filter.mp hin).1
        obtain ⟨hr,hlo,hlt⟩ := entry_iff.mp he
        have large : q < p.1 := by
          by_contra! small
          apply hout
          apply mem_filter.mpr
          exact ⟨he,by omega,by omega⟩
        have hw : p.1 ≤ wt p := entry_lower _ _ hlo hlt
        have ins := wt_mono (show insert p L ⊆ D from insert_subset hin incl)
        have add : weightOf (insert p L) = wt p + weightOf L := by unfold weightOf; rw [sum_insert hout]
        rw [add] at ins
        omega
    · have miss : d < a*(P.1:ℤ)+b*P.2 := by
        by_contra! hx
        exact hp (mem_filter.mpr ⟨(mem_filter.mp hP).1,hx⟩)
      let G := capSet (2*m-2) q
      have sub : D ⊆ (L.erase P) ∪ G := by
        intro p hin
        obtain ⟨he,hval⟩ := mem_filter.mp hin
        by_cases hl : p ∈ L
        · exact mem_union.mpr (Or.inl (mem_erase.mpr ⟨by rintro rfl; exact hp hin,hl⟩))
        · apply mem_union.mpr
          right
          obtain ⟨hr,hlo,hlt⟩ := entry_iff.mp he
          have hcol : q ≤ p.2 := by
            by_contra! hk
            have far : 2*m+(q-1) < p.1+p.2 := by
              by_contra! le
              exact hl (mem_filter.mpr ⟨he,hk,le⟩)
            have eqc : p.2=P.2 := by dsimp [P]; omega
            have hrow : a*(P.1:ℤ) ≤ a*(p.1:ℤ) :=
              mul_le_mul_of_nonneg_left (by dsimp [P]; omega) ha.le
            rw [eqc] at hval
            omega
          have hk' : (b-a)*(P.2:ℤ) ≤ (b-a)*p.2 :=
            mul_le_mul_of_nonneg_left (by dsimp [P]; omega) (by omega)
          have hlt' : (p.1:ℤ)+p.2 < (P.1:ℤ)+P.2 := by
            by_contra! ge
            have hm' := mul_le_mul_of_nonneg_left ge ha.le
            nlinarith
          have hs : p.1+(p.2-q) ≤ 2*m-2 := by dsimp [P] at hlt'; omega
          exact mem_filter.mpr ⟨entry_iff.mpr ⟨by omega,hlo,hlt⟩,hcol,hs⟩
      have bound := cap_bound (2*m-2) q hq (by omega)
      rw [show 2*m-2+2=2*m by omega] at bound
      have c : (2*m).choose (q+2) ≤ wt P := by
        change _ ≤ (2*m).choose (q-1)
        rcases e with ⟨_,hq'⟩ | ⟨_,hq'⟩
        · rw [hq', Nat.choose_symm_of_eq_add (show 2*m=(m-1)+(m+1) by omega)]
          exact choose_decrease _ (m+1) (by omega)
        · simp only [hq',Nat.add_sub_cancel]
          exact (choose_decrease _ (m+1+1) (by omega)).trans
            ((choose_decrease _ (m+1) (by omega)).trans (choose_decrease _ m (by omega)))
      have wbound : weightOf G ≤ wt P := bound.trans c
      have shrink : weightOf (L.erase P) + wt P = weightOf L := L.sum_erase_add wt hP
      have hsub := wt_mono sub
      have hun := wt_union_le (L.erase P) G
      omega

  /- Both parities, uniformly in the integer threshold. -/
  have column_dominant (n : ℕ) (hn : 4 ≤ n) (a b d : ℤ) (ha : 0 < a) (hb : a ≤ b) :
      (∑ p ∈ (entries n).filter (fun p => d < a*(p.1:ℤ)+b*p.2), p.1.choose p.2) ≠
        ∑ p ∈ (entries n).filter (fun p => a*(p.1:ℤ)+b*p.2 ≤ d), p.1.choose p.2 := by
    let m := n/2
    have hm : 2 ≤ m := by dsimp [m]; omega
    rcases (show n=2*m ∨ n=2*m+1 by dsimp [m]; omega) with h | h
    · exact diagonal_sector_aux m n m hm (Or.inl ⟨h,rfl⟩) a b d ha hb
    · exact diagonal_sector_aux m n (m+1) hm (Or.inr ⟨h,rfl⟩) a b d ha hb



  /- Telescoping adjacent ratios bound a whole prefix using its last coefficient. -/
  have ratio_prefix (t k : ℕ) (hk : k ≤ t) :
      ((t:ℤ)-2*k-1) * (∑ j ∈ range k, (t.choose j : ℤ)) ≤
        ((k:ℤ)+1)*t.choose k := by
    have bound (i : ℕ) (hi : i ≤ k) :
        ((t:ℤ)-2*k-1)*(∑ j ∈ range i, (t.choose j : ℤ)) ≤ ((k:ℤ)+1)*t.choose i := by
      induction i with
      | zero => simp; omega
      | succ i ih =>
        specialize ih (by omega)
        have adj := Nat.choose_succ_right_eq t i
        have hsub : i ≤ t := by omega
        have adj' : ((i:ℤ)+1)*t.choose (i+1) = ((t:ℤ)-i)*t.choose i := by
          have hcast := congrArg (fun z : ℕ => (z:ℤ)) adj
          push_cast [Nat.cast_sub hsub] at hcast
          linarith
        have l : ((t:ℤ)-k)*t.choose i ≤ ((t:ℤ)-i)*t.choose i :=
          mul_le_mul_of_nonneg_right (by omega) (by positivity)
        have r : ((i:ℤ)+1)*t.choose (i+1) ≤ ((k:ℤ)+1)*t.choose (i+1) :=
          mul_le_mul_of_nonneg_right (by omega) (by positivity)
        rw [sum_range_succ]
        change _ ≤ ((k:ℤ)+1)*t.choose (i+1)
        linarith only [ih,l,r,adj']
    exact bound k le_rfl

  have prefix_row_identity (t k : ℕ) (hk : 0 < k) :
      rowPrefix (t+1) k = rowPrefix t k + ∑ j ∈ range k, t.choose j := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have he : range (j+1) = insert 0 (Ioc 0 j) := by ext i; simp
    rw [prefix_pascal,he,sum_insert (by simp),Nat.choose_zero_right]
    simp only [rowPrefix,Nat.succ_eq_add_one]
    omega

  have quadratic_slope (n : ℕ) (hn : 4 ≤ n) (a b d : ℤ) (ha : 0 < a) (hb : 0 < b)
      (h : ((n:ℤ)*b)^2 ≤ a^2 + 4*n*a*b) :
      (∑ p ∈ (entries n).filter (fun p => d < a*(p.1:ℤ)+b*p.2), p.1.choose p.2) ≠
        ∑ p ∈ (entries n).filter (fun p => a*(p.1:ℤ)+b*p.2 ≤ d), p.1.choose p.2 := by
    obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    intro eq
    obtain ⟨k,large,hkt,low,high,gap⟩ := balanced_locus t (by omega) a b d ha hb eq.symm
    let N : ℤ := (t:ℤ)+1
    let X : ℤ := (t:ℤ)-k
    let Y : ℤ := (k:ℤ)+1
    let Z := X-Y
    let S : ℤ := ∑ j ∈ range k, (t.choose j : ℤ)
    have hab : a < Z*b := by dsimp [Z,X,Y]; linarith only [low,high]
    have hZ : 0 < Z := by
      by_contra! hz
      have := mul_nonpos_of_nonpos_of_nonneg hz hb.le
      omega
    have hY : 0 < Y := by dsimp [Y]; omega
    have hN : 0 < N := by dsimp [N]; omega
    have hu := penultimate_bound (show k+1<t by dsimp [Z,X,Y] at hZ; omega) a b d hb.le high
    rw [prefix_step] at hu
    rw [prefix_row_identity _ _ (by omega)] at gap
    have less : (t.choose (k+1):ℤ) < S := by
      dsimp [S]
      exact_mod_cast (show t.choose (k+1) < ∑ j ∈ range k, t.choose j by omega)
    have bnd : Z*S ≤ Y*t.choose k := by
      have sub : Z=(t:ℤ)-2*k-1 := by dsimp [Z,X,Y]; ring
      rw [sub]
      exact ratio_prefix t k hkt.le
    have adj : Y*t.choose (k+1) = X*t.choose k := by
      have hs := congrArg (fun z : ℕ => (z:ℤ)) (Nat.choose_succ_right_eq t k)
      push_cast [Nat.cast_sub hkt.le] at hs
      dsimp [Y,X]; linarith
    have lt₁ := (mul_lt_mul_of_pos_left less hZ).trans_le bnd
    have lt₂ := mul_lt_mul_of_pos_left lt₁ hY
    have lt₃ : Z*X*(t.choose k:ℤ) < Y^2*(t.choose k:ℤ) := by
      calc
        _ = Z*(X*t.choose k) := by ring
        _ = Z*(Y*t.choose (k+1)) := by rw [adj]
        _ = Y*(Z*t.choose (k+1)) := by ring
        _ < Y*(Y*t.choose k) := lt₂
        _ = _ := by ring
    have coeff : Z*X < Y^2 := by
      by_contra! hz
      have := mul_le_mul_of_nonneg_right hz (show 0 ≤ (t.choose k:ℤ) by positivity)
      omega
    have square : Z^2+4*N*Z < N^2 := by dsimp [Z,X,Y,N] at coeff ⊢; nlinarith only [coeff]
    have sqgap := mul_pos (sub_pos.mpr hab) (show 0 < Z*b+a by positivity)
    have lingap := mul_pos (show 0 < 4*N*b by positivity) (sub_pos.mpr hab)
    have bound := mul_lt_mul_of_pos_right square (sq_pos_of_pos hb)
    change (N*b)^2 ≤ a^2+4*N*a*b at h
    nlinarith only [sqgap,lingap,bound,h]

  intro evenCase oddCase n hn u v d hu hv _
  apply normalize n (by omega) _ u v d hu hv
  intro a b t ha hb hau hbu ht
  by_cases zero : b=0
  · subst b
    unfold Unequal
    have hf : (entries n).filter (fun p => t < a*(p.1:ℤ)+0*p.2) =
        (entries n).filter (fun p => (-a)*(p.1:ℤ)+(-0:ℤ)*p.2 ≤ -t-1) := by
      apply filter_congr
      intro p _
      simp only [neg_mul,zero_mul,add_zero,neg_zero]
      omega
    rw [hf]
    exact (row_dominant n (by omega) a 0 t ha.le le_rfl (by simp; omega)).symm
  have bp : 0 < b := by omega
  by_cases col : a ≤ b
  · exact column_dominant n (by omega) a b t ha col
  by_cases rowBound : ((n:ℤ)*b)^2 ≤ a^2+4*n*a*b
  · exact quadratic_slope n (by omega) a b t ha bp rowBound
  rcases (show n%2=0 ∨ n%2=1 by omega) with hp | hp
  · exact evenCase n hn hp a b t ha bp hau hbu ht (by omega) (by omega)
  · exact oddCase n hn hp a b t ha bp hau hbu ht (by omega) (by omega)

end OMA.R_mse_4815847_R1_H2_R1
