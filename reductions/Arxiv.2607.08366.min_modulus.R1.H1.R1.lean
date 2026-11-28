import OMAReductions.R_Arxiv_2607_08366_min_modulus_R1

/-!
# Odd moduli for the unique multiset-sum problem

A valid size-n set has exactly one multiset of size n with the same sum as the
set. Translating an element to zero, the other n−1 elements have pairwise
distinct subset sums, as proved by @kyka776 in project note 56429. If n ≥ 4
and the modulus is odd, doubling each nonzero element, reflecting those values
about half the total sum, and including the midpoint yield another 2n−1
distinct residues. This proves N ≥ 2^(n−1)+2n−1.

Finite certificates settle the remaining cases through n = 5. A table entry
encodes a multiplicity vector. The kernel checks its sum, its weighted sum
modulo N, and that at least one multiplicity differs from one. Translation and
unit scaling put both zero and one in the set whenever the translated set
contains a unit. The complementary search uses only nonunit residues.

For composite moduli, dividing a residue class by its common spacing produces
a valid set in the quotient. Induction discards every case where that smaller
bound already suffices. The transport argument generalizes @rorcores's
divide-by-two proof in the parent reduction. Project notes from @bryding and
@maz777 also discuss the small configurations.
-/
namespace OMA.R_Arxiv_2607_08366_min_modulus_R1_H1_R1
open Finset Arxiv.«2607.08366» OMA.R_Arxiv_2607_08366_min_modulus_R1

private lemma rescale {d M : ℕ} (hd : 0 < d) (hM : 0 < M) (C : Finset (ZMod (d * M))) (p : ℕ)
    (hp : ∀ a ∈ C, a.val % d = p) (hC : IsValidMod C) :
    ∃ C' : Finset (ZMod M), #C' = #C ∧ IsValidMod C' := by
  classical
  have : NeZero (d * M) := ⟨Nat.ne_of_gt (Nat.mul_pos hd hM)⟩
  have : NeZero M := ⟨by omega⟩
  have hinj : Set.InjOn (fun a : ZMod (d * M) => ((a.val / d : ℕ) : ZMod M)) (C : Set (ZMod (d * M))) := by
    intro a ha b hb hab
    have ha : a ∈ C := ha
    have hb : b ∈ C := hb
    have hab : ((a.val / d : ℕ) : ZMod M) = ((b.val / d : ℕ) : ZMod M) := hab
    have ha2 : a.val / d < M := by exact (Nat.div_lt_iff_lt_mul hd).mpr (by simpa [Nat.mul_comm] using ZMod.val_lt a)
    have hb2 : b.val / d < M := by exact (Nat.div_lt_iff_lt_mul hd).mpr (by simpa [Nat.mul_comm] using ZMod.val_lt b)
    have hq : a.val / d = b.val / d := by
      have h := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hab
      rwa [Nat.mod_eq_of_lt ha2, Nat.mod_eq_of_lt hb2] at h
    apply ZMod.val_injective
    have h1 := hp a ha
    have h2 := hp b hb
    have x := Nat.mod_add_div a.val d
    have y := Nat.mod_add_div b.val d
    rw [h1,hq,← h2,y] at x
    exact x.symm
  refine ⟨C.image fun a => ((a.val / d : ℕ) : ZMod M), Finset.card_image_of_injOn hinj, ?_⟩
  intro m' hsize hsum c' hc'
  obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.1 hc'
  rw [Finset.sum_image hinj, Finset.card_image_of_injOn hinj] at hsize
  rw [Finset.sum_image hinj, Finset.sum_image hinj] at hsum
  -- the hypothesis on sums, as a congruence between natural numbers modulo `M`
  have hS : (∑ a ∈ C, m' ((a.val / d : ℕ) : ZMod M) * (a.val / d)) ≡ (∑ a ∈ C, a.val / d) [MOD M] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    exact hsum
  -- every element of `C` is `d * (a.val / d) + p`
  have hval : ∀ a ∈ C, a = ((d * (a.val / d) + p : ℕ) : ZMod (d * M)) := by
    intro a ha
    have h1 := hp a ha
    have h2 : d * (a.val / d) + p = a.val := by rw [Nat.add_comm, ← h1, Nat.mod_add_div]
    rw [h2, ZMod.natCast_zmod_val]
  have key := hC (fun a => m' ((a.val / d : ℕ) : ZMod M)) hsize ?_ a₀ ha₀
  · exact key
  · have hL : ∑ a ∈ C, ((m' ((a.val / d : ℕ) : ZMod M) : ℕ) : ZMod (d * M)) * a
        = ((∑ a ∈ C, m' ((a.val / d : ℕ) : ZMod M) * (d * (a.val / d) + p) : ℕ) : ZMod (d * M)) := by
      rw [Nat.cast_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Nat.cast_mul]
      congr 1
      exact hval a ha
    have hR : ∑ a ∈ C, a = ((∑ a ∈ C, (d * (a.val / d) + p) : ℕ) : ZMod (d * M)) := by
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl fun a ha => hval a ha
    rw [hL, hR, ZMod.natCast_eq_natCast_iff]
    have e1 : ∑ a ∈ C, m' ((a.val / d : ℕ) : ZMod M) * (d * (a.val / d) + p)
        = d * (∑ a ∈ C, m' ((a.val / d : ℕ) : ZMod M) * (a.val / d)) + p * #C := by
      rw [← hsize, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    have e2 : ∑ a ∈ C, (d * (a.val / d) + p) = d * (∑ a ∈ C, a.val / d) + p * #C := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul, mul_comm p]
    rw [e1, e2]
    exact (Nat.ModEq.mul_left' d hS).add_right _


/-- In a smallest counterexample, no single residue class can account for enough
of the set to recover the bound by descent to the quotient modulus. -/
private def spread (N : Nat) (A : Finset (ZMod N)) : Prop :=
  ∀ d M, 1 < d → N = d * M → ∀ r < d,
    N+1 < 2^(#A - #(A.filter fun a => a.val % d = r)) * (M+1)

private theorem shrink {N : Nat} (odd : N%2=1) (A : Finset (ZMod N)) (valid : IsValidMod A)
    (smaller : ∀ M < N, M%2=1 → ∀ C : Finset (ZMod M), IsValidMod C → 2^#C ≤ M+1)
    (fail : ¬spread N A) : 2^#A ≤ N+1 := by
  classical
  simp only [spread,not_forall,not_lt] at fail
  obtain ⟨d,M,hd,hN,r,_,hr⟩ := fail
  subst N
  have hM : 0 < M := by by_contra! h; simp [show M=0 by omega] at odd
  have oddM : M%2=1 := by
    rcases Nat.mod_two_eq_zero_or_one M with h|h
    · simp [Nat.mul_mod,h] at odd
    · exact h
  let C := A.filter fun a => a.val % d = r
  have sub : C ⊆ A := Finset.filter_subset _ _
  obtain ⟨D,eqn,hD⟩ := rescale (by omega : 0 < d) hM C r
    (fun a ha => (Finset.mem_filter.mp ha).2) (isValidMod_subset sub valid)
  have ltM : M < d*M := by nlinarith
  have bound := smaller M ltM oddM D hD
  rw [eqn] at bound
  have le := Finset.card_le_card sub
  have add : #A-#C+#C=#A := Nat.sub_add_cancel le
  calc
    2^#A = 2^(#A-#C) * 2^#C := by rw [← pow_add,add]
    _ ≤ 2^(#A-#C)*(M+1) := Nat.mul_le_mul_left _ bound
    _ ≤ d*M+1 := hr

private structure Table where
  depth : Nat
  onlyNonunits : Bool
  positions : Nat
  codes : Nat
  words : Nat

private def binomials : Nat := 0x22caa06b0d00fdc001b30001e000011cfe305cc700e46001960001d0000117fe804ffb00ccc0017a0001c0000113b5a0448e00b6d0015f0001b00001100f403a6600a28001450001a000010cf8a0316a008fc0012c00019000010a60802982007e80011400018000010837102297006eb000fd0001700001066de01c9300604000e7000160000104f7d0176100532000d2000150000103c90012ed00474000be000140000102d6c00f24003c9000ab00013000010217800bf4003300009900012000010182c0094c002a8000880001100001011100071c0023000078000100000100bbb00555001c7000690000f00001007d2003e90016c0005b0000e0000100507002cb0011e0004e0000d0000100318001ef000dc000420000c00001001ce0014a000a5000370000b00001000fc000d2000780002d0000a000010007e0007e000540002400009000010003800046000380001c0000800001000150002300023000150000700001000060000f000140000f000060000100001000050000a0000a0000500001000000000100004000060000400001000000000000001000030000300001000000000000000000010000200001000000000000000000000000100001000000000000000000000000000001

private def rank (tab : Table) : Nat → List Nat → Nat
  | j+1,x::xs =>
    let p := (tab.positions >>> (5*x)) % 32
    ((binomials >>> (20*(p*6+j+1))) % 1048576) + rank tab j xs
  | _,_ => 0

private def allowed (tab : Table) (N x : Nat) := !tab.onlyNonunits || !decide (x.Coprime N)

private def witness (tab : Table) (xs : List Nat) : Nat :=
  let i := rank tab tab.depth xs
  let tag := (tab.words >>> (8*i)) % 256
  (tab.codes >>> (15*tag)) % 32768

private def weight (w : Nat) (s : List Nat) (i : Nat) := (w >>> (3*s.idxOf i)) % 8

private theorem sum_word (f : Nat → Nat) (s : List Nat) (unique : s.Nodup) :
    (s.map f).sum = ∑ a∈s.toFinset,f a := by
  induction s with
  | nil => simp
  | cons a l ih =>
    obtain ⟨hne,hu⟩ := List.nodup_cons.mp unique
    simp [hne,ih hu]

private def obstruction (N : Nat) (s : List Nat) (w : Nat) : Bool :=
  let m := weight w s
  decide (s.Nodup ∧ (s.map m).sum = s.length ∧
    (s.map (fun x => m x*x)).sum % N = s.sum % N ∧ ∃ i ∈ s, m i ≠ 1)

private theorem obstruction_sound {N : Nat} [NeZero N] (s : List Nat) (w : Nat)
    (hs : ∀ i ∈ s, i < N) (bad : obstruction N s w = true)
    (valid : IsValidMod (s.toFinset.image (fun i : Nat => (i : ZMod N)))) : False := by
  let t := s.toFinset
  let m := weight w s
  obtain ⟨hu,hc,hv,i,hm,hdiff⟩ := of_decide_eq_true bad
  have hcount : (∑ a∈t,m a) = #t :=
    (sum_word m s hu).symm.trans (hc.trans (List.toFinset_card_of_nodup hu).symm)
  have hi : i ∈ t := List.mem_toFinset.mpr hm
  have plain : s.sum = ∑ a∈t,a := by simpa [t] using sum_word id s hu
  have hsum : (∑ a∈t,m a*a)%N = (∑ a∈t,a)%N := by
    rw [← sum_word (fun x => m x*x) s hu,← plain]
    exact hv
  have val (a : Nat) (ha : a ∈ t) : (a : ZMod N).val = a :=
    (ZMod.val_natCast N a).trans (Nat.mod_eq_of_lt (hs a (List.mem_toFinset.mp ha)))
  have inj : Set.InjOn (fun a : Nat => (a : ZMod N)) (t : Set Nat) := by
    intro a ha b hb eqn
    have e := congrArg ZMod.val eqn
    simpa only [val a ha,val b hb] using e
  have hlen : ∑ a ∈ t.image (fun a : Nat => (a : ZMod N)), m a.val = #(t.image (fun a : Nat => (a : ZMod N))) := by
    rw [Finset.sum_image inj,Finset.card_image_of_injOn inj]
    exact (Finset.sum_congr rfl (fun a ha => congrArg m (val a ha))).trans hcount
  have hw : ∑ a ∈ t.image (fun a : Nat => (a : ZMod N)), (m a.val : ZMod N)*a =
      ∑ a ∈ t.image (fun a : Nat => (a : ZMod N)), a := by
    rw [Finset.sum_image inj,Finset.sum_image inj]
    have eql : ((∑ a ∈ t, m a*a : Nat) : ZMod N) = ((∑ a ∈ t, a : Nat) : ZMod N) :=
      (ZMod.natCast_eq_natCast_iff' ..).mpr hsum
    push_cast at eql
    exact (Finset.sum_congr rfl (fun a ha => by rw [val a ha])).trans eql
  have res := valid (fun a => m a.val) hlen hw (i : ZMod N) (Finset.mem_image_of_mem _ hi)
  exact hdiff (by simpa only [val i hi] using res)

private def walk (N : Nat) (table : Table) : Nat → Nat → List Nat → Bool
  | 0,_,s => obstruction N s (witness table s)
  | k+1,start,s => (List.range (N-start)).all fun i =>
      !allowed table N (start+i) || walk N table k (start+i+1) ((start+i)::s)

private theorem certify_children (N : Nat) (tab : Table) (k start : Nat) (s : List Nat)
    (h : ∀ i < N-start, allowed tab N (start+i) = true →
      walk N tab k (start+i+1) ((start+i)::s) = true) :
    walk N tab (k+1) start s = true := by
  apply List.all_eq_true.mpr
  intro i hi
  cases hr : allowed tab N (start+i) with
  | false => simp [hr]
  | true => simpa [hr] using h i (List.mem_range.mp hi) hr

private theorem walk_sound {N : Nat} [NeZero N] (tab : Table) (k start : Nat) (xs : List Nat)
    (good : walk N tab k start xs = true) (hxs : ∀ x ∈ xs, x<N) (s : Finset Nat)
    (size : #s=k) (hs : ∀ x∈s, start ≤ x ∧ x<N ∧ allowed tab N x = true)
    (valid : IsValidMod ((s ∪ xs.toFinset).image fun i : Nat => (i : ZMod N))) : False := by
  induction k generalizing s start xs with
  | zero =>
    have : s = ∅ := Finset.card_eq_zero.mp size
    subst s
    exact obstruction_sound xs _ hxs good (by simpa using valid)
  | succ k ih =>
    have ne := Finset.card_pos.mp (show 0 < #s by omega)
    let a := s.min' ne
    have ha : a ∈ s := s.min'_mem ne
    obtain ⟨lo,hi,yes⟩ := hs a ha
    have child := List.all_eq_true.mp good (a-start) (List.mem_range.mpr (by omega))
    rw [show start+(a-start)=a by omega] at child
    simp only [yes,Bool.not_true,Bool.false_or] at child
    apply ih (a+1) (a::xs) child (by simpa [hi] using hxs) (s.erase a) (by rw [Finset.card_erase_of_mem ha,size]; omega)
    · intro b hb
      obtain ⟨diff,bs⟩ := Finset.mem_erase.mp hb
      have least := s.min'_le b bs
      change a ≤ b at least
      exact ⟨by omega,(hs b bs).2⟩
    · have eqn : s.erase a ∪ (a::xs).toFinset = s ∪ xs.toFinset := by
        ext b
        by_cases he : b=a <;> simp [he,ha]
      rwa [eqn]

private lemma affine_valid {N : Nat} (u c : ZMod N)
    (cancel : Function.Injective (fun x : ZMod N => u*x))
    (A : Finset (ZMod N)) (valid : IsValidMod A) :
    IsValidMod (A.image fun a => u*a+c) := by
  classical
  have inj : Set.InjOn (fun a : ZMod N => u*a+c) (A : Set (ZMod N)) :=
    fun _ _ _ _ e => cancel (add_right_cancel e)
  intro m size weighted t ht
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp ht
  rw [Finset.sum_image inj,Finset.card_image_of_injOn inj] at size
  rw [Finset.sum_image inj,Finset.sum_image inj] at weighted
  apply valid (fun b => m (u*b+c)) size _ a ha
  apply cancel
  have eqn : u*(∑ b ∈ A, (m (u*b+c) : ZMod N)*b) +
      (∑ b ∈ A, (m (u*b+c) : ZMod N))*c = u*(∑ b ∈ A, b) + (#A : ZMod N)*c := by
    calc
      _ = ∑ b ∈ A, (m (u*b+c) : ZMod N)*(u*b+c) := by
        rw [Finset.mul_sum,Finset.sum_mul,← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun b _ => by ring)
      _ = ∑ b ∈ A, (u*b+c) := weighted
      _ = _ := by rw [Finset.sum_add_distrib,Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
  rw [← Nat.cast_sum,size] at eqn
  exact add_right_cancel eqn

private lemma anchor {N : Nat} (A : Finset (ZMod N)) (ne : A.Nonempty)
    (valid : IsValidMod A) : ∃ B : Finset (ZMod N), #B=#A ∧ 0∈B ∧ IsValidMod B := by
  obtain ⟨a,ha⟩ := ne
  let F := fun x : ZMod N => (1:ZMod N)*x + (-a)
  have inj : Function.Injective F := by intro x y h; simpa [F] using h
  exact ⟨A.image F,Finset.card_image_of_injective _ inj,
    Finset.mem_image.mpr ⟨a,ha,by simp [F]⟩,
    affine_valid 1 (-a) (fun _ _ h => by simpa using h) A valid⟩

private lemma anchor_pair {N : Nat} [Fact N.Prime] (A : Finset (ZMod N))
    (many : 1 < #A) (valid : IsValidMod A) :
    ∃ B : Finset (ZMod N), #B=#A ∧ 0∈B ∧ 1∈B ∧ IsValidMod B := by
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp many
  let u := (b-a)⁻¹
  have d : b-a≠0 := sub_ne_zero.mpr hab.symm
  have cancel : Function.Injective (fun x : ZMod N => u*x) :=
    fun _ _ h => mul_left_cancel₀ (inv_ne_zero d) h
  let F := fun x => u*x + (-(u*a))
  have inj : Function.Injective F := fun _ _ h => cancel (add_right_cancel h)
  refine ⟨A.image F,Finset.card_image_of_injective _ inj,Finset.mem_image.mpr ⟨a,ha,by simp [F]⟩,
    Finset.mem_image.mpr ⟨b,hb,?_⟩,affine_valid u (-(u*a)) cancel A valid⟩
  dsimp [F,u]
  rw [← sub_eq_add_neg, ← mul_sub,inv_mul_cancel₀ d]

private theorem cover {N : Nat} [NeZero N] (tab : Table) (k start : Nat) (xs : List Nat)
    (good : walk N tab k start xs = true) (A : Finset (ZMod N)) (valid : IsValidMod A)
    (inside : ∀ i ∈ xs, i<N ∧ (i : ZMod N)∈A)
    (outside : ∀ a ∈ A, a.val ∉ xs → start ≤ a.val ∧ allowed tab N a.val = true) :
    #A < k + xs.toFinset.card := by
  classical
  by_contra! large
  let F := A.image ZMod.val
  have count : #F = #A := Finset.card_image_of_injective _ (ZMod.val_injective N)
  have sub : xs.toFinset ⊆ F := by
    intro i hi
    obtain ⟨small,red⟩ := inside i (List.mem_toFinset.mp hi)
    exact Finset.mem_image.mpr ⟨(i : ZMod N),red,(ZMod.val_natCast N i).trans (Nat.mod_eq_of_lt small)⟩
  have total := Finset.card_sdiff_add_card_eq_card sub
  obtain ⟨s,hs,size⟩ := Finset.exists_subset_card_eq (show k ≤ #(F \ xs.toFinset) by omega)
  apply walk_sound tab k start xs good (fun i hi => (inside i hi).1) s size
  · intro x hx
    obtain ⟨mem,abs⟩ := Finset.mem_sdiff.mp (hs hx)
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp mem
    have h := outside a ha (fun h => abs (List.mem_toFinset.mpr h))
    exact ⟨h.1,ZMod.val_lt _,h.2⟩
  · apply isValidMod_subset _ valid
    intro y hy
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
    rcases Finset.mem_union.mp hi with h|h
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp (hs h)).1
      simpa using ha
    · exact (inside i (List.mem_toFinset.mp h)).2

private theorem smallCase {N : Nat} [NeZero N] (big : 1<N) (k : Nat) (u t : Table)
    (uf : u.onlyNonunits=false) (tf : t.onlyNonunits=true)
    (pu : walk N u k 2 [1,0]=true) (pt : walk N t (k+1) 1 [0]=true)
    (A : Finset (ZMod N)) (zero : 0∈A) (valid : IsValidMod A) : #A < k+2 := by
  classical
  by_cases has : ∃ a∈A, IsUnit a
  · obtain ⟨a,ha,v,rfl⟩ := has
    let f := fun x : ZMod N => (↑(v⁻¹) : ZMod N)*x+0
    have cancel : Function.Injective (fun x : ZMod N => (↑(v⁻¹) : ZMod N)*x) := by
      intro a b eqn
      simpa only [← mul_assoc,Units.mul_inv, one_mul] using congrArg (fun x : ZMod N => (v : ZMod N)*x) eqn
    have inj : Function.Injective f := fun _ _ eqn => cancel (add_right_cancel eqn)
    let B := A.image f
    have b0 : 0 ∈ B := Finset.mem_image.mpr ⟨0,zero,by simp [f]⟩
    have b1 : 1 ∈ B := Finset.mem_image.mpr ⟨(v : ZMod N),ha,by simp [f]⟩
    have res := cover u k 2 [1,0] pu B (affine_valid _ 0 cancel A valid)
      (by intro i hi; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; rcases hi with rfl|rfl <;> simp [big,b1,b0,show 0<N by omega])
      (by
        intro a _ hh
        have h0 : a.val ≠ 0 := fun e => hh (by rw [e]; simp)
        have h1 : a.val ≠ 1 := fun e => hh (by rw [e]; simp)
        exact ⟨by omega,by simp [allowed,uf]⟩)
    simpa [B,Finset.card_image_of_injective _ inj] using res
  · have res := cover t (k+1) 1 [0] pt A valid
      (by intro i hi; simp only [List.mem_singleton] at hi; subst i; simp [zero,show 0<N by omega])
      (by
        intro a ha h
        have notUnit : ¬IsUnit a := fun hu => has ⟨a,ha,hu⟩
        have neg : ¬a.val.Coprime N := by
          intro cp
          apply notUnit
          simpa using (ZMod.isUnit_iff_coprime a.val N).mpr cp
        have nz : a.val ≠ 0 := fun e => h (by rw [e]; simp)
        exact ⟨by omega,by simp [allowed,tf,neg]⟩)
    simpa [Nat.add_assoc] using res
-- Anchored subset-sum injection from @kyka776, project note 56429.
private lemma anchored_subset_sums {N : ℕ} {A : Finset (ZMod N)} {z : ZMod N}
    (hz : z ∈ A) (hA : IsValidMod A) :
    Set.InjOn (fun B : Finset (ZMod N) => ∑ a ∈ B, (a - z))
      (↑(A.erase z).powerset : Set (Finset (ZMod N))) := by
  classical
  intro B hB C hC heq
  wlog hcard : #B ≤ #C generalizing B C
  · exact (this hC hB heq.symm (by omega)).symm
  have hB : B ⊆ A.erase z := mem_powerset.mp hB
  have hC : C ⊆ A.erase z := mem_powerset.mp hC
  change ∑ a ∈ B, (a - z) = ∑ a ∈ C, (a - z) at heq
  let q (T : Finset (ZMod N)) (a : ZMod N) : ℕ := if a ∈ T then 1 else 0
  let e (a : ZMod N) : ℕ := if a = z then #C - #B else 0
  let m (a : ZMod N) : ℕ := (1 - q C a) + q B a + e a
  have hp (a) : m a + q C a = 1 + q B a + e a := by
    by_cases ha : a ∈ C <;> simp [m, q, ha, add_left_comm, add_comm]
  have hq (T : Finset (ZMod N)) (hTA : T ⊆ A) : ∑ a ∈ A, q T a = #T := by
    calc
      _ = ∑ a ∈ T, q T a := (sum_subset hTA (fun a _ h => by simp [q, h])).symm
      _ = #T := by simp [q]
  have he : ∑ a ∈ A, e a = #C - #B := by
    rw [sum_eq_single_of_mem z hz (fun a _ h => by simp [e, h])]
    simp [e]
  have hn : ∑ a ∈ A, m a = #A := by
    have h := sum_congr (s₁ := A) rfl (fun a _ => hp a)
    simp only [sum_add_distrib, sum_const, smul_eq_mul, mul_one] at h
    rw [hq C (hC.trans (erase_subset _ _)), hq B (hB.trans (erase_subset _ _)), he] at h
    omega
  have hweight (T : Finset (ZMod N)) (hTA : T ⊆ A) :
      ∑ a ∈ A, (q T a : ZMod N) * (a - z) = ∑ a ∈ T, (a - z) := by
    calc
      _ = ∑ a ∈ T, (q T a : ZMod N) * (a - z) :=
        (sum_subset hTA (fun a _ h => by simp [q, h])).symm
      _ = _ := sum_congr rfl (fun a h => by simp [q, h])
  have hew : ∑ a ∈ A, (e a : ZMod N) * (a - z) = 0 := by
    apply sum_eq_zero
    intro a _
    by_cases h : a = z <;> simp [e, h]
  have hshift : ∑ a ∈ A, (m a : ZMod N) * (a - z) = ∑ a ∈ A, (a - z) := by
    have h := sum_congr (s₁ := A) rfl
      (fun a _ => congrArg (fun k : ℕ => (k : ZMod N) * (a - z)) (hp a))
    push_cast at h
    simp only [add_mul, sum_add_distrib, one_mul] at h
    rw [hweight C (hC.trans (erase_subset _ _)), hweight B (hB.trans (erase_subset _ _)),
      hew, add_zero, heq] at h
    exact add_right_cancel h
  have hw : ∑ a ∈ A, (m a : ZMod N) * a = ∑ a ∈ A, a := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, ← Nat.cast_sum, hn, sum_const,
      nsmul_eq_mul] at hshift
    exact sub_left_inj.mp hshift
  have hall := hA m hn hw
  ext a
  by_cases hb : a ∈ B <;> by_cases hc : a ∈ C
  · simp [hb, hc]
  · have hA' := mem_of_mem_erase (hB hb)
    have hne := ne_of_mem_erase (hB hb)
    have hh := hall a hA'
    simp [m, q, e, hb, hc, hne] at hh
  · have hA' := mem_of_mem_erase (hC hc)
    have hne := ne_of_mem_erase (hC hc)
    have hh := hall a hA'
    simp [m, q, e, hb, hc, hne] at hh
  · simp [hb, hc]


private theorem missed_multiple {N : Nat} (A : Finset (ZMod N)) (zA : 0∈A)
    (valid : IsValidMod A) (x : ZMod N) (hx : x∈A.erase 0)
    (S : Finset (ZMod N)) (hs : S⊆A.erase 0) (k : Nat) (hk : 2≤k) (hr : k≤#S+1) :
    (k : ZMod N)*x ≠ ∑ a∈S,a := by
  classical
  intro eqn
  let D := A.erase 0 \ S
  have hD : D ⊆ A := (Finset.sdiff_subset).trans (Finset.erase_subset _ _)
  let w (a : ZMod N) := (if a∈D then 1 else 0 : Nat) +
    (if a=x then k else 0) + (if a=0 then #S+1-k else 0)
  have xA := Finset.mem_of_mem_erase hx
  have hnum : (∑ a∈A, (if a∈D then 1 else 0 : Nat)) = #D := by
    rw [← Finset.sum_filter]
    have e : A.filter (·∈D) = D := by ext a; simp [and_iff_right_of_imp (fun hd => hD hd)]
    simp [e]
  have hweight : (∑ a∈A, (if a∈D then a else 0)) = ∑ a∈D,a := by
    rw [← Finset.sum_filter]
    have e : A.filter (·∈D) = D := by ext a; simp [and_iff_right_of_imp (fun hd => hD hd)]
    rw [e]
  have size : ∑ a∈A,w a = #A := by
    simp only [w,Finset.sum_add_distrib]
    rw [hnum]
    simp [Finset.sum_ite_eq',xA,zA]
    have c := Finset.card_sdiff_add_card_eq_card hs
    change #D+#S=#(A.erase 0) at c
    have ne := Finset.card_pos.mpr (show A.Nonempty from ⟨0,zA⟩)
    rw [Finset.card_erase_of_mem zA] at c
    omega
  have weighted : (∑ a∈A, (w a : ZMod N)*a) = ∑ a∈A,a := by
    simp only [w,Nat.cast_add,add_mul,Finset.sum_add_distrib,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
      ite_mul,zero_mul,one_mul]
    rw [hweight]
    simp [Finset.sum_ite_eq',xA,zA]
    rw [eqn,Finset.sum_sdiff hs,← Finset.sum_erase_add _ _ zA]
    simp
  have unique := valid w size weighted x xA
  have xne := Finset.ne_of_mem_erase hx
  simp [w,xne] at unique
  split at unique <;> omega

private theorem odd_lower {N : Nat} (odd : N%2=1) (A : Finset (ZMod N)) (zA : 0∈A)
    (large : 4 ≤ #A) (valid : IsValidMod A) : 2^(#A-1)+2*(#A-1)+1 ≤ N := by
  classical
  letI : NeZero N := ⟨by omega⟩
  let E := A.erase 0
  let total := ∑ a∈E,a
  let sums := E.powerset.image (fun U => ∑ a∈U,a)
  have size : #E = #A-1 := Finset.card_erase_of_mem zA
  have nonempty : E.Nonempty := Finset.card_pos.mp (by omega)
  have inj : Set.InjOn (fun U : Finset (ZMod N) => ∑ a∈U,a) (E.powerset : Set (Finset (ZMod N))) := by
    simpa only [sub_zero] using anchored_subset_sums zA valid
  have unit : IsUnit (2 : ZMod N) := by
    simpa using (ZMod.isUnit_iff_coprime 2 N).mpr (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr odd))
  have dbl : Function.Injective (fun x : ZMod N => 2*x) := unit.mul_right_injective
  have comp (S : Finset (ZMod N)) (sub : S⊆E) : (∑ a∈E \ S,a) + (∑ a∈S,a) = total :=
    Finset.sum_sdiff sub
  have nohalf (S : Finset (ZMod N)) (sub : S⊆E) : 2*(∑ a∈S,a) ≠ total := by
    intro eqn
    have h := comp S sub
    have eqS : S = E \ S := inj (Finset.mem_powerset.mpr sub) (Finset.mem_powerset.mpr Finset.sdiff_subset)
      (by change (∑ a∈S,a) = ∑ a∈E \ S,a; linear_combination eqn - h)
    obtain ⟨x,hx⟩ := nonempty
    have hmem : x∈S ↔ x∉S := by conv_lhs => rw [eqS]; simp [hx]
    tauto
  have notFour (x : ZMod N) (hx : x∈E) : 2*(2*x) ≠ total := by
    intro eqn
    have card := Finset.card_erase_of_mem hx
    have bad := missed_multiple A zA valid x hx (E.erase x) (Finset.erase_subset _ _) 3 (by decide) (by omega)
    apply bad
    have es : (∑ a∈E.erase x,a) + x = total := Finset.sum_erase_add _ _ hx
    push_cast
    linear_combination eqn - es
  let D := E.image fun x => 2*x
  let K := D.image fun x => total-x
  have apart : Disjoint sums D := by
    apply Finset.disjoint_left.mpr
    intro b hb hd
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨x,hx,eqn⟩ := Finset.mem_image.mp hd
    by_cases e : S.Nonempty
    · exact missed_multiple A zA valid x hx S (Finset.mem_powerset.mp hS) 2 (by decide)
        (by have := Finset.card_pos.mpr e; omega) eqn
    · have := Finset.not_nonempty_iff_eq_empty.mp e
      subst S
      have eq0 : 2*x = 2*(0:ZMod N) := by simpa using eqn
      exact (Finset.ne_of_mem_erase hx) (dbl eq0)
  have apartK : Disjoint sums K := by
    apply Finset.disjoint_left.mpr
    intro b hb hk
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨x,hx,eqn⟩ := Finset.mem_image.mp hk
    have eqc : x=∑ a∈E \ S,a := by linear_combination -(comp S (Finset.mem_powerset.mp hS)) - eqn
    exact Finset.disjoint_left.mp apart (Finset.mem_image.mpr ⟨E \ S,Finset.mem_powerset.mpr Finset.sdiff_subset,eqc.symm⟩) hx
  have DK : Disjoint D K := by
    apply Finset.disjoint_left.mpr
    intro p hp hK
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q,hq,eqn⟩ := Finset.mem_image.mp hK
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
    by_cases eqxy : x=y
    · subst y
      apply notFour x hx
      linear_combination -eqn
    · have h := nohalf {x,y} (by intro b hb; simp only [Finset.mem_insert,Finset.mem_singleton] at hb; rcases hb with rfl|rfl <;> assumption)
      apply h
      simp [eqxy]
      linear_combination -eqn
  obtain ⟨m,hm⟩ := Finite.surjective_of_injective dbl total
  change 2*m = total at hm
  have mS : m∉sums := by
    intro h; obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp h
    exact nohalf S (Finset.mem_powerset.mp hS) hm
  have mD : m∉D := by
    intro h; obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp h
    exact notFour x hx hm
  have mK : m∉K := by
    intro h; obtain ⟨x,hx,eqn⟩ := Finset.mem_image.mp h
    have : m=x := by linear_combination hm + eqn
    exact mD (this ▸ hx)
  have cs : #sums = 2^#E := (Finset.card_image_of_injOn inj).trans (Finset.card_powerset E)
  have cd : #D = #E := Finset.card_image_of_injective _ dbl
  have ck : #K = #D := Finset.card_image_of_injective _ (fun _ _ h => sub_right_inj.mp h)
  have uni := (insert m (sums ∪ D ∪ K)).card_le_univ
  have mid : m ∉ sums ∪ D ∪ K := by simp [mS,mD,mK]
  rw [Finset.card_insert_of_notMem mid,Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨apartK,DK⟩),
    Finset.card_union_of_disjoint apart,cs,ck,cd,size,ZMod.card] at uni
  omega
private def tab3u : Table := ⟨1,false,0x0,0xc00030000c044005001020044021000a,0x6⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked3u : walk 3 tab3u 1 2 [1, 0] = true := by decide +kernel
private def tab3n : Table := ⟨2,true,0x0,0xc00030000c044005001020044021000a,0x0⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked3n : walk 3 tab3n 2 1 [0] = true := by decide +kernel
private def tab5u : Table := ⟨1,false,0x208000,0xc00030000c044005001020044021000a,0x80607⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked5u : walk 5 tab5u 1 2 [1, 0] = true := by decide +kernel
private def tab5n : Table := ⟨2,true,0x0,0xc00030000c044005001020044021000a,0x0⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked5n : walk 5 tab5n 2 1 [0] = true := by decide +kernel
private def tab25u : Table := ⟨3,false,0x16ad2728c1ee6b16a4a0e62906208000,0x50006800980050030800d00830026001406020184006820180830026001430020c04030800d20030806020c009800584006002020244010808a00a40110006010021204080841101220084221028208140228109005204080110006080029004400a0810902040500884110122008510114024084110884102824014102804510120424014880202040088003192016402580c820b0430480c904320164121820b0096190096016082190486082c16012182406490190432016490190430486402c105804b44905120944125044825104940a20928128124224908905124844828825124844828825024a,0x16171717171717171717171717171717171717171718181818181818181818181818181818181818182c2c281b1c2c2c1d29212c2c2c2c242c252c192c2c2c281b1c1d292c202c2c242c252c191e2c2c2c2c281b1c2c212c242c252c192c1e2c2c2c2c1d281b1c202c252c192c2c1e2c2c2c1d292c241b1c2c192c2c2c1e2c2c1d29242c2520191c2c2c2c1e2c1d242c252c192c281b1c2c1e1d29252c192c202c2c281b1c1a1a191a1a1a1a1a1a1a1a1926262626202626261e2c2c2c2c212c2c2c1e2c2c2c2c202c2c1e2c2c2c212c2c1e2c2c2c202c1e2c2c212c1e2c2c201e2c211e2c1e1e15161b1c3f3f3f3f1d2a202f3f3f3f3f242d251e16171717171717171717171717171717171717181818181818181818181818181818181818323738285b1b1c622149244325402d3919333333331d2a1b1c202f2533332d191e4537381d2a28241b1c40415819391e45371d2a244325201b1c192d341e451d244325402128191b1c351e1d2a25404155192f282d1b1c1a1a1a1a191a1a1a1a1a1a2727192727202727271e1937343521582d391e3435384e202d391e453738212d391e453738202f1e453721391e452d201e2d211e301e1e2815161b1c323f1d3f213f2f3f3f242d252e1e151637381b1c1d4e29204249244325392e1e1617171717171717171717171717171717181818181818181818181818181818184532371d2829241b1c2f402d392e1932461d38242825201b1c2d39191e331d2429253321332f1b192e1e1d4325384041202819391b1c1a1a1a1a1a1a191a1a1a1a2941373819202d342e1e26261926212626261e194d373420392e1e45343521392e1e35582d202e1e452d212e1e2d39201e30211e2e1e1e283415161b1c1d322a203f2f242d252e3f1e35151637381b1c2a2149244325392e401e151628371d321b1c2043252d392e411e1617171717171717171717171717171818181818181818181818181818451d242a252821402d1b1c5a191d3225373840202d2f2e191c1a1a1a1a1a1a1a1a191a1a2a3333333320192e281e27272727192727271e454e192d202e2f1e19582d212e351e452d3420381e2d3521371e302e201e2e211e311e1e283f3415161b1c3f2132242d252e3f3f1e342815161d381b1c204325392e5a401e4515161d3738241b1c2d2f2e40411e15161d28242925201b1c2e414d1e161717171717171717171717171818181818181818181818181a1a1a1a1a1a1a1a1a1a19452932412d202e28191e2932582d212e192f1e262626261926261e332d192133331e19392e20371e302e21301e2e34201e31211e451e1e283f3f3415161b1c202d252e3f3f3f1e452835151637241b1c392e5a5c401e35461516242a25201b1c2f40411e45151628253721392e1b1c4c1e1516252a282d202e412f1b1c1617171717171717171717181818181818181818182a402d392137382819272727272027191e2d392e2119371e302e1920301e193621361e3131201e45211e341e1e283f3f1d3415161b1c2e3f2f3f321e45281d35151625201b1c4d4e321e341d24151629212e5a1b1c321e1d4315162939203840411b1c1a15161a1a1a1a1a1a1a1a151629392e203738321e1617171717171717171818181818181818262626212626192e363620191e313119311e1961201e45211e321e1e283f1d3f242d15161b1c3f2f3f1e451d243425151637381b1c401e1d34252d1516203738401b1c1a1a1a15161a1a1a1a1a1a452d151628204137381e2d151640212846371e151630302030281e161717171717171818181818184561214e19454c191e19211e451e1e281d242d252e2115161b1c2f1e1d2825392e29151637381b1c1a1a1a1a1a15161a1a1a1a2d352e2815164041371e302e2915163030301e2e2915162028361e2915162131311e15162620261e161717171718181818452119191e1e1d2d252e3f2a203415161b1c1a1a1a1a1a1a1a15161a1a302e282a30201516301e2e342a28211516361e312a31311516311e2a40411516281e27271516271e451516631e1516201e1617171818191a1a1a1a1a1a1a1a1a15162e283636292034351516313128292131311516455b292820411516342940212815162941552015162626211516454d151645151615161614141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414283f3f3f213f3f3f1e332833292033331e455b282140411e45294020341e294121351e2626201e45211e451e1e283f322a203f3f1e45282a2155401e322a2820411e2a3321281e2727201e45211e351e1e283f3f21323f1e45282920401e452921411e2932201e26211e331e1e283f2a203f1e452821401e2a40201e27211e451e1e283f213f1e4528201e29211e261e1e282a201e2a211e271e1e28211e291e1e281e1e1e⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked25u_0 : walk 25 tab25u 2 3 [2, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked25u_1 : walk 25 tab25u 2 4 [3, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked25u_2 : walk 25 tab25u 2 5 [4, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked25u_3 : walk 25 tab25u 2 6 [5, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked25u_4 : walk 25 tab25u 2 7 [6, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked25u_5 : walk 25 tab25u 2 8 [7, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked25u_6 : walk 25 tab25u 2 9 [8, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked25u_7 : walk 25 tab25u 2 10 [9, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked25u_8 : walk 25 tab25u 2 11 [10, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked25u_9 : walk 25 tab25u 2 12 [11, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked25u_10 : walk 25 tab25u 2 13 [12, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked25u_11 : walk 25 tab25u 2 14 [13, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked25u_12 : walk 25 tab25u 2 15 [14, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked25u_13 : walk 25 tab25u 2 16 [15, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked25u_14 : walk 25 tab25u 2 17 [16, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked25u_15 : walk 25 tab25u 2 18 [17, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked25u_16 : walk 25 tab25u 2 19 [18, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked25u_17 : walk 25 tab25u 2 20 [19, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked25u_18 : walk 25 tab25u 2 21 [20, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked25u_19 : walk 25 tab25u 2 22 [21, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked25u_20 : walk 25 tab25u 2 23 [22, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked25u_21 : walk 25 tab25u 2 24 [23, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked25u_22 : walk 25 tab25u 2 25 [24, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked25u : walk 25 tab25u 3 2 [1, 0] = true := by
  apply certify_children
  intro i bound eligible
  interval_cases i
  · exact checked25u_0
  · exact checked25u_1
  · exact checked25u_2
  · exact checked25u_3
  · exact checked25u_4
  · exact checked25u_5
  · exact checked25u_6
  · exact checked25u_7
  · exact checked25u_8
  · exact checked25u_9
  · exact checked25u_10
  · exact checked25u_11
  · exact checked25u_12
  · exact checked25u_13
  · exact checked25u_14
  · exact checked25u_15
  · exact checked25u_16
  · exact checked25u_17
  · exact checked25u_18
  · exact checked25u_19
  · exact checked25u_20
  · exact checked25u_21
  · exact checked25u_22
private def tab25n : Table := ⟨4,true,0x30000010000004000000000000,0x50006800980050030800d00830026001406020184006820180830026001430020c04030800d20030806020c009800584006002020244010808a00a40110006010021204080841101220084221028208140228109005204080110006080029004400a0810902040500884110122008510114024084110884102824014102804510120424014880202040088003192016402580c820b0430480c904320164121820b0096190096016082190486082c16012182406490190432016490190430486402c105804b44905120944125044825104940a20928128124224908905124844828825124844828825024a,0x16⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked25n : walk 25 tab25n 4 1 [0] = true := by decide +kernel
private def tab27u : Table := ⟨3,false,0x62f6ad2728c1ee6b16a4a0e62906208000,0x50006800980050030800d00830026001406020184006820180830026001430020c04030800d20030806020c009800584006002020244010808a00a40110006010021204080841101220084221028208140228109005204080110006080029004400a0810902040500884110122008510114024084110884102824014102804510120424014880202040088003192016402580c820b0430480c904320164121820b0096190096016082190486082c16012182406490190432016490190430486402c105804b44905120944125044825104940a20928128124224908905124844828825124844828825024a,0x1617171717171717171717171717171717171717171717181818181818181818181818181818181818181818182c2c281b1c2c2c2c1d29212c2c2c2c2c242c252c192c2c2c281b1c2c1d292c202c2c2c242c252c191e2c2c2c2c281b1c292c212c2c242c252c192c1e2c2c2c2c2c1d1b1c2c20242c252c192c2c1e2c2c2c2c1d29281b1c2c252c192c2c2c1e2c2c2c1d292c24281b1c192c2c2c2c1e2c2c1d29242c2521191b1c2c2c2c1e2c1d242c252c19202c281b1c2c1e1d29252c192c212c2c2c281b1c1a1a191a1a1a1a1a1a1a1a1a192626262621262626261e2c2c2c2c2c202c2c2c1e2c2c2c2c212c2c2c1e2c2c2c2c202c2c1e2c2c2c212c2c1e2c2c2c202c1e2c2c212c1e2c2c201e2c211e2c1e1e15161b1c3f3f3f3f3f1d2a202f3f3f3f3f3f242d251e161717171717171717171717171717171717171717181818181818181818181818181818181818181832373828651b1c2a69214e49244325402d391933333333281d1b1c332024332533332d191e4537385c1d28701b1c432540414d19391e4537381d2a4924431b1c4167192d341e45371d2a24432521411b19582d351e451d24432540412019681b1c391e1d2a25404167196834282d1b1c1a1a1a1a191a1a1a1a1a1a1a272719272721272727271e1937343565202f2d391e3435384e21422d391e4537386e202d391e453738212d391e453738202f1e453721391e452d201e2d211e301e1e2815161b1c323f3f1d3f213f2f3f3f3f242d252e1e151637381b1c4d1d692920766d49244325392e1e16171717171717171717171717171717171717181818181818181818181818181818181818453237381d70291b1c43254b402d392e19326e371d6f2824431b1c40412d39191e33331d3324332521331b1c2d192e1e451d2429254b40206c58191c2e1e1d43253840412167192d391b1c1a1a1a1a1a1a191a1a1a1a1a294137381921582d352e1e2626192626202626261e194d3734212d2f2e1e4534353820392e1e356e3721392e1e45582d202e1e452d212e1e2d39201e30211e2e1e1e283415161b1c3f1d3f2a203f2f3f242d252e3f1e35151637381b1c4d2a216349244325392e401e15162837381d1b1c6320242f252d392e411e16171717171717171717171717171717171818181818181818181818181818181845461d37242825214c1b1c392e4c19451d242a254b2820412d1b1c191e1d432537384021282d39191b1c1a1a1a1a1a1a1a1a191a1a1a2a404137382119392e281e2727272719202727271e454e193721392e351e19554d2d202e2f1e45582d212e4e1e342d3920381e2d3921371e302e201e2e211e311e1e283f3415161b1c3f3f213f3f242d252e3f3f1e34281516371d1b1c2920244325392e5a401e451516701d386e1b1c43252d392e40411e1516641d373824431b1c2d392e41691e16171717171717171717171717171718181818181818181818181818181d4325293738212d392e5a1b191a1a1a1a1a1a1a1a1a1a191a452940413721392e195c1e29416a422d20195a6f1e26262626192626261e454d193920386e1e192d392137341e2d392e20351e302e21301e2e36201e31211e451e1e283f3f3415161b1c2a20242d252e3f3f3f1e452835151637381b1c4325392e5a69401e356f15165b3724431b1c392e4e40411e45151628242a25212d1b1c40414d1e1516244325373820392e1b1c651e16171717171717171717171717181818181818181818181818452a6a402d212e287067192a40412d39203867191e27272727212719271e452d392e1937381e2d3919215f371e192e3020301e2e3621361e3131201e34211e451e1e283f3f3f1d15161b1c2d252e2f323f3f1e4528341d151624291b1c2e4e325c401e34351d1516432521391b1c2f40411e451d151625292d202e4c1b1c4c1e1d15164b282d212e40322f1b1c15161a1a1a1a1a1a1a1a1a1a161717171717171717171718181818181818181818292d392e2132373819262626262026191e302e302119301e2e361920361e193121311e3261201e33211e451e1e283f3f1d3f3415161b1c3f3f2f3f3f1e45281d34241516212e1b1c4d4e401e451d24431516392038661b1c411e1d432515163921373840411b1c1a1a15161a1a1a1a1a1a1a1a451516392e21413738661e1516392e41202837381e16171717171717171718181818181818182e36362136361931313120191e456119611e1968201e45211e451e1e283f1d3f242d2515161b1c3f2f3f1e451d24432535151637381b1c401e1d43252d391516663738401b1c1a1a1a1a15161a1a1a1a1a1a452d39151621404137381e2d39151640205f5f371e30151630213028301e151636362036361e161717171717171818181818184562214d194567191e19211e451e1e281d242d252e2a2015161b1c2f1e1d2825392e2a21151637381b1c1a1a1a1a1a1a15161a1a1a1a2d342e285f15164041371e302e2a3015163030301e2e2a3615162836361e2a3115162031281e2715162127271e15166220461e161717171718181818452119191e1e1d2d252e3f3f213f3415161b1c1a1a1a1a1a1a1a1a15161a1a302e28302921301516301e2e36342836201516361e31312931211516311e452940411516611e29416915166f1e26261516261e451516661e1516201e1617171818191a1a1a1a1a1a1a1a1a1a15162e2836362a2136343515163131282a312031311516455c2a282140411516452a3540206c15162a4041216f1516272727201516454e21151645661516451516151616141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414283f3f3f2a203f3f3f1e3328332a213333331e455c28702040411e452a6b2141341e2a404120281e272721271e354e201e45211e451e1e283f323f213f3f3f1e452870292069401e325b282140411e33293320331e294121651e2626201e34211e451e1e283f3f2a203f3f1e45282a2155401e452a2820411e2a3221281e2727201e33211e451e1e283f3f213f3f1e45282920401e452921411e2941201e26211e451e1e283f2a203f1e452821401e2a40201e27211e451e1e283f213f1e4528201e29211e261e1e282a201e2a211e271e1e28211e291e1e281e1e1e⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked27u_0 : walk 27 tab27u 2 3 [2, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked27u_1 : walk 27 tab27u 2 4 [3, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked27u_2 : walk 27 tab27u 2 5 [4, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked27u_3 : walk 27 tab27u 2 6 [5, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked27u_4 : walk 27 tab27u 2 7 [6, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked27u_5 : walk 27 tab27u 2 8 [7, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked27u_6 : walk 27 tab27u 2 9 [8, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked27u_7 : walk 27 tab27u 2 10 [9, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked27u_8 : walk 27 tab27u 2 11 [10, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked27u_9 : walk 27 tab27u 2 12 [11, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked27u_10 : walk 27 tab27u 2 13 [12, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked27u_11 : walk 27 tab27u 2 14 [13, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked27u_12 : walk 27 tab27u 2 15 [14, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked27u_13 : walk 27 tab27u 2 16 [15, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked27u_14 : walk 27 tab27u 2 17 [16, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked27u_15 : walk 27 tab27u 2 18 [17, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked27u_16 : walk 27 tab27u 2 19 [18, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked27u_17 : walk 27 tab27u 2 20 [19, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked27u_18 : walk 27 tab27u 2 21 [20, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked27u_19 : walk 27 tab27u 2 22 [21, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked27u_20 : walk 27 tab27u 2 23 [22, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked27u_21 : walk 27 tab27u 2 24 [23, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked27u_22 : walk 27 tab27u 2 25 [24, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked27u_23 : walk 27 tab27u 2 26 [25, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked27u_24 : walk 27 tab27u 2 27 [26, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked27u : walk 27 tab27u 3 2 [1, 0] = true := by
  apply certify_children
  intro i bound eligible
  interval_cases i
  · exact checked27u_0
  · exact checked27u_1
  · exact checked27u_2
  · exact checked27u_3
  · exact checked27u_4
  · exact checked27u_5
  · exact checked27u_6
  · exact checked27u_7
  · exact checked27u_8
  · exact checked27u_9
  · exact checked27u_10
  · exact checked27u_11
  · exact checked27u_12
  · exact checked27u_13
  · exact checked27u_14
  · exact checked27u_15
  · exact checked27u_16
  · exact checked27u_17
  · exact checked27u_18
  · exact checked27u_19
  · exact checked27u_20
  · exact checked27u_21
  · exact checked27u_22
  · exact checked27u_23
  · exact checked27u_24
private def tab27n : Table := ⟨4,true,0x7000c00140020003000400040000000,0x50006800980050030800d00830026001406020184006820180830026001430020c04030800d20030806020c009800584006002020244010808a00a40110006010021204080841101220084221028208140228109005204080110006080029004400a0810902040500884110122008510114024084110884102824014102804510120424014880202040088003192016402580c820b0430480c904320164121820b0096190096016082190486082c16012182406490190432016490190430486402c105804b44905120944125044825104940a20928128124224908905124844828825124844828825024a,0x1717171716171716171617171717171f1a1618161e181b181816181a181a1919191e1e151515151a1e16161b1c17171616171716181819141e1a15151615151616211414141e⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked27n : walk 27 tab27n 4 1 [0] = true := by decide +kernel
private def tab29u : Table := ⟨3,false,0x1ace2f6ad2728c1ee6b16a4a0e62906208000,0x50006800980050030800d00830026001406020184006820180830026001430020c04030800d20030806020c009800584006002020244010808a00a40110006010021204080841101220084221028208140228109005204080110006080029004400a0810902040500884110122008510114024084110884102824014102804510120424014880202040088003192016402580c820b0430480c904320164121820b0096190096016082190486082c16012182406490190432016490190430486402c105804b44905120944125044825104940a20928128124224908905124844828825124844828825024a,0x161717171717171717171717171717171717171717171717171818181818181818181818181818181818181818181818182c2c281b1c2c2c2c2c1d29212c2c2c2c2c2c242c252c192c2c2c281b1c2c2c1d292c202c2c2c2c242c252c191e2c2c2c2c281b1c1d292c212c2c2c242c252c192c1e2c2c2c2c2c281b1c2c2c202c242c252c192c2c1e2c2c2c2c2c1d281b1c21242c252c192c2c2c1e2c2c2c2c1d292c281b1c252c192c2c2c2c1e2c2c2c1d292c242c211b192c2c2c2c2c1e2c2c1d29242c252c19281b1c2c2c2c1e2c1d242c252c19212c2c281b1c2c1e1d29252c192c2c202c2c2c281b1c1a1a191a1a1a1a1a1a1a1a1a1a19262626262620262626261e2c2c2c2c2c212c2c2c2c1e2c2c2c2c2c202c2c2c1e2c2c2c2c212c2c2c1e2c2c2c2c202c2c1e2c2c2c212c2c1e2c2c2c202c1e2c2c212c1e2c2c201e2c211e2c1e1e15161b1c3f3f3f3f3f3f1d2a202f3f3f3f3f3f3f242d251e16171717171717171717171717171717171717171717171818181818181818181818181818181818181818181832373828651b1c1d2a4d21624249244325402d39193333333328331b1c3333202f24332533332d191e453738465b1d2a1b1c2124432540415819391e4537385c1d2a28491b1c2540415b192d341e4537381d2a492428211b1c4c194c2d351e45371d2a24432540202f191c342d391e451d2443254041211928341b1c391e1d2a2540416719202f35282d1b1c1a1a1a1a191a1a1a1a1a1a1a1a27271927272720272727271e19373435652176582d391e3435384e65202f2d391e4537386a214e2d391e45373877202d391e453738212d391e453738202f1e453721391e452d201e2d211e301e1e2815161b1c323f3f3f1d3f213f2f3f3f3f3f242d252e1e151637381b1c4d4e1d6a292062755549244325392e1e161717171717171717171717171717171717171717181818181818181818181818181818181818181845323738281d621b1c21242f254b402d392e19327137381d2829491b1c254b40412d39191e3333331d33292433211b1c33332d192e1e45461d382443252820411b1c19392e1e451d2429254b4021282f191b1c2e1e1d4325384041552019282d341b1c1a1a1a1a1a1a191a1a1a1a1a1a29413738196820342d392e1e262619262621262626261e194d373435202d392e1e45343538212d2f2e1e3578373820392e1e454c3721392e1e45582d202e1e452d212e1e2d39201e30211e2e1e1e283415161b1c3f321d3f2a203f2f3f3f242d252e3f1e35151637381b1c1d4e2a217b4249244325392e401e1516283738321b1c2a4d20492443252d392e411e161717171717171717171717171717171717171818181818181818181818181818181818184562321d38282443211b1c402d392e4d1945321d372443254b20401b1c392e191e321d242a254b6b2141582d1b195a1e1d33253333333320282d192e1b1c1a1a1a1a1a1a1a1a191a1a1a1a2a4041373867192d2f2e281e272727271921272727271e454e19373820342e5a1e19684d3721352e421e4571342d202e2f1e34352d212e5a1e452d3920381e2d3921371e302e201e2e211e311e1e283f3415161b1c1d3f32213f3f2f242d252e3f3f1e3428151637381b1c32292049244325392e5a401e45151646371d771b1c212443252d392e40411e151662281d3832291b1c254b2d392e416c1e161717171717171717171717171717171718181818181818181818181818181818451d243225382821402d2f1b1c67191d432529373840202d392e5a191c1a1a1a1a1a1a1a1a1a1a191a1a322940413738203919285b1e293333333321192e2f331e2626262619202626261e454d192d212e462f1e19582d392034351e452d392135381e2d342e20371e302e21301e2e36201e31211e451e1e283f3f3415161b1c3f2a2032242d252e3f3f3f1e45283515161d381b1c21244325392e5a42401e356215161d37382a1b1c252d2f2e5a40411e4515161d5b372443211b1c392e4041661e15161d49242a2532202d1b1c415b711e16171717171717171717171717171718181818181818181818181818181a1a1a1a1a1a1a1a1a1a1a1a19452a6b32412d202e282f191e2a4032422d212e5a19281e2727272727201927271e324e2d39193738421e332d192e2033331e19392e214d371e302e3020301e2e3621351e3131201e45211e451e1e283f3f3f3415161b1c21242d252e3f3f3f3f1e45283435151637381b1c25392e5a656b401e3435281516492429211b1c2e2f4e40411e454615162443253820391b1c40414d1e4515164325293721392e401b1c661e1516254b29282d202e416c751b1c161717171717171717171717171818181818181818181818184529402d39213738282f1929412d392e203738191e26262626212619261e2d392e5a195f371e302e192130301e19363620361e313121311e4561201e45211e351e1e283f3f3f1d3415161b1c252e3f2f3f323f1e4528701d3515162a211b1c4d4e7532401e45341d491516252d202e1b1c2f32411e351d2415162a2d212e4c461b1c4c1e1d431516282d39203840412f1b1c1a15161a1a1a1a1a1a1a1a1a1a15162a2d392e203738322f1e161717171717171717171718181818181818181818272727272127272719302e30302030191e2e36362119361e31311920311e196121611e4532201e32211e331e1e283f3f1d3f3f2415161b1c3f3f2f3f3f1e45281d492435151620381b1c4d4e401e451d2435251516213738461b1c411e1d35252815162e20373840411b1c1a1a1a15161a1a1a1a1a1a1a1a454215162e2820413738761e4515162e4021287037381e15162e4155205f28371e16171717171717171718181818181818183131312131311945616120191e454c194c1e1968201e45211e451e1e283f1d3f242d252a15161b1c3f2f3f1e451d244325342a151637381b1c401e1d43252d352a1516783738401b1c1a1a1a1a1a15161a1a1a1a1a1a352d392a151620404137381e2d392a151621415f5f371e302a151630202830301e2a151636213636281e151627272027271e16171717171717181818181818457a2163194563191e19211e451e1e281d242d252e3f213415161b1c2f1e1d2825392e4c2920151637381b1c1a1a1a1a1a1a1a15161a1a1a1a2d392e28295f15164041371e302e30292815163030301e2e36293615163636361e31293115163128311e294115162061611e2615162126261e15164e20461e161717171718181818452119191e1e1d2d252e3f3f2a203f3415161b1c1a1a1a1a1a1a1a1a1a15161a1a302e28302a3020301516301e2e3636283521361516361e31312a3128201516311e352a6140211516421e2a4041551516281e2727271516271e454e1516461e4515164e1e1516201e1617171818191a1a1a1a1a1a1a1a1a1a1a15162e2836363629203634351516313128312921313131151645616128342040411516455b29352141461516342940412028151629416c21631516262626201516454d21151645661516451516151616141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414283f3f3f3f213f3f3f3f1e3328333329203333331e45652829215540411e455b29282041341e4529402128351e29413420461e262621261e454d201e45211e451e1e283f323f2a203f3f3f1e45285b2a216346401e325c28632040411e332a332133331e2a404120281e272721271e4534201e35211e451e1e283f3f3f213f3f3f1e452863292065401e455b282140411e45294020461e2941216f1e2626201e45211e341e1e283f3f2a203f321e45282a2155321e452a2820321e2a4021281e2727201e45211e321e1e283f3f213f3f1e45282920401e452921411e2941201e26211e451e1e283f2a203f1e452821401e2a40201e27211e451e1e283f213f1e4528201e29211e261e1e282a201e2a211e271e1e28211e291e1e281e1e1e⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29u_0 : walk 29 tab29u 2 3 [2, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29u_1 : walk 29 tab29u 2 4 [3, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29u_2 : walk 29 tab29u 2 5 [4, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29u_3 : walk 29 tab29u 2 6 [5, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29u_4 : walk 29 tab29u 2 7 [6, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29u_5 : walk 29 tab29u 2 8 [7, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29u_6 : walk 29 tab29u 2 9 [8, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29u_7 : walk 29 tab29u 2 10 [9, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29u_8 : walk 29 tab29u 2 11 [10, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29u_9 : walk 29 tab29u 2 12 [11, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29u_10 : walk 29 tab29u 2 13 [12, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29u_11 : walk 29 tab29u 2 14 [13, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29u_12 : walk 29 tab29u 2 15 [14, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29u_13 : walk 29 tab29u 2 16 [15, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29u_14 : walk 29 tab29u 2 17 [16, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29u_15 : walk 29 tab29u 2 18 [17, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29u_16 : walk 29 tab29u 2 19 [18, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29u_17 : walk 29 tab29u 2 20 [19, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29u_18 : walk 29 tab29u 2 21 [20, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29u_19 : walk 29 tab29u 2 22 [21, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29u_20 : walk 29 tab29u 2 23 [22, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29u_21 : walk 29 tab29u 2 24 [23, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29u_22 : walk 29 tab29u 2 25 [24, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29u_23 : walk 29 tab29u 2 26 [25, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29u_24 : walk 29 tab29u 2 27 [26, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29u_25 : walk 29 tab29u 2 28 [27, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29u_26 : walk 29 tab29u 2 29 [28, 1, 0] = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29u : walk 29 tab29u 3 2 [1, 0] = true := by
  apply certify_children
  intro i bound eligible
  interval_cases i
  · exact checked29u_0
  · exact checked29u_1
  · exact checked29u_2
  · exact checked29u_3
  · exact checked29u_4
  · exact checked29u_5
  · exact checked29u_6
  · exact checked29u_7
  · exact checked29u_8
  · exact checked29u_9
  · exact checked29u_10
  · exact checked29u_11
  · exact checked29u_12
  · exact checked29u_13
  · exact checked29u_14
  · exact checked29u_15
  · exact checked29u_16
  · exact checked29u_17
  · exact checked29u_18
  · exact checked29u_19
  · exact checked29u_20
  · exact checked29u_21
  · exact checked29u_22
  · exact checked29u_23
  · exact checked29u_24
  · exact checked29u_25
  · exact checked29u_26
private def tab29n : Table := ⟨4,true,0x0,0x50006800980050030800d00830026001406020184006820180830026001430020c04030800d20030806020c009800584006002020244010808a00a40110006010021204080841101220084221028208140228109005204080110006080029004400a0810902040500884110122008510114024084110884102824014102804510120424014880202040088003192016402580c820b0430480c904320164121820b0096190096016082190486082c16012182406490190432016490190430486402c105804b44905120944125044825104940a20928128124224908905124844828825124844828825024a,0x0⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem checked29n : walk 29 tab29n 4 1 [0] = true := by decide +kernel
private theorem five_bound (N : Nat) (odd : N%2=1) (A : Finset (ZMod N))
    (nsmall : #A ≤ 5) (valid : IsValidMod A) : 2^#A ≤ N+1 := by
  by_contra! fail
  have cap := Nat.pow_le_pow_right (by decide : 0<2) nsmall
  have small : N ≤ 29 := by norm_num at cap; omega
  have ne : A.Nonempty := Finset.card_pos.mp (by
    by_contra! z
    have := Nat.eq_zero_of_le_zero z
    simp [this] at fail)
  obtain ⟨B,hB,zB,vB⟩ := anchor A ne valid
  have cases : N=1 ∨ N=3 ∨ N=5 ∨ N=25 ∨ N=27 ∨ N=29 := by
    by_cases n3 : #A≤3
    · have p := Nat.pow_le_pow_right (by decide : 0<2) n3
      norm_num at p
      omega
    · have lb := odd_lower odd B zB (by omega) vB
      rw [hB] at lb
      have which : #A=4 ∨ #A=5 := by omega
      rcases which with h|h <;> rw [h] at lb fail <;> norm_num at lb fail <;> omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · have boundB : #B ≤ 1 := by simpa [ZMod.card] using B.card_le_univ
    rw [hB] at boundB
    have hpow := Nat.pow_le_pow_right (by decide : 0<2) boundB
    norm_num at hpow
    omega
  · have lim := smallCase (by decide : 1<3) 1 tab3u tab3n rfl rfl checked3u checked3n B zB vB
    rw [hB] at lim
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show #A ≤ 2 by omega)
    norm_num at hpow
    omega
  · have lim := smallCase (by decide : 1<5) 1 tab5u tab5n rfl rfl checked5u checked5n B zB vB
    rw [hB] at lim
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show #A ≤ 2 by omega)
    norm_num at hpow
    omega
  · have lim := smallCase (by decide : 1<25) 3 tab25u tab25n rfl rfl checked25u checked25n B zB vB
    rw [hB] at lim
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show #A ≤ 4 by omega)
    norm_num at hpow
    omega
  · have lim := smallCase (by decide : 1<27) 3 tab27u tab27n rfl rfl checked27u checked27n B zB vB
    rw [hB] at lim
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show #A ≤ 4 by omega)
    norm_num at hpow
    omega
  · have lim := smallCase (by decide : 1<29) 3 tab29u tab29n rfl rfl checked29u checked29n B zB vB
    rw [hB] at lim
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show #A ≤ 4 by omega)
    norm_num at hpow
    omega


/-- The remaining prime moduli. Translation and scaling put 0 and 1 in the set. -/
def H1 : Prop := ∀ (N : Nat), N.Prime → ∀ A : Finset (ZMod N),
    6 ≤ #A → 0 ∈ A → 1 ∈ A → 2^(#A-1)+2*(#A-1)+1≤N → IsValidMod A → 2^#A ≤ N+1

/-- The remaining odd composite moduli. Each concentration in a residue class
must be too small for the bound at the quotient modulus to settle this set. -/
def H2 : Prop := ∀ (N : Nat), N%2=1 → ¬N.Prime → ∀ A : Finset (ZMod N),
    6 ≤ #A → 0 ∈ A → 2^(#A-1)+2*(#A-1)+1≤N → IsValidMod A →
    (∀ d M, 1 < d → N=d*M → ∀ r < d,
      N+1 < 2^(#A - #(A.filter fun a => a.val % d = r))*(M+1)) →
    2^#A ≤ N+1

theorem main : H1 → H2 → OMA.R_Arxiv_2607_08366_min_modulus_R1.H1 := by
  intro prime composite n N odd A size valid
  subst n
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases small : #A ≤ 5
    · exact five_bound N odd A small valid
    have large : 6 ≤ #A := by omega
    by_cases hp : N.Prime
    · letI : Fact N.Prime := ⟨hp⟩
      obtain ⟨B,cB,zB,oB,vB⟩ := anchor_pair A (by omega) valid
      rw [← cB]
      exact prime N hp B (by omega) zB oB (odd_lower odd B zB (by omega) vB) vB
    · obtain ⟨B,cB,zB,vB⟩ := anchor A (Finset.card_pos.mp (by omega)) valid
      rw [← cB]
      by_cases balanced : spread N B
      · exact composite N odd hp B (by omega) zB (odd_lower odd B zB (by omega) vB) vB balanced
      · exact shrink odd B vB ih balanced

end OMA.R_Arxiv_2607_08366_min_modulus_R1_H1_R1
