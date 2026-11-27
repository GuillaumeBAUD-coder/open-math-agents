import OMAReductions.R_OeisA261680_conjecture_R1

/-! # Four binary palindromes by reading the two ends together

The three length patterns are those in Rajasekaran, Shallit and Smith,
*Sums of Palindromes: an Approach via Nested-Word Automata*, Theorem 1 (arXiv:1706.10206).
The finite carry certificate and its verification below use length-indexed sums.
-/
-- Credit: @steveDOTdigital
namespace OMA.BinaryPalindromes
open Finset

private def wrap (k b x : ℕ) := b*2^(k+1)+2*x+b

-- Pad allows zero bits at both ends of an interior word.
private inductive Pad : ℕ → ℕ → Prop
  | nil : Pad 0 0
  | single (b : ℕ) (hb : b<2) : Pad 1 b
  | grow {k x : ℕ} (b : ℕ) (hb : b<2) (h : Pad k x) : Pad (k+2) (wrap k b x)

private lemma spell {k x : ℕ} (h : Pad k x) :
    ∃ l : List ℕ, l.length=k ∧ l.reverse=l ∧ (∀ i∈l, i<2) ∧ Nat.ofDigits 2 l=x := by
  induction h with
  | nil => exact ⟨[],by simp⟩
  | single b hb => exact ⟨[b],by simp; omega⟩
  | @grow k x b hb h ih =>
    obtain ⟨l,len,rev,bits,num⟩ := ih
    refine ⟨b :: (l ++ [b]),by simp [len],by simp [rev],?_,?_⟩
    · intro i hi
      simp at hi
      rcases hi with e|hil|e <;> first | exact bits i hil | omega
    · rw [Nat.ofDigits_cons,Nat.ofDigits_append,Nat.ofDigits_singleton,len,num]
      simp [wrap,pow_succ]; ring

private lemma canonical {k x : ℕ} (h : Pad k x) : OeisA261680.isBinaryPalindrome (wrap k 1 x) = true := by
  obtain ⟨l,len,rev,bits,num⟩ := spell h
  let w := 1 :: (l ++ [1])
  have val : Nat.ofDigits 2 w = wrap k 1 x := by
    dsimp [w]; rw [Nat.ofDigits_cons,Nat.ofDigits_append,Nat.ofDigits_singleton,len,num]
    simp [wrap,pow_succ]; ring
  have bin (i : ℕ) (hi : i ∈ w) : i<2 := by
    simp [w] at hi
    rcases hi with e|hl|e <;> first | exact bits i hl | omega
  have last (hn : w≠[]) : w.getLast hn ≠ 0 := by simp [w]
  rw [OeisA261680.isBinaryPalindrome,←val,Nat.digits_ofDigits 2 (by decide) w bin last]
  simp [w,rev]

private def vals : ℕ → List ℕ
  | 0 => [0]
  | 1 => [0,1]
  | k+2 => (vals k).flatMap (fun x => [wrap k 0 x,wrap k 1 x])

private lemma vals_ok (k x : ℕ) (h : x ∈ vals k) : Pad k x := by
  induction k using Nat.twoStepInduction generalizing x with
  | zero => simp [vals] at h; subst x; exact Pad.nil
  | one =>
    simp [vals] at h
    rcases h with rfl|rfl <;> exact Pad.single _ (by decide)
  | more k ih _ =>
    obtain ⟨y,hy,which⟩ := List.mem_flatMap.mp h
    simp at which
    rcases which with rfl|rfl <;> exact Pad.grow _ (by decide) (ih _ hy)

-- Modes 0 and 1 allow three palindromes; mode 2 allows one palindrome.
private def delta (m : ℕ) := if m=1 then 2 else 3
private def aBit (j : ℕ) := j%2
private def bBit (j : ℕ) := (j/2)%2
private def cBit (j : ℕ) := (j/4)%2
private def low (j : ℕ) := aBit j+bBit j+cBit j
private def high (m j : ℕ) := aBit j*2^(delta m)+2*bBit j+cBit j
private def atBit (s m h c : ℕ) := s.testBit ((m*12+h)*3+c)
-- Each mask records triples (mode, upper carry, lower carry).
-- For an inner mask and the two new input bits, transitions selects an outer mask.
private def masks : Array ℕ := #[
  39006747274603858241781749, 1315915754758609837420969962, 2477126783376281128457469916,
  5106578220024005601647394809, 54042992591241212, 108086052828217337,
  90071856182198270, 126100588776652793, 108085980887515130,
  90071585599258618, 54042928166731772, 108085847743528952,
  72057117296558072, 18014193424793597, 36028455569063930,
  144114642615009272, 126100517909692412, 18014055985840123,
  18014330863747070, 72057052872048632, 36028391144554490,
  126100247326752760, 36028386849587195, 54042717713334265,
  54042923871764477, 18014262144270335, 18014266439237630,
  72057048577081337]
private def transitions : Array ℕ := #[
  21, 8, 4, 5, 16, 11, 17, 6, 12, 21, 13, 14, 7, 8, 4, 9,
  12, 11, 13, 14, 7, 8, 4, 9, 16, 11, 13, 6, 21, 8, 4, 5,
  16, 11, 13, 6, 10, 11, 4, 6, 19, 11, 13, 20, 21, 11, 4, 9,
  12, 11, 13, 14, 23, 8, 13, 17, 4, 11, 13, 18, 15, 11, 13, 8,
  15, 11, 13, 8, 4, 8, 13, 13, 4, 11, 13, 18, 19, 11, 13, 20,
  10, 11, 13, 26, 11, 11, 4, 8, 24, 11, 13, 25, 12, 8, 13, 14,
  27, 11, 13, 22, 24, 11, 13, 25, 10, 11, 13, 26, 27, 11, 13, 22]
private def bases : Array ℕ := #[
  11, 9, 0, 1, 2, 3, 17, 6, 11, 8, 10, 11,
  12, 9, 13, 20, 24, 11, 17, 6, 13, 14, 4, 6]
private def mask (i : ℕ) := masks[i]?.getD 0
private def next (i hi lo : ℕ) := transitions[i*4+hi*2+lo]?.getD 28
private def base (k v : ℕ) := bases[(if k=3 then 0 else 8)+v]?.getD 28

-- The upper outgoing carry h, the lower incoming carry c, and a guessed triple of bits j
-- determine the two carries after peeling off the next pair of digits.
private def legal (s m h c hi lo j : ℕ) : Bool :=
  let H := 2*h+hi-high m j
  let C := (low j+c)/2
  decide ((m=2 → bBit j = 0 ∧ cBit j = 0) ∧ 2*h+hi=H+high m j ∧ low j+c=2*C+lo ∧ H<12 ∧ C<3) && atBit s m H C

private def witness (k v m h c : ℕ) : Bool :=
  (vals (k+delta m)).any fun x => (vals (k+1)).any fun y => (vals k).any fun z =>
    decide ((m=2 → y=0 ∧ z=0) ∧ x+y+z+c=h*2^k+v)

private def Rep (k v m h c : ℕ) : Prop :=
  ∃ x y z : ℕ, Pad (k+delta m) x ∧ Pad (k+1) y ∧ Pad k z ∧
    (m=2 → y=0 ∧ z=0) ∧ x+y+z+c=h*2^k+v

private def Good (i k v : ℕ) : Prop :=
  ∀ (m : Fin 3) (h : Fin 12) (c : Fin 3), atBit (mask i) m h c = true → Rep k v m h c

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem seeds : ∀ (t : Fin 2) (v : Fin (2^(t.val+3))),
    base (t.val+3) v < 28 ∧ ∀ (m : Fin 3) (h : Fin 12) (c : Fin 3),
      atBit (mask (base (t.val+3) v)) m h c = true → witness (t.val+3) v m h c = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem closed : ∀ (i : Fin 28) (hi lo : Fin 2),
    next i hi lo < 28 ∧ ∀ (m : Fin 3) (h : Fin 12) (c : Fin 3),
      atBit (mask (next i hi lo)) m h c = true →
      ∃ j : Fin 8, legal (mask i) m h c hi lo j = true := by decide +kernel

private def boundary (m : ℕ) := if m=2 then 1 else 7

set_option maxRecDepth 10000 in
private theorem outer : ∀ (i : Fin 28) (h : Fin 4) (hi : Fin 2), ∃ m : Fin 3,
    legal (mask i) m (h.val+4) 0 hi 1 (boundary m) = true := by decide +kernel

private lemma seed_good (t : Fin 2) (v : Fin (2^(t.val+3))) :
    ∃ i : Fin 28, Good i (t.val+3) v := by
  have ck := seeds t v
  refine ⟨⟨_,ck.1⟩,?_⟩
  intro m h c present
  have cert := ck.2 m h c present
  obtain ⟨x,hx,y,hy,z,hz,h⟩ := by
    simpa only [witness,List.any_eq_true,decide_eq_true_eq] using cert
  exact ⟨x,y,z,vals_ok _ _ hx,vals_ok _ _ hy,vals_ok _ _ hz,h⟩

-- Any transition backed by a good inner state supplies concrete summands.
private lemma peel {i k v : ℕ} (g : Good i k v) (m : Fin 3) (h c hi lo j : ℕ)
    (ok : legal (mask i) m h c hi lo j = true) :
    ∃ x y z, Pad (k+delta m) x ∧ Pad (k+1) y ∧ Pad k z ∧
    (m.val=2 → y=0 ∧ z=0 ∧ bBit j=0 ∧ cBit j=0) ∧
    wrap (k+delta m) (aBit j) x + wrap (k+1) (bBit j) y + wrap k (cBit j) z + c =
      h*2^(k+2)+(hi*2^(k+1)+2*v+lo) := by
  let H := 2*h+hi-high m j
  let C := (low j+c)/2
  change (decide ((m.val=2 → bBit j=0 ∧ cBit j=0) ∧ 2*h+hi=H+high m j ∧ low j+c=2*C+lo ∧ H<12 ∧ C<3) && atBit (mask i) m H C) = true at ok
  simp only [Bool.and_eq_true,decide_eq_true_eq] at ok
  obtain ⟨allowed,hh,cc,hH,hC⟩ := ok.1
  obtain ⟨x,y,z,px,py,pz,unused,eq⟩ := g m ⟨H,hH⟩ ⟨C,hC⟩ ok.2
  change x+y+z+C=H*2^k+v at eq
  refine ⟨x,y,z,px,py,pz,fun em => ⟨(unused em).1,(unused em).2,allowed em⟩,?_⟩
  calc
    _ = high m j*2^(k+1)+2*(x+y+z)+low j+c := by simp only [wrap,high,low,pow_add,pow_one]; ring
    _ = _ := by
      have mul := congrArg (fun z : ℕ => z*2^(k+1)) hh
      simp only [pow_succ] at mul ⊢
      nlinarith only [mul,cc,eq]

private lemma propagate {k v : ℕ} {i : Fin 28} (g : Good i k v) (hi lo : Fin 2) :
    ∃ q : Fin 28, Good q (k+2) (hi.val*2^(k+1)+2*v+lo.val) := by
  have ck := closed i hi lo
  refine ⟨⟨_,ck.1⟩,?_⟩
  intro m h c present
  obtain ⟨j,legal'⟩ := ck.2 m h c present
  obtain ⟨x,y,z,px,py,pz,unused,eq⟩ := peel g m h c hi lo j legal'
  refine ⟨_,_,_,?_,?_,Pad.grow (cBit j) (Nat.mod_lt _ (by decide)) pz,?_,eq⟩
  · rw [Nat.add_right_comm k 2 (delta m)]
    exact Pad.grow (aBit j) (Nat.mod_lt _ (by decide)) px
  · rw [Nat.add_right_comm k 2 1]
    exact Pad.grow (bBit j) (Nat.mod_lt _ (by decide)) py
  · intro h
    obtain ⟨a,b,e,f⟩ := unused h
    simp [a,b,e,f,wrap]

private lemma split_digits (k z : ℕ) (hz : z < 2^(k+2)) :
    ∃ hi lo : Fin 2, ∃ v < 2^k, z=hi.val*2^(k+1)+2*v+lo.val := by
  let u := z/2
  let q := 2^k
  have qp : 0<q := Nat.two_pow_pos _
  have lim : u/q<2 := by
    apply (Nat.div_lt_iff_lt_mul qp).mpr
    apply (Nat.div_lt_iff_lt_mul (by decide : 0<2)).mpr
    simpa [q,pow_succ,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hz
  refine ⟨⟨u/q,lim⟩,⟨z%2,Nat.mod_lt _ (by decide)⟩,u%q,Nat.mod_lt _ qp,?_⟩
  have lower := Nat.mod_add_div z 2
  have upper := Nat.mod_add_div u q
  change z%2+2*u=z at lower
  change z = u/q*2^(k+1)+2*(u%q)+z%2
  change u%q+2^k*(u/q)=u at upper
  rw [pow_succ]
  nlinarith only [upper,lower]

private theorem interior (r : ℕ) : ∀ v < 2^(r+3), ∃ i : Fin 28, Good i (r+3) v := by
  induction r using Nat.twoStepInduction with
  | zero => intro v hv; exact seed_good (0 : Fin 2) ⟨v,hv⟩
  | one => intro v hv; exact seed_good (1 : Fin 2) ⟨v,hv⟩
  | more r ih _ =>
    intro w hw
    obtain ⟨hi,lo,v,hv,e⟩ := split_digits (r+3) w hw
    obtain ⟨i,h⟩ := ih v hv
    exact e ▸ propagate h hi lo

private def Tri (n : ℕ) : Prop := ∃ x y z : ℕ,
  OeisA261680.isBinaryPalindrome x = true ∧ OeisA261680.isBinaryPalindrome y = true ∧
  OeisA261680.isBinaryPalindrome z = true ∧ x+y+z=n

private lemma outside (k v : ℕ) (hk : 3≤k) (hv : v<2^k) (H : Fin 4) (hi : Fin 2) :
    Tri ((H.val+4)*2^(k+2)+(hi.val*2^(k+1)+2*v+1)) := by
  obtain ⟨r,rfl⟩ : ∃ r, k=r+3 := ⟨k-3,by omega⟩
  obtain ⟨i,g⟩ := interior r v hv
  obtain ⟨m,ok⟩ := outer i H hi
  obtain ⟨x,y,z,px,py,pz,unused,eq⟩ := peel g m (H.val+4) 0 hi 1 (boundary m) ok
  by_cases hm : m.val=2
  · obtain ⟨rfl,rfl,_,_⟩ := unused hm
    refine ⟨_,0,0,canonical px,by decide,by decide,?_⟩
    simpa [boundary,hm,aBit,bBit,cBit,wrap] using eq
  · refine ⟨_,_,_,canonical px,canonical py,canonical pz,?_⟩
    simpa [boundary,hm,aBit,bBit,cBit] using eq

-- The top three bits give the upper carry; the last bit is one.
private lemma odd_large (n : ℕ) (hn : 128≤n) (odd : n%2=1) : Tri n := by
  let k := Nat.log 2 n - 4
  have lg : 7≤Nat.log 2 n := Nat.le_log_of_pow_le (by decide) hn
  have hk : 3≤k := by dsimp [k]; omega
  have ek : k+4=Nat.log 2 n := by dsimp [k]; omega
  have es : k+5=(Nat.log 2 n).succ := by omega
  let p := 2^(k+2)
  have hp : 0<p := Nat.two_pow_pos _
  have lower : 4*p≤n := by
    calc
      _ = 2^(k+4) := by dsimp [p]; ring
      _ ≤ _ := by rw [ek]; exact Nat.pow_log_le_self 2 (by omega)
  have upper : n<8*p := by
    calc
      _ < 2^(k+5) := by rw [es]; exact Nat.lt_pow_succ_log_self (by decide) n
      _ = _ := by dsimp [p]; ring
  let H := n/p
  have Hl : 4≤H := (Nat.le_div_iff_mul_le hp).mpr lower
  have Hu : H<8 := (Nat.div_lt_iff_lt_mul hp).mpr upper
  obtain ⟨hi,lo,v,hv,re⟩ := split_digits k (n%p) (Nat.mod_lt _ hp)
  have ne : n=H*p+(hi.val*2^(k+1)+2*v+lo.val) := by
    calc n = n%p+p*(n/p) := (Nat.mod_add_div n p).symm
         _ = _ := by rw [re]; dsimp [H]; ring
  have parity : n=2*(H*2^(k+1)+hi.val*2^k+v)+lo.val := by
    calc n = _ := ne
         _ = _ := by dsimp [p]; simp only [pow_succ]; ring
  have lr := lo.isLt
  have l1 : lo.val=1 := by omega
  have top := outside k v hk hv (⟨H-4,by omega⟩ : Fin 4) hi
  change Tri ((H-4+4)*2^(k+2)+(hi.val*2^(k+1)+2*v+1)) at top
  rw [Nat.sub_add_cancel Hl] at top
  rw [ne,l1]
  exact top

-- Direct witnesses cover the odd numbers below the first complete carry window.
private def small : Array (ℕ × ℕ × ℕ) := #[
  (0,0,1), (0,0,3), (0,0,5), (0,0,7), (0,0,9), (1,1,9), (1,3,9), (0,0,15),
  (0,0,17), (1,1,17), (0,0,21), (1,1,21), (1,3,21), (0,0,27), (1,1,27), (0,0,31),
  (0,0,33), (1,1,33), (1,3,33), (1,5,33), (1,7,33), (1,9,33), (0,0,45), (1,1,45),
  (1,3,45), (0,0,51), (1,1,51), (1,3,51), (1,5,51), (1,7,51), (1,9,51), (0,0,63),
  (0,0,65), (1,1,65), (1,3,65), (1,5,65), (0,0,73), (1,1,73), (1,3,73), (1,5,73),
  (1,7,73), (1,9,73), (0,0,85), (1,1,85), (1,3,85), (1,5,85), (0,0,93), (1,1,93),
  (1,3,93), (0,0,99), (1,1,99), (1,3,99), (1,5,99), (0,0,107), (1,1,107), (1,3,107),
  (1,5,107), (1,7,107), (1,9,107), (0,0,119), (1,1,119), (1,3,119), (1,5,119), (0,0,127)]

private theorem small_ok : ∀ i : Fin 64, let t := small[i.val]?.getD (0,0,0)
    OeisA261680.isBinaryPalindrome t.1 = true ∧ OeisA261680.isBinaryPalindrome t.2.1 = true ∧
    OeisA261680.isBinaryPalindrome t.2.2 = true ∧ t.1+t.2.1+t.2.2=2*i.val+1 := by decide +kernel

private lemma odd_tri (n : ℕ) (odd : n%2=1) : Tri n := by
  by_cases h : n<128
  · let i : Fin 64 := ⟨n/2,by omega⟩
    have e : n=2*i.val+1 := by dsimp [i]; omega
    have ok := small_ok i
    rw [e]
    exact ⟨_,_,_,ok⟩
  · exact odd_large n (by omega) odd

private lemma count_pos {n x y z w : ℕ} (hx : OeisA261680.isBinaryPalindrome x=true)
    (hy : OeisA261680.isBinaryPalindrome y=true) (hz : OeisA261680.isBinaryPalindrome z=true)
    (hw : OeisA261680.isBinaryPalindrome w=true) (e : x+y+z+w=n) : 0<OeisA261680.a n := by
  unfold OeisA261680.a
  apply Finset.sum_pos' (fun _ _ => Nat.zero_le _)
  refine ⟨x,Finset.mem_range.mpr (by omega),?_⟩
  apply Finset.sum_pos' (fun _ _ => Nat.zero_le _)
  refine ⟨y,Finset.mem_range.mpr (by omega),?_⟩
  apply Finset.sum_pos' (fun _ _ => Nat.zero_le _)
  refine ⟨z,Finset.mem_range.mpr (by omega),?_⟩
  have last : n-(x+y+z)=w := by omega
  simp [last,hx,hy,hz,hw]

theorem tail (n : ℕ) (hn : 30≤n) : 0<OeisA261680.a n := by
  by_cases odd : n%2=1
  · obtain ⟨x,y,z,hx,hy,hz,e⟩ := odd_tri n odd
    exact count_pos hx hy hz (w:=0) (by decide) (by omega)
  · obtain ⟨x,y,z,hx,hy,hz,e⟩ := odd_tri (n-1) (by omega)
    exact count_pos hx hy hz (w:=1) (by decide) (by omega)

end OMA.BinaryPalindromes

theorem OMA.solution : OMA.R_OeisA261680_conjecture_R1.H2 := OMA.BinaryPalindromes.tail
