import FormalConjectures.GreensOpenProblems.«95»

/-!
Zakharov, Most integers are not a sum of two palindromes, arXiv:2402.10808.

Two padded palindromes of lengths m+d and m can be peeled from both ends
in blocks of d+2 digits. Zakharov's two pairs of outer blocks give the
same contribution to the sum. Thus an outer block has at most U-1
different values, where U is the number of pairs of digit words.
Iterating this deterministic bound gives a factor U/(U+t) after t
blocks. Far apart lengths are bounded by counting all pairs of words.
The resulting logarithmic exponent is 1/32.
-/


namespace Z95
open Finset
open scoped Pointwise

def words (g : ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | l + 1 => image₂ List.cons (range g) (words g l)

lemma mem_words {g l : ℕ} {w : List ℕ} :
    w ∈ words g l ↔ w.length = l ∧ ∀ a ∈ w, a < g := by
  induction l generalizing w with
  | zero => cases w <;> simp [words]
  | succ l ih =>
    cases w with
    | nil => simp [words, mem_image₂]
    | cons a w => simp [words, mem_image₂, ih, and_left_comm]

lemma words_card (g l : ℕ) : (words g l).card ≤ g^l := by
  induction l with
  | zero => simp [words]
  | succ l ih =>
    exact (card_image₂_le ..).trans (by simpa [pow_succ, mul_comm] using Nat.mul_le_mul_left g ih)

def pal (g n : ℕ) : Finset ℕ :=
  ((words g n).filter fun w => w.reverse = w).image (Nat.ofDigits g)

lemma mem_pal {g n p : ℕ} : p ∈ pal g n ↔ ∃ w ∈ words g n, w.reverse = w ∧ Nat.ofDigits g w = p := by
  simp [pal, and_assoc]

lemma split {g L m : ℕ} {w : List ℕ} (hw : w ∈ words g (L+m+L)) (hs : w.reverse=w) :
    ∃ a ∈ words g L, ∃ b ∈ words g m, b.reverse=b ∧ w=a++b++a.reverse := by
  obtain ⟨hw, hd⟩ := mem_words.mp hw
  let a := w.take L
  let b := (w.drop L).take m
  let c := (w.drop L).drop m
  have ha : a.length=L := by simp [a, hw]
  have hb : b.length=m := by simp [b, hw]
  have hc : c.length=L := by simp [c, hw]
  have he : w=a++(b++c) := by
    simp [a,b,c]
  have hr : c.reverse ++ (b.reverse ++ a.reverse) = a ++ (b ++ c) := by
    calc _ = (a ++ (b ++ c)).reverse := by simp
         _ = _ := he ▸ hs
  have hca := congrArg (List.take L) hr
  rw [List.take_left' (by simpa using hc), List.take_left' ha] at hca
  have hac : a.reverse=c := by rw [← hca, List.reverse_reverse]
  have hsym : b.reverse=b := by
    rw [hca] at hr
    exact List.append_cancel_right (hac ▸ List.append_cancel_left hr)
  have hd' : ∀ x ∈ a++(b++c), x<g := he ▸ hd
  exact ⟨a, mem_words.mpr ⟨ha, fun x hx => hd' x (by simp [hx])⟩,
    b, mem_words.mpr ⟨hb, fun x hx => hd' x (by simp [hx])⟩, hsym,
    by simpa [List.append_assoc, hac] using he⟩

def edge (g L m : ℕ) (a : List ℕ) := Nat.ofDigits g a + g^(L+m)*Nat.ofDigits g a.reverse

lemma pal_split {g L m p : ℕ} (hp : p ∈ pal g (L+m+L)) :
    ∃ a ∈ words g L, ∃ q ∈ pal g m, p = edge g L m a + g^L*q := by
  obtain ⟨w, hw, hs, rfl⟩ := mem_pal.mp hp
  obtain ⟨a,ha,b,hb,hb',rfl⟩ := split hw hs
  refine ⟨a,ha,_,mem_pal.mpr ⟨b,hb,hb',rfl⟩,?_⟩
  simp only [Nat.ofDigits_append,List.length_append,(mem_words.mp ha).1,(mem_words.mp hb).1,edge]
  ring

lemma pal_card (g n : ℕ) : (pal g n).card ≤ g^((n+1)/2) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | m
    · exact (card_image_le.trans (card_filter_le ..)).trans (words_card g 0)
    · exact (card_image_le.trans (card_filter_le ..)).trans (words_card g 1)
    · have sub : pal g (m+2) ⊆ image₂ (fun a q => edge g 1 m a + g^1*q) (words g 1) (pal g m) := by
        intro p hp
        obtain ⟨a,ha,q,hq,he⟩ := pal_split (L:=1) (m:=m) (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hp : p ∈ pal g (1+m+1))
        exact mem_image₂.mpr ⟨a, ha, q, hq, he.symm⟩
      refine (card_le_card sub).trans ((card_image₂_le ..).trans ?_)
      have he : (m+2+1)/2 = (m+1)/2+1 := by omega
      rw [he, pow_succ, mul_comm]
      exact Nat.mul_le_mul (ih m (by omega)) (by simpa using words_card g 1)

end Z95


namespace Z95
open Finset
open scoped Pointwise

private lemma digits_zero (g d : ℕ) : Nat.ofDigits g (List.replicate d 0) = 0 := by
  induction d with
  | zero => rfl
  | succ d ih => simp [List.replicate_succ, Nat.ofDigits, ih]

private lemma digits_max {g : ℕ} (hg : 2 ≤ g) (d : ℕ) :
    Nat.ofDigits g (List.replicate d (g-1)) + 1 = g^d := by
  induction d with
  | zero => simp
  | succ d ih =>
    simp only [List.replicate_succ, Nat.ofDigits_cons, pow_succ]
    rw [← ih]
    have : g-1+1=g := by omega
    nlinarith

def edgeSum (g d m : ℕ) (p : List ℕ × List ℕ) :=
  edge g (d+2) (m+d) p.1 + edge g (d+2) m p.2

private theorem collide {g d m : ℕ} (hg : 2≤g) :
    ¬ Set.InjOn (edgeSum g d m) ↑((words g (d+2)) ×ˢ (words g (d+2))) := by
  let a := 1 :: (List.replicate d 0 ++ [1])
  let b := List.replicate (d+2) 0
  let c := 0 :: (List.replicate d (g-1) ++ [0])
  let e := 1 :: 1 :: List.replicate d 0
  have h1 : 1 < g := by omega
  have h0 : 0 < g := by omega
  have hm : g-1 < g := by omega
  have ha : a ∈ words g (d+2) := by simp [mem_words,a]; aesop
  have hb : b ∈ words g (d+2) := by simp [mem_words,b]; aesop
  have hc : c ∈ words g (d+2) := by simp [mem_words,c]; aesop
  have he : e ∈ words g (d+2) := by simp [mem_words,e]; aesop
  have hh : edgeSum g d m (a,b) = edgeSum g d m (c,e) := by
    simp only [edgeSum,edge,a,b,c,e,List.reverse_cons,List.reverse_append,List.reverse_replicate,
      List.reverse_singleton,List.singleton_append,List.reverse_nil,List.nil_append,List.append_assoc,
      Nat.ofDigits_append,Nat.ofDigits_cons,Nat.ofDigits_nil,List.length_replicate,List.length_cons,
      List.length_nil,digits_zero,mul_zero,add_zero,zero_add,one_mul,mul_one,pow_zero]
    have h := digits_max hg d
    simp only [pow_add, pow_succ, pow_one] at *
    rw [← h]
    ring
  intro hi
  have heq : (a,b)=(c,e) := hi (Finset.mem_product.mpr ⟨ha,hb⟩) (Finset.mem_product.mpr ⟨hc,he⟩) hh
  have := congrArg (fun p : List ℕ × List ℕ => p.1.head?) heq
  simp [a,c] at this

def sumPal (g d m : ℕ) := pal g (m+d) + pal g m

def blockSize (g d : ℕ) := g^(2*(d+2))
def freeSize (g d m : ℕ) := g^((m+d+1)/2+(m+1)/2)

lemma basic (g d m : ℕ) : (sumPal g d m).card ≤ freeSize g d m := by
  exact card_add_le.trans (by simpa [freeSize, pow_add] using Nat.mul_le_mul (pal_card g (m+d)) (pal_card g m))

lemma blockStep {g d m : ℕ} (hg : 2≤g) :
    (sumPal g d (m+2*(d+2))).card ≤ (blockSize g d-1)*(sumPal g d m).card := by
  let L := d+2
  let P := words g L ×ˢ words g L
  let E := P.image (edgeSum g d m)
  have hE : E.card < blockSize g d := by
    have hl : E.card < P.card := lt_of_le_of_ne card_image_le (fun h => collide hg (card_image_iff.mp h))
    apply hl.trans_le
    simpa [P, blockSize,L, two_mul,pow_add] using Nat.mul_le_mul (words_card g L) (words_card g L)
  have hsub : sumPal g d (m+2*(d+2)) ⊆ image₂ (fun v z => v+g^L*z) E (sumPal g d m) := by
    intro v hv
    obtain ⟨p,hp,q,hq,rfl⟩ := Finset.mem_add.mp hv
    obtain ⟨a,ha,p,hp',rfl⟩ := pal_split (L:=L) (m:=m+d)
      (by convert hp using 2 <;> dsimp [L] <;> omega : p ∈ pal g (L+(m+d)+L))
    obtain ⟨b,hb,q,hq',rfl⟩ := pal_split (L:=L) (m:=m)
      (by convert hq using 2 <;> dsimp [L] <;> omega : q ∈ pal g (L+m+L))
    exact mem_image₂.mpr ⟨_, mem_image.mpr ⟨(a,b),mem_product.mpr ⟨ha,hb⟩,rfl⟩,
      p+q, Finset.add_mem_add hp' hq', by simp only [edgeSum]; dsimp [L]; ring⟩
  exact (card_le_card hsub).trans ((card_image₂_le ..).trans (Nat.mul_le_mul_right _ (by omega)))

lemma saved {g : ℕ} (hg : 2 ≤ g) (d m : ℕ) :
    (sumPal g d m).card * (blockSize g d + m / (2*(d+2))) ≤ freeSize g d m * blockSize g d := by
  let T := 2*(d+2)
  let U := blockSize g d
  have hT : 0<T := by dsimp [T]; omega
  have hU : 1≤U := pow_pos (by omega : 0<g) _
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases h : m<T
    · rw [Nat.div_eq_of_lt h, Nat.add_zero]
      exact Nat.mul_le_mul_right _ (basic ..)
    · let r := m-T
      have he : m=r+T := by dsimp [r]; omega
      have hr := ih r (by omega)
      have hs := blockStep (d:=d) (m:=r) hg
      have hF : freeSize g d (r+T) = freeSize g d r * U := by
        dsimp only [freeSize,U,blockSize]
        rw [← pow_add]
        congr 1
        dsimp [T]
        omega
      rw [he, Nat.add_div_right _ hT, hF]
      change (sumPal g d (r+T)).card*(U+(r/T+1)) ≤ freeSize g d r * U * U
      calc _ ≤ (U-1)*(sumPal g d r).card*(U+(r/T+1)) := Nat.mul_le_mul_right _ hs
           _ ≤ ((sumPal g d r).card*(U+r/T))*U := by
             have h : (U-1)*(U+(r/T+1)) ≤ (U+r/T)*U := by
               obtain ⟨a,ha⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : U≠0)
               rw [ha]
               simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
               generalize r/T = z
               calc _ ≤ a*(a+1+(z+1))+(z+1) := Nat.le_add_right ..
                    _ = _ := by ring
             simpa only [mul_assoc, mul_left_comm, mul_comm] using Nat.mul_le_mul_left (sumPal g d r).card h
           _ ≤ _ := Nat.mul_le_mul_right _ hr

end Z95



namespace Z95
open Finset
open scoped Pointwise

private def weight (g n : ℕ) := g^((n+1)/2)
private def mass (g k : ℕ) := ∑ n ∈ range (k+1), weight g n

private lemma mass_le {g : ℕ} (hg : 2 ≤ g) (k : ℕ) : mass g k  ≤  4*weight g k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | _ | k
    · simp [mass,weight]
    · simp [mass,weight,Finset.sum_range_succ]; omega
    · have h := ih k (by omega)
      have he : weight g (k+2)=weight g k*g := by
        unfold weight
        rw [show (k+2+1)/2=(k+1)/2+1 by omega, pow_succ]
      have h1 : weight g (k+1)  ≤  weight g (k+2) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      unfold mass
      rw [sum_range_succ, sum_range_succ]
      change mass g k + weight g (k+1) + weight g (k+2)  ≤  _
      rw [he] at h1 ⊢
      nlinarith [Nat.mul_le_mul_left (weight g k) hg]

private def allPal (g k : ℕ) := (range (k+1)).biUnion (pal g)

private lemma all_card (g k : ℕ) : (allPal g k).card  ≤  mass g k :=
  card_biUnion_le.trans (sum_le_sum (fun n _ => pal_card g n))

private lemma exp_large {g j : ℕ} (hg : 2 ≤ g) (hj : 8 ≤ j) : 16*j+16  ≤  g^j := by
  induction j, hj using Nat.le_induction with
  | base => exact le_trans (by decide : 16*8+16 ≤ 2^8) (Nat.pow_le_pow_left hg _)
  | succ n hn ih =>
    rw [pow_succ]
    have h := Nat.mul_le_mul_right (g^n) hg
    nlinarith

private lemma near_ordered {g k j m n : ℕ} (hg : 2 ≤ g) (hj : 8 ≤ j) (hk : g^(16*j) ≤ k)
    (hm : k-2*j ≤ m) (hn : n ≤ k) (hmn : m ≤ n) :
    (pal g n + pal g m).card*g^j  ≤  weight g n * weight g m := by
  let d := n-m
  let T := 2*(d+2)
  let U := blockSize g d
  have hd : d ≤ 2*j := by dsimp [d]; omega
  have hJ := exp_large hg hj
  have hT : T ≤ g^j := by dsimp [T]; omega
  have hU : U  ≤  g^(4*j+4) := Nat.pow_le_pow_right (by omega)
    (show 2*(d+2) ≤ 4*j+4 by omega)
  have hsmall : U*g^j*T  ≤  g^(6*j+4) := by
    calc _  ≤  g^(4*j+4)*g^j*g^j := Nat.mul_le_mul (Nat.mul_le_mul_right _ hU) hT
         _ = _ := by rw [← pow_add, ← pow_add]; congr 1; omega
  have hrest : g^(6*j+4)+2*j  ≤  k := by
    have h1 : g^j ≤ g^(6*j+4) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : g^(6*j+4+1)  ≤  g^(16*j) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [pow_succ] at h2
    have h3 := Nat.mul_le_mul_left (g^(6*j+4)) hg
    omega
  have hdiv : U*g^j  ≤  m/T := (Nat.le_div_iff_mul_le (by dsimp [T]; omega)).mpr (by omega)
  have hS := saved hg d m
  change (sumPal g d m).card * (U + m/T)  ≤  freeSize g d m * U at hS
  have h' : (sumPal g d m).card * g^j * U  ≤  freeSize g d m * U := by
    rw [mul_assoc, mul_comm (g^j)]
    exact (Nat.mul_le_mul_left _ (hdiv.trans (Nat.le_add_left ..))).trans hS
  have hu : 0<U := pow_pos (by omega : 0<g) _
  have out := Nat.le_of_mul_le_mul_right h' hu
  have he : m+d=n := by dsimp [d]; omega
  simpa [sumPal,freeSize,weight,he,pow_add] using out

private def near (g k j : ℕ) := (Icc (k-2*j) k).biUnion fun n =>
  (Icc (k-2*j) k).biUnion fun m => pal g n + pal g m

private lemma near_card {g k j : ℕ} (hg : 2 ≤ g) (hj : 8 ≤ j) (hk : g^(16*j) ≤ k) :
    (near g k j).card*g^j  ≤  mass g k * mass g k := by
  let I := Icc (k-2*j) k
  have hI : I ⊆ range (k+1) := fun n hn => mem_range.mpr (by have := (mem_Icc.mp hn).2; omega)
  have hs : (∑ n ∈ I, weight g n)  ≤  mass g k := sum_le_sum_of_subset hI
  have hb (n : ℕ) (hn : n∈I) (m : ℕ) (hm : m∈I) :
      (pal g n + pal g m).card*g^j  ≤  weight g n * weight g m := by
    rcases le_total m n with h | h
    · exact near_ordered hg hj hk (mem_Icc.mp hm).1 (mem_Icc.mp hn).2 h
    · simpa [add_comm,mul_comm] using near_ordered hg hj hk (mem_Icc.mp hn).1 (mem_Icc.mp hm).2 h
  have h : (near g k j).card  ≤  ∑ n ∈ I, ∑ m ∈ I, (pal g n + pal g m).card :=
      card_biUnion_le.trans (sum_le_sum fun n _ => card_biUnion_le)
  calc _  ≤  (∑ n ∈ I, ∑ m ∈ I, (pal g n + pal g m).card)*g^j := Nat.mul_le_mul_right _ h
       _ = ∑ n ∈ I, ∑ m ∈ I, (pal g n + pal g m).card*g^j := by simp only [sum_mul]
       _  ≤  ∑ n ∈ I, ∑ m ∈ I, weight g n * weight g m := sum_le_sum fun n hn => sum_le_sum (hb n hn)
       _ = (∑ n ∈ I, weight g n)*(∑ n ∈ I, weight g n) := by rw [sum_mul]; simp only [mul_sum]
       _  ≤  _ := Nat.mul_le_mul hs hs

theorem count {g k j X : ℕ} (hg : 2 ≤ g) (hj : 8 ≤ j) (hk : g^(16*j) ≤ k) (hX : X ≤ g^k) :
    (Green95.sumsOfTwo g ∩ Set.Iio X).ncard*g^j  ≤  32*g^(k+1) := by
  let far := allPal g k + allPal g (k-2*j)
  have hsub : Green95.sumsOfTwo g ∩ Set.Iio X ⊆ (↑(far ∪ near g k j) : Set ℕ) := by
    rintro s ⟨⟨p,q,sp,sq,rfl⟩,hl⟩
    change p+q < X at hl
    let n := (g.digits p).length
    let m := (g.digits q).length
    have hp' : p∈pal g n := mem_pal.mpr ⟨g.digits p,mem_words.mpr ⟨rfl,fun _ => Nat.digits_lt_base hg⟩,sp,Nat.ofDigits_digits ..⟩
    have hq' : q∈pal g m := mem_pal.mpr ⟨g.digits q,mem_words.mpr ⟨rfl,fun _ => Nat.digits_lt_base hg⟩,sq,Nat.ofDigits_digits ..⟩
    have hn : n ≤ k := (Nat.digits_length_le_iff hg p).mpr (by omega)
    have hm : m ≤ k := (Nat.digits_length_le_iff hg q).mpr (by omega)
    have ins {a l K : ℕ} (h : a∈pal g l) (hl : l ≤ K) : a∈allPal g K :=
      mem_biUnion.mpr ⟨l,mem_range.mpr (by omega),h⟩
    change p+q ∈ far ∪ near g k j
    by_cases hm' : m ≤ k-2*j
    · exact mem_union_left _ (add_mem_add (ins hp' hn) (ins hq' hm'))
    by_cases hn' : n ≤ k-2*j
    · rw [Nat.add_comm]
      exact mem_union_left _ (add_mem_add (ins hq' hm) (ins hp' hn'))
    · exact mem_union_right _ (mem_biUnion.mpr ⟨n,mem_Icc.mpr ⟨by omega,hn⟩,
        mem_biUnion.mpr ⟨m,mem_Icc.mpr ⟨by omega,hm⟩,add_mem_add hp' hq'⟩⟩)
  have hcard := Set.ncard_le_ncard hsub (far ∪ near g k j).finite_toSet
  rw [Set.ncard_coe_finset] at hcard
  have hfar : far.card  ≤  mass g k * mass g (k-2*j) :=
    card_add_le.trans (Nat.mul_le_mul (all_card ..) (all_card ..))
  have hkj : 2*j ≤ k := by
    have := exp_large hg hj
    have : g^j ≤ g^(16*j) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hpow : weight g (k-2*j)*g^j=weight g k := by
    unfold weight
    rw [←pow_add]; congr 1; omega
  have hfar' : far.card*g^j  ≤  16*(weight g k)^2 := by
    calc _  ≤  ((4*weight g k)*(4*weight g (k-2*j)))*g^j :=
          Nat.mul_le_mul_right _ (hfar.trans (Nat.mul_le_mul (mass_le hg _) (mass_le hg _)))
         _ = _ := by rw [← hpow]; ring
  have hnear' := (near_card hg hj hk).trans (Nat.mul_le_mul (mass_le hg k) (mass_le hg k))
  have hw : (weight g k)^2 ≤ g^(k+1) := by
    rw [weight,←pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have h := Nat.mul_le_mul_right (g^j) (hcard.trans (card_union_le ..))
  rw [add_mul] at h
  nlinarith

end Z95



namespace Z95
open Filter Real
open scoped Topology

theorem main {g : ℕ} (hg : 2 ≤ g) : ∀ᶠ X : ℕ in atTop,
    ((Green95.sumsOfTwo g ∩ Set.Iio X).ncard : ℝ) ≤ (X : ℝ) / Real.log X ^ (1/32 : ℝ) := by
  let b := g^16
  have hb : 1 < b := one_lt_pow₀ (by omega : 1<g) (by decide)
  filter_upwards [eventually_ge_atTop (max 2 (g^(b^32)))] with X hX
  have hX2 := (le_max_left 2 (g^(b^32))).trans hX
  let k := Nat.log g X+1
  let j := Nat.log b k
  have hx : X ≤ g^k := (Nat.lt_pow_succ_log_self hg X).le
  have hx' : g^(Nat.log g X) ≤ X := Nat.pow_log_le_self _ (by omega)
  have hbk : b^32 ≤ k := Nat.le_trans
    (Nat.le_log_of_pow_le hg ((le_max_right 2 (g^(b^32))).trans hX)) (Nat.le_succ _)
  have hj : 32 ≤ j := Nat.le_log_of_pow_le hb hbk
  have hk : g^(16*j) ≤ k := by
    rw [pow_mul]; exact Nat.pow_log_le_self _ (Nat.succ_ne_zero _)
  have hk' : k ≤ g^(16*(j+1)) := by
    rw [pow_mul]; exact (Nat.lt_pow_succ_log_self hb k).le
  let A := (Green95.sumsOfTwo g ∩ Set.Iio X).ncard
  let C := 32*g^2
  have hbound : A*g^j ≤ C*X := by
    apply (count hg (by omega : 8≤j) hk hx).trans
    dsimp only [k,C]
    rw [pow_succ, pow_succ]
    nlinarith [Nat.mul_le_mul_right (32*g*g) hx']
  have hC : C ≤ g^7 := by
    have hs : 32≤g^5 := (show 32=2^5 by decide) ▸ Nat.pow_le_pow_left hg 5
    calc _ ≤ g^5*g^2 := Nat.mul_le_mul_right _ hs
         _ = _ := (pow_add ..).symm
  have hpow : C^32 *(k*g) ≤ (g^j)^32 := by
    calc _ ≤ (g^7)^32 * (g^(16*(j+1))*g) :=
               Nat.mul_le_mul (Nat.pow_le_pow_left hC 32) (Nat.mul_le_mul_right _ hk')
         _ = g^(7*32+16*(j+1)+1) := by simp only [pow_add,pow_mul,pow_one]; ring
         _ ≤ _ := by rw [←pow_mul]; exact Nat.pow_le_pow_right (by omega) (by omega)
  have hgR : (0 : ℝ)≤g := by positivity
  have hX0 : (0:ℝ)<X := by exact_mod_cast (show 0<X by omega)
  have hl0 : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1<X by omega))
  have hlog : Real.log X ≤ (k:ℝ)*g := by
    have hh := Real.log_le_log hX0 (show (X:ℝ)≤(g:ℝ)^k by exact_mod_cast hx)
    rw [Real.log_pow] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (Real.log_le_self hgR) (by positivity))
  have h32 : ((Real.log X)^(1/32 : ℝ))^32 = Real.log X := by
    rw [← Real.rpow_mul_natCast hl0.le]; norm_num
  have hscale : (C:ℝ)*Real.log X^(1/32 : ℝ) ≤ (g^j : ℕ) := by
    apply le_of_pow_le_pow_left₀ (n:=32) (by decide) (by positivity)
    rw [mul_pow, h32]
    exact (mul_le_mul_of_nonneg_left hlog (by positivity)).trans (by exact_mod_cast hpow)
  have hC0 : (0:ℝ)<C := by dsimp [C]; positivity
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hl0 _)).mpr
  change (A:ℝ)*Real.log X^(1/32 : ℝ) ≤ X
  apply le_of_mul_le_mul_left (a:= (C:ℝ)) _ hC0
  calc _ = (A:ℝ)*((C:ℝ)*Real.log X^(1/32 : ℝ)) := by ring
       _ ≤ (A:ℝ)*(g^j : ℕ) := mul_le_mul_of_nonneg_left hscale (by positivity)
       _ ≤ _ := by exact_mod_cast hbound

end Z95



open Filter Real
open scoped Topology

theorem OMA.solution : type_of% @Green95.green_95 := by
  intro g hg
  let S := Green95.sumsOfTwo g
  have hinv : Tendsto (fun n : ℕ => (Real.log n^(1/32 : ℝ))⁻¹) atTop (𝓝 0) :=
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/32)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).inv_tendsto_atTop
  have ht : Tendsto (S.partialDensity Set.univ) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => by unfold Set.partialDensity; positivity) _ hinv
    filter_upwards [Z95.main hg,eventually_ge_atTop 2] with n h hn
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
    change ((Green95.sumsOfTwo g ∩ Set.Iio n).ncard : ℝ)/(n:ℝ) ≤ _
    apply (div_le_iff₀ (by exact_mod_cast (show 0<n by omega) : 0<(n:ℝ))).mpr
    simpa only [div_eq_mul_inv, mul_comm] using h
  rw [Set.lowerDensity, show (atTop.liminf fun n : ℕ => S.partialDensity Set.univ n) = 0 from ht.liminf_eq]
  exact lt_irrefl _

