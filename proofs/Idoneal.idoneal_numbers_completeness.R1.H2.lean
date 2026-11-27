import OMAReductions.R_Idoneal_idoneal_numbers_completeness_R1

/-! # A modular sieve for the finite idoneal-number range -/
-- Credit: @steveDOTdigital
namespace OMA.IdonealSieve
open Finset

-- Each residue mask marks residues without a usable square root of minus n.
private structure Row where
  q : ℕ
  mask : ℕ
  depth : ℕ
  deriving DecidableEq

private def rows : List Row := [
  ⟨3,3,15⟩,
  ⟨5,13,14⟩,
  ⟨7,23,14⟩,
  ⟨11,571,13⟩,
  ⟨13,2533,13⟩,
  ⟨17,23785,12⟩,
  ⟨19,199411,12⟩,
  ⟨23,340831,12⟩,
  ⟨29,204397837,12⟩,
  ⟨31,303908791,12⟩,
  ⟨37,41370444133,11⟩,
  ⟨41,328519579849,11⟩,
  ⟨43,3678700564051,11⟩,
  ⟨47,4626135339999,11⟩,
  ⟨53,3697175711994157,11⟩,
  ⟨59,156326468341437115,11⟩,
  ⟨61,642916798280633797,11⟩,
  ⟨67,61808106872519771731,10⟩,
  ⟨71,20052041432995567487,10⟩,
  ⟨73,384875580742593342625,10⟩,
  ⟨79,89932533647391829339959,10⟩,
  ⟨83,2911111237809585785085595,10⟩,
  ⟨89,92163013807473543562719433,10⟩,
  ⟨97,6380052750319376475725948065,10⟩,
  ⟨101,984868415575749434490170416525,10⟩,
  ⟨103,1760368345969468176824550810519,10⟩,
  ⟨107,50079290986288516948354744811035,10⟩,
  ⟨109,176014145500707040523653282164037,10⟩,
  ⟨113,1797644397492755318821822240789609,10⟩,
  ⟨127,30790515292689894969866990722818747159,10⟩,
  ⟨131,736595995152387833549853625256200223419,9⟩,
  ⟨137,30179077125861480759279369339831925617769,9⟩,
  ⟨139,264983527547230301571683161851591864167155,9⟩,
  ⟨149,271771707175801987860979625893642796133580045,9⟩,
  ⟨151,425021430996567349671854096638566139059703607,9⟩,
  ⟨157,56382897303629494179631795089211348116942651877,9⟩]

private def tile (q m : ℕ) : ℕ → ℕ
  | 0 => m
  | d+1 => let v := tile q m d; v ||| (v <<< (q*2^d))

private def width := 65536

private def rowBits (r : Row) (b : ℕ) : ℕ :=
  ((tile r.q r.mask r.depth) >>> ((b*width)%r.q)) |||
    (if b = 0 then 2^(r.q*r.q+1)-1 else 0)

private def survivors (b : ℕ) : ℕ :=
  rows.foldl (fun w r => w &&& rowBits r b) (2^width-1)

private def Rep (n : ℕ) := ∃ a b c : ℕ, 0<a ∧ a<b ∧ b<c ∧ n=a*b+b*c+a*c

-- n+a²=qv and 2a<q<v give (a,b,c)=(a,q-a,v-a).
private lemma factor {n a q : ℕ} (ha : 0 < a) (h : 2*a < q)
    (divide : q ∣ n+a*a) (large : q*q < n) : Rep n := by
  obtain ⟨v,hv⟩ := divide
  have gt : q < v := by
    by_contra! no
    have := Nat.mul_le_mul_left q no
    omega
  obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le (show a ≤ q by omega)
  obtain ⟨c,rfl⟩ := Nat.exists_eq_add_of_le (show a ≤ v by omega)
  exact ⟨a,b,c,ha,by omega,by omega,by nlinarith only [hv]⟩

private def Valid (r : Row) : Prop :=
  0<r.q ∧ r.q*r.q < width ∧ width+r.q ≤ r.q*2^r.depth ∧
  ∀ i : Fin r.q, r.mask.testBit i.val = false →
    ∃ a : Fin r.q, 0<a.val ∧ 2*a.val<r.q ∧ (i.val + a.val*a.val)%r.q=0

private instance (r : Row) : Decidable (Valid r) := by unfold Valid; infer_instance

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1500000 in
private lemma rowsChecked : rows.all (fun r => decide (Valid r)) = true := by decide +kernel

private lemma tile_true (q m d i : ℕ) (bound : i < q*2^d) (h : m.testBit (i%q) = true) :
    (tile q m d).testBit i = true := by
  induction d generalizing i with
  | zero =>
    simp only [pow_zero,Nat.mul_one] at bound
    simpa [tile,Nat.mod_eq_of_lt bound] using h
  | succ d ih =>
    rw [tile,Nat.testBit_or,Bool.or_eq_true]
    by_cases low : i < q*2^d
    · exact Or.inl (ih _ low h)
    · right
      have ge := Nat.le_of_not_gt low
      rw [Nat.testBit_shiftLeft,decide_eq_true ge,Bool.true_and]
      have large : i < q*2^d + q*2^d := by simpa [pow_succ,Nat.mul_assoc,Nat.mul_two,Nat.mul_add] using bound
      apply ih _ (by omega)
      have e : (i - q*2^d)%q = i%q := by
        calc
          _ = (i - q*2^d + q*2^d)%q := (Nat.add_mul_mod_self_left _ _ _).symm
          _ = _ := by rw [Nat.sub_add_cancel ge]
      rwa [e]

private lemma row_true (r : Row) (vr : Valid r) (b j : ℕ) (small : j < width)
    (no : ¬Rep (b*width+j)) : (rowBits r b).testBit j = true := by
  obtain ⟨qp,qw,deep,mask⟩ := vr
  rw [rowBits,Nat.testBit_or,Bool.or_eq_true]
  by_cases large : r.q*r.q < b*width+j
  · left
    rw [Nat.testBit_shiftRight]
    have rem := Nat.mod_lt (b*width) qp
    apply tile_true _ _ _ _ (by omega)
    have e : ((b*width)%r.q+j)%r.q = (b*width+j)%r.q := Nat.mod_add_mod _ _ _
    rw [e]
    by_contra! bad
    have bit : r.mask.testBit ((b*width+j)%r.q) = false := by cases h : r.mask.testBit ((b*width+j)%r.q) <;> simp_all
    obtain ⟨a,ha,lt,eq⟩ := mask ⟨(b*width+j)%r.q,Nat.mod_lt _ qp⟩ bit
    apply no (factor ha lt ?_ large)
    apply Nat.dvd_of_mod_eq_zero
    exact (Nat.mod_add_mod _ _ _).symm.trans eq
  · right
    have z : b=0 := by
      by_contra! pos
      have := Nat.mul_le_mul_right width (show 1 ≤ b by omega)
      simp only [Nat.one_mul] at this
      omega
    subst b
    simp only [if_true,Nat.testBit_two_pow_sub_one,decide_eq_true_eq]
    simp only [Nat.zero_mul,Nat.zero_add] at large
    omega

private lemma survive (b j : ℕ) (hj : j<width) (no : ¬Rep (b*width+j)) :
    (survivors b).testBit j = true := by
  have all (r : Row) (hr : r ∈ rows) := row_true r (of_decide_eq_true (List.all_eq_true.mp rowsChecked r hr)) b j hj no
  have fold (rs : List Row) (sub : ∀ r ∈ rs, r ∈ rows) (w : ℕ) (hw : w.testBit j = true) :
      (rs.foldl (fun v r => v &&& rowBits r b) w).testBit j = true := by
    induction rs generalizing w with
    | nil => exact hw
    | cons r rs ih =>
      change (rs.foldl _ (w &&& rowBits r b)).testBit j = true
      apply ih (fun t ht => sub t (List.mem_cons_of_mem _ ht))
      simp [hw,all r (sub r List.mem_cons_self)]
  exact fold rows (fun _ h => h) _ (by simp [hj])
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem positiveCheck : (List.range 1525).all (fun j => survivors (j+1) == 0) = true := by
  decide +kernel

private def known : List ℕ := [1,2,3,4,5,6,7,8,9,10,12,13,15,16,18,21,22,24,25,28,30,33,37,40,42,45,48,57,58,60,70,72,78,85,88,93,102,105,112,120,130,133,165,168,177,190,210,232,240,253,273,280,312,330,345,357,385,408,462,520,760,840,1320,1365,1848]
private def triples : List (ℕ × ℕ × ℕ) := [
  (1,3,4),
  (1,3,6),
  (1,3,10),
  (1,3,15),
  (1,3,16),
  (2,6,11),
  (1,3,33),
  (1,3,36),
  (2,6,17),
  (1,3,40),
  (1,3,61),
  (1,3,66),
  (2,6,32),
  (3,6,35),
  (3,6,56),
  (2,6,80),
  (2,6,87),
  (4,12,55),
  (1,3,366)]
private def value (w : ℕ × ℕ × ℕ) := w.1*w.2.1 + w.2.1*w.2.2 + w.1*w.2.2
private def mark : List ℕ → ℕ
  | [] => 0
  | x::xs => 2^x ||| mark xs

private lemma marked (xs : List ℕ) (n : ℕ) (h : (mark xs).testBit n = true) : n ∈ xs := by
  induction xs with
  | nil => simp [mark] at h
  | cons x xs ih =>
    simp only [mark,Nat.testBit_or,Nat.testBit_two_pow,Bool.or_eq_true,decide_eq_true_eq] at h
    exact h.elim (fun e => e ▸ List.mem_cons_self) (fun hx => List.mem_cons_of_mem _ (ih hx))

set_option maxRecDepth 8000 in
private lemma firstCheck : survivors 0 = mark (0 :: known ++ triples.map value) := by decide +kernel

private lemma small_case (n : ℕ) (hn : 0<n) (nk : n ∉ Idoneal.knownIdonealNumbers)
    (h : (survivors 0).testBit n = true) : Rep n := by
  have ka : known.all (fun v => decide (v ∈ Idoneal.knownIdonealNumbers)) = true := by decide +kernel
  have ta : triples.all (fun w => decide (0<w.1 ∧ w.1<w.2.1 ∧ w.2.1<w.2.2)) = true := by decide +kernel
  rw [firstCheck] at h
  have mem := marked _ _ h
  simp only [List.mem_cons,List.mem_append,List.mem_map] at mem
  rcases mem with (e|hk)|⟨t,ht,eq⟩
  · omega
  · exact (nk (of_decide_eq_true (List.all_eq_true.mp ka _ hk))).elim
  · have ord := of_decide_eq_true (List.all_eq_true.mp ta t ht)
    exact ⟨t.1,t.2.1,t.2.2,ord.1,ord.2.1,ord.2.2,eq.symm⟩

private theorem finite_check (n : ℕ) (hn : 0 < n) (bound : n < 10^8) (nk : n ∉ Idoneal.knownIdonealNumbers) : Rep n := by
  by_contra no
  let b := n / width
  let j := n % width
  have eq : b*width+j=n := by simpa [b,j,Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div n width
  have hj : j < width := Nat.mod_lt _ (by decide)
  have h := survive b j hj (fun rep => no (eq ▸ rep))
  by_cases zero : b=0
  · rw [zero,Nat.zero_mul,Nat.zero_add] at eq
    rw [zero,eq] at h
    exact no (small_case n hn nk h)
  · obtain ⟨i,hi⟩ : ∃ i, b=i+1 := Nat.exists_eq_add_one_of_ne_zero zero
    have lim : b < 1526 := (Nat.div_lt_iff_lt_mul (show 0 < width by decide)).mpr
      (lt_of_lt_of_le bound (by decide))
    have cap : i < 1525 := by omega
    have z := of_decide_eq_true (show decide (survivors (i+1)=0) = true by
      simpa using List.all_eq_true.mp positiveCheck i (List.mem_range.mpr cap))
    rw [hi,z] at h
    simp at h

end OMA.IdonealSieve

theorem OMA.solution : OMA.R_Idoneal_idoneal_numbers_completeness_R1.H2 := OMA.IdonealSieve.finite_check
