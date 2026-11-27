import FormalConjectures.OEIS.«55487»

/-! # A cubic bound for the least inverse totient of a factorial

Primes dividing a competitor bound its totient loss from below. A single sufficiently
short inverse forces the minimum to be a product of distinct primes. The least prime in
Hasler's definition then selects a minimum among all two-prime representations. -/

namespace OMA.R_OeisA55487_conjecture_R1

open OeisA55487

/-- The multiples of a prime divisor account for at least its cofactor in the totient loss. -/
theorem prime_divisor_loss {r : ℕ} (hr : r.Prime) (k : ℕ) :
    (r*k).totient + k ≤ r*k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    by_cases hd : r ∣ k
    · obtain ⟨t, rfl⟩ := hd
      have ht : 0 < t := Nat.pos_of_mul_pos_left hk
      have hlt : t < r*t := by nlinarith [hr.two_le]
      rw [Nat.totient_mul_of_prime_of_dvd hr (dvd_mul_right r t), ← Nat.mul_add]
      exact Nat.mul_le_mul_left _ (ih t hlt)
    · rw [Nat.totient_mul_of_prime_of_not_dvd hr hd]
      have hpred : r - 1 + 1 = r := Nat.sub_add_cancel hr.one_lt.le
      nlinarith [Nat.mul_le_mul_left (r-1) (Nat.totient_le k),
        congrArg (· * k) hpred]

/-- A composite number in the cubic range is a product of two primes, counting multiplicity. -/
theorem short_composite {m : ℕ} (hm : 1 < m) (hnp : ¬ m.Prime)
    (hshort : (m - m.totient)^3 ≤ m.totient^2) :
    ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ m = r*s := by
  let r := m.minFac
  have hr : r.Prime := Nat.minFac_prime (by omega)
  obtain ⟨k,hk⟩ := Nat.minFac_dvd m
  change m = r*k at hk
  have hnot1 : k ≠ 1 := by
    intro h
    rw [h, mul_one] at hk
    exact hnp (hk ▸ hr)
  have hkpos : 0 < k := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at hk; omega
  refine ⟨r,k,hr,?_,hk⟩
  by_contra hcomp
  have hsmall : r ≤ k.minFac := Nat.minFac_le_of_dvd
    (Nat.minFac_prime hnot1).two_le ((Nat.minFac_dvd k).trans ⟨r, by simpa [mul_comm] using hk⟩)
  have hrsq : r^2 ≤ k :=
    (Nat.pow_le_pow_left hsmall 2).trans (Nat.minFac_sq_le_self hkpos hcomp)
  have hloss := prime_divisor_loss hr k
  rw [← hk] at hloss
  have hkc : k^3 ≤ (m-m.totient)^3 := Nat.pow_le_pow_left (by omega) 3
  have hlow : m^2 ≤ k^3 := by
    rw [hk, mul_pow]
    calc r^2 * k^2 ≤ k * k^2 := Nat.mul_le_mul_right _ hrsq
         _ = _ := by ring
  have hlt : m.totient^2 < m^2 := Nat.pow_lt_pow_left (Nat.totient_lt m hm) (by decide)
  omega

theorem factorial_gt_square {n : ℕ} (hn : 4 ≤ n) : n^2 < n.factorial := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [Nat.factorial_succ]
    nlinarith [Nat.mul_le_mul_left (n+1) (Nat.succ_le_of_lt ih),
      Nat.mul_le_mul_left (n^2) hn]

theorem factorial_ne_totient_prime_square {n r : ℕ} (hn : 4 ≤ n) (hr : r.Prime) :
    (r*r).totient ≠ n.factorial := by
  rw [← pow_two, Nat.totient_prime_pow_succ hr 1, pow_one]
  intro he
  have hle := hr.dvd_factorial.mp (show r ∣ n.factorial from ⟨_,he.symm⟩)
  have hlt := factorial_gt_square hn
  nlinarith [Nat.mul_le_mul hle hle, Nat.mul_le_mul_left r (Nat.sub_le r 1)]

/-- Bertrand supplies a prime with factorial valuation exactly one. -/
theorem factorial_ne_square {n : ℕ} (hn : 2 ≤ n) (t : ℕ) : n.factorial ≠ t*t := by
  obtain ⟨s,hs,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (n/2) (by omega)
  have hsn : s ≤ n := by omega
  have hns : n < 2*s := by omega
  have hs2 := hs.two_le
  have hsq : n < s^2 := by nlinarith [Nat.mul_le_mul_right s hs2]
  have hlog : Nat.log s n < 2 := (Nat.log_lt_iff_lt_pow hs.one_lt (by omega)).2 hsq
  have hd : n/s = 1 := (Nat.div_eq_of_lt_le (k:=1) (by simpa) (by simpa [two_mul] using hns))
  have hval : n.factorial.factorization s = 1 := by
    rw [Nat.factorization_factorial hs hlog]
    simp [show Finset.Ico 1 2 = {1} by decide, hd]
  intro he
  have ht : t ≠ 0 := by intro h; exact n.factorial_ne_zero (by simpa [h] using he)
  rw [he, Nat.factorization_mul ht ht] at hval
  simp only [Finsupp.coe_add, Pi.add_apply] at hval
  omega

/-- At fixed product, moving a factor into the interval between the old factors can
only decrease the sum. Both possible orientations of the new pair are covered. -/
theorem shifted_pair_le {x y d e : ℕ} (hd : 0 < d) (hx : x ≤ d) (hy : d ≤ y)
    (he : d*e = x*y) : (d+1)*(e+1) ≤ (x+1)*(y+1) := by
  have hs : d+e ≤ x+y := by
    have hc : d*(d+e) ≤ d*(x+y) := by
      zify at *
      nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]
    exact Nat.le_of_mul_le_mul_left hc hd
  nlinarith

/-- The canonical pair is a totient preimage no larger than any shifted-prime pair. -/
theorem canonical_le_sorted {n x y : ℕ} (hn : 2 ≤ n) (hx : (x+1).Prime)
    (hy : (y+1).Prime) (hxy : x ≤ y) (hprod : n.factorial = x*y) :
    (p n).Prime ∧ (q n).Prime ∧ (p n*q n).totient = n.factorial ∧ p n*q n ≤ (x+1)*(y+1) := by
  have hxp := hx.two_le
  have hyp := hy.two_le
  let S := {t : ℕ | t.Prime ∧ n.factorial.sqrt < t ∧ (t-1) ∣ n.factorial ∧
    (n.factorial/(t-1)+1).Prime}
  have hycut : n.factorial.sqrt < y+1 := Nat.sqrt_lt.mpr (by
    nlinarith [Nat.mul_le_mul_right y hxy])
  have hym : y+1 ∈ S := by
    change (y+1).Prime ∧ _ ∧ _ ∧ _
    simp only [Nat.add_sub_cancel]
    exact ⟨hy,hycut,⟨x,by simpa [mul_comm] using hprod⟩,
      by simpa [hprod, Nat.mul_div_cancel _ (show 0 < y by omega)] using hx⟩
  have hp : p n ∈ S := Nat.sInf_mem (show S.Nonempty from ⟨_,hym⟩)
  obtain ⟨hpprime,hcut,hdvd,hqprime⟩ := hp
  change (q n).Prime at hqprime
  have hple : p n ≤ y+1 := Nat.sInf_le hym
  let d := p n - 1
  let e := q n - 1
  have hdp : d+1 = p n := Nat.sub_add_cancel hpprime.one_lt.le
  have heq : e+1 = q n := Nat.sub_add_cancel hqprime.one_lt.le
  have hde : d*e = n.factorial := by
    dsimp [d,e,q]
    exact Nat.mul_div_cancel' hdvd
  have hne : p n ≠ q n := by
    intro h
    exact factorial_ne_square hn d (by simpa [d,e,← h] using hde.symm)
  have hcop := (Nat.coprime_primes hpprime hqprime).mpr hne
  have hxs : x ≤ n.factorial.sqrt := Nat.le_sqrt.mpr (hprod ▸ Nat.mul_le_mul_left _ hxy)
  refine ⟨hpprime,hqprime,?_,?_⟩
  · rw [Nat.totient_mul hcop, Nat.totient_prime hpprime, Nat.totient_prime hqprime]
    exact hde
  · rw [← hdp, ← heq]
    apply shifted_pair_le (by have := hpprime.two_le; omega) (by omega) (by omega)
    exact hde.trans hprod

theorem canonical_le_pair {n x y : ℕ} (hn : 2 ≤ n) (hx : (x+1).Prime)
    (hy : (y+1).Prime) (hprod : n.factorial = x*y) :
    (p n).Prime ∧ (q n).Prime ∧ (p n*q n).totient = n.factorial ∧ p n*q n ≤ (x+1)*(y+1) := by
  rcases le_total x y with h | h
  · exact canonical_le_sorted hn hx hy h hprod
  · simpa only [mul_comm (y+1) (x+1)] using
      canonical_le_sorted hn hy hx h (hprod.trans (Nat.mul_comm x y))

/-- Any two-prime preimage bounds the canonical product, including at the endpoints
where the first eligible prime can be the smaller of the two primes. -/
theorem canonical_le_semiprime {n r s : ℕ} (hn : 4 ≤ n) (hr : r.Prime) (hs : s.Prime)
    (hphi : (r*s).totient = n.factorial) :
    (p n).Prime ∧ (q n).Prime ∧ (p n*q n).totient = n.factorial ∧ p n*q n ≤ r*s := by
  have hrs : r ≠ s := by
    rintro rfl
    exact factorial_ne_totient_prime_square hn hr hphi
  have htot := Nat.totient_mul ((Nat.coprime_primes hr hs).mpr hrs)
  rw [hphi, Nat.totient_prime hr, Nat.totient_prime hs] at htot
  have herr := Nat.sub_add_cancel hr.one_lt.le
  have hess := Nat.sub_add_cancel hs.one_lt.le
  simpa only [herr,hess] using canonical_le_pair (by omega : 2 ≤ n)
    (by rwa [herr] : (r-1+1).Prime) (by rwa [hess] : (s-1+1).Prime) htot

/-- One short preimage, of any shape, certifies the exact conclusion. -/
theorem of_short_inverse {n w : ℕ} (hn : 4 ≤ n) (hcom : ¬ isFactorialPrime n)
    (hw : w.totient = n.factorial) (hshort : (w-n.factorial)^3 ≤ n.factorial^2) :
    (p n).Prime ∧ a n = p n*q n := by
  let T := {m : ℕ | 0 < m ∧ m.totient = n.factorial}
  have hlarge : 1 < n.factorial := by
    have := factorial_gt_square hn
    nlinarith [Nat.mul_le_mul hn hn]
  have hwpos : 0 < w := by
    have := Nat.totient_le w
    omega
  have hwm : w ∈ T := ⟨hwpos,hw⟩
  have hm : a n ∈ T := Nat.sInf_mem (show T.Nonempty from ⟨w,hwm⟩)
  obtain ⟨hmpos,hphi⟩ := hm
  have hle : a n ≤ w := Nat.sInf_le hwm
  have hmgt : 1 < a n := by have := Nat.totient_le (a n); omega
  have hnp : ¬ (a n).Prime := by
    intro ha
    rw [Nat.totient_prime ha] at hphi
    exact hcom (show (n.factorial+1).Prime from (by rwa [show n.factorial+1 = a n by omega]))
  have hs : (a n - (a n).totient)^3 ≤ (a n).totient^2 := by
    rw [hphi]
    exact (Nat.pow_le_pow_left (Nat.sub_le_sub_right hle _) _).trans hshort
  obtain ⟨r,s,hr,hs,he⟩ := short_composite hmgt hnp hs
  obtain ⟨hpp,_,hpq,hmin⟩ := canonical_le_semiprime hn hr hs (he ▸ hphi)
  rw [← he] at hmin
  have hpqpos : 0 < p n*q n := by have := Nat.totient_le (p n*q n); omega
  exact ⟨hpp,le_antisymm (Nat.sInf_le (show p n*q n ∈ T from ⟨hpqpos,hpq⟩)) hmin⟩

theorem of_short_pair {n x y : ℕ} (hn : 4 ≤ n) (hcom : ¬ isFactorialPrime n)
    (hx : (x+1).Prime) (hy : (y+1).Prime) (hprod : n.factorial = x*y)
    (hshort : (x+y+1)^3 ≤ n.factorial^2) : (p n).Prime ∧ a n = p n * q n := by
  have hne : x+1 ≠ y+1 := by
    intro h
    exact factorial_ne_square (n:=n) (by omega) x (by rwa [show y = x by omega] at hprod)
  have hphi := Nat.totient_mul ((Nat.coprime_primes hx hy).mpr hne)
  rw [Nat.totient_prime hx, Nat.totient_prime hy] at hphi
  simp only [Nat.add_sub_cancel] at hphi
  apply of_short_inverse hn hcom (hphi.trans hprod.symm)
  rwa [show (x+1)*(y+1)-n.factorial = x+y+1 by rw [hprod, show (x+1)*(y+1) = x+y+1+x*y by ring, Nat.add_sub_cancel]]

private theorem binary_power {M : Type*} [Monoid M] (a : M) (k : ℕ) :
    npowBinRec k a = a^k := by
  induction k with
  | zero => simp [npowBinRec_zero]
  | succ k ih => rw [npowBinRec_succ, ih, pow_succ]

/-- A divisor of n! has no prime factor above n. This bounds the Lucas certificate checks. -/
theorem shifted_prime_certificate {n d : ℕ} (hd : d ∣ n.factorial) (g : ℕ)
    (h : npowBinRec d (g : ZMod (d+1)) = 1 ∧ ∀ j : Fin (n+1),
      j.val.Prime → j.val ∣ d → npowBinRec (d/j.val) (g : ZMod (d+1)) ≠ 1) :
    (d+1).Prime := by
  apply lucas_primality (d+1) (g : ZMod (d+1))
  · simpa only [Nat.add_sub_cancel, binary_power] using h.1
  · simp only [Nat.add_sub_cancel]
    intro s hs hsd
    have hle := hs.dvd_factorial.mp (hsd.trans hd)
    simpa only [binary_power] using h.2 ⟨s,by omega⟩ hs hsd

/-- Each table row lists one factorial divisor and the Lucas bases for the two shifts. -/
private theorem check_block (b : ℕ) (rows : List (ℕ × ℕ × ℕ)) :
    let cert (n d g : ℕ) := npowBinRec d (g : ZMod (d+1)) = 1 ∧ ∀ j : Fin (n+1),
      j.val.Prime → j.val ∣ d → npowBinRec (d/j.val) (g : ZMod (d+1)) ≠ 1
    (∀ i : Fin rows.length, let n := b+i.val
      let row := rows.get i
      let d := row.1
      let e := n.factorial/d
      n.factorial = d*e ∧ (d+e+1)^3 ≤ n.factorial^2 ∧
        cert n d row.2.1 ∧ cert n e row.2.2) →
    ∀ n, 4 ≤ n → b ≤ n → n < b+rows.length → ¬ isFactorialPrime n →
      (p n).Prime ∧ a n = p n*q n := by
  dsimp only
  intro checked n hn hlo hhi hcom
  let i : Fin rows.length := ⟨n-b,by omega⟩
  have hni : b+i.val = n := by dsimp [i]; omega
  have h := checked i
  rw [hni] at h
  obtain ⟨hprod,hshort,hd,he⟩ := h
  apply of_short_pair hn hcom _ _ hprod hshort
  · exact shifted_prime_certificate ⟨_,hprod⟩ _ hd
  · exact shifted_prime_certificate ⟨_,hprod.trans (Nat.mul_comm _ _)⟩ _ he

private theorem through_four {n : ℕ} (hn : 1 ≤ n) (hn4 : n ≤ 4)
    (h : ¬ isFactorialPrime n) : (p n).Prime ∧ a n = p n*q n := by
  interval_cases n
  · exact (h (by unfold isFactorialPrime; decide +kernel)).elim
  · exact (h (by unfold isFactorialPrime; decide +kernel)).elim
  · exact (h (by unfold isFactorialPrime; decide +kernel)).elim
  · have hp : p 4 = 5 := by
      unfold p
      apply IsLeast.csInf_eq
      have hroot : (Nat.factorial 4).sqrt = 4 := by norm_num
      refine ⟨?_,?_⟩
      · simp only [Set.mem_ofPred_eq, hroot]
        decide +kernel
      · intro t ht
        have hh := ht.2.1
        rw [hroot] at hh
        omega
    rw [a_4, q, hp]
    decide

-- BEGIN checked table
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- Every applicable index in this finite range satisfies the exact statement. -/
theorem finite_cases {n : ℕ} (hn : 1 ≤ n) (ht : n ≤ 100)
    (hcom : ¬ isFactorialPrime n) : (p n).Prime ∧ a n = p n*q n := by
  by_cases small : n ≤ 4
  · exact through_four hn small hcom
  by_cases hb5 : n < 15
  · apply check_block 5 [
      (10,2,2),
      (18,2,6),
      (70,7,5),
      (192,5,2),
      (576,5,3),
      (1800,11,5),
      (6300,10,10),
      (20160,13,7),
      (66528,19,22),
      (285120,34,29)] (by decide +kernel) n (by omega) (by omega) _ hcom
    change n < 15
    exact hb5
  by_cases hb15 : n < 25
  · apply check_block 15 [
      (1143072,5,3),
      (4299750,3,7),
      (18849600,53,29),
      (77616000,13,7),
      (346705920,46,29),
      (1510913250,3,17),
      (7131013120,13,22),
      (33381089280,13,21),
      (160672512000,17,11),
      (783433728000,39,29)] (by decide +kernel) n (by omega) (by omega) _ hcom
    change n < 25
    exact hb15
  by_cases hb25 : n < 35
  · apply check_block 25 [
      (3926707200000,7,13),
      (20080172077056,29,17),
      (104342224896000,19,10),
      (551972322720000,22,38),
      (2972741094400000,6,19),
      (16270845315379200,17,19),
      (90666280925220000,93,13),
      (512776871998390272,5,13),
      (2944853936640000000,39,10),
      (17181282958430062500,2,29)] (by decide +kernel) n (by omega) (by omega) _ hcom
    change n < 35
    exact hb25
  by_cases hb35 : n < 45
  · apply check_block 35 [
      (101618283013632000000,37,41),
      (609895697210557857792,19,37),
      (3709820742318093312000,79,29),
      (22869371294790451200000,13,53),
      (142805840918690157035520,13,19),
      (903278455429618099814400,7,29),
      (5783814386039595309465600,43,23),
      (37482398332777484255232000,86,31),
      (764104057375178520000,19,17),
      (42723769244356561600512,10,53)] (by decide +kernel) n (by omega) (by omega) _ hcom
    change n < 45
    exact hb35
  by_cases hb45 : n < 55
  · apply check_block 45 [
      (3893113183244313600000,7,109),
      (50106095908932984921000,17,14),
      (189541479322800000000,39,43),
      (2597729000854561879864859688960,7,37),
      (1539169025801430676004352000000,59,37),
      (303813837503242040246272000000,15,46),
      (16411973632751336218951680000,26,106),
      (7861956572803437232128000,53,57),
      (1524654817230936961858928640000000,67,55),
      (169656255585880533550080000,58,31)] (by decide +kernel) n (by omega) (by omega) _ hcom
    change n < 55
    exact hb45
  by_cases hb55 : n < 65
  · apply check_block 55 [
      (1313983112157174415097374045312500000,37,41),
      (6768284713728022833161958144000,19,22),
      (93244310472686731335065088,19,124),
      (82450132900781835104341096552801920,76,59),
      (839801546391130154551387472805000000000,109,97),
      (529240748236231439067339423744000,67,31),
      (42602650923518317477211132812500000,22,15),
      (4122782147814463019175950472109704806400,67,22),
      (54203410915568659444895507812500,18,34),
      (309600951410348708583330396040320,11,26)] (by decide +kernel) n (by omega) (by omega) _ hcom
    change n < 65
    exact hb55
  by_cases hb65 : n < 75
  · apply check_block 65 [
      (344010805606513229987864490456498831360,29,37),
      (387544816972101858141868389264080566406250,2,33),
      (208275247820950321627556709268500,10,62),
      (8609384255099416318486010742187500,14,83),
      (918320505900180929912416770084666686586652459008,59,34),
      (76910395626172578989968189666308497866752,5,23),
      (4571758916701034445431537802157902435817881600,67,73),
      (117616834445792761811886814603736448638976,5,53),
      (154074495309636155522059540889662500000,87,34),
      (50345467858119213595194380727910500476160000000000,46,31)] (by decide +kernel) n (by omega) (by omega) _ hcom
    change n < 75
    exact hb65
  by_cases hb75 : n < 85
  · apply check_block 75 [
      (1206147432664890889738022466605551383000000,28,86),
      (480045846645036139368156741274485915648000000000000000,28,79),
      (202032014271077988875554747040105158498320384000000000000,13,127),
      (193622521254877424060720328387298590720000000000000000,106,79),
      (587532600594327203850360908235040358400000000,7,101),
      (75056926125347473501647472540898754452717731933593750000,58,89),
      (578869097743729400265451738441641817748275200000000000000,57,58),
      (348074768394469918517074957172736000000000000000000,11,87),
      (14825115251112588089061186604010373541615632384000,46,57),
      (1554277513584905047303824094715431211297587500857425920,37,51)] (by decide +kernel) n (by omega) (by omega) _ hcom
    change n < 85
    exact hb75
  by_cases hb85 : n < 95
  · apply check_block 85 [
      (1527357492575202261694107233905563210224762880000000000000000,11,86),
      (1342467016994164734486013227211826872706416424672821248000,31,95),
      (17537574049142402535549469281354427014807073583308057700399579136,5,67),
      (16505522178150712785478150938147811839122331402240000000000000000,31,17),
      (30358870659756957731128629267450655184550191614049438505369600000,58,78),
      (59798266355036524914811717660921469687244007969811524200439453125000,107,59),
      (2131060467874266836505138121000202985599735210490089472,20,67),
      (4473238091977534332478673425810129371373261900616155791360000000000000,34,62),
      (5455908863521981594471532160239408990781017215016278068949942272,20,118),
      (461110065056072003882686490986386520839383002252800000,82,38)] (by decide +kernel) n (by omega) (by omega) _ hcom
    change n < 95
    exact hb85
  by_cases hb95 : n < 101
  · apply check_block 95 [
      (474610734216147334165526712374300534897190088212480000000000,107,71),
      (9272956123726296461710005907050425806925064928702164062400000000000000,59,38),
      (5081239764295501212701465712934633788931090666277818500000000000,17,97),
      (180371481948414522203317466291707478100172104126937190223965087292456960000,79,41),
      (19538984672959088669890213110420126654577686793254866300751052800000000000,59,71),
      (240414329120437883813955593492854175127347237227295371460715290296320000000,29,38)] (by decide +kernel) n (by omega) (by omega) _ hcom
    change n < 101
    exact hb95
  omega

/-- Existence with no size or minimality condition on the two shifted primes. -/
def H1 : Prop := ∀ n : ℕ, 100 < n → ¬ isFactorialPrime n →
  ∃ x y : ℕ, n.factorial = x*y ∧ (x+1).Prime ∧ (y+1).Prime

/-- Local improvement. Given a shifted-prime split and an explicitly smaller inverse
with composite cofactor after removing its least prime, find any split of smaller sum.
Only inverses beyond the cubic range require an improvement. -/
def H2 : Prop := ∀ n : ℕ, 100 < n → ¬ isFactorialPrime n → ∀ x y m : ℕ,
  n.factorial = x*y → (x+1).Prime → (y+1).Prime →
  m.totient = n.factorial → ¬ (m/m.minFac).Prime →
  n.factorial^2 < (m-n.factorial)^3 → m < (x+1)*(y+1) →
  ∃ u v : ℕ, n.factorial = u*v ∧ (u+1).Prime ∧ (v+1).Prime ∧ u+v < x+y

theorem main : H1 → H2 → type_of% @OeisA55487.conjecture := by
  intro seed improve n hn hcom
  by_cases hfin : n ≤ 100
  · exact finite_cases hn hfin hcom
  obtain ⟨x,y,hprod,hx,hy⟩ := seed n (by omega) hcom
  obtain ⟨hp,hq,hphi,_⟩ := canonical_le_pair (by omega : 2 ≤ n) hx hy hprod
  have hn4 : 4 ≤ n := by omega
  have hpos := Nat.mul_pos hp.pos hq.pos
  let T := {m : ℕ | 0 < m ∧ m.totient = n.factorial}
  have hpqmem : p n*q n ∈ T := ⟨hpos,hphi⟩
  have hm : a n ∈ T := Nat.sInf_mem (show T.Nonempty from ⟨_,hpqmem⟩)
  obtain ⟨_,hmphi⟩ := hm
  have hle : a n ≤ p n*q n := Nat.sInf_le hpqmem
  refine ⟨hp,?_⟩
  by_contra hne
  have hlt := lt_of_le_of_ne hle hne
  by_cases hshort : (a n - n.factorial)^3 ≤ n.factorial^2
  · exact hne (of_short_inverse hn4 hcom hmphi hshort).2
  have hmgt : 1 < a n := by
    have := factorial_gt_square hn4
    have := Nat.mul_le_mul hn4 hn4
    have := Nat.totient_le (a n)
    nlinarith
  have hk : ¬ (a n/(a n).minFac).Prime := by
    intro hk
    have hr := Nat.minFac_prime (n := a n) hmgt.ne'
    have he := Nat.mul_div_cancel' (Nat.minFac_dvd (a n))
    have hcan := canonical_le_semiprime hn4 hr hk (by rwa [he])
    exact hlt.not_ge (by simpa only [he] using hcan.2.2.2)
  have hdistinct : p n ≠ q n := by
    intro he
    exact factorial_ne_totient_prime_square hn4 hp (by rwa [← he] at hphi)
  have he := Nat.totient_mul ((Nat.coprime_primes hp hq).mpr hdistinct)
  rw [hphi, Nat.totient_prime hp, Nat.totient_prime hq] at he
  have hpred := Nat.sub_add_cancel hp.one_lt.le
  have hqred := Nat.sub_add_cancel hq.one_lt.le
  obtain ⟨u,v,huv,hu,hv,hbetter⟩ := improve n (by omega) hcom
    (p n-1) (q n-1) (a n) he (by rwa [hpred]) (by rwa [hqred])
    hmphi hk (by omega) (by rwa [hpred,hqred])
  have hmin := (canonical_le_pair (by omega : 2 ≤ n) hu hv huv).2.2.2
  rw [← hpred, ← hqred] at hmin
  nlinarith

end OMA.R_OeisA55487_conjecture_R1

