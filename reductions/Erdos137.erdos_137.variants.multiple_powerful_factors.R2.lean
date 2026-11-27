import FormalConjectures.ErdosProblems.«137»

/-! # A fixed-window reduction for Erdős problem 137

Write d(x) for the product of the primes occurring exactly once in x. A
uniform positive-power lower bound for d(x) somewhere in every fixed-length
window, together with the polynomial-height case, implies the full conjecture.
The proof bounds the contribution of all primes at most n to a length-n block
by n^(2n), uniformly in the starting point. Credit: @FelixDou.

There is also an informal consequence for abc triples. If H2 fails, then for
every positive h,e one can take arbitrarily large t with d(x)^e ≤ t
throughout (t,t+h]. Let h,e tend to infinity and choose t ≥ h². For each y with y±5 in the block, set
A=(y-5)(y-1)^3(y+4)^2, B=432y, C=(y+5)(y+1)^3(y-4)^2. Expansion gives
A+B=C. Since A(0)=80, gcd(A,B) ≤ 432·80. Divide by this common factor.
The radical of the resulting triple is at most six times the product of
rad(y+s) for s=0,±1,±4,±5. Prime by prime, rad(x)^2 ≤ x·d(x). Thus the
logarithm of the radical is at most (7/2+o(1))log t, uniformly in y, and
the logarithm of the reduced C is (6+o(1))log t. Failure would give
arbitrarily long consecutive runs of centers of quality above any fixed
q < 12/7. The Lean proof below uses the fixed-window hypothesis directly. -/

namespace OMA.R_Erdos137_erdos_137_variants_multiple_powerful_factors_R2

/-- The bounded-height problem, for each fixed polynomial height. This follows
from Theorem 3.1 of S. Venkat, Ramanujan primes and primes of exponent one
in products of consecutive integers (2026). -/
def H1 : Prop :=
  ∀ D k : ℕ, ∀ᶠ n in Filter.atTop, ∀ m : ℕ, 0 < m → m ≤ n ^ D →
    ∃ P : Finset ℕ, P.card = k ∧ ∀ p ∈ P, p.Prime ∧
      p ∣ (∏ x ∈ Finset.Ioc m (m + n), x) ∧ ¬ p ^ 2 ∣ (∏ x ∈ Finset.Ioc m (m + n), x)

/-- A fixed window contains an integer for which the product of the primes
occurring exactly once exceeds a fixed positive power of the starting point. -/
def H2 : Prop :=
  ∃ h e : ℕ, 0 < h ∧ 0 < e ∧ ∀ᶠ t in Filter.atTop,
    ∃ x ∈ Finset.Ioc t (t + h), t < (∏ p ∈ x.primeFactors.filter (fun p => ¬ p ^ 2 ∣ x), p) ^ e

lemma multiples_bound {m n p : ℕ} (hp : 0 < p) (hle : p ≤ n) :
    ((Finset.Ioc m (m + n)).filter (fun x => p ∣ x)).card ≤
      2 * ((Finset.Ioc 0 n).filter (fun x => p ∣ x)).card := by
  have hsub : ((Finset.Ioc 0 m).filter (fun x => p ∣ x)) ⊆
      ((Finset.Ioc 0 (m + n)).filter (fun x => p ∣ x)) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hx ⊢
    omega
  have hdiff : ((Finset.Ioc m (m + n)).filter (fun x => p ∣ x)) =
      ((Finset.Ioc 0 (m + n)).filter (fun x => p ∣ x)) \
        ((Finset.Ioc 0 m).filter (fun x => p ∣ x)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff]
    omega
  rw [hdiff, Finset.card_sdiff_of_subset hsub]
  simp only [Nat.Ioc_filter_dvd_card_eq_div]
  have hone : 0 < n / p := Nat.div_pos hle hp
  rw [Nat.add_div hp]
  split <;> omega

lemma count_by_prime (s P : Finset ℕ) :
    (∏ x ∈ s, ∏ p ∈ P.filter (fun p => p ∣ x), p) =
      ∏ p ∈ P, p ^ (s.filter (fun x => p ∣ x)).card := by
  simp only [Finset.prod_filter]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro p hp
  rw [← Finset.prod_filter, Finset.prod_const]

lemma positive_prime_product (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (x : ℕ) :
    0 < ∏ p ∈ P.filter (fun p => p ∣ x), p := by
  exact Finset.prod_pos (fun p hp => (hP p (Finset.mem_filter.mp hp).1).pos)

/-- Uniform in the offset and in the chosen subset of interval terms. -/
lemma small_prime_budget {m n : ℕ} (s : Finset ℕ) (hs : s ⊆ Finset.Ioc m (m + n)) :
    let P := (Finset.Ioc 0 n).filter Nat.Prime
    (∏ x ∈ s, ∏ p ∈ P.filter (fun p => p ∣ x), p) ≤ n ^ (2 * n) := by
  classical
  let P := (Finset.Ioc 0 n).filter Nat.Prime
  let small := fun x : ℕ => ∏ p ∈ P.filter (fun p => p ∣ x), p
  let base := Finset.Ioc 0 n
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime := (Finset.mem_filter.mp hp).2
  have hbase (x : ℕ) (hx : x ∈ base) : small x ≤ n := by
    have hx' := Finset.mem_Ioc.mp hx
    have hsub : P.filter (fun p => p ∣ x) ⊆ x.primeFactors := by
      intro p hp
      obtain ⟨hp, hpx⟩ := Finset.mem_filter.mp hp
      exact Nat.mem_primeFactors.mpr ⟨hP p hp, hpx, hx'.1.ne'⟩
    have hd := Finset.prod_dvd_prod_of_subset (P.filter (fun p => p ∣ x)) x.primeFactors
      (fun z : ℕ => z) hsub
    exact (Nat.le_of_dvd hx'.1 (hd.trans (Nat.prod_primeFactors_dvd x))).trans hx'.2
  have hb : (∏ x ∈ base, small x) ≤ n ^ n := by
    calc
      (∏ x ∈ base, small x) ≤ ∏ _x ∈ base, n := Finset.prod_le_prod' hbase
      _ = _ := by simp [base]
  change (∏ x ∈ s, small x) ≤ _
  calc
    (∏ x ∈ s, small x) ≤ ∏ x ∈ Finset.Ioc m (m + n), small x :=
      Finset.prod_le_prod_of_subset_of_one_le' hs (fun x _ _ => positive_prime_product P hP x)
    _ = ∏ p ∈ P, p ^ ((Finset.Ioc m (m + n)).filter (fun x => p ∣ x)).card :=
      count_by_prime _ _
    _ ≤ ∏ p ∈ P, (p ^ (base.filter (fun x => p ∣ x)).card) ^ 2 := by
      apply Finset.prod_le_prod'
      intro p hp
      rw [← pow_mul, Nat.mul_comm _ 2]
      apply Nat.pow_le_pow_right (hP p hp).pos
      exact multiples_bound (hP p hp).pos (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
    _ = (∏ x ∈ base, small x) ^ 2 := by
      rw [Finset.prod_pow]
      exact congrArg (fun z : ℕ => z ^ 2) (count_by_prime base P).symm
    _ ≤ (n ^ n) ^ 2 := Nat.pow_le_pow_left hb 2
    _ = _ := by rw [← pow_mul, Nat.mul_comm]

/-- Many disjoint fixed-length windows force a prime above the full interval length. -/
lemma chunk_witness {m n t r h e L : ℕ} (hn : 1 < n) (hleft : m ≤ t)
    (hright : t + r * h ≤ m + n) (hcount : 2 * n < L * r) (hheight : (n ^ L) ^ e ≤ t)
    (hw : ∀ u ≥ t, ∃ x ∈ Finset.Ioc u (u + h),
      u < (∏ p ∈ x.primeFactors.filter (fun p => ¬ p ^ 2 ∣ x), p) ^ e) :
    ∃ x ∈ Finset.Ioc t (t + r * h), ∃ p, n < p ∧ p.Prime ∧ p ∣ x ∧ ¬ p ^ 2 ∣ x := by
  classical
  let P := (Finset.Ioc 0 n).filter Nat.Prime
  let small := fun x : ℕ => ∏ p ∈ P.filter (fun p => p ∣ x), p
  let simple := fun x : ℕ => x.primeFactors.filter (fun p => ¬ p ^ 2 ∣ x)
  have windows (i : Fin r) := hw (t + i.val * h) (by omega)
  choose x hx hsize using windows
  have hmem (i : Fin r) : x i ∈ Finset.Ioc t (t + r * h) := by
    have hi := Finset.mem_Ioc.mp (hx i)
    have hend := Nat.mul_le_mul_right h (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at hend
    exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
  have hmono : StrictMono x := by
    intro i j hij
    have hi := Finset.mem_Ioc.mp (hx i)
    have hj := Finset.mem_Ioc.mp (hx j)
    have hstep := Nat.mul_le_mul_right h (Nat.succ_le_of_lt (show i.val < j.val from hij))
    rw [Nat.succ_mul] at hstep
    omega
  by_contra hnone
  have hsmall (i : Fin r) : n ^ L ≤ small (x i) := by
    have hsub : simple (x i) ⊆ P.filter (fun p => p ∣ x i) := by
      intro p hp
      obtain ⟨hpf, hs⟩ := Finset.mem_filter.mp hp
      obtain ⟨hprime, hdiv, _⟩ := Nat.mem_primeFactors.mp hpf
      have hle : p ≤ n := le_of_not_gt fun h => hnone ⟨x i, hmem i, p, h, hprime, hdiv, hs⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hprime.pos, hle⟩,
        hprime⟩, hdiv⟩
    have hpow : (n ^ L) ^ e < (∏ p ∈ simple (x i), p) ^ e :=
      lt_of_le_of_lt (hheight.trans (Nat.le_add_right _ _)) (hsize i)
    exact (lt_of_pow_lt_pow_left' e hpow).le.trans
      (Finset.prod_le_prod_of_subset_of_one_le' hsub (fun p hp _ =>
        (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.pos))
  let s := Finset.univ.image x
  have hs : s ⊆ Finset.Ioc m (m + n) := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    have hi := Finset.mem_Ioc.mp (hmem i)
    exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
  have hprod : n ^ (L * r) ≤ n ^ (2 * n) := calc
    n ^ (L * r) = ∏ _y ∈ s, n ^ L := by
      rw [pow_mul, Finset.prod_const]
      simp [s, Finset.card_image_of_injective _ hmono.injective]
    _ ≤ ∏ y ∈ s, small y := by
      apply Finset.prod_le_prod'
      intro y hy
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
      exact hsmall i
    _ ≤ _ := small_prime_budget s hs
  exact (Nat.pow_lt_pow_right hn hcount).not_ge hprod

lemma unique_multiple {m n p x y : ℕ} (hsize : n ≤ p ∨ m + n < 2 * p)
    (hx : x ∈ Finset.Ioc m (m + n)) (hy : y ∈ Finset.Ioc m (m + n))
    (hpx : p ∣ x) (hpy : p ∣ y) : x = y := by
  have impossible (u v : ℕ) (hu : m < u) (hv : v ≤ m + n) (huv : u < v)
      (hpu : p ∣ u) (hpv : p ∣ v) : False := by
    have hgap := Nat.le_of_dvd (Nat.sub_pos_of_lt huv) (Nat.dvd_sub hpv hpu)
    have hlo := Nat.le_of_dvd (by omega : 0 < u) hpu
    omega
  obtain ⟨hxl, hxr⟩ := Finset.mem_Ioc.mp hx
  obtain ⟨hyl, hyr⟩ := Finset.mem_Ioc.mp hy
  rcases lt_trichotomy x y with h | h | h
  · exact (impossible x y hxl hyr h hpx hpy).elim
  · exact h
  · exact (impossible y x hyl hxr h hpy hpx).elim

lemma transfer_factor {m n p x : ℕ} (hsize : n ≤ p ∨ m + n < 2 * p)
    (hx : x ∈ Finset.Ioc m (m + n)) (hp : p.Prime) (hd : p ∣ x) (hsq : ¬ p ^ 2 ∣ x) :
    p ∣ (∏ y ∈ Finset.Ioc m (m + n), y) ∧ ¬ p ^ 2 ∣ (∏ y ∈ Finset.Ioc m (m + n), y) := by
  let s := Finset.Ioc m (m + n)
  have hrest : ¬ p ∣ ∏ y ∈ s.erase x, y := by
    intro h
    obtain ⟨y, hy, hpy⟩ := (hp.prime.dvd_finsetProd_iff (fun z : ℕ => z)).mp h
    obtain ⟨hne, hym⟩ := Finset.mem_erase.mp hy
    exact hne (unique_multiple hsize hym hx hpy hd)
  have hcop := (hp.coprime_iff_not_dvd.mpr hrest).pow_left 2
  change p ∣ (∏ y ∈ s, y) ∧ ¬ p ^ 2 ∣ (∏ y ∈ s, y)
  rw [← Finset.mul_prod_erase s (fun y : ℕ => y) hx]
  exact ⟨dvd_mul_of_dvd_left hd _, fun h => hsq (hcop.dvd_of_dvd_mul_right h)⟩

theorem main : H1 → H2 → type_of% @Erdos137.erdos_137.variants.multiple_powerful_factors := by
  classical
  intro hlow hwindow k
  obtain ⟨h, e, hh, he, hw⟩ := hwindow
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hw
  let B := (k + 1) * h
  let L := 4 * B
  let D := L * e
  have hB : 0 < B := Nat.mul_pos (by omega) hh
  have hD : 0 < D := Nat.mul_pos (Nat.mul_pos (by decide) hB) he
  obtain ⟨F, hF⟩ := Filter.eventually_atTop.mp (hlow D k)
  apply Filter.eventually_atTop.mpr
  refine ⟨max (max F T) (max B 2), ?_⟩
  intro n hn m hm
  have hf : F ≤ n := by omega
  have ht : T ≤ n := by omega
  have hb : B ≤ n := by omega
  have hn2 : 1 < n := by omega
  by_cases hbounded : m ≤ n ^ D
  · exact hF n hf m hm hbounded
  have hmT : T ≤ m := ht.trans ((Nat.le_self_pow hD.ne' n).trans (by omega))
  let r := n / B
  let w := r * h
  have hr : 0 < r := Nat.div_pos hb hB
  have hpack : k * w ≤ n := calc
    k * w ≤ (k + 1) * w := Nat.mul_le_mul_right _ (by omega)
    _ = r * B := by dsimp [w, B]; ring
    _ ≤ n := Nat.div_mul_le_self _ _
  have hcount : 2 * n < L * r := by
    have hround : n < B * (r + 1) := Nat.lt_mul_div_succ n hB
    have hbr := Nat.mul_le_mul_left B (show r + 1 ≤ 2 * r by omega)
    dsimp [L]
    nlinarith only [hround, hbr]
  have chunks (i : Fin k) := chunk_witness (m := m) (n := n) (t := m + i.val * w)
    (r := r) (h := h) (e := e) (L := L) hn2 (by omega) (by
      have hi := (Nat.mul_le_mul_right w (Nat.succ_le_of_lt i.isLt)).trans hpack
      rw [Nat.succ_mul] at hi
      change m + i.val * w + w ≤ m + n
      omega) hcount (by rw [← pow_mul]; change n ^ D ≤ m + i.val * w; omega)
    (fun u hu => hT u (by omega))
  choose x hx p hbig hprime hd hsq using chunks
  have hmem (i : Fin k) : x i ∈ Finset.Ioc m (m + n) := by
    have hrange := Finset.mem_Ioc.mp (hx i)
    change m + i.val * w < x i ∧ x i ≤ m + i.val * w + w at hrange
    have hi := (Nat.mul_le_mul_right w (Nat.succ_le_of_lt i.isLt)).trans hpack
    rw [Nat.succ_mul] at hi
    exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
  have hmono : StrictMono x := by
    intro i j hij
    have hi := (Finset.mem_Ioc.mp (hx i)).2
    change x i ≤ m + i.val * w + w at hi
    have hj := (Finset.mem_Ioc.mp (hx j)).1
    have hstep := Nat.mul_le_mul_right w (Nat.succ_le_of_lt (show i.val < j.val from hij))
    rw [Nat.succ_mul] at hstep
    omega
  have hinj : Function.Injective p := by
    intro i j hij
    exact hmono.injective (unique_multiple (Or.inl (hbig i).le) (hmem i) (hmem j) (hd i) (hij ▸ hd j))
  refine ⟨Finset.univ.image p, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨hprime i, transfer_factor (Or.inl (hbig i).le) (hmem i) (hprime i) (hd i) (hsq i)⟩

end OMA.R_Erdos137_erdos_137_variants_multiple_powerful_factors_R2
