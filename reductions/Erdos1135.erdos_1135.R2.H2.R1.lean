import OMAReductions.R_Erdos1135_erdos_1135_R2

/-!
# A finite cycle search for each reduced odd count

Write the primitive period k and its odd count s as k = p d and s = q d
with p and q coprime. A possible nontrivial cycle has q ≥ 1636 and its
minimum n satisfies n > 330911 and n ≡ 3 (mod 4).

H1 bounds the relative gap between powers of two and three by C(q).
It has a separate proof using the LABO-COLLATZ two-logarithm estimate.
In H2 both the seed and the repetition count d have explicit bounds in q.
The reduced odd count q itself is unbounded.
-/

namespace OMA.R_Erdos1135_erdos_1135_R2_H2_R1

open Finset Function

def H1 : Prop :=
  let C := fun s : ℕ => min (2 ^ (s / 13)) (if s < 10 ^ 100 then 10 ^ 101 + 1
    else 2 ^ (2 * 10 ^ 12 * (Nat.log 2 s + 1) ^ 5) + 1)
  ∀ k s : ℕ, 94 ≤ s → 3 ^ s < 2 ^ k → 2 ^ k ≤ (2 ^ k - 3 ^ s) * C s

/-- At each reduced odd count q, all possible primitive periods and seeds
lie in explicit finite ranges. -/
def H2 : Prop :=
  let C := fun q : ℕ => min (2 ^ (q / 13)) (if q < 10 ^ 100 then 10 ^ 101 + 1
    else 2 ^ (2 * 10 ^ 12 * (Nat.log 2 q + 1) ^ 5) + 1)
  let T := fun n : ℕ => if n % 2 = 0 then n / 2 else (3 * n + 1) / 2
  ∀ q p d n : ℕ, 1636 ≤ q → p.Coprime q → 0 < p → p < 2 * q →
    330911 < n → n % 4 = 3 → 3 * n + 1 ≤ q * C q →
    0 < d → d < C q * (Nat.log 2 (1 + 2 * q * C q) / 5 + 1) →
    3 ^ q < 2 ^ p → (3 * n + 1) * (2 ^ p - 3 ^ q) ≤ q * 2 ^ p →
    ((range (p*d)).filter fun i => T^[i] n % 2 = 1).card = q*d →
    (∀ i < p*d, n ≤ T^[i] n) → T^[p*d] n ≠ n

lemma decode {T : ℕ → ℕ} (hT : ∀ x, T x = if x % 2 = 0 then x / 2 else (3 * x + 1) / 2)
    (F : ℕ → ℕ) (S : Finset ℕ) (n : ℕ) (hz : F 0 = n)
    (hF : ∀ j, F (j + 1) = if j ∈ S then 3 * F j + 2 ^ j else F j)
    {k y : ℕ} (he : F k = 2 ^ k * y) : T^[k] n = y := by
  induction k generalizing y with
  | zero => simpa [hz] using he
  | succ k ih =>
    rw [hF, pow_succ] at he
    by_cases ho : k ∈ S
    · rw [if_pos ho] at he
      have hdiv : 2 ^ k ∣ 3 * F k + 2 ^ k := ⟨2 * y, by rw [he]; ring⟩
      have h3 : 2 ^ k ∣ 3 * F k := (Nat.dvd_add_iff_left (dvd_refl (2 ^ k))).mpr hdiv
      have hd := ((by decide : Nat.Coprime 2 3).pow_left k).dvd_of_dvd_mul_left h3
      obtain ⟨z, hz'⟩ := hd
      have eq : 2 ^ k * (3 * z + 1) = 2 ^ k * (2 * y) := by
        rw [hz'] at he; nlinarith only [he]
      have hes := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ k) eq
      rw [iterate_succ_apply', ih hz', hT, if_neg (by omega)]
      omega
    · rw [if_neg ho] at he
      have hh : F k = 2 ^ k * (2 * y) := by rw [he]; ring
      rw [iterate_succ_apply', ih hh, hT, if_pos (by omega)]
      omega

/-- Read an integer solution of the affine mask equation as an actual orbit. -/
lemma mask_returns {T : ℕ → ℕ} (hT : ∀ x, T x = if x % 2 = 0 then x / 2 else (3 * x + 1) / 2)
    (k n : ℕ) (S : Finset ℕ) (hS : S ⊆ range k)
    (he : 2 ^ k * n = 3 ^ S.card * n + ∑ i ∈ S, 2 ^ i * 3 ^ (S.filter fun j => i < j).card) :
    T^[k] n = n := by
  let A := fun j => (range j).filter (· ∈ S)
  let F := fun j => 3 ^ (A j).card * n + ∑ i ∈ A j, 2 ^ i * 3 ^ ((A j).filter fun d => i < d).card
  have hlt (j i : ℕ) (hi : i ∈ A j) : i < j := mem_range.mp (mem_filter.mp hi).1
  have hA : A k = S := by
    ext i; exact ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨hS h, h⟩⟩
  apply decode hT F S n (by simp [F, A]) _ (by simpa only [F, hA] using he.symm)
  intro j
  have hsucc : A (j + 1) = if j ∈ S then insert j (A j) else A j := by
    simp only [A, range_add_one, filter_insert]
  simp only [F, hsucc]
  by_cases hj : j ∈ S
  · rw [if_pos hj, if_pos hj]
    have hn : j ∉ A j := fun h => (lt_irrefl j) (hlt j j h)
    have hlast : ((insert j (A j)).filter fun i => j < i) = ∅ := by
      ext i; simp only [mem_filter, mem_insert, notMem_empty, iff_false, not_and]
      rintro (rfl | hi) h
      · omega
      · exact (lt_asymm h) (hlt j i hi)
    have ht (i : ℕ) (hi : i ∈ A j) : 2 ^ i * 3 ^ (((insert j (A j)).filter fun d => i < d).card) =
        3 * (2 ^ i * 3 ^ (((A j).filter fun d => i < d).card)) := by
      rw [filter_insert, if_pos (hlt j i hi), card_insert_of_notMem, pow_succ]
      · ring
      · exact fun h => hn (mem_filter.mp h).1
    rw [card_insert_of_notMem hn, pow_succ, sum_insert hn, hlast, sum_congr rfl ht, ← Finset.mul_sum]
    simp only [card_empty, pow_zero, mul_one]; ring
  · simp [hj]

/-- A denominator-free form of the elementary bound
1 − (b/(b+1))^s ≤ s/(b+1). -/
lemma tangent (b s : ℕ) :
    (b + 1) * (b + 1) ^ s ≤ (b + 1) * b ^ s + s * (b + 1) ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hY := Nat.mul_le_mul_left (b + 1) (Nat.pow_le_pow_left (show b ≤ b + 1 by omega) s)
    have hi := Nat.mul_le_mul_right (b + 1) ih
    simp only [pow_succ]
    nlinarith only [hi, hY]

lemma minimum_bound {A n s C : ℕ} (hc : 3 ^ s < A)
    (h : A * n ^ s ≤ (3 * n + 1) ^ s)
    (hg : A ≤ (A - 3 ^ s) * C) :
    (3 * n + 1) * (A - 3 ^ s) ≤ s * A ∧ 3 * n + 1 ≤ s * C := by
  let b := 3 * n
  let B := b + 1
  have h1 : A * b ^ s ≤ 3 ^ s * B ^ s := by
    dsimp [b, B]; rw [mul_pow]; nlinarith only [Nat.mul_le_mul_left (3 ^ s) h]
  have ht := Nat.mul_le_mul_left A (tangent b s)
  change A * (B * B ^ s) ≤ A * (B * b ^ s + s * B ^ s) at ht
  have ha := Nat.mul_le_mul_left B h1
  have he : A = (A - 3 ^ s) + 3 ^ s := by omega
  have h2 : (B * (A - 3 ^ s)) * B ^ s ≤ (s * A) * B ^ s := by
    nlinarith only [ht, ha, congrArg (fun x : ℕ => (B * x) * B ^ s) he]
  have hBp : 0 < B := by dsimp [B]; omega
  have h3 := le_of_mul_le_mul_right h2 (pow_pos hBp s)
  have h4 := h3.trans (Nat.mul_le_mul_left s hg)
  rw [Nat.mul_comm B, ← Nat.mul_assoc, Nat.mul_comm s (A - 3 ^ s), Nat.mul_assoc] at h4
  exact ⟨h3, le_of_mul_le_mul_left h4 (by omega : 0 < A - 3 ^ s)⟩


lemma small_converges (T : ℕ → ℕ) (hT : T = fun x => if x % 2 = 0 then x / 2 else (3 * x + 1) / 2)
    (n : ℕ) (hn : 0 < n) (hB : n ≤ 2048) : ∃ j, T^[j] n = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases he : n = 1
    · exact ⟨0, he⟩
    let r : Fin 2047 := ⟨n - 2, by omega⟩
    obtain ⟨t, ht⟩ := OMA.R_Erdos1135_erdos_1135_R2.small_descent T hT r
    have hr : r.val + 2 = n := by dsimp [r]; omega
    rw [hr] at ht
    obtain ⟨j, hj⟩ := ih (T^[t.val] n) ht
      (OMA.R_Erdos1135_erdos_1135_R2.shortcut_positive (T := T) (fun x => congrFun hT x) hn t) (by omega)
    exact ⟨j + t.val, by rw [iterate_add_apply, hj]⟩

lemma no_small_phase (T : ℕ → ℕ) (hT : T = fun x => if x % 2 = 0 then x / 2 else (3 * x + 1) / 2)
    (n k : ℕ) (hn : 2 < n) (hk : 0 < k) (hfix : T^[k] n = n) (i : ℕ) : 2048 < T^[i] n := by
  by_contra! hsmall
  obtain ⟨j, hj⟩ := small_converges T hT (T^[i] n)
    (OMA.R_Erdos1135_erdos_1135_R2.shortcut_positive (T := T) (fun x => congrFun hT x) (by omega) i) hsmall
  let t := j + i
  have hhit : T^[t] n = 1 := by rw [show t = j + i from rfl, iterate_add_apply, hj]
  have hbounded (d : ℕ) : T^[d] 1 ≤ 2 := by
    induction d with
    | zero => change (1:ℕ) ≤ 2; decide
    | succ d ih => rw [iterate_succ_apply', congrFun hT (T^[d] 1)]; split <;> omega
  have hmult (q : ℕ) : T^[q * k] n = n := by
    induction q with
    | zero => simp
    | succ q ih => rw [Nat.succ_mul, iterate_add_apply, hfix, ih]
  have H := hbounded (t * k - t)
  rw [← hhit, ← iterate_add_apply, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ hk), hmult] at H
  omega


set_option maxRecDepth 20000 in
set_option maxHeartbeats 6400000 in
lemma minimum_above_330911 (T : ℕ → ℕ)
    (hT : T = fun x => if x % 2 = 0 then x / 2 else (3 * x + 1) / 2)
    (y : ℕ) (hfour : y % 4 = 3) (hl : ∀ j, y ≤ T^[j] y) : 330911 < y := by
  let hit (n : ℕ) := Nat.rec (motive := fun _ => ℕ → Bool) (fun x => decide (x < n))
    (fun _ f x => decide (x < n) || f (T x))
  have witnessed (n t x : ℕ) (h : hit n t x = true) : ∃ j, T^[j] x < n := by
    induction t generalizing x with
    | zero => exact ⟨0, of_decide_eq_true h⟩
    | succ t ih =>
      change (decide (x < n) || hit n t (T x)) = true at h
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with hh | hh
      · exact ⟨0, hh⟩
      · obtain ⟨j, hj⟩ := ih (T x) hh
        exact ⟨j + 1, by rw [iterate_succ_apply]; exact hj⟩
  have checked : ∀ a : Fin 383, ∀ b : Fin 216,
      let z := 4 * (a.val * 216 + b.val) + 3
      hit z 164 z = true := by
    subst T
    dsimp only [hit]
    decide +kernel
  by_contra! hy
  let a : Fin 383 := ⟨y / 4 / 216, by omega⟩
  let b : Fin 216 := ⟨y / 4 % 216, by omega⟩
  have hc := checked a b
  have hh : 4 * (a.val * 216 + b.val) + 3 = y := by dsimp [a,b]; omega
  dsimp only at hc
  rw [hh] at hc
  obtain ⟨j, hj⟩ := witnessed y 164 y hc
  exact (not_lt_of_ge (hl j)) hj

lemma minimum_above_100000 (T : ℕ → ℕ)
    (hT : T = fun x => if x % 2 = 0 then x / 2 else (3 * x + 1) / 2)
    (y : ℕ) (hfour : y % 4 = 3) (hl : ∀ j, y ≤ T^[j] y) : 100000 < y :=
  lt_trans (by decide : 100000 < 330911) (minimum_above_330911 T hT y hfour hl)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3200000 in
lemma short_odd_counts : ∀ s : Fin 971, 300001 ^ s.val <
    2 ^ ((3 ^ s.val).log2 + 1) * 100000 ^ s.val := by decide +kernel


lemma least_mod_four (T : ℕ → ℕ) (hT : ∀ x, T x = if x % 2 = 0 then x / 2 else (3 * x + 1) / 2)
    (y : ℕ) (hy : 1 < y) (hl : ∀ i, y ≤ T^[i] y) : y % 4 = 3 := by
  have h1 := hl 1
  change y ≤ T y at h1
  rw [hT] at h1
  have he : y % 2 ≠ 0 := by
    intro h; rw [if_pos h] at h1; omega
  by_contra hn
  have hz : ((3 * y + 1) / 2) % 2 = 0 := by omega
  have h2 := hl 2
  change y ≤ T (T y) at h2
  have ht : T y = (3 * y + 1) / 2 := by rw [hT, if_neg he]
  rw [ht, hT, if_pos hz] at h2
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3200000 in
private theorem first_band_powers : ∀ q : Fin 1636,
    let A := 2 ^ ((3 ^ q.val).log2+1)
    q.val * A < (3*330912+1) * (A-3^q.val) := by decide +kernel

lemma first_band_minimum {n p q : ℕ} (hq : q < 1636) (hc : 3^q < 2^p)
    (hgap : (3*n+1)*(2^p-3^q) ≤ q*2^p) : n ≤ 330911 := by
  let A := 2 ^ ((3 ^ q).log2+1)
  have hA := first_band_powers ⟨q,hq⟩
  change q * A < (3*330912+1) * (A-3^q) at hA
  have hp : A ≤ 2^p := Nat.pow_le_pow_right (by decide)
    ((Nat.log2_lt (by positivity : 3^q ≠ 0)).mpr hc)
  have hs : 3^q < A := by
    apply (Nat.log2_lt (by positivity : 3^q ≠ 0)).mp
    omega
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hp
  by_contra! hn
  have hdiff : 2^p-3^q = (A-3^q)+d := by omega
  have hadd := Nat.mul_le_mul_right d (show q ≤ 3*330912+1 by omega)
  have hn' := Nat.mul_le_mul_right (2^p-3^q) (show 3*330912+1 ≤ 3*n+1 by omega)
  rw [hdiff] at hn' hgap
  rw [hd] at hgap
  nlinarith only [hA,hadd,hn',hgap]

/-- Bernoulli's inequality after clearing denominators. -/
lemma scaled_bernoulli (B D j : ℕ) : (B + j * D) * B ^ j ≤ B * (B + D) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_succ]
    calc
      (B + (j + 1) * D) * (B ^ j * B) ≤ ((B + j * D) * B ^ j) * (B + D) := by
        nlinarith only [Nat.zero_le (j * D ^ 2 * B ^ j)]
      _ ≤ _ := by simpa only [mul_assoc] using Nat.mul_le_mul_right (B + D) ih

/-- A relative gap of at least one part in C gives a doubling in C repetitions. -/
lemma gap_doubling {A B C : ℕ} (hb : 0 < B) (hab : B < A) (hg : A ≤ (A-B)*C) :
    2 * B ^ C ≤ A ^ C := by
  let D := A-B
  have he : B+D = A := by dsimp only [D]; omega
  have hd : B ≤ C*D := by rw [Nat.mul_comm]; exact hab.le.trans hg
  have h : B * (2 * B ^ C) ≤ B * A ^ C := calc
    _ = (B+B) * B ^ C := by ring
    _ ≤ (B+C*D) * B ^ C := Nat.mul_le_mul_right _ (Nat.add_le_add_left hd B)
    _ ≤ B * (B+D) ^ C := scaled_bernoulli B D C
    _ = _ := by rw [he]
  exact le_of_mul_le_mul_left h hb

/-- In a primitive cycle the correction from distinct odd inputs is at most
linear after taking the sixth power. Successive blocks of C repetitions
double, which bounds the multiplicity of any reduced length-to-odd-count ratio. -/
lemma cycle_multiplier_bound {A B C q d : ℕ} (hb : 0 < B) (hab : B < A)
    (hg : A ≤ (A-B)*C) (hpack : (A^d)^6 ≤ (2*(q*d)+1)*(B^d)^6) :
    d < C * (Nat.log 2 (1 + 2*q*C) / 5 + 1) := by
  have hC : 0 < C := by
    by_contra! h
    have := Nat.eq_zero_of_le_zero h
    simp_all
  let t := d / C
  let r := d % C
  have he : C*t+r = d := Nat.div_add_mod d C
  have hblocks : 2^t * B^d ≤ A^d := calc
    _ = (2 * B^C)^t * B^r := by
      conv_lhs => rw [← he, pow_add, pow_mul]
      rw [mul_pow]; ring
    _ ≤ (A^C)^t * A^r := Nat.mul_le_mul
      (Nat.pow_le_pow_left (gap_doubling hb hab hg) t) (Nat.pow_le_pow_left hab.le r)
    _ = _ := by rw [← pow_mul, ← pow_add, he]
  have h6 := Nat.pow_le_pow_left hblocks 6
  rw [mul_pow] at h6
  have hu := le_of_mul_le_mul_right (h6.trans hpack) (by positivity : 0 < (B^d)^6)
  rw [← pow_mul] at hu
  have ht : d < C*(t+1) := Nat.lt_mul_div_succ d hC
  have ht2 : t+1 ≤ 2^t := by
    induction t with
    | zero => decide
    | succ j ih => rw [pow_succ]; omega
  have hpad : 2*(q*d)+1 ≤ (1+2*q*C)*(t+1) := by
    nlinarith only [Nat.mul_le_mul_left (2*q) ht.le, Nat.zero_le t]
  have hpow : 2^(5*t)*2^t ≤ (1+2*q*C)*2^t := calc
    _ = 2^(t*6) := by rw [← pow_add]; congr 1; omega
    _ ≤ 2*(q*d)+1 := hu
    _ ≤ (1+2*q*C)*(t+1) := hpad
    _ ≤ _ := Nat.mul_le_mul_left _ ht2
  have hlog := Nat.le_log_of_pow_le (by decide : 1 < 2)
    (le_of_mul_le_mul_right hpow (by positivity : 0 < 2^t))
  exact ht.trans_le (Nat.mul_le_mul_left C (by omega))

/-- Route a cycle to its minimum, preserving its return time. -/
theorem main : H1 → H2 → OMA.R_Erdos1135_erdos_1135_R2.H2 := by
  classical
  intro hgap hsearch k n S hn hS hS94 _ _ he
  let T := fun v : ℕ => if v % 2 = 0 then v / 2 else (3 * v + 1) / 2
  have hfix := mask_returns (T := T) (fun _ => rfl) k n S hS he
  have hcard := card_le_card hS
  rw [card_range] at hcard
  have hk : 0 < k := by omega
  have hex : ∃ y : ℕ, ∃ j, T^[j] n = y := ⟨n, 0, rfl⟩
  let y := Nat.find hex
  obtain ⟨j, hj⟩ : ∃ j, T^[j] n = y := Nat.find_spec hex
  have hy : 2048 < y := hj ▸ no_small_phase T rfl n k (by omega) hk hfix j
  have hmin (i : ℕ) : y ≤ T^[i] y := Nat.find_min' hex ⟨i + j, by rw [iterate_add_apply, hj]⟩
  have hreturn : T^[k] y = y := by rw [← hj, ← iterate_add_apply, Nat.add_comm k j, iterate_add_apply, hfix]
  let L := minimalPeriod T y
  have hL : 0 < L := (show IsPeriodicPt T k y from hreturn).minimalPeriod_pos hk
  have hcy : T^[L] y = y := iterate_minimalPeriod
  let odds := fun d => (range d).filter fun i => T^[i] y % 2 = 1
  let s := (odds L).card
  have hrec := OMA.R_Erdos1135_erdos_1135_R2.shortcut_rec (T := T) (fun _ => rfl) y
  have ha := OMA.R_Erdos1135_erdos_1135_R2.affine_identity (x := fun i => T^[i] y) (odds := odds)
    hrec (fun _ => rfl) L
  change 2 ^ L * T^[L] y = 3 ^ s * y + _ at ha
  rw [hcy] at ha
  have hypos : 0 < y := by omega
  have hle := le_of_mul_le_mul_right (by omega : 3 ^ s * y ≤ 2 ^ L * y) hypos
  have hc : 3 ^ s < 2 ^ L := by
    have h3 : 3 ^ s % 2 = 1 := by rw [Nat.pow_mod]; norm_num
    have h2 : 2 ^ L % 2 = 0 := by
      obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
      simp [ha, pow_succ]
    omega
  have hcB (B : ℕ) (hB : ∀ i, B ≤ T^[i] y) : 2 ^ L * B ^ s ≤ (3 * B + 1) ^ s := by
    have H := OMA.R_Erdos1135_erdos_1135_R2.slope_upper B (fun i => T^[i] y) odds hrec (fun _ => rfl) hB L
    change (2 ^ L * T^[L] y) * B ^ s ≤ (3 * B + 1) ^ s * y at H
    rw [hcy, mul_right_comm] at H
    exact le_of_mul_le_mul_right H hypos
  have hy4 := least_mod_four T (fun _ => rfl) y (by omega) hmin
  have hyB := minimum_above_330911 T rfl y hy4 hmin
  let d := Nat.gcd L s
  let p := L / d
  let q := s / d
  have hd : 0 < d := Nat.gcd_pos_of_pos_left _ hL
  have hpd : p*d = L := Nat.div_mul_cancel (Nat.gcd_dvd_left L s)
  have hqd : q*d = s := Nat.div_mul_cancel (Nat.gcd_dvd_right L s)
  have hp : 0 < p := by
    by_contra! h
    have hz := Nat.eq_zero_of_le_zero h
    rw [hz, Nat.zero_mul] at hpd
    omega
  have hred : 3^q < 2^p := by
    apply (Nat.pow_lt_pow_iff_left (by omega : d ≠ 0)).mp
    simpa only [← pow_mul, hpd, hqd] using hc
  have hslope (B : ℕ) (hB : ∀ i, B ≤ T^[i] y) : 2^p * B^q ≤ (3*B+1)^q := by
    apply (Nat.pow_le_pow_iff_left (by omega : d ≠ 0)).mp
    simpa only [mul_pow, ← pow_mul, hpd, hqd] using hcB B hB
  have hnum := hslope y hmin
  have htriv : 2^p ≤ (2^p-3^q)*2^p :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hlocal := (minimum_bound hred hnum htriv).1
  have hq : 1636 ≤ q := by
    by_contra! hsmall
    exact (not_le_of_gt hyB) (first_band_minimum hsmall hred hlocal)
  have hu : 2^p * 100000^q ≤ 300001^q := hslope 100000 (fun i => by have := hmin i; omega)
  have hlen : p < 2*q := by
    have hh := Nat.pow_lt_pow_left (by decide : 300001 < 4 * 100000) (by omega : q ≠ 0)
    rw [mul_pow, show (4 : ℕ) = 2 ^ 2 by decide, ← pow_mul] at hh
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
      (Nat.lt_of_mul_lt_mul_right (hu.trans_lt hh))
  have hpack : (2^L)^6 ≤ (2*s+1)*(3^s)^6 := by
    by_contra! htest
    have hprod := OMA.R_Erdos1135_erdos_1135_R2.product_identity (x := fun i => T^[i] y)
      (odds := odds) hrec (fun _ => rfl) L
    have hinj : Set.InjOn (fun i : ℕ => T^[i] y) (odds L) := by
      intro i hi j hj he
      exact (iterate_eq_iterate_iff_of_lt_minimalPeriod
        (mem_range.mp (mem_filter.mp hi).1) (mem_range.mp (mem_filter.mp hj).1)).mp he
    have hdrop := OMA.R_Erdos1135_erdos_1135_R2.parity_drop 0 (fun i : ℕ => T^[i] y) L
      (odds L) hypos (fun i hi => (mem_filter.mp hi).2)
      (fun i _ => by have := hmin i; omega) hinj hprod (by simpa only [Nat.zero_add,
        Nat.mul_zero, Nat.one_mul] using htest)
    rw [hcy] at hdrop
    exact (lt_irrefl y) hdrop
  have hg := hgap p q (by omega) hred
  have huniform := (minimum_bound hred hnum hg).2
  have hmult := cycle_multiplier_bound (d := d) (q := q) (by positivity : 0 < 3^q) hred hg
    (by simpa only [← pow_mul, hpd, hqd] using hpack)
  exact hsearch q p d y hq (Nat.coprime_div_gcd_div_gcd hd) hp hlen hyB hy4 huniform
    hd hmult hred hlocal (by rw [hpd, hqd]) (fun i _ => hmin i) (by rwa [hpd])

/-- The remaining search follows from the original cycle exclusion. -/
theorem necessary (h : OMA.R_Erdos1135_erdos_1135_R2.H2) : H2 := by
  let T := fun v : ℕ => if v % 2 = 0 then v / 2 else (3 * v + 1) / 2
  intro q p d n _ _ hp _ hn _ _ hd _ _ _ _ _ hfix
  have hk : 0 < p*d := Nat.mul_pos hp hd
  exact OMA.R_Erdos1135_erdos_1135_R2.no_large_cycle h (T := T) (fun _ => rfl) n (p*d) hk
    (no_small_phase T rfl n (p*d) (by omega) hk hfix) hfix

end OMA.R_Erdos1135_erdos_1135_R2_H2_R1
