import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1

/-!
# Simple primes below 126943 in the branch containing 19423

Of the ten forced simple primes, six already divide successors of other
forced primes. Each can occur there only once. If a further simple prime
q lies below 126943, the remaining four primes cannot account for the odd
part of q+1. A finite power-of-two check gives a prime divisor r ≥ 25000
with q+1 equal to 2r or 4r. Iterating once identifies a repeated prime z
and leaves just three possibilities for q. The product bound on the
repeated primes permits at most two such q, and at most one below 100000.
The three subproblems ask for a uniform exponent bound at each possible
count of these simple primes.
-/

-- Credit: @Pixelstorm44
namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1_H2_R2

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1.Erdos1052C7
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1.Erdos1052C9

set_option maxRecDepth 4096 in
/-- A simple successor with no large odd factor would have odd part one or a
single unused prime. Check the possible powers of two for those five odd parts. -/
private theorem noSmooth (q k u : ℕ) (hp : q.Prime) (hlo : 41348 ≤ q)
    (hhi : q < 126943) (he : q + 1 = 2 ^ k * u) (hu : u = 1 ∨ u ∈ ({223, 3967, 8191, 19423} : Finset ℕ)) : False := by
  have hu0 : 0 < u := by by_contra! h; simp [show u = 0 by omega] at he
  have hk : k < 17 := by
    by_contra! hk
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) hk
    have hh := Nat.le_mul_of_pos_right (2 ^ k) hu0
    norm_num at h
    omega
  have cert : ∀ j : Fin 17, ∀ v ∈ insert 1 ({223, 3967, 8191, 19423} : Finset ℕ),
      let x := 2 ^ j.val * v - 1
      41348 ≤ x → x < 126943 → ¬ Nat.Prime x := by
    intro j v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl|rfl|rfl|rfl|rfl <;> fin_cases j <;> norm_num
  have hc := cert ⟨k,hk⟩ u (Finset.mem_insert.mpr hu)
  simp [← he, hlo, hhi, hp] at hc

/-- Two distinct unused primes already have product greater than the window. -/
private theorem largePair : ∀ r ∈ ({223, 3967, 8191, 19423} : Finset ℕ), ∀ s ∈ ({223, 3967, 8191, 19423} : Finset ℕ), r ≠ s → 126943 < r * s := by decide

private theorem largeFactor {q : ℕ} (hp : q.Prime) (hl : 41348 ≤ q) (hh : q < 126943)
    (hsmall : ∀ r, r.Prime → r ≠ 2 → r ∣ q + 1 → r < 25000 → r ∈ ({223, 3967, 8191, 19423} : Finset ℕ))
    (hsq : ∀ r ∈ ({223, 3967, 8191, 19423} : Finset ℕ), ¬ r * r ∣ q + 1) :
    ∃ r, r.Prime ∧ 25000 ≤ r ∧ r ∣ q + 1 := by
  by_contra! hnone
  have tip {r : ℕ} (hr : r.Prime) (h2 : r ≠ 2) (hd : r ∣ q + 1) : r ∈ ({223, 3967, 8191, 19423} : Finset ℕ) :=
    hsmall r hr h2 hd (by by_contra! h; exact hnone r hr h hd)
  obtain ⟨k,u,hu,he⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.succ_ne_zero q)
  change q + 1 = 2 ^ k * u at he
  by_cases hu1 : u = 1
  · exact noSmooth q k u hp hl hh he (Or.inl hu1)
  obtain ⟨r,v,hr,hr2,hv,hv0⟩ := odd_prime_factor hu hu1
  have rd : r ∣ q + 1 := ⟨2 ^ k * v, by rw [he,hv]; ring⟩
  have rt := tip hr hr2 rd
  by_cases hv1 : v = 1
  · exact noSmooth q k u hp hl hh he (Or.inr (by simpa [hv,hv1] using rt : u ∈ ({223, 3967, 8191, 19423} : Finset ℕ)))
  obtain ⟨s,w,hs,hs2,hw,hw0⟩ := odd_prime_factor (Nat.odd_mul.mp (hv ▸ hu)).2 hv1
  have rs : r * s ∣ q + 1 := ⟨2 ^ k * w, by rw [he,hv,hw]; ring⟩
  have st := tip hs hs2 ((dvd_mul_left s r).trans rs)
  by_cases eq : r = s
  · exact hsq r rt (eq ▸ rs)
  have := largePair r rt s st eq
  have := Nat.le_of_dvd (Nat.succ_pos q) rs
  omega

private theorem cofactor {q r : ℕ} (hq : q.Prime) (hr : r.Prime)
    (hlo : 41348 ≤ q) (hhi : q < 126943) (hrlo : 25000 ≤ r) (hd : r ∣ q+1) :
    q + 1 = 2*r ∨ q + 1 = 4*r := by
  obtain ⟨k,hk⟩ := hd
  have hk6 : k < 6 := by
    by_contra! hb
    have := Nat.mul_le_mul hrlo hb
    omega
  have hqo := hq.odd_of_ne_two (by omega)
  have hro := hr.odd_of_ne_two (by omega)
  have hev : Even (r*k) := hk ▸ (by obtain ⟨j,hj⟩ := hqo; exact ⟨j+1,by omega⟩ : Even (q+1))
  have hke : Even k := (Nat.even_mul.mp hev).resolve_left (Nat.not_even_iff_odd.mpr hro)
  obtain ⟨j,hj⟩ := hke
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  rcases (show k = 2 ∨ k = 4 by omega) with h|h <;> simp_all [Nat.mul_comm]


/-- Every new simple prime in the window has a prime divisor of its successor
with cofactor 2 or 4. The six exhausted odd primes have distinct known sources. -/
private theorem step {n q : ℕ} {S P : Finset ℕ}
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (hge : ∀ z ∈ S, 25000 ≤ z)
    (mem : ∀ p, p ∈ P ↔ p.Prime ∧ p ≠ 2 ∧ p ∣ n ∧ p ∉ S)
    (hc : ({3, 5, 7, 19, 31, 223, 607, 3967, 8191, 19423} : Finset ℕ) ⊆ P)
    (cl : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ S → ∀ p ∈ P, c ∣ p+1 → c ∈ P)
    (uniq : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ S → ∀ p ∈ P, ∀ t ∈ P,
      c ∣ p+1 → c ∣ t+1 → p=t)
    (sq : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ S → ∀ p ∈ P, ¬ c*c ∣ p+1)
    (gap : ∀ r ∈ P, r < 41348 → r ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 8191, 19423} : Finset ℕ))
    (hq : (19423 < q ∧ Nat.Prime q ∧ q ∣ n ∧ ¬ q ^ 2 ∣ n)) (hhi : q < 126943) :
    ∃ r, (r ∈ S ∨ (19423 < r ∧ Nat.Prime r ∧ r ∣ n ∧ ¬ r ^ 2 ∣ n)) ∧ (q+1=2*r ∨ q+1=4*r) := by
  obtain ⟨hbig,hp,hd,hns⟩ := hq
  have hP := (mem q).mpr ⟨hp,by omega,hd,fun hs => hns ((hS q).mp hs).2.2⟩
  have away : ∀ x ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 8191, 19423} : Finset ℕ), x ≤ 19423 := by decide
  have hlow : 41348 ≤ q := by by_contra! h; exact (not_le.mpr hbig) (away q (gap q hP h))
  have outside {r} (hr : r < 25000) : r ∉ S := fun h => (not_le.mpr hr) (hge r h)
  have used {r t : ℕ} (hr : r.Prime) (h2 : r ≠ 2) (hl : r < 25000)
      (ht : t ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 8191, 19423} : Finset ℕ)) (hrd : r ∣ t+1) : ¬ r ∣ q+1 := by
    intro hdq
    have := uniq r hr h2 (outside hl) q hP t (hc ht) hdq hrd
    have := away t ht
    omega
  have small {r} (hr : r.Prime) (h2 : r ≠ 2) (hrd : r ∣ q+1) (hl : r < 25000) : r ∈ ({223, 3967, 8191, 19423} : Finset ℕ) := by
    have rc := gap r (cl r hr h2 (outside hl) q hP hrd) (by omega)
    simp only [Finset.mem_insert, Finset.mem_singleton] at rc
    rcases rc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact False.elim (used hr h2 hl (t := 5) (by decide) (by decide) hrd)
    · exact False.elim (used hr h2 hl (t := 19) (by decide) (by decide) hrd)
    · exact False.elim (used hr h2 hl (t := 223) (by decide) (by decide) hrd)
    · exact False.elim (used hr h2 hl (t := 607) (by decide) (by decide) hrd)
    · exact False.elim (used hr h2 hl (t := 3967) (by decide) (by decide) hrd)
    · decide
    · exact False.elim (used hr h2 hl (t := 19423) (by decide) (by decide) hrd)
    · decide
    · decide
    · decide
  have ts : ∀ r ∈ ({223, 3967, 8191, 19423} : Finset ℕ), Nat.Prime r ∧ r ≠ 2 ∧ r < 25000 := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> norm_num
  obtain ⟨r,hr,hrlo,hrd⟩ := largeFactor hp hlow hhi (fun _ => small)
    (fun r hm => sq r (ts r hm).1 (ts r hm).2.1 (outside (ts r hm).2.2) q hP)
  refine ⟨r,?_,cofactor hp hr hlow hhi hrlo hrd⟩
  by_cases hs : r ∈ S
  · exact Or.inl hs
  have h2 : r ≠ 2 := by omega
  exact Or.inr ⟨by omega,hr,((mem r).mp (cl r hr h2 hs q hP hrd)).2.2.1,
    fun hsqr => hs ((hS r).mpr ⟨hr,h2,hsqr⟩)⟩
private theorem classify {n q : ℕ} {S : Finset ℕ}
    (next : ∀ q, ((19423 < q ∧ Nat.Prime q ∧ q ∣ n ∧ ¬ q ^ 2 ∣ n) ∧ q < 126943) → ∃ r, (r ∈ S ∨ (19423 < r ∧ Nat.Prime r ∧ r ∣ n ∧ ¬ r ^ 2 ∣ n)) ∧ (q+1=2*r ∨ q+1=4*r))
    (mod3 : ∀ q, (19423 < q ∧ Nat.Prime q ∧ q ∣ n ∧ ¬ q ^ 2 ∣ n) → q%3 = 1)
    (floorP : ∀ q, (19423 < q ∧ Nat.Prime q ∧ q ∣ n ∧ ¬ q ^ 2 ∣ n) → 41348 ≤ q)
    (floorS : ∀ z ∈ S, 25000 ≤ z)
    (hq : ((19423 < q ∧ Nat.Prime q ∧ q ∣ n ∧ ¬ q ^ 2 ∣ n) ∧ q < 126943)) : ∃ z ∈ S, z ≤ 63472 ∧ ((q+1 = 2*z ∧ z%3 = 1) ∨ (q+1 = 4*z ∧ z%3 = 2) ∨
      (q+3 = 4*z ∧ z%3 = 1 ∧ (19423 < (2*z-1) ∧ Nat.Prime (2*z-1) ∧ (2*z-1) ∣ n ∧ ¬ (2*z-1) ^ 2 ∣ n))) := by
  obtain ⟨r,hr,link⟩ := next q hq
  obtain ⟨qp,qt⟩ := hq
  have qm := mod3 q qp
  rcases hr with hr|hr
  · refine ⟨r,hr,by omega,?_⟩
    omega
  have rm := mod3 r hr
  obtain ⟨z,hz,link'⟩ := next r ⟨hr,by omega⟩
  rcases hz with hz|hz
  · have := floorS z hz
    have eq : 2*z-1 = r := by omega
    refine ⟨z,hz,by omega,Or.inr (Or.inr ⟨by omega,by omega,eq ▸ hr⟩)⟩
  · have := floorP z hz
    omega

/-- A product bound for a finite subset of the repeated primes. -/
private theorem budget {S T : Finset ℕ} (hthin : ∏ z ∈ S, (1+5/(z:ℚ)) ≤ 5001/5000)
    (hT : T ⊆ S) : ∏ z ∈ T, (1+5/(z:ℚ)) ≤ 5001/5000 := by
  refine le_trans (Finset.prod_le_prod_of_subset_of_one_le hT (fun z _ => by positivity) ?_) hthin
  intro z _ _
  have : (0:ℚ) ≤ 5 / (z:ℚ) := by positivity
  linarith

private theorem weight {z B : ℕ} (hz : 0 < z) (hB : z ≤ B) :
    1 + 5 / (B:ℚ) ≤ 1 + 5 / (z:ℚ) := by
  have hz' : (0:ℚ) < z := by exact_mod_cast hz
  exact add_le_add_right (div_le_div_of_nonneg_left (by norm_num) hz' (by exact_mod_cast hB)) _

private theorem capacity {n : ℕ} {S : Finset ℕ}
    (floorS : ∀ z ∈ S, 25000 ≤ z)
    (thin : ∏ z ∈ S, (1+5/(z:ℚ)) ≤ 5001/5000)
    (shape : ∀ q, ((19423 < q ∧ Nat.Prime q ∧ q ∣ n ∧ ¬ q ^ 2 ∣ n) ∧ q < 126943) → ∃ z ∈ S, z ≤ 63472 ∧ ((q+1 = 2*z ∧ z%3 = 1) ∨ (q+1 = 4*z ∧ z%3 = 2) ∨
      (q+3 = 4*z ∧ z%3 = 1 ∧ (19423 < (2*z-1) ∧ Nat.Prime (2*z-1) ∧ (2*z-1) ∣ n ∧ ¬ (2*z-1) ^ 2 ∣ n)))) :
    ∀ a b c, ((19423 < a ∧ Nat.Prime a ∧ a ∣ n ∧ ¬ a ^ 2 ∣ n) ∧ a < 126943) → ((19423 < b ∧ Nat.Prime b ∧ b ∣ n ∧ ¬ b ^ 2 ∣ n) ∧ b < 126943) → ((19423 < c ∧ Nat.Prime c ∧ c ∣ n ∧ ¬ c ^ 2 ∣ n) ∧ c < 126943) → a ≠ b → a ≠ c → b ≠ c → False := by
  intro a b c ha hb hc hab hac hbc
  obtain ⟨x,hx,xl,xa⟩ := shape a ha
  obtain ⟨y,hy,yl,yb⟩ := shape b hb
  obtain ⟨z,hz,zl,zc⟩ := shape c hc
  have pos {t} (ht : t ∈ S) : 0 < t := lt_of_lt_of_le (by decide : 0 < 25000) (floorS t ht)
  by_cases sm : ∃ t ∈ S, t ≤ 31736
  · obtain ⟨t,ht,ts⟩ := sm
    have unique {v} (hv : v ∈ S) (vl : v ≤ 63472) : v = t := by
      by_contra h
      have hprod := budget thin (T := {v,t}) (Finset.insert_subset hv (Finset.singleton_subset_iff.mpr ht))
      rw [Finset.prod_pair h] at hprod
      have hw := mul_le_mul (weight (pos hv) vl) (weight (pos ht) ts) (by positivity) (by positivity)
      norm_num at hw
      linarith
    rw [unique hx xl] at xa
    rw [unique hy yl] at yb
    rw [unique hz zl] at zc
    omega
  · push Not at sm
    have only {p v} (hp : ((19423 < p ∧ Nat.Prime p ∧ p ∣ n ∧ ¬ p ^ 2 ∣ n) ∧ p < 126943)) (hv : v ∈ S) (h : ((p+1 = 2*v ∧ v%3 = 1) ∨ (p+1 = 4*v ∧ v%3 = 2) ∨
      (p+3 = 4*v ∧ v%3 = 1 ∧ (19423 < (2*v-1) ∧ Nat.Prime (2*v-1) ∧ (2*v-1) ∣ n ∧ ¬ (2*v-1) ^ 2 ∣ n)))) : p+1 = 2*v := by
      have := sm v hv
      have := hp.2
      omega
    have ea := only ha hx xa
    have eb := only hb hy yb
    have ec := only hc hz zc
    have xy : x ≠ y := by omega
    have xz : x ≠ z := by omega
    have yz : y ≠ z := by omega
    have hprod := budget thin (T := {x,y,z}) (Finset.insert_subset hx (Finset.insert_subset hy (Finset.singleton_subset_iff.mpr hz)))
    rw [Finset.prod_insert (by simp [xy,xz]), Finset.prod_pair yz] at hprod
    have hyz := mul_le_mul (weight (pos hy) yl) (weight (pos hz) zl) (by positivity) (by positivity)
    have hxyz := mul_le_mul (weight (pos hx) xl) hyz (by positivity) (by positivity)
    norm_num at hxyz
    linarith

private theorem smallUnique {n : ℕ} {S : Finset ℕ}
    (floorS : ∀ z ∈ S, 25001 ≤ z)
    (thin : ∏ z ∈ S, (1+5/(z:ℚ)) ≤ 5001/5000)
    (shape : ∀ q, ((19423 < q ∧ Nat.Prime q ∧ q ∣ n ∧ ¬ q ^ 2 ∣ n) ∧ q < 126943) → ∃ z ∈ S, z ≤ 63472 ∧ ((q+1 = 2*z ∧ z%3 = 1) ∨ (q+1 = 4*z ∧ z%3 = 2) ∨
      (q+3 = 4*z ∧ z%3 = 1 ∧ (19423 < (2*z-1) ∧ Nat.Prime (2*z-1) ∧ (2*z-1) ∣ n ∧ ¬ (2*z-1) ^ 2 ∣ n))))
    {a b : ℕ} (ha : ((19423 < a ∧ Nat.Prime a ∧ a ∣ n ∧ ¬ a ^ 2 ∣ n) ∧ a < 126943)) (hb : ((19423 < b ∧ Nat.Prime b ∧ b ∣ n ∧ ¬ b ^ 2 ∣ n) ∧ b < 126943)) (al : a < 100000) (bl : b < 100000) : a=b := by
  obtain ⟨x,hx,_,xa⟩ := shape a ha
  obtain ⟨y,hy,_,yb⟩ := shape b hb
  have xf := floorS x hx
  have yf := floorS y hy
  have ex : a+1=2*x := by omega
  have ey : b+1=2*y := by omega
  by_contra h
  have xy : x ≠ y := by omega
  have hprod := budget thin (T := {x,y}) (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy))
  rw [Finset.prod_pair xy] at hprod
  have wx := weight (z := x) (B := 50000) (by omega) (by omega)
  have wy := weight (z := y) (B := 50000) (by omega) (by omega)
  have ww := mul_le_mul wx wy (by positivity) (by positivity)
  norm_num at ww
  linarith

private theorem residue_one {q : ℕ} (h : ¬ 3 ∣ q) (h' : ¬ 3 ∣ q+1) : q%3=1 := by omega

private theorem shape_floor {n q z : ℕ} (h : ((q+1 = 2*z ∧ z%3 = 1) ∨ (q+1 = 4*z ∧ z%3 = 2) ∨
      (q+3 = 4*z ∧ z%3 = 1 ∧ (19423 < (2*z-1) ∧ Nat.Prime (2*z-1) ∧ (2*z-1) ∣ n ∧ ¬ (2*z-1) ^ 2 ∣ n)))) (hz : 25001 ≤ z) : 50000 < q := by
  omega
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n → 223 ∣ n → 607 ∣ n → 3967 ∣ n → 48 ≤ padicValNat 2 n →
    ∏ z ∈ S, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000 → (∀ z ∈ S, 25000 ≤ z) →
    8191 ∣ n → ¬ 7933 ∣ n → ¬ 16381 ∣ n → 19423 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → ¬ q ^ 2 ∣ n → q < 41348 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨
        q = 8191 ∨ q = 19423) →
    let extra := fun q : ℕ => 19423 < q ∧ q.Prime ∧ q ∣ n ∧ ¬ q ^ 2 ∣ n
    (∀ q, extra q → 126943 ≤ q) →
    padicValNat 2 n ≤ A

def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n → 223 ∣ n → 607 ∣ n → 3967 ∣ n → 48 ≤ padicValNat 2 n →
    ∏ z ∈ S, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000 → (∀ z ∈ S, 25000 ≤ z) →
    8191 ∣ n → ¬ 7933 ∣ n → ¬ 16381 ∣ n → 19423 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → ¬ q ^ 2 ∣ n → q < 41348 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨
        q = 8191 ∨ q = 19423) →
    let extra := fun q : ℕ => 19423 < q ∧ q.Prime ∧ q ∣ n ∧ ¬ q ^ 2 ∣ n
    let window := fun q : ℕ => extra q ∧ q < 126943
    let classified := fun q : ℕ => window q ∧ 50000 < q ∧ ∃ z ∈ S, z ≤ 63472 ∧
      ((q+1 = 2*z ∧ z%3 = 1) ∨ (q+1 = 4*z ∧ z%3 = 2) ∨
       (q+3 = 4*z ∧ z%3 = 1 ∧ extra (2*z-1)))
    (∃ q, classified q ∧ ∀ r, window r → r=q) →
    padicValNat 2 n ≤ A

def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n → 223 ∣ n → 607 ∣ n → 3967 ∣ n → 48 ≤ padicValNat 2 n →
    ∏ z ∈ S, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000 → (∀ z ∈ S, 25000 ≤ z) →
    8191 ∣ n → ¬ 7933 ∣ n → ¬ 16381 ∣ n → 19423 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → ¬ q ^ 2 ∣ n → q < 41348 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨
        q = 8191 ∨ q = 19423) →
    let extra := fun q : ℕ => 19423 < q ∧ q.Prime ∧ q ∣ n ∧ ¬ q ^ 2 ∣ n
    let window := fun q : ℕ => extra q ∧ q < 126943
    let classified := fun q : ℕ => window q ∧ 50000 < q ∧ ∃ z ∈ S, z ≤ 63472 ∧
      ((q+1 = 2*z ∧ z%3 = 1) ∨ (q+1 = 4*z ∧ z%3 = 2) ∨
       (q+3 = 4*z ∧ z%3 = 1 ∧ extra (2*z-1)))
    (∃ a b, classified a ∧ classified b ∧ a<b ∧ 100000 ≤ b ∧
      ∀ c, window c → c=a ∨ c=b) →
    padicValNat 2 n ≤ A

theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1.H2 := by
  intro h₁ h₂ h₃
  obtain ⟨A,hA⟩ := h₁
  obtain ⟨B,hB⟩ := h₂
  obtain ⟨C,hC⟩ := h₃
  refine ⟨max A (max B C), ?_⟩
  intro n hn hns S hS ha hb h4 h3 h5 h7 h19 hsup h16 h32 h31 h223 h607 h3967 h48 hthin hge h8191 h79 h163 h194 hexc
  let core := ({3, 5, 7, 19, 31, 223, 607, 3967, 8191, 19423} : Finset ℕ)
  let Extra := fun (n q : ℕ) => (19423 < q ∧ Nat.Prime q ∧ q ∣ n ∧ ¬ q ^ 2 ∣ n)
  let Window := fun (n q : ℕ) => Extra n q ∧ q < 126943
  let Shape := fun (n q z : ℕ) => ((q+1 = 2*z ∧ z%3 = 1) ∨ (q+1 = 4*z ∧ z%3 = 2) ∨
      (q+3 = 4*z ∧ z%3 = 1 ∧ (19423 < (2*z-1) ∧ Nat.Prime (2*z-1) ∧ (2*z-1) ∣ n ∧ ¬ (2*z-1) ^ 2 ∣ n)))
  let Classified := fun (n : ℕ) (S : Finset ℕ) (q : ℕ) =>
    Window n q ∧ 50000 < q ∧ ∃ z ∈ S, z ≤ 63472 ∧ Shape n q z
  have hm2 : 2 ∣ n := dvd_of_one_le_padicValNat (le_trans (by norm_num) h48)
  obtain ⟨K,K',P,hP,hK,_,_,E,mem⟩ := setup7 hn hS hm2
  obtain ⟨cl,_,uniq,_,_,sq,_,_⟩ := facts hP hK E
  have cdata : ∀ r ∈ core, Nat.Prime r ∧ r ≠ 2 ∧ r < 25000 := by
    intro r hr
    simp only [core, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  have hc : core ⊆ P := by
    intro r hr
    obtain ⟨rp,r2,rl⟩ := cdata r hr
    refine (mem r).mpr ⟨rp,r2,?_,fun hs => (not_le.mpr rl) (hge r hs)⟩
    simp only [core, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> assumption
  have gap : ∀ r ∈ P, r < 41348 → r ∈ core := by
    intro r hr hl
    obtain ⟨hp,h2,hd,hs⟩ := (mem r).mp hr
    have he := hexc r hp hd (fun hsqr => hs ((hS r).mpr ⟨hp,h2,hsqr⟩)) hl
    simp only [core, Finset.mem_insert, Finset.mem_singleton]
    exact he.resolve_left h2
  have inP {q} (hq : Extra n q) : q ∈ P := (mem q).mpr
    ⟨hq.2.1,ne_of_gt (lt_trans (by decide : 2 < 19423) hq.1),hq.2.2.1,
      fun hs => hq.2.2.2 ((hS q).mp hs).2.2⟩
  have floorP {q} (hq : Extra n q) : 41348 ≤ q := by
    by_contra! h
    have top : ∀ r ∈ core, r ≤ 19423 := by change ∀ r ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 8191, 19423} : Finset ℕ), r ≤ 19423; decide
    exact (not_le.mpr hq.1) (top q (gap q (inP hq) h))
  have mod3 {q} (hq : Extra n q) : q%3=1 := by
    have hl := floorP hq
    have ne0 : ¬ 3 ∣ q := fun hd => (ne_of_lt (lt_of_lt_of_le (by decide : 3 < 41348) hl))
      ((Nat.prime_dvd_prime_iff_eq (by decide) hq.2.1).mp hd)
    have ne2 : ¬ 3 ∣ q+1 := by
      intro hd
      have h := uniq 3 (by decide) (by decide) (fun hs => (by decide : ¬ 25000 ≤ 3) (hge 3 hs))
        q (inP hq) 5 (hc (by change 5 ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 8191, 19423} : Finset ℕ); decide)) hd (by decide)
      exact (ne_of_gt (lt_of_lt_of_le (by decide : 5 < 41348) hl)) h
    exact residue_one ne0 ne2
  have shapes : ∀ q, Window n q → ∃ z ∈ S, z ≤ 63472 ∧ Shape n q z :=
    fun _ hw => classify (fun _ h => step hS hge mem hc cl uniq sq gap h.1 h.2)
      (fun _ => mod3) (fun _ => floorP) hge hw
  have high : ∀ z ∈ S, 25001 ≤ z := by
    intro z hz
    have hl := hge z hz
    have hp := ((hS z).mp hz).1
    have ne : z ≠ 25000 := by rintro rfl; exact (by norm_num : ¬ Nat.Prime 25000) hp
    exact lt_of_le_of_ne hl (Ne.symm ne)
  have known {q} (hq : Window n q) : Classified n S q := by
    obtain ⟨z,hz,hl,form⟩ := shapes q hq
    exact ⟨hq,shape_floor form (high z hz),z,hz,hl,form⟩
  specialize hA n hn hns S hS ha hb h4 h3 h5 h7 h19 hsup h16 h32 h31 h223 h607 h3967 h48 hthin hge h8191 h79 h163 h194 hexc
  specialize hB n hn hns S hS ha hb h4 h3 h5 h7 h19 hsup h16 h32 h31 h223 h607 h3967 h48 hthin hge h8191 h79 h163 h194 hexc
  specialize hC n hn hns S hS ha hb h4 h3 h5 h7 h19 hsup h16 h32 h31 h223 h607 h3967 h48 hthin hge h8191 h79 h163 h194 hexc
  by_cases one : ∃ q, Window n q
  · obtain ⟨q,hq⟩ := one
    by_cases two : ∃ r, Window n r ∧ r ≠ q
    · obtain ⟨r,hr,hrq⟩ := two
      have twoCase {a b} (ha : Window n a) (hb : Window n b) (ab : a<b) :
          padicValNat 2 n ≤ C := by
        apply hC
        refine ⟨a,b,known ha,known hb,ab,?_,?_⟩
        · by_contra! bl
          exact (ne_of_lt ab) (smallUnique high hthin shapes ha hb (lt_trans ab bl) bl)
        · intro c hc'
          by_contra! h
          exact capacity hge hthin shapes a b c ha hb hc' (ne_of_lt ab) h.1.symm h.2.symm
      have : padicValNat 2 n ≤ C := by
        rcases lt_or_gt_of_ne hrq with h|h
        · exact twoCase hr hq h
        · exact twoCase hq hr h
      exact this.trans ((le_max_right B C).trans (le_max_right A _))
    · have h := hB ⟨q,known hq,fun r hr => by by_contra h; exact two ⟨r,hr,h⟩⟩
      exact h.trans ((le_max_left B C).trans (le_max_right A _))
  · have h := hA (fun q hq => by by_contra! hl; exact one ⟨q,hq,hl⟩)
    exact h.trans (le_max_left A _)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1_H2_R2
