import FormalConjectures.OEIS.«219791»
import Mathlib.NumberTheory.Fermat

/-! A lower sieve estimate and an upper bound for balanced semiprimes in the
discriminant-square sequence imply the partition conjecture. -/

namespace OMA.R_OeisA219791_conjecture_2_R1

/-- More than half of the fourth-root survivors also survive to the cube root. -/
def H1 : Prop :=
  ∀ k : ℕ, 0 < k → ∃ N : ℕ, ∀ n ≥ N,
    let F := fun x : ℕ => (x * (n - x)) ^ (2 ^ k) + 1
    let splits := Finset.Icc 1 (n / 2)
    (splits.filter fun x => F x < (F x).minFac ^ 4).card <
      2 * (splits.filter fun x => F x < (F x).minFac ^ 3).card

/-- At most half as many balanced prime products occur on the discriminant-square
sequence as there are fourth-root survivors. -/
def H2 : Prop := by
  classical
  exact ∀ k : ℕ, 0 < k → ∃ N : ℕ, ∀ n ≥ N,
    let F := fun x : ℕ => (x * (n - x)) ^ (2 ^ k) + 1
    let bases := Finset.Icc 1 (n ^ 2 / 4)
    let paired := bases.filter fun t =>
      (∃ u : ℕ, 4 * t + u ^ 2 = n ^ 2) ∧
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ q < p ^ 2 ∧
        2 ^ (k + 1) ∣ p - 1 ∧ 2 ^ (k + 1) ∣ q - 1 ∧ p * q = t ^ (2 ^ k) + 1
    2 * paired.card ≤
      ((Finset.Icc 1 (n / 2)).filter fun x => F x < (F x).minFac ^ 4).card

lemma split_product_strict {n a b : ℕ} (hab : a < b) (hb : b ≤ n / 2) :
    a * (n - a) < b * (n - b) := by
  have diff : 0 < (b-a) * (n-a-b) := Nat.mul_pos (by omega) (by omega)
  zify [show a ≤ n by omega, show b ≤ n by omega, hab.le, show b ≤ n-a by omega] at diff ⊢
  nlinarith

lemma balanced_factors {m : ℕ} (hm : 8 ≤ m) (hsieve : m < m.minFac ^ 3)
    (hcomp : ¬ m.Prime) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 < p ∧ p ≤ q ∧ q < p ^ 2 ∧ p * q = m := by
  let p := m.minFac
  let q := m / p
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hprod : p*q = m := Nat.mul_div_cancel' (Nat.minFac_dvd _)
  have hpq : p ≤ q := Nat.minFac_le_div (by omega) hcomp
  have hp2 : 2 < p := by
    change m < p ^ 3 at hsieve
    by_contra! h
    have : p ^ 3 ≤ 2 ^ 3 := Nat.pow_le_pow_left h 3
    omega
  have hsmall : q < p^2 := by
    apply Nat.lt_of_mul_lt_mul_left (a := p)
    simpa only [hprod, ← pow_succ'] using hsieve
  have hq : q.Prime := by
    by_contra hn
    have hleast : p ≤ q.minFac := Nat.minFac_le_of_dvd
      (Nat.minFac_prime (n := q) (by omega)).two_le
      ((Nat.minFac_dvd q).trans (hprod ▸ dvd_mul_left q p))
    have hsq := Nat.minFac_sq_le_self (by omega : 0 < q) hn
    exact (not_lt_of_ge (le_trans (Nat.pow_le_pow_left hleast 2) hsq)) hsmall
  exact ⟨p, q, hp, hq, hp2, hpq, hsmall, hprod⟩

lemma square_gap {t p : ℕ} (ht : 0 < t) : p * p ≠ t ^ 2 + 1 := by
  by_cases h : p ≤ t
  · have := Nat.mul_le_mul h h
    nlinarith
  · have := Nat.mul_le_mul (by omega : t + 1 ≤ p) (by omega : t + 1 ≤ p)
    nlinarith

lemma prime_factor_class {k t p : ℕ} (hp : p.Prime) (hodd : 2 < p)
    (hdvd : p ∣ t ^ (2 ^ k) + 1) : 2 ^ (k + 1) ∣ p - 1 := by
  obtain ⟨r, hr⟩ := Nat.pow_pow_add_primeFactors_one_lt hp (by omega) hdvd
  rw [hr, Nat.add_sub_cancel]
  exact dvd_mul_left _ _

lemma paired_of_composite {k n x : ℕ} (hk : 0 < k) (hn : 8 ≤ n)
    (hx : x ∈ Finset.Icc 1 (n / 2)) :
    let t := x * (n - x)
    let m := t ^ (2 ^ k) + 1
    m < m.minFac ^ 3 → ¬m.Prime →
      t ∈ Finset.Icc 1 (n ^ 2 / 4) ∧ (∃ u : ℕ, 4 * t + u ^ 2 = n ^ 2) ∧
        ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ q < p ^ 2 ∧
          2 ^ (k + 1) ∣ p - 1 ∧ 2 ^ (k + 1) ∣ q - 1 ∧ p * q = m := by
  dsimp only
  intro hsieve hcomp
  obtain ⟨hx1, hx2⟩ := Finset.mem_Icc.mp hx
  let t := x * (n-x)
  have hy : 0 < n-x := by omega
  have ht : 0 < t := Nat.mul_pos hx1 hy
  have hlarge : n ≤ t+1 := by
    have h := Nat.zero_le ((x-1)*((n-x)-1))
    dsimp [t]
    zify [show 1 ≤ x by omega, show 1 ≤ n-x by omega, show x ≤ n by omega] at h ⊢
    nlinarith
  have hpow : t ≤ t ^ (2 ^ k) := Nat.le_self_pow (by positivity) t
  obtain ⟨p, q, hp, hq, hp2, hpq, hsmall, heq⟩ :=
    balanced_factors (m := t^(2^k)+1) (by omega) hsieve hcomp
  have hdisc : 4*t + (n-2*x)^2 = n^2 := by
    dsimp [t]
    zify [show x ≤ n by omega, show 2*x ≤ n by omega]
    ring
  have hne : p ≠ q := by
    rintro rfl
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [pow_succ 2 j, pow_mul] at heq
    exact square_gap (pow_pos ht _) heq
  exact ⟨Finset.mem_Icc.mpr ⟨ht, by omega⟩, ⟨_, hdisc⟩, p, q, hp, hq,
    lt_of_le_of_ne hpq hne, hsmall,
    prime_factor_class hp hp2 (heq ▸ dvd_mul_right _ _),
    prime_factor_class hq (by omega) (heq ▸ dvd_mul_left _ _), heq⟩

theorem main : H1 → H2 → type_of% @OeisA219791.conjecture_2 := by
  classical
  intro lower upper k hk
  obtain ⟨L, hL⟩ := lower k hk
  obtain ⟨U, hU⟩ := upper k hk
  refine ⟨max 8 (max L U), ?_⟩
  intro n hn
  have hl := hL n (by omega)
  have hu := hU n (by omega)
  let base := fun x : ℕ => x * (n-x)
  let F := fun x : ℕ => (base x)^(2^k)+1
  let splits := Finset.Icc 1 (n/2)
  let survivors := splits.filter fun x => F x < (F x).minFac^3
  let reference := splits.filter fun x => F x < (F x).minFac^4
  let paired := (Finset.Icc 1 (n^2/4)).filter fun t =>
    (∃ u : ℕ, 4*t+u^2=n^2) ∧
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ q < p^2 ∧
      2^(k+1) ∣ p-1 ∧ 2^(k+1) ∣ q-1 ∧ p*q=t^(2^k)+1
  change reference.card < 2 * survivors.card at hl
  change 2 * paired.card ≤ reference.card at hu
  by_contra h
  have maps : Set.MapsTo base survivors paired := by
    intro x hx
    obtain ⟨hxI, hs⟩ := Finset.mem_filter.mp hx
    have hxB := Finset.mem_Icc.mp hxI
    have hc : ¬ (F x).Prime := fun hp => h ⟨x, n-x, hxB.1, by omega, by omega, hp⟩
    exact Finset.mem_filter.mpr (paired_of_composite hk (by omega) hxI hs hc)
  have hinj : (survivors : Set ℕ).InjOn base := by
    intro a ha b hb heq
    have haI := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2
    have hbI := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).2
    rcases lt_trichotomy a b with hab | hab | hba
    · exact (ne_of_lt (split_product_strict hab hbI) heq).elim
    · exact hab
    · exact (ne_of_lt (split_product_strict hba haI) heq.symm).elim
  have := Finset.card_le_card_of_injOn base maps hinj
  omega

end OMA.R_OeisA219791_conjecture_2_R1
