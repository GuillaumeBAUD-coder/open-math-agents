import FormalConjectures.ErdosProblems.«368»
import Mathlib.NumberTheory.Pell
/-! Smooth coordinates in a Pell sequence grow at most linearly with their index. -/
open Pell Pell.Solution₁ Finset Filter
namespace SmoothPell
variable {d : ℤ}

lemma expansion (a : Solution₁ d) (k : ℕ) : ∃ u v : ℤ,
    (a^(k+1)).x = a.x^(k+1) + a.y^2*u ∧
    (a^(k+1)).y = a.y*((k+1:ℕ)*a.x^k+a.y^2*v) := by
  induction k with
  | zero => exact ⟨0,0,by simp,by simp⟩
  | succ k ih =>
    obtain ⟨u,v,hu,hv⟩ := ih
    refine ⟨u*a.x+d*((k+1:ℕ)*a.x^k+a.y^2*v), u+v*a.x, ?_, ?_⟩
    · rw [pow_succ a,x_mul,hu,hv,pow_succ a.x]; ring
    · rw [pow_succ a,y_mul,hu,hv,pow_succ a.x]; push_cast; ring

lemma y_dvd_pow (a : Solution₁ d) (k : ℕ) : a.y ∣ (a^k).y := by
  cases k with
  | zero => simp
  | succ k =>
    obtain ⟨_,v,_,hy⟩ := expansion a k
    exact ⟨_,hy⟩

lemma posY {a : Solution₁ d} (hx : 0 < a.x) (hy : 0 < a.y) {n : ℕ} (hn : n ≠ 0) :
    0 < (a^n).y := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact y_pow_succ_pos hx hy _

lemma val_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (a : Solution₁ d)
    (hx : 0 < a.x) (hy : 0 < a.y) (hd : (p:ℤ) ∣ a.y) :
    (a^q).y.natAbs.factorization p = a.y.natAbs.factorization p + q.factorization p := by
  have hpz := Nat.prime_iff_prime_int.mp hp
  have hpx : ¬ (p:ℤ) ∣ a.x := by
    intro hh
    apply hpz.not_dvd_one
    rw [← a.prop]
    exact dvd_sub (dvd_pow hh (by decide : 2 ≠ 0)) ((dvd_pow hd (by decide : 2 ≠ 0)).mul_left _)
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne_zero
  obtain ⟨_,v,_,hyq⟩ := expansion a k
  change q = k+1 at hk
  rw [← hk] at hyq
  have hxy := posY hx hy hq.ne_zero
  have hfac {z : ℤ} (hz : (a^q).y=a.y*z) : (a^q).y.natAbs.factorization p =
      a.y.natAbs.factorization p + z.natAbs.factorization p := by
    rw [hz, Int.natAbs_mul,Nat.factorization_mul (Int.natAbs_ne_zero.mpr hy.ne')
      (Int.natAbs_ne_zero.mpr (by intro he; rw [hz,he,mul_zero] at hxy; omega))]
    rfl
  rw [hfac hyq]
  congr 1
  obtain ⟨w,hw⟩ := hd
  have hxn : ¬ (p:ℤ) ∣ a.x^k := fun hh => hpx (hpz.dvd_of_dvd_pow hh)
  clear hk
  by_cases he : p = q
  · subst q
    have hz : (p:ℤ)*a.x^k + a.y^2*v = p*(a.x^k+p*w^2*v) := by rw [hw]; ring
    have hn : ¬ (p:ℤ) ∣ a.x^k+p*w^2*v := fun hh =>
      hxn ((dvd_add_left (by exact ⟨w^2*v,by ring⟩ : (p:ℤ) ∣ p*w^2*v)).mp hh)
    have hne : a.x^k+(p:ℤ)*w^2*v ≠ 0 := fun hh => hn (hh ▸ dvd_zero _)
    rw [hz,Int.natAbs_mul,Int.natAbs_natCast,Nat.factorization_mul hp.ne_zero
      (Int.natAbs_ne_zero.mpr hne),Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd
      (fun hh => hn (Int.natCast_dvd.mpr hh)),add_zero]
  · have hnq : ¬p ∣ q := fun hh => he ((Nat.dvd_prime hq).mp hh |>.resolve_left hp.ne_one)
    have hn : ¬ (p:ℤ) ∣ (q:ℤ)*a.x^k+a.y^2*v := by
      intro hh
      have h1 := (dvd_add_left (((dvd_pow (show (p:ℤ) ∣ a.y from ⟨w,hw⟩) (by decide : 2 ≠ 0))).mul_right v)).mp hh
      exact (hpz.dvd_or_dvd h1).elim (fun hq => hnq (Int.natCast_dvd_natCast.mp hq)) hxn
    rw [Nat.factorization_eq_zero_of_not_dvd (fun hh => hn (Int.natCast_dvd.mpr hh)),
      Nat.factorization_eq_zero_of_not_dvd hnq]

lemma val_power {p : ℕ} (hp : p.Prime) (n : ℕ) (hn : n ≠ 0) (a : Solution₁ d)
    (hx : 0 < a.x) (hy : 0 < a.y) (hd : (p:ℤ) ∣ a.y) :
    (a^n).y.natAbs.factorization p = a.y.natAbs.factorization p + n.factorization p := by
  induction n using Nat.recOnMul generalizing a with
  | zero => contradiction
  | one => simp
  | prime q hq => exact val_prime hp hq a hx hy hd
  | mul n m ih jh =>
    have ⟨hn,hm⟩ := mul_ne_zero_iff.mp hn
    rw [pow_mul,jh hm _ (x_pow_pos hx n) (posY hx hy hn) (hd.trans (y_dvd_pow a n)),
      ih hn _ hx hy hd,Nat.factorization_mul hn hm,Finsupp.add_apply,add_assoc]

lemma growth (a : Solution₁ d) (h : IsFundamental a) (n : ℕ) :
    (n:ℤ)^2 ≤ 4*(a^n).y := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hx := x_pow_pos h.x_pos n
    have hy : 0 ≤ (a^n).y := by cases n with
                                 | zero => simp
                                 | succ n => exact (y_pow_succ_pos h.x_pos h.2.1 n).le
    have hx2 : 2 ≤ a.x := h.1
    have hm := mul_le_mul_of_nonneg_left hx2 hy
    have h1 := Int.mul_pos hx h.2.1
    rw [pow_succ a,y_mul]
    push_cast
    nlinarith [sq_nonneg ((n:ℤ)-1)]

lemma bounded_index {a : Solution₁ d} (h : IsFundamental a) (K : ℕ) :
    ∃ B : ℕ, ∀ n : ℕ, 0 < n → (a^n).y.natAbs.primeFactors ⊆ range K → n ≤ B := by
  classical
  let rank := fun p : ℕ => if he : ∃ k : ℕ, 0 < k ∧ (p:ℤ) ∣ (a^k).y then he.choose else 1
  have rankpos (p : ℕ) : 0 < rank p := by
    dsimp [rank]; split <;> rename_i hh
    · exact hh.choose_spec.1
    · decide
  let m := ∏ p ∈ range K, rank p
  have hm : 0 < m := prod_pos (fun p _ => rankpos p)
  have hmy := posY h.x_pos h.2.1 hm.ne'
  refine ⟨4*(a^m).y.natAbs,fun n hn hs => ?_⟩
  have hny := posY h.x_pos h.2.1 hn.ne'
  have divides : (a^n).y.natAbs ∣ (a^m).y.natAbs*n := by
    apply (Nat.factorization_le_iff_dvd (Int.natAbs_ne_zero.mpr hny.ne')
      (Nat.mul_ne_zero (Int.natAbs_ne_zero.mpr hmy.ne') hn.ne')).mp
    intro p
    by_cases hf : p ∈ (a^n).y.natAbs.primeFactors
    swap
    · simp [Finsupp.notMem_support_iff.mp (show p ∉ (a^n).y.natAbs.factorization.support from hf)]
    obtain ⟨hp,hnp,_⟩ := Nat.mem_primeFactors.mp hf
    have ex : ∃ k : ℕ, 0 < k ∧ (p:ℤ) ∣ (a^k).y := ⟨n,hn,Int.natCast_dvd.mpr hnp⟩
    have hd : (p:ℤ) ∣ (a^(rank p)).y := by simpa [rank,dif_pos ex] using ex.choose_spec.2
    have hdiv : rank p ∣ m := dvd_prod_of_mem rank (hs hf)
    obtain ⟨j,hj⟩ := hdiv
    have hd' : (p:ℤ) ∣ (a^m).y := by rw [hj,pow_mul]; exact hd.trans (y_dvd_pow _ _)
    have hbig := posY h.x_pos h.2.1 (Nat.mul_ne_zero hn.ne' hm.ne')
    have hnd : (a^n).y.natAbs ∣ (a^(n*m)).y.natAbs := by
      rw [pow_mul]; exact Int.natAbs_dvd_natAbs.mpr (y_dvd_pow _ _)
    have hh := (Nat.factorization_le_iff_dvd (Int.natAbs_ne_zero.mpr hny.ne')
      (Int.natAbs_ne_zero.mpr hbig.ne')).mpr hnd p
    rw [Nat.mul_comm n m,pow_mul,val_power hp n hn.ne' _ (x_pow_pos h.x_pos _) hmy hd'] at hh
    rwa [Nat.factorization_mul (Int.natAbs_ne_zero.mpr hmy.ne') hn.ne',Finsupp.add_apply]
  have hh := Nat.le_of_dvd (Nat.mul_pos (Int.natAbs_pos.mpr hmy.ne') hn) divides
  have hg : n^2 ≤ 4*(a^n).y.natAbs := by
    have hr := growth a h n
    rw [← Int.natAbs_of_nonneg hny.le] at hr
    exact_mod_cast hr
  apply Nat.le_of_mul_le_mul_right (c := n) _ hn
  nlinarith only [hh,hg]

lemma bounded_x (d : ℤ) (K : ℕ) : ∃ B : ℕ, ∀ a : Solution₁ d,
    1 < a.x → 0 < a.y → a.y.natAbs.primeFactors ⊆ range K → a.x.natAbs ≤ B := by
  classical
  by_cases hex : ∃ g : Solution₁ d, IsFundamental g
  · obtain ⟨g,hg⟩ := hex
    obtain ⟨B,hB⟩ := bounded_index hg K
    refine ⟨(range (B+1)).sup (fun i => (g^i).x.natAbs),fun a hx hy hs => ?_⟩
    obtain ⟨n,rfl⟩ := hg.eq_pow_of_nonneg (by omega) hy.le
    have hn : 0 < n := by
      cases n with
      | zero => simp at hx
      | succ n => omega
    exact le_sup (f := fun i => (g^i).x.natAbs) (mem_range.mpr (Nat.lt_succ_of_le (hB n hn hs)))
  · refine ⟨0, fun a hx _ _ => ?_⟩
    exact (hex (IsFundamental.exists_of_not_isSquare (d_pos_of_one_lt_x hx)
      (d_nonsquare_of_one_lt_x hx))).elim

end SmoothPell

theorem OMA.solution : type_of% @Erdos368.erdos_368.variants.tendsto := by
  classical
  rw [Filter.tendsto_atTop_atTop]
  intro K
  let D := ∏ t ∈ Icc 1 K, t
  choose B hB using fun (e : ℕ) => SmoothPell.bounded_x (4*(e:ℤ)) K
  let C := (range (D+1)).sup B
  refine ⟨C+1,fun n hn => ?_⟩
  by_contra! hf
  have hn0 : 0 < n := by omega
  have hN : 0 < n*(n+1) := by positivity
  have hs {p : ℕ} (hp : p.Prime) (hd : p ∣ n*(n+1)) : p < K :=
    lt_of_le_of_lt (Nat.le_maxPrimeFac hN.ne' hp hd) hf
  obtain ⟨e,b,he,hb,heq,hsq⟩ := Nat.sq_mul_squarefree_of_pos hN
  have hd : e ∣ n*(n+1) := heq ▸ dvd_mul_left e (b^2)
  have hbdiv : b ∣ n*(n+1) := heq ▸ (dvd_pow_self b (by decide : 2 ≠ 0)).mul_right e
  have heD : e ≤ D := by
    rw [← Nat.prod_primeFactors_of_squarefree hsq]
    apply prod_le_prod_of_subset_of_one_le
    · intro p hp
      obtain ⟨hp,hpe,_⟩ := Nat.mem_primeFactors.mp hp
      exact mem_Icc.mpr ⟨hp.pos,(hs hp (hpe.trans hd)).le⟩
    · intro p _; exact Nat.zero_le p
    · intro p hp _; exact (mem_Icc.mp hp).1
  have heqZ : (b:ℤ)^2*e = (n:ℤ)*(n+1) := by exact_mod_cast heq
  let a : Solution₁ (4*(e:ℤ)) := Solution₁.mk (2*(n:ℤ)+1) b (by nlinarith only [heqZ])
  have hx : 1 < a.x := by change 1 < 2*(n:ℤ)+1; omega
  have hy : 0 < a.y := by change 0 < (b:ℤ); exact_mod_cast hb
  have hpr : a.y.natAbs.primeFactors ⊆ range K := by
    change b.primeFactors ⊆ range K
    intro p hp
    obtain ⟨hp,hpb,_⟩ := Nat.mem_primeFactors.mp hp
    exact mem_range.mpr (hs hp (hpb.trans hbdiv))
  have hbound := (hB e a hx hy hpr).trans
    (le_sup (f := B) (mem_range.mpr (Nat.lt_succ_of_le heD)))
  change (2*(n:ℤ)+1).natAbs ≤ C at hbound
  omega
