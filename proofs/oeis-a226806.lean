import OMAStatements.S_oeis_a226806

-- Credit: @rleshner

/-!
# A divisibility antichain of sums of powers for each admissible integer

This proves Zhi-Wei Sun's conjecture in OEIS A226806 (May 1, 2023).
Multiplication by four preserves the class of summands and the divisibility
condition. For a large target not divisible by four, we first select one to
three odd summands of the form m·2^k+1. The remainder is divisible by four
and is less than four times every chosen summand. After excluding the two
exceptional remainders, strong induction represents its quotient by four.
A finite table certifies all smaller targets.
-/

namespace SunCover

private theorem dyadicInterval (N : ℕ) (h : 224 ≤ N) :
    ∃ k : ℕ, 5 ≤ k ∧ 7 * 2^k ≤ N ∧ N < 14 * 2^k := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hb : N < 448
    · exact ⟨5, by decide, h, hb⟩
    obtain ⟨k,hk,hl,hu⟩ := ih (N/2) (by omega) (by omega)
    exact ⟨k+1, by omega, by rw [pow_succ]; omega, by rw [pow_succ]; omega⟩

theorem selectTemplate (n : ℕ) (hn : 512 ≤ n) (hr : n%4 ≠ 0) :
    ∃ k R : ℕ, ∃ c : Finset ℕ, 5 ≤ k ∧ 4 ∣ R ∧ R < 4*(2^k+1) ∧
      1 ∈ c ∧ c ⊆ {1,2,4,8} ∧ n = (∑ m ∈ c, (m*2^k+1)) + R := by
  let N := n - n%4
  have hrange : n%4 < 4 := Nat.mod_lt _ (by decide)
  have hN : N + n%4 = n := by dsimp [N]; omega
  have hN4 : 4 ∣ N := by dsimp [N]; omega
  obtain ⟨k,hk,hl,hu⟩ := dyadicInterval N (by omega)
  have hd : 4 ∣ 2^k := (show (2:ℕ)^2 ∣ 2^k from pow_dvd_pow 2 (by omega))
  have h1 : 0 < (2:ℕ)^k := by positivity
  obtain ⟨t,ht⟩ := hd
  rcases (by omega : n%4=1 ∨ n%4=2 ∨ n%4=3) with r|r|r
  · refine ⟨k+2, N - 4*2^k, {1}, by omega, by omega, ?_, by decide, by decide, ?_⟩
    · rw [pow_add]; norm_num; omega
    · simp [pow_add]; omega
  · refine ⟨k+1, N - 6*2^k, {1,2}, by omega, by omega, ?_, by decide, by decide, ?_⟩
    · rw [pow_succ]; omega
    · norm_num [Finset.sum_insert, pow_succ]; omega
  · by_cases hc : N < 11*2^k
    · refine ⟨k, N - 7*2^k, {1,2,4}, hk, by omega, by omega, by decide, by decide, ?_⟩
      norm_num [Finset.sum_insert]; omega
    · refine ⟨k, N - 11*2^k, {1,2,8}, hk, by omega, by omega, by decide, by decide, ?_⟩
      norm_num [Finset.sum_insert]; omega


theorem selectGoodTemplate (n : ℕ) (hn : 512 ≤ n) (hr : n%4 ≠ 0) :
    ∃ k R : ℕ, ∃ c : Finset ℕ, 4 ≤ k ∧ 4 ∣ R ∧ R < 4*(2^k+1) ∧
      c ⊆ {1,2,4,8,16} ∧ R ≠ 4 ∧ R ≠ 16 ∧ n = (∑ m ∈ c, (m*2^k+1)) + R := by
  obtain ⟨k,R,c,hk,h4,hlt,h1,hc,heq⟩ := selectTemplate n hn hr
  by_cases ex : R=4 ∨ R=16
  · let u := 2^(k-1)
    have hu : 16 ≤ u := Nat.pow_le_pow_right (n:=2) (i:=4) (by decide) (by omega)
    have old : 2^k = 2*u := by
      calc
        2^k = 2^((k-1)+1) := congrArg (fun t : ℕ => 2^t) (by omega)
        _ = 2*u := by rw [pow_succ]; exact Nat.mul_comm _ _
    have u4 : 4 ∣ u := (show 2^2 ∣ 2^(k-1) from pow_dvd_pow 2 (by omega))
    let rest := (c.erase 1).image (fun m => 2*m)
    have no1 : 1 ∉ rest := by
      intro h
      obtain ⟨m,_,hm⟩ := Finset.mem_image.mp h
      omega
    have subs : insert 1 rest ⊆ ({1,2,4,8,16} : Finset ℕ) := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl|h
      · decide
      obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp h
      have hmc := hc (Finset.mem_erase.mp hm).2
      simp at hmc ⊢
      omega
    have sumrest : (∑ z ∈ rest, (z*u+1)) = ∑ m ∈ c.erase 1, (m*2^k+1) := by
      dsimp only [rest]
      rw [Finset.sum_image (by intro a _ b _ h; dsimp only at h; omega)]
      apply Finset.sum_congr rfl
      intro m _
      rw [old]
      ring
    have s := Finset.sum_erase_add c (fun m => m*2^k+1) h1
    simp only [one_mul] at s
    refine ⟨k-1,u+R,insert 1 rest,by omega,dvd_add u4 h4,by change u+R < 4*(u+1); omega,subs,by omega,by omega,?_⟩
    change n = (∑ z ∈ insert 1 rest, (z*u+1)) + (u+R)
    rw [Finset.sum_insert no1, one_mul,sumrest]
    omega
  · have sub : c ⊆ ({1,2,4,8,16} : Finset ℕ) := hc.trans (by decide)
    exact ⟨k,R,c,by omega,h4,hlt,sub,by tauto,by tauto,heq⟩

end SunCover

namespace A226806

def Rep (n : ℕ) : Prop := ∃ s : Finset ℕ,
  (∀ x ∈ s, ∃ a b : ℕ, x=2^a+4^b) ∧ ∑ x ∈ s, x = n ∧
  (∀ x ∈ s, ∀ y ∈ s, x ∣ y → x=y)

private def Term (x : ℕ) : Prop := ∃ a b : ℕ, x=2^a+4^b

private def Anti (s : Finset ℕ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ∣ y → x=y

private theorem elem16 (k : ℕ) (hk : 4 ≤ k) : 16 ≤ 2^k :=
  Nat.pow_le_pow_right (n:=2) (by decide) hk

private theorem anchorPower (k m : ℕ) (hm : m ∈ ({1,2,4,8,16}:Finset ℕ)) :
    ∃ p : ℕ, m*2^k=2^p := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl
  · exact ⟨k,by simp⟩
  · exact ⟨k+1,by rw [pow_succ]; ring⟩
  · exact ⟨k+2,by rw [pow_add]; ring⟩
  · exact ⟨k+3,by rw [pow_add]; ring⟩
  · exact ⟨k+4,by rw [pow_add]; ring⟩

private theorem anchor_term (k m : ℕ) (hm : m ∈ ({1,2,4,8,16}:Finset ℕ)) :
    Term (m*2^k+1) := by
  obtain ⟨p,hp⟩ := anchorPower k m hm
  exact ⟨p,0,by simp [hp]⟩

private theorem affine_nodiv {u d q : ℕ} (hu : 16≤u) (hd : 2≤d) (hm : d≤16)
    (e : (d*u+1)=(u+1)*q) : False := by
  have a : q < d := by
    by_contra! h
    have z := Nat.mul_le_mul_left (u+1) h
    nlinarith only [e,z,hd]
  have b : q+1≤d := by omega
  have z := Nat.mul_le_mul_right u b
  nlinarith only [z,e,hu,hm,a]

private theorem anchor_ratio {a b : ℕ} (ha : a∈({1,2,4,8,16}:Finset ℕ))
    (hb : b∈({1,2,4,8,16}:Finset ℕ)) (h : a < b) :
    ∃ d, 2≤d ∧ d≤16 ∧ b=d*a := by
  have cert : ∀ a b : Fin 17, a.val ∈ ({1,2,4,8,16}:Finset ℕ) →
      b.val ∈ ({1,2,4,8,16}:Finset ℕ) → a.val < b.val →
      ∃ d : Fin 17, 2≤d.val ∧ b.val=d.val*a.val := by decide
  have f {a : ℕ} (h : a∈({1,2,4,8,16}:Finset ℕ)) : a<17 := by
    simp at h; omega
  obtain ⟨d,hd,hb'⟩ := cert ⟨a,f ha⟩ ⟨b,f hb⟩ ha hb h
  exact ⟨d,hd,by omega,hb'⟩

private theorem template_anti (u : ℕ) (hu : 16≤u) (c : Finset ℕ)
    (hc : c ⊆ {1,2,4,8,16}) : Anti (c.image (fun m => m*u+1)) := by
  intro x hx y hy hdiv
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
  have order := Nat.le_of_dvd (by positivity) hdiv
  by_cases h : a < b
  · obtain ⟨d,hd,hd',rfl⟩ := anchor_ratio (hc ha) (hc hb) h
    obtain ⟨q,hq⟩ := hdiv
    have ha' : 1≤a := by have := hc ha; simp at this; omega
    exact (affine_nodiv (u:=a*u) (d:=d) (q:=q) (by nlinarith) hd (by omega)
      (by simpa [Nat.mul_assoc] using hq)).elim
  · have b' : b ≤ a := by omega
    have := Nat.mul_le_mul_right u b'
    omega

private theorem template_sum (u : ℕ) (hu : 0<u) (c : Finset ℕ) :
    ∑ x ∈ c.image (fun m => m*u+1), x = ∑ m ∈ c, (m*u+1) := by
  rw [Finset.sum_image]
  intro a _ b _ eq
  exact Nat.eq_of_mul_eq_mul_right hu (by simp only at eq; omega)

private theorem scaled (n : ℕ) (hn : Rep n) :
    ∃ s : Finset ℕ, (∀ x ∈ s, Term x ∧ 4 ∣ x) ∧ ∑ x ∈ s,x = 4*n ∧ Anti s := by
  obtain ⟨s,hs,hval,hnod⟩ := hn
  refine ⟨s.image (fun x => 4*x), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨a,b,rfl⟩ := hs z hz
    refine ⟨⟨a+2,b+1,by rw [pow_add,pow_succ]; ring⟩,dvd_mul_right _ _⟩
  · rw [Finset.sum_image (by intro a _ b _ eq; dsimp only at eq; omega),←Finset.mul_sum,hval]
  · intro x hx y hy hdiv
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
    rw [hnod a ha b hb (Nat.dvd_of_mul_dvd_mul_left (by decide) hdiv)]

private theorem term_pos {x : ℕ} (hx : Term x) : 0<x := by
  obtain ⟨a,b,rfl⟩ := hx
  positivity

private theorem join_sets (a b : Finset ℕ) (na nb : ℕ)
    (hta : ∀ x ∈ a, Term x) (htb : ∀ x ∈ b, Term x)
    (hsa : ∑ x ∈ a,x=na) (hsb : ∑ x ∈ b,x=nb)
    (haa : Anti a) (hbb : Anti b)
    (cross : ∀ x ∈ a, ∀ y ∈ b, ¬x ∣ y ∧ ¬y ∣ x) : Rep (na+nb) := by
  have dis : Disjoint a b := Finset.disjoint_left.mpr (fun _ hx hy =>
    (cross _ hx _ hy).1 (dvd_refl _))
  refine ⟨a∪b, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with h|h
    · exact hta x h
    · exact htb x h
  · rw [Finset.sum_union dis,hsa,hsb]
  · intro x hx y hy dv
    rcases Finset.mem_union.mp hx with ax|bx <;> rcases Finset.mem_union.mp hy with ay|by'
    · exact haa x ax y ay dv
    · exact ((cross x ax y by').1 dv).elim
    · exact ((cross y ay x bx).2 dv).elim
    · exact hbb x bx y by' dv

private theorem small_scaled_cross (x y : ℕ) (hy : 0<y) (hx : x%4=1)
    (hd : 4 ∣ y) (hb : y<4*x) : ¬x∣y ∧ ¬y∣x := by
  refine ⟨?_,fun h => by have := dvd_trans hd h; omega⟩
  rintro ⟨q,rfl⟩
  have qlt : q<4 := by
    by_contra! h
    have := Nat.mul_le_mul_left x h
    omega
  interval_cases q <;> omega

theorem normal_template (k R : ℕ) (c : Finset ℕ) (hk : 4 ≤ k)
    (hc : c ⊆ {1,2,4,8,16}) (hR : 4 ∣ R) (hlt : R < 4*(2^k+1))
    (hrep : Rep (R/4)) : Rep ((∑ m ∈ c, (m*2^k+1))+R) := by
  let u := 2^k
  have hu := elem16 k hk
  have h4 : 4 ∣ u := Nat.pow_dvd_pow 2 (show 2≤k by omega)
  obtain ⟨b,hb,sumB,antiB⟩ := scaled _ hrep
  have qr := Nat.div_mul_cancel hR
  have sumB' : ∑ y ∈ b,y=R := by omega
  apply join_sets (c.image (fun m => m*u+1)) b
  · intro x hx
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hx
    exact anchor_term k m (hc hm)
  · exact fun x hx => (hb x hx).1
  · exact template_sum u (by positivity) c
  · exact sumB'
  · exact template_anti u (by dsimp [u]; omega) c hc
  · exact antiB
  · intro x hx y hy
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hx
    have hm' : 1 ≤ m := by have := hc hm; simp at this; omega
    have hxy : u ≤ m*u := by simpa only [one_mul] using Nat.mul_le_mul_right u hm'
    have hbound : y ≤ R := by
      rw [←sumB']; exact Finset.single_le_sum (f:=id) (fun z _ => Nat.zero_le z) hy
    apply small_scaled_cross _ _ (term_pos (hb y hy).1) _ (hb y hy).2
      (by change R < 4*(u+1) at hlt; omega)
    have := dvd_mul_of_dvd_right h4 m
    omega

theorem scale_four (n : ℕ) (hn : Rep n) : Rep (4*n) := by
  obtain ⟨s,hs,hval,hanti⟩ := scaled n hn
  exact ⟨s,fun x hx => (hs x hx).1,hval,hanti⟩

theorem rep_zero : Rep 0 := by
  refine ⟨∅,by simp,by simp,by simp⟩

end A226806

namespace A226806

private def summand (ab : ℕ × ℕ) : ℕ := 2 ^ ab.1 + 4 ^ ab.2

private def test (n : ℕ) (row : List (ℕ × ℕ)) : Bool :=
  let s := (row.map summand).toFinset
  decide ((∑ x ∈ s, x) = n ∧ ∀ x ∈ s, ∀ y ∈ s, x ∣ y → x = y)

private theorem test_sound (n : ℕ) (row : List (ℕ × ℕ)) (h : test n row) : Rep n := by
  refine ⟨(row.map summand).toFinset, ?_, of_decide_eq_true h⟩
  intro x hx
  obtain ⟨ab, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
  exact ⟨ab.1, ab.2, rfl⟩

private def table : Array (List (ℕ × ℕ)) := #[
[],
  [],
  [(0, 0)],
  [(1, 0)],
  [],
  [(2, 0)],
  [(1, 1)],
  [(0, 0), (2, 0)],
  [(2, 1)],
  [(3, 0)],
  [(0, 0), (1, 0), (2, 0)],
  [(0, 0), (3, 0)],
  [(3, 1)],
  [(2, 0), (2, 1)],
  [(2, 0), (3, 0)],
  [(1, 1), (3, 0)],
  [(0, 0), (2, 0), (3, 0)],
  [(4, 0)],
  [(1, 2)],
  [(0, 0), (4, 0)],
  [(4, 1)],
  [(3, 0), (3, 1)],
  [(2, 0), (4, 0)],
  [(1, 0), (4, 1)],
  [(3, 2)],
  [(2, 1), (4, 0)],
  [(1, 1), (4, 1)],
  [(0, 0), (1, 0), (2, 0), (4, 0)],
  [(2, 1), (4, 1)],
  [(2, 0), (3, 2)],
  [(3, 1), (1, 2)],
  [(1, 0), (2, 1), (4, 1)],
  [(4, 2)],
  [(5, 0)],
  [(2, 0), (3, 1), (4, 0)],
  [(0, 0), (5, 0)],
  [(5, 1)],
  [(2, 0), (4, 2)],
  [(2, 0), (5, 0)],
  [(1, 1), (5, 0)],
  [(0, 0), (2, 0), (5, 0)],
  [(2, 0), (5, 1)],
  [(3, 0), (5, 0)],
  [(2, 0), (1, 1), (4, 2)],
  [(2, 1), (5, 1)],
  [(3, 1), (5, 0)],
  [(2, 0), (2, 1), (5, 0)],
  [(2, 0), (3, 0), (5, 0)],
  [(5, 2)],
  [(4, 0), (4, 2)],
  [(4, 0), (5, 0)],
  [(1, 2), (5, 0)],
  [(4, 1), (4, 2)],
  [(2, 0), (5, 2)],
  [(2, 0), (4, 0), (4, 2)],
  [(1, 0), (4, 1), (4, 2)],
  [(4, 1), (5, 1)],
  [(3, 0), (5, 2)],
  [(2, 0), (4, 0), (5, 1)],
  [(1, 1), (4, 1), (5, 0)],
  [(3, 2), (5, 1)],
  [(2, 0), (3, 2), (4, 2)],
  [(2, 0), (3, 0), (5, 2)],
  [(3, 1), (1, 2), (5, 0)],
  [(2, 1), (4, 1), (5, 1)],
  [(6, 0)],
  [(1, 3)],
  [(0, 0), (6, 0)],
  [(6, 1)],
  [(5, 0), (5, 1)],
  [(0, 0), (1, 0), (6, 0)],
  [(1, 0), (6, 1)],
  [(3, 3)],
  [(2, 0), (6, 1)],
  [(1, 1), (6, 1)],
  [(3, 0), (1, 3)],
  [(2, 1), (6, 1)],
  [(2, 0), (3, 3)],
  [(3, 1), (1, 3)],
  [(1, 0), (2, 1), (6, 1)],
  [(6, 2)],
  [(5, 0), (5, 2)],
  [(4, 0), (6, 0)],
  [(1, 0), (6, 2)],
  [(1, 2), (1, 3)],
  [(4, 1), (6, 0)],
  [(1, 1), (6, 2)],
  [(3, 0), (3, 1), (1, 3)],
  [(4, 1), (6, 1)],
  [(3, 0), (6, 2)],
  [(3, 2), (1, 3)],
  [(1, 0), (4, 1), (6, 1)],
  [(3, 1), (6, 2)],
  [(2, 1), (4, 1), (6, 0)],
  [(2, 0), (4, 0), (3, 3)],
  [(2, 0), (3, 2), (1, 3)],
  [(5, 3)],
  [(4, 0), (6, 2)],
  [(1, 2), (6, 2)],
  [(3, 0), (3, 2), (1, 3)],
  [(4, 2), (6, 1)],
  [(2, 0), (5, 3)],
  [(5, 1), (1, 3)],
  [(1, 0), (4, 2), (6, 1)],
  [(3, 2), (6, 2)],
  [(3, 0), (5, 3)],
  [(2, 0), (5, 0), (6, 1)],
  [(2, 0), (5, 1), (1, 3)],
  [(1, 2), (3, 2), (1, 3)],
  [(2, 0), (4, 2), (3, 3)],
  [(2, 0), (3, 0), (5, 3)],
  [(2, 0), (1, 1), (4, 2), (6, 1)],
  [(4, 2), (6, 2)],
  [(4, 0), (5, 3)],
  [(1, 2), (5, 3)],
  [(1, 0), (4, 2), (6, 2)],
  [(4, 1), (5, 3)],
  [(4, 1), (4, 2), (6, 0)],
  [(2, 0), (4, 0), (5, 3)],
  [(2, 0), (1, 2), (5, 3)],
  [(5, 2), (3, 3)],
  [(2, 0), (5, 2), (6, 1)],
  [(3, 0), (4, 0), (5, 3)],
  [(3, 0), (5, 2), (1, 3)],
  [(3, 1), (4, 2), (6, 2)],
  [(2, 0), (5, 2), (3, 3)],
  [(3, 2), (5, 1), (1, 3)],
  [(2, 0), (3, 0), (4, 0), (5, 3)],
  [(6, 3)],
  [(7, 0)],
  [(4, 0), (5, 0), (6, 2)],
  [(0, 0), (7, 0)],
  [(7, 1)],
  [(2, 0), (6, 3)],
  [(2, 0), (7, 0)],
  [(1, 1), (7, 0)],
  [(0, 0), (2, 0), (7, 0)],
  [(2, 0), (7, 1)],
  [(3, 0), (7, 0)],
  [(2, 0), (1, 1), (6, 3)],
  [(2, 1), (7, 1)],
  [(3, 0), (7, 1)],
  [(2, 0), (2, 1), (7, 0)],
  [(2, 0), (3, 0), (7, 0)],
  [(7, 2)],
  [(4, 0), (6, 3)],
  [(4, 0), (7, 0)],
  [(1, 2), (7, 0)],
  [(4, 1), (6, 3)],
  [(2, 0), (7, 2)],
  [(1, 2), (7, 1)],
  [(1, 0), (4, 1), (6, 3)],
  [(4, 1), (7, 1)],
  [(3, 2), (7, 0)],
  [(2, 0), (4, 0), (7, 1)],
  [(2, 0), (1, 2), (7, 1)],
  [(3, 2), (7, 1)],
  [(2, 0), (3, 2), (6, 3)],
  [(2, 0), (3, 2), (7, 0)],
  [(3, 1), (1, 2), (7, 0)],
  [(2, 1), (4, 1), (7, 1)],
  [(4, 0), (7, 2)],
  [(5, 0), (7, 0)],
  [(4, 0), (1, 2), (6, 3)],
  [(4, 1), (7, 2)],
  [(5, 1), (7, 0)],
  [(2, 0), (4, 0), (7, 2)],
  [(2, 0), (5, 0), (7, 0)],
  [(5, 1), (7, 1)],
  [(2, 0), (4, 2), (7, 1)],
  [(2, 0), (5, 1), (7, 0)],
  [(3, 0), (5, 0), (7, 0)],
  [(4, 1), (3, 2), (6, 3)],
  [(2, 0), (5, 1), (7, 1)],
  [(3, 1), (5, 0), (7, 0)],
  [(2, 0), (2, 1), (5, 0), (7, 0)],
  [(4, 2), (7, 2)],
  [(5, 0), (7, 2)],
  [(4, 0), (4, 2), (7, 0)],
  [(4, 0), (5, 0), (7, 0)],
  [(5, 2), (7, 1)],
  [(2, 0), (4, 2), (7, 2)],
  [(2, 0), (5, 0), (7, 2)],
  [(1, 0), (4, 2), (6, 1), (6, 2)],
  [(4, 1), (4, 2), (7, 1)],
  [(2, 0), (5, 2), (7, 1)],
  [(3, 0), (5, 2), (7, 0)],
  [(2, 0), (4, 0), (5, 1), (7, 0)],
  [(4, 1), (5, 1), (7, 1)],
  [(3, 0), (5, 2), (7, 1)],
  [(2, 0), (3, 0), (5, 2), (6, 3)],
  [(2, 0), (3, 0), (5, 2), (7, 0)],
  [(7, 3)],
  [(6, 0), (6, 3)],
  [(6, 0), (7, 0)],
  [(1, 3), (7, 0)],
  [(6, 1), (6, 3)],
  [(2, 0), (7, 3)],
  [(1, 2), (5, 2), (7, 1)],
  [(1, 0), (6, 1), (6, 3)],
  [(6, 1), (7, 1)],
  [(3, 0), (7, 3)],
  [(2, 0), (6, 1), (7, 0)],
  [(1, 1), (6, 1), (7, 0)],
  [(3, 3), (7, 1)],
  [(2, 0), (6, 1), (7, 1)],
  [(2, 0), (3, 0), (7, 3)],
  [(3, 1), (1, 3), (7, 0)],
  [(6, 2), (6, 3)],
  [(4, 0), (7, 3)],
  [(1, 2), (7, 3)],
  [(1, 0), (6, 2), (6, 3)],
  [(4, 1), (7, 3)],
  [(1, 2), (1, 3), (7, 0)],
  [(2, 0), (4, 0), (7, 3)],
  [(2, 0), (1, 2), (7, 3)],
  [(4, 1), (6, 1), (6, 3)],
  [(2, 0), (6, 1), (7, 2)],
  [(3, 0), (4, 0), (7, 3)],
  [(3, 2), (1, 3), (7, 0)],
  [(3, 1), (6, 2), (6, 3)],
  [(3, 0), (4, 1), (7, 3)],
  [(2, 0), (4, 0), (3, 3), (6, 3)],
  [(2, 0), (3, 0), (4, 0), (7, 3)],
  [(6, 2), (7, 2)],
  [(5, 0), (7, 3)],
  [(4, 0), (6, 0), (7, 2)],
  [(4, 0), (1, 2), (7, 3)],
  [(5, 1), (7, 3)],
  [(2, 0), (5, 3), (6, 3)],
  [(2, 0), (5, 0), (7, 3)],
  [(5, 1), (1, 3), (7, 0)],
  [(4, 1), (6, 1), (7, 2)],
  [(2, 0), (5, 1), (7, 3)],
  [(3, 0), (5, 0), (7, 3)],
  [(2, 0), (5, 0), (6, 1), (7, 0)],
  [(3, 2), (6, 2), (7, 1)],
  [(3, 0), (5, 3), (7, 1)],
  [(2, 0), (3, 0), (5, 3), (6, 3)],
  [(2, 0), (3, 0), (5, 0), (7, 3)],
  [(5, 3), (7, 2)],
  [(4, 0), (6, 2), (7, 2)],
  [(4, 0), (5, 0), (7, 3)],
  [(1, 2), (5, 0), (7, 3)],
  [(4, 1), (5, 3), (6, 3)],
  [(2, 0), (5, 3), (7, 2)],
  [(1, 2), (5, 3), (7, 1)],
  [(2, 0), (4, 0), (5, 0), (7, 3)],
  [(4, 1), (5, 1), (7, 3)],
  [(5, 2), (3, 3), (7, 0)],
  [(2, 0), (4, 0), (5, 1), (7, 3)],
  [(2, 0), (1, 2), (5, 3), (7, 1)],
  [(5, 2), (3, 3), (7, 1)],
  [(2, 0), (5, 2), (6, 1), (7, 1)],
  [(2, 0), (5, 2), (3, 3), (7, 0)],
  [(3, 2), (5, 1), (1, 3), (7, 0)],
  [(4, 2), (6, 2), (7, 2)],
  [(8, 0)],
  [(1, 4)],
  [(0, 0), (8, 0)],
  [(8, 1)],
  [(7, 0), (7, 1)],
  [(2, 0), (8, 0)],
  [(1, 0), (8, 1)],
  [(3, 4)],
  [(2, 1), (8, 0)],
  [(1, 1), (8, 1)],
  [(3, 0), (1, 4)],
  [(2, 1), (8, 1)],
  [(2, 0), (3, 4)],
  [(3, 1), (1, 4)],
  [(1, 0), (2, 1), (8, 1)],
  [(8, 2)],
  [(3, 0), (3, 4)],
  [(4, 0), (8, 0)],
  [(1, 0), (8, 2)],
  [(1, 2), (1, 4)],
  [(2, 0), (8, 2)],
  [(1, 1), (8, 2)],
  [(2, 0), (4, 0), (8, 0)],
  [(1, 0), (2, 0), (8, 2)],
  [(3, 0), (8, 2)],
  [(1, 2), (3, 4)],
  [(2, 0), (1, 1), (8, 2)],
  [(3, 1), (8, 2)],
  [(2, 1), (4, 0), (8, 1)],
  [(2, 0), (3, 0), (8, 2)],
  [(2, 0), (1, 2), (3, 4)],
  [(5, 4)],
  [(4, 2), (8, 0)],
  [(1, 2), (8, 2)],
  [(5, 0), (1, 4)],
  [(4, 1), (8, 2)],
  [(2, 0), (5, 4)],
  [(5, 1), (1, 4)],
  [(1, 0), (4, 1), (8, 2)],
  [(3, 2), (8, 2)],
  [(5, 0), (3, 3), (7, 3)],
  [(2, 0), (5, 1), (8, 0)],
  [(2, 0), (5, 1), (1, 4)],
  [(5, 1), (3, 4)],
  [(2, 0), (3, 2), (8, 2)],
  [(2, 1), (5, 1), (1, 4)],
  [(3, 1), (5, 0), (1, 4)],
  [(4, 2), (8, 2)],
  [(4, 0), (5, 4)],
  [(5, 2), (1, 4)],
  [(1, 0), (4, 2), (8, 2)],
  [(4, 1), (5, 4)],
  [(2, 0), (4, 2), (8, 2)],
  [(2, 0), (4, 0), (5, 4)],
  [(2, 0), (5, 2), (1, 4)],
  [(5, 2), (3, 4)],
  [(2, 0), (5, 1), (8, 2)],
  [(3, 0), (5, 0), (8, 2)],
  [(3, 0), (5, 2), (1, 4)],
  [(3, 1), (4, 2), (8, 2)],
  [(2, 0), (5, 2), (3, 4)],
  [(3, 2), (5, 1), (1, 4)],
  [(2, 0), (3, 0), (5, 0), (8, 2)],
  [(8, 3)],
  [(5, 0), (5, 4)],
  [(6, 0), (8, 0)],
  [(1, 0), (8, 3)],
  [(1, 3), (1, 4)],
  [(6, 1), (8, 0)],
  [(1, 1), (8, 3)],
  [(5, 0), (5, 1), (1, 4)],
  [(6, 1), (8, 1)],
  [(3, 0), (8, 3)],
  [(3, 3), (1, 4)],
  [(1, 0), (6, 1), (8, 1)],
  [(3, 1), (8, 3)],
  [(2, 1), (6, 1), (8, 0)],
  [(2, 0), (3, 3), (8, 0)],
  [(2, 0), (3, 3), (1, 4)],
  [(3, 3), (3, 4)],
  [(4, 0), (8, 3)],
  [(1, 2), (8, 3)],
  [(4, 0), (6, 0), (8, 0)],
  [(6, 2), (8, 1)],
  [(2, 0), (3, 3), (3, 4)],
  [(1, 2), (1, 3), (1, 4)],
  [(1, 0), (6, 2), (8, 1)],
  [(3, 2), (8, 3)],
  [(4, 1), (6, 1), (8, 0)],
  [(1, 1), (6, 2), (8, 1)],
  [(3, 0), (1, 3), (8, 2)],
  [(3, 2), (1, 3), (1, 4)],
  [(2, 0), (3, 3), (8, 2)],
  [(3, 1), (1, 2), (8, 3)],
  [(2, 0), (4, 0), (3, 3), (8, 0)],
  [(6, 2), (8, 2)],
  [(5, 0), (8, 3)],
  [(1, 3), (5, 4)],
  [(1, 0), (6, 2), (8, 2)],
  [(5, 1), (8, 3)],
  [(4, 0), (6, 2), (8, 1)],
  [(2, 0), (5, 3), (8, 0)],
  [(2, 0), (1, 3), (5, 4)],
  [(5, 3), (3, 4)],
  [(2, 0), (6, 1), (5, 4)],
  [(3, 0), (5, 0), (8, 3)],
  [(3, 0), (5, 3), (1, 4)],
  [(3, 1), (6, 2), (8, 2)],
  [(2, 0), (5, 3), (3, 4)],
  [(2, 0), (4, 2), (3, 3), (8, 0)],
  [(2, 0), (3, 0), (5, 3), (8, 0)],
  [(5, 2), (8, 3)],
  [(3, 0), (5, 3), (3, 4)],
  [(4, 0), (5, 0), (8, 3)],
  [(4, 0), (1, 3), (5, 4)],
  [(1, 2), (5, 3), (1, 4)],
  [(2, 0), (5, 3), (8, 2)],
  [(1, 2), (5, 3), (8, 1)],
  [(1, 0), (4, 2), (6, 2), (8, 1)],
  [(4, 1), (6, 1), (5, 4)],
  [(3, 0), (5, 2), (8, 3)],
  [(1, 2), (5, 3), (3, 4)],
  [(2, 0), (5, 1), (1, 3), (8, 2)],
  [(4, 1), (5, 3), (3, 4)],
  [(2, 0), (4, 2), (3, 3), (8, 2)],
  [(2, 0), (3, 0), (5, 3), (8, 2)],
  [(2, 0), (1, 2), (5, 3), (3, 4)],
  [(7, 4)],
  [(6, 0), (8, 3)],
  [(1, 3), (8, 3)],
  [(5, 0), (5, 3), (1, 4)],
  [(6, 1), (8, 3)],
  [(2, 0), (7, 4)],
  [(7, 1), (1, 4)],
  [(1, 0), (6, 1), (8, 3)],
  [(3, 3), (8, 3)],
  [(3, 0), (7, 4)],
  [(2, 0), (7, 1), (8, 0)],
  [(2, 0), (7, 1), (1, 4)],
  [(5, 1), (5, 3), (3, 4)],
  [(2, 0), (6, 3), (3, 4)],
  [(2, 0), (3, 0), (7, 4)],
  [(3, 0), (7, 1), (1, 4)],
  [(6, 3), (8, 2)],
  [(4, 0), (7, 4)],
  [(1, 2), (7, 4)],
  [(1, 0), (6, 3), (8, 2)],
  [(4, 1), (7, 4)],
  [(2, 0), (6, 3), (8, 2)],
  [(2, 0), (4, 0), (7, 4)],
  [(2, 0), (1, 2), (7, 4)],
  [(7, 2), (3, 4)],
  [(2, 0), (7, 1), (8, 2)],
  [(3, 0), (4, 0), (7, 4)],
  [(1, 2), (7, 0), (3, 4)],
  [(3, 1), (6, 3), (8, 2)],
  [(2, 0), (7, 2), (3, 4)],
  [(3, 2), (7, 1), (1, 4)],
  [(2, 0), (3, 0), (4, 0), (7, 4)],
  [(5, 3), (8, 3)],
  [(5, 0), (7, 4)],
  [(4, 0), (7, 2), (8, 0)],
  [(4, 0), (1, 2), (7, 4)],
  [(5, 1), (7, 4)],
  [(2, 0), (6, 3), (5, 4)],
  [(2, 0), (5, 0), (7, 4)],
  [(1, 0), (4, 1), (6, 3), (8, 2)],
  [(4, 1), (7, 1), (8, 2)],
  [(2, 0), (5, 1), (7, 4)],
  [(3, 0), (5, 0), (7, 4)],
  [(2, 0), (1, 2), (7, 1), (8, 2)],
  [(4, 1), (7, 2), (3, 4)],
  [(5, 1), (7, 0), (3, 4)],
  [(2, 0), (4, 0), (7, 2), (3, 4)],
  [(2, 0), (3, 0), (5, 0), (7, 4)],
  [(3, 3), (5, 3), (3, 4)],
  [(4, 0), (5, 3), (8, 3)],
  [(4, 0), (5, 0), (7, 4)],
  [(1, 2), (5, 0), (7, 4)],
  [(4, 1), (6, 3), (5, 4)],
  [(4, 0), (5, 1), (7, 4)],
  [(5, 2), (7, 1), (1, 4)],
  [(2, 0), (4, 0), (5, 0), (7, 4)],
  [(4, 1), (5, 1), (7, 4)],
  [(5, 2), (7, 0), (3, 4)],
  [(2, 0), (4, 0), (5, 1), (7, 4)],
  [(2, 0), (5, 2), (7, 1), (1, 4)],
  [(4, 1), (3, 2), (6, 3), (8, 2)],
  [(2, 0), (4, 2), (7, 2), (3, 4)],
  [(2, 0), (5, 2), (7, 0), (3, 4)],
  [(3, 0), (5, 2), (7, 1), (1, 4)],
  [(6, 3), (8, 3)],
  [(6, 0), (7, 4)],
  [(1, 3), (7, 4)],
  [(1, 0), (6, 3), (8, 3)],
  [(6, 1), (7, 4)],
  [(5, 0), (5, 1), (7, 4)],
  [(2, 0), (7, 3), (8, 0)],
  [(2, 0), (1, 3), (7, 4)],
  [(3, 3), (7, 4)],
  [(2, 0), (6, 1), (7, 4)],
  [(3, 0), (6, 0), (7, 4)],
  [(3, 0), (1, 3), (7, 4)],
  [(3, 1), (6, 3), (8, 3)],
  [(2, 0), (3, 3), (7, 4)],
  [(3, 3), (7, 1), (1, 4)],
  [(2, 0), (3, 0), (7, 3), (8, 0)],
  [(6, 2), (7, 4)],
  [(3, 0), (7, 3), (3, 4)],
  [(4, 0), (6, 0), (7, 4)],
  [(4, 0), (1, 3), (7, 4)],
  [(1, 2), (1, 3), (7, 4)],
  [(2, 0), (7, 3), (8, 2)],
  [(1, 2), (6, 1), (7, 4)],
  [(1, 0), (6, 2), (6, 3), (8, 1)],
  [(4, 1), (6, 1), (7, 4)],
  [(3, 0), (6, 2), (7, 4)],
  [(1, 2), (7, 3), (3, 4)],
  [(2, 0), (1, 2), (6, 1), (7, 4)],
  [(4, 1), (3, 3), (7, 4)],
  [(2, 0), (3, 3), (6, 3), (8, 2)],
  [(2, 0), (3, 0), (7, 3), (8, 2)],
  [(2, 0), (1, 2), (7, 3), (3, 4)],
  [(7, 3), (5, 4)],
  [(4, 0), (6, 2), (7, 4)],
  [(1, 2), (6, 2), (7, 4)],
  [(5, 0), (7, 3), (1, 4)],
  [(4, 1), (7, 3), (8, 2)],
  [(2, 0), (7, 3), (5, 4)],
  [(5, 1), (1, 3), (7, 4)],
  [(2, 0), (1, 2), (7, 3), (8, 2)],
  [(5, 1), (6, 1), (7, 4)],
  [(5, 0), (3, 3), (7, 4)],
  [(2, 0), (5, 0), (6, 1), (7, 4)],
  [(2, 0), (5, 1), (1, 3), (7, 4)],
  [(5, 1), (7, 3), (3, 4)],
  [(2, 0), (5, 1), (6, 1), (7, 4)],
  [(2, 0), (5, 0), (3, 3), (7, 4)],
  [(3, 0), (5, 3), (7, 1), (1, 4)],
  [(5, 2), (6, 3), (8, 3)],
  [(4, 0), (7, 3), (5, 4)],
  [(5, 3), (7, 2), (1, 4)],
  [(4, 0), (1, 2), (6, 2), (7, 4)],
  [(4, 1), (7, 3), (5, 4)],
  [(2, 0), (5, 3), (6, 3), (8, 2)],
  [(2, 0), (4, 0), (7, 3), (5, 4)],
  [(2, 0), (5, 3), (7, 2), (1, 4)],
  [(5, 3), (7, 2), (3, 4)],
  [(2, 0), (5, 1), (7, 3), (8, 2)],
  [(3, 0), (5, 0), (6, 2), (7, 4)],
  [(1, 2), (5, 3), (7, 0), (3, 4)],
  [(4, 1), (5, 1), (6, 1), (7, 4)],
  [(2, 0), (5, 3), (7, 2), (3, 4)],
  [(5, 2), (3, 3), (7, 1), (1, 4)],
  [(2, 0), (3, 0), (5, 0), (7, 3), (8, 2)]]

private def row (n : ℕ) : List (ℕ × ℕ) := (table[n]?).getD []

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
private theorem all_rows : ∀ n : Fin 512, (n : ℕ) < 2 ∨ (n : ℕ) = 4 ∨ test n (row n) := by
  decide +kernel

theorem rep_small (n : ℕ) (h : n < 512) (hn : 2 ≤ n) (hne : n ≠ 4) : Rep n := by
  have hh : n < 2 ∨ n = 4 ∨ test n (row n) := all_rows ⟨n, h⟩
  exact test_sound n _ ((hh.resolve_left (by omega)).resolve_left hne)

end A226806

namespace A226806

theorem all_targets (n : ℕ) (hn : 1 < n) (hne : n ≠ 4) : Rep n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n < 512
    · exact rep_small n small hn hne
    by_cases h4 : n % 4 = 0
    · have hs := scale_four (n/4) (ih (n/4) (by omega) (by omega) (by omega))
      simpa only [show 4*(n/4)=n by omega] using hs
    obtain ⟨k,R,c,hk,hR,hlt,hc,h4R,h16R,heq⟩ := SunCover.selectGoodTemplate n (by omega) h4
    have hrec : Rep (R/4) := by
      by_cases hz : R = 0
      · subst R
        exact rep_zero
      exact ih (R/4) (by omega) (by omega) (by omega)
    rw [heq]
    exact normal_template k R c hk hc hR hlt hrec

end A226806

theorem OMA.solution : type_of% @OMA.S_oeis_a226806.main := by
  intro n hn hne
  exact A226806.all_targets n hn hne
