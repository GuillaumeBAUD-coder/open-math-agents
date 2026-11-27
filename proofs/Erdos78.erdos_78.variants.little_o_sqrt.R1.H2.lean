import OMAReductions.R_Erdos78_erdos_78_variants_little_o_sqrt_R1

/-! In a monochromatic set the occupied digit classes form a monochromatic
set in the base graph, and each class projects injectively to a monochromatic
set at the next depth. -/

namespace OMA.HexRamsey

private def digit (u : ℕ) : Fin 16 := ⟨u % 16, Nat.mod_lt _ (by decide)⟩

private def residue (x y : Fin 16) : Bool :=
  decide (((x.val + 17 - y.val) % 17) ∈ ([1,2,4,8,9,13,15,16] : List ℕ))

private lemma symmetric : ∀ x y : Fin 16, residue x y = residue y x := by decide +kernel

set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 0 in
private lemma four : ∀ b : Bool, ∀ i j k l : Fin 16,
    i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
    residue i j = b → residue i k = b → residue i l = b →
    residue j k = b → residue j l = b → residue k l ≠ b := by
  intro b
  cases b <;> decide +kernel

private lemma palette (s : Finset (Fin 16)) (b : Bool)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → residue i j = b) : s.card ≤ 3 := by
  by_contra! ht
  obtain ⟨i,hi,j,hj,k,hk,l,hl,ij,ik,il,jk,jl,kl⟩ := Finset.three_lt_card.mp ht
  exact four b i j k l ij ik il jk jl kl (h _ hi _ hj ij) (h _ hi _ hk ik)
    (h _ hi _ hl il) (h _ hj _ hk jk) (h _ hj _ hl jl) (h _ hk _ hl kl)

end OMA.HexRamsey

open Erdos78 OMA.HexRamsey

theorem OMA.solution : OMA.R_Erdos78_erdos_78_variants_little_o_sqrt_R1.H2 := by
  intro color rule d n hn
  let edge (x y : ℕ) := color x y || color y x
  have across {x y : ℕ} (hd : digit x ≠ digit y) : edge x y = residue (digit x) (digit y) := by
    have hne : x ≠ y := fun h => hd (congrArg digit h)
    have hr : x%16 ≠ y%16 := fun h => hd (Fin.ext h)
    change (color x y || color y x) = _
    rw [rule x y, if_neg hne, if_neg hr, rule y x, if_neg hne.symm, if_neg hr.symm]
    change (residue (digit x) (digit y) || residue (digit y) (digit x)) = _
    rw [symmetric (digit y) (digit x), Bool.or_self]
  have within {x y : ℕ} (hne : x ≠ y) (hd : digit x = digit y) :
      edge x y = edge (x/16) (y/16) := by
    have hr := congrArg Fin.val hd
    change x%16 = y%16 at hr
    change (color x y || color y x) = _
    rw [rule x y, if_neg hne, if_pos hr, rule y x, if_neg hne.symm, if_pos hr.symm]
  have bound (depth : ℕ) (s : Finset ℕ) (b : Bool) (small : ∀ x ∈ s, x < 16^depth)
      (mono : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → edge x y = b) : s.card ≤ 3^depth := by
    induction depth generalizing s with
    | zero =>
      have sub : s ⊆ {0} := by
        intro x hx
        have h := small x hx
        simp at h
        simpa using h
      simpa using Finset.card_le_card sub
    | succ j ih =>
      have hp : (s.image digit).card ≤ 3 := by
        apply palette _ b
        intro a ha c hc hac
        obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hc
        rw [← across hac]
        exact mono x hx y hy (fun h => hac (congrArg digit h))
      have fiber (a : Fin 16) (_ : a ∈ s.image digit) :
          (s.filter (fun x => digit x = a)).card ≤ 3^j := by
        let t := s.filter (fun x => digit x = a)
        have inject : Set.InjOn (fun x : ℕ => x/16) (t : Set ℕ) := by
          intro x hx y hy h
          have hr := congrArg Fin.val ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
          change x%16 = y%16 at hr
          change x/16 = y/16 at h
          omega
        change t.card ≤ _
        rw [← Finset.card_image_of_injOn inject]
        apply ih
        · intro z hz
          obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
          have h := small x (Finset.mem_filter.mp hx).1
          rw [pow_succ] at h
          exact (Nat.div_lt_iff_lt_mul (by decide)).mpr h
        · intro z hz w hw hne
          obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
          obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hw
          have xne : x ≠ y := fun h => hne (congrArg (fun v : ℕ => v/16) h)
          rw [← within xne ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)]
          exact mono _ (Finset.mem_filter.mp hx).1 _ (Finset.mem_filter.mp hy).1 xne
      exact (s.card_le_mul_card_image (3^j) fiber).trans (by rw [pow_succ]; gcongr)
  let G := explicitGraph (fun p => color p.2.1 p.2.2) n
  have adj {x y : Fin n} (h : x ≠ y) : G.Adj x y ↔ edge x.val y.val = true := by
    simp [G, explicitGraph, SimpleGraph.fromRel_adj, h, edge]
  have finish (s : Finset (Fin n)) (b : Bool)
      (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → edge x.val y.val = b) : s.card ≤ 3^d := by
    let t := s.image Fin.val
    have ht : t.card = s.card := Finset.card_image_of_injective _ Fin.val_injective
    rw [← ht]
    apply bound d _ b
    · intro v hv
      obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hv
      exact x.isLt.trans_le hn
    · intro v hv w hw hne
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hw
      exact h _ hx _ hy (fun he => hne (congrArg Fin.val he))
  constructor
  · intro s hs
    have h := finish s true (fun x hx y hy hne => (adj hne).mp (hs.isClique hx hy hne))
    have := hs.card_eq
    omega
  · intro s hs
    have h := finish s false (by
      intro x hx y hy hne
      have hnG : ¬ G.Adj x y := (hs.isClique hx hy hne).2
      cases he : edge x.val y.val with
      | false => rfl
      | true => exact (hnG ((adj hne).mpr he)).elim)
    have := hs.card_eq
    omega
