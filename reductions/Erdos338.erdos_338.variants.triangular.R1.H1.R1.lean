import OMAReductions.R_Erdos338_erdos_338_variants_triangular_R1

-- Credit: @marcusbuffett
/-!
Write N = 8m+3. Every representation by three natural squares has odd
coordinates. A representation with a repeated coordinate comes from x²+2y²
in at most three ways. This separates the ternary lower estimate (Gauss's
class-number formula and Siegel's lower bound) from the binary divisor bound.
-/
namespace OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1

open Filter Finset

/-- Lower estimate for ordered nonnegative three-square representations. -/
def H1 : Prop := ∀ᶠ m : ℕ in atTop,
  let N := 8*m+3
  3 * N.sqrt.sqrt < (((range (N+1)) ×ˢ ((range (N+1)) ×ˢ (range (N+1)))).filter (fun v : ℕ × ℕ × ℕ => v.1^2 + v.2.1^2 + v.2.2^2 = N)).card

/-- Divisor-type bound for the positive definite binary form x²+2y². -/
def H2 : Prop := ∀ᶠ m : ℕ in atTop,
  let N := 8*m+3
  (((range (N+1)) ×ˢ (range (N+1))).filter (fun v : ℕ × ℕ => v.1^2 + 2*v.2^2 = N)).card ≤ N.sqrt.sqrt

theorem distinct_rep {N : ℕ} (h : 3*(((range (N+1)) ×ˢ (range (N+1))).filter (fun v : ℕ × ℕ => v.1^2 + 2*v.2^2 = N)).card < (((range (N+1)) ×ˢ ((range (N+1)) ×ˢ (range (N+1)))).filter (fun v : ℕ × ℕ × ℕ => v.1^2 + v.2.1^2 + v.2.2^2 = N)).card) :
    ∃ a b c : ℕ, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a^2+b^2+c^2=N := by
  classical
  by_contra! bad
  let P := (((range (N+1)) ×ˢ (range (N+1))).filter (fun v : ℕ × ℕ => v.1^2 + 2*v.2^2 = N))
  let T := (((range (N+1)) ×ˢ ((range (N+1)) ×ˢ (range (N+1)))).filter (fun v : ℕ × ℕ × ℕ => v.1^2 + v.2.1^2 + v.2.2^2 = N))
  let A := P.image (fun v => (v.1,v.2,v.2))
  let B := P.image (fun v => (v.2,v.1,v.2))
  let C := P.image (fun v => (v.2,v.2,v.1))
  have sub : T ⊆ A ∪ B ∪ C := by
    rintro ⟨x,y,z⟩ hv
    simp only [T, mem_filter, mem_product, mem_range] at hv
    obtain ⟨⟨hx,hy,hz⟩,he⟩ := hv
    by_cases hxy : x = y
    · subst y
      apply mem_union_right
      apply mem_image.mpr
      refine ⟨(z,x), ?_, rfl⟩
      simp only [P, mem_filter, mem_product, mem_range]
      exact ⟨⟨hz,hx⟩, by nlinarith⟩
    by_cases hxz : x = z
    · subst z
      apply mem_union_left
      apply mem_union_right
      apply mem_image.mpr
      refine ⟨(y,x), ?_, rfl⟩
      simp only [P, mem_filter, mem_product, mem_range]
      exact ⟨⟨hy,hx⟩, by nlinarith⟩
    have hyz : y = z := by by_contra hyz; exact bad x y z hxy hxz hyz he
    subst z
    apply mem_union_left
    apply mem_union_left
    apply mem_image.mpr
    refine ⟨(x,y), ?_, rfl⟩
    simp only [P, mem_filter, mem_product, mem_range]
    exact ⟨⟨hx,hy⟩, by nlinarith⟩
  have hA : A.card ≤ P.card := card_image_le
  have hB : B.card ≤ P.card := card_image_le
  have hC : C.card ≤ P.card := card_image_le
  have hAB := card_union_le A B
  have hABC := card_union_le (A ∪ B) C
  have hc := card_le_card sub
  change 3*P.card < T.card at h
  omega

lemma odd_square {u : ℕ} (hu : u % 2 = 1) :
    8*(u/2 * (u/2+1) / 2)+1 = u^2 := by
  have ht := Nat.div_mul_cancel (Nat.two_dvd_mul_add_one (u/2))
  have h : u = 2*(u/2)+1 := by omega
  calc 8 * (u/2 * (u/2+1) / 2) + 1 = (2*(u/2)+1)^2 := by nlinarith
    _ = u^2 := by rw [← h]

lemma odd_coords {a b c m : ℕ} (he : a^2+b^2+c^2=8*m+3) :
    a%2=1 ∧ b%2=1 ∧ c%2=1 := by
  have hr : ((a%8)^2 + (b%8)^2 + (c%8)^2) % 8 = 3 := by
    calc
      _ = (a^2+b^2+c^2)%8 := by
        have ha : a % 8 ≡ a [MOD 8] := Nat.mod_modEq _ _
        have hb : b % 8 ≡ b [MOD 8] := Nat.mod_modEq _ _
        have hc : c % 8 ≡ c [MOD 8] := Nat.mod_modEq _ _
        exact ((ha.pow 2).add (hb.pow 2)).add (hc.pow 2)
      _ = 3 := by rw [he]; omega
  have check : ∀ x y z : Fin 8, (x.val^2+y.val^2+z.val^2)%8=3 →
      x.val%2=1 ∧ y.val%2=1 ∧ z.val%2=1 := by decide
  have hh := check ⟨a%8, Nat.mod_lt _ (by decide)⟩
    ⟨b%8, Nat.mod_lt _ (by decide)⟩ ⟨c%8, Nat.mod_lt _ (by decide)⟩ hr
  dsimp at hh
  omega

theorem main : H1 → H2 → OMA.R_Erdos338_erdos_338_variants_triangular_R1.H1 := by
  intro h₁ h₂
  unfold H1 at h₁
  unfold H2 at h₂
  change ∀ᶠ m : ℕ in atTop, ∃ S : Finset ℕ, _ ∧ _ ∧ _
  filter_upwards [h₁,h₂] with m hl hu
  dsimp only at hl hu
  obtain ⟨a,b,c,hab,hac,hbc,he⟩ := distinct_rep ((Nat.mul_le_mul_left 3 hu).trans_lt hl)
  obtain ⟨ha,hb,hc⟩ := odd_coords he
  have ea := odd_square ha
  have eb := odd_square hb
  have ec := odd_square hc
  let tri (j : ℕ) := j*(j+1)/2
  have ne {x y : ℕ} (hx : x%2=1) (hy : y%2=1) (hxy : x ≠ y) :
      tri (x/2) ≠ tri (y/2) := by
    intro h
    have ex : 8*tri (x/2)+1 = x^2 := odd_square hx
    have ey : 8*tri (y/2)+1 = y^2 := odd_square hy
    have eq : x^2 = y^2 := by rw [← ex, ← ey, h]
    exact hxy (Nat.pow_left_injective (by decide : 2 ≠ 0) eq)
  have nab := ne ha hb hab
  have nac := ne ha hc hac
  have nbc := ne hb hc hbc
  refine ⟨{tri (a/2), tri (b/2), tri (c/2)}, ?_, ?_, ?_⟩
  · intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl|rfl|rfl
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · simp [nab,nac,nbc]
  · simp [nab,nac,nbc]
    dsimp [tri]
    omega

end OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1
