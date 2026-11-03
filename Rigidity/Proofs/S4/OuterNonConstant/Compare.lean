import Rigidity.Proofs.S4.OuterNonConstant.Defs
import Rigidity.Proofs.S3.Divergence

/-!
# Lemma 4.8, conditional form: comparison of two environments

If two corrected planes `ℓ₁`, `ℓ₂` of slope `q` live on clusters of two environments `ω₁`, `ω₂`
whose bonds differ only at bonds whose endpoints lie in `𝒞₂` at the level `c` of `ℓ₂`, and
`𝒞₁ \ 𝒞₂` is finite, then `ℓ₁` is constant on the sites where `ℓ₂` is `c` or absent
(Liouville theorem at order zero on `𝒞₁`).
-/

namespace Rigidity.Proofs.S4.OuterNonConstant

open LatticeProb LatticeProb.Percolation LatticeProb.Network Rigidity.Section4 Rigidity.Steps.S4

variable {d : ℕ}

/-- **Comparison of two environments.** The function equal to `ℓ₂` on `𝒞₁ ∩ 𝒞₂` and to `c` on
`𝒞₁ \ 𝒞₂` is harmonic on `𝒞₁` with slope `q`; the Liouville theorem on `𝒞₁` applied to the
difference with `ℓ₁` makes `ℓ₁` constant on the sites where `ℓ₂ = c` or which are not in `𝒞₂`. -/
theorem exists_const_of_compare {ω₁ ω₂ : Configuration d} {q : Fin d → ℝ}
    (C₁ : OpenComponent ω₁) (C₂ : OpenComponent ω₂)
    (hliou : ∀ v : C₁ → ℝ, (∀ x, componentLaplacian C₁ v x = 0) →
      componentSlopeAsymptotics C₁ 0 v → ∃ c : ℝ, ∀ x, v x = c)
    {ℓ₁ : C₁ → ℝ} (hℓ₁ : IsCorrectedPlane C₁ q ℓ₁) {ℓ₂ : C₂ → ℝ}
    (hℓ₂ : IsCorrectedPlane C₂ q ℓ₂) (c : ℝ)
    (hdiff : ∀ z w, Xor ((openGraph ω₁).Adj z w) ((openGraph ω₂).Adj z w) →
      ∀ hz : z ∈ C₂.supp, ℓ₂ ⟨z, hz⟩ = c)
    (hfin : (C₁.supp \ C₂.supp).Finite) :
    ∃ k : ℝ, ∀ x : C₁, (∀ hx : x.1 ∈ C₂.supp, ℓ₂ ⟨x.1, hx⟩ = c) → ℓ₁ x = k := by
  classical
  let g : Vertex d → ℝ := fun y => if y ∈ C₂.supp then Section3.extend C₂ ℓ₂ y else c
  let v : C₁ → ℝ := fun x => g x.1
  have hextv : ∀ y, y ∈ C₁.supp → Section3.extend C₁ v y = g y := fun y hy => dif_pos hy
  have hgin : ∀ y (hy : y ∈ C₂.supp), g y = ℓ₂ ⟨y, hy⟩ := fun y hy => by
    show (if y ∈ C₂.supp then Section3.extend C₂ ℓ₂ y else c) = _
    rw [if_pos hy]
    exact dif_pos hy
  have hgout : ∀ y, y ∉ C₂.supp → g y = c := fun y hy => if_neg hy
  have hℓ₂h := ((mem_harmonicGrowthSpace_iff _ _ _).mp hℓ₂.1).1
  have hℓ₁h := ((mem_harmonicGrowthSpace_iff _ _ _).mp hℓ₁.1).1
  -- both values `g` at the endpoints of a bond where the adjacencies differ are `c`
  have hbond : ∀ z w, Xor ((openGraph ω₁).Adj z w) ((openGraph ω₂).Adj z w) → g z = c ∧ g w = c := by
    intro z w hx
    have hx' : Xor ((openGraph ω₁).Adj w z) ((openGraph ω₂).Adj w z) := by
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1.symm, fun h => h2 h.symm⟩
      · exact Or.inr ⟨h1.symm, fun h => h2 h.symm⟩
    refine ⟨?_, ?_⟩
    · by_cases hz : z ∈ C₂.supp
      · rw [hgin z hz]; exact hdiff z w hx hz
      · exact hgout z hz
    · by_cases hw : w ∈ C₂.supp
      · rw [hgin w hw]; exact hdiff w z hx' hw
      · exact hgout w hw
  -- `v` is harmonic on `𝒞₁`
  have hv : ∀ x, componentLaplacian C₁ v x = 0 := by
    rintro ⟨x, hx⟩
    rw [Rigidity.Proofs.S3.componentLaplacian_eq_sum_lattice C₁ v x hx, hextv x hx]
    by_cases hx' : x ∈ C₂.supp
    · have h0 := hℓ₂h ⟨x, hx'⟩
      rw [Rigidity.Proofs.S3.componentLaplacian_eq_sum_lattice C₂ ℓ₂ x hx'] at h0
      refine (Finset.sum_congr rfl fun y _ => ?_).trans h0
      by_cases h1 : (openGraph ω₁).Adj x y
      · have hyC : y ∈ C₁.supp := C₁.mem_supp_of_adj_mem_supp hx h1
        rw [hextv y hyC, if_pos h1]
        by_cases h2 : (openGraph ω₂).Adj x y
        · have hy' : y ∈ C₂.supp := C₂.mem_supp_of_adj_mem_supp hx' h2
          rw [if_pos h2, hgin y hy', hgin x hx']
          simp only [Section3.extend, dif_pos hy', dif_pos hx']
        · obtain ⟨e1, e2⟩ := hbond x y (Or.inl ⟨h1, h2⟩)
          rw [if_neg h2, e1, e2, sub_self]
      · rw [if_neg h1]
        by_cases h2 : (openGraph ω₂).Adj x y
        · have hy' : y ∈ C₂.supp := C₂.mem_supp_of_adj_mem_supp hx' h2
          obtain ⟨e1, e2⟩ := hbond x y (Or.inr ⟨h2, h1⟩)
          rw [if_pos h2]
          have f1 : Section3.extend C₂ ℓ₂ y = g y := by
            rw [hgin y hy']; exact dif_pos hy'
          have f2 : Section3.extend C₂ ℓ₂ x = g x := by
            rw [hgin x hx']; exact dif_pos hx'
          rw [f1, f2, e1, e2, sub_self]
        · rw [if_neg h2]
    · refine Finset.sum_eq_zero fun y _ => ?_
      split_ifs with h1
      · have hyC : y ∈ C₁.supp := C₁.mem_supp_of_adj_mem_supp hx h1
        rw [hextv y hyC, hgout x hx']
        by_cases hy' : y ∈ C₂.supp
        · have h2 : ¬ (openGraph ω₂).Adj x y := fun h2 =>
            hx' (C₂.mem_supp_of_adj_mem_supp hy' h2.symm)
          obtain ⟨-, e2⟩ := hbond x y (Or.inl ⟨h1, h2⟩)
          rw [e2, sub_self]
        · rw [hgout y hy', sub_self]
      · rfl
  -- `ℓ₁ - v` is sublinear
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ x : C₁, x.1 ∉ C₂.supp → |ℓ₁ x - c| ≤ K := by
    refine ⟨∑ y ∈ hfin.toFinset, |Section3.extend C₁ ℓ₁ y - c|, fun x hx => ?_⟩
    have hmem : x.1 ∈ hfin.toFinset := (Set.Finite.mem_toFinset _).mpr ⟨x.2, hx⟩
    have := Finset.single_le_sum (f := fun y => |Section3.extend C₁ ℓ₁ y - c|)
      (fun _ _ => abs_nonneg _) hmem
    have hx1 : Section3.extend C₁ ℓ₁ x.1 = ℓ₁ x := dif_pos x.2
    rw [hx1] at this
    exact this
  have hsl : componentSlopeAsymptotics C₁ 0 (fun x => ℓ₁ x - v x) := by
    intro ε hε
    obtain ⟨R₁, hR₁, h1⟩ := hℓ₁.2 (ε / 2) (by positivity)
    obtain ⟨R₂, hR₂, h2⟩ := hℓ₂.2 (ε / 2) (by positivity)
    refine ⟨max (max R₁ R₂) (K / ε), lt_max_of_lt_left (lt_max_of_lt_left hR₁), ?_⟩
    intro r hr x hx
    simp only [max_le_iff] at hr
    obtain ⟨⟨hr1, hr2⟩, hr3⟩ := hr
    have hs0 : componentSlope C₁ 0 x = 0 := by simp [componentSlope]
    beta_reduce
    rw [hs0, sub_zero]
    by_cases hx' : x.1 ∈ C₂.supp
    · have hvx : v x = ℓ₂ ⟨x.1, hx'⟩ := hgin x.1 hx'
      have hb' : (⟨x.1, hx'⟩ : C₂) ∈ componentEuclideanBall C₂ 0 r := by
        rw [mem_componentEuclideanBall] at hx ⊢
        exact hx
      have e1 := h1 r hr1 x hx
      have e2 := h2 r hr2 _ hb'
      have hsl : componentSlope C₂ q ⟨x.1, hx'⟩ = componentSlope C₁ q x := rfl
      rw [hsl] at e2
      rw [hvx]
      calc |ℓ₁ x - ℓ₂ ⟨x.1, hx'⟩|
          = |(ℓ₁ x - componentSlope C₁ q x) - (ℓ₂ ⟨x.1, hx'⟩ - componentSlope C₁ q x)| := by
            ring_nf
        _ ≤ |ℓ₁ x - componentSlope C₁ q x| + |ℓ₂ ⟨x.1, hx'⟩ - componentSlope C₁ q x| :=
          abs_sub _ _
        _ ≤ ε / 2 * r + ε / 2 * r := add_le_add e1 e2
        _ = ε * r := by ring
    · have hvx : v x = c := hgout x.1 hx'
      rw [hvx]
      calc |ℓ₁ x - c| ≤ K := hK x hx'
        _ ≤ ε * r := by
          have := (div_le_iff₀ hε).mp hr3
          linarith
  obtain ⟨k, hk⟩ := hliou _
    (fun x => by rw [Rigidity.Steps.S3.componentLaplacian_sub, hℓ₁h x, hv x, sub_zero]) hsl
  refine ⟨k + c, fun x hx => ?_⟩
  have := hk x
  have hvx : v x = c := by
    by_cases hx' : x.1 ∈ C₂.supp
    · rw [show v x = g x.1 from rfl, hgin x.1 hx']; exact hx hx'
    · exact hgout x.1 hx'
  simp only [hvx] at this
  linarith

end Rigidity.Proofs.S4.OuterNonConstant
