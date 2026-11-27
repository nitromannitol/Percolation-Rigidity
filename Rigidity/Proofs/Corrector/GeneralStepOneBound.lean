import Rigidity.Proofs.Corrector.GeneralStepOneMoments

/-!
# Step 1 of Lemma 3.3 of Dario on `ℤᵈ`, bond by bond, with the partition of the open flip

`flipTermOne_sq_le` bounds `T₁(e)²` through boxes around an endpoint `a` of `e` of radii comparable
to the side `s₀` of the partition cube of `ω^{e,0}` at `a`. Applying Lemma 3.5
(`ResamplePartitionBound C₀ C`) with the roles of the flips exchanged, `s₀ ≤ C s₁` with `s₁` the
side of the partition cube of `ω^{e,1}` at `a`; since all the factors grow with the boxes,
`flipTermOne_sq_le_of_bound` bounds `T₁(e)²` by quantities of the single configuration
`ω^{e,1}`: boxes of radii `C₀ C s₁` and `(C₀ C s₁ + 1) + 3 C² s₁` and the Lipschitz bounds of its
corrector. The endpoint is `bondBase e`, the first point of a presentation of the bond. This is
the planar `Rigidity.Corrector.flipTermOne_sq_le_of_bound` on `ℤᵈ`.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Poincare.GeneralDim
open scoped Classical

variable {d : ℕ}

/-- The first point of a presentation `e = {x, y}` of the bond. -/
noncomputable def bondBase (e : Bond d) : Vertex d := Classical.choose e.2

theorem bondBase_mem (e : Bond d) : bondBase e ∈ e.1 := by
  obtain ⟨y, hy, -⟩ := Classical.choose_spec e.2
  have key : ∀ (b : Sym2 (Vertex d)) (u v : Vertex d), b = s(u, v) → u ∈ b := by
    rintro b u v rfl
    exact Sym2.mem_mk_left _ _
  exact key _ _ _ hy

theorem supBox_subset_of_le (a : Vertex d) {ρ ρ' : ℕ} (h : ρ ≤ ρ') : supBox a ρ ⊆ supBox a ρ' :=
  fun z hz => by
    rw [mem_supBox] at hz ⊢
    exact fun i => (hz i).trans (by exact_mod_cast h)

/-- The bound of Step 1 grows with the boxes. -/
theorem stepOne_box_bound_mono (a : Vertex d) {ρ ρ' R R' : ℕ} (hρ : ρ ≤ ρ') (hR : R ≤ R')
    (φ Λ : Vertex d → ℝ) (hΛ0 : ∀ z, 0 ≤ Λ z) :
    ((supBox a ρ).card : ℝ) * (∑ y ∈ supBox a ρ, φ y ^ 2) * (4 * d * ∑ z ∈ supBox a R, Λ z) ^ 2 ≤
      (supBox a ρ').card * (∑ y ∈ supBox a ρ', φ y ^ 2) *
        (4 * d * ∑ z ∈ supBox a R', Λ z) ^ 2 := by
  have hB := supBox_subset_of_le a hρ
  have hB' := supBox_subset_of_le a hR
  have hcard : ((supBox a ρ).card : ℝ) ≤ (supBox a ρ').card := by
    exact_mod_cast Finset.card_le_card hB
  have hΦ : ∑ y ∈ supBox a ρ, φ y ^ 2 ≤ ∑ y ∈ supBox a ρ', φ y ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hB fun _ _ _ => sq_nonneg _
  have hΛs : ∑ z ∈ supBox a R, Λ z ≤ ∑ z ∈ supBox a R', Λ z :=
    Finset.sum_le_sum_of_subset_of_nonneg hB' fun z _ _ => hΛ0 z
  have hΛ0' : 0 ≤ ∑ z ∈ supBox a R, Λ z := Finset.sum_nonneg fun z _ => hΛ0 z
  have hΦ0 : 0 ≤ ∑ y ∈ supBox a ρ, φ y ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hd0 : (0 : ℝ) ≤ 4 * d := by positivity
  have h8 : (4 * d * ∑ z ∈ supBox a R, Λ z) ^ 2 ≤ (4 * d * ∑ z ∈ supBox a R', Λ z) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hΛs hd0) 2
  exact mul_le_mul (mul_le_mul hcard hΦ hΦ0 (by positivity)) h8 (by positivity) (by positivity)

section Bound

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- **Step 1 for one bond, in terms of `ω^{e,1}`**: with `s₁` the side of the partition cube of
`ω^{e,1}` at the base `a` of `e`, `ρ₁ = C₀ C s₁` and `R₁ = (ρ₁ + 1) + 3 C (C s₁)`,
`T₁(e)² ≤ |B(a, ρ₁)| (Σ_{y ∈ B(a, ρ₁)} Φ²) (4d Σ_{z ∈ B(a, R₁)} Λ(z))²`. -/
theorem flipTermOne_sq_le_of_bound (hd : 0 < d) {C₀ C : ℕ} (hC₀ : 0 < C₀)
    (hres : ResamplePartitionBound (d := d) C₀ C)
    {e : Bond d} {ω : Configuration d} (hω₁ : setBond e true ω ∈ G)
    (hP₁ : PartitionEvent (setBond e true ω)) (hP₀ : PartitionEvent (setBond e false ω))
    {i : Fin d} {Λ : Vertex d → ℝ} (hΛ0 : ∀ z, 0 ≤ Λ z)
    (hΛ : ∀ z, setBond e true ω ∈ infiniteComponentEvent z → ∀ y,
      (openGraph (setBond e true ω)).Adj z y →
        |correctorDiff hG hGv (Pi.single i 1) (setBond e true ω) z y| ≤ Λ z)
    (j : Fin d) (r : ℝ) (x : Vertex d) :
    flipTermOne hG hGv i j r x e ω ^ 2 ≤
      (supBox (bondBase e)
        (C₀ * C * 3 ^ (partitionCube (setBond e true ω) (bondBase e)).scale)).card *
        (∑ y ∈ supBox (bondBase e)
            (C₀ * C * 3 ^ (partitionCube (setBond e true ω) (bondBase e)).scale),
          zdHeat d (r ^ 2) x y ^ 2) *
        (4 * d * ∑ z ∈ supBox (bondBase e)
            ((C₀ * C * 3 ^ (partitionCube (setBond e true ω) (bondBase e)).scale + 1) +
              3 * (C * (C * 3 ^ (partitionCube (setBond e true ω) (bondBase e)).scale))),
          Λ z) ^ 2 := by
  have hx : bondBase e ∈ e.1 := bondBase_mem e
  -- Lemma 3.5 with the flips exchanged: `s₀ ≤ C s₁`
  have hss : 3 ^ (partitionCube (setBond e false ω) (bondBase e)).scale ≤
      C * 3 ^ (partitionCube (setBond e true ω) (bondBase e)).scale := by
    refine (hres e (setBond e true ω) (setBond e false ω) (setBond_agree_off e true false ω) hP₁
      hP₀ (bondBase e) hx (bondBase e)).1 fun i => ?_
    rw [sub_self, abs_zero]
    exact mul_pos (by exact_mod_cast hC₀) (by positivity)
  have key : ∀ s₀ s₁ : ℕ, s₀ ≤ C * s₁ → C₀ * s₀ ≤ C₀ * C * s₁ ∧
      (C₀ * s₀ + 1) + 3 * (C * s₀) ≤ (C₀ * C * s₁ + 1) + 3 * (C * (C * s₁)) := by
    intro s₀ s₁ h
    have h1 : C₀ * s₀ ≤ C₀ * C * s₁ := by
      rw [mul_assoc]
      exact Nat.mul_le_mul_left _ h
    exact ⟨h1, Nat.add_le_add (Nat.add_le_add_right h1 1)
      (Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left C h))⟩
  have hloc := resampleLocal_of_bound hres (setBond_agree_off e false true ω) hP₀ hP₁ hx
  have hk := key _ _ hss
  exact (flipTermOne_sq_le hG hGv hd hω₁ hP₁ hP₀ hloc hΛ0 hΛ j r x).trans
    (stepOne_box_bound_mono (bondBase e) hk.1 hk.2 _ Λ hΛ0)

end Bound

end Rigidity.Corrector.GeneralDim
