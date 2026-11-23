import Rigidity.Proofs.Corrector.DarioStepOneMoments

/-!
# Step 1 of Lemma 3.3 of Dario, bond by bond, with the partition of the flip with the bond open

`flipTermOne_sq_le` bounds `T₁(e)²` through boxes around an endpoint `a` of `e` of radii comparable
to the side `s₀` of the partition cube of `ω^{e,0}` at `a`. Applying Lemma 3.5
(`ResamplePartitionBound C₀ C`) with the roles of the flips exchanged, `s₀ ≤ C s₁` with `s₁` the
side of the partition cube of `ω^{e,1}` at `a`; since all the factors grow with the boxes,
`flipTermOne_sq_le_of_bound` bounds `T₁(e)²` by quantities of the single configuration
`ω^{e,1}`: boxes of radii `C₀ C s₁` and `(C₀ C s₁ + 1) + 5 C² s₁` and the Lipschitz bounds of its
corrector. The endpoint is `bondBase e`, the tail of an oriented edge of the bond.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Poincare
open scoped Classical

/-- The tail of an oriented lattice edge of the bond. -/
noncomputable def bondBase (e : Bond 2) : Vertex 2 := (Classical.choose (exists_edgeBond_eq e)).1

theorem bondBase_mem (e : Bond 2) : bondBase e ∈ e.1 := by
  have h := Classical.choose_spec (exists_edgeBond_eq e)
  unfold bondBase
  generalize Classical.choose (exists_edgeBond_eq e) = a at h ⊢
  subst h
  exact Sym2.mem_mk_left _ _

theorem supBox_subset_of_le (a : Vertex 2) {ρ ρ' : ℕ} (h : ρ ≤ ρ') : supBox a ρ ⊆ supBox a ρ' :=
  fun z hz => by
    rw [mem_supBox] at hz ⊢
    exact fun i => (hz i).trans (by exact_mod_cast h)

/-- The bound of Step 1 grows with the boxes. -/
theorem stepOne_box_bound_mono (a : Vertex 2) {ρ ρ' R R' : ℕ} (hρ : ρ ≤ ρ') (hR : R ≤ R')
    (φ Λ : Vertex 2 → ℝ) (hΛ0 : ∀ z, 0 ≤ Λ z) :
    ((supBox a ρ).card : ℝ) * (∑ y ∈ supBox a ρ, φ y ^ 2) * (8 * ∑ z ∈ supBox a R, Λ z) ^ 2 ≤
      (supBox a ρ').card * (∑ y ∈ supBox a ρ', φ y ^ 2) * (8 * ∑ z ∈ supBox a R', Λ z) ^ 2 := by
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
  have h8 : (8 * ∑ z ∈ supBox a R, Λ z) ^ 2 ≤ (8 * ∑ z ∈ supBox a R', Λ z) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  exact mul_le_mul (mul_le_mul hcard hΦ hΦ0 (by positivity)) h8 (by positivity) (by positivity)

section Bound

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- **Step 1 for one bond, in terms of `ω^{e,1}`**: with `s₁` the side of the partition cube of
`ω^{e,1}` at the base `a` of `e`, `ρ₁ = C₀ C s₁` and `R₁ = (ρ₁ + 1) + 5 C (C s₁)`,
`T₁(e)² ≤ |B(a, ρ₁)| (Σ_{y ∈ B(a, ρ₁)} Φ²) (8 Σ_{z ∈ B(a, R₁)} Λ(z))²`. -/
theorem flipTermOne_sq_le_of_bound {C₀ C : ℕ} (hC₀ : 0 < C₀) (hres : ResamplePartitionBound C₀ C)
    {e : Bond 2} {ω : Configuration 2} (hω₁ : setBond e true ω ∈ G)
    (hP₁ : PlanarPartitionEvent (setBond e true ω)) (hP₀ : PlanarPartitionEvent (setBond e false ω))
    {i : Fin 2} {Λ : Vertex 2 → ℝ} (hΛ0 : ∀ z, 0 ≤ Λ z)
    (hΛ : ∀ z, setBond e true ω ∈ infiniteComponentEvent z → ∀ y,
      (openGraph (setBond e true ω)).Adj z y →
        |correctorDiff hG hGv (Pi.single i 1) (setBond e true ω) z y| ≤ Λ z)
    (j : Fin 2) (r : ℝ) (x : Vertex 2) :
    flipTermOne hG hGv i j r x e ω ^ 2 ≤
      (supBox (bondBase e)
        (C₀ * C * 3 ^ (planarPartCube (setBond e true ω) (bondBase e)).scale)).card *
        (∑ y ∈ supBox (bondBase e)
            (C₀ * C * 3 ^ (planarPartCube (setBond e true ω) (bondBase e)).scale),
          latticeHeat (r ^ 2) x y ^ 2) *
        (8 * ∑ z ∈ supBox (bondBase e)
            ((C₀ * C * 3 ^ (planarPartCube (setBond e true ω) (bondBase e)).scale + 1) +
              5 * (C * (C * 3 ^ (planarPartCube (setBond e true ω) (bondBase e)).scale))),
          Λ z) ^ 2 := by
  have hx : bondBase e ∈ e.1 := bondBase_mem e
  -- Lemma 3.5 with the flips exchanged: `s₀ ≤ C s₁`
  have hss : 3 ^ (planarPartCube (setBond e false ω) (bondBase e)).scale ≤
      C * 3 ^ (planarPartCube (setBond e true ω) (bondBase e)).scale := by
    refine (hres e (setBond e true ω) (setBond e false ω) (setBond_agree_off e true false ω) hP₁
      hP₀ (bondBase e) hx (bondBase e)).1 fun i => ?_
    rw [sub_self, abs_zero]
    exact mul_pos (by exact_mod_cast hC₀) (by positivity)
  have key : ∀ s₀ s₁ : ℕ, s₀ ≤ C * s₁ → C₀ * s₀ ≤ C₀ * C * s₁ ∧
      (C₀ * s₀ + 1) + 5 * (C * s₀) ≤ (C₀ * C * s₁ + 1) + 5 * (C * (C * s₁)) := by
    intro s₀ s₁ h
    have h1 : C₀ * s₀ ≤ C₀ * C * s₁ := by
      rw [mul_assoc]
      exact Nat.mul_le_mul_left _ h
    exact ⟨h1, Nat.add_le_add (Nat.add_le_add_right h1 1)
      (Nat.mul_le_mul_left 5 (Nat.mul_le_mul_left C h))⟩
  have hloc := resampleLocal_of_bound hres (setBond_agree_off e false true ω) hP₀ hP₁ hx
  have hk := key _ _ hss
  exact (flipTermOne_sq_le hG hGv hω₁ hP₁ hP₀ hloc hΛ0 hΛ j r x).trans
    (stepOne_box_bound_mono (bondBase e) hk.1 hk.2 _ Λ hΛ0)

end Bound

end Rigidity.Corrector
