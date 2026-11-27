import Rigidity.Proofs.Corrector.GeneralStepOneMoments

/-!
# Step 1 of Lemma 3.3 of Dario on `ℤᵈ`, bond by bond

`flipTermOne_sq_le` bounds `T₁(e)²` through boxes around an endpoint `a` of `e` of radii comparable
to the scale `S` of the corrected Lemma 3.5, the larger side of the partition cubes of `ω^{e,0}`
and `ω^{e,1}` at `a` (`resampleScale`). With `ResamplePartitionBound C₀ C`,
`flipTermOne_sq_le_of_bound` bounds `T₁(e)²` by boxes of radii `C₀ S` and `(C₀ S + 1) + 3 C S` and
the Lipschitz bounds of the corrector of `ω^{e,1}`. The endpoint is `bondBase e`, the first point
of a presentation of the bond. This is the planar `Rigidity.Corrector.flipTermOne_sq_le_of_bound`
on `ℤᵈ`, with the scale `S` in place of the side of one partition.
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

/-- The scale `S` of the corrected Lemma 3.5 for the flips of `e` at its base: the larger side of
the partition cubes of `ω^{e,0}` and `ω^{e,1}` at `bondBase e`. -/
noncomputable def flipScale (e : Bond d) (ω : Configuration d) : ℕ :=
  resampleScale (setBond e false ω) (setBond e true ω) (bondBase e)

/-- **Step 1 for one bond**: with `S` the scale of the flips of `e` at its base `a`,
`T₁(e)² ≤ |B(a, C₀ S)| (Σ_{y ∈ B(a, C₀ S)} Φ²) (4d Σ_{z ∈ B(a, R)} Λ(z))²`,
`R = (C₀ S + 1) + 3 C S`, with Lipschitz bounds `Λ` of the corrector of `ω^{e,1}`. -/
theorem flipTermOne_sq_le_of_bound (hd : 0 < d) {C₀ C : ℕ}
    (hres : ResamplePartitionBound (d := d) C₀ C)
    {e : Bond d} {ω : Configuration d} (hω₁ : setBond e true ω ∈ G)
    (hP₁ : PartitionEvent (setBond e true ω)) (hP₀ : PartitionEvent (setBond e false ω))
    {i : Fin d} {Λ : Vertex d → ℝ} (hΛ0 : ∀ z, 0 ≤ Λ z)
    (hΛ : ∀ z, setBond e true ω ∈ infiniteComponentEvent z → ∀ y,
      (openGraph (setBond e true ω)).Adj z y →
        |correctorDiff hG hGv (Pi.single i 1) (setBond e true ω) z y| ≤ Λ z)
    (j : Fin d) (r : ℝ) (x : Vertex d) :
    flipTermOne hG hGv i j r x e ω ^ 2 ≤
      (supBox (bondBase e) (C₀ * flipScale e ω)).card *
        (∑ y ∈ supBox (bondBase e) (C₀ * flipScale e ω), zdHeat d (r ^ 2) x y ^ 2) *
        (4 * d * ∑ z ∈ supBox (bondBase e)
            ((C₀ * flipScale e ω + 1) + 3 * (C * flipScale e ω)), Λ z) ^ 2 :=
  flipTermOne_sq_le hG hGv hd hω₁ hP₁ hP₀
    (resampleLocal_of_bound hres (setBond_agree_off e false true ω) hP₀ hP₁ (bondBase_mem e))
    hΛ0 hΛ j r x

end Bound

end Rigidity.Corrector.GeneralDim
