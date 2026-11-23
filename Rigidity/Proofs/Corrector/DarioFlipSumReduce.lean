import Rigidity.Proofs.Corrector.DarioFlipSumTerms

/-!
# Convergence of the heat series of the split (3.15)

Of the three heat series of the split (`FlipSummable`), the first and the third are the series of
`Φ_{r²} * ∇_j[χ_{e_i}]_𝒫` for the flips `ω^{e,1}` and `ω^{e,0}` themselves
(`flipCorrector_sub_eq_coarseField_sub`), which converge almost surely for every flip
(`ae_flipSeries_summable`, from `ae_summable_heat_coarseField` of main and the quasi-invariance of
the bond law under flips). The second is the sum of the third and of the series of the term
(3.15)-(ii) (`flipSummable_of`). Hence (`darioFlipSumBound_of_sums`) Dario's (3.13) in flip form
follows from the convergence of the series of the term (3.15)-(ii) (`FlipTermTwoSummable`) and
the `O_s(C/r²)` bounds of `Σ_e T₁(e)²` and `Σ_e T₂(e)²`.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical ENNReal

section Series

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- The heat series of the term (3.15)-(ii): `Σ_y Φ_{r²}(x, y) ∇_j[χ₁ - χ₀]_{𝒫⁰}(y)` converges. -/
def FlipTermTwoSummable (i j : Fin 2) (r : ℝ) (x : Vertex 2) (e : Bond 2) (ω : Configuration 2) :
    Prop :=
  Summable fun y => latticeHeat (r ^ 2) x y *
    ((flipCorrector hG hGv i true e ω (guardAnchor (setBond e false ω) (y + LatticeProb.unit j)) -
        flipCorrector hG hGv i false e ω (guardAnchor (setBond e false ω) (y + LatticeProb.unit j))) -
      (flipCorrector hG hGv i true e ω (guardAnchor (setBond e false ω) y) -
        flipCorrector hG hGv i false e ω (guardAnchor (setBond e false ω) y)))

/-- The coarse gradient of `χ_b` for the partition of `ω^{e,b}` is that of the coarsened corrector
of `ω^{e,b}`. -/
theorem flipCorrector_sub_eq_coarseField_sub {e : Bond 2} {ω : Configuration 2} {b : Bool}
    (hω : setBond e b ω ∈ G) (hP : PlanarPartitionEvent (setBond e b ω))
    (hP₀ : PlanarPartitionEvent (setBond e false ω)) (i j : Fin 2) (y : Vertex 2) :
    flipCorrector hG hGv i b e ω (guardAnchor (setBond e b ω) (y + LatticeProb.unit j)) -
        flipCorrector hG hGv i b e ω (guardAnchor (setBond e b ω) y) =
      coarseField hG hGv i 0 (y + LatticeProb.unit j) (setBond e b ω) -
        coarseField hG hGv i 0 y (setBond e b ω) := by
  have ho : setBond e b ω ∈ infiniteComponentEvent (guardAnchor (setBond e false ω) 0) := by
    refine infiniteComponentEvent_setBond_true ?_ b
    rw [guardAnchor_of_event hP₀]
    exact infinite_planarCoarseAnchor hP₀ 0
  have hA : ∀ z, setBond e b ω ∈ infiniteComponentEvent (guardAnchor (setBond e b ω) z) :=
    fun z => by
      rw [guardAnchor_of_event hP]
      exact infinite_planarCoarseAnchor hP z
  unfold flipCorrector coarseField
  simp only [shiftedAnchor_zero]
  have h1 := correctorDiff_sub_eq hG hGv (q := Pi.single i 1) hω (hA (y + LatticeProb.unit j))
    (hA y) ho
  have h2 := correctorDiff_sub_eq hG hGv (q := Pi.single i 1) hω (hA (y + LatticeProb.unit j))
    (hA y) (hA 0)
  linarith

/-- **The first and third series converge**: almost surely, for every bond, flip, point, direction
and radius `r > 0`, the heat series of the coarse gradient of `χ_b` for the partition of `ω^{e,b}`
converges. -/
theorem ae_flipSeries_summable {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) (i : Fin 2) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (e : Bond 2) (b : Bool) (x : Vertex 2) (j : Fin 2) (r : ℝ), 0 < r →
      Summable fun y => latticeHeat (r ^ 2) x y *
        (flipCorrector hG hGv i b e ω (guardAnchor (setBond e b ω) (y + LatticeProb.unit j)) -
          flipCorrector hG hGv i b e ω (guardAnchor (setBond e b ω) y)) := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg 2).trans_lt hpc
  have h := ae_summable_heat_coarseField hG hGv
    Rigidity.Proofs.Regularity.armstrongDarioOrderZeroTwo_holds hpc hp1 hGae i
  filter_upwards [ae_setBond hp0 hp1 h, ae_setBond hp0 hp1 hGae,
    ae_setBond hp0 hp1 (ae_planarPartitionEvent hpc)] with ω hS hG' hP' e b x j r hr
  refine (hS e b x j r hr).congr fun y => ?_
  rw [flipCorrector_sub_eq_coarseField_sub hG hGv (hG' e b) (hP' e b) (hP' e false) i j y]

/-- The second series of the split is the sum of the third and of the series of (3.15)-(ii). -/
theorem flipSummable_of {i j : Fin 2} {r : ℝ} {x : Vertex 2} {e : Bond 2} {ω : Configuration 2}
    (h₁ : Summable fun y => latticeHeat (r ^ 2) x y *
      (flipCorrector hG hGv i true e ω (guardAnchor (setBond e true ω) (y + LatticeProb.unit j)) -
        flipCorrector hG hGv i true e ω (guardAnchor (setBond e true ω) y)))
    (hII : FlipTermTwoSummable hG hGv i j r x e ω)
    (h₃ : Summable fun y => latticeHeat (r ^ 2) x y *
      (flipCorrector hG hGv i false e ω (guardAnchor (setBond e false ω) (y + LatticeProb.unit j)) -
        flipCorrector hG hGv i false e ω (guardAnchor (setBond e false ω) y))) :
    FlipSummable hG hGv i j r x e ω :=
  ⟨h₁, (h₃.add hII).congr fun y => by ring, h₃⟩

end Series

/-- **(3.13) in flip form from the convergence of the series of (3.15)-(ii) and the bounds of the
two square sums**: `DarioFlipSumBound` holds if, for the conull sets `G` of the measurable
corrector, there are `s, C > 0` such that for all `i, j`, `r ≥ 1` and `x`, almost surely the series
of the term (3.15)-(ii) converges for every bond, and `Σ_e T₁(e)²` (Step 1) and `Σ_e T₂(e)²`
(Step 2) are almost surely finite and `≤ O_s(C/r²)`. -/
theorem darioFlipSumBound_of_sums
    (h : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∀ (G : Set (Configuration 2)) (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2),
        (∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) → ∃ s C : ℝ, 0 < s ∧ 0 < C ∧
          ∀ (i j : Fin 2) (r : ℝ), 1 ≤ r → ∀ x : Vertex 2,
            (∀ᵐ ω ∂latticeBondLaw 2 p, ∀ e, FlipTermTwoSummable hG hGv i j r x e ω) ∧
            (∀ᵐ ω ∂latticeBondLaw 2 p, flipSumOne hG hGv i j r x ω < ∞) ∧
            (∀ᵐ ω ∂latticeBondLaw 2 p, flipSumTwo hG hGv i j r x ω < ∞) ∧
            IsOsBond 2 p (fun ω => (flipSumOne hG hGv i j r x ω).toReal) s (C / r ^ 2) ∧
            IsOsBond 2 p (fun ω => (flipSumTwo hG hGv i j r x ω).toReal) s (C / r ^ 2)) :
    DarioFlipSumBound := by
  refine darioFlipSumBound_of_terms fun p hpc hp1 G hG hGv hGae => ?_
  obtain ⟨s, C, hs, hC, hb⟩ := h p hpc hp1 G hG hGv hGae
  refine ⟨s, C, hs, hC, fun i j r hr x => ?_⟩
  obtain ⟨hII, h1, h2, h3, h4⟩ := hb i j r hr x
  refine ⟨?_, h1, h2, h3, h4⟩
  filter_upwards [ae_flipSeries_summable hG hGv hpc hp1 hGae i, hII] with ω hS hII' e
  exact flipSummable_of hG hGv (hS e true x j r (by linarith)) (hII' e)
    (hS e false x j r (by linarith))

end Rigidity.Corrector
