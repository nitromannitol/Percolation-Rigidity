import Rigidity.Support.PlanarMixedGreen
import Rigidity.Steps.S3.NotLipschitz

/-!
# Planar origin-gradient bound

The large-gradient contradiction needs only planar Green and order-zero inputs.
-/

open MeasureTheory LatticeProb.Percolation Classical Filter Topology

namespace Rigidity.Steps.S3

open Rigidity.Section3

/-- The origin gradient has positive outer probability at every threshold. -/
theorem originGradient_of_wellConnected_event_two (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hginput : Rigidity.External.SupercriticalBondGreenQuantitativeTwo)
    (hreg : Rigidity.External.ArmstrongDarioOrderZeroTwo)
    (hclassical : LatticeProb.External.SupercriticalBondUniqueness)
    (h33 : Section3.CompareDifferentPlanesStmt 2 le_rfl p)
    (hEdge : EdgeGradientStep 2 p) (hFE : FiniteEnergyStep 2 p) (hCU : ClosedBondsUniqueStep 2 p)
    (hWC : Tendsto (fun N : ℕ =>
      latticeBondLaw 2 p {ω | ¬ Rigidity.External.IsWellConnected ω 0 N}) atTop (𝓝 0))
    (hGS : GreenScaleEventStep 2 p)
    (hFlux : FluxEventStep 2 p) (hRem : RemovalStep 2) (hSP : ShortPathsStep 2)
    (hDiv : DivergenceStep 2) (hBr : BridgeFluxStep 2) (hKer : GreenKernelSumStep 2)
    (L : ℝ) (hL : 0 ≤ L) :
    latticeBondLaw 2 p {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
        ∃ ho : (0 : Vertex 2) ∈ (uniqueInfiniteComponent h).supp,
        ∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) (slopeE1 2) u ∧
          L < originGradientNorm (uniqueInfiniteComponent h) ho u} ≠ 0 := by
  intro h0
  have hLipae := hFE hp1 L (hEdge L h0)
  have hUqae := hCU hp1 (hclassical.2 2 le_rfl p hpc hp1)
  obtain ⟨s, CG, hs, hCG, hMG⟩ :=
    Rigidity.Support.mixed_green_two hginput hreg p hpc hp1 (1 / 4) (by norm_num)
  choose M hMmeas _hM1 hMint hMle hMae using hMG
  have hMae' := ae_all_iff.2 hMae
  obtain ⟨a, ha, hfl⟩ := hFlux le_rfl hpc hp1
  obtain ⟨Ksp, hKsp, H, hH⟩ := hSP le_rfl
  obtain ⟨Kker, hKker⟩ := hKer le_rfl
  have hsum := (hWC.add (hGS s CG hs hCG M hMmeas hMint hMle)).add
    (hfl (a / 2) (by positivity))
  rw [add_zero, add_zero] at hsum
  obtain ⟨N, hN1, hNprob, hNH, hNker, hNarith⟩ := ((eventually_ge_atTop 1).and
    ((hsum.eventually_lt_const zero_lt_one).and (hH.and (hKker.and
      (eventually_flux_arith (d := 2) (a / 2) (L * Ksp) (CG * L * Ksp * Kker)
        (by positivity)))))).exists
  obtain ⟨ω, hω1, hω2, hω3, hLipω, hUqω, ⟨h1, h33ω⟩, hMω⟩ :=
    exists_notMem_of_measure_lt hNprob (hLipae.and (hUqae.and (h33.and hMae')))
  obtain ⟨h, u0, hu0, hleft, hside⟩ := not_not.1 hω3
  obtain ⟨hNHc, hNHct, hNHsp⟩ := hNH
  have hgr : ∀ y ∈ latticeCube 2 N, M y ω ≤ (N : ℝ) ^ (1 / (10 * (2 : ℝ) ^ 2)) :=
    fun y hy => not_lt.1 fun hlt => hω2 ⟨y, hy, hlt⟩
  refine false_of_steps_at le_rfl hRem hDiv hBr (ε := a / 2) hL hCG hKsp hN1 (H N) hNHc hNHct
    hNker ?_ h (hNHsp ω (not_not.1 hω1) _ (uniqueInfiniteComponent_infinite h)) hUqω hLipω h33ω
    (fun y => M y ω) hgr (fun y hy g hg x hx => (hMω y).elim fun _ hall => hall h hy g hg x hx)
    u0 hu0 hleft hside
  linarith


end Rigidity.Steps.S3
