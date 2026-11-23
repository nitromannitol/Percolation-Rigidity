import Rigidity.Proofs.Regularity.PlanarCorrectorReduction
import LatticeProb.Prob.Percolation.LatticeOrderZeroTranslation

/-!
# The quantitative sublinearity of the planar correctors in `L²`, and the Lipschitz estimate at
every centre

`PlanarCorrectorSublinearL2Two` is the bound (1.18) of Armstrong and Dario (arXiv:1609.09431v2),
the case `k = 1` of Theorem 2 (ii), in dimension two: almost surely, for every slope `q` there is
`u ∈ 𝒜_1(𝒞_∞)` whose corrector `χ_q = u - q · x` satisfies
`‖χ_q‖_{L̲²(𝒞_∞ ∩ B_r)} ≤ K |q| r^{1-δ}` for every `r ≥ 𝒳`, with `𝒳 ≤ O_s(θ)`.

`exists_planar_all_centres_constant_approximation` transports the order-zero regularity of
Theorem 2 (iii) (`ArmstrongDarioOrderZeroTwo`, the Lipschitz estimate (1.19) in the form of the
approximation by constants) from the origin to every centre `z`, with the minimal scale
`𝒳 ∘ τ_{-z}` of the same law (`origin_constant_approximation_translation`,
`measurePreserving_configurationTranslation`), as `exists_all_centers_constant_approximation`
does for the input in every dimension.
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory LatticeProb.Percolation Rigidity.External

/-- **Armstrong–Dario, (1.18), in dimension two** (Theorem 2 (ii) for `k = 1`): the correctors are
sublinear in `L²` with a rate. -/
def PlanarCorrectorSublinearL2Two : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∃ s δ θ K : ℝ, 0 < s ∧ 0 < δ ∧ 0 < θ ∧ 0 ≤ K ∧
      ∃ X : Configuration 2 → ℝ, Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧ IsOsBond 2 p X s θ ∧
        ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ q : Fin 2 → ℝ,
          ∃ u : uniqueInfiniteComponent h → ℝ,
            u ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 1 ∧
            ∀ r : ℝ, X ω ≤ r →
              componentBallL2 (uniqueInfiniteComponent h) 0 r
                  (fun x => u x - componentSlope (uniqueInfiniteComponent h) q x) ≤
                K * (|q 0| + |q 1|) * r ^ (1 - δ)

/-- The order-zero regularity of the origin as an approximation by constants. -/
theorem exists_planar_origin_constant_approximation (hR3 : ArmstrongDarioOrderZeroTwo)
    (p : unitInterval) (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ (s θ C : ℝ), 0 < s ∧ 0 < θ ∧ 0 < C ∧
      ∃ X : Configuration 2 → ℝ,
        Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧
        Integrable (fun ω => Real.exp (Real.rpow (X ω / θ) s)) (latticeBondLaw 2 p) ∧
        (∫ ω, Real.exp (Real.rpow (X ω / θ) s) ∂latticeBondLaw 2 p) ≤ 2 ∧
        ∀ᵐ ω ∂latticeBondLaw 2 p,
          ∃ _h : HasUniqueInfiniteOpenComponent ω,
            ∀ h' : HasUniqueInfiniteOpenComponent ω,
              ∀ (R : ℝ), 2 * X ω ≤ R →
                ∀ u : uniqueInfiniteComponent h' → ℝ,
                  (∀ x ∈ componentEuclideanBall (uniqueInfiniteComponent h') 0 R,
                    (∀ y : uniqueInfiniteComponent h',
                      (componentGraph (uniqueInfiniteComponent h')).Adj x y →
                        y ∈ componentEuclideanBall (uniqueInfiniteComponent h') 0 R) →
                    componentLaplacian (uniqueInfiniteComponent h') u x = 0) →
                  ∃ c : ℝ, ∀ r : ℝ, X ω ≤ r → r ≤ R / 2 →
                    componentBallL2 (uniqueInfiniteComponent h') 0 r (u - fun _ => c) ≤
                      C * (r / R) * componentBallL2 (uniqueInfiniteComponent h') 0 R u := by
  obtain ⟨s, θ, C, hs, hθ, hC, X, hXmeas, hXnonneg, hXint, hXmoment, hAE⟩ := hR3 p hp hp1
  refine ⟨s, θ, C, hs, hθ, hC, X, hXmeas, hXnonneg, hXint, hXmoment, ?_⟩
  filter_upwards [hAE] with ω hω
  obtain ⟨hex, hω⟩ := hω
  refine ⟨hex, ?_⟩
  intro h R hR u hu
  obtain ⟨hfinite, hrank, happ⟩ := hω h
  obtain ⟨φ, hφ, happrox⟩ := happ R hR u hu
  obtain ⟨c, hc⟩ := harmonicGrowthSpace_zero_eq_const _ hfinite hrank φ hφ
  refine ⟨c, ?_⟩
  intro r hr hRr
  simpa only [hc] using happrox r hr hRr

/-- **The order-zero regularity at every centre in dimension two**: the minimal scale at `z` is
`𝒳 ∘ τ_{-z}`, with the same law. -/
theorem exists_planar_all_centres_constant_approximation (hR3 : ArmstrongDarioOrderZeroTwo)
    (p : unitInterval) (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ (s θ C : ℝ), 0 < s ∧ 0 < θ ∧ 0 < C ∧
      ∃ X : Vertex 2 → Configuration 2 → ℝ,
        (∀ z, Measurable (X z)) ∧ (∀ z ω, 0 ≤ X z ω) ∧
        (∀ z, Integrable (fun ω => Real.exp (Real.rpow (X z ω / θ) s))
          (latticeBondLaw 2 p)) ∧
        (∀ z, (∫ ω, Real.exp (Real.rpow (X z ω / θ) s) ∂latticeBondLaw 2 p) ≤ 2) ∧
        ∀ᵐ ω ∂latticeBondLaw 2 p,
          ∃ _h : HasUniqueInfiniteOpenComponent ω,
            ∀ h' : HasUniqueInfiniteOpenComponent ω, ∀ z : Vertex 2,
              ∀ (R : ℝ), 2 * X z ω ≤ R →
                ∀ u : uniqueInfiniteComponent h' → ℝ,
                  (∀ x ∈ componentEuclideanBall (uniqueInfiniteComponent h') z R,
                    (∀ y : uniqueInfiniteComponent h',
                      (componentGraph (uniqueInfiniteComponent h')).Adj x y →
                        y ∈ componentEuclideanBall (uniqueInfiniteComponent h') z R) →
                    componentLaplacian (uniqueInfiniteComponent h') u x = 0) →
                  ∃ c : ℝ, ∀ r : ℝ, X z ω ≤ r → r ≤ R / 2 →
                    componentBallL2 (uniqueInfiniteComponent h') z r (u - fun _ => c) ≤
                      C * (r / R) * componentBallL2 (uniqueInfiniteComponent h') z R u := by
  obtain ⟨s, θ, C, hs, hθ, hC, X, hXm, hXn, hXi, hXb, hAE⟩ :=
    exists_planar_origin_constant_approximation hR3 p hp hp1
  let Y : Vertex 2 → Configuration 2 → ℝ := fun z ω => X (configurationTranslation (-z) ω)
  refine ⟨s, θ, C, hs, hθ, hC, Y, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    exact hXm.comp (configurationTranslationMeasurableEquiv (-z)).measurable
  · intro z ω
    exact hXn _
  · intro z
    exact (measurePreserving_configurationTranslation p (-z)).integrable_comp_of_integrable hXi
  · intro z
    have he := (measurePreserving_configurationTranslation p (-z)).integral_comp
      (configurationTranslationMeasurableEquiv (-z)).measurableEmbedding
      (fun ω => Real.exp (Real.rpow (X ω / θ) s))
    exact he.trans_le hXb
  · have hall := ae_all_iff.mpr (fun z : Vertex 2 =>
      (measurePreserving_configurationTranslation p (-z)).quasiMeasurePreserving.ae hAE)
    filter_upwards [hAE, hall] with ω hω hz
    obtain ⟨h, _⟩ := hω
    refine ⟨h, ?_⟩
    intro h' z
    have ht := (hasUniqueInfiniteOpenComponent_translation_iff (-z) ω).mpr h'
    exact origin_constant_approximation_translation z h' (Y z ω) C ((hz z).2 ht)

end Rigidity.Proofs.Regularity
