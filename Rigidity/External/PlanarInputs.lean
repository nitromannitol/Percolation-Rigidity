import Rigidity.External.ArmstrongDarioRegularity
import LatticeProb.External.SupercriticalBondCorrectorInput
import LatticeProb.External.ArmstrongDarioOrderZero
import LatticeProb.External.GreenColumnExistence
import LatticeProb.External.GreenQuantitative

/-!
# Planar specializations of percolation inputs

The following estimates retain the constants and almost-sure quantifiers of the corresponding
all-dimensional statements, specialized to dimension two.
-/

open MeasureTheory LatticeProb.Percolation
open scoped ENNReal Classical

namespace Rigidity.External

/-- Planar quantitative corrector estimate. -/
def CorrectorQuantitativeInputTwo : Prop :=
  ∀ p : unitInterval,
    criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∀ α : ℝ, 0 < α → ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ x : Vertex 2,
      ∃ M : Configuration 2 → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond 2 p M s C ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ (q : Fin 2 → ℝ) (ℓ : uniqueInfiniteComponent h → ℝ),
          IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ →
        ∀ r : ℝ, M ω ≤ r →
        ∀ a b a' b' : uniqueInfiniteComponent h,
          ‖latticeEuclideanEmbedding a.val - latticeEuclideanEmbedding x‖ < r →
          ‖latticeEuclideanEmbedding b.val - latticeEuclideanEmbedding x‖ < r →
          ‖latticeEuclideanEmbedding a'.val - latticeEuclideanEmbedding x‖ < r →
          ‖latticeEuclideanEmbedding b'.val - latticeEuclideanEmbedding x‖ < r →
          (componentGraph (uniqueInfiniteComponent h)).Adj a' b' →
          |(ℓ a - ∑ i, q i * a.val i) - (ℓ b - ∑ i, q i * b.val i)| +
              |(ℓ a' - ∑ i, q i * a'.val i) - (ℓ b' - ∑ i, q i * b'.val i)|
            ≤ C * (∑ i, |q i|) * r ^ α

/-- The all-dimensional input implies its planar specialization. -/
theorem correctorQuantitativeInputTwo_of_input
    (h : Rigidity.External.CorrectorQuantitativeInput) :
    CorrectorQuantitativeInputTwo :=
  h 2 le_rfl

/-- Planar order-one regularity at the origin. -/
def ArmstrongDarioOrderOneOriginTwo : Prop :=
  ∀ p : unitInterval,
    criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∃ s C₀ : ℝ, 0 < s ∧ 0 < C₀ ∧
      ∃ X : Configuration 2 → ℝ, Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧ IsOsBond 2 p X s C₀ ∧
      ∃ C : ℝ, ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ R : ℝ, 2 * X ω ≤ R → ∀ u : uniqueInfiniteComponent h → ℝ,
          (∀ z ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 R,
            (∀ w, (componentGraph (uniqueInfiniteComponent h)).Adj z w →
              w ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 R) →
            componentLaplacian (uniqueInfiniteComponent h) u z = 0) →
          ∃ φ ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 1,
            ∀ r : ℝ, X ω ≤ r → r ≤ R / 2 →
              componentBallL2 (uniqueInfiniteComponent h) 0 r (u - φ) ≤
                C * (r / R) ^ 2 * componentBallL2 (uniqueInfiniteComponent h) 0 R u

/-- The all-dimensional input implies its planar specialization. -/
theorem armstrongDarioOrderOneOriginTwo_of_input
    (h : Rigidity.External.ArmstrongDarioOrderOneOrigin) :
    ArmstrongDarioOrderOneOriginTwo :=
  h 2 le_rfl

/-- Planar qualitative corrector estimate. -/
def SupercriticalBondCorrectorInputTwo : Prop :=
  ∀ p : unitInterval,
    criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
      (∀ q : Fin 2 → ℝ, ∀ o : uniqueInfiniteComponent h,
        ∃! u : uniqueInfiniteComponent h → ℝ,
          IsCorrectedPlane (uniqueInfiniteComponent h) q u ∧ u o = 0) ∧
      (∀ u : uniqueInfiniteComponent h → ℝ,
        u ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 1 →
        ∃! q : Fin 2 → ℝ, IsCorrectedPlane (uniqueInfiniteComponent h) q u)

/-- The all-dimensional input implies its planar specialization. -/
theorem supercriticalBondCorrectorInputTwo_of_input
    (h : LatticeProb.External.SupercriticalBondCorrectorInput) :
    SupercriticalBondCorrectorInputTwo :=
  h 2 le_rfl

/-- Planar order-zero regularity. -/
def ArmstrongDarioOrderZeroTwo : Prop :=
  ∀ p : unitInterval,
    criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∃ (s θ C : ℝ), 0 < s ∧ 0 < θ ∧ 0 < C ∧
      ∃ X : Configuration 2 → ℝ,
        Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧
        Integrable (fun ω => Real.exp (Real.rpow (X ω / θ) s)) (latticeBondLaw 2 p) ∧
        (∫ ω, Real.exp (Real.rpow (X ω / θ) s) ∂latticeBondLaw 2 p) ≤ 2 ∧
        ∀ᵐ ω ∂latticeBondLaw 2 p,
          ∃ _h : HasUniqueInfiniteOpenComponent ω,
            ∀ h' : HasUniqueInfiniteOpenComponent ω,
              FiniteDimensional ℝ (harmonicGrowthSpace (uniqueInfiniteComponent h') 0) ∧
              Module.finrank ℝ (harmonicGrowthSpace (uniqueInfiniteComponent h') 0) = 1 ∧
              ∀ (R : ℝ), 2 * X ω ≤ R →
                ∀ u : uniqueInfiniteComponent h' → ℝ,
                  (∀ x ∈ componentEuclideanBall (uniqueInfiniteComponent h') 0 R,
                    (∀ y : uniqueInfiniteComponent h',
                      (componentGraph (uniqueInfiniteComponent h')).Adj x y →
                        y ∈ componentEuclideanBall (uniqueInfiniteComponent h') 0 R) →
                    componentLaplacian (uniqueInfiniteComponent h') u x = 0) →
                  ∃ φ : uniqueInfiniteComponent h' → ℝ,
                    φ ∈ harmonicGrowthSpace (uniqueInfiniteComponent h') 0 ∧
                    ∀ r : ℝ, X ω ≤ r → r ≤ R / 2 →
                      componentBallL2 (uniqueInfiniteComponent h') 0 r (u - φ) ≤
                        C * (r / R) * componentBallL2 (uniqueInfiniteComponent h') 0 R u

/-- The all-dimensional input implies its planar specialization. -/
theorem armstrongDarioOrderZeroTwo_of_input
    (h : LatticeProb.External.ArmstrongDarioOrderZero) :
    ArmstrongDarioOrderZeroTwo :=
  h 2 le_rfl

/-- Planar existence and uniqueness of Green columns. -/
def SupercriticalBondGreenColumnExistenceTwo : Prop :=
  ∀ p : unitInterval,
    criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∀ y : Vertex 2, ∀ᵐ ω ∂latticeBondLaw 2 p,
      ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
          ∃! g : uniqueInfiniteComponent h → ℝ,
            IsGreenColumn 2 le_rfl (uniqueInfiniteComponent h) ⟨y, hy⟩ g

/-- The all-dimensional input implies its planar specialization. -/
theorem supercriticalBondGreenColumnExistenceTwo_of_input
    (h : LatticeProb.External.SupercriticalBondGreenColumnExistence) :
    SupercriticalBondGreenColumnExistenceTwo :=
  h 2 le_rfl

/-- Planar quantitative Green function estimate. -/
def SupercriticalBondGreenQuantitativeTwo : Prop :=
  ∀ p : unitInterval,
    criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∃ κ : ℝ, ∃ hκ : 0 < κ,
      ∃ K : Vertex 2 → Configuration 2 → ℝ,
          (∀ y, Measurable (K y)) ∧
          ∀ δ : ℝ, 0 < δ → ∃ C s : ℝ, 0 < C ∧ 0 < s ∧
            ∀ y : Vertex 2,
              (∀ R : ℝ, 0 ≤ R →
                latticeBondLaw 2 p {ω | R ≤ |K y ω|} ≤
                  ENNReal.ofReal (C * Real.exp (-Real.rpow R s / C))) ∧
              ∃ M : Configuration 2 → ℝ,
                Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧
                (∀ R : ℝ, 0 ≤ R →
                  latticeBondLaw 2 p {ω | R ≤ M ω} ≤
                    ENNReal.ofReal (C * Real.exp (-Real.rpow R s / C))) ∧
                ∀ᵐ ω ∂latticeBondLaw 2 p,
                  ∀ h : HasUniqueInfiniteOpenComponent ω,
                    ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
                      ∀ g : uniqueInfiniteComponent h → ℝ,
                        IsGreenColumn 2 le_rfl (uniqueInfiniteComponent h) ⟨y, hy⟩ g →
                        (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
                          ∀ x : uniqueInfiniteComponent h,
                            ∀ z : {v : EuclideanSpace ℝ (Fin 2) // v ≠ 0},
                              z.val = latticeEuclideanEmbedding x.val -
                                latticeEuclideanEmbedding y →
                              R ≤ ‖latticeEuclideanEmbedding x.val‖ →
                              |g x - continuumGreen 2 le_rfl ⟨κ, hκ⟩ z - K y ω| ≤ ε) ∧
                        ∀ x : uniqueInfiniteComponent h,
                          ∀ z : {v : EuclideanSpace ℝ (Fin 2) // v ≠ 0},
                            z.val = latticeEuclideanEmbedding x.val -
                              latticeEuclideanEmbedding y →
                            M ω ≤ ‖z.val‖ →
                            |g x - continuumGreen 2 le_rfl ⟨κ, hκ⟩ z - K y ω| ≤
                              C / Real.rpow ‖z.val‖ (1 - δ)

/-- The all-dimensional input implies its planar specialization. -/
theorem supercriticalBondGreenQuantitativeTwo_of_input
    (h : LatticeProb.External.SupercriticalBondGreenQuantitative) :
    SupercriticalBondGreenQuantitativeTwo := by
  intro p hpc hp1
  obtain ⟨κ, hκ, h2, _⟩ := h 2 le_rfl p hpc hp1
  exact ⟨κ, hκ, h2 rfl⟩

end Rigidity.External
