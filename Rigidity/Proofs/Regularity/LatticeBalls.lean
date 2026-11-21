import Rigidity.Proofs.S2.ClusterDensityFromDarioGu
import Rigidity.Proofs.Regularity.ClusterKIterationOne

/-!
# Lemma 7.2 of Armstrong–Dario on balls of the lattice

The whole lattice `ℤ^d` is the open component `latticeComponent d` of the configuration in which
every bond is open. Its density in every triadic cube is one (`clusterCubeDensity_latticeComponent`),
so the balls of the lattice satisfy all the properties of the normalized `L²` norms and of the
polynomials used in the iteration of Armstrong–Dario, Lemma 7.2 (arXiv:1609.09431v2), with
deterministic constants and no minimal scale beyond a multiple of `√d`
(`armstrongDario_lemma_7_2_zero_lattice`, `armstrongDario_lemma_7_2_one_lattice`). This is the
setting of a discrete homogenized problem with constant coefficients on `ℤ^d`, where the class
`Abar` consists of discrete `ā`-harmonic functions; their excess decay (`HarmonicRegularity`) and
the harmonic approximation hypothesis remain hypotheses.
-/

namespace Rigidity.Proofs.Regularity

open LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S2

variable {d : ℕ}

/-- The whole lattice, as the open component of the fully open configuration containing `0`. -/
def latticeComponent (d : ℕ) : OpenComponent (allOpen d) :=
  (openGraph (allOpen d)).connectedComponentMk 0

theorem latticeComponent_supp (d : ℕ) [NeZero d] : (latticeComponent d).supp = Set.univ := by
  ext y
  simp only [latticeComponent, SimpleGraph.ConnectedComponent.mem_supp_iff,
    SimpleGraph.ConnectedComponent.eq, openGraph_allOpen, Set.mem_univ, iff_true]
  exact (Graph.Zd.latticeConnected d).preconnected y 0

/-- Every triadic cube is filled by the lattice: the cube density holds with `κ = 1` at every
scale and locality. -/
theorem clusterCubeDensity_latticeComponent [NeZero d] (z : Vertex d) (Λ ℓ : ℝ) :
    ClusterCubeDensity (latticeComponent d) z Λ ℓ 1 := by
  classical
  intro m k _ hk
  have hmem : ∀ y : Vertex d, y ∈ (latticeComponent d).supp := fun y => by
    rw [latticeComponent_supp]; trivial
  have hcard := card_triadicCubeFinset (d := d) m k
  rw [one_mul]
  have hle : (triadicCubeFinset d m k).card ≤
      (clusterCubePoints (latticeComponent d) z (Λ * 3 ^ m) m k).card := by
    refine Finset.card_le_card_of_injOn (fun y => (⟨y, hmem y⟩ : latticeComponent d)) ?_ ?_
    · intro y hy
      have hyQ : y ∈ triadicCube d m k := by
        rw [← coe_triadicCubeFinset]; exact hy
      simp only [clusterCubePoints, Finset.coe_filter, Set.mem_setOf_eq,
        mem_componentEuclideanBall]
      exact ⟨hk y hyQ, hyQ⟩
    · intro y _ y' _ h
      exact congrArg Subtype.val h
  rw [hcard] at hle
  exact_mod_cast hle

/-- **Armstrong–Dario, Lemma 7.2 (`k = 0`), on balls of the lattice.** -/
theorem armstrongDario_lemma_7_2_zero_lattice (d : ℕ) (hd : 0 < d) {A α CH : ℝ} (hA : 2 ≤ A)
    (hα : 0 < α) (hCH : 0 ≤ CH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : Vertex d) (Abar : ℝ → Set (latticeComponent d → ℝ)) (R X E : ℝ)
      (u : latticeComponent d → ℝ),
      1 ≤ X → X ≤ R / A → 0 ≤ E → 24 * Real.sqrt d ≤ X →
      HarmonicRegularity (componentBallSeminorm (latticeComponent d) z) Abar
        (clusterAffine (latticeComponent d)) 1 X R CH →
      (∀ r : ℝ, X ≤ r → r ≤ R / A → (Abar r).Nonempty) →
      HarmonicApproximation (componentBallSeminorm (latticeComponent d) z) Abar
        (clusterConstants (latticeComponent d)) A α X R E u →
      ∀ r : ℝ, max X C ≤ r → r ≤ R / 2 →
        ballExcess (componentBallSeminorm (latticeComponent d) z)
            (clusterConstants (latticeComponent d)) r u ≤
          C * (r / R) * ballExcess (componentBallSeminorm (latticeComponent d) z)
            (clusterConstants (latticeComponent d)) R u +
          C * r ^ (1 - α) * (ballExcess (componentBallSeminorm (latticeComponent d) z)
            (clusterConstants (latticeComponent d)) R u / R + E / r) := by
  haveI : NeZero d := ⟨hd.ne'⟩
  obtain ⟨C, hC, h⟩ := armstrongDario_lemma_7_2_zero_of_clusterCubeDensity d hd hA hα one_pos hCH
  refine ⟨C, hC, fun z Abar R X E u hX hXR hE hX24 hreg hne happ => ?_⟩
  exact h (allOpen d) (latticeComponent d) z Abar R X E 1 u hX hXR hE
    (by rw [max_eq_right le_rfl, mul_one]; exact hX24)
    (clusterCubeDensity_latticeComponent z _ 1) hreg hne happ

/-- **Armstrong–Dario, Lemma 7.2 (`k = 1`), on balls of the lattice**, with `Ā_2 = P₂` any
subgroup of the quadratic functions on `ℤ^d` containing the affine functions. -/
theorem armstrongDario_lemma_7_2_one_lattice (d : ℕ) (hd : 0 < d) {A α CH : ℝ} (hA : 2 ≤ A)
    (hα : 0 < α) (hCH : 0 ≤ CH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : Vertex d) (P₂ : AddSubgroup (latticeComponent d → ℝ))
      (Abar : ℝ → Set (latticeComponent d → ℝ)) (R X E : ℝ) (u : latticeComponent d → ℝ),
      clusterAffine (latticeComponent d) ≤ P₂ → P₂ ≤ clusterQuadratic (latticeComponent d) →
      1 ≤ X → X ≤ R / A → 0 ≤ E → quadLocality d (capFraction d 1) ≤ X →
      HarmonicRegularity (componentBallSeminorm (latticeComponent d) z) Abar
        (clusterAffine (latticeComponent d)) 1 X R CH →
      HarmonicRegularity (componentBallSeminorm (latticeComponent d) z) Abar P₂ 2 X R CH →
      (∀ r : ℝ, X ≤ r → r ≤ R / A → (Abar r).Nonempty) →
      HarmonicApproximation (componentBallSeminorm (latticeComponent d) z) Abar
        (clusterConstants (latticeComponent d)) A α X R E u →
      ∀ r : ℝ, max X C ≤ r → r ≤ R / 2 →
        ballExcess (componentBallSeminorm (latticeComponent d) z)
            (clusterAffine (latticeComponent d)) r u ≤
          C * (r / R) ^ 2 * ballExcess (componentBallSeminorm (latticeComponent d) z)
            (clusterAffine (latticeComponent d)) R u +
          C * r ^ (1 - α) * (ballExcess (componentBallSeminorm (latticeComponent d) z)
            (clusterConstants (latticeComponent d)) R u / R + E / r) := by
  haveI : NeZero d := ⟨hd.ne'⟩
  obtain ⟨C, hC, h⟩ := armstrongDario_lemma_7_2_one_of_clusterCubeDensity d hd hA hα one_pos hCH
  refine ⟨C, hC, fun z P₂ Abar R X E u hAP hPQ hX hXR hE hXq hreg₁ hreg₂ hne happ => ?_⟩
  exact h (allOpen d) (latticeComponent d) z P₂ Abar R X E 1 u hAP hPQ hX hXR hE
    (by rw [max_eq_right le_rfl, mul_one]; exact hXq)
    (clusterCubeDensity_latticeComponent z _ 1) hreg₁ hreg₂ hne happ

end Rigidity.Proofs.Regularity
