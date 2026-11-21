import Rigidity.External.PlanarInputs
import LatticeProb.Prob.Percolation.LatticeOrderZeroGradient

/-!
# Planar order-zero gradient bounds

The all-centers order-zero gradient estimate follows from the planar regularity input.
-/

open MeasureTheory
open scoped ProbabilityTheory

namespace Rigidity.Support

open LatticeProb.Percolation

theorem exists_origin_constant_approximation_two (input : Rigidity.External.ArmstrongDarioOrderZeroTwo) (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
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
  obtain ⟨s, θ, C, hs, hθ, hC, X, hXmeas, hXnonneg, hXint, hXmoment, hAE⟩ :=
    input p hp hp1
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


theorem exists_all_centers_constant_approximation_two
    (input : Rigidity.External.ArmstrongDarioOrderZeroTwo) (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
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
    exists_origin_constant_approximation_two input p hp hp1
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


theorem exists_all_centers_order_zero_gradient_two
    (input : Rigidity.External.ArmstrongDarioOrderZeroTwo) (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ (s θ K : ℝ), 0 < s ∧ 0 < θ ∧ 0 < K ∧
      ∃ X : Vertex 2 → Configuration 2 → ℝ,
        (∀ z, Measurable (X z)) ∧ (∀ z ω, 0 ≤ X z ω) ∧
        (∀ z, Integrable (fun ω => Real.exp (Real.rpow (X z ω / θ) s))
          (latticeBondLaw 2 p)) ∧
        (∀ z, (∫ ω, Real.exp (Real.rpow (X z ω / θ) s) ∂latticeBondLaw 2 p) ≤ 2) ∧
        ∀ᵐ ω ∂latticeBondLaw 2 p,
          ∃ _h : HasUniqueInfiniteOpenComponent ω,
            ∀ h' : HasUniqueInfiniteOpenComponent ω,
              ∀ x : uniqueInfiniteComponent h', ∀ R : ℝ,
                8 * max 2 (X x.val ω) ≤ R →
                ∀ u : uniqueInfiniteComponent h' → ℝ,
                  (∀ z ∈ componentEuclideanBall (uniqueInfiniteComponent h') x.val R,
                    (∀ w : uniqueInfiniteComponent h',
                      (componentGraph (uniqueInfiniteComponent h')).Adj z w →
                        w ∈ componentEuclideanBall (uniqueInfiniteComponent h') x.val R) →
                    componentLaplacian (uniqueInfiniteComponent h') u z = 0) →
                  ∀ y : uniqueInfiniteComponent h',
                    (componentGraph (uniqueInfiniteComponent h')).Adj x y →
                    (u x - u y) ^ 2 ≤
                      K * (max 2 (X x.val ω)) ^ 2 / R ^ 2 *
                        (componentBallL2 (uniqueInfiniteComponent h') x.val R u) ^ 2 := by
  obtain ⟨s, θ, C, hs, hθ, hC, X, hXm, hXn, hXi, hXb, hAE⟩ :=
    exists_all_centers_constant_approximation_two input p hp hp1
  obtain ⟨K, hK, hgrad⟩ := component_local_gradient 2 le_rfl
  refine ⟨s, θ, 16 * K * C ^ 2, hs, hθ, by positivity, X, hXm, hXn, hXi, hXb, ?_⟩
  filter_upwards [hAE] with ω hω
  obtain ⟨h, hall⟩ := hω
  refine ⟨h, ?_⟩
  intro h' x R hR u hu y hxy
  let m := max 2 (X x.val ω)
  have hm : 2 ≤ m := le_max_left _ _
  have hRm : 8 * m ≤ R := hR
  have hmpos : 0 < m := by linarith
  have hRpos : 0 < R := by linarith
  have hXR : 2 * X x.val ω ≤ R := by
    have := le_max_right 2 (X x.val ω)
    dsimp [m] at hR hm
    linarith
  obtain ⟨c, hc⟩ := hall h' x.val R hXR u hu
  have hcr := hc (4 * m) (by
    have := le_max_right 2 (X x.val ω)
    dsimp [m]
    linarith) (by linarith)
  have hh : ∀ z ∈ componentEuclideanBall (uniqueInfiniteComponent h') x.val (2 * m),
      componentLaplacian (uniqueInfiniteComponent h') (u - fun _ => c) z = 0 := by
    intro z hz
    have hz' := (mem_componentEuclideanBall (uniqueInfiniteComponent h') x.val _ z).mp hz
    have hzR : z ∈ componentEuclideanBall (uniqueInfiniteComponent h') x.val R :=
      (mem_componentEuclideanBall (uniqueInfiniteComponent h') x.val R z).mpr (by linarith)
    have hn : ∀ w : uniqueInfiniteComponent h',
        (componentGraph (uniqueInfiniteComponent h')).Adj z w →
        w ∈ componentEuclideanBall (uniqueInfiniteComponent h') x.val R := by
      intro w hzw
      apply (mem_componentEuclideanBall (uniqueInfiniteComponent h') x.val R w).mpr
      have he : dist (latticeEuclideanEmbedding w.val) (latticeEuclideanEmbedding z.val) = 1 :=
        dist_embedding_adj hzw.symm
      have ht := dist_triangle (latticeEuclideanEmbedding w.val)
        (latticeEuclideanEmbedding z.val) (latticeEuclideanEmbedding x.val)
      linarith
    have hzu := hu z hzR hn
    simp only [componentLaplacian, Pi.sub_apply] at hzu ⊢
    convert hzu using 1
    apply Finset.sum_congr rfl
    intro w hw
    ring
  have hg := hgrad ω (uniqueInfiniteComponent h') x y m hm (u - fun _ => c) hxy hh
  have hnon := componentBallL2_nonneg (uniqueInfiniteComponent h') x.val (4 * m) (u - fun _ => c)
  have hsq : (componentBallL2 (uniqueInfiniteComponent h') x.val (4 * m) (u - fun _ => c)) ^ 2 ≤
      (C * (4 * m / R) * componentBallL2 (uniqueInfiniteComponent h') x.val R u) ^ 2 :=
    (sq_le_sq₀ hnon (le_trans hnon hcr)).2 hcr
  have hpw : m ^ 2 = m ^ (2 - 2) * m ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel le_rfl]
  calc
    _ = (u x - c - (u y - c)) ^ 2 := by ring
    _ ≤ K * m ^ (2 - 2) *
        (componentBallL2 (uniqueInfiniteComponent h') x.val (4 * m) (u - fun _ => c)) ^ 2 := by
      simpa only [Pi.sub_apply] using hg
    _ ≤ K * m ^ (2 - 2) *
        (C * (4 * m / R) * componentBallL2 (uniqueInfiniteComponent h') x.val R u) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by rw [hpw]; field_simp; ring


end Rigidity.Support
