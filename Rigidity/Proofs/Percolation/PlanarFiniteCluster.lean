import Rigidity.Proofs.Section5.ManyPaths
import Rigidity.Proofs.Percolation.PlanarAnnulusTail
import Rigidity.Proofs.Percolation.SupercriticalUniqueness
import Rigidity.Proofs.S3.ChemicalDistance
import LatticeProb.Prob.Percolation.LatticeBondTranslationLaw
import LatticeProb.Prob.Percolation.OpenComponentTranslation

/-!
# Planar finite clusters and annulus crossings

A loop in the infinite cluster separates any finite cluster intersecting the inner cube from the
outside of the enclosing cube. Supercritical annulus crossings supply such loops at each scale.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5
open Rigidity.Proofs.Section5

namespace Rigidity.Percolation

/-- A finite cluster touching the inner cube stays inside a surrounding infinite-cluster loop. -/
theorem finite_component_subset_cube_of_loop {ω : Configuration 2}
    (h : HasUniqueInfiniteOpenComponent ω) {R n : ℕ}
    (γ : Fin (n + 1) → uniqueInfiniteComponent h)
    (hγa : ∀ i, (componentGraph _).Adj (γ i) (γ (i + 1)))
    (hγm : ∀ i, (γ i).val ∈ cube (2 * R) \ cube R)
    (hγw : windingNumber (fun i => (γ i).val) ≠ 0)
    {x : Vertex 2} (hx : x ∈ cube R)
    (hf : ((openGraph ω).connectedComponentMk x).supp.Finite) :
    ((openGraph ω).connectedComponentMk x).supp ⊆ cube (2 * R) := by
  intro y hy
  by_contra hyout
  have hxy : (openGraph ω).Reachable x y := by
    apply SimpleGraph.ConnectedComponent.exact
    exact ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hy).symm
  obtain ⟨W⟩ := hxy
  have hβa : ∀ i, latticeL1Dist (γ i).val (γ (i + 1)).val = 1 :=
    fun i => latticeL1Dist_eq_one_of_adj (hγa i)
  have hβw : windAt (fun i => (γ i).val) 0 ≠ 0 := by
    intro hz
    apply hγw
    rw [windingNumber_eq_windAt, hz, zero_div]
  obtain ⟨i, hi, t, hit⟩ := exists_eq_of_crossing hβa hγm hβw
    (P := W.getVert) (L := W.length)
    (fun i hi => lattice_adj_iff_l1Dist.1 (W.adj_getVert_succ hi).1)
    (by simpa using hx) (by simpa using hyout)
  have hxγ : (openGraph ω).Reachable x (γ t).val := by
    rw [hit]
    exact (W.takeUntil (W.getVert i) (W.getVert_mem_support i)).reachable
  have hinf := (mem_uniqueInfiniteComponent_iff h (γ t).val).1 (γ t).property
  change ((openGraph ω).connectedComponentMk (γ t).val).supp.Infinite at hinf
  have heq := SimpleGraph.ConnectedComponent.sound hxγ
  rw [← heq] at hinf
  exact hinf hf

/-- Uniform annulus crossings confine finite clusters touching the inner cube. -/
theorem finite_component_subset_cube_of_crossings {ω : Configuration 2}
    (h : HasUniqueInfiniteOpenComponent ω) {M R : ℕ}
    (hM : ∀ r : ℕ, M ≤ r → AnnulusCrossings ω r) (hR : M + 1 ≤ R)
    {x : Vertex 2} (hx : x ∈ cube R)
    (hf : ((openGraph ω).connectedComponentMk x).supp.Finite) :
    ((openGraph ω).connectedComponentMk x).supp ⊆ cube (2 * R) := by
  obtain ⟨n, γ, hγa, hγm, hγw⟩ := loop_at_scale_of_crossings ω h M hM R hR
  exact finite_component_subset_cube_of_loop h γ hγa hγm hγw hx hf

/-- Crossings confine a finite component to at most the volume of the enclosing square. -/
theorem finite_component_card_le_of_crossings {ω : Configuration 2}
    (h : HasUniqueInfiniteOpenComponent ω) {M R : ℕ}
    (hM : ∀ r : ℕ, M ≤ r → AnnulusCrossings ω r) (hR : M + 1 ≤ R)
    {x : Vertex 2} (hx : x ∈ cube R)
    (hf : ((openGraph ω).connectedComponentMk x).supp.Finite) :
    ((openGraph ω).connectedComponentMk x).supp.ncard ≤ (4 * R + 1) ^ 2 := by
  have heq : cube (2 * R) = Rigidity.External.cubeAt (0 : Vertex 2) (2 * R) := by
    ext v
    simp [cube, Rigidity.External.cubeAt]
  have hsub := finite_component_subset_cube_of_crossings h hM hR hx hf
  rw [heq] at hsub
  have hcard := Set.ncard_le_ncard hsub (Rigidity.Proofs.S3.finite_cubeAt 0 (2 * R))
  have hset : Rigidity.External.cubeAt (0 : Vertex 2) (2 * R) =
      ↑(Rigidity.Proofs.S3.cubeFinset (0 : Vertex 2) (2 * R)) := by
    ext v
    exact Rigidity.Proofs.S3.mem_cubeFinset.symm
  rw [hset, Set.ncard_coe_finset, Rigidity.Proofs.S3.card_cubeFinset] at hcard
  convert hcard using 1; ring

/-- The origin's finite cluster exceeds the enclosing square only if a crossing fails. -/
theorem finite_cluster_exceeds_square_tail (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ R : ℕ, 1 ≤ R →
      latticeBondLaw 2 p {ω |
        ((openGraph ω).connectedComponentMk 0).supp.Finite ∧
        (4 * R + 1) ^ 2 < ((openGraph ω).connectedComponentMk 0).supp.ncard} ≤
      ENNReal.ofReal (C * Real.exp (-(c * (R - 1 : ℕ)))) := by
  obtain ⟨C, c, hC, hc, hcross⟩ := annulusCrossings_tail p hp
  refine ⟨C, c, hC, hc, fun R hR => ?_⟩
  have hU : ∀ᵐ ω ∂latticeBondLaw 2 p, HasUniqueInfiniteOpenComponent ω :=
    (mem_ae_iff_prob_eq_one (measurableSet_uniqueInfiniteComponentEvent 2)).2
      (uniqueInfiniteComponentEvent_eq_one_of_criticalProbability_lt 2 p hp)
  have hsub : ∀ᵐ ω ∂latticeBondLaw 2 p,
      ω ∈ {ω | ((openGraph ω).connectedComponentMk 0).supp.Finite ∧
        (4 * R + 1) ^ 2 < ((openGraph ω).connectedComponentMk 0).supp.ncard} →
      ω ∈ {ω | ∃ n : ℕ, R - 1 ≤ n ∧ ¬ AnnulusCrossings ω n} := by
    filter_upwards [hU] with ω hω ⟨hfin, hsize⟩
    by_contra hbad
    have hM : ∀ n : ℕ, R - 1 ≤ n → AnnulusCrossings ω n := by
      intro n hn
      by_contra hn'
      exact hbad ⟨n, hn, hn'⟩
    have hle := finite_component_card_le_of_crossings hω (M := R - 1) (R := R) hM (by omega)
      (x := 0) (by simp [cube]) hfin
    omega
  exact (measure_mono_ae hsub).trans (hcross (R - 1))

/-- A supercritical planar finite cluster has a stretched-exponential size tail. -/
theorem planar_finite_cluster_size_tail (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ,
      latticeBondLaw 2 p {ω |
        ((openGraph ω).connectedComponentMk 0).supp.Finite ∧
        N ≤ ((openGraph ω).connectedComponentMk 0).supp.ncard} ≤
      ENNReal.ofReal (C * Real.exp (-(c * Real.sqrt N))) := by
  obtain ⟨C, c, hC, hc, htail⟩ := finite_cluster_exceeds_square_tail p hp
  refine ⟨(C + 1) * Real.exp (2 * c), c / 8, by positivity, by positivity, fun N => ?_⟩
  have hroot : Real.sqrt N ≤ (Nat.sqrt N : ℝ) + 1 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have hnat : N < (Nat.sqrt N + 1) * (Nat.sqrt N + 1) :=
        Nat.sqrt_lt.mp (Nat.lt_succ_self _)
      have hreal : (N : ℝ) ≤ ((Nat.sqrt N : ℝ) + 1) * ((Nat.sqrt N : ℝ) + 1) := by
        exact_mod_cast hnat.le
      nlinarith
  by_cases hN : 64 ≤ N
  · let R := Nat.sqrt N / 8
    have hk : 8 ≤ Nat.sqrt N := Nat.le_sqrt.mpr (by omega)
    have hR : 1 ≤ R := by dsimp [R]; omega
    have hdiv := Nat.div_add_mod (Nat.sqrt N) 8
    have hmod := Nat.mod_lt (Nat.sqrt N) (by omega : 0 < 8)
    have hlo : 8 * R ≤ Nat.sqrt N := by dsimp [R]; omega
    have hhi : Nat.sqrt N < 8 * R + 8 := by dsimp [R]; omega
    have hvol : (4 * R + 1) ^ 2 < N := by
      have hlt : 4 * R + 1 < Nat.sqrt N := by omega
      have hsq := Nat.sqrt_le N
      nlinarith
    have hsqrt : Real.sqrt N ≤ 8 * (R : ℝ) + 8 := by
      have hcst : (Nat.sqrt N : ℝ) ≤ 8 * (R : ℝ) + 7 := by exact_mod_cast (show Nat.sqrt N ≤ 8 * R + 7 by omega)
      linarith
    have he : Real.exp (-(c * (R - 1 : ℕ))) ≤
        Real.exp (2 * c) * Real.exp (-(c / 8 * Real.sqrt N)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [Nat.cast_sub hR]
      push_cast
      nlinarith
    calc
      _ ≤ latticeBondLaw 2 p {ω |
          ((openGraph ω).connectedComponentMk 0).supp.Finite ∧
          (4 * R + 1) ^ 2 < ((openGraph ω).connectedComponentMk 0).supp.ncard} := by
        apply measure_mono
        rintro ω ⟨hfin, hsize⟩
        exact ⟨hfin, hvol.trans_le hsize⟩
      _ ≤ ENNReal.ofReal (C * Real.exp (-(c * (R - 1 : ℕ)))) := htail R hR
      _ ≤ ENNReal.ofReal ((C + 1) * Real.exp (2 * c) *
          Real.exp (-(c / 8 * Real.sqrt N))) := by
        apply ENNReal.ofReal_le_ofReal
        have hexp : 0 ≤ Real.exp (2 * c) * Real.exp (-(c / 8 * Real.sqrt N)) := by positivity
        nlinarith
  · have hsqrt : Real.sqrt N ≤ 8 := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · norm_num
      · have : (N : ℝ) ≤ 64 := by exact_mod_cast (show N ≤ 64 by omega)
        nlinarith
    have he : 1 ≤ Real.exp (2 * c) * Real.exp (-(c / 8 * Real.sqrt N)) := by
      rw [← Real.exp_add, ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      nlinarith
    calc
      _ ≤ (latticeBondLaw 2 p) Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal ((C + 1) * Real.exp (2 * c) *
          Real.exp (-(c / 8 * Real.sqrt N))) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith [Real.exp_pos (2 * c), Real.exp_pos (-(c / 8 * Real.sqrt N))]

/-- The finite-cluster size tail is uniform over the root vertex. -/
theorem planar_finite_cluster_size_tail_at (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (x : Vertex 2) (N : ℕ),
      latticeBondLaw 2 p {ω |
        ((openGraph ω).connectedComponentMk x).supp.Finite ∧
        N ≤ ((openGraph ω).connectedComponentMk x).supp.ncard} ≤
      ENNReal.ofReal (C * Real.exp (-(c * Real.sqrt N))) := by
  obtain ⟨C, c, hC, hc, htail⟩ := planar_finite_cluster_size_tail p hp
  refine ⟨C, c, hC, hc, fun x N => ?_⟩
  have hpre : {ω : Configuration 2 |
      ((openGraph ω).connectedComponentMk x).supp.Finite ∧
      N ≤ ((openGraph ω).connectedComponentMk x).supp.ncard} =
      configurationTranslation (-x) ⁻¹' {ω : Configuration 2 |
        ((openGraph ω).connectedComponentMk 0).supp.Finite ∧
        N ≤ ((openGraph ω).connectedComponentMk 0).supp.ncard} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    have hsupp : ((openGraph (configurationTranslation (-x) ω)).connectedComponentMk 0).supp =
        (fun y : Vertex 2 => y + -x) '' ((openGraph ω).connectedComponentMk x).supp := by
      have h := openComponentTranslation_supp (-x) ((openGraph ω).connectedComponentMk x)
      simpa only [openComponentTranslation_mk, add_neg_cancel] using h
    have hinj : Function.Injective (fun y : Vertex 2 => y + -x) := fun _ _ h => add_right_cancel h
    rw [hsupp, Set.finite_image_iff hinj.injOn, Set.ncard_image_of_injective _ hinj]
  rw [hpre, (measurePreserving_configurationTranslation p (-x)).measure_preimage_emb
    (configurationTranslationMeasurableEquiv (-x)).measurableEmbedding]
  exact htail N

end Rigidity.Percolation
