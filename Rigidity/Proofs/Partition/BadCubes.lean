import Rigidity.Proofs.Partition.AlmostSure
import Rigidity.Percolation.TriadicGoodJointIndependence

/-!
# Bad cubes near large partition cubes

A partition cube `Q` of scale `n` is a stopping cube with a child outside the stable good cubes,
so some cube of scale at least `n - 1` in the influence of that child is not good; it lies within
eleven of its side lengths of every vertex of `Q`. Large partition cubes are therefore controlled
by counting bad cubes.

Bad events of cubes of scale at least three with disjoint threefold enlargements are independent,
so the probability that at least `k` cubes of such a family of `N` cubes are bad, each with
probability at most `q`, is at most `C(N, k) q^k`.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- **A bad cube near a partition cube.** Every vertex `x` has a cube which is not good, of scale
at least one less than the partition cube of `x`, whose centre is within eleven of its side
lengths of `x`. -/
theorem exists_bad_near_partitionCube {ω : Configuration d} (hP : PartitionEvent ω)
    (x : Vertex d) :
    ∃ T : TriadicCube d, T ∉ TriadicCube.goodCubes ω ∧ (partitionCube ω x).scale ≤ T.scale + 1 ∧
      ∀ i, |x i - T.center i| ≤ 11 * T.side := by
  have h3 := three_le_scale_partitionCube hP x
  have hxQ := mem_partitionCube hP x
  obtain ⟨-, hstop⟩ := (partitionCube_spec hP x).2.1
  set Q := partitionCube ω x with hQdef
  rcases hstop with h0 | ⟨digits, hbad⟩
  · omega
  simp only [TriadicCube.stableGood, Set.mem_setOf_eq, Set.not_subset] at hbad
  obtain ⟨T, hT, hTbad⟩ := hbad
  have hscale := TriadicCube.scale_le_of_mem_influence hT
  have hcs : (Q.child digits).scale = Q.scale - 1 := rfl
  refine ⟨T, hTbad, by omega, fun i => ?_⟩
  have h1 := TriadicCube.abs_center_sub_le_of_mem_influence hT i
  have hcQ : (Q.child digits).vertices ⊆ Q.vertices := Q.vertices_child_subset digits (by omega)
  have h2 := TriadicCube.abs_coord_sub_lt_side hxQ (hcQ (Q.child digits).center_mem) i
  have hside3 : 3 * (Q.child digits).side = Q.side := by
    rw [← TriadicCube.side_parent, TriadicCube.child_parent _ _ (by omega)]
  have hsideT : (Q.child digits).side ≤ T.side :=
    pow_le_pow_right₀ (by norm_num) hscale
  have h4 := abs_sub_le (x i) ((Q.child digits).center i) (T.center i)
  change |x i - (Q.child digits).center i| < Q.side at h2
  linarith

/-- For cubes of scale at least three, goodness is goodness for the well-connected family of the
rounded three-quarter cubes. -/
theorem TriadicCube.mem_goodCubes_iff_of_three_le {Q : TriadicCube d} (hQ : 3 ≤ Q.scale)
    (ω : Configuration d) :
    Q ∈ goodCubes ω ↔ Q ∈ goodOfWellConnected
      (wellConnectedFamily (fun R => ↑R.threeQuarterCube.vertices) ω) := by
  unfold goodCubes goodOfWellConnected wellConnectedCubes wellConnectedFamily
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨h0, ⟨-, hw⟩, hch⟩
    exact ⟨h0, hw, fun digits => (hch digits).2⟩
  · rintro ⟨h0, hw, hch⟩
    refine ⟨h0, ⟨by omega, hw⟩, fun digits => ⟨?_, hch digits⟩⟩
    change 2 ≤ Q.scale - 1
    omega

open scoped Classical in
/-- **Many bad cubes in a separated family.** For a finite family of cubes of scale at least
three with pairwise disjoint threefold enlargements, each failing to be good with probability at
most `q`, at least `k` of them fail with probability at most `C(N, k) q^k`, `N` the size of the
family. -/
theorem measure_le_card_bad_le (p : unitInterval) {ι : Type*} (Q : ι → TriadicCube d)
    (hQ3 : ∀ i, 3 ≤ (Q i).scale)
    (hsep : Pairwise fun i j => Disjoint (Q i).centeredTriple (Q j).centeredTriple)
    (s : Finset ι) (q : ℝ≥0∞)
    (hq : ∀ i ∈ s, latticeBondLaw d p {ω | Q i ∉ TriadicCube.goodCubes ω} ≤ q) (k : ℕ) :
    latticeBondLaw d p
        {ω | k ≤ (s.filter fun i => Q i ∉ TriadicCube.goodCubes ω).card} ≤
      (s.card.choose k : ℝ≥0∞) * q ^ k := by
  have hinterior : ∀ R : TriadicCube d,
      (↑R.threeQuarterCube.vertices : Set (Vertex d)) ⊆ R.vertices :=
    fun R => R.threeQuarterCube_subset_envelope.trans R.threeQuarterEnvelope_subset
  have hbad : ∀ i ω, Q i ∉ TriadicCube.goodCubes ω ↔ Q i ∉ TriadicCube.goodOfWellConnected
      (TriadicCube.wellConnectedFamily (fun R => ↑R.threeQuarterCube.vertices) ω) :=
    fun i ω => not_congr (TriadicCube.mem_goodCubes_iff_of_three_le (hQ3 i) ω)
  have hsub : {ω | k ≤ (s.filter fun i => Q i ∉ TriadicCube.goodCubes ω).card} ⊆
      ⋃ S ∈ s.powersetCard k, ⋂ i ∈ S, {ω | Q i ∉ TriadicCube.goodOfWellConnected
        (TriadicCube.wellConnectedFamily (fun R => ↑R.threeQuarterCube.vertices) ω)} := by
    intro ω hω
    obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq hω
    simp only [Set.mem_iUnion, Set.mem_iInter, Set.mem_setOf_eq, exists_prop]
    refine ⟨S, Finset.mem_powersetCard.2 ⟨hS.trans (Finset.filter_subset _ _), hcard⟩,
      fun i hi => (hbad i ω).1 (Finset.mem_filter.1 (hS hi)).2⟩
  calc _ ≤ latticeBondLaw d p (⋃ S ∈ s.powersetCard k, ⋂ i ∈ S, {ω | Q i ∉
        TriadicCube.goodOfWellConnected
          (TriadicCube.wellConnectedFamily (fun R => ↑R.threeQuarterCube.vertices) ω)}) :=
        measure_mono hsub
    _ ≤ ∑ S ∈ s.powersetCard k, latticeBondLaw d p (⋂ i ∈ S, {ω | Q i ∉
        TriadicCube.goodOfWellConnected
          (TriadicCube.wellConnectedFamily (fun R => ↑R.threeQuarterCube.vertices) ω)}) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _S ∈ s.powersetCard k, q ^ k := by
        refine Finset.sum_le_sum fun S hS => ?_
        have hS' := Finset.mem_powersetCard.1 hS
        have h := measure_all_bad_le_pow p Q (fun R => ↑R.threeQuarterCube.vertices) hinterior
          hsep S q (fun i hi => by
            have hq' := hq i (hS'.1 hi)
            have heq : {ω | Q i ∉ TriadicCube.goodOfWellConnected
                (TriadicCube.wellConnectedFamily (fun R => ↑R.threeQuarterCube.vertices) ω)} =
                {ω | Q i ∉ TriadicCube.goodCubes ω} := by
              ext ω
              exact (hbad i ω).symm
            rw [heq]
            exact hq')
        rwa [hS'.2] at h
    _ = (s.card.choose k : ℝ≥0∞) * q ^ k := by
        rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]

end Rigidity.Percolation
