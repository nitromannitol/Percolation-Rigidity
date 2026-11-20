import Rigidity.Percolation.BoundaryContactDecay
import Rigidity.Percolation.BondSeedExploration

/-!
# Reached contacts on expanding cube boundaries

The probability that a finite seed reaches a positive but bounded number of
vertices on an expanding cube boundary tends to zero.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External Filter
open scoped Topology

/-- The centered lattice cube of integer radius `n`. -/
def centeredBondCube {d : ℕ} (n : ℕ) : Set (Vertex d) :=
  latticeRectangle (fun _ => -(n : ℤ)) (fun _ => (n : ℤ) + 1)

/-- Centered cubes are finite. -/
theorem finite_centeredBondCube {d : ℕ} (n : ℕ) : (centeredBondCube (d := d) n).Finite :=
  finite_latticeRectangle _ _

/-- The centered cube consists of vertices with all coordinates of absolute
value at most the radius. -/
theorem mem_centeredBondCube {d : ℕ} (n : ℕ) (x : Vertex d) :
    x ∈ centeredBondCube n ↔ ∀ i, |x i| ≤ (n : ℤ) := by
  simp only [centeredBondCube, latticeRectangle, Set.mem_setOf_eq, abs_le]
  constructor <;> intro h i <;> have := h i <;> omega

/-- The inner vertex boundary of a centered cube. -/
noncomputable def centeredBondCubeBoundary {d : ℕ} (n : ℕ) : Finset (Vertex d) := by
  classical
  exact (finite_centeredBondCube (d := d) n).toFinset.filter fun x =>
    ∃ i, |x i| = (n : ℤ)

/-- Boundary membership is cube membership together with an extremal coordinate. -/
theorem mem_centeredBondCubeBoundary {d : ℕ} (n : ℕ) (x : Vertex d) :
    x ∈ centeredBondCubeBoundary n ↔
      x ∈ centeredBondCube n ∧ ∃ i, |x i| = (n : ℤ) := by
  classical
  simp only [centeredBondCubeBoundary, Finset.mem_filter, Set.Finite.mem_toFinset]

/-- Any lattice bond exiting a centered cube starts on its boundary. -/
theorem mem_centeredBondCubeBoundary_of_exit {d : ℕ} {n : ℕ} {x y : Vertex d}
    (hx : x ∈ centeredBondCube n) (hy : y ∉ centeredBondCube n)
    (hxy : (nearestNeighborGraph d).Adj x y) : x ∈ centeredBondCubeBoundary n := by
  classical
  apply (mem_centeredBondCubeBoundary n x).mpr
  refine ⟨hx, ?_⟩
  by_contra h
  push Not at h
  apply hy
  apply (mem_centeredBondCube n y).mpr
  intro i
  have hxi := (mem_centeredBondCube n x).mp hx i
  have hne := h i
  have hsum := lattice_adj_iff_l1Dist.mp hxy
  have hdist : |x i - y i| ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => abs_nonneg (x j - y j)) (Finset.mem_univ i)
  have htri : |y i| ≤ |x i - y i| + |x i| := by
    have heq : y i = -(x i - y i) + x i := by ring
    conv_lhs => rw [heq]
    simpa only [abs_neg] using abs_add_le (-(x i - y i)) (x i)
  omega

/-- The next cube boundary lies outside the present centered cube. -/
theorem centeredBondCubeBoundary_succ_outside {d : ℕ} (n : ℕ) {x : Vertex d}
    (hx : x ∈ centeredBondCubeBoundary (n + 1)) : x ∉ centeredBondCube n := by
  obtain ⟨_, i, hi⟩ := (mem_centeredBondCubeBoundary (n + 1) x).mp hx
  intro h
  have hle := (mem_centeredBondCube n x).mp h i
  have : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by exact_mod_cast rfl
  omega

/-- A finite seed has a vanishing probability of reaching a positive but
uniformly bounded number of vertices on expanding cube boundaries. -/
theorem tendsto_measure_bounded_centeredCube_contacts {d : ℕ} (p : unitInterval)
    (hp : (p : ℝ) < 1) (roots : Finset (Vertex d)) (M m : ℕ)
    (hroots : ∀ z ∈ roots, z ∈ centeredBondCube M) :
    Tendsto (fun n => latticeBondLaw d p {ω |
      0 < (seedReachableContacts (centeredBondCube (M + n)) roots
        (centeredBondCubeBoundary (M + n)) ω).card ∧
      (seedReachableContacts (centeredBondCube (M + n)) roots
        (centeredBondCubeBoundary (M + n)) ω).card ≤ m}) atTop (𝓝 0) := by
  apply tendsto_measure_bounded_seed_contacts p hp
    (fun n => centeredBondCube (M + n)) roots (fun n => centeredBondCubeBoundary (M + n)) m
  · intro n
    exact finite_centeredBondCube _
  · intro n z hz
    apply (mem_centeredBondCube _ z).mpr
    intro i
    have h := (mem_centeredBondCube M z).mp (hroots z hz) i
    exact h.trans (by exact_mod_cast Nat.le_add_right M n)
  · intro n x hx
    exact ((mem_centeredBondCubeBoundary _ _).mp hx).1
  · intro n x hx y hy hxy
    exact mem_centeredBondCubeBoundary_of_exit hx hy hxy
  · intro n w hw
    exact centeredBondCubeBoundary_succ_outside (M + n) (by simpa only [Nat.add_assoc] using hw)

end Rigidity.Percolation
