import Rigidity.Percolation.TriadicGoodIndependence

/-!
# Joint independence of separated cube events

Events depending on pairwise disjoint bond regions are jointly independent.
This gives product formulas for any finite family of separated good cubes.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Local edge sigma algebras on pairwise disjoint regions are jointly independent. -/
theorem iIndep_localEdgeSigma {d : ℕ} {ι : Type*} (p : unitInterval)
    (U : ι → Set (Vertex d)) (hU : Pairwise fun i j => Disjoint (U i) (U j)) :
    iIndep (fun i => localEdgeSigma (U i)) (latticeBondLaw d p) := by
  classical
  rw [iIndep_iff]
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro A hA
    simp
  | @insert i s hi ih =>
    intro A hA
    have hAs : ∀ j, j ∈ s → MeasurableSet[localEdgeSigma (U j)] (A j) :=
      fun j hj => hA j (Finset.mem_insert_of_mem hj)
    have hdisj : Disjoint (U i) (⋃ j ∈ s, U j) := by
      rw [Set.disjoint_left]
      intro x hx hy
      obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hy
      have hij : i ≠ j := by
        intro h
        subst j
        exact hi hj
      exact Set.disjoint_left.mp (hU hij) hx hxj
    have hsmeas : MeasurableSet[localBondSigma (⋃ j ∈ s, U j)] (⋂ j ∈ s, A j) := by
      apply Finset.measurableSet_biInter s
      intro j hj
      have hsub : U j ⊆ ⋃ k ∈ s, U k := by
        intro x hx
        exact Set.mem_iUnion₂.mpr ⟨j, hj, hx⟩
      exact localBondSigma_mono hsub _
        (localEdgeSigma_le_localBondSigma (U j) _ (hAs j hj))
    have himeas := localEdgeSigma_le_localBondSigma (U i) _ (hA i (Finset.mem_insert_self i s))
    have hind := (Indep_iff _ _ _).mp (indep_localBondSigma p hdisj) (A i)
      (⋂ j ∈ s, A j) himeas hsmeas
    simpa only [Finset.set_biInter_insert, Finset.prod_insert hi]
      using hind.trans (congrArg (fun x => latticeBondLaw d p (A i) * x) (ih hAs))

/-- Good events for cubes with pairwise disjoint threefold enlargements are jointly independent. -/
theorem iIndep_good_events {d : ℕ} {ι : Type*} (p : unitInterval)
    (Q : ι → TriadicCube d) (interior : TriadicCube d → Set (Vertex d))
    (hinterior : ∀ T, interior T ⊆ T.vertices)
    (hQ : Pairwise fun i j => Disjoint (Q i).centeredTriple (Q j).centeredTriple) :
    iIndepSet (fun i => {ω | Q i ∈ TriadicCube.goodOfWellConnected
      (TriadicCube.wellConnectedFamily interior ω)}) (latticeBondLaw d p) := by
  rw [iIndepSet_iff_iIndep, iIndep_iff]
  intro s A hA
  apply (iIndep_localEdgeSigma p (fun i => (Q i).centeredTriple) hQ).meas_biInter
  intro i hi
  apply MeasurableSpace.generateFrom_le ?_ _ (hA i hi)
  rintro E rfl
  exact (Q i).measurableSet_goodOfWellConnected_localEdge interior hinterior

/-- The probability that finitely many separated cubes are all bad is the
product of their individual bad-event probabilities. -/
theorem measure_all_bad_eq_prod {d : ℕ} {ι : Type*} (p : unitInterval)
    (Q : ι → TriadicCube d) (interior : TriadicCube d → Set (Vertex d))
    (hinterior : ∀ T, interior T ⊆ T.vertices)
    (hQ : Pairwise fun i j => Disjoint (Q i).centeredTriple (Q j).centeredTriple)
    (s : Finset ι) :
    latticeBondLaw d p (⋂ i ∈ s, {ω | Q i ∉ TriadicCube.goodOfWellConnected
      (TriadicCube.wellConnectedFamily interior ω)}) =
      ∏ i ∈ s, latticeBondLaw d p {ω | Q i ∉ TriadicCube.goodOfWellConnected
        (TriadicCube.wellConnectedFamily interior ω)} := by
  apply (iIndep_localEdgeSigma p (fun i => (Q i).centeredTriple) hQ).meas_biInter
  intro i hi
  exact ((Q i).measurableSet_goodOfWellConnected_localEdge interior hinterior).compl

/-- A uniform bound on individual bad events yields a power bound for a finite
separated family. -/
theorem measure_all_bad_le_pow {d : ℕ} {ι : Type*} (p : unitInterval)
    (Q : ι → TriadicCube d) (interior : TriadicCube d → Set (Vertex d))
    (hinterior : ∀ T, interior T ⊆ T.vertices)
    (hQ : Pairwise fun i j => Disjoint (Q i).centeredTriple (Q j).centeredTriple)
    (s : Finset ι) (q : ℝ≥0∞)
    (hq : ∀ i ∈ s, latticeBondLaw d p {ω | Q i ∉ TriadicCube.goodOfWellConnected
      (TriadicCube.wellConnectedFamily interior ω)} ≤ q) :
    latticeBondLaw d p (⋂ i ∈ s, {ω | Q i ∉ TriadicCube.goodOfWellConnected
      (TriadicCube.wellConnectedFamily interior ω)}) ≤ q ^ s.card := by
  rw [measure_all_bad_eq_prod p Q interior hinterior hQ s]
  calc
    _ ≤ ∏ _i ∈ s, q := Finset.prod_le_prod' hq
    _ = q ^ s.card := Finset.prod_const q

end Rigidity.Percolation
