import Rigidity.Percolation.WellConnectedRegions
import LatticeProb.Prob.HarrisCube
import LatticeProb.Prob.Percolation.LatticeBondProbability

/-!
# Positive association of connections

Under Bernoulli bond percolation, simultaneous connections from a vertex to
finitely many targets have probability at least the product of their individual
probabilities.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External

/-- The event that a root connects inside a region to a point in a target. -/
def targetConnection {d : ℕ} (B T : Set (Vertex d)) (x : Vertex d) :
    Set (Configuration d) :=
  {ω | ∃ y ∈ B, y ∈ T ∧ (openIn ω B).Reachable x y}

/-- A target-connection event is measurable. -/
theorem measurableSet_targetConnection {d : ℕ} (B T : Set (Vertex d)) (x : Vertex d) :
    MeasurableSet (targetConnection B T x) := by
  apply measurableSet_setOf.2
  exact Measurable.exists fun y => measurable_const.and (measurable_const.and
    (measurableSet_setOf.1 (measurableSet_openIn_reachable B x y)))

/-- Opening more bonds can only add edges inside a region. -/
theorem openIn_mono_configuration {d : ℕ} {ω η : Configuration d}
    (h : ω ≤ η) (B : Set (Vertex d)) : openIn ω B ≤ openIn η B := by
  intro x y hxy
  obtain ⟨⟨hadj, hopen⟩, hx, hy⟩ := hxy
  refine ⟨⟨hadj, ?_⟩, hx, hy⟩
  have he := h (bondOfAdjacent hadj)
  rw [hopen] at he
  cases hη : η (bondOfAdjacent hadj) with
  | false => exact ((by decide : ¬ true ≤ false) (hη ▸ he)).elim
  | true => rfl

/-- A target-connection event is increasing in the configuration. -/
theorem isUpperSet_targetConnection {d : ℕ} (B T : Set (Vertex d)) (x : Vertex d) :
    IsUpperSet (targetConnection B T x) := by
  intro ω η hωη hω
  obtain ⟨y, hyB, hyT, hy⟩ := hω
  exact ⟨y, hyB, hyT, hy.mono (openIn_mono_configuration hωη B)⟩

/-- Harris's inequality for a finite collection of target connections. -/
theorem prod_measure_targetConnection_le {d : ℕ} {ι : Type*} (p : unitInterval)
    (B : Set (Vertex d)) (T : ι → Set (Vertex d)) (x : Vertex d) (s : Finset ι) :
    (∏ i ∈ s, (latticeBondLaw d p).real (targetConnection B (T i) x)) ≤
      (latticeBondLaw d p).real (⋂ i ∈ s, targetConnection B (T i) x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.set_biInter_insert]
    calc
      _ ≤ (latticeBondLaw d p).real (targetConnection B (T i) x) *
          (latticeBondLaw d p).real (⋂ j ∈ s, targetConnection B (T j) x) :=
            mul_le_mul_of_nonneg_left ih measureReal_nonneg
      _ ≤ _ := by
        exact LatticeProb.infinitePi_harris_bool
          (fun _ : Bond d => bernoulliMeasure true false p)
          (isUpperSet_targetConnection B (T i) x)
          (isUpperSet_iInter₂ fun j _ => isUpperSet_targetConnection B (T j) x)
          (measurableSet_targetConnection B (T i) x)
          (s.measurableSet_biInter fun j _ => measurableSet_targetConnection B (T j) x)

/-- The probability that the root's component meets every specified lower and
upper face is at least the product of the individual connection probabilities. -/
theorem prod_measure_faceConnection_le_crossingRoot {d : ℕ} (p : unitInterval)
    (B : Set (Vertex d)) (lower upper : Fin d → Set (Vertex d)) (x : Vertex d)
    (hx : x ∈ B) :
    (∏ face : Fin d × Bool, (latticeBondLaw d p).real
      (targetConnection B (if face.2 then upper face.1 else lower face.1) x)) ≤
      (latticeBondLaw d p).real {ω | IsCrossingRoot ω B lower upper x} := by
  let faces : Fin d × Bool → Set (Vertex d) := fun face =>
    if face.2 then upper face.1 else lower face.1
  have hprod := prod_measure_targetConnection_le p B faces x Finset.univ
  apply hprod.trans
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  simp only [Set.mem_iInter, Finset.mem_univ, forall_const] at hω
  refine ⟨hx, ?_⟩
  intro i
  constructor
  · simpa only [faces, Bool.false_eq_true, ↓reduceIte, targetConnection, Set.mem_setOf_eq]
      using hω (i, false)
  · simpa only [faces, ↓reduceIte, targetConnection, Set.mem_setOf_eq] using hω (i, true)

end Rigidity.Percolation
