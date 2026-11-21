import Rigidity.Proofs.Regularity.ContinuumBallExcess
import Mathlib.MeasureTheory.Function.Floor
import LatticeProb.Prob.Percolation.LatticeClusterBall

/-!
# Step functions of lattice functions

A function `f` on `ℤ^d` extends to `ℝ^d` as the step function constant on the unit cubes
`k + [-1/2, 1/2)^d` (`latticeStep f`), the extension by which Armstrong and Dario
(arXiv:1609.09431v2, Section 7) regard coarsened functions `[u]_P` as functions on `ℝ^d`. It is
square integrable on every ball (`latticeStepFun f ∈ locallySqIntegrable d`), so the continuum
instances of Lemma 7.2 apply to it.
-/

open MeasureTheory Metric

namespace Rigidity.Proofs.Regularity

variable {d : ℕ}

/-- The lattice point `k` with `x ∈ k + [-1/2, 1/2)^d`. -/
noncomputable def latticePointOf (x : EuclideanSpace ℝ (Fin d)) : Fin d → ℤ :=
  fun i => ⌊x i + 1 / 2⌋

/-- The step function of `f`, constant on the unit cubes centred at the lattice points. -/
noncomputable def latticeStep (f : (Fin d → ℤ) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  f (latticePointOf x)

theorem measurable_latticePointOf : Measurable (latticePointOf (d := d)) := by
  refine measurable_pi_lambda _ fun i => ?_
  have hc : Continuous fun x : EuclideanSpace ℝ (Fin d) => x i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous
  exact Int.measurable_floor.comp (hc.measurable.add_const _)

theorem abs_latticePointOf_le (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    |(latticePointOf x i : ℝ)| ≤ ‖x‖ + 1 := by
  have h1 := Int.floor_le (x i + 1 / 2)
  have h2 := Int.lt_floor_add_one (x i + 1 / 2)
  have h3 : |x i| ≤ ‖x‖ := by
    have := PiLp.norm_apply_le x i
    rwa [Real.norm_eq_abs] at this
  have h4 := abs_le.1 h3
  rw [abs_le]
  simp only [latticePointOf]
  constructor <;> linarith

theorem memLp_latticeStep (f : (Fin d → ℤ) → ℝ) (c : EuclideanSpace ℝ (Fin d)) (R : ℝ) :
    MemLp (latticeStep f) 2 (volume.restrict (ball c R)) := by
  classical
  set K : ℕ := ⌈‖c‖ + |R| + 1⌉₊ with hK
  set box : Finset (Fin d → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(K : ℤ)) K with hbox
  refine MemLp.of_bound
    ((measurable_of_countable f).comp measurable_latticePointOf).aestronglyMeasurable
    (∑ k ∈ box, |f k|) ?_
  refine ae_restrict_of_forall_mem measurableSet_ball fun x hx => ?_
  rw [Real.norm_eq_abs]
  have hx' : ‖x‖ ≤ ‖c‖ + |R| := by
    have h1 : ‖x - c‖ < R := by rw [← dist_eq_norm]; exact mem_ball.1 hx
    calc ‖x‖ = ‖(x - c) + c‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - c‖ + ‖c‖ := norm_add_le _ _
      _ ≤ ‖c‖ + |R| := by linarith [le_abs_self R]
  have hmem : latticePointOf x ∈ box := by
    rw [hbox, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have h := abs_latticePointOf_le x i
    have hKr : ‖c‖ + |R| + 1 ≤ (K : ℝ) := Nat.le_ceil _
    have h5 : |(latticePointOf x i : ℝ)| ≤ K := by linarith
    have h6 : |latticePointOf x i| ≤ (K : ℤ) := by exact_mod_cast h5
    exact abs_le.1 h6
  exact Finset.single_le_sum (f := fun k => |f k|) (fun _ _ => abs_nonneg _) hmem

/-- The step function of `f` as an element of `locallySqIntegrable d`. -/
noncomputable def latticeStepFun (f : (Fin d → ℤ) → ℝ) : locallySqIntegrable d :=
  ⟨latticeStep f, fun c R => memLp_latticeStep f c R⟩

@[simp] theorem latticeStepFun_apply (f : (Fin d → ℤ) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    (latticeStepFun f : EuclideanSpace ℝ (Fin d) → ℝ) x = f (latticePointOf x) :=
  rfl

theorem latticePointOf_latticeEuclideanEmbedding (k : Fin d → ℤ) :
    latticePointOf (LatticeProb.Percolation.latticeEuclideanEmbedding k) = k := by
  funext i
  simp only [latticePointOf]
  have : (LatticeProb.Percolation.latticeEuclideanEmbedding k) i = (k i : ℝ) := rfl
  rw [this, Int.floor_eq_iff]
  constructor <;> linarith

end Rigidity.Proofs.Regularity
