import Rigidity.Proofs.Regularity.ContinuumBallExcess
import Mathlib.MeasureTheory.Function.Floor
import LatticeProb.Prob.Percolation.LatticeClusterBall

/-!
# Step functions of lattice functions

A function `f` on `ℤ^d` extends to `ℝ^d` as the step function constant on the unit cubes
`k + [-1/2, 1/2)^d` (`latticeStep f`), the extension by which Armstrong and Dario
(arXiv:1609.09431v2, Section 7) regard coarsened functions `[u]_P` as functions on `ℝ^d`. It is
square integrable on every ball (`latticeStepFun f ∈ locallySqIntegrable d`), so the continuum
instances of Lemma 7.2 apply to it. The integral of `(latticeStep f)²` over `B_r(z)` lies between
the sums of `f²` over the lattice points whose cubes lie in `B_r(z)` and over those whose cubes
meet it (`sum_sq_le_integral_sq_latticeStep`, `integral_sq_latticeStep_le_sum`), the unit cubes
having volume one (`volume_latticeCube`).
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

/-- The unit cube `k + [-1/2, 1/2)^d` on which `latticeStep f` takes the value `f k`. -/
def latticeCube (k : Fin d → ℤ) : Set (EuclideanSpace ℝ (Fin d)) := latticePointOf ⁻¹' {k}

theorem measurableSet_latticeCube (k : Fin d → ℤ) : MeasurableSet (latticeCube k) :=
  measurable_latticePointOf (measurableSet_singleton k)

theorem latticeCube_eq (k : Fin d → ℤ) :
    latticeCube k = (fun x : EuclideanSpace ℝ (Fin d) => WithLp.ofLp x) ⁻¹'
      Set.pi Set.univ fun i => Set.Ico ((k i : ℝ) - 1 / 2) (k i + 1 / 2) := by
  ext x
  simp only [latticeCube, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ,
    true_implies, Set.mem_Ico, latticePointOf, funext_iff, Int.floor_eq_iff]
  refine forall_congr' fun i => ?_
  change (k i : ℝ) ≤ x i + 1 / 2 ∧ x i + 1 / 2 < k i + 1 ↔
    (k i : ℝ) - 1 / 2 ≤ x i ∧ x i < k i + 1 / 2
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem volume_latticeCube (k : Fin d → ℤ) : volume (latticeCube k) = 1 := by
  rw [latticeCube_eq, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico).nullMeasurableSet, volume_pi_pi]
  simp only [Real.volume_Ico]
  have e : ∀ i : Fin d, (k i : ℝ) + 1 / 2 - ((k i : ℝ) - 1 / 2) = 1 := fun i => by ring
  simp only [e, ENNReal.ofReal_one, Finset.prod_const_one]

theorem setIntegral_sq_latticeCube (f : (Fin d → ℤ) → ℝ) (k : Fin d → ℤ) :
    ∫ x in latticeCube k, latticeStep f x ^ 2 = f k ^ 2 := by
  have heq : Set.EqOn (fun x => latticeStep f x ^ 2) (fun _ => f k ^ 2) (latticeCube k) :=
    fun x hx => by
      have hxk : latticePointOf x = k := Set.mem_singleton_iff.1 hx
      simp only [latticeStep, hxk]
  rw [setIntegral_congr_fun (measurableSet_latticeCube k) heq, setIntegral_const, Measure.real,
    volume_latticeCube, ENNReal.toReal_one, one_smul]

theorem integrableOn_sq_latticeCube (f : (Fin d → ℤ) → ℝ) (k : Fin d → ℤ) :
    IntegrableOn (fun x => latticeStep f x ^ 2) (latticeCube k) := by
  have h : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin d) => f k ^ 2) (latticeCube k) :=
    integrableOn_const (by rw [volume_latticeCube]; exact ENNReal.one_ne_top)
  refine h.congr_fun (fun x hx => ?_) (measurableSet_latticeCube k)
  have hxk : latticePointOf x = k := Set.mem_singleton_iff.1 hx
  simp only [latticeStep, hxk]

theorem pairwise_disjoint_latticeCube (S : Set (Fin d → ℤ)) :
    S.Pairwise (Function.onFun Disjoint (latticeCube (d := d))) := by
  intro k _ l _ hkl
  exact Set.disjoint_left.2 fun x hk hl =>
    hkl ((Set.mem_singleton_iff.1 hk).symm.trans (Set.mem_singleton_iff.1 hl))

theorem setIntegral_sq_biUnion_latticeCube (f : (Fin d → ℤ) → ℝ) (S : Finset (Fin d → ℤ)) :
    ∫ x in ⋃ k ∈ S, latticeCube k, latticeStep f x ^ 2 = ∑ k ∈ S, f k ^ 2 := by
  rw [integral_biUnion_finset S (fun k _ => measurableSet_latticeCube k)
    (pairwise_disjoint_latticeCube _) (fun k _ => integrableOn_sq_latticeCube f k)]
  exact Finset.sum_congr rfl fun k _ => setIntegral_sq_latticeCube f k

/-- **Lower bound by lattice sums**: the cubes of `S` lie in `B_r(z)`. -/
theorem sum_sq_le_integral_sq_latticeStep (f : (Fin d → ℤ) → ℝ) (z : EuclideanSpace ℝ (Fin d))
    (r : ℝ) (S : Finset (Fin d → ℤ)) (hS : ∀ k ∈ S, latticeCube k ⊆ ball z r) :
    ∑ k ∈ S, f k ^ 2 ≤ ∫ x in ball z r, latticeStep f x ^ 2 := by
  rw [← setIntegral_sq_biUnion_latticeCube]
  have hsub : (⋃ k ∈ S, latticeCube k) ⊆ ball z r := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨k, hk, hxk⟩ := hx
    exact hS k hk hxk
  exact setIntegral_mono_set (memLp_latticeStep f z r).integrable_sq
    (Filter.Eventually.of_forall fun _ => sq_nonneg _) hsub.eventuallyLE

/-- **Upper bound by lattice sums**: `S` contains the lattice points of the cubes meeting
`B_r(z)`. -/
theorem integral_sq_latticeStep_le_sum (f : (Fin d → ℤ) → ℝ) (z : EuclideanSpace ℝ (Fin d))
    (r : ℝ) (S : Finset (Fin d → ℤ)) (hS : ∀ x ∈ ball z r, latticePointOf x ∈ S) :
    ∫ x in ball z r, latticeStep f x ^ 2 ≤ ∑ k ∈ S, f k ^ 2 := by
  rw [← setIntegral_sq_biUnion_latticeCube]
  have hint : IntegrableOn (fun x => latticeStep f x ^ 2) (⋃ k ∈ S, latticeCube k) :=
    (integrableOn_finset_iUnion).2 fun k _ => integrableOn_sq_latticeCube f k
  have hsub : ball z r ⊆ ⋃ k ∈ S, latticeCube k := by
    intro x hx
    simp only [Set.mem_iUnion]
    exact ⟨latticePointOf x, hS x hx, Set.mem_singleton _⟩
  exact setIntegral_mono_set hint (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    hsub.eventuallyLE

end Rigidity.Proofs.Regularity
