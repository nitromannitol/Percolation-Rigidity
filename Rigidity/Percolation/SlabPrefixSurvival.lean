import Rigidity.Percolation.SlabPrefixGeometry

/-!
# Survival of components across cube slabs

Two components survive to a slab when both reach its boundary and remain
unconnected in the explored prefix. These events are measurable in past bonds
and decrease as the prefix expands.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External
open scoped MeasureTheory

/-- Both components reach the next slab without joining in the prefix. -/
def IntegerCube.slabPrefixSurvival {d : ℕ} (Q : IntegerCube d) (j : Fin d)
    (width k : ℕ) (z z' : Vertex d) : Set (Configuration d) :=
  {ω | slabBoundaryReachable (Q.slabPrefix j width k) (Q.slab j width k) z ω ∧
    slabBoundaryReachable (Q.slabPrefix j width k) (Q.slab j width k) z' ω ∧
    ¬ (openIn ω (Q.slabPrefix j width k)).Reachable z z'}

/-- Survival depends only on bonds internal to the explored prefix. -/
theorem IntegerCube.measurableSet_slabPrefixSurvival {d : ℕ} (Q : IntegerCube d)
    (j : Fin d) (width k : ℕ) {z z' : Vertex d}
    (hz : z ∈ Q.slabPrefix j width k) (hz' : z' ∈ Q.slabPrefix j width k) :
    MeasurableSet[bondSigma (localBonds (Q.slabPrefix j width k))]
      (Q.slabPrefixSurvival j width k z z') := by
  exact (measurableSet_slabBoundaryReachable_bondSigma _ _
    (Q.finite_slabPrefix j width k) hz).inter
    ((measurableSet_slabBoundaryReachable_bondSigma _ _
      (Q.finite_slabPrefix j width k) hz').inter
      (measurableSet_reachable_openIn_bondSigma _
        (Q.finite_slabPrefix j width k) hz hz').compl)

/-- Surviving a later slab entails survival of the preceding slab. -/
theorem IntegerCube.slabPrefixSurvival_succ_subset {d : ℕ} (Q : IntegerCube d)
    (j : Fin d) {width k : ℕ} (hwidth : 0 < width) (hsize : k * width < Q.size)
    {z z' : Vertex d} (hz : z ∈ Q.slabPrefix j width k)
    (hz' : z' ∈ Q.slabPrefix j width k) :
    Q.slabPrefixSurvival j width (k + 1) z z' ⊆ Q.slabPrefixSurvival j width k z z' := by
  intro ω h
  refine ⟨Q.slabBoundaryReachable_of_next j hwidth hsize hz h.1,
    Q.slabBoundaryReachable_of_next j hwidth hsize hz' h.2.1, ?_⟩
  intro hconn
  exact h.2.2 (reachable_openIn_mono (Q.slabPrefix_mono j width (Nat.le_succ k)) hconn)

/-- A slab is contained in the prefix ending immediately after it. -/
theorem IntegerCube.slab_subset_slabPrefix_succ {d : ℕ} (Q : IntegerCube d)
    (j : Fin d) (width k : ℕ) :
    Q.slab j width k ⊆ Q.slabPrefix j width (k + 1) := by
  intro x hx
  exact ⟨hx.1, hx.2.2⟩

/-- Under a uniform two-point bound in each fresh slab, the probability that
both components survive `n` slabs decays geometrically. -/
theorem IntegerCube.measureReal_slabPrefixSurvival_le {d : ℕ} (Q : IntegerCube d)
    (j : Fin d) (width k₀ N : ℕ) (hwidth : 0 < width)
    (hsize : ∀ n < N, (k₀ + n) * width < Q.size)
    (z z' : Vertex d) (hz : z ∈ Q.slabPrefix j width k₀)
    (hz' : z' ∈ Q.slabPrefix j width k₀) (p : unitInterval) (δ : ℝ) (hδ : δ ≤ 1)
    (hprob : ∀ n < N, ∀ y ∈ Q.slab j width (k₀ + n),
      ∀ y' ∈ Q.slab j width (k₀ + n), δ ≤ (latticeBondLaw d p).real
        {ω | (openIn ω (Q.slab j width (k₀ + n))).Reachable y y'}) :
    ∀ n ≤ N, (latticeBondLaw d p).real (Q.slabPrefixSurvival j width (k₀ + n) z z') ≤
      (1 - (p : ℝ) * ((p : ℝ) * δ)) ^ n := by
  have hfirst : (p : ℝ) * δ ≤ 1 := by
    calc
      (p : ℝ) * δ ≤ (p : ℝ) * 1 := mul_le_mul_of_nonneg_left hδ p.property.1
      _ ≤ 1 := by simpa using p.property.2
  have hq : 0 ≤ 1 - (p : ℝ) * ((p : ℝ) * δ) := by
    have h : (p : ℝ) * ((p : ℝ) * δ) ≤ 1 := by
      calc
        (p : ℝ) * ((p : ℝ) * δ) ≤ (p : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hfirst p.property.1
        _ ≤ 1 := by simpa using p.property.2
    exact sub_nonneg.mpr h
  intro n hn
  induction n with
  | zero => simpa only [Nat.add_zero, pow_zero] using
      (measureReal_le_one (μ := latticeBondLaw d p)
        (s := Q.slabPrefixSurvival j width k₀ z z'))
  | succ n ih =>
    have hn' : n < N := by omega
    have hzₙ : z ∈ Q.slabPrefix j width (k₀ + n) :=
      Q.slabPrefix_mono j width (Nat.le_add_right k₀ n) hz
    have hzₙ' : z' ∈ Q.slabPrefix j width (k₀ + n) :=
      Q.slabPrefix_mono j width (Nat.le_add_right k₀ n) hz'
    have hznext : z ∈ Q.slabPrefix j width (k₀ + n + 1) :=
      Q.slabPrefix_mono j width (Nat.le_succ _) hzₙ
    have hznext' : z' ∈ Q.slabPrefix j width (k₀ + n + 1) :=
      Q.slabPrefix_mono j width (Nat.le_succ _) hzₙ'
    let P := Q.slabPrefix j width (k₀ + n)
    let S := Q.slab j width (k₀ + n)
    let D := Q.slabPrefix j width (k₀ + n + 1)
    let G := Q.slabPrefixSurvival j width (k₀ + n) z z'
    let H := Q.slabPrefixSurvival j width (k₀ + n + 1) z z'
    let C : Set (Configuration d) := {ω | (openIn ω D).Reachable z z'}
    have hG : MeasurableSet[bondSigma (localBonds P)] G :=
      Q.measurableSet_slabPrefixSurvival j width (k₀ + n) hzₙ hzₙ'
    have hH : MeasurableSet H := bondSigma_le _ _
      (Q.measurableSet_slabPrefixSurvival j width (k₀ + n + 1) hznext hznext')
    have hC : MeasurableSet C := measurableSet_openIn_reachable D z z'
    have hHG : H ⊆ G := Q.slabPrefixSurvival_succ_subset j hwidth (hsize n hn') hzₙ hzₙ'
    have hHC : Disjoint H C := by
      rw [Set.disjoint_left]
      intro ω hω hconn
      exact hω.2.2 hconn
    have hcond : ∀ᵐ ω ∂(latticeBondLaw d p).restrict G,
        (p : ℝ) * ((p : ℝ) * δ) ≤ (latticeBondLaw d p)[
          C.indicator (fun _ => (1 : ℝ)) | bondSigma (localBonds P)] ω := by
      exact condExp_reachable_lower_of_two_boundary_candidates p P S D
        (Q.finite_slabPrefix j width (k₀ + n)) (Q.finite_slab j width (k₀ + n))
        (Q.disjoint_slabPrefix_slab j width (k₀ + n))
        (Q.slabPrefix_mono j width (Nat.le_succ _))
        (Q.slab_subset_slabPrefix_succ j width (k₀ + n))
        z z' hzₙ hzₙ' δ (hprob n hn')
    have hupper := condExp_indicator_le_one_sub_of_disjoint (latticeBondLaw d p)
      (bondSigma_le (localBonds P)) hH hC hHC ((p : ℝ) * ((p : ℝ) * δ)) hcond
    have hstep := measureReal_le_mul_of_condExp_indicator_le (latticeBondLaw d p)
      (bondSigma_le (localBonds P)) hG hH hHG (1 - (p : ℝ) * ((p : ℝ) * δ)) hupper
    have ih' := ih (by omega)
    change (latticeBondLaw d p).real H ≤ _
    calc
      (latticeBondLaw d p).real H ≤ (1 - (p : ℝ) * ((p : ℝ) * δ)) *
          (latticeBondLaw d p).real G := hstep
      _ ≤ (1 - (p : ℝ) * ((p : ℝ) * δ)) ^ (n + 1) := by
        simpa only [pow_succ, mul_comm] using mul_le_mul_of_nonneg_left ih' hq

/-- Two globally disconnected components that both leave a prefix survive at
its boundary. -/
theorem IntegerCube.slabPrefixSurvival_of_two_escapes {d : ℕ} (Q : IntegerCube d)
    (j : Fin d) {width k : ℕ} (hwidth : 0 < width) (hsize : k * width < Q.size)
    {ω : Configuration d} {z z' : Vertex d} (hz : z ∈ Q.slabPrefix j width k)
    (hz' : z' ∈ Q.slabPrefix j width k)
    (hescape : targetConnection Q.vertices (Q.vertices \ Q.slabPrefix j width k) z ω)
    (hescape' : targetConnection Q.vertices (Q.vertices \ Q.slabPrefix j width k) z' ω)
    (hsep : ¬ (openIn ω Q.vertices).Reachable z z') :
    ω ∈ Q.slabPrefixSurvival j width k z z' := by
  obtain ⟨w, _, hw, hzw⟩ := hescape
  obtain ⟨w', _, hw', hz'w'⟩ := hescape'
  refine ⟨Q.slabBoundaryReachable_of_reachable_outside_prefix j hwidth hsize hz hw.2 hzw,
    Q.slabBoundaryReachable_of_reachable_outside_prefix j hwidth hsize hz' hw'.2 hz'w', ?_⟩
  intro hconn
  exact hsep (reachable_openIn_mono (fun _ hx => hx.1) hconn)

/-- The probability that two disconnected components both leave a distant
prefix has the same geometric upper bound as slab survival. -/
theorem IntegerCube.measureReal_two_escapes_le {d : ℕ} (Q : IntegerCube d)
    (j : Fin d) (width k₀ N : ℕ) (hwidth : 0 < width)
    (hsize : ∀ n ≤ N, (k₀ + n) * width < Q.size)
    (z z' : Vertex d) (hz : z ∈ Q.slabPrefix j width k₀)
    (hz' : z' ∈ Q.slabPrefix j width k₀) (p : unitInterval) (δ : ℝ) (hδ : δ ≤ 1)
    (hprob : ∀ n < N, ∀ y ∈ Q.slab j width (k₀ + n),
      ∀ y' ∈ Q.slab j width (k₀ + n), δ ≤ (latticeBondLaw d p).real
        {ω | (openIn ω (Q.slab j width (k₀ + n))).Reachable y y'}) :
    (latticeBondLaw d p).real {ω |
      targetConnection Q.vertices (Q.vertices \ Q.slabPrefix j width (k₀ + N)) z ω ∧
      targetConnection Q.vertices (Q.vertices \ Q.slabPrefix j width (k₀ + N)) z' ω ∧
      ¬ (openIn ω Q.vertices).Reachable z z'} ≤
      (1 - (p : ℝ) * ((p : ℝ) * δ)) ^ N := by
  apply (measureReal_mono ?_ (measure_ne_top _ _)).trans
    (Q.measureReal_slabPrefixSurvival_le j width k₀ N hwidth
      (fun n hn => hsize n (Nat.le_of_lt hn)) z z' hz hz' p δ hδ hprob N le_rfl)
  intro ω hω
  exact Q.slabPrefixSurvival_of_two_escapes j hwidth (hsize N le_rfl)
    (Q.slabPrefix_mono j width (Nat.le_add_right k₀ N) hz)
    (Q.slabPrefix_mono j width (Nat.le_add_right k₀ N) hz') hω.1 hω.2.1 hω.2.2

end Rigidity.Percolation
