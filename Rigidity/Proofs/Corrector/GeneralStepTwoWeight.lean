import Rigidity.Proofs.Corrector.GeneralCaseField

/-!
# The weight of the Step 2 sum on `ℤᵈ`: the side, the plane gradient and the open energy

The bound of the Step 2 sum of the proof of Lemma 3.3 of Dario is written with (the definitions of
the planar file `DarioStepTwoWeight`, for the partition into good cubes of `ℤᵈ`)

* the side `s(z)` of the partition cube at `z`, through the stopping size (`partSide`);
* a bound `G(z)` for the gradient of the corrected plane of slope `e_i` at `z`: one plus the
  corrector increments along the open edges at `z` (`planeGrad`), so that
  `|χ(z) - χ(w)| + 1 ≤ G(z)` along every open edge `{z, w}` (`abs_correctorDiff_add_one_le`);
* the open energy `E_f(u) = Σ_{w ~ u} (f(u) - f(w))²` of a function at a vertex (`openEnergy`).

The total variations of Step 1 are bounded by these: `V_S(f) ≤ 2d Σ_{u ∈ S} g(u)` when `f` changes
by at most `g(u)` along the open edges at `u` (`edgeVariationIn_le_mul_sum`), and
`V_S(f)² ≤ 2d |S| Σ_{u ∈ S} E_f(u)` (`sq_edgeVariationIn_le`, Cauchy–Schwarz).
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical ENNReal InnerProductSpace

variable {d : ℕ}

/-- The side of the partition cube at `z`, through the stopping size. -/
noncomputable def partSide (ω : Configuration d) (z : Vertex d) : ℕ :=
  ⌊TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z⌋₊

theorem measurable_partSide (z : Vertex d) : Measurable fun ω => partSide ω z :=
  Nat.measurable_floor.comp (measurable_stoppingSize_goodCubes z)

theorem partSide_eq {ω : Configuration d} (hP : PartitionEvent ω) (z : Vertex d) :
    partSide ω z = 3 ^ (partitionCube ω z).scale := by
  unfold partSide
  rw [stoppingSize_goodCubes_eq hP z]
  rw [show (3 : ℝ) ^ (partitionCube ω z).scale =
    ((3 ^ (partitionCube ω z).scale : ℕ) : ℝ) by push_cast; rfl, Nat.floor_natCast]

/-- The open energy of `f` at `u`. -/
noncomputable def openEnergy (ω : Configuration d) (f : Vertex d → ℝ) (u : Vertex d) : ℝ :=
  ∑ w ∈ (openGraph ω).neighborFinset u, (f u - f w) ^ 2

theorem openEnergy_nonneg (ω : Configuration d) (f : Vertex d → ℝ) (u : Vertex d) :
    0 ≤ openEnergy ω f u :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sq_sub_le_openEnergy {ω : Configuration d} (f : Vertex d → ℝ) {u w : Vertex d}
    (h : (openGraph ω).Adj u w) : (f u - f w) ^ 2 ≤ openEnergy ω f u :=
  Finset.single_le_sum (f := fun w => (f u - f w) ^ 2) (fun _ _ => sq_nonneg _)
    ((SimpleGraph.mem_neighborFinset _ _ _).2 h)

/-- **The total variation by a pointwise bound**: if `f` changes by at most `g(u)` along the open
edges at `u`, then `V_S(f) ≤ 2d Σ_{u ∈ S} g(u)`. -/
theorem edgeVariationIn_le_mul_sum {ω : Configuration d} (S : Finset (Vertex d))
    {f g : Vertex d → ℝ} (hg : ∀ u, 0 ≤ g u)
    (hf : ∀ u w, (openGraph ω).Adj u w → |f u - f w| ≤ g u) :
    edgeVariationIn ω S f ≤ 2 * d * ∑ u ∈ S, g u := by
  unfold edgeVariationIn
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun u _ => ?_
  have hterm : ∀ w ∈ S, (if (openGraph ω).Adj u w then |f u - f w| else 0) ≤
      if (openGraph ω).Adj u w then g u else 0 := by
    intro w _
    split_ifs with huw
    · exact hf u w huw
    · exact le_rfl
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have h4 : ((S.filter fun w => (openGraph ω).Adj u w).card : ℝ) ≤ 2 * d := by
    exact_mod_cast card_filter_adj_le ω S u
  nlinarith [hg u]

/-- **The total variation by the energy** (Cauchy–Schwarz): `V_S(f)² ≤ 2d |S| Σ_{u ∈ S} E_f(u)`. -/
theorem sq_edgeVariationIn_le (ω : Configuration d) (S : Finset (Vertex d)) (f : Vertex d → ℝ) :
    edgeVariationIn ω S f ^ 2 ≤ 2 * d * S.card * ∑ u ∈ S, openEnergy ω f u := by
  unfold edgeVariationIn
  have hu : ∀ u ∈ S, (∑ w ∈ S, if (openGraph ω).Adj u w then |f u - f w| else 0) ^ 2 ≤
      2 * d * openEnergy ω f u := by
    intro u _
    rw [← Finset.sum_filter]
    have hc : ((S.filter fun w => (openGraph ω).Adj u w).card : ℝ) ≤ 2 * d := by
      exact_mod_cast card_filter_adj_le ω S u
    have hsub : S.filter (fun w => (openGraph ω).Adj u w) ⊆ (openGraph ω).neighborFinset u :=
      fun w hw => (SimpleGraph.mem_neighborFinset _ _ _).2 (Finset.mem_filter.1 hw).2
    have hs : ∑ w ∈ S.filter (fun w => (openGraph ω).Adj u w), |f u - f w| ^ 2 ≤
        openEnergy ω f u := by
      simp only [sq_abs]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
    have h0 : 0 ≤ ∑ w ∈ S.filter (fun w => (openGraph ω).Adj u w), |f u - f w| ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hcs := sq_sum_le_card_mul_sum_sq (s := S.filter (fun w => (openGraph ω).Adj u w))
      (f := fun w => |f u - f w|)
    nlinarith
  have hcs := sq_sum_le_card_mul_sum_sq (s := S)
    (f := fun u => ∑ w ∈ S, if (openGraph ω).Adj u w then |f u - f w| else 0)
  calc _ ≤ (S.card : ℝ) * ∑ u ∈ S,
        (∑ w ∈ S, if (openGraph ω).Adj u w then |f u - f w| else 0) ^ 2 := hcs
    _ ≤ S.card * ∑ u ∈ S, 2 * d * openEnergy ω f u :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hu) (Nat.cast_nonneg _)
    _ = 2 * d * S.card * ∑ u ∈ S, openEnergy ω f u := by rw [← Finset.mul_sum]; ring

/-- Along a walk of the cluster, the sum of `P ξ` is the increment of its potential on the
cluster. -/
theorem walkSum_greenProj_eq_clusterPot {ω : Configuration d} (ξ : EdgeField d) {u v : Vertex d}
    (p : (openGraph ω).Walk u v) (hu : ω ∈ infiniteComponentEvent u) :
    walkSum ω (greenProj ω ξ) p = clusterPot ω ξ v - clusterPot ω ξ u := by
  have hv : ω ∈ infiniteComponentEvent v := by
    change ((openGraph ω).connectedComponentMk v).supp.Infinite
    rw [← SimpleGraph.ConnectedComponent.sound p.reachable]
    exact hu
  rw [walkSum_eq_of_isGradOf _ (exists_isGradOf_greenProj ω ξ).choose_spec p]
  unfold clusterPot
  rw [if_pos hu, if_pos hv]

theorem abs_sub_le_one_of_adj {ω : Configuration d} {u w : Vertex d} (h : (openGraph ω).Adj u w)
    (i : Fin d) : |(u i : ℝ) - (w i : ℝ)| ≤ 1 := by
  obtain ⟨k, hk | hk⟩ := LatticeProb.Graph.Zd.adj_iff.1 (openGraph_le ω h)
  · have hw : w = u + LatticeProb.unit k := hk
    have := (abs_sub_add_unit_le u k i).1
    rw [← hw] at this
    exact_mod_cast this
  · have hu : u = w + LatticeProb.unit k := by rw [hk]; abel
    have := (abs_sub_add_unit_le w k i).2
    rw [← hu] at this
    exact_mod_cast this

/-- The box `anchorBox` of the partition cube at `z` lies in the box of radius `L + 5 s(z)` around
any `x` with `|z - x|_∞ ≤ L`. -/
theorem anchorBox_subset_boxFinset {ω : Configuration d} (hP : PartitionEvent ω)
    {x z : Vertex d} {L : ℕ} (hzx : ∀ i, |z i - x i| ≤ L) :
    anchorBox ω z ⊆ LatticeProb.boxFinset x (L + 5 * partSide ω z) := by
  intro w hw
  rw [mem_anchorBox] at hw
  rw [LatticeProb.mem_boxFinset_iff]
  intro i
  have h1 := hw i
  have h2 := hzx i
  have hs : 3 ^ ((partitionCube ω z).scale + 1) ≤ 5 * partSide ω z := by
    rw [partSide_eq hP z, pow_succ]
    omega
  have hs' : ((3 ^ ((partitionCube ω z).scale + 1) : ℕ) : ℤ) ≤ ((5 * partSide ω z : ℕ) : ℤ) := by
    exact_mod_cast hs
  have h3 : |w i - x i| ≤ |w i - z i| + |z i - x i| := abs_sub_le _ _ _
  push_cast at hs' h1 ⊢
  linarith

theorem sq_le_of_abs_le_two_mul_add {Δ V₁ V₂ X : ℝ} (hΔ : |Δ| ≤ 2 * (V₁ + V₂))
    (h1 : V₁ ^ 2 ≤ X) (h2 : V₂ ^ 2 ≤ X) : Δ ^ 2 ≤ 16 * X := by
  have hsq : Δ ^ 2 ≤ (2 * (V₁ + V₂)) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hΔ 2
  nlinarith [sq_nonneg (V₁ - V₂)]

theorem boxFinset_mono {x : Vertex d} {r r' : ℕ} (h : r ≤ r') :
    LatticeProb.boxFinset x r ⊆ LatticeProb.boxFinset x r' := by
  intro z hz
  rw [LatticeProb.mem_boxFinset_iff] at hz ⊢
  intro i
  exact (hz i).trans (by exact_mod_cast h)

section Grad

variable {G : Set (Configuration d)} (hG : MeasurableSet G)
  (hGv : G ⊆ correctorValidEvent d)

/-- A bound for the gradient of the corrected plane of slope `e_i` at `z`. -/
noncomputable def planeGrad (i : Fin d) (ω : Configuration d) (z : Vertex d) : ℝ :=
  1 + ∑ k : Fin d,
    ((if EdgeOpen ω (z, k) then
        |correctorDiff hG hGv (Pi.single i 1) ω z (z + LatticeProb.unit k)| else 0) +
      (if EdgeOpen ω (z - LatticeProb.unit k, k) then
        |correctorDiff hG hGv (Pi.single i 1) ω z (z - LatticeProb.unit k)| else 0))

theorem planeGrad_term_nonneg (i : Fin d) (ω : Configuration d) (z : Vertex d) (k : Fin d) :
    0 ≤ (if EdgeOpen ω (z, k) then
        |correctorDiff hG hGv (Pi.single i 1) ω z (z + LatticeProb.unit k)| else 0) +
      (if EdgeOpen ω (z - LatticeProb.unit k, k) then
        |correctorDiff hG hGv (Pi.single i 1) ω z (z - LatticeProb.unit k)| else 0) := by
  refine add_nonneg ?_ ?_ <;> split_ifs <;> positivity

theorem one_le_planeGrad (i : Fin d) (ω : Configuration d) (z : Vertex d) :
    1 ≤ planeGrad hG hGv i ω z := by
  unfold planeGrad
  have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => planeGrad_term_nonneg hG hGv i ω z k
  linarith

theorem planeGrad_nonneg (i : Fin d) (ω : Configuration d) (z : Vertex d) :
    0 ≤ planeGrad hG hGv i ω z :=
  zero_le_one.trans (one_le_planeGrad hG hGv i ω z)

/-- `|χ(z) - χ(w)| + 1 ≤ G(z)` along every open edge `{z, w}`. -/
theorem abs_correctorDiff_add_one_le {i : Fin d} {ω : Configuration d} {z w : Vertex d}
    (h : (openGraph ω).Adj z w) :
    |correctorDiff hG hGv (Pi.single i 1) ω z w| + 1 ≤ planeGrad hG hGv i ω z := by
  have hsum : ∀ k, (if EdgeOpen ω (z, k) then
        |correctorDiff hG hGv (Pi.single i 1) ω z (z + LatticeProb.unit k)| else 0) +
      (if EdgeOpen ω (z - LatticeProb.unit k, k) then
        |correctorDiff hG hGv (Pi.single i 1) ω z (z - LatticeProb.unit k)| else 0) ≤
      ∑ k : Fin d, ((if EdgeOpen ω (z, k) then
        |correctorDiff hG hGv (Pi.single i 1) ω z (z + LatticeProb.unit k)| else 0) +
      (if EdgeOpen ω (z - LatticeProb.unit k, k) then
        |correctorDiff hG hGv (Pi.single i 1) ω z (z - LatticeProb.unit k)| else 0)) :=
    fun k => Finset.single_le_sum (f := fun k => (if EdgeOpen ω (z, k) then
        |correctorDiff hG hGv (Pi.single i 1) ω z (z + LatticeProb.unit k)| else 0) +
      (if EdgeOpen ω (z - LatticeProb.unit k, k) then
        |correctorDiff hG hGv (Pi.single i 1) ω z (z - LatticeProb.unit k)| else 0))
      (fun k _ => planeGrad_term_nonneg hG hGv i ω z k) (Finset.mem_univ k)
  unfold planeGrad
  obtain ⟨k, hk | hk⟩ := LatticeProb.Graph.Zd.adj_iff.1 (openGraph_le ω h)
  · have hw : w = z + LatticeProb.unit k := hk
    have hopen : EdgeOpen ω (z, k) := by
      unfold EdgeOpen edgeHead
      rw [← hw]
      exact h
    have h2 := hsum k
    rw [if_pos hopen, ← hw] at h2
    have h3 : 0 ≤ (if EdgeOpen ω (z - LatticeProb.unit k, k) then
        |correctorDiff hG hGv (Pi.single i 1) ω z (z - LatticeProb.unit k)| else 0) := by
      split_ifs <;> positivity
    linarith
  · have hw : w = z - LatticeProb.unit k := hk
    have hopen : EdgeOpen ω (z - LatticeProb.unit k, k) := by
      unfold EdgeOpen edgeHead
      rw [sub_add_cancel, ← hw]
      exact h.symm
    have h2 := hsum k
    rw [if_pos hopen, ← hw] at h2
    have h3 : 0 ≤ (if EdgeOpen ω (z, k) then
        |correctorDiff hG hGv (Pi.single i 1) ω z (z + LatticeProb.unit k)| else 0) := by
      split_ifs <;> positivity
    linarith

/-- The corrected plane of slope `e_i` rooted at `o`, extended by `0` off the infinite cluster,
changes by at most `G(u)` along the open edges at `u`. -/
theorem abs_sub_rootedPlane_le [NeZero d] {i : Fin d} {ω : Configuration d} (hω : ω ∈ G) {o : Vertex d}
    (ho : ω ∈ infiniteComponentEvent o) {u w : Vertex d} (h : (openGraph ω).Adj u w) :
    |(if ω ∈ infiniteComponentEvent u then
          correctorDiff hG hGv (Pi.single i 1) ω u o + (u i : ℝ) else 0) -
        (if ω ∈ infiniteComponentEvent w then
          correctorDiff hG hGv (Pi.single i 1) ω w o + (w i : ℝ) else 0)| ≤
      planeGrad hG hGv i ω u := by
  by_cases hu : ω ∈ infiniteComponentEvent u
  · have hw := mem_infiniteComponentEvent_of_adj h hu
    rw [if_pos hu, if_pos hw]
    have e := correctorDiff_sub_eq hG hGv (q := Pi.single i 1) hω hu hw ho
    have h1 := abs_correctorDiff_add_one_le hG hGv (i := i) h
    have h2 := abs_sub_le_one_of_adj h i
    calc |correctorDiff hG hGv (Pi.single i 1) ω u o + (u i : ℝ) -
          (correctorDiff hG hGv (Pi.single i 1) ω w o + (w i : ℝ))|
        = |correctorDiff hG hGv (Pi.single i 1) ω u w + ((u i : ℝ) - (w i : ℝ))| := by
          rw [← e]; ring_nf
      _ ≤ |correctorDiff hG hGv (Pi.single i 1) ω u w| + |(u i : ℝ) - (w i : ℝ)| := abs_add_le _ _
      _ ≤ planeGrad hG hGv i ω u := by linarith
  · have hw : ω ∉ infiniteComponentEvent w := fun hw =>
      hu (mem_infiniteComponentEvent_of_adj h.symm hw)
    rw [if_neg hu, if_neg hw, sub_zero, abs_zero]
    exact planeGrad_nonneg hG hGv i ω u

end Grad

end Rigidity.Corrector.GeneralDim
