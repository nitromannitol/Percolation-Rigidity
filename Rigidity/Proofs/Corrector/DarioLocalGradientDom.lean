import Rigidity.Proofs.Corrector.DarioLocalGradient

/-!
# The local gradient bound dominates the corrector

* `mem_localCluster_of_infinite`: the points of the infinite cluster in `B(0, R)` are in the local
  cluster (an open path to infinity leaves `B(0, 2R)` through its boundary, `exists_exit_openWalk`);
* `abs_correctorDiff_le_localGrad`: if the local cluster lies in the infinite cluster and the
  corrector of slope `e_i` rooted at the origin is at most `R` there, the corrected plane rooted at
  the origin is admissible, so `|χ(0) - χ(w)| ≤ localGrad R ω + 1` along every open edge `{0, w}`.

This is the deterministic part of the finite-range domination of the weight of the Step 2 sum.
-/

namespace Rigidity.Corrector

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.Proofs.Section5 Rigidity.Poincare
open scoped Classical

/-- An open walk from a set to its complement leaves it along an open edge. -/
theorem exists_exit_openWalk {ω : Configuration 2} {B : Set (Vertex 2)} :
    ∀ {u v : Vertex 2} (W : (openGraph ω).Walk u v), u ∈ B → v ∉ B →
      ∃ p q, (openGraph ω).Adj p q ∧ q ∉ B ∧ ReachIn ω B u p
  | _, _, .nil, hu, hv => absurd hu hv
  | u, _, .cons (v := w) h W', hu, hv => by
      by_cases hw : w ∈ B
      · obtain ⟨p, q, hpq, hq, W₁, hW₁⟩ := exists_exit_openWalk W' hw hv
        refine ⟨p, q, hpq, hq, .cons h W₁, fun z hz => ?_⟩
        rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hu
        · exact hW₁ z hz
      · refine ⟨u, w, h, hw, .nil, fun z hz => ?_⟩
        rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
        rw [hz]
        exact hu

theorem abs_le_of_mem_supBox_zero {z : Vertex 2} {r : ℕ} (h : z ∈ supBox (0 : Vertex 2) r)
    (i : Fin 2) : |z i| ≤ r := by
  have := (mem_supBox.1 h) i
  simpa using this

/-- **The points of the infinite cluster in `B(0, R)` are in the local cluster.** -/
theorem mem_localCluster_of_infinite {ω : Configuration 2} {R : ℕ} {y : Vertex 2}
    (hy : y ∈ supBox (0 : Vertex 2) R) (hinf : ω ∈ infiniteComponentEvent y) :
    y ∈ localCluster R ω := by
  have hinf' : ((openGraph ω).connectedComponentMk y).supp.Infinite := hinf
  obtain ⟨b, hb, hbB⟩ :=
    (hinf'.sdiff (Finset.finite_toSet (supBox (0 : Vertex 2) (2 * R)))).nonempty
  have hreach : (openGraph ω).Reachable y b :=
    (SimpleGraph.ConnectedComponent.exact
      ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hb)).symm
  have hy2 : y ∈ (↑(supBox (0 : Vertex 2) (2 * R)) : Set (Vertex 2)) :=
    Finset.mem_coe.2 (supBox_mono (by omega) hy)
  obtain ⟨p, q, hpq, hq, hW⟩ := exists_exit_openWalk hreach.some hy2 hbB
  have hp : p ∈ supBox (0 : Vertex 2) (2 * R) := by
    obtain ⟨W, hWs⟩ := hW
    exact Finset.mem_coe.1 (hWs p W.end_mem_support)
  refine Finset.mem_filter.2 ⟨hy, p, hp, ?_, hW⟩
  have hq' : ¬ ∀ i, |q i - (0 : Vertex 2) i| ≤ ((2 * R : ℕ) : ℤ) := fun h =>
    hq (Finset.mem_coe.2 (mem_supBox.2 h))
  push Not at hq'
  obtain ⟨i, hi⟩ := hq'
  refine ⟨i, ?_⟩
  have h1 := abs_sub_le_one_of_adj hpq i
  have h1' : |p i - q i| ≤ 1 := by exact_mod_cast h1
  have h2 : (2 * R : ℤ) < |q i| := by simpa using hi
  have t := abs_sub_abs_le_abs_sub (q i) (p i)
  rw [abs_sub_comm (q i) (p i)] at t
  push_cast
  omega

section Planes

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

theorem correctorDiff_self_of_mem {q : Fin 2 → ℝ} {ω : Configuration 2} (hω : ω ∈ G) {a : Vertex 2}
    (ha : ω ∈ infiniteComponentEvent a) : correctorDiff hG hGv q ω a a = 0 := by
  have := correctorDiff_sub_eq hG hGv (q := q) hω ha ha ha
  linarith

/-- **The local gradient bound dominates the corrector at the origin.** -/
theorem abs_correctorDiff_le_localGrad {ω : Configuration 2} (hω : ω ∈ G) {R : ℕ} (hR : 1 ≤ R)
    {i : Fin 2} (h0 : ω ∈ infiniteComponentEvent 0)
    (hsub : ∀ y ∈ localCluster R ω, ω ∈ infiniteComponentEvent y)
    (hosc : ∀ y ∈ localCluster R ω, |correctorDiff hG hGv (Pi.single i 1) ω y 0| ≤ R)
    {w : Vertex 2} (hw : (openGraph ω).Adj 0 w) :
    |correctorDiff hG hGv (Pi.single i 1) ω 0 w| ≤ localGrad R ω + 1 := by
  obtain ⟨h', -⟩ := hGv hω
  set K := uniqueInfiniteComponent h' with hK
  have hKinf := uniqueInfiniteComponent_infinite h'
  obtain ⟨ℓ, hℓ⟩ := exists_correctedPlane_of_valid (hGv hω) hKinf (Pi.single i 1)
  have hmemK : ∀ y, ω ∈ infiniteComponentEvent y → y ∈ K.supp := fun y hy =>
    (mem_uniqueInfiniteComponent_iff h' y).2 hy
  have h0K := hmemK 0 h0
  set u : K → ℝ := fun y => ℓ y - ℓ ⟨0, h0K⟩ with hu
  have hharm : ∀ z, componentLaplacian K u z = 0 := by
    intro z
    simp only [componentLaplacian, hu, sub_sub_sub_cancel_right]
    exact hℓ.1.1 z
  -- the rooted corrected plane through the corrector
  set f : Vertex 2 → ℝ := fun y => if ω ∈ infiniteComponentEvent y then
    correctorDiff hG hGv (Pi.single i 1) ω y 0 + (y i : ℝ) else 0 with hf
  have hfu : ∀ y, f y = extendComp K u y := by
    intro y
    by_cases hy : ω ∈ infiniteComponentEvent y
    · have hyK := hmemK y hy
      simp only [hf, if_pos hy]
      rw [extendComp_of_mem _ _ hyK,
        correctorDiff_eq hG hGv hω hKinf hℓ ⟨y, hyK⟩ ⟨0, h0K⟩, sum_single_mul_coord,
        sum_single_mul_coord]
      simp only [hu, Pi.zero_apply, Int.cast_zero]
      ring
    · have hyK : y ∉ K.supp := fun h => hy ((mem_uniqueInfiniteComponent_iff h' y).1 h)
      simp only [hf, if_neg hy, extendComp_of_not_mem _ _ hyK]
  have hadm : LocalAdmissible R ω f := by
    refine ⟨fun y hy _ => ?_, 0, fun y hy => ?_⟩
    · rw [show f = extendComp K u from funext hfu, openLaplacian_eq_edgeDiv]
      exact edgeDiv_edgeGrad_extendComp_of_harmonic K hharm (hmemK y (hsub y hy))
    · have hyinf := hsub y hy
      simp only [hf, if_pos hyinf, sub_zero]
      have h1 := hosc y hy
      have h2 := abs_le_of_mem_supBox_zero (Finset.mem_filter.1 hy).1 i
      have h2' : |(y i : ℝ)| ≤ R := by exact_mod_cast h2
      calc |correctorDiff hG hGv (Pi.single i 1) ω y 0 + (y i : ℝ)|
          ≤ |correctorDiff hG hGv (Pi.single i 1) ω y 0| + |(y i : ℝ)| := abs_add_le _ _
        _ ≤ 3 * R := by linarith
  have h0L : (0 : Vertex 2) ∈ localCluster R ω :=
    mem_localCluster_of_infinite (by rw [mem_supBox]; intro k; simp) h0
  have hbound := abs_sub_le_localGrad hR hadm h0L hw
  have hwinf := mem_infiniteComponentEvent_of_adj hw h0
  have hf0 : f 0 = 0 := by
    simp only [hf, if_pos h0, correctorDiff_self_of_mem hG hGv (q := Pi.single i 1) hω h0,
      Pi.zero_apply, Int.cast_zero, add_zero]
  have hfw : f w = correctorDiff hG hGv (Pi.single i 1) ω w 0 + (w i : ℝ) := by
    simp only [hf, if_pos hwinf]
  have hanti : correctorDiff hG hGv (Pi.single i 1) ω 0 w =
      -correctorDiff hG hGv (Pi.single i 1) ω w 0 := by
    have := correctorDiff_sub_eq hG hGv (q := Pi.single i 1) hω h0 hwinf h0
    rw [correctorDiff_self_of_mem hG hGv (q := Pi.single i 1) hω h0] at this
    linarith
  rw [hf0, hfw, zero_sub, abs_neg] at hbound
  have hwi : |(w i : ℝ)| ≤ 1 := by
    have := abs_sub_le_one_of_adj hw i
    simpa using this
  rw [hanti, abs_neg]
  calc |correctorDiff hG hGv (Pi.single i 1) ω w 0|
      = |(correctorDiff hG hGv (Pi.single i 1) ω w 0 + (w i : ℝ)) - (w i : ℝ)| := by ring_nf
    _ ≤ |correctorDiff hG hGv (Pi.single i 1) ω w 0 + (w i : ℝ)| + |(w i : ℝ)| := abs_sub _ _
    _ ≤ localGrad R ω + 1 := by linarith

end Planes

end Rigidity.Corrector
