import Rigidity.Proofs.Corrector.GeneralCoarseningError

/-!
# The comparison (5.7) of the translated partitions in every dimension

Dario's (5.7) bounds `|[χ]_{𝒫_y}(z) - [χ]_𝒫(z)|` by `O_s(C)`. Here, for the partition into good
cubes of `ℤᵈ`, with `a' = a_{𝒫_y}(z)`:

* `χ(a') - χ(a_𝒫(a'))` is a coarsening error (5.10) at the cluster vertex `a'`;
* along a lattice walk from `z` to `a'` inside the box spanned by them (`exists_walk_near`), the
  anchors `a_𝒫(z)` and `a_𝒫(a')` are joined by an open path inside the union of the partition
  cubes of the vertices of the walk (Armstrong–Dario, Corollary 2.10,
  `Rigidity.Percolation.reachable_partitionAnchor_of_walk`), so `χ(a_𝒫(a')) - χ(a_𝒫(z))` is
  bounded by the sums of (5.10) at the vertices of the walk;
* the walk lies in the ball of radius `d size(□_{𝒫_y}(z))` around `z`, and the moments follow
  from `lintegral_randomBallSum_le` with the moments of `stepSix_data` (`baseComparison`).

With (5.10) (`baseCoarseningError`), this reduces Dario's Theorem 1 in dimension `d ≥ 3` to (5.5)
at the origin with box oscillations bounded uniformly in the scale
(`darioOptimalCorrectorThree_of_baseTheorem`).
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter Set LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical ENNReal

variable {d : ℕ}

/-- **Monotone lattice walks**: a lattice walk from `z` to `z'` whose vertices `u` satisfy
`|u_i - z_i| ≤ |z'_i - z_i|` in every coordinate. -/
theorem exists_walk_near (z' : Vertex d) : ∀ (n : ℕ) (z : Vertex d),
    ∑ i, (z' i - z i).natAbs ≤ n →
    ∃ P : (nearestNeighborGraph d).Walk z z', ∀ u ∈ P.support, ∀ i, |u i - z i| ≤ |z' i - z i| := by
  intro n
  induction n with
  | zero =>
    intro z hz
    have he : z = z' := by
      funext i
      have := (Finset.sum_eq_zero_iff.1 (Nat.le_zero.1 hz)) i (Finset.mem_univ i)
      omega
    subst he
    refine ⟨SimpleGraph.Walk.nil, fun u hu i => ?_⟩
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hu
    rw [hu]
  | succ n ih =>
    intro z hz
    by_cases he : z = z'
    · subst he
      refine ⟨SimpleGraph.Walk.nil, fun u hu i => ?_⟩
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hu
      rw [hu]
    obtain ⟨j, hj⟩ : ∃ j, z j ≠ z' j := by
      by_contra h
      push Not at h
      exact he (funext h)
    set σ : ℤ := if z j < z' j then 1 else -1 with hσ
    set z₁ : Vertex d := z + Pi.single j σ with hz₁
    have hz₁j : z₁ j = z j + σ := by simp [hz₁]
    have hz₁i : ∀ i, i ≠ j → z₁ i = z i := fun i hi => by simp [hz₁, hi]
    have hadj : (nearestNeighborGraph d).Adj z z₁ := by
      change ∃ k : Fin d, z₁ = z + LatticeProb.unit k ∨ z = z₁ + LatticeProb.unit k
      refine ⟨j, ?_⟩
      by_cases hlt : z j < z' j
      · left
        simp only [hz₁, hσ, if_pos hlt, LatticeProb.unit]
      · right
        funext i
        by_cases hij : i = j
        · subst hij
          simp [hz₁, hσ, hlt, LatticeProb.unit]
        · simp [hz₁, LatticeProb.unit, hij]
    have hstep : (z' j - z₁ j).natAbs + 1 = (z' j - z j).natAbs := by
      rw [hz₁j]
      simp only [hσ]
      split_ifs with h <;> omega
    have hsum : ∑ i, (z' i - z₁ i).natAbs + 1 = ∑ i, (z' i - z i).natAbs := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ j),
        Finset.sum_congr rfl fun i hi => by rw [hz₁i i (Finset.ne_of_mem_erase hi)]]
      omega
    obtain ⟨P, hP⟩ := ih z₁ (by omega)
    refine ⟨SimpleGraph.Walk.cons hadj P, fun u hu i => ?_⟩
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hu
    rcases hu with rfl | hu
    · simp
    · have h1 := hP u hu i
      by_cases hij : i = j
      · subst hij
        rw [hz₁j] at h1
        rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at h1 ⊢
        simp only [hσ] at h1
        split_ifs at h1 with h <;> omega
      · rw [hz₁i i hij] at h1
        exact h1

/-- A sum over a union of finite sets of a nonnegative function is at most the sum of the sums. -/
theorem sum_biUnion_le_of_nonneg {ι : Type*} (s : Finset ι) (t : ι → Finset (Vertex d))
    {f : Vertex d → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ a ∈ s, ∑ x ∈ t a, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have h := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
    have h0 : 0 ≤ ∑ x ∈ t a ∩ s.biUnion t, f x := Finset.sum_nonneg fun x _ => hf x
    linarith

/-- The tail of `c size(□_𝒫(v))` from the exponential moment of the size. -/
theorem measure_le_const_mul_stoppingSize_le {p : unitInterval} {θ c : ℝ} (hθ : 0 < θ)
    (hc : 0 < c) (v : Vertex d)
    (hint : Integrable
      (fun ω => Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v / θ))
      (latticeBondLaw d p))
    (hb : ∫ ω, Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v / θ)
      ∂latticeBondLaw d p ≤ 2)
    (t : ℝ) :
    latticeBondLaw d p {ω | t ≤ c * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v} ≤
      ENNReal.ofReal (2 * Real.exp (-(t / (c * θ)))) := by
  set f : Configuration d → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v / θ))
  have hsub : {ω | t ≤ c * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v} ⊆
      {ω | ENNReal.ofReal (Real.exp (t / (c * θ))) ≤ f ω} := by
    intro ω hω
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    change t ≤ _ at hω
    rw [div_le_div_iff₀ (by positivity) hθ]
    calc t * θ ≤ (c * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v) * θ :=
          mul_le_mul_of_nonneg_right hω hθ.le
      _ = _ := by ring
  refine (measure_mono hsub).trans ((meas_ge_le_lintegral_div hint.1.aemeasurable.ennreal_ofReal
    (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top).trans ?_)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun _ => (Real.exp_pos _).le),
    ← ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff_of_pos_right (Real.exp_pos _)]
  exact hb

/-- The vertices of the partition cube of `u` lie in `anchorBox ω u`. -/
theorem mem_anchorBox_of_mem_partitionCube {ω : Configuration d} (hP : PartitionEvent ω)
    {u x : Vertex d} (hx : x ∈ (partitionCube ω u).vertices) : x ∈ anchorBox ω u := by
  rw [mem_anchorBox]
  intro i
  have h := Rigidity.Proofs.Regularity.abs_sub_lt_side_of_mem hx (mem_partitionCube hP u) i
  have h3 : (3 : ℤ) ^ (partitionCube ω u).scale ≤ ((3 ^ ((partitionCube ω u).scale + 1) : ℕ) : ℤ) := by
    push_cast
    exact pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)
  linarith

section Base

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- `2d` times the sum of the Lipschitz bounds over `anchorBox ω u` is at most the sum (5.10)
at `u`. -/
theorem ofReal_sum_anchorBox_le {ω : Configuration d} (hP : PartitionEvent ω)
    {Λ : Vertex d → Configuration d → ℝ} (hΛ0 : ∀ x, 0 ≤ Λ x ω) (u : Vertex d) :
    ENNReal.ofReal (2 * d * ∑ x ∈ anchorBox ω u, Λ x ω) ≤ stepSixSum Λ u ω := by
  have hsize : TriadicCube.stoppingSize (TriadicCube.goodCubes ω) u =
      (3 : ℝ) ^ (partitionCube ω u).scale :=
    TriadicCube.stoppingSize_eq_of_mem (mem_partitionCube hP u) (partitionCube_spec hP u).2
  unfold stepSixSum
  rw [hsize, Finset.mul_sum]
  calc ENNReal.ofReal (∑ x ∈ anchorBox ω u, 2 * d * Λ x ω)
      = ∑ x ∈ anchorBox ω u, ENNReal.ofReal (2 * d * Λ x ω) :=
        ENNReal.ofReal_sum_of_nonneg fun x _ => by have := hΛ0 x; positivity
    _ = ∑ x ∈ anchorBox ω u, ENNReal.ofReal (if ‖latticeEuclideanEmbedding (x - u)‖ ≤
          3 * d * (3 : ℝ) ^ (partitionCube ω u).scale then 2 * d * Λ x ω else 0) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [if_pos (norm_sub_le_of_mem_anchorBox hx)]
    _ ≤ _ := ENNReal.sum_le_tsum _

/-- **The comparison (5.7) at a configuration**: on the partition events of `ω` and `τ_{-y'} ω`,
the difference of the coarsened correctors for `𝒫_{y'}` and `𝒫` at `z` is at most twice the sum
of the sums (5.10) over the ball of radius `d size(□_{𝒫_{y'}}(z))` around `z`. -/
theorem ofReal_abs_coarseField_sub_le (hd : 0 < d) {ω : Configuration d} (hω : ω ∈ G)
    (hP : PartitionEvent ω) {y' : Vertex d}
    (hP' : PartitionEvent (configurationTranslation (-y') ω)) {i : Fin d}
    {Λ : Vertex d → Configuration d → ℝ} (hΛ0 : ∀ x, 0 ≤ Λ x ω)
    (hΛ : ∀ x, ω ∈ infiniteComponentEvent x → ∀ y, (openGraph ω).Adj x y →
      |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ x ω) (z : Vertex d) :
    ENNReal.ofReal |coarseField hG hGv i y' z ω - coarseField hG hGv i 0 z ω| ≤
      2 * ∑' u, if ‖latticeEuclideanEmbedding (u - z)‖ ≤ d * TriadicCube.stoppingSize
        (TriadicCube.goodCubes (configurationTranslation (-y') ω)) (z - y')
        then stepSixSum Λ u ω else 0 := by
  set a' := shiftedAnchor y' ω z with ha'def
  set R := TriadicCube.stoppingSize (TriadicCube.goodCubes (configurationTranslation (-y') ω)) (z - y') with hR
  set T := ∑' u, if ‖latticeEuclideanEmbedding (u - z)‖ ≤ d * R then stepSixSum Λ u ω else 0
    with hT
  have ha' : ω ∈ infiniteComponentEvent a' := infinite_shiftedAnchor hd hP' z
  have hA0 : ∀ v, shiftedAnchor 0 ω v = partitionAnchor ω v := fun v => by
    rw [shiftedAnchor_zero, guardAnchor_of_event hP]
  have hinf : ∀ v, ω ∈ infiniteComponentEvent (partitionAnchor ω v) :=
    infinite_partitionAnchor hd hP
  have hdiff : coarseField hG hGv i y' z ω - coarseField hG hGv i 0 z ω =
      correctorDiff hG hGv (Pi.single i 1) ω a' (partitionAnchor ω z) := by
    unfold coarseField
    rw [hA0 z, hA0 0]
    exact correctorDiff_sub_eq hG hGv hω ha' (hinf z) (hinf 0)
  -- the distance from `z` to `a'`
  have hRsize : R = (3 : ℝ) ^ (partitionCube (configurationTranslation (-y') ω) (z - y')).scale :=
    TriadicCube.stoppingSize_eq_of_mem (mem_partitionCube hP' _) (partitionCube_spec hP' _).2
  have ha'z : ∀ k, |a' k - z k| < (3 : ℤ) ^ (partitionCube (configurationTranslation (-y') ω) (z - y')).scale := by
    intro k
    have h := Rigidity.Proofs.Regularity.abs_sub_lt_side_of_mem
      (partitionAnchor_mem hP' (z - y')) (mem_partitionCube hP' (z - y')) k
    have ea : a' = y' + partitionAnchor (configurationTranslation (-y') ω) (z - y') := by
      rw [ha'def]
      unfold shiftedAnchor
      rw [guardAnchor_of_event hP']
    have e : a' k - z k = partitionAnchor (configurationTranslation (-y') ω) (z - y') k -
        (z - y') k := by
      rw [ea, Pi.add_apply, Pi.sub_apply]
      ring
    rw [e]
    exact h
  obtain ⟨W, hW⟩ := exists_walk_near a' _ z le_rfl
  have hnorm : ∀ u ∈ W.support, ‖latticeEuclideanEmbedding (u - z)‖ ≤ d * R := by
    intro u hu
    rw [hRsize]
    refine norm_latticeEuclideanEmbedding_le_of_abs_le (by positivity) fun k => ?_
    have h1 := (hW u hu k).trans (ha'z k).le
    rw [Pi.sub_apply]
    exact_mod_cast h1
  have hsupp : ∑ u ∈ W.support.toFinset, stepSixSum Λ u ω ≤ T := by
    calc ∑ u ∈ W.support.toFinset, stepSixSum Λ u ω
        = ∑ u ∈ W.support.toFinset,
            (if ‖latticeEuclideanEmbedding (u - z)‖ ≤ d * R then stepSixSum Λ u ω else 0) :=
          Finset.sum_congr rfl fun u hu => by rw [if_pos (hnorm u (List.mem_toFinset.1 hu))]
      _ ≤ T := ENNReal.sum_le_tsum _
  -- the coarsening error at `a'`
  have h1 : ENNReal.ofReal |correctorDiff hG hGv (Pi.single i 1) ω a' (partitionAnchor ω a')| ≤
      T := by
    have h := abs_correctorDiff_guardAnchor_le hG hGv hd hω hP ha' (Λ := fun x => Λ x ω) hΛ0 hΛ
    rw [guardAnchor_of_event hP] at h
    refine h.trans (le_trans ?_ hsupp)
    exact Finset.single_le_sum (f := fun u => stepSixSum Λ u ω) (fun _ _ => zero_le)
      (List.mem_toFinset.2 W.end_mem_support)
  -- the anchors along the walk
  set S := W.support.toFinset.biUnion (anchorBox ω) with hS
  set w : Vertex d → ℝ := fun x => if ω ∈ infiniteComponentEvent x then
    correctorDiff hG hGv (Pi.single i 1) ω x (partitionAnchor ω z) else 0 with hw
  have hreach : (openIn ω ↑S).Reachable (partitionAnchor ω z) (partitionAnchor ω a') := by
    refine Rigidity.Percolation.openIn_reachable_mono_region ?_
      (reachable_partitionAnchor_of_walk hd hP W)
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨u, hu, hxu⟩ := hx
    rw [Finset.mem_coe, hS, Finset.mem_biUnion]
    exact ⟨u, List.mem_toFinset.2 hu, mem_anchorBox_of_mem_partitionCube hP hxu⟩
  have hv := abs_sub_le_edgeVariationIn_of_reachable S w hreach
  have hwz : w (partitionAnchor ω z) = 0 := by
    simp only [hw, if_pos (hinf z)]
    obtain ⟨h, -⟩ := hGv hω
    exact correctorDiff_self hG hGv hω (uniqueInfiniteComponent_infinite h)
      ⟨partitionAnchor ω z, (mem_uniqueInfiniteComponent_iff h _).2 (hinf z)⟩
  have hwa : w (partitionAnchor ω a') =
      correctorDiff hG hGv (Pi.single i 1) ω (partitionAnchor ω a') (partitionAnchor ω z) := by
    simp only [hw, if_pos (hinf a')]
  rw [hwz, hwa, zero_sub, abs_neg] at hv
  have hev := edgeVariationIn_correctorDiff_le hG hGv hω (hinf z) S (Λ := fun x => Λ x ω) hΛ0 hΛ
  have hbu := sum_biUnion_le_of_nonneg W.support.toFinset (anchorBox ω) (f := fun x => Λ x ω) hΛ0
  have h2 : ENNReal.ofReal
      |correctorDiff hG hGv (Pi.single i 1) ω (partitionAnchor ω a') (partitionAnchor ω z)| ≤ T := by
    refine le_trans ?_ hsupp
    calc ENNReal.ofReal
          |correctorDiff hG hGv (Pi.single i 1) ω (partitionAnchor ω a') (partitionAnchor ω z)|
        ≤ ENNReal.ofReal (∑ u ∈ W.support.toFinset, 2 * d * ∑ x ∈ anchorBox ω u, Λ x ω) := by
          refine ENNReal.ofReal_le_ofReal (hv.trans (hev.trans ?_))
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left hbu (by positivity)
      _ = ∑ u ∈ W.support.toFinset, ENNReal.ofReal (2 * d * ∑ x ∈ anchorBox ω u, Λ x ω) :=
          ENNReal.ofReal_sum_of_nonneg fun u _ => by
            have := Finset.sum_nonneg fun x (_ : x ∈ anchorBox ω u) => hΛ0 x
            positivity
      _ ≤ ∑ u ∈ W.support.toFinset, stepSixSum Λ u ω :=
          Finset.sum_le_sum fun u _ => ofReal_sum_anchorBox_le hP hΛ0 u
  -- assembling
  rw [hdiff, correctorDiff_add' hG hGv hω ha' (hinf a') (hinf z)]
  calc ENNReal.ofReal |correctorDiff hG hGv (Pi.single i 1) ω a' (partitionAnchor ω a') +
        correctorDiff hG hGv (Pi.single i 1) ω (partitionAnchor ω a') (partitionAnchor ω z)|
      ≤ ENNReal.ofReal
          (|correctorDiff hG hGv (Pi.single i 1) ω a' (partitionAnchor ω a')| +
            |correctorDiff hG hGv (Pi.single i 1) ω (partitionAnchor ω a')
              (partitionAnchor ω z)|) := ENNReal.ofReal_le_ofReal (abs_add_le _ _)
    _ = ENNReal.ofReal |correctorDiff hG hGv (Pi.single i 1) ω a' (partitionAnchor ω a')| +
          ENNReal.ofReal |correctorDiff hG hGv (Pi.single i 1) ω (partitionAnchor ω a')
            (partitionAnchor ω z)| := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ T + T := add_le_add h1 h2
    _ = 2 * T := (two_mul T).symm

end Base

end Rigidity.Corrector.GeneralDim
