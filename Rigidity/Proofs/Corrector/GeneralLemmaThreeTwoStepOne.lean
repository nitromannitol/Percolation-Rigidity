import Rigidity.Proofs.Corrector.GeneralStationaryCoarsening
import Rigidity.Proofs.Corrector.GeneralPartitionComparison

/-!
# Dario, Lemma 3.2, Step 1, in every dimension

Step 1 of the proof of Lemma 3.2 compares the coarsened corrector of the partition `𝒫` into good
cubes of `ℤᵈ` with that of the stationary partition `𝒫_stat^k`, through the discrepancy of the
anchors `statDiscrepancy i k z = χ_{e_i}(z̄_stat(z)) - χ_{e_i}(z̄(z))`.

* `ofReal_abs_correctorDiff_partitionAnchor_le`: for a point `a` of the infinite cluster within
  `R` of `z` in every coordinate, `|χ(a) - χ(z̄(z))|` is at most twice the sum of the sums of
  (5.10) over the ball of radius `d R` around `z`;
* `abs_statAnchor_sub_le`: `z̄_stat(z)` is within `3^k + Σ_{|v - z|_∞ ≤ 3^k} size(□_𝒫(v))` of `z`
  in every coordinate (`statSizeSum`);
* `statDiscrepancy_eq_zero`: the discrepancy vanishes where the two partition cubes agree;
* `measure_le_statSizeSum_le`, `measure_le_statRadius_le`: the tails of `statSizeSum` and of the
  radius `d (3^k + statSizeSum)` of the crude bound;
* `exists_lintegral_sq_statDiscrepancy_le`: `E[|χ(z̄_stat(z)) - χ(z̄(z))|²] ≤ K₁ (1 + θ₀ 3^{kd})^{2d}`;
* `exists_lintegral_abs_statDiscrepancy_le`: **Step 1 at one vertex**,
  `E|χ(z̄_stat(z)) - χ(z̄(z))| ≤ K (1 + θ₀ 3^{kd})^{2d} e^{-c 3^k/2}`, since the discrepancy vanishes
  outside the event of (3.3) for the cube of scale `k` containing `z`.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter Set LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical ENNReal

variable {d : ℕ}

/-- The sum of the sizes of the cubes of the partition at the vertices of `z + [-3^k, 3^k]ᵈ`. -/
noncomputable def statSizeSum (k : ℕ) (z : Vertex d) (ω : Configuration d) : ℝ :=
  ∑ v ∈ LatticeProb.boxFinset z (3 ^ k), TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v

theorem statSizeSum_nonneg (k : ℕ) (z : Vertex d) (ω : Configuration d) :
    0 ≤ statSizeSum k z ω :=
  Finset.sum_nonneg fun v _ => TriadicCube.stoppingSize_nonneg _ v

theorem measurable_statSizeSum (k : ℕ) (z : Vertex d) : Measurable (statSizeSum k z) :=
  Finset.measurable_sum _ fun v _ => measurable_stoppingSize_goodCubes v

theorem mem_boxFinset {z v : Vertex d} {R : ℕ} :
    v ∈ LatticeProb.boxFinset z R ↔ ∀ i, |v i - z i| ≤ (R : ℤ) := by
  simp only [LatticeProb.boxFinset, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]
  exact forall_congr' fun i => by constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The anchor of the partition at `v` is within `size(□_𝒫(v))` of `v` in every coordinate. -/
theorem abs_partitionAnchor_sub_le {ω : Configuration d} (hP : PartitionEvent ω) (v : Vertex d)
    (j : Fin d) :
    |((partitionAnchor ω v j - v j : ℤ) : ℝ)| ≤ TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v := by
  rw [TriadicCube.stoppingSize_eq_of_mem (mem_partitionCube hP v) (partitionCube_spec hP v).2]
  have h := Rigidity.Proofs.Regularity.abs_sub_lt_side_of_mem (partitionAnchor_mem hP v)
    (mem_partitionCube hP v) j
  have h' : |((partitionAnchor ω v j - v j : ℤ) : ℝ)| < (((3 : ℤ) ^ (partitionCube ω v).scale : ℤ) : ℝ) := by
    rw [← Int.cast_abs]
    exact_mod_cast h
  push_cast at h' ⊢
  exact h'.le

/-- **Dario, Lemma 3.2, Step 1, the anchors of `𝒫_stat^k`**: `z̄_stat(z)` is within
`3^k + statSizeSum k z` of `z` in every coordinate. -/
theorem abs_statAnchor_sub_le (hd : 0 < d) {ω : Configuration d} (hP : PartitionEvent ω) (k : ℕ)
    (z : Vertex d) (j : Fin d) :
    |((statAnchor k ω z - z) j : ℝ)| ≤ (3 : ℝ) ^ k + statSizeSum k z ω := by
  set Q := TriadicCube.cappedCube (TriadicCube.goodCubes ω) k z with hQ
  have hzQ : z ∈ Q.vertices := (TriadicCube.cappedCube_spec _ k z).1
  have hscale : Q.scale ≤ k := TriadicCube.scale_cappedCube_le _ k z
  have hrad : 2 * Q.radius + 1 = (3 : ℤ) ^ Q.scale := by
    have := Q.side_eq_two_mul_radius_add_one
    rw [← this]
    rfl
  have hpow : (3 : ℤ) ^ Q.scale ≤ (3 : ℤ) ^ k := pow_le_pow_right₀ (by norm_num) hscale
  have hzc : ∀ i, |z i - Q.center i| ≤ Q.radius := (Q.mem_vertices_iff z).1 hzQ
  have hS0 := statSizeSum_nonneg k z ω
  have h3pos : (0 : ℤ) < (3 : ℤ) ^ k := by positivity
  have hr3 : Q.radius ≤ (3 : ℤ) ^ k := by linarith
  have hzc3 : ∀ i, |z i - Q.center i| ≤ (3 : ℤ) ^ k := fun i => (hzc i).trans hr3
  have hcbox : Q.center ∈ LatticeProb.boxFinset z (3 ^ k) := by
    rw [mem_boxFinset]
    intro i
    rw [abs_sub_comm]
    push_cast
    exact hzc3 i
  have hsize : TriadicCube.stoppingSize (TriadicCube.goodCubes ω) Q.center ≤ statSizeSum k z ω :=
    Finset.single_le_sum (f := fun v => TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v)
      (fun v _ => TriadicCube.stoppingSize_nonneg _ v) hcbox
  have h3k : ((3 : ℤ) ^ k : ℝ) = (3 : ℝ) ^ k := by push_cast; ring
  rw [Pi.sub_apply]
  unfold statAnchor statAnchorOf
  rw [← hQ]
  split_ifs with h
  · have ha : Q.anchor ω ∈ Q.vertices :=
      TriadicCube.crossingCluster_subset _ _ (TriadicCube.anchor_mem_crossingCluster h.1.2.1)
    have h1 := Rigidity.Proofs.Regularity.abs_sub_lt_side_of_mem ha hzQ j
    have h2 : |((Q.anchor ω j - z j : ℤ) : ℝ)| ≤ (3 : ℝ) ^ k := by
      rw [← h3k, ← Int.cast_abs]
      exact_mod_cast h1.le.trans hpow
    linarith
  · have hinf := infinite_partitionAnchor hd hP Q.center
    have hnear := Q.isNearestInf_nearestInf hinf
    have hle := hnear.2 _ hinf
    have hfst : (ofLex (Q.anchorKey (Q.nearestInf ω))).1 ≤
        (ofLex (Q.anchorKey (partitionAnchor ω Q.center))).1 := by
      change toLex _ ≤ toLex _ at hle
      rw [Prod.Lex.toLex_le_toLex] at hle
      rcases hle with h' | ⟨h', -⟩
      · exact h'.le
      · exact h'.le
    rw [TriadicCube.anchorKey_fst, TriadicCube.anchorKey_fst] at hfst
    have hj : (Q.nearestInf ω j - Q.center j).natAbs ≤
        Finset.univ.sup fun i => (Q.nearestInf ω i - Q.center i).natAbs :=
      Finset.le_sup (f := fun i => (Q.nearestInf ω i - Q.center i).natAbs) (Finset.mem_univ j)
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_sup Finset.univ
      (Finset.univ_nonempty_iff.2 ⟨j⟩)
      (fun i => (partitionAnchor ω Q.center i - Q.center i).natAbs)
    rw [hi₀] at hfst
    have hA := abs_partitionAnchor_sub_le hP Q.center i₀
    have hnat : (((Q.nearestInf ω j - Q.center j).natAbs : ℕ) : ℝ) ≤
        (((partitionAnchor ω Q.center i₀ - Q.center i₀).natAbs : ℕ) : ℝ) := by
      exact_mod_cast hj.trans hfst
    rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs] at hnat
    have hzc' : |((z j - Q.center j : ℤ) : ℝ)| ≤ (3 : ℝ) ^ k := by
      rw [← h3k, ← Int.cast_abs]
      exact_mod_cast hzc3 j
    set A : ℝ := ((Q.nearestInf ω j - Q.center j : ℤ) : ℝ)
    set B : ℝ := ((z j - Q.center j : ℤ) : ℝ)
    have e : ((Q.nearestInf ω j - z j : ℤ) : ℝ) = A - B := by
      simp only [A, B]
      push_cast
      ring
    have tri : |A - B| ≤ |A| + |B| :=
      abs_le.2 ⟨by linarith [neg_abs_le A, le_abs_self B], by linarith [le_abs_self A, neg_abs_le B]⟩
    rw [e]
    have hAs : |A| ≤ TriadicCube.stoppingSize (TriadicCube.goodCubes ω) Q.center :=
      hnat.trans hA
    linarith

section Carrier

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- **The comparison with the anchor of the partition**: for `a` in the infinite cluster within
`R` of `z` in every coordinate, `|χ(a) - χ(z̄(z))|` is at most twice the sum of the sums of
(5.10) over the ball of radius `d R` around `z`. -/
theorem ofReal_abs_correctorDiff_partitionAnchor_le (hd : 0 < d) {ω : Configuration d}
    (hω : ω ∈ G) (hP : PartitionEvent ω) {i : Fin d} {a z : Vertex d}
    (ha : ω ∈ infiniteComponentEvent a) {R : ℝ} (haz : ∀ k, |((a - z) k : ℝ)| ≤ R)
    {Λ : Vertex d → Configuration d → ℝ} (hΛ0 : ∀ x, 0 ≤ Λ x ω)
    (hΛ : ∀ x, ω ∈ infiniteComponentEvent x → ∀ y, (openGraph ω).Adj x y →
      |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ x ω) :
    ENNReal.ofReal |correctorDiff hG hGv (Pi.single i 1) ω a (partitionAnchor ω z)| ≤
      2 * ∑' u, if ‖latticeEuclideanEmbedding (u - z)‖ ≤ d * R then stepSixSum Λ u ω else 0 := by
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (haz ⟨0, hd⟩)
  set T := ∑' u, if ‖latticeEuclideanEmbedding (u - z)‖ ≤ d * R then stepSixSum Λ u ω else 0
    with hT
  have hinf : ∀ v, ω ∈ infiniteComponentEvent (partitionAnchor ω v) :=
    infinite_partitionAnchor hd hP
  obtain ⟨W, hW⟩ := exists_walk_near a _ z le_rfl
  have hnorm : ∀ u ∈ W.support, ‖latticeEuclideanEmbedding (u - z)‖ ≤ d * R := by
    intro u hu
    refine norm_latticeEuclideanEmbedding_le_of_abs_le hR0 fun k => ?_
    have h1 : |((u k - z k : ℤ) : ℝ)| ≤ |((a k - z k : ℤ) : ℝ)| := by
      rw [← Int.cast_abs, ← Int.cast_abs]
      exact_mod_cast hW u hu k
    have h2 := haz k
    rw [Pi.sub_apply] at h2 ⊢
    exact h1.trans h2
  have hsupp : ∑ u ∈ W.support.toFinset, stepSixSum Λ u ω ≤ T := by
    calc ∑ u ∈ W.support.toFinset, stepSixSum Λ u ω
        = ∑ u ∈ W.support.toFinset,
            (if ‖latticeEuclideanEmbedding (u - z)‖ ≤ d * R then stepSixSum Λ u ω else 0) :=
          Finset.sum_congr rfl fun u hu => by rw [if_pos (hnorm u (List.mem_toFinset.1 hu))]
      _ ≤ T := ENNReal.sum_le_tsum _
  have h1 : ENNReal.ofReal |correctorDiff hG hGv (Pi.single i 1) ω a (partitionAnchor ω a)| ≤
      T := by
    have h := abs_correctorDiff_guardAnchor_le hG hGv hd hω hP ha (Λ := fun x => Λ x ω) hΛ0 hΛ
    rw [guardAnchor_of_event hP] at h
    refine h.trans (le_trans ?_ hsupp)
    exact Finset.single_le_sum (f := fun u => stepSixSum Λ u ω) (fun _ _ => zero_le)
      (List.mem_toFinset.2 W.end_mem_support)
  set S := W.support.toFinset.biUnion (anchorBox ω) with hS
  set w : Vertex d → ℝ := fun x => if ω ∈ infiniteComponentEvent x then
    correctorDiff hG hGv (Pi.single i 1) ω x (partitionAnchor ω z) else 0 with hw
  have hreach : (openIn ω ↑S).Reachable (partitionAnchor ω z) (partitionAnchor ω a) := by
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
  have hwa : w (partitionAnchor ω a) =
      correctorDiff hG hGv (Pi.single i 1) ω (partitionAnchor ω a) (partitionAnchor ω z) := by
    simp only [hw, if_pos (hinf a)]
  rw [hwz, hwa, zero_sub, abs_neg] at hv
  have hev := edgeVariationIn_correctorDiff_le hG hGv hω (hinf z) S (Λ := fun x => Λ x ω) hΛ0 hΛ
  have hbu := sum_biUnion_le_of_nonneg W.support.toFinset (anchorBox ω) (f := fun x => Λ x ω) hΛ0
  have h2 : ENNReal.ofReal
      |correctorDiff hG hGv (Pi.single i 1) ω (partitionAnchor ω a) (partitionAnchor ω z)| ≤
        T := by
    refine le_trans ?_ hsupp
    calc ENNReal.ofReal
          |correctorDiff hG hGv (Pi.single i 1) ω (partitionAnchor ω a) (partitionAnchor ω z)|
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
  rw [correctorDiff_add' hG hGv hω ha (hinf a) (hinf z)]
  calc ENNReal.ofReal |correctorDiff hG hGv (Pi.single i 1) ω a (partitionAnchor ω a) +
        correctorDiff hG hGv (Pi.single i 1) ω (partitionAnchor ω a) (partitionAnchor ω z)|
      ≤ ENNReal.ofReal
          (|correctorDiff hG hGv (Pi.single i 1) ω a (partitionAnchor ω a)| +
            |correctorDiff hG hGv (Pi.single i 1) ω (partitionAnchor ω a)
              (partitionAnchor ω z)|) := ENNReal.ofReal_le_ofReal (abs_add_le _ _)
    _ = ENNReal.ofReal |correctorDiff hG hGv (Pi.single i 1) ω a (partitionAnchor ω a)| +
          ENNReal.ofReal |correctorDiff hG hGv (Pi.single i 1) ω (partitionAnchor ω a)
            (partitionAnchor ω z)| := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ T + T := add_le_add h1 h2
    _ = 2 * T := (two_mul T).symm

/-- The discrepancy `χ_{e_i}(z̄_stat(z)) - χ_{e_i}(z̄(z))` of the two coarsenings at `z`. -/
noncomputable def statDiscrepancy (i : Fin d) (k : ℕ) (z : Vertex d) (ω : Configuration d) : ℝ :=
  correctorDiff hG hGv (Pi.single i 1) ω (statAnchor k ω z) (guardAnchor ω z)

theorem measurable_statDiscrepancy (i : Fin d) (k : ℕ) (z : Vertex d) :
    Measurable (statDiscrepancy hG hGv i k z) :=
  measurable_correctorDiff_comp hG hGv _ (measurable_statAnchor k z) (measurable_guardAnchor z)

/-- The discrepancy vanishes where the cube of `𝒫_stat^k` is the cube of the partition. -/
theorem statDiscrepancy_eq_zero (hd : 0 < d) {ω : Configuration d} (hω : ω ∈ G)
    (hP : PartitionEvent ω) {i : Fin d} {k : ℕ} {z : Vertex d}
    (h : TriadicCube.cappedCube (TriadicCube.goodCubes ω) k z = partitionCube ω z) :
    statDiscrepancy hG hGv i k z ω = 0 := by
  unfold statDiscrepancy
  rw [statAnchor_eq_partitionAnchor hd hP h, guardAnchor_of_event hP]
  have hb := infinite_partitionAnchor hd hP z
  have := correctorDiff_sub_eq hG hGv (q := Pi.single i 1) hω hb hb hb
  linarith

/-- **The crude bound of the discrepancy**: at most twice the sum of the sums of (5.10) over the
ball of radius `d (3^k + statSizeSum k z)` around `z`. -/
theorem ofReal_abs_statDiscrepancy_le (hd : 0 < d) {ω : Configuration d} (hω : ω ∈ G)
    (hP : PartitionEvent ω) {i : Fin d} (k : ℕ) (z : Vertex d)
    {Λ : Vertex d → Configuration d → ℝ} (hΛ0 : ∀ x, 0 ≤ Λ x ω)
    (hΛ : ∀ x, ω ∈ infiniteComponentEvent x → ∀ y, (openGraph ω).Adj x y →
      |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ x ω) :
    ENNReal.ofReal |statDiscrepancy hG hGv i k z ω| ≤
      2 * ∑' u, if ‖latticeEuclideanEmbedding (u - z)‖ ≤ d * ((3 : ℝ) ^ k + statSizeSum k z ω)
        then stepSixSum Λ u ω else 0 := by
  unfold statDiscrepancy
  rw [guardAnchor_of_event hP]
  exact ofReal_abs_correctorDiff_partitionAnchor_le hG hGv hd hω hP
    (statAnchor_mem_inf k z (infinite_partitionAnchor hd hP z))
    (abs_statAnchor_sub_le hd hP k z) hΛ0 hΛ

end Carrier

/-- **The tail of the sum of the sizes**: `P[t ≤ statSizeSum k z] ≤ 2 e^{-t/(Nθ)}` with
`N = (2·3^k + 1)^d`. -/
theorem measure_le_statSizeSum_le {p : unitInterval} {θ : ℝ} (hθ : 0 < θ)
    (hexp : ∀ v : Vertex d,
      Integrable (fun ω => Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v / θ))
        (latticeBondLaw d p) ∧
      ∫ ω, Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v / θ)
        ∂latticeBondLaw d p ≤ 2)
    (k : ℕ) (z : Vertex d) (t : ℝ) :
    latticeBondLaw d p {ω | t ≤ statSizeSum k z ω} ≤
      ENNReal.ofReal (2 * Real.exp (-(t / (((2 * 3 ^ k + 1) ^ d : ℕ) * θ)))) := by
  set F := LatticeProb.boxFinset z (3 ^ k) with hF
  set N : ℕ := (2 * 3 ^ k + 1) ^ d with hN
  have hcard : F.card = N := LatticeProb.Percolation.card_boxFinset z (3 ^ k)
  have hN0 : (0 : ℝ) < N := by positivity
  set f : Configuration d → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (Real.exp (statSizeSum k z ω / (N * θ)))
  have hjensen : ∀ ω, Real.exp (statSizeSum k z ω / (N * θ)) ≤
      ∑ v ∈ F, (1 / (N : ℝ)) *
        Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v / θ) := by
    intro ω
    have h := (convexOn_exp).map_sum_le (t := F) (w := fun _ => 1 / (N : ℝ))
      (p := fun v => TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v / θ)
      (fun v _ => by positivity)
      (by rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_one_div_cancel hN0.ne'])
      (fun v _ => Set.mem_univ _)
    simp only [smul_eq_mul] at h
    refine (congrArg Real.exp ?_).trans_le h
    rw [statSizeSum, ← hF, Finset.sum_div]
    refine Finset.sum_congr rfl fun v _ => ?_
    field_simp
  have hf : ∫⁻ ω, f ω ∂latticeBondLaw d p ≤ 2 := by
    calc ∫⁻ ω, f ω ∂latticeBondLaw d p
        ≤ ∫⁻ ω, ∑ v ∈ F, ENNReal.ofReal (1 / (N : ℝ)) *
            ENNReal.ofReal (Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v / θ))
            ∂latticeBondLaw d p := by
          refine lintegral_mono fun ω => ?_
          calc f ω ≤ ENNReal.ofReal (∑ v ∈ F, (1 / (N : ℝ)) *
                Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v / θ)) :=
                ENNReal.ofReal_le_ofReal (hjensen ω)
            _ = ∑ v ∈ F, ENNReal.ofReal ((1 / (N : ℝ)) *
                Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v / θ)) :=
                ENNReal.ofReal_sum_of_nonneg fun v _ => by positivity
            _ = _ := Finset.sum_congr rfl fun v _ => ENNReal.ofReal_mul (by positivity)
      _ = ∑ v ∈ F, ENNReal.ofReal (1 / (N : ℝ)) * ∫⁻ ω,
            ENNReal.ofReal (Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v / θ))
            ∂latticeBondLaw d p := by
          rw [lintegral_finsetSum' _ fun v _ =>
            ((hexp v).1.aemeasurable.ennreal_ofReal).const_mul _]
          exact Finset.sum_congr rfl fun v _ => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ∑ _v ∈ F, ENNReal.ofReal (1 / (N : ℝ)) * 2 := by
          refine Finset.sum_le_sum fun v _ => mul_le_mul_right ?_ _
          rw [← ofReal_integral_eq_lintegral_ofReal (hexp v).1
            (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
          exact (ENNReal.ofReal_le_ofReal (hexp v).2).trans_eq (ENNReal.ofReal_ofNat 2)
      _ = 2 := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity), mul_one_div_cancel hN0.ne', ENNReal.ofReal_one,
            one_mul]
  have hsub : {ω | t ≤ statSizeSum k z ω} ⊆
      {ω | ENNReal.ofReal (Real.exp (t / (N * θ))) ≤ f ω} := by
    intro ω hω
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    exact div_le_div_of_nonneg_right hω (by positivity)
  have hfm : Measurable f :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((measurable_statSizeSum k z).div_const _))
  refine (measure_mono hsub).trans ((meas_ge_le_lintegral_div hfm.aemeasurable
    (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top).trans ?_)
  calc (∫⁻ ω, f ω ∂latticeBondLaw d p) / ENNReal.ofReal (Real.exp (t / (N * θ)))
      ≤ 2 / ENNReal.ofReal (Real.exp (t / (N * θ))) := ENNReal.div_le_div_right hf _
    _ = ENNReal.ofReal (2 * Real.exp (-(t / (N * θ)))) := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_div_of_pos (Real.exp_pos _), Real.exp_neg,
          div_eq_mul_inv]

/-- The scale `θ_k = d (2 N θ + 4·3^k)` of the tail of the radius of the crude bound. -/
noncomputable def statTailScale (d : ℕ) (θ : ℝ) (k : ℕ) : ℝ :=
  d * (2 * (((2 * 3 ^ k + 1) ^ d : ℕ) : ℝ) * θ + 4 * 3 ^ k)

theorem statTailScale_pos (hd : 0 < d) {θ : ℝ} (hθ : 0 < θ) (k : ℕ) :
    0 < statTailScale d θ k := by
  have : (0 : ℝ) < d := by exact_mod_cast hd
  unfold statTailScale
  positivity

theorem statTailScale_le (hd : 0 < d) {θ : ℝ} (hθ : 0 < θ) (k : ℕ) :
    statTailScale d θ k ≤ d * (2 * 3 ^ d * θ + 4) * ((3 : ℝ) ^ k) ^ d := by
  unfold statTailScale
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hN : ((((2 * 3 ^ k + 1) ^ d : ℕ)) : ℝ) ≤ 3 ^ d * ((3 : ℝ) ^ k) ^ d := by
    push_cast
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) d
  have hk : (3 : ℝ) ^ k ≤ ((3 : ℝ) ^ k) ^ d := le_self_pow₀ h1 (by omega)
  have : 2 * (((2 * 3 ^ k + 1) ^ d : ℕ) : ℝ) * θ + 4 * 3 ^ k ≤
      (2 * 3 ^ d * θ + 4) * ((3 : ℝ) ^ k) ^ d := by nlinarith
  calc (d : ℝ) * (2 * (((2 * 3 ^ k + 1) ^ d : ℕ) : ℝ) * θ + 4 * 3 ^ k)
      ≤ d * ((2 * 3 ^ d * θ + 4) * ((3 : ℝ) ^ k) ^ d) := mul_le_mul_of_nonneg_left this hd0.le
    _ = d * (2 * 3 ^ d * θ + 4) * ((3 : ℝ) ^ k) ^ d := by ring

/-- **The tail of the radius of the crude bound**:
`P[t ≤ d (3^k + statSizeSum k z)] ≤ 2 e^{-t/θ_k}`. -/
theorem measure_le_statRadius_le (hd : 0 < d) {p : unitInterval} {θ : ℝ} (hθ : 0 < θ)
    (hexp : ∀ v : Vertex d,
      Integrable (fun ω => Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v / θ))
        (latticeBondLaw d p) ∧
      ∫ ω, Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v / θ)
        ∂latticeBondLaw d p ≤ 2)
    (k : ℕ) (z : Vertex d) (t : ℝ) (ht : 0 ≤ t) :
    latticeBondLaw d p {ω | t ≤ d * ((3 : ℝ) ^ k + statSizeSum k z ω)} ≤
      ENNReal.ofReal (2 * Real.exp (-(t / statTailScale d θ k))) := by
  set θk := statTailScale d θ k with hθk
  have hθk0 : 0 < θk := statTailScale_pos hd hθ k
  set N : ℝ := (((2 * 3 ^ k + 1) ^ d : ℕ) : ℝ) with hN
  have hN0 : 0 < N := by positivity
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h3 : (0 : ℝ) < 3 ^ k := by positivity
  by_cases hsmall : t ≤ 2 * d * 3 ^ k
  · refine prob_le_one.trans ?_
    have hle : t / θk ≤ 1 / 2 := by
      rw [div_le_iff₀ hθk0, hθk, statTailScale]
      have : 0 ≤ d * (2 * N * θ) := by positivity
      nlinarith
    have he := Real.add_one_le_exp (-(t / θk))
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · push Not at hsmall
    have hsub : {ω | t ≤ d * ((3 : ℝ) ^ k + statSizeSum k z ω)} ⊆
        {ω | t / (2 * d) ≤ statSizeSum k z ω} := by
      intro ω hω
      change t ≤ _ at hω
      change t / (2 * d) ≤ _
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    refine (measure_mono hsub).trans ((measure_le_statSizeSum_le hθ hexp k z (t / (2 * d))).trans ?_)
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num))
    rw [neg_le_neg_iff, div_div, div_le_div_iff₀ hθk0 (by positivity)]
    have : 2 * d * (N * θ) ≤ θk := by
      rw [hθk, statTailScale]
      nlinarith
    nlinarith

/-- `|e| ≤ η e² + η⁻¹ 1_{e ≠ 0}`. -/
theorem abs_le_mul_sq_add_inv' {e η : ℝ} (hη : 0 < η) :
    |e| ≤ η * |e| ^ 2 + η⁻¹ * (if e = 0 then 0 else 1) := by
  by_cases he : e = 0
  · rw [he, abs_zero, if_pos rfl]
    simp
  · rw [if_neg he, mul_one]
    by_cases h : |e| ≤ η⁻¹
    · have : 0 ≤ η * |e| ^ 2 := by positivity
      linarith
    · push Not at h
      have h1 : 1 ≤ η * |e| := by
        have := mul_lt_mul_of_pos_left h hη
        rw [mul_inv_cancel₀ hη.ne'] at this
        exact this.le
      have : 0 ≤ η⁻¹ := (inv_pos.2 hη).le
      nlinarith [abs_nonneg e]

section Carrier

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- **The second moment of the discrepancy**: there are `K₁, θ₀ > 0` with
`E[|χ(z̄_stat(z)) - χ(z̄(z))|²] ≤ K₁ (1 + θ₀ 3^{kd})^{2d}` for every `k`, `z` and `i`. -/
theorem exists_lintegral_sq_statDiscrepancy_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) :
    ∃ K₁ θ₀ : ℝ, 0 < K₁ ∧ 0 < θ₀ ∧ ∀ (i : Fin d) (k : ℕ) (z : Vertex d),
      ∫⁻ ω, ENNReal.ofReal |statDiscrepancy hG hGv i k z ω| ^ (2 : ℝ) ∂latticeBondLaw d p ≤
        ENNReal.ofReal (K₁ * (1 + θ₀ * ((3 : ℝ) ^ k) ^ d) ^ (2 * d)) := by
  obtain ⟨Λ, A, κ, hA0, -, hΛm, hΛ0, hlip, hmom6⟩ := stepSix_data hG hGv hd hpc hp1 hGae
  obtain ⟨θ, hθ, hexp⟩ := (partition_estimates hd hpc).2.1
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  set M : ℝ := (A * 4 ^ κ) ^ 2 with hM
  have hM0 : 0 ≤ M := by positivity
  set θ₀ : ℝ := d * (2 * 3 ^ d * θ + 4) with hθ₀
  set K₁ : ℝ := 4 * (Real.sqrt 2 * M * (16 * d) ^ (2 * d)) with hK₁
  refine ⟨K₁ + 1, θ₀, by positivity, by positivity, fun i k z => ?_⟩
  set θk := statTailScale d θ k with hθk
  have hθk0 : 0 < θk := statTailScale_pos hd0 hθ k
  have hθkle : θk ≤ θ₀ * ((3 : ℝ) ^ k) ^ d := statTailScale_le hd0 hθ k
  set ε : Configuration d → ℝ := statDiscrepancy hG hGv i k z with hε
  set T : Configuration d → ℝ≥0∞ := fun ω => ∑' u, if ‖latticeEuclideanEmbedding (u - z)‖ ≤
    d * ((3 : ℝ) ^ k + statSizeSum k z ω) then stepSixSum (Λ i) u ω else 0 with hT
  have hall : ∀ᵐ ω ∂latticeBondLaw d p, ∀ x, ω ∈ infiniteComponentEvent x → ∀ y,
      (openGraph ω).Adj x y → |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ i x ω :=
    ae_all_iff.2 fun x => hlip i x
  have hpt : ∀ᵐ ω ∂latticeBondLaw d p, ENNReal.ofReal |ε ω| ≤ 2 * T ω := by
    filter_upwards [hGae, ae_partitionEvent hd hpc, hall] with ω hω hP hl
    exact ofReal_abs_statDiscrepancy_le hG hGv hd0 hω hP k z (fun x => hΛ0 i x ω) hl
  have hYm : ∀ u, ∫⁻ ω, stepSixSum (Λ i) u ω ^ (2 * (2 : ℝ)) ∂latticeBondLaw d p ≤
      ENNReal.ofReal (M ^ 2) := by
    intro u
    have h := hmom6 i u (2 * 2) (by norm_num)
    have e : (A * (2 * 2 : ℝ) ^ κ) ^ (2 * 2 : ℝ) = M ^ 2 := by
      rw [hM, show (2 * 2 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Nat.cast_ofNat]
      ring
    rw [e] at h
    exact h
  have hρm : Measurable fun ω => (d : ℝ) * ((3 : ℝ) ^ k + statSizeSum k z ω) :=
    ((measurable_statSizeSum k z).const_add _).const_mul _
  have hball := lintegral_randomBallSum_le (p := p) z hθk0
    (fun t ht => measure_le_statRadius_le hd0 hθ hexp k z t ht) hρm
    (fun u => measurable_stepSixSum (hΛm i) u) (by norm_num : (1 : ℝ) ≤ 2) hM0 hYm
  have hT2 : ∫⁻ ω, T ω ^ (2 : ℝ) ∂latticeBondLaw d p ≤
      ENNReal.ofReal (Real.sqrt 2 * M * (16 * d) ^ (2 * d) * (1 + θk) ^ (2 * d)) := by
    refine hball.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    have h1 : 2 * (1 + d * (4 * 2 * θk)) ≤ 16 * d * (1 + θk) := by nlinarith
    have h2 : 2 * (1 + d * (4 * θk)) ≤ 16 * d * (1 + θk) := by nlinarith
    have hs : 0 ≤ Real.sqrt 2 * M := by positivity
    calc (2 * (1 + d * (4 * 2 * θk))) ^ d * (Real.sqrt 2 * (2 * (1 + d * (4 * θk))) ^ d * M)
        = (2 * (1 + d * (4 * 2 * θk))) ^ d * (2 * (1 + d * (4 * θk))) ^ d *
            (Real.sqrt 2 * M) := by ring
      _ ≤ (16 * d * (1 + θk)) ^ d * (16 * d * (1 + θk)) ^ d * (Real.sqrt 2 * M) := by
          gcongr
      _ = Real.sqrt 2 * M * (16 * d) ^ (2 * d) * (1 + θk) ^ (2 * d) := by
          rw [← pow_add, ← two_mul, mul_pow]
          ring
  calc ∫⁻ ω, ENNReal.ofReal |ε ω| ^ (2 : ℝ) ∂latticeBondLaw d p
      ≤ ∫⁻ ω, 4 * T ω ^ (2 : ℝ) ∂latticeBondLaw d p := by
        refine lintegral_mono_ae ?_
        filter_upwards [hpt] with ω hω
        calc ENNReal.ofReal |ε ω| ^ (2 : ℝ) ≤ (2 * T ω) ^ (2 : ℝ) :=
              ENNReal.rpow_le_rpow hω (by norm_num)
          _ = 4 * T ω ^ (2 : ℝ) := by
              rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
              congr 1
              rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
              norm_num
    _ = 4 * ∫⁻ ω, T ω ^ (2 : ℝ) ∂latticeBondLaw d p :=
        lintegral_const_mul' _ _ (by norm_num)
    _ ≤ 4 * ENNReal.ofReal (Real.sqrt 2 * M * (16 * d) ^ (2 * d) * (1 + θk) ^ (2 * d)) :=
        mul_le_mul_right hT2 _
    _ ≤ ENNReal.ofReal ((K₁ + 1) * (1 + θ₀ * ((3 : ℝ) ^ k) ^ d) ^ (2 * d)) := by
        rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h4 : (1 + θk) ^ (2 * d) ≤ (1 + θ₀ * ((3 : ℝ) ^ k) ^ d) ^ (2 * d) :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
        have h1 : (1 : ℝ) ≤ (1 + θ₀ * ((3 : ℝ) ^ k) ^ d) ^ (2 * d) :=
          one_le_pow₀ (by have : 0 ≤ θ₀ * ((3 : ℝ) ^ k) ^ d := by positivity
                          linarith)
        have h0 : 0 ≤ Real.sqrt 2 * M * (16 * d) ^ (2 * d) := by positivity
        rw [hK₁]
        nlinarith

/-- **Dario, Lemma 3.2, Step 1, at one vertex**: there are `K, c, θ₀ > 0` with
`E|χ(z̄_stat(z)) - χ(z̄(z))| ≤ K (1 + θ₀ 3^{kd})^{2d} e^{-c 3^k / 2}` for every `k`, `z` and `i`. -/
theorem exists_lintegral_abs_statDiscrepancy_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) :
    ∃ K c θ₀ : ℝ, 0 < K ∧ 0 < c ∧ 0 < θ₀ ∧ ∀ (i : Fin d) (k : ℕ) (z : Vertex d),
      ∫⁻ ω, ENNReal.ofReal |statDiscrepancy hG hGv i k z ω| ∂latticeBondLaw d p ≤
        ENNReal.ofReal (K * (1 + θ₀ * ((3 : ℝ) ^ k) ^ d) ^ (2 * d) *
          Real.exp (-(c * 3 ^ k / 2))) := by
  obtain ⟨K₁, θ₀, hK₁, hθ₀, hsq⟩ :=
    exists_lintegral_sq_statDiscrepancy_le hG hGv hd hpc hp1 hGae
  obtain ⟨C₃, hC₃, c₃, hc₃, h33⟩ := dario_errorstatpart hd hpc
  have hd0 : 0 < d := by omega
  refine ⟨K₁ + C₃.toReal + 1, c₃, θ₀, by positivity, hc₃, hθ₀, fun i k z => ?_⟩
  set ε : Configuration d → ℝ := statDiscrepancy hG hGv i k z with hε
  have hεm : Measurable ε := measurable_statDiscrepancy hG hGv i k z
  have hε2 := hsq i k z
  set P : ℝ := (1 + θ₀ * ((3 : ℝ) ^ k) ^ d) ^ (2 * d) with hP
  obtain ⟨V, ⟨hVk, hzV⟩, -⟩ := TriadicCube.existsUnique_mem d k z
  have hprob : latticeBondLaw d p {ω | ε ω ≠ 0} ≤
      ENNReal.ofReal (C₃.toReal * Real.exp (-c₃ * (3 : ℝ) ^ k)) := by
    have h := h33 V
    rw [hVk] at h
    refine (measure_mono_ae ?_).trans (h.trans_eq ?_)
    · filter_upwards [hGae, ae_partitionEvent hd hpc] with ω hω hP
      intro hne
      refine ⟨z, hzV, fun heq => hne ?_⟩
      exact statDiscrepancy_eq_zero hG hGv hd0 hω hP (i := i) (k := k) (z := z) heq.symm
    · rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC₃]
  set η : ℝ := Real.exp (-(c₃ * 3 ^ k / 2)) with hη
  have hη0 : 0 < η := Real.exp_pos _
  have hAM : ∀ ω, ENNReal.ofReal |ε ω| ≤ ENNReal.ofReal η * ENNReal.ofReal |ε ω| ^ (2 : ℝ) +
      ENNReal.ofReal η⁻¹ * Set.indicator {ω | ε ω ≠ 0} 1 ω := by
    intro ω
    have h := abs_le_mul_sq_add_inv' (e := ε ω) hη0
    refine (ENNReal.ofReal_le_ofReal h).trans ?_
    rw [ENNReal.ofReal_add (by positivity) (by split_ifs <;> positivity),
      ENNReal.ofReal_mul hη0.le, ENNReal.ofReal_mul (inv_pos.2 hη0).le,
      ENNReal.ofReal_pow (abs_nonneg _)]
    refine add_le_add (le_of_eq ?_) (mul_le_mul_right ?_ _)
    · rw [← ENNReal.rpow_natCast, Nat.cast_ofNat]
    · by_cases he : ε ω = 0
      · rw [if_pos he]
        simp
      · rw [if_neg he, Set.indicator_of_mem (show ω ∈ {ω | ε ω ≠ 0} from he)]
        simp
  calc ∫⁻ ω, ENNReal.ofReal |ε ω| ∂latticeBondLaw d p
      ≤ ∫⁻ ω, (ENNReal.ofReal η * ENNReal.ofReal |ε ω| ^ (2 : ℝ) +
          ENNReal.ofReal η⁻¹ * Set.indicator {ω | ε ω ≠ 0} 1 ω) ∂latticeBondLaw d p :=
        lintegral_mono hAM
    _ = ENNReal.ofReal η * ∫⁻ ω, ENNReal.ofReal |ε ω| ^ (2 : ℝ) ∂latticeBondLaw d p +
          ENNReal.ofReal η⁻¹ * latticeBondLaw d p {ω | ε ω ≠ 0} := by
        rw [lintegral_add_left (f := fun ω => ENNReal.ofReal η * ENNReal.ofReal |ε ω| ^ (2 : ℝ))
            (((ENNReal.measurable_ofReal.comp hεm.abs).pow_const _).const_mul _),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_indicator_one
            (show MeasurableSet {ω | ε ω ≠ 0} from hεm (measurableSet_singleton 0).compl)]
    _ ≤ ENNReal.ofReal η * ENNReal.ofReal (K₁ * P) +
          ENNReal.ofReal η⁻¹ * ENNReal.ofReal (C₃.toReal * Real.exp (-c₃ * (3 : ℝ) ^ k)) :=
        add_le_add (mul_le_mul_right hε2 _) (mul_le_mul_right hprob _)
    _ ≤ ENNReal.ofReal ((K₁ + C₃.toReal + 1) * P * η) := by
        rw [← ENNReal.ofReal_mul hη0.le, ← ENNReal.ofReal_mul (inv_pos.2 hη0).le,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hinv : η⁻¹ * Real.exp (-c₃ * (3 : ℝ) ^ k) = η := by
          rw [hη, ← Real.exp_neg, ← Real.exp_add]
          congr 1
          ring
        have h1 : (1 : ℝ) ≤ P := one_le_pow₀ (by
          have : 0 ≤ θ₀ * ((3 : ℝ) ^ k) ^ d := by positivity
          linarith)
        have hC0 : 0 ≤ C₃.toReal := ENNReal.toReal_nonneg
        calc η * (K₁ * P) + η⁻¹ * (C₃.toReal * Real.exp (-c₃ * (3 : ℝ) ^ k))
            = η * (K₁ * P) + C₃.toReal * η := by
              rw [mul_left_comm η⁻¹ C₃.toReal, hinv]
          _ ≤ (K₁ + C₃.toReal + 1) * P * η := by
              nlinarith [mul_nonneg hC0 hη0.le, mul_le_mul_of_nonneg_left h1 (mul_nonneg hC0 hη0.le),
                mul_pos hη0 (lt_of_lt_of_le one_pos h1)]

end Carrier

end Rigidity.Corrector.GeneralDim
