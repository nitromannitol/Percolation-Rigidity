import Rigidity.Proofs.Corrector.DarioStationaryCoarsening
import Rigidity.Proofs.Corrector.PlanarPartitionComparison

/-!
# Dario, Lemma 3.2, Step 1: the two coarsenings differ only where the partitions do

Step 1 of the proof of Lemma 3.2 compares the coarsened corrector of the planar partition `𝒫`
with that of the stationary partition `𝒫_stat^k`. Here the comparison is made through the
discrepancy of the anchors,
`statDiscrepancy i k z = χ_{e_i}(z̄_stat(z)) - χ_{e_i}(z̄(z))`,
in terms of which `∇[χ]_𝒫(y) - ∇[χ]_{𝒫_stat^k}(y)` is the difference of the discrepancies at `y`
and `y + e_j`.

* `ofReal_abs_correctorDiff_coarseAnchor_le`: for a point `a` of the infinite cluster within `d`
  of `z` in every coordinate, `|χ(a) - χ(z̄(z))|` is at most three times the sum of the sums
  of (5.10) over the ball of radius `2d` around `z` (the coarsening error at `a` and the chain
  of coarse gradients from `a` to `z`, as in (5.7));
* `abs_statAnchor_sub_le`: `z̄_stat(z)` is within `3^k + Σ_{|v - z|_∞ ≤ 3^k} size(□_𝒫(v))` of `z`
  in every coordinate (`sizeSum`);
* `statDiscrepancy_eq_zero`: the discrepancy vanishes where the two partition cubes agree;
* `ofReal_abs_statDiscrepancy_le`: the crude bound of the discrepancy by the sums of (5.10) over
  the ball of radius `2 (3^k + sizeSum k z)` around `z`.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter Set LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical ENNReal

/-- The square `z + [-R, R]²` of the lattice. -/
noncomputable def boxAround (z : Vertex 2) (R : ℤ) : Finset (Vertex 2) :=
  Fintype.piFinset fun i => Finset.Icc (z i - R) (z i + R)

theorem mem_boxAround {z v : Vertex 2} {R : ℤ} : v ∈ boxAround z R ↔ ∀ i, |v i - z i| ≤ R := by
  simp only [boxAround, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]
  refine forall_congr' fun i => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The sum of the sizes of the cubes of the planar partition at the vertices of
`z + [-3^k, 3^k]²`. -/
noncomputable def sizeSum (k : ℕ) (z : Vertex 2) (ω : Configuration 2) : ℝ :=
  ∑ v ∈ boxAround z ((3 : ℤ) ^ k), TriadicCube.stoppingSize (planarGoodCubes ω) v

theorem sizeSum_nonneg (k : ℕ) (z : Vertex 2) (ω : Configuration 2) : 0 ≤ sizeSum k z ω :=
  Finset.sum_nonneg fun v _ => stoppingSize_nonneg' _ v

theorem measurable_sizeSum (k : ℕ) (z : Vertex 2) : Measurable (sizeSum k z) :=
  Finset.measurable_sum _ fun v _ => measurable_stoppingSize_planar v

/-- The anchor of the planar partition at `v` is within `size(□_𝒫(v))` of `v` in every
coordinate. -/
theorem abs_planarCoarseAnchor_sub_le {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    (v : Vertex 2) (j : Fin 2) :
    |((planarCoarseAnchor ω v - v) j : ℝ)| ≤
      TriadicCube.stoppingSize (planarGoodCubes ω) v := by
  have h := abs_shiftedAnchor_sub_le (y := 0) (ω := ω) (by rwa [neg_zero,
    configurationTranslation_zero]) v j
  rw [shiftedAnchor_zero, guardAnchor_of_event hP, neg_zero, configurationTranslation_zero,
    sub_zero] at h
  exact h

/-- **Dario, Lemma 3.2, Step 1, the anchors of `𝒫_stat^k`**: `z̄_stat(z)` is within
`3^k + sizeSum k z` of `z` in every coordinate. -/
theorem abs_statAnchor_sub_le {ω : Configuration 2} (hP : PlanarPartitionEvent ω) (k : ℕ)
    (z : Vertex 2) (j : Fin 2) :
    |((statAnchor k ω z - z) j : ℝ)| ≤ (3 : ℝ) ^ k + sizeSum k z ω := by
  set Q := TriadicCube.cappedCube (planarGoodCubes ω) k z with hQ
  have hzQ : z ∈ Q.vertices := (TriadicCube.cappedCube_spec _ k z).1
  have hscale : Q.scale ≤ k := TriadicCube.scale_cappedCube_le _ k z
  have hrad : 2 * Q.radius + 1 = (3 : ℤ) ^ Q.scale := by
    have := Q.side_eq_two_mul_radius_add_one
    rw [← this]
    rfl
  have hpow : (3 : ℤ) ^ Q.scale ≤ (3 : ℤ) ^ k := pow_le_pow_right₀ (by norm_num) hscale
  have hzc : ∀ i, |z i - Q.center i| ≤ Q.radius := (Q.mem_vertices_iff z).1 hzQ
  have hS0 := sizeSum_nonneg k z ω
  -- the centre of the cube is in the box around `z`
  have h3pos : (0 : ℤ) < (3 : ℤ) ^ k := by positivity
  have hr3 : Q.radius ≤ (3 : ℤ) ^ k := by linarith
  have hzc3 : ∀ i, |z i - Q.center i| ≤ (3 : ℤ) ^ k := fun i => (hzc i).trans hr3
  have hcbox : Q.center ∈ boxAround z ((3 : ℤ) ^ k) := by
    rw [mem_boxAround]
    intro i
    rw [abs_sub_comm]
    exact hzc3 i
  have hsize : TriadicCube.stoppingSize (planarGoodCubes ω) Q.center ≤ sizeSum k z ω :=
    Finset.single_le_sum (f := fun v => TriadicCube.stoppingSize (planarGoodCubes ω) v)
      (fun v _ => stoppingSize_nonneg' _ v) hcbox
  -- the two cases of the anchor
  have key : |statAnchor k ω z j - z j| ≤ (3 : ℤ) ^ k ∨
      (|statAnchor k ω z j - Q.center j| ≤
        ((Finset.univ.sup fun i => (planarCoarseAnchor ω Q.center i - Q.center i).natAbs : ℕ) : ℤ)) := by
    unfold statAnchor statAnchorOf
    rw [← hQ]
    split_ifs with h
    · left
      have hfam : Q ∈ planarMeshedFamily ω := h.1.2.1
      have hlarge : 1000 ≤ 3 ^ Q.scale :=
        calc 1000 ≤ 3 ^ 7 := by norm_num
          _ ≤ 3 ^ Q.scale := Nat.pow_le_pow_right (by norm_num) hfam.1
      have ha := (TriadicCube.planarAnchor_spec hfam.2 hlarge).1
      have h1 := (Q.mem_vertices_iff _).1 ha j
      have h2 := hzc j
      rw [abs_le] at h1 h2 ⊢
      constructor <;> omega
    · right
      have hinf := infinite_planarCoarseAnchor hP Q.center
      have hnear := Q.isNearestInf_nearestInf hinf
      have hle := hnear.2 _ hinf
      have hfst : (ofLex (Q.anchorKey (Q.nearestInf ω))).1 ≤
          (ofLex (Q.anchorKey (planarCoarseAnchor ω Q.center))).1 := by
        change toLex _ ≤ toLex _ at hle
        rw [Prod.Lex.toLex_le_toLex] at hle
        rcases hle with h' | ⟨h', -⟩
        · exact h'.le
        · exact h'.le
      rw [TriadicCube.anchorKey_fst, TriadicCube.anchorKey_fst] at hfst
      have hj : (Q.nearestInf ω j - Q.center j).natAbs ≤
          Finset.univ.sup fun i => (Q.nearestInf ω i - Q.center i).natAbs :=
        Finset.le_sup (f := fun i => (Q.nearestInf ω i - Q.center i).natAbs) (Finset.mem_univ j)
      have hj' := hj.trans hfst
      rw [← Int.natCast_natAbs]
      exact_mod_cast hj'
  -- the size bound of the nearest case
  have hsup : ((Finset.univ.sup fun i => (planarCoarseAnchor ω Q.center i - Q.center i).natAbs :
      ℕ) : ℝ) ≤ TriadicCube.stoppingSize (planarGoodCubes ω) Q.center := by
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
      (fun i => (planarCoarseAnchor ω Q.center i - Q.center i).natAbs)
    rw [hi]
    have := abs_planarCoarseAnchor_sub_le hP Q.center i
    rw [Pi.sub_apply] at this
    have e : (((planarCoarseAnchor ω Q.center i - Q.center i).natAbs : ℕ) : ℝ) =
        |((planarCoarseAnchor ω Q.center i - Q.center i : ℤ) : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [e]
    exact this
  have h3k : ((3 : ℤ) ^ k : ℝ) = (3 : ℝ) ^ k := by push_cast; ring
  rw [Pi.sub_apply]
  rcases key with h | h
  · have : |((statAnchor k ω z j - z j : ℤ) : ℝ)| ≤ (3 : ℝ) ^ k := by
      rw [← h3k, ← Int.cast_abs]
      exact_mod_cast h
    linarith
  · have h' : |((statAnchor k ω z j - Q.center j : ℤ) : ℝ)| ≤
        TriadicCube.stoppingSize (planarGoodCubes ω) Q.center := by
      refine le_trans ?_ hsup
      rw [← Int.cast_abs]
      exact_mod_cast h
    have hzc' : |((z j - Q.center j : ℤ) : ℝ)| ≤ (3 : ℝ) ^ k := by
      rw [← h3k, ← Int.cast_abs]
      exact_mod_cast hzc3 j
    set A : ℝ := ((statAnchor k ω z j - Q.center j : ℤ) : ℝ)
    set B : ℝ := ((z j - Q.center j : ℤ) : ℝ)
    have e : ((statAnchor k ω z j - z j : ℤ) : ℝ) = A - B := by
      simp only [A, B]
      push_cast
      ring
    have tri : |A - B| ≤ |A| + |B| :=
      abs_le.2 ⟨by linarith [neg_abs_le A, le_abs_self B], by linarith [le_abs_self A, neg_abs_le B]⟩
    rw [e]
    linarith

section Carrier

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- **The comparison with the anchor of the planar partition**: for `a` in the infinite cluster
within `d` of `z` in every coordinate, `|χ(a) - χ(z̄(z))|` is at most three times the sum of the
sums of (5.10) over the ball of radius `2d` around `z`. -/
theorem ofReal_abs_correctorDiff_coarseAnchor_le {ω : Configuration 2} (hω : ω ∈ G)
    (hP : PlanarPartitionEvent ω) {q : Fin 2 → ℝ} {a z : Vertex 2}
    (ha : ω ∈ infiniteComponentEvent a) {d : ℝ} (hd : ∀ j, |((a - z) j : ℝ)| ≤ d)
    {Λ : Vertex 2 → Configuration 2 → ℝ} (hΛ0 : ∀ x, 0 ≤ Λ x ω)
    (hΛ : ∀ x, ω ∈ infiniteComponentEvent x → ∀ y, (openGraph ω).Adj x y →
      |correctorDiff hG hGv q ω x y| ≤ Λ x ω) :
    ENNReal.ofReal |correctorDiff hG hGv q ω a (planarCoarseAnchor ω z)| ≤
      3 * ∑' u, if ‖latticeEuclideanEmbedding (u - z)‖ ≤ 2 * d then stepSixSum Λ u ω else 0 := by
  set b := planarCoarseAnchor ω z with hbdef
  have hb : ω ∈ infiniteComponentEvent b := infinite_planarCoarseAnchor hP z
  set a'' := planarCoarseAnchor ω a with ha''def
  have ha'' : ω ∈ infiniteComponentEvent a'' := infinite_planarCoarseAnchor hP a
  have hsplit := correctorDiff_add' hG hGv (q := q) hω ha ha'' hb
  have h1 : ENNReal.ofReal |correctorDiff hG hGv q ω a a''| ≤ stepSixSum Λ a ω := by
    have := abs_correctorDiff_guardAnchor_le hG hGv hω hP ha (Λ := fun x => Λ x ω) hΛ0 hΛ
    rw [guardAnchor_of_event hP] at this
    exact this
  set w : Vertex 2 → ℝ := fun x => if ω ∈ infiniteComponentEvent x then
    correctorDiff hG hGv q ω x b else 0 with hw
  set W : Vertex 2 → ℝ := fun u => w (planarCoarseAnchor ω u) with hW
  set e : Vertex 2 → ℝ := fun u => edgeVariationIn ω (planarPartCube ω u).ninefold.vertices w
    with he
  have he0 : ∀ u, 0 ≤ e u := fun u => edgeVariationIn_nonneg _ _ _
  have hchain := abs_sub_le_of_chain (W := W) he0 (fun u u' hn => abs_coarse_step_le hP w hn)
    _ a z le_rfl
  have hWa : W a = correctorDiff hG hGv q ω a'' b := by
    simp only [hW, hw]
    exact if_pos ha''
  have hbb : correctorDiff hG hGv q ω b b = 0 := by
    have := correctorDiff_sub_eq hG hGv (q := q) hω hb hb hb
    linarith
  have hWz : W z = 0 := by
    simp only [hW, hw]
    rw [← hbdef, if_pos hb, hbb]
  have hD2 : correctorDiff hG hGv q ω a'' b = W a - W z := by
    rw [hWa, hWz, sub_zero]
  have hball : ∀ u ∈ latticeBetween a z, ‖latticeEuclideanEmbedding (u - z)‖ ≤ 2 * d :=
    fun u hu => norm_sub_le_of_mem_latticeBetween hd hu
  set T := ∑' u, if ‖latticeEuclideanEmbedding (u - z)‖ ≤ 2 * d then stepSixSum Λ u ω else 0
    with hT
  have h2 : ENNReal.ofReal |correctorDiff hG hGv q ω a'' b| ≤ 2 * T := by
    rw [hD2]
    have hle : |W a - W z| ≤ 2 * ∑ u ∈ latticeBetween a z, e u := by
      have := he0 a
      have := he0 z
      linarith
    calc ENNReal.ofReal |W a - W z| ≤ ENNReal.ofReal (2 * ∑ u ∈ latticeBetween a z, e u) :=
          ENNReal.ofReal_le_ofReal hle
      _ = 2 * ∑ u ∈ latticeBetween a z, ENNReal.ofReal (e u) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_sum_of_nonneg fun u _ => he0 u]
          simp
      _ ≤ 2 * ∑ u ∈ latticeBetween a z, stepSixSum Λ u ω := by
          gcongr with u hu
          exact ofReal_edgeVariationIn_le_stepSixSum hG hGv hω hP hb hΛ0 hΛ u
      _ = 2 * ∑ u ∈ latticeBetween a z,
            (if ‖latticeEuclideanEmbedding (u - z)‖ ≤ 2 * d then stepSixSum Λ u ω else 0) := by
          congr 1
          exact Finset.sum_congr rfl fun u hu => by rw [if_pos (hball u hu)]
      _ ≤ 2 * T := by
          gcongr
          exact ENNReal.sum_le_tsum _
  have haT : stepSixSum Λ a ω ≤ T := by
    have hmem : a ∈ latticeBetween a z := by
      rw [mem_latticeBetween]
      exact fun j => ⟨min_le_left _ _, le_max_left _ _⟩
    have h := ENNReal.le_tsum (f := fun u => if ‖latticeEuclideanEmbedding (u - z)‖ ≤ 2 * d then
      stepSixSum Λ u ω else 0) a
    rw [if_pos (hball a hmem)] at h
    exact h
  rw [hsplit]
  calc ENNReal.ofReal |correctorDiff hG hGv q ω a a'' + correctorDiff hG hGv q ω a'' b|
      ≤ ENNReal.ofReal (|correctorDiff hG hGv q ω a a''| + |correctorDiff hG hGv q ω a'' b|) :=
        ENNReal.ofReal_le_ofReal (abs_add_le _ _)
    _ ≤ ENNReal.ofReal |correctorDiff hG hGv q ω a a''| +
          ENNReal.ofReal |correctorDiff hG hGv q ω a'' b| := ENNReal.ofReal_add_le
    _ ≤ T + 2 * T := add_le_add (h1.trans haT) h2
    _ = 3 * T := by ring

/-- The discrepancy `χ_{e_i}(z̄_stat(z)) - χ_{e_i}(z̄(z))` of the two coarsenings at `z`. -/
noncomputable def statDiscrepancy (i : Fin 2) (k : ℕ) (z : Vertex 2) (ω : Configuration 2) : ℝ :=
  correctorDiff hG hGv (Pi.single i 1) ω (statAnchor k ω z) (guardAnchor ω z)

theorem measurable_statDiscrepancy (i : Fin 2) (k : ℕ) (z : Vertex 2) :
    Measurable (statDiscrepancy hG hGv i k z) :=
  measurable_correctorDiff_comp hG hGv _ (measurable_statAnchor k z) (measurable_guardAnchor z)

/-- The discrepancy vanishes where the cube of `𝒫_stat^k` is the cube of the planar partition. -/
theorem statDiscrepancy_eq_zero {ω : Configuration 2} (hω : ω ∈ G) (hP : PlanarPartitionEvent ω)
    {i : Fin 2} {k : ℕ} {z : Vertex 2}
    (h : TriadicCube.cappedCube (planarGoodCubes ω) k z = planarPartCube ω z) :
    statDiscrepancy hG hGv i k z ω = 0 := by
  unfold statDiscrepancy
  rw [statAnchor_eq_planarCoarseAnchor hP h, guardAnchor_of_event hP]
  have hb := infinite_planarCoarseAnchor hP z
  have := correctorDiff_sub_eq hG hGv (q := Pi.single i 1) hω hb hb hb
  linarith

/-- **The crude bound of the discrepancy**: at most three times the sum of the sums of (5.10)
over the ball of radius `2 (3^k + sizeSum k z)` around `z`. -/
theorem ofReal_abs_statDiscrepancy_le {ω : Configuration 2} (hω : ω ∈ G)
    (hP : PlanarPartitionEvent ω) {i : Fin 2} (k : ℕ) (z : Vertex 2)
    {Λ : Vertex 2 → Configuration 2 → ℝ} (hΛ0 : ∀ x, 0 ≤ Λ x ω)
    (hΛ : ∀ x, ω ∈ infiniteComponentEvent x → ∀ y, (openGraph ω).Adj x y →
      |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ x ω) :
    ENNReal.ofReal |statDiscrepancy hG hGv i k z ω| ≤
      3 * ∑' u, if ‖latticeEuclideanEmbedding (u - z)‖ ≤ 2 * ((3 : ℝ) ^ k + sizeSum k z ω) then
        stepSixSum Λ u ω else 0 := by
  unfold statDiscrepancy
  rw [guardAnchor_of_event hP]
  exact ofReal_abs_correctorDiff_coarseAnchor_le hG hGv hω hP
    (statAnchor_mem_inf k z (infinite_planarCoarseAnchor hP z))
    (abs_statAnchor_sub_le hP k z) hΛ0 hΛ

end Carrier

end Rigidity.Corrector
