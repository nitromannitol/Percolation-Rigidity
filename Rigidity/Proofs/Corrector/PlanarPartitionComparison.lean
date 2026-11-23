import Rigidity.Proofs.Corrector.PlanarCoarseningError

/-!
# The comparison (5.7) of the translated partitions

Dario's (5.7) bounds `|[χ]_{𝒫_y}(z) - [χ]_𝒫(z)|` by `O_s(C)`: the anchors of the two partition
cubes of `z` are joined in a ball of radius `C max(size)`, on which Proposition 2.14 bounds the sum
of `|∇χ|`. Here, with `a' = a_{𝒫_y}(z)`:

* `χ(a') - χ(a_𝒫(a'))` is a coarsening error (5.10) at the cluster vertex `a'`;
* `χ(a_𝒫(a')) - χ(a_𝒫(z))` is an increment of the coarsened corrector along the lattice rectangle
  between `a'` and `z`, bounded by the coarse gradients of main's `abs_coarseAnchor_sub_le`
  (`abs_sub_le_of_chain`), hence by the sums of (5.10) at the vertices of the rectangle;
* the rectangle lies in the ball of radius `2 size(□_{𝒫_y}(z))` around `z`, and the moments follow
  from `lintegral_randomBallSum_le` with the moments of `stepSix_data`
  (`baseComparison`).
-/

namespace Rigidity.Corrector

open MeasureTheory Filter Set LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped Classical ENNReal

/-- The lattice rectangle spanned by two vertices. -/
noncomputable def latticeBetween (z z' : Vertex 2) : Finset (Vertex 2) :=
  Fintype.piFinset fun i => Finset.Icc (min (z i) (z' i)) (max (z i) (z' i))

theorem mem_latticeBetween {z z' u : Vertex 2} :
    u ∈ latticeBetween z z' ↔ ∀ i, min (z i) (z' i) ≤ u i ∧ u i ≤ max (z i) (z' i) := by
  simp only [latticeBetween, Fintype.mem_piFinset, Finset.mem_Icc]

/-- **Chains of neighbour steps**: if `|W u - W u'| ≤ e u + e u'` for all lattice neighbours, then
`|W z - W z'| ≤ 2 Σ_{u ∈ [z, z']} e u - e z - e z'` over the lattice rectangle between `z` and `z'`. -/
theorem abs_sub_le_of_chain {W e : Vertex 2 → ℝ} (he : ∀ u, 0 ≤ e u)
    (hstep : ∀ u u' : Vertex 2, (∀ i, |u i - u' i| ≤ 1) → |W u - W u'| ≤ e u + e u') :
    ∀ n : ℕ, ∀ z z' : Vertex 2, (z 0 - z' 0).natAbs + (z 1 - z' 1).natAbs ≤ n →
      |W z - W z'| ≤ 2 * ∑ u ∈ latticeBetween z z', e u - e z - e z' := by
  intro n
  induction n with
  | zero =>
    intro z z' hn
    have hzz : z = z' := by
      funext i
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> omega
    subst hzz
    have hbox : latticeBetween z z = {z} := by
      ext u
      rw [mem_latticeBetween, Finset.mem_singleton]
      constructor
      · intro h
        funext i
        have := h i
        simp only [min_self, max_self] at this
        omega
      · rintro rfl i
        simp
    rw [hbox, Finset.sum_singleton, sub_self, abs_zero]
    linarith
  | succ n ih =>
    intro z z' hn
    by_cases h0 : z = z'
    · subst h0
      have := ih z z (by simp)
      simpa using this
    · -- a coordinate in which `z` and `z'` differ, and the step towards `z'`
      obtain ⟨i, hi⟩ : ∃ i, z i ≠ z' i := by
        by_contra h
        push Not at h
        exact h0 (funext h)
      set σ : ℤ := if z i < z' i then 1 else -1 with hσ
      set z₁ : Vertex 2 := z + Pi.single i σ with hz₁
      have hz₁i : z₁ i = z i + σ := by simp [hz₁]
      have hz₁j : ∀ j, j ≠ i → z₁ j = z j := fun j hj => by simp [hz₁, hj]
      have hnear : ∀ j, |z j - z₁ j| ≤ 1 := by
        intro j
        by_cases hj : j = i
        · subst hj; rw [hz₁i]; simp only [hσ]; split_ifs <;> simp
        · rw [hz₁j j hj, sub_self, abs_zero]; norm_num
      have hdist : (z₁ 0 - z' 0).natAbs + (z₁ 1 - z' 1).natAbs ≤ n := by
        have key : ∀ j, (z₁ j - z' j).natAbs + (if j = i then 1 else 0) = (z j - z' j).natAbs := by
          intro j
          by_cases hj : j = i
          · subst hj
            rw [if_pos rfl, hz₁i]
            simp only [hσ]
            split_ifs with h <;> omega
          · rw [if_neg hj, hz₁j j hj, add_zero]
        have k0 := key 0
        have k1 := key 1
        fin_cases i <;> simp at k0 k1 <;> omega
      have hsub : latticeBetween z₁ z' ⊆ latticeBetween z z' := by
        intro u hu
        rw [mem_latticeBetween] at hu ⊢
        intro j
        obtain ⟨h1, h2⟩ := hu j
        by_cases hj : j = i
        · subst hj
          rw [hz₁i] at h1 h2
          simp only [hσ] at h1 h2
          split_ifs at h1 h2 with h <;> constructor <;> omega
        · rw [hz₁j j hj] at h1 h2
          exact ⟨h1, h2⟩
      have hnot : z ∉ latticeBetween z₁ z' := by
        rw [mem_latticeBetween]
        intro h
        obtain ⟨h1, h2⟩ := h i
        rw [hz₁i] at h1 h2
        simp only [hσ] at h1 h2
        split_ifs at h1 h2 with h <;> omega
      have hzmem : z ∈ latticeBetween z z' := by
        rw [mem_latticeBetween]
        intro j
        exact ⟨min_le_left _ _, le_max_left _ _⟩
      have hsum : e z + ∑ u ∈ latticeBetween z₁ z', e u ≤ ∑ u ∈ latticeBetween z z', e u := by
        rw [← Finset.sum_insert hnot]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.insert_subset hzmem hsub)
          fun u _ _ => he u
      have h1 := hstep z z₁ hnear
      have h2 := ih z₁ z' hdist
      calc |W z - W z'| ≤ |W z - W z₁| + |W z₁ - W z'| := abs_sub_le _ _ _
        _ ≤ (e z + e z₁) + (2 * ∑ u ∈ latticeBetween z₁ z', e u - e z₁ - e z') := add_le_add h1 h2
        _ ≤ 2 * ∑ u ∈ latticeBetween z z', e u - e z - e z' := by linarith

/-- Coarse gradients between lattice neighbours (main's `abs_coarseAnchor_sub_le` in both orders). -/
theorem abs_coarse_step_le {ω : Configuration 2} (hP : PlanarPartitionEvent ω) (w : Vertex 2 → ℝ)
    {u u' : Vertex 2} (hnear : ∀ i, |u i - u' i| ≤ 1) :
    |w (planarCoarseAnchor ω u) - w (planarCoarseAnchor ω u')| ≤
      edgeVariationIn ω (planarPartCube ω u).ninefold.vertices w +
        edgeVariationIn ω (planarPartCube ω u').ninefold.vertices w := by
  have h0 := edgeVariationIn_nonneg ω (planarPartCube ω u).ninefold.vertices w
  have h0' := edgeVariationIn_nonneg ω (planarPartCube ω u').ninefold.vertices w
  rcases le_total (planarPartCube ω u).scale (planarPartCube ω u').scale with h | h
  · have := abs_coarseAnchor_sub_le hP hnear h w
    linarith
  · have hnear' : ∀ i, |u' i - u i| ≤ 1 := fun i => by rw [abs_sub_comm]; exact hnear i
    have := abs_coarseAnchor_sub_le hP hnear' h w
    rw [abs_sub_comm] at this
    linarith

/-- The tail of `c size(□_𝒫(v))` from the exponential moment of the size. -/
theorem measure_le_const_mul_stoppingSize_le {p : unitInterval} {θ c : ℝ} (hθ : 0 < θ) (hc : 0 < c)
    (v : Vertex 2)
    (hint : Integrable (fun ω => Real.exp (TriadicCube.stoppingSize (planarGoodCubes ω) v / θ))
      (latticeBondLaw 2 p))
    (hb : ∫ ω, Real.exp (TriadicCube.stoppingSize (planarGoodCubes ω) v / θ) ∂latticeBondLaw 2 p ≤ 2)
    (t : ℝ) :
    latticeBondLaw 2 p {ω | t ≤ c * TriadicCube.stoppingSize (planarGoodCubes ω) v} ≤
      ENNReal.ofReal (2 * Real.exp (-(t / (c * θ)))) := by
  set f : Configuration 2 → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (Real.exp (TriadicCube.stoppingSize (planarGoodCubes ω) v / θ))
  have hsub : {ω | t ≤ c * TriadicCube.stoppingSize (planarGoodCubes ω) v} ⊆
      {ω | ENNReal.ofReal (Real.exp (t / (c * θ))) ≤ f ω} := by
    intro ω hω
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    change t ≤ _ at hω
    rw [div_le_div_iff₀ (by positivity) hθ]
    nlinarith
  refine (measure_mono hsub).trans ((meas_ge_le_lintegral_div hint.1.aemeasurable.ennreal_ofReal
    (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top).trans ?_)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => (Real.exp_pos _).le),
    ← ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff_of_pos_right (Real.exp_pos _)]
  exact hb

section Base

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- The edge variation of the corrector increments on the square of side `9s` around a partition
cube is at most the sum of (5.10) at the vertex. -/
theorem ofReal_edgeVariationIn_le_stepSixSum {ω : Configuration 2} (hω : ω ∈ G)
    (hP : PlanarPartitionEvent ω) {q : Fin 2 → ℝ} {b : Vertex 2}
    (hb : ω ∈ infiniteComponentEvent b) {Λ : Vertex 2 → Configuration 2 → ℝ}
    (hΛ0 : ∀ x, 0 ≤ Λ x ω)
    (hΛ : ∀ x, ω ∈ infiniteComponentEvent x → ∀ y, (openGraph ω).Adj x y →
      |correctorDiff hG hGv q ω x y| ≤ Λ x ω) (u : Vertex 2) :
    ENNReal.ofReal (edgeVariationIn ω (planarPartCube ω u).ninefold.vertices
      (fun x => if ω ∈ infiniteComponentEvent x then correctorDiff hG hGv q ω x b else 0)) ≤
      stepSixSum Λ u ω := by
  have h2 := edgeVariationIn_correctorDiff_le hG hGv hω hb (planarPartCube ω u).ninefold.vertices
    hΛ0 hΛ
  have hsize : TriadicCube.stoppingSize (planarGoodCubes ω) u = (3 : ℝ) ^ (planarPartCube ω u).scale :=
    TriadicCube.stoppingSize_eq_of_mem (planarPartCube_spec hP u).1 (planarPartCube_spec hP u).2
  unfold stepSixSum
  rw [hsize]
  calc ENNReal.ofReal (edgeVariationIn ω (planarPartCube ω u).ninefold.vertices _)
      ≤ ENNReal.ofReal (∑ x ∈ (planarPartCube ω u).ninefold.vertices, 4 * Λ x ω) := by
        refine ENNReal.ofReal_le_ofReal (h2.trans_eq ?_)
        rw [Finset.mul_sum]
    _ = ∑ x ∈ (planarPartCube ω u).ninefold.vertices, ENNReal.ofReal (4 * Λ x ω) :=
        ENNReal.ofReal_sum_of_nonneg fun x _ => by have := hΛ0 x; positivity
    _ = ∑ x ∈ (planarPartCube ω u).ninefold.vertices, ENNReal.ofReal
          (if ‖latticeEuclideanEmbedding (x - u)‖ ≤ 10 * (3 : ℝ) ^ (planarPartCube ω u).scale
            then 4 * Λ x ω else 0) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [if_pos (norm_sub_le_of_mem_ninefold (planarPartCube_spec hP u).1 hx)]
    _ ≤ _ := ENNReal.sum_le_tsum _

/-- The anchor of `𝒫_y` at `z` is within `size(□_{𝒫_y}(z))` of `z` in every coordinate. -/
theorem abs_shiftedAnchor_sub_le {ω : Configuration 2} {y : Vertex 2}
    (hP : PlanarPartitionEvent (configurationTranslation (-y) ω)) (z : Vertex 2) (j : Fin 2) :
    |((shiftedAnchor y ω z - z) j : ℝ)| ≤
      TriadicCube.stoppingSize (planarGoodCubes (configurationTranslation (-y) ω)) (z - y) := by
  set ω' := configurationTranslation (-y) ω
  set Q := planarPartCube ω' (z - y)
  have hsize : TriadicCube.stoppingSize (planarGoodCubes ω') (z - y) = (3 : ℝ) ^ Q.scale :=
    TriadicCube.stoppingSize_eq_of_mem (planarPartCube_spec hP (z - y)).1
      (planarPartCube_spec hP (z - y)).2
  rw [hsize]
  have ha := planarCoarseAnchor_mem hP (z - y)
  have hz := (planarPartCube_spec hP (z - y)).1
  rw [TriadicCube.mem_vertices_iff] at ha hz
  have hrad : 2 * Q.radius + 1 = (3 : ℤ) ^ Q.scale := by
    have := Q.side_eq_two_mul_radius_add_one
    rw [← this]
    rfl
  have e : (shiftedAnchor y ω z - z) j = planarCoarseAnchor ω' (z - y) j - (z - y) j := by
    simp only [shiftedAnchor, Pi.sub_apply, Pi.add_apply]
    rw [guardAnchor_of_event hP]
    ring
  have key : |planarCoarseAnchor ω' (z - y) j - (z - y) j| ≤ (3 : ℤ) ^ Q.scale := by
    have h1 := ha j
    have h2 := hz j
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith
  rw [e]
  exact_mod_cast key

/-- The vertices of the lattice rectangle between `a` and `z` are within `2 d` of `z` when `a` is
within `d` of `z` in every coordinate. -/
theorem norm_sub_le_of_mem_latticeBetween {a z u : Vertex 2} {d : ℝ}
    (ha : ∀ j, |((a - z) j : ℝ)| ≤ d) (hu : u ∈ latticeBetween a z) :
    ‖latticeEuclideanEmbedding (u - z)‖ ≤ 2 * d := by
  rw [mem_latticeBetween] at hu
  have hc : ∀ j, |((u - z) j : ℝ)| ≤ d := by
    intro j
    obtain ⟨h1, h2⟩ := hu j
    have h3 := ha j
    have key : |(u - z) j| ≤ |(a - z) j| := by
      simp only [Pi.sub_apply]
      rw [abs_le]
      rcases le_total (a j) (z j) with h | h
      · rw [min_eq_left h] at h1
        rw [max_eq_right h] at h2
        rw [abs_of_nonpos (by omega)]
        constructor <;> omega
      · rw [min_eq_right h] at h1
        rw [max_eq_left h] at h2
        rw [abs_of_nonneg (by omega)]
        constructor <;> omega
    have : |((u - z) j : ℝ)| ≤ |((a - z) j : ℝ)| := by exact_mod_cast key
    linarith
  have := norm_latticeEuclideanEmbedding_le_sum (u - z)
  linarith [hc 0, hc 1]

theorem stoppingSize_nonneg' (G' : Set (TriadicCube 2)) (x : Vertex 2) :
    0 ≤ TriadicCube.stoppingSize G' x := by
  unfold TriadicCube.stoppingSize
  exact ENNReal.toReal_nonneg

/-- **The comparison (5.7) of the translated partitions, pointwise**: `|[χ]_{𝒫_{y'}}(z) - [χ]_𝒫(z)|`
is at most three times the sum of the sums of (5.10) over the ball of radius
`4 size(□_{𝒫_{y'}}(z))` around `z`. -/
theorem ofReal_abs_coarseField_sub_le {ω : Configuration 2} (hω : ω ∈ G)
    (hP : PlanarPartitionEvent ω) {y' : Vertex 2}
    (hP' : PlanarPartitionEvent (configurationTranslation (-y') ω)) {i : Fin 2}
    {Λ : Vertex 2 → Configuration 2 → ℝ} (hΛ0 : ∀ x, 0 ≤ Λ x ω)
    (hΛ : ∀ x, ω ∈ infiniteComponentEvent x → ∀ y, (openGraph ω).Adj x y →
      |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ x ω) (z : Vertex 2) :
    ENNReal.ofReal |coarseField hG hGv i y' z ω - coarseField hG hGv i 0 z ω| ≤
      3 * ∑' u, if ‖latticeEuclideanEmbedding (u - z)‖ ≤ 4 * TriadicCube.stoppingSize
        (planarGoodCubes (configurationTranslation (-y') ω)) (z - y') then
          stepSixSum Λ u ω else 0 := by
  set q : Fin 2 → ℝ := Pi.single i 1
  set a' := shiftedAnchor y' ω z with ha'def
  set a := shiftedAnchor 0 ω z with hadef
  set b := shiftedAnchor 0 ω 0 with hbdef
  set Sz := TriadicCube.stoppingSize (planarGoodCubes (configurationTranslation (-y') ω)) (z - y')
  have hSz0 : 0 ≤ Sz := stoppingSize_nonneg' _ _
  have ha' : ω ∈ infiniteComponentEvent a' := infinite_shiftedAnchor hP' z
  have ha : ω ∈ infiniteComponentEvent a := infinite_shiftedAnchor_zero hP z
  have hb : ω ∈ infiniteComponentEvent b := infinite_shiftedAnchor_zero hP 0
  have haz : a = planarCoarseAnchor ω z := by rw [hadef, shiftedAnchor_zero, guardAnchor_of_event hP]
  set a'' := planarCoarseAnchor ω a' with ha''def
  have ha'' : ω ∈ infiniteComponentEvent a'' := infinite_planarCoarseAnchor hP a'
  have hdiff : coarseField hG hGv i y' z ω - coarseField hG hGv i 0 z ω =
      correctorDiff hG hGv q ω a' a := correctorDiff_sub_eq hG hGv hω ha' ha hb
  have hsplit := correctorDiff_add' hG hGv (q := q) hω ha' ha'' ha
  -- the coarsening error at `a'`
  have h1 : ENNReal.ofReal |correctorDiff hG hGv q ω a' a''| ≤ stepSixSum Λ a' ω := by
    have := abs_correctorDiff_guardAnchor_le hG hGv hω hP ha' (Λ := fun x => Λ x ω) hΛ0 hΛ
    rw [guardAnchor_of_event hP] at this
    exact this
  -- the chain from `a'` to `z`
  set w : Vertex 2 → ℝ := fun x => if ω ∈ infiniteComponentEvent x then
    correctorDiff hG hGv q ω x b else 0 with hw
  set W : Vertex 2 → ℝ := fun u => w (planarCoarseAnchor ω u) with hW
  set e : Vertex 2 → ℝ := fun u => edgeVariationIn ω (planarPartCube ω u).ninefold.vertices w
    with he
  have he0 : ∀ u, 0 ≤ e u := fun u => edgeVariationIn_nonneg _ _ _
  have hchain := abs_sub_le_of_chain (W := W) he0 (fun u u' hn => abs_coarse_step_le hP w hn)
    _ a' z le_rfl
  have hWa' : W a' = correctorDiff hG hGv q ω a'' b := by
    simp only [hW, hw]
    exact if_pos ha''
  have hWz : W z = correctorDiff hG hGv q ω a b := by
    simp only [hW, hw]
    rw [← haz, if_pos ha]
  have hD2 : correctorDiff hG hGv q ω a'' a = W a' - W z := by
    rw [hWa', hWz]
    exact (correctorDiff_sub_eq hG hGv hω ha'' ha hb).symm
  have hball : ∀ u ∈ latticeBetween a' z, ‖latticeEuclideanEmbedding (u - z)‖ ≤ 4 * Sz := by
    intro u hu
    have := norm_sub_le_of_mem_latticeBetween (abs_shiftedAnchor_sub_le hP' z) hu
    linarith
  set T := ∑' u, if ‖latticeEuclideanEmbedding (u - z)‖ ≤ 4 * Sz then stepSixSum Λ u ω else 0
    with hT
  have h2 : ENNReal.ofReal |correctorDiff hG hGv q ω a'' a| ≤ 2 * T := by
    rw [hD2]
    have hle : |W a' - W z| ≤ 2 * ∑ u ∈ latticeBetween a' z, e u := by
      have := he0 a'
      have := he0 z
      linarith
    calc ENNReal.ofReal |W a' - W z| ≤ ENNReal.ofReal (2 * ∑ u ∈ latticeBetween a' z, e u) :=
          ENNReal.ofReal_le_ofReal hle
      _ = 2 * ∑ u ∈ latticeBetween a' z, ENNReal.ofReal (e u) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_sum_of_nonneg fun u _ => he0 u]
          simp
      _ ≤ 2 * ∑ u ∈ latticeBetween a' z, stepSixSum Λ u ω := by
          gcongr with u hu
          exact ofReal_edgeVariationIn_le_stepSixSum hG hGv hω hP hb hΛ0 hΛ u
      _ = 2 * ∑ u ∈ latticeBetween a' z,
            (if ‖latticeEuclideanEmbedding (u - z)‖ ≤ 4 * Sz then stepSixSum Λ u ω else 0) := by
          congr 1
          exact Finset.sum_congr rfl fun u hu => by rw [if_pos (hball u hu)]
      _ ≤ 2 * T := by
          gcongr
          exact ENNReal.sum_le_tsum _
  have ha'T : stepSixSum Λ a' ω ≤ T := by
    have hmem : a' ∈ latticeBetween a' z := by
      rw [mem_latticeBetween]
      exact fun j => ⟨min_le_left _ _, le_max_left _ _⟩
    have h := ENNReal.le_tsum (f := fun u => if ‖latticeEuclideanEmbedding (u - z)‖ ≤ 4 * Sz then
      stepSixSum Λ u ω else 0) a'
    rw [if_pos (hball a' hmem)] at h
    exact h
  rw [hdiff, hsplit]
  calc ENNReal.ofReal |correctorDiff hG hGv q ω a' a'' + correctorDiff hG hGv q ω a'' a|
      ≤ ENNReal.ofReal (|correctorDiff hG hGv q ω a' a''| + |correctorDiff hG hGv q ω a'' a|) :=
        ENNReal.ofReal_le_ofReal (abs_add_le _ _)
    _ ≤ ENNReal.ofReal |correctorDiff hG hGv q ω a' a''| +
          ENNReal.ofReal |correctorDiff hG hGv q ω a'' a| := ENNReal.ofReal_add_le
    _ ≤ T + 2 * T := add_le_add (h1.trans ha'T) h2
    _ = 3 * T := by ring

/-- **The comparison (5.7) of the translated partitions** (`BaseComparison`), from the order-zero
regularity input and the exponential moments of the partition sizes. -/
theorem baseComparison (hR3 : ArmstrongDarioOrderZeroTwo) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) :
    ∃ B k : ℝ, 0 < B ∧ 0 < k ∧ BaseComparison hG hGv p B k := by
  obtain ⟨Λ, A, k, hA0, hk0, hΛm, hΛ0, hlip, hmom6⟩ := stepSix_data hG hGv hR3 hpc hp1 hGae
  obtain ⟨θ', hθ', hexp⟩ := (planar_meshed_partition_estimates hpc).2.1
  set B₂ : ℝ := 4 * (1 + 8 * (4 * θ')) ^ 2 with hB₂
  have hB₂4 : 4 ≤ B₂ := by
    have : 1 ≤ (1 + 8 * (4 * θ')) ^ 2 := one_le_pow₀ (by linarith)
    linarith
  set B : ℝ := Real.sqrt 2 * (3 * B₂ * A * 2 ^ k) with hB
  refine ⟨B, k + 2, by positivity, by positivity, fun i y' z q hq => ?_⟩
  have hq0 : 0 < q := by linarith
  set ρ : Configuration 2 → ℝ := fun ω => 4 * TriadicCube.stoppingSize
    (planarGoodCubes (configurationTranslation (-y') ω)) (z - y') with hρ
  have hρm : Measurable ρ := ((measurable_stoppingSize_planar (z - y')).comp
    (measurable_configurationTranslation (-y'))).const_mul 4
  have htail : ∀ t : ℝ, 0 ≤ t →
      latticeBondLaw 2 p {ω | t ≤ ρ ω} ≤ ENNReal.ofReal (2 * Real.exp (-(t / (4 * θ')))) := by
    intro t _
    have hmeas : MeasurableSet {ω : Configuration 2 |
        t ≤ 4 * TriadicCube.stoppingSize (planarGoodCubes ω) (z - y')} :=
      measurableSet_le measurable_const ((measurable_stoppingSize_planar (z - y')).const_mul 4)
    have hpre : {ω | t ≤ ρ ω} = configurationTranslation (-y') ⁻¹'
        {ω | t ≤ 4 * TriadicCube.stoppingSize (planarGoodCubes ω) (z - y')} := rfl
    rw [hpre, (measurePreserving_configurationTranslation p (-y')).measure_preimage
      hmeas.nullMeasurableSet]
    exact measure_le_const_mul_stoppingSize_le hθ' (by norm_num) (z - y') (hexp _).1 (hexp _).2 t
  have hYm : ∀ u, ∫⁻ ω, stepSixSum (Λ i) u ω ^ (2 * q) ∂latticeBondLaw 2 p ≤
      ENNReal.ofReal (((A * (2 * q) ^ k) ^ q) ^ 2) := by
    intro u
    refine (hmom6 i u (2 * q) (by linarith)).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    push_cast
    ring_nf
  have hball := lintegral_randomBallSum_le (p := p) z (θ := 4 * θ') (by positivity) htail hρm
    (Y := fun u => stepSixSum (Λ i) u) (fun u => measurable_stepSixSum (hΛm i) u) hq
    (by positivity) hYm
  have hall : ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ x, ω ∈ infiniteComponentEvent x → ∀ y,
      (openGraph ω).Adj x y → |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ i x ω :=
    ae_all_iff.2 fun x => hlip i x
  have hpt : ∀ᵐ ω ∂latticeBondLaw 2 p,
      ENNReal.ofReal (|coarseField hG hGv i y' z ω - coarseField hG hGv i 0 z ω| ^ q) ≤
        3 ^ q * (∑' u, if ‖latticeEuclideanEmbedding (u - z)‖ ≤ ρ ω then
          stepSixSum (Λ i) u ω else 0) ^ q := by
    filter_upwards [hGae, ae_planarPartitionEvent hpc,
      ae_planarPartitionEvent_translation hpc (-y'), hall] with ω hω hP hP' hl
    have h := ofReal_abs_coarseField_sub_le hG hGv hω hP hP' (Λ := Λ i) (fun x => hΛ0 i x ω) hl z
    rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq0.le]
    calc ENNReal.ofReal |coarseField hG hGv i y' z ω - coarseField hG hGv i 0 z ω| ^ q
        ≤ (3 * ∑' u, if ‖latticeEuclideanEmbedding (u - z)‖ ≤ ρ ω then
            stepSixSum (Λ i) u ω else 0) ^ q := ENNReal.rpow_le_rpow h hq0.le
      _ = _ := ENNReal.mul_rpow_of_nonneg _ _ hq0.le
  unfold mom
  have h3 : (3 : ℝ≥0∞) ^ q = ENNReal.ofReal (3 ^ q) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num) hq0.le, ENNReal.ofReal_ofNat]
  calc ∫⁻ ω, ENNReal.ofReal (|coarseField hG hGv i y' z ω - coarseField hG hGv i 0 z ω| ^ q)
        ∂latticeBondLaw 2 p
      ≤ ∫⁻ ω, 3 ^ q * (∑' u, if ‖latticeEuclideanEmbedding (u - z)‖ ≤ ρ ω then
          stepSixSum (Λ i) u ω else 0) ^ q ∂latticeBondLaw 2 p := lintegral_mono_ae hpt
    _ = 3 ^ q * ∫⁻ ω, (∑' u, if ‖latticeEuclideanEmbedding (u - z)‖ ≤ ρ ω then
          stepSixSum (Λ i) u ω else 0) ^ q ∂latticeBondLaw 2 p :=
        lintegral_const_mul' _ _ (by rw [h3]; exact ENNReal.ofReal_ne_top)
    _ ≤ ENNReal.ofReal (3 ^ q) * ENNReal.ofReal ((4 * (1 + 8 * q * (4 * θ')) ^ 2) ^ (q - 1) *
          (Real.sqrt 2 * 4 * (1 + 8 * (4 * θ')) ^ 2 * (A * (2 * q) ^ k) ^ q)) := by
        rw [h3]
        exact mul_le_mul_right hball _
    _ ≤ ENNReal.ofReal ((B * q ^ (k + 2)) ^ q) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hq2 : (1 : ℝ) ≤ q ^ 2 := one_le_pow₀ hq
        have hbase : 4 * (1 + 8 * q * (4 * θ')) ^ 2 ≤ B₂ * q ^ 2 := by
          rw [hB₂]
          have : 1 + 8 * q * (4 * θ') ≤ q * (1 + 8 * (4 * θ')) := by nlinarith
          have h0 : 0 ≤ 1 + 8 * q * (4 * θ') := by positivity
          nlinarith [pow_le_pow_left₀ h0 this 2]
        have h1 : (4 * (1 + 8 * q * (4 * θ')) ^ 2) ^ (q - 1) ≤ (B₂ * q ^ 2) ^ q / B₂ := by
          calc (4 * (1 + 8 * q * (4 * θ')) ^ 2) ^ (q - 1) ≤ (B₂ * q ^ 2) ^ (q - 1) :=
                Real.rpow_le_rpow (by positivity) hbase (by linarith)
            _ = (B₂ * q ^ 2) ^ q / (B₂ * q ^ 2) := by
                rw [Real.rpow_sub (by positivity), Real.rpow_one]
            _ ≤ (B₂ * q ^ 2) ^ q / B₂ := by
                gcongr
                nlinarith
        have h2 : Real.sqrt 2 ≤ Real.sqrt 2 ^ q := by
          simpa using Real.rpow_le_rpow_of_exponent_le
            (show (1 : ℝ) ≤ Real.sqrt 2 by rw [Real.one_le_sqrt]; norm_num) hq
        have hAq : (A * (2 * q) ^ k) ^ q = (A * 2 ^ k * q ^ k) ^ q := by
          rw [Real.mul_rpow (by norm_num) hq0.le, mul_assoc]
        have hkq : q ^ 2 * q ^ k = q ^ (k + 2) := by
          rw [Real.rpow_add hq0, Real.rpow_two, mul_comm]
        have e : Real.sqrt 2 * 4 * (1 + 8 * (4 * θ')) ^ 2 = Real.sqrt 2 * B₂ := by rw [hB₂]; ring
        rw [e, hAq]
        calc 3 ^ q * ((4 * (1 + 8 * q * (4 * θ')) ^ 2) ^ (q - 1) *
              (Real.sqrt 2 * B₂ * (A * 2 ^ k * q ^ k) ^ q))
            ≤ 3 ^ q * ((B₂ * q ^ 2) ^ q / B₂ * (Real.sqrt 2 * B₂ * (A * 2 ^ k * q ^ k) ^ q)) := by
              gcongr
          _ = Real.sqrt 2 * (3 ^ q * (B₂ * q ^ 2) ^ q * (A * 2 ^ k * q ^ k) ^ q) := by
              have hB₂ne : B₂ ≠ 0 := (by linarith : (0 : ℝ) < B₂).ne'
              rw [div_mul_eq_mul_div, mul_div_assoc', div_eq_iff hB₂ne]
              ring
          _ ≤ Real.sqrt 2 ^ q * (3 ^ q * (B₂ * q ^ 2) ^ q * (A * 2 ^ k * q ^ k) ^ q) := by
              gcongr
          _ = (B * q ^ (k + 2)) ^ q := by
              rw [← Real.mul_rpow (by norm_num) (by positivity),
                ← Real.mul_rpow (by positivity) (by positivity),
                ← Real.mul_rpow (by positivity) (by positivity), hB, ← hkq]
              congr 1
              ring

end Base


end Rigidity.Corrector
