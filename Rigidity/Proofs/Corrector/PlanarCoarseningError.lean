import Rigidity.Proofs.Corrector.PlanarCorrectorLipschitz
import Rigidity.Proofs.Corrector.DarioCoarsenedFields
import Rigidity.Proofs.Corrector.RandomBallSums
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The coarsening error (5.10) of the planar corrector

Step 6 of the proof of Dario's Theorem 1 bounds `|χ(y) - [χ]_𝒫(y)| 1_{y ∈ 𝒞_∞}` by the sum of
`|∇χ|` over a ball of radius `C size(□_𝒫(y))`, and this sum by Proposition 2.15. Here:

* `lipschitz_correctorDiff`: the Lipschitz bound `|χ(x) - χ(y)| ≤ (L max(X ∘ τ_{-x}, 2)² + 1) Σ|q_i|`
  along every open edge `xy` at a cluster vertex `x`, from `lipschitz_correctedPlane_origin` and
  the stationarity of the corrector increments;
* `abs_correctorDiff_guardAnchor_le`: on the partition event, `|χ(v) - χ(a_𝒫(v))|` is at most four
  times the sum of these bounds over the square of side `9 size(□_𝒫(v))` around the partition cube
  (main's `abs_sub_coarseAnchor_le`), hence over the ball of radius `10 size(□_𝒫(v))` around `v`.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter Set LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped Classical ENNReal

/-- Adjacent vertices have the same open component. -/
theorem mem_infiniteComponentEvent_of_adj {ω : Configuration 2} {x y : Vertex 2}
    (hxy : (openGraph ω).Adj x y) (hx : ω ∈ infiniteComponentEvent x) :
    ω ∈ infiniteComponentEvent y := by
  have : (openGraph ω).connectedComponentMk y = (openGraph ω).connectedComponentMk x :=
    SimpleGraph.ConnectedComponent.eq.2 hxy.reachable.symm
  change ((openGraph ω).connectedComponentMk y).supp.Infinite
  rw [this]
  exact hx

theorem abs_sum_mul_le_of_near (q : Fin 2 → ℝ) {y : Vertex 2} (hy : ∀ i, |y i| ≤ 1) :
    |∑ i, q i * (y i : ℝ)| ≤ ∑ i, |q i| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  have : |((y i : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast hy i
  nlinarith [abs_nonneg (q i)]

section Carrier

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- **The Lipschitz bound of the corrector increments at every vertex.** -/
theorem lipschitz_correctorDiff (hR3 : ArmstrongDarioOrderZeroTwo) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) :
    ∃ s θ L : ℝ, 0 < s ∧ 0 < θ ∧ 0 < L ∧ ∃ X : Configuration 2 → ℝ, Measurable X ∧
      (∀ ω, 0 ≤ X ω) ∧ IsOsBond 2 p X s θ ∧
      ∀ (q : Fin 2 → ℝ) (x : Vertex 2), ∀ᵐ ω ∂latticeBondLaw 2 p,
        ω ∈ infiniteComponentEvent x → ∀ y, (openGraph ω).Adj x y →
          |correctorDiff hG hGv q ω x y| ≤
            (L * max (X (configurationTranslation (-x) ω)) 2 ^ 2 + 1) * ∑ i, |q i| := by
  obtain ⟨s, θ, L, hs, hθ, hL, X, hXm, hX0, hXO, hae⟩ := lipschitz_correctedPlane_origin hR3 hpc hp1
  refine ⟨s, θ, L, hs, hθ, hL, X, hXm, hX0, hXO, fun q x => ?_⟩
  have hTq := (measurePreserving_configurationTranslation p (-x)).quasiMeasurePreserving
  filter_upwards [hGae, hTq.ae hGae, hTq.ae hae] with ω hω hω' hlip hx y hxy
  set ω' := configurationTranslation (-x) ω with hω'def
  have hy : ω ∈ infiniteComponentEvent y := mem_infiniteComponentEvent_of_adj hxy hx
  rw [← correctorDiff_translate hG hGv (-x) hω hω' hx hy, add_neg_cancel]
  obtain ⟨h', -⟩ := hGv hω'
  set K := uniqueInfiniteComponent h'
  have hKinf := uniqueInfiniteComponent_infinite h'
  obtain ⟨ℓ, hℓ⟩ := exists_correctedPlane_of_valid (hGv hω') hKinf q
  have h0 : (0 : Vertex 2) ∈ K.supp := by
    have := mem_infiniteComponentEvent_translation (-x) hx
    rw [add_neg_cancel] at this
    exact (mem_uniqueInfiniteComponent_iff h' 0).2 this
  have hy' : y + -x ∈ K.supp :=
    (mem_uniqueInfiniteComponent_iff h' _).2 (mem_infiniteComponentEvent_translation (-x) hy)
  have hadj' : (openGraph ω').Adj 0 (y + -x) := by
    have := (openGraph_adj_translation_iff (-x) ω x y).2 hxy
    rwa [add_neg_cancel] at this
  have hadjK : (componentGraph K).Adj ⟨0, h0⟩ ⟨y + -x, hy'⟩ := (K.toSimpleGraph_adj h0 hy').2 hadj'
  have hD := correctorDiff_eq hG hGv hω' hKinf hℓ ⟨0, h0⟩ ⟨y + -x, hy'⟩
  have hl := hlip h' q ℓ hℓ ⟨0, h0⟩ ⟨y + -x, hy'⟩ hadjK (by
    show ‖latticeEuclideanEmbedding (0 : Vertex 2)‖ < 2
    rw [latticeEuclideanEmbedding_zero, norm_zero]
    norm_num)
  have hnear : ∀ i, |(y + -x) i| ≤ 1 := by
    have h := near_of_nearestNeighbor_adj (openGraph_le ω' hadj')
    intro i
    have h' := h i
    simp only [Pi.zero_apply, zero_sub, abs_neg] at h'
    exact h'
  have hq := abs_sum_mul_le_of_near q hnear
  change correctorDiff hG hGv q ω' (0 : Vertex 2) (y + -x) =
    (ℓ ⟨0, h0⟩ - ∑ i, q i * (((0 : Vertex 2) i : ℤ) : ℝ)) -
      (ℓ ⟨y + -x, hy'⟩ - ∑ i, q i * (((y + -x) i : ℤ) : ℝ)) at hD
  simp only [Pi.zero_apply, Int.cast_zero, mul_zero, Finset.sum_const_zero, sub_zero] at hD
  rw [hD]
  calc |ℓ ⟨0, h0⟩ - (ℓ ⟨y + -x, hy'⟩ - ∑ i, q i * ((y + -x) i : ℝ))|
      ≤ |ℓ ⟨0, h0⟩ - ℓ ⟨y + -x, hy'⟩| + |∑ i, q i * ((y + -x) i : ℝ)| := by
        rw [show ℓ ⟨0, h0⟩ - (ℓ ⟨y + -x, hy'⟩ - ∑ i, q i * ((y + -x) i : ℝ)) =
          (ℓ ⟨0, h0⟩ - ℓ ⟨y + -x, hy'⟩) + ∑ i, q i * ((y + -x) i : ℝ) by ring]
        exact abs_add_le _ _
    _ ≤ L * max (X ω') 2 ^ 2 * ∑ i, |q i| + ∑ i, |q i| := add_le_add hl hq
    _ = (L * max (X ω') 2 ^ 2 + 1) * ∑ i, |q i| := by ring

/-- The lattice neighbours of a vertex inside a finite set are at most four. -/
theorem card_filter_adj_le (ω : Configuration 2) (S : Finset (Vertex 2)) (x : Vertex 2) :
    (S.filter fun y => (openGraph ω).Adj x y).card ≤ 4 := by
  have hsub : S.filter (fun y => (openGraph ω).Adj x y) ⊆
      {x + LatticeProb.unit 0, x - LatticeProb.unit 0, x + LatticeProb.unit 1,
        x - LatticeProb.unit 1} := by
    intro y hy
    rw [Finset.mem_filter] at hy
    have h : ∃ j : Fin 2, y = x + LatticeProb.unit j ∨ x = y + LatticeProb.unit j :=
      openGraph_le ω hy.2
    obtain ⟨j, hj | hj⟩ := h
    · fin_cases j <;> simp [hj]
    · have : y = x - LatticeProb.unit j := by rw [hj]; abel
      fin_cases j <;> simp [this]
  exact (Finset.card_le_card hsub).trans Finset.card_le_four

/-- **The edge variation of the corrector increments** over a finite set is at most four times the
sum of the Lipschitz bounds. -/
theorem edgeVariationIn_correctorDiff_le {ω : Configuration 2} (hω : ω ∈ G) {q : Fin 2 → ℝ}
    {v : Vertex 2} (hv : ω ∈ infiniteComponentEvent v) (S : Finset (Vertex 2))
    {Λ : Vertex 2 → ℝ} (hΛ0 : ∀ x, 0 ≤ Λ x)
    (hΛ : ∀ x, ω ∈ infiniteComponentEvent x → ∀ y, (openGraph ω).Adj x y →
      |correctorDiff hG hGv q ω x y| ≤ Λ x) :
    edgeVariationIn ω S (fun x => if ω ∈ infiniteComponentEvent x then
      correctorDiff hG hGv q ω x v else 0) ≤ 4 * ∑ x ∈ S, Λ x := by
  unfold edgeVariationIn
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  have hterm : ∀ y ∈ S, (if (openGraph ω).Adj x y then
      |(if ω ∈ infiniteComponentEvent x then correctorDiff hG hGv q ω x v else 0) -
        (if ω ∈ infiniteComponentEvent y then correctorDiff hG hGv q ω y v else 0)| else 0) ≤
      if (openGraph ω).Adj x y then Λ x else 0 := by
    intro y _
    by_cases hxy : (openGraph ω).Adj x y
    · rw [if_pos hxy, if_pos hxy]
      by_cases hx : ω ∈ infiniteComponentEvent x
      · have hy := mem_infiniteComponentEvent_of_adj hxy hx
        rw [if_pos hx, if_pos hy, correctorDiff_sub_eq hG hGv hω hx hy hv]
        exact hΛ x hx y hxy
      · have hy : ω ∉ infiniteComponentEvent y := fun hy =>
          hx (mem_infiniteComponentEvent_of_adj hxy.symm hy)
        rw [if_neg hx, if_neg hy, sub_zero, abs_zero]
        exact hΛ0 x
    · rw [if_neg hxy, if_neg hxy]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have := card_filter_adj_le ω S x
  have h4 : ((S.filter fun y => (openGraph ω).Adj x y).card : ℝ) ≤ 4 := by exact_mod_cast this
  nlinarith [hΛ0 x]

theorem norm_latticeEuclideanEmbedding_le_sum (v : Vertex 2) :
    ‖latticeEuclideanEmbedding v‖ ≤ |(v 0 : ℝ)| + |(v 1 : ℝ)| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have h0 : ‖latticeEuclideanEmbedding v 0‖ = |(v 0 : ℝ)| := Real.norm_eq_abs _
  have h1 : ‖latticeEuclideanEmbedding v 1‖ = |(v 1 : ℝ)| := Real.norm_eq_abs _
  rw [h0, h1, Real.sqrt_le_left (by positivity)]
  nlinarith [mul_nonneg (abs_nonneg (v 0 : ℝ)) (abs_nonneg (v 1 : ℝ)), sq_abs (v 0 : ℝ),
    sq_abs (v 1 : ℝ)]

/-- The square of side `9s` around a triadic cube of side `s` containing `v` lies in the ball of
radius `10 s` around `v`. -/
theorem norm_sub_le_of_mem_ninefold {Q : TriadicCube 2} {v x : Vertex 2} (hv : v ∈ Q.vertices)
    (hx : x ∈ Q.ninefold.vertices) :
    ‖latticeEuclideanEmbedding (x - v)‖ ≤ 10 * (3 : ℝ) ^ Q.scale := by
  rw [IntegerCube.mem_vertices] at hx
  rw [TriadicCube.mem_vertices_iff] at hv
  have hR := TriadicCube.two_mul_ninefoldRadius Q
  have hrad : 2 * Q.radius + 1 = (3 : ℤ) ^ Q.scale := by
    have := Q.side_eq_two_mul_radius_add_one
    rw [← this]
    rfl
  have hcoord : ∀ i, |((x - v) i : ℝ)| ≤ 5 * (3 : ℝ) ^ Q.scale := by
    intro i
    obtain ⟨h1, h2⟩ := hx i
    have h3 := hv i
    simp only [TriadicCube.ninefold] at h1 h2
    rw [abs_le] at h3
    have key : |(x - v) i| ≤ 5 * (3 : ℤ) ^ Q.scale := by
      rw [abs_le, Pi.sub_apply]
      constructor <;> push_cast at h1 h2 ⊢ <;> omega
    exact_mod_cast key
  have := norm_latticeEuclideanEmbedding_le_sum (x - v)
  linarith [hcoord 0, hcoord 1]

/-- **The coarsening error at a cluster vertex** (Dario, (5.10)): on the partition event,
`|χ(v) - χ(a_𝒫(v))|` is at most four times the sum of the Lipschitz bounds over the ball of radius
`10 size(□_𝒫(v))` around `v`. -/
theorem abs_correctorDiff_guardAnchor_le {ω : Configuration 2} (hω : ω ∈ G)
    (hP : PlanarPartitionEvent ω) {q : Fin 2 → ℝ} {v : Vertex 2}
    (hv : ω ∈ infiniteComponentEvent v) {Λ : Vertex 2 → ℝ} (hΛ0 : ∀ x, 0 ≤ Λ x)
    (hΛ : ∀ x, ω ∈ infiniteComponentEvent x → ∀ y, (openGraph ω).Adj x y →
      |correctorDiff hG hGv q ω x y| ≤ Λ x) :
    ENNReal.ofReal |correctorDiff hG hGv q ω v (guardAnchor ω v)| ≤
      ∑' x, ENNReal.ofReal (if ‖latticeEuclideanEmbedding (x - v)‖ ≤
        10 * TriadicCube.stoppingSize (planarGoodCubes ω) v then 4 * Λ x else 0) := by
  set Q := planarPartCube ω v
  set w : Vertex 2 → ℝ := fun x => if ω ∈ infiniteComponentEvent x then
    correctorDiff hG hGv q ω x v else 0
  have ha := infinite_planarCoarseAnchor hP v
  have h1 := abs_sub_coarseAnchor_le hP hv w
  have hwv : w v = 0 := by
    simp only [w, if_pos hv]
    obtain ⟨h, -⟩ := hGv hω
    exact correctorDiff_self hG hGv hω (uniqueInfiniteComponent_infinite h)
      ⟨v, (mem_uniqueInfiniteComponent_iff h v).2 hv⟩
  have hwa : w (planarCoarseAnchor ω v) = correctorDiff hG hGv q ω (planarCoarseAnchor ω v) v := by
    simp only [w, if_pos ha]
  rw [hwv, hwa, zero_sub, abs_neg, correctorDiff_swap' hG hGv hω hv ha, abs_neg] at h1
  have h2 := edgeVariationIn_correctorDiff_le hG hGv hω hv Q.ninefold.vertices hΛ0 hΛ
  have hsize : TriadicCube.stoppingSize (planarGoodCubes ω) v = (3 : ℝ) ^ Q.scale :=
    TriadicCube.stoppingSize_eq_of_mem (planarPartCube_spec hP v).1 (planarPartCube_spec hP v).2
  rw [guardAnchor_of_event hP, hsize]
  calc ENNReal.ofReal |correctorDiff hG hGv q ω v (planarCoarseAnchor ω v)|
      ≤ ENNReal.ofReal (∑ x ∈ Q.ninefold.vertices, 4 * Λ x) := by
        refine ENNReal.ofReal_le_ofReal (h1.trans (h2.trans_eq ?_))
        rw [Finset.mul_sum]
    _ = ∑ x ∈ Q.ninefold.vertices, ENNReal.ofReal (4 * Λ x) :=
        ENNReal.ofReal_sum_of_nonneg fun x _ => by have := hΛ0 x; positivity
    _ = ∑ x ∈ Q.ninefold.vertices, ENNReal.ofReal (if ‖latticeEuclideanEmbedding (x - v)‖ ≤
          10 * (3 : ℝ) ^ Q.scale then 4 * Λ x else 0) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [if_pos (norm_sub_le_of_mem_ninefold (planarPartCube_spec hP v).1 hx)]
    _ ≤ ∑' x, ENNReal.ofReal (if ‖latticeEuclideanEmbedding (x - v)‖ ≤
          10 * (3 : ℝ) ^ Q.scale then 4 * Λ x else 0) := ENNReal.sum_le_tsum _

end Carrier

/-! ### Moments -/

/-- The moments of `X + 2` for `X ≤ O_s(θ)`: `E[(X + 2)^{4q}] ≤ 3 (2 D q^{1/s})^{4q}` with
`D = θ (4/s)^{1/s} + 2`. -/
theorem lintegral_add_two_rpow_le {p : unitInterval} {X : Configuration 2 → ℝ} {s θ : ℝ}
    (hs : 0 < s) (hθ : 0 < θ) (hXm : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    (hXO : IsOsBond 2 p X s θ) {q : ℝ} (hq : 1 ≤ q) :
    ∫⁻ ω, ENNReal.ofReal ((X ω + 2) ^ (4 * q)) ∂latticeBondLaw 2 p ≤
      ENNReal.ofReal (3 * (2 * (θ * (4 / s) ^ (1 / s) + 2) * q ^ (1 / s)) ^ (4 * q)) := by
  have hq0 : 0 < q := by linarith
  have h4q : 0 < 4 * q := by linarith
  set D := θ * (4 / s) ^ (1 / s) + 2 with hD
  have hD2 : 2 ≤ D := by have : 0 ≤ θ * (4 / s) ^ (1 / s) := (by positivity); linarith
  have hq1s : 1 ≤ q ^ (1 / s) := Real.one_le_rpow hq (by positivity)
  obtain ⟨hint, hle⟩ := IsOsBond.integral_rpow_le hs hθ h4q hXm hX0 hXO
  -- pointwise
  have hpt : ∀ ω, (X ω + 2) ^ (4 * q) ≤ 2 ^ (4 * q) * (X ω ^ (4 * q) + 2 ^ (4 * q)) := by
    intro ω
    have hm : X ω + 2 ≤ 2 * max (X ω) 2 := by
      have := le_max_left (X ω) 2
      have := le_max_right (X ω) 2
      linarith
    calc (X ω + 2) ^ (4 * q) ≤ (2 * max (X ω) 2) ^ (4 * q) :=
          Real.rpow_le_rpow (by linarith [hX0 ω]) hm h4q.le
      _ = 2 ^ (4 * q) * max (X ω) 2 ^ (4 * q) :=
          Real.mul_rpow (by norm_num) (le_max_of_le_right (by norm_num))
      _ ≤ 2 ^ (4 * q) * (X ω ^ (4 * q) + 2 ^ (4 * q)) := by
          gcongr
          rcases le_total (X ω) 2 with h | h
          · rw [max_eq_right h]
            have := Real.rpow_nonneg (hX0 ω) (4 * q)
            linarith
          · rw [max_eq_left h]
            have : (0 : ℝ) ≤ 2 ^ (4 * q) := by positivity
            linarith
  have hint' : Integrable (fun ω => 2 ^ (4 * q) * (X ω ^ (4 * q) + 2 ^ (4 * q)))
      (latticeBondLaw 2 p) := (hint.add (integrable_const _)).const_mul _
  calc ∫⁻ ω, ENNReal.ofReal ((X ω + 2) ^ (4 * q)) ∂latticeBondLaw 2 p
      ≤ ∫⁻ ω, ENNReal.ofReal (2 ^ (4 * q) * (X ω ^ (4 * q) + 2 ^ (4 * q))) ∂latticeBondLaw 2 p :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal (∫ ω, 2 ^ (4 * q) * (X ω ^ (4 * q) + 2 ^ (4 * q)) ∂latticeBondLaw 2 p) :=
        (ofReal_integral_eq_lintegral_ofReal hint'
          (Eventually.of_forall fun ω => by have := Real.rpow_nonneg (hX0 ω) (4 * q); positivity)).symm
    _ ≤ ENNReal.ofReal (3 * (2 * D * q ^ (1 / s)) ^ (4 * q)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_const_mul, integral_add hint (integrable_const _), integral_const,
          probReal_univ, one_smul]
        have hX4 : ∫ ω, X ω ^ (4 * q) ∂latticeBondLaw 2 p ≤ 2 * (D * q ^ (1 / s)) ^ (4 * q) := by
          refine hle.trans ?_
          have he : Real.exp (-(4 * q / s)) ≤ 1 := Real.exp_le_one_iff.2 (by
            have := div_pos h4q hs; linarith)
          have hbase : θ ^ (4 * q) * (4 * q / s) ^ (4 * q / s) =
              (θ * (4 / s) ^ (1 / s) * q ^ (1 / s)) ^ (4 * q) := by
            rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hθ.le (by positivity),
              ← Real.rpow_mul (show (0 : ℝ) ≤ 4 / s by positivity), ← Real.rpow_mul hq0.le,
              mul_assoc, ← Real.mul_rpow (show (0 : ℝ) ≤ 4 / s by positivity) hq0.le]
            congr 2
            · ring
            · ring
          have hle2 : θ * (4 / s) ^ (1 / s) * q ^ (1 / s) ≤ D * q ^ (1 / s) := by
            have : 0 ≤ q ^ (1 / s) := by positivity
            nlinarith
          have h1 : (θ * (4 / s) ^ (1 / s) * q ^ (1 / s)) ^ (4 * q) ≤ (D * q ^ (1 / s)) ^ (4 * q) :=
            Real.rpow_le_rpow (by positivity) hle2 h4q.le
          have h0 : 0 ≤ θ ^ (4 * q) * (4 * q / s) ^ (4 * q / s) := by positivity
          calc 2 * θ ^ (4 * q) * ((4 * q / s) ^ (4 * q / s) * Real.exp (-(4 * q / s)))
              ≤ 2 * (θ ^ (4 * q) * (4 * q / s) ^ (4 * q / s)) := by nlinarith [Real.exp_pos (-(4 * q / s))]
            _ ≤ 2 * (D * q ^ (1 / s)) ^ (4 * q) := by rw [hbase]; linarith
        have h2 : (2 : ℝ) ^ (4 * q) ≤ (D * q ^ (1 / s)) ^ (4 * q) :=
          Real.rpow_le_rpow (by norm_num) (by nlinarith) h4q.le
        have he2 : (2 * D * q ^ (1 / s)) ^ (4 * q) = 2 ^ (4 * q) * (D * q ^ (1 / s)) ^ (4 * q) := by
          rw [mul_assoc, Real.mul_rpow (by norm_num) (by positivity)]
        rw [he2]
        have : (0 : ℝ) ≤ 2 ^ (4 * q) := by positivity
        nlinarith

/-- The tail of the radius `10 size(□_𝒫(v))` from the exponential moment of the size. -/
theorem measure_le_stoppingSize_le {p : unitInterval} {θ : ℝ} (hθ : 0 < θ) (v : Vertex 2)
    (hint : Integrable (fun ω => Real.exp (TriadicCube.stoppingSize (planarGoodCubes ω) v / θ))
      (latticeBondLaw 2 p))
    (hb : ∫ ω, Real.exp (TriadicCube.stoppingSize (planarGoodCubes ω) v / θ) ∂latticeBondLaw 2 p ≤ 2)
    (t : ℝ) :
    latticeBondLaw 2 p {ω | t ≤ 10 * TriadicCube.stoppingSize (planarGoodCubes ω) v} ≤
      ENNReal.ofReal (2 * Real.exp (-(t / (10 * θ)))) := by
  set f : Configuration 2 → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (Real.exp (TriadicCube.stoppingSize (planarGoodCubes ω) v / θ))
  have hsub : {ω | t ≤ 10 * TriadicCube.stoppingSize (planarGoodCubes ω) v} ⊆
      {ω | ENNReal.ofReal (Real.exp (t / (10 * θ))) ≤ f ω} := by
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

theorem measurable_stoppingSize_planar (v : Vertex 2) :
    Measurable fun ω => TriadicCube.stoppingSize (planarGoodCubes ω) v :=
  TriadicCube.measurable_stoppingSize (fun ω => planarGoodCubes ω)
    (fun T => TriadicCube.measurableSet_mem_goodOfWellConnected planarMeshedFamily
      measurableSet_mem_planarMeshedFamily T) v

/-- The sum of (5.10): four times the Lipschitz bounds `Λ x` over the ball of radius
`10 size(□_𝒫(v))` around `v`. -/
noncomputable def stepSixSum (Λ : Vertex 2 → Configuration 2 → ℝ) (v : Vertex 2)
    (ω : Configuration 2) : ℝ≥0∞ :=
  ∑' x, ENNReal.ofReal (if ‖latticeEuclideanEmbedding (x - v)‖ ≤
    10 * TriadicCube.stoppingSize (planarGoodCubes ω) v then 4 * Λ x ω else 0)

theorem measurable_stepSixSum {Λ : Vertex 2 → Configuration 2 → ℝ} (hΛ : ∀ x, Measurable (Λ x))
    (v : Vertex 2) : Measurable (stepSixSum Λ v) :=
  Measurable.tsum fun x => (Measurable.ite (measurableSet_le measurable_const
    ((measurable_stoppingSize_planar v).const_mul 10)) ((hΛ x).const_mul 4)
    measurable_const).ennreal_ofReal

/-- **The Lipschitz bounds and the moments of the sums of (5.10)**: bounds `Λ i x` for the corrector
increments of slope `e_i` along the open edges at `x`, and moments of order `q` of
`stepSixSum (Λ i) v` growing like `(A q^k)^q`, from the order-zero regularity input and the
exponential moments of the partition sizes. -/
theorem stepSix_data (hR3 : ArmstrongDarioOrderZeroTwo) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) :
    ∃ (Λ : Fin 2 → Vertex 2 → Configuration 2 → ℝ) (A k : ℝ), 0 < A ∧ 0 < k ∧
      (∀ i x, Measurable (Λ i x)) ∧ (∀ i x ω, 0 ≤ Λ i x ω) ∧
      (∀ i x, ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ infiniteComponentEvent x → ∀ y,
        (openGraph ω).Adj x y → |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ i x ω) ∧
      (∀ i v (q : ℝ), 1 ≤ q →
        ∫⁻ ω, stepSixSum (Λ i) v ω ^ q ∂latticeBondLaw 2 p ≤ ENNReal.ofReal ((A * q ^ k) ^ q)) := by
  obtain ⟨s, θ, L, hs, hθ, hL, X, hXm, hX0, hXO, hlip⟩ :=
    lipschitz_correctorDiff hG hGv hR3 hpc hp1 hGae
  obtain ⟨θ', hθ', hexp⟩ := (planar_meshed_partition_estimates hpc).2.1
  set D := θ * (4 / s) ^ (1 / s) + 2 with hD
  have hD2 : 2 ≤ D := by have : 0 ≤ θ * (4 / s) ^ (1 / s) := (by positivity); linarith
  set c : ℝ := 4 * L + 1 with hc
  have hc0 : 0 < c := by positivity
  set B₁ : ℝ := 4 * (1 + 8 * (10 * θ')) ^ 2 with hB₁
  have hB₁4 : 4 ≤ B₁ := by
    have : 1 ≤ (1 + 8 * (10 * θ')) ^ 2 := one_le_pow₀ (by linarith)
    linarith
  set k : ℝ := 2 + 2 / s with hk
  have hk0 : 0 < k := by positivity
  set A : ℝ := Real.sqrt 6 * (4 * B₁ * c * D ^ 2) with hA
  have hA0 : 0 < A := by positivity
  have hQ : ∀ i : Fin 2, ∑ j, |(Pi.single i (1 : ℝ) : Fin 2 → ℝ) j| = 1 := by
    intro i
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp
  set Λ : Fin 2 → Vertex 2 → Configuration 2 → ℝ := fun i x ω =>
    (L * max (X (configurationTranslation (-x) ω)) 2 ^ 2 + 1) *
      ∑ j, |(Pi.single i (1 : ℝ) : Fin 2 → ℝ) j| with hΛ
  have hΛ0 : ∀ i x ω, 0 ≤ Λ i x ω := fun i x ω => by simp only [hΛ, hQ]; positivity
  have hΛm : ∀ i x, Measurable (Λ i x) := fun i x =>
    ((((hXm.comp (measurable_configurationTranslation (-x))).max measurable_const).pow_const 2
      ).const_mul L |>.add_const 1).mul_const _
  refine ⟨Λ, A, k, hA0, hk0, hΛm, hΛ0, fun i x => hlip _ x, fun i v q' hq' => ?_⟩
  have hq'0 : 0 < q' := by linarith
  -- the moments of the summands
  have hYm : ∀ x, ∫⁻ ω, ENNReal.ofReal (4 * Λ i x ω) ^ (2 * q') ∂latticeBondLaw 2 p ≤
      ENNReal.ofReal ((Real.sqrt 3 * (4 * c * D ^ 2 * q' ^ (2 / s)) ^ q') ^ 2) := by
    intro x
    have hpt : ∀ ω, ENNReal.ofReal (4 * Λ i x ω) ^ (2 * q') ≤
        ENNReal.ofReal (c ^ (2 * q') * (X (configurationTranslation (-x) ω) + 2) ^ (4 * q')) := by
      intro ω
      rw [ENNReal.ofReal_rpow_of_nonneg (by have := hΛ0 i x ω; positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      set Y := X (configurationTranslation (-x) ω)
      have hY0 : 0 ≤ Y := hX0 _
      have h1 : 4 * Λ i x ω ≤ c * (Y + 2) ^ 2 := by
        simp only [hΛ, hQ, mul_one, hc]
        have hm : max Y 2 ^ 2 ≤ (Y + 2) ^ 2 := by
          have : max Y 2 ≤ Y + 2 := max_le (by linarith) (by linarith)
          exact pow_le_pow_left₀ (le_max_of_le_right (by norm_num)) this 2
        have h4 : 4 ≤ (Y + 2) ^ 2 := by nlinarith
        nlinarith
      calc (4 * Λ i x ω) ^ (2 * q') ≤ (c * (Y + 2) ^ 2) ^ (2 * q') :=
            Real.rpow_le_rpow (by have := hΛ0 i x ω; positivity) h1 (by positivity)
        _ = c ^ (2 * q') * (Y + 2) ^ (4 * q') := by
            rw [Real.mul_rpow hc0.le (by positivity), ← Real.rpow_natCast,
              ← Real.rpow_mul (by positivity)]
            congr 2
            push_cast
            ring
    calc ∫⁻ ω, ENNReal.ofReal (4 * Λ i x ω) ^ (2 * q') ∂latticeBondLaw 2 p
        ≤ ∫⁻ ω, ENNReal.ofReal (c ^ (2 * q') * (X (configurationTranslation (-x) ω) + 2) ^ (4 * q'))
            ∂latticeBondLaw 2 p := lintegral_mono hpt
      _ = ENNReal.ofReal (c ^ (2 * q')) * ∫⁻ ω, ENNReal.ofReal ((X ω + 2) ^ (4 * q'))
            ∂latticeBondLaw 2 p := by
          simp_rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ c ^ (2 * q') by positivity)]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          exact (measurePreserving_configurationTranslation p (-x)).lintegral_comp
            ((hXm.add_const 2).pow_const _).ennreal_ofReal
      _ ≤ ENNReal.ofReal (c ^ (2 * q')) *
            ENNReal.ofReal (3 * (2 * D * q' ^ (1 / s)) ^ (4 * q')) := by
          gcongr
          exact lintegral_add_two_rpow_le hs hθ hXm hX0 hXO hq'
      _ = ENNReal.ofReal ((Real.sqrt 3 * (4 * c * D ^ 2 * q' ^ (2 / s)) ^ q') ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [mul_pow, Real.sq_sqrt (by norm_num),
            ← Real.rpow_natCast ((4 * c * D ^ 2 * q' ^ (2 / s)) ^ q') 2,
            ← Real.rpow_mul (by positivity)]
          have e1 : (2 * D * q' ^ (1 / s)) ^ (4 * q') = (4 * D ^ 2 * q' ^ (2 / s)) ^ (2 * q') := by
            rw [show 4 * q' = 2 * (2 * q') by ring, Real.rpow_mul (by positivity)]
            congr 1
            rw [Real.rpow_two, mul_pow, mul_pow, ← Real.rpow_natCast (q' ^ (1 / s)) 2,
              ← Real.rpow_mul (by positivity)]
            push_cast
            ring_nf
          rw [e1, show q' * ((2 : ℕ) : ℝ) = 2 * q' by push_cast; ring,
            show 4 * c * D ^ 2 * q' ^ (2 / s) = c * (4 * D ^ 2 * q' ^ (2 / s)) by ring,
            Real.mul_rpow hc0.le (by positivity)]
          ring
  -- the random ball sum
  have hball := lintegral_randomBallSum_le (p := p) v (θ := 10 * θ') (by positivity)
    (fun t _ => measure_le_stoppingSize_le hθ' v (hexp v).1 (hexp v).2 t)
    ((measurable_stoppingSize_planar v).const_mul 10)
    (Y := fun x ω => ENNReal.ofReal (4 * Λ i x ω))
    (fun x => ((hΛm i x).const_mul 4).ennreal_ofReal) hq' (by positivity) hYm
  have hE : ∀ ω, stepSixSum (Λ i) v ω = ∑' x, if ‖latticeEuclideanEmbedding (x - v)‖ ≤
      10 * TriadicCube.stoppingSize (planarGoodCubes ω) v then
        ENNReal.ofReal (4 * Λ i x ω) else 0 := by
    intro ω
    unfold stepSixSum
    refine tsum_congr fun x => ?_
    split_ifs <;> simp
  simp only [hE]
  refine hball.trans (ENNReal.ofReal_le_ofReal ?_)
  -- the arithmetic of the constants
  set P := 4 * c * D ^ 2 * q' ^ (2 / s) with hP
  have hP0 : 0 < P := by positivity
  have hq2 : (1 : ℝ) ≤ q' ^ 2 := one_le_pow₀ hq'
  have hbase : 4 * (1 + 8 * q' * (10 * θ')) ^ 2 ≤ B₁ * q' ^ 2 := by
    rw [hB₁]
    have : 1 + 8 * q' * (10 * θ') ≤ q' * (1 + 8 * (10 * θ')) := by nlinarith
    have h0 : 0 ≤ 1 + 8 * q' * (10 * θ') := by positivity
    nlinarith [pow_le_pow_left₀ h0 this 2]
  have h1 : (4 * (1 + 8 * q' * (10 * θ')) ^ 2) ^ (q' - 1) ≤ (B₁ * q' ^ 2) ^ q' / B₁ := by
    calc (4 * (1 + 8 * q' * (10 * θ')) ^ 2) ^ (q' - 1) ≤ (B₁ * q' ^ 2) ^ (q' - 1) :=
          Real.rpow_le_rpow (by positivity) hbase (by linarith)
      _ = (B₁ * q' ^ 2) ^ q' / (B₁ * q' ^ 2) := by
          rw [Real.rpow_sub (by positivity), Real.rpow_one]
      _ ≤ (B₁ * q' ^ 2) ^ q' / B₁ := by
          gcongr
          nlinarith
  have hs6 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
    rw [← Real.sqrt_mul (by norm_num)]
    norm_num
  have h6 : Real.sqrt 6 ≤ Real.sqrt 6 ^ q' := by
    simpa using Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ Real.sqrt 6 by rw [Real.one_le_sqrt]; norm_num) hq'
  have hkq : (q' ^ 2) * q' ^ (2 / s) = q' ^ k := by
    rw [hk, Real.rpow_add hq'0, Real.rpow_two]
  calc (4 * (1 + 8 * q' * (10 * θ')) ^ 2) ^ (q' - 1) *
        (Real.sqrt 2 * 4 * (1 + 8 * (10 * θ')) ^ 2 * (Real.sqrt 3 * P ^ q'))
      ≤ (B₁ * q' ^ 2) ^ q' / B₁ * (Real.sqrt 2 * B₁ * (Real.sqrt 3 * P ^ q')) := by
        have e : Real.sqrt 2 * 4 * (1 + 8 * (10 * θ')) ^ 2 = Real.sqrt 2 * B₁ := by rw [hB₁]; ring
        rw [e]
        gcongr
    _ = Real.sqrt 6 * ((B₁ * q' ^ 2) ^ q' * P ^ q') := by
        have hB₁ne : B₁ ≠ 0 := (by linarith : (0 : ℝ) < B₁).ne'
        rw [← hs6, div_mul_eq_mul_div, div_eq_iff hB₁ne]
        ring
    _ ≤ Real.sqrt 6 ^ q' * ((B₁ * q' ^ 2) ^ q' * P ^ q') := by
        gcongr
    _ = (A * q' ^ k) ^ q' := by
        rw [← Real.mul_rpow (by positivity) (by positivity),
          ← Real.mul_rpow (by positivity) (by positivity), hA, hP, ← hkq]
        congr 1
        ring

/-- **The coarsening error (5.10) at every vertex**, from the order-zero regularity input and the
exponential moments of the partition sizes. -/
theorem baseCoarseningError (hR3 : ArmstrongDarioOrderZeroTwo) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) :
    ∃ s₆ C₆ : ℝ, 0 < s₆ ∧ 0 < C₆ ∧ BaseCoarseningError hG hGv p s₆ C₆ := by
  obtain ⟨Λ, A, k, hA0, hk0, hΛm, hΛ0, hlip, hmom6⟩ := stepSix_data hG hGv hR3 hpc hp1 hGae
  set s₆ : ℝ := 1 / (2 * k) with hs₆
  have hs₆0 : 0 < s₆ := by positivity
  have hs₆k : s₆ * k < 1 := by rw [hs₆]; field_simp; linarith
  obtain ⟨C₆, hC₆, hmom⟩ := isOsBond_of_moment_le (d := 2) (p := p) hA0 hs₆0 hs₆k
  refine ⟨s₆, C₆, hs₆0, hC₆, fun i v => ?_⟩
  have hE₆m := measurable_stepSixSum (hΛm i) v
  have hfin : ∀ᵐ ω ∂latticeBondLaw 2 p, stepSixSum (Λ i) v ω < ⊤ := by
    refine ae_lt_top hE₆m ?_
    have := hmom6 i v 1 le_rfl
    simp only [ENNReal.rpow_one] at this
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top this
  refine ⟨fun ω => (stepSixSum (Λ i) v ω).toReal, hE₆m.ennreal_toReal, ?_, ?_⟩
  · refine hmom _ hE₆m.ennreal_toReal (fun ω => ENNReal.toReal_nonneg) fun q' hq' => ?_
    have hq'0 : 0 < q' := by linarith
    have hmq : Measurable fun ω => (stepSixSum (Λ i) v ω).toReal ^ q' :=
      hE₆m.ennreal_toReal.pow_const q'
    have hnn : 0 ≤ᵐ[latticeBondLaw 2 p] fun ω => (stepSixSum (Λ i) v ω).toReal ^ q' :=
      Eventually.of_forall fun ω => by positivity
    have hlin : ∫⁻ ω, ENNReal.ofReal ((stepSixSum (Λ i) v ω).toReal ^ q') ∂latticeBondLaw 2 p ≤
        ENNReal.ofReal ((A * q' ^ k) ^ q') := by
      refine (lintegral_mono fun ω => ?_).trans (hmom6 i v q' hq')
      rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hq'0.le]
      exact ENNReal.rpow_le_rpow ENNReal.ofReal_toReal_le hq'0.le
    refine ⟨⟨hmq.aestronglyMeasurable, ?_⟩, ?_⟩
    · rw [hasFiniteIntegral_iff_ofReal hnn]
      exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
    · rw [integral_eq_lintegral_of_nonneg_ae hnn hmq.aestronglyMeasurable]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlin
  · have hall : ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ x, ω ∈ infiniteComponentEvent x →
        ∀ y, (openGraph ω).Adj x y →
          |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ i x ω :=
      ae_all_iff.2 fun x => hlip i x
    filter_upwards [hGae, ae_planarPartitionEvent hpc, hall, hfin] with ω hω hP hl hf hv
    have h := abs_correctorDiff_guardAnchor_le hG hGv hω hP hv (Λ := fun x => Λ i x ω)
      (fun x => hΛ0 i x ω) hl
    exact (ENNReal.ofReal_le_iff_le_toReal hf.ne).1 h

end Base

end Rigidity.Corrector
