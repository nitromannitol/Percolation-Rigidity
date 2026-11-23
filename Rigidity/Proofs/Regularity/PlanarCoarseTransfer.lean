import Rigidity.Proofs.Regularity.PlanarCoarseCells
import Rigidity.Proofs.Regularity.OrderOneOrigin

/-!
# Passing between a cluster function and its coarsening on the balls of `ℤ²`

The steps of the proof of Lemma 7.3 of Armstrong and Dario (arXiv:1609.09431v2) which compare a
function `u` on a planar open cluster `C` with its coarsening `[u]_𝒫` (`coarseAtAnchor C u`, the
value at the anchor of the partition cube), in the normalizations `r^{-1} ‖·‖_{ℓ²(C ∩ B_r)}`
(`clusterBallVolumeL2`) on `C` and `‖·‖_{L̲²(B_r)}` (`componentBallL2` of `latticeComponent 2`) on
the lattice:

* the lattice balls have at least `ρ²` points (`le_card_latticeBall'`), and the cluster ball of
  radius `r ≥ 3` carries at most `9` times the normalized norm of the lattice ball
  (`clusterBallVolumeL2_le_three_mul`);
* if the anchors of the points of `B_ρ` lie in `C ∩ B_R` and the partition cubes there have at most
  `S²` points, `‖[u]_𝒫 - a‖_{L̲²(B_ρ)} ≤ (S R / ρ) R^{-1} ‖u - a‖_{ℓ²(C ∩ B_R)}`
  (`componentBallL2_coarse_sub_const_le`, the crude bound of the top coarse oscillations);
* if moreover `|W(y) - W(x)| ≤ Λ (|y₀ - x₀| + |y₁ - x₁|)`,
  `∑_{B_ρ} |[u]_𝒫 - W| ≤ (∑_{B_ρ} 9^{s})^{1/2} R · R^{-1} ‖u - W‖_{ℓ²(C ∩ B_R)} +
  2 Λ ∑_{B_ρ} 3^{s}` (`sum_abs_coarse_sub_le`, the `ℓ¹` step of Step 2 of the proof, by
  Cauchy–Schwarz over the fibres of the anchor map), `s` the scales of the partition cubes.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.External

variable {ω : Configuration 2}

/-- The points of `ℤ²` in the lattice ball. -/
noncomputable def latticeBallPoints (z : Vertex 2) (ρ : ℝ) : Finset (Vertex 2) :=
  (componentEuclideanBall (latticeComponent 2) z ρ).image Subtype.val

theorem mem_latticeBallPoints {z y : Vertex 2} {ρ : ℝ} :
    y ∈ latticeBallPoints z ρ ↔
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding z) < ρ := by
  rw [latticeBallPoints, mem_image_componentEuclideanBall]
  exact ⟨fun h => h.2, fun h => ⟨mem_latticeComponent_supp y, h⟩⟩

theorem sum_latticeBallPoints (z : Vertex 2) (ρ : ℝ) (f : Vertex 2 → ℝ) :
    ∑ x ∈ componentEuclideanBall (latticeComponent 2) z ρ, f x.val =
      ∑ y ∈ latticeBallPoints z ρ, f y :=
  (sum_image (f := f) fun _ _ _ _ h => Subtype.val_injective h).symm

theorem card_latticeBallPoints (z : Vertex 2) (ρ : ℝ) :
    (latticeBallPoints z ρ).card = (componentEuclideanBall (latticeComponent 2) z ρ).card :=
  card_image_of_injective _ Subtype.val_injective

/-- A sum over a finite set of points of a cluster inside a ball is at most the sum over the
cluster ball. -/
theorem sum_le_sum_componentEuclideanBall (C : OpenComponent ω) {S : Finset (Vertex 2)}
    {R : ℝ} (hS : ∀ y ∈ S, y ∈ C.supp ∧
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex 2)) < R)
    (f : Vertex 2 → ℝ) (hf : ∀ y, 0 ≤ f y) :
    ∑ y ∈ S, f y ≤ ∑ x ∈ componentEuclideanBall C 0 R, f x.val := by
  classical
  rw [← sum_image (f := f) (s := componentEuclideanBall C 0 R)
    fun _ _ _ _ h => Subtype.val_injective h]
  exact sum_le_sum_of_subset_of_nonneg (fun y hy => (mem_image_componentEuclideanBall C 0 y R).2
    (hS y hy)) fun y _ _ => hf y

/-- **A lattice ball of radius `ρ ≥ 3` has at least `ρ²` points.** -/
theorem le_card_latticeBall' (z : Vertex 2) {ρ : ℝ} (hρ : 3 ≤ ρ) :
    ρ ^ 2 ≤ ((componentEuclideanBall (latticeComponent 2) z ρ).card : ℝ) := by
  classical
  set L := ⌊7 * ρ / 10⌋₊ with hL
  have hL1 : 7 * ρ / 10 - 1 < L := Nat.sub_one_lt_floor (7 * ρ / 10)
  have hLle : (L : ℝ) ≤ 7 * ρ / 10 := Nat.floor_le (by positivity)
  have hsub : supBox z L ⊆ latticeBallPoints z ρ := by
    intro y hy
    rw [mem_latticeBallPoints]
    refine (dist_le_of_mem_supBox hy).trans_lt ?_
    have hs : Real.sqrt ((2 : ℕ) : ℝ) < 142 / 100 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have h0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    calc Real.sqrt ((2 : ℕ) : ℝ) * L ≤ 142 / 100 * (7 * ρ / 10) :=
          mul_le_mul hs.le hLle h0 (by norm_num)
      _ < ρ := by linarith
  have hcard : (supBox z L).card = (2 * L + 1) ^ 2 := by
    rw [supBox, Fintype.card_piFinset]
    simp only [Int.card_Icc]
    have : ∀ i : Fin 2, (z i + (L : ℤ) + 1 - (z i - L)).toNat = 2 * L + 1 := fun i => by omega
    simp [this]
  have h := card_le_card hsub
  rw [hcard, card_latticeBallPoints] at h
  have h' : ((2 * L + 1 : ℕ) : ℝ) ^ 2 ≤ ((componentEuclideanBall (latticeComponent 2) z ρ).card : ℝ) := by
    exact_mod_cast h
  have h2 : ρ ≤ ((2 * L + 1 : ℕ) : ℝ) := by push_cast; linarith
  exact (pow_le_pow_left₀ (by linarith) h2 2).trans h'

/-- **The cluster ball against the lattice ball**: for `r ≥ 3`,
`r^{-1} ‖F‖_{ℓ²(C ∩ B_r)} ≤ 3 ‖F‖_{L̲²(B_r)}`. -/
theorem clusterBallVolumeL2_le_three_mul (C : OpenComponent ω) {r : ℝ} (hr : 3 ≤ r)
    (F : Vertex 2 → ℝ) :
    clusterBallVolumeL2 C r (fun x => F x.val) ≤
      3 * componentBallL2 (latticeComponent 2) 0 r (fun x => F x.val) := by
  classical
  have hr0 : 0 < r := by linarith
  have hsum : ∑ x ∈ componentEuclideanBall C 0 r, F x.val ^ 2 ≤
      ∑ x ∈ componentEuclideanBall (latticeComponent 2) 0 r, F x.val ^ 2 := by
    rw [sum_latticeBallPoints 0 r (fun y => F y ^ 2)]
    rw [← sum_image (f := fun y => F y ^ 2) (s := componentEuclideanBall C 0 r)
      fun _ _ _ _ h => Subtype.val_injective h]
    refine sum_le_sum_of_subset_of_nonneg (fun y hy => ?_) fun _ _ _ => sq_nonneg _
    rw [mem_image_componentEuclideanBall] at hy
    exact mem_latticeBallPoints.2 hy.2
  have hcard : ((componentEuclideanBall (latticeComponent 2) 0 r).card : ℝ) ≤ 9 * r ^ 2 := by
    have := card_componentEuclideanBall_le (latticeComponent 2) 0 hr0.le
    calc _ ≤ (2 * r + 3) ^ 2 := this
      _ ≤ 9 * r ^ 2 := by nlinarith
  have hsq := sum_sq_eq_card_mul_componentBallL2_sq (latticeComponent 2) 0 r (fun x => F x.val)
  rw [clusterBallVolumeL2]
  have hK : 0 ≤ 3 * componentBallL2 (latticeComponent 2) 0 r (fun x => F x.val) :=
    mul_nonneg (by norm_num) (componentBallL2_nonneg _ _ _ _)
  rw [Real.sqrt_le_left hK, div_le_iff₀ (by positivity)]
  have hN0 := sq_nonneg (componentBallL2 (latticeComponent 2) 0 r (fun x => F x.val))
  calc ∑ x ∈ componentEuclideanBall C 0 r, F x.val ^ 2
      ≤ ((componentEuclideanBall (latticeComponent 2) 0 r).card : ℝ) *
          componentBallL2 (latticeComponent 2) 0 r (fun x => F x.val) ^ 2 := hsum.trans hsq.le
    _ ≤ 9 * r ^ 2 * componentBallL2 (latticeComponent 2) 0 r (fun x => F x.val) ^ 2 :=
        mul_le_mul_of_nonneg_right hcard hN0
    _ = (3 * componentBallL2 (latticeComponent 2) 0 r (fun x => F x.val)) ^ 2 * r ^ 2 := by
        ring

/-- The cluster function as a function on `ℤ²`, `0` off the cluster. -/
theorem extend_val' (C : OpenComponent ω) (f : C → ℝ) (x : C) :
    Rigidity.Section3.extend C f x.val = f x := by
  rw [Rigidity.Section3.extend]
  exact dif_pos (show x.val ∈ C.supp from x.2)

/-- **Crude bound for the coarse oscillation.** -/
theorem componentBallL2_coarse_sub_const_le (hP : PlanarPartitionEvent ω)
    (h : HasUniqueInfiniteOpenComponent ω) (u : uniqueInfiniteComponent h → ℝ) {ρ R S : ℝ}
    (hρ : 3 ≤ ρ) (hS : 0 ≤ S)
    (hanchor : ∀ y ∈ latticeBallPoints 0 ρ,
      dist (latticeEuclideanEmbedding (planarCoarseAnchor ω y))
        (latticeEuclideanEmbedding (0 : Vertex 2)) < R)
    (hsize : ∀ y ∈ latticeBallPoints 0 ρ, ((3 : ℝ) ^ (planarPartCube ω y).scale) ^ 2 ≤ S ^ 2)
    (a : ℝ) :
    componentBallL2 (latticeComponent 2) 0 ρ
        (fun x => coarseAtAnchor (uniqueInfiniteComponent h) u x.val - a) ≤
      S * R / ρ * clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - fun _ => a) := by
  classical
  have hρ0 : 0 < ρ := by linarith
  set f : Vertex 2 → ℝ := fun y => Rigidity.Section3.extend (uniqueInfiniteComponent h) u y - a with hf
  have hcoarse : ∀ y, coarseAtAnchor (uniqueInfiniteComponent h) u y - a = f (planarCoarseAnchor ω y) := fun y => rfl
  have hsum1 : ∑ x ∈ componentEuclideanBall (latticeComponent 2) 0 ρ,
      (coarseAtAnchor (uniqueInfiniteComponent h) u x.val - a) ^ 2 =
      ∑ y ∈ latticeBallPoints 0 ρ, f (planarCoarseAnchor ω y) ^ 2 := by
    rw [sum_latticeBallPoints 0 ρ (fun y => (coarseAtAnchor (uniqueInfiniteComponent h) u y - a) ^ 2)]
    exact sum_congr rfl fun y _ => by rw [hcoarse]
  have hfib := sum_sq_comp_le (latticeBallPoints 0 ρ) (planarCoarseAnchor ω) (W₀ := S ^ 2) f
    fun y hy => (card_filter_anchor_eq_le hP _ y).trans (hsize y hy)
  have himage : ∑ y ∈ (latticeBallPoints 0 ρ).image (planarCoarseAnchor ω), f y ^ 2 ≤
      ∑ x ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 R, f x.val ^ 2 := by
    refine sum_le_sum_componentEuclideanBall (uniqueInfiniteComponent h) (fun y hy => ?_) _ fun _ => sq_nonneg _
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
    exact ⟨planarCoarseAnchor_mem_uniqueInfiniteComponent hP h x, hanchor x hx⟩
  have hcl : ∑ x ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 R, f x.val ^ 2 =
      R ^ 2 * clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - fun _ => a) ^ 2 := by
    rcases le_or_gt R 0 with hR | hR
    · rw [componentEuclideanBall_eq_empty (uniqueInfiniteComponent h) 0 hR]; simp [clusterBallVolumeL2,
        componentEuclideanBall_eq_empty (uniqueInfiniteComponent h) 0 hR]
    · rw [clusterBallVolumeL2, Real.sq_sqrt (div_nonneg (sum_nonneg fun _ _ => sq_nonneg _)
        (by positivity))]
      have e : ∀ x : (uniqueInfiniteComponent h),
          f x.val ^ 2 = ((u - fun _ => a : uniqueInfiniteComponent h → ℝ) x) ^ 2 := fun x => by
        simp only [hf, extend_val', Pi.sub_apply]
      rw [sum_congr rfl fun x _ => e x]
      field_simp
  have hcard := le_card_latticeBall' 0 hρ
  have hK : 0 ≤ S * R / ρ * clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - fun _ => a) := by
    rcases le_or_gt R 0 with hR | hR
    · have : clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - fun _ => a) = 0 := by
        simp [clusterBallVolumeL2, componentEuclideanBall_eq_empty (uniqueInfiniteComponent h) 0 hR]
      rw [this, mul_zero]
    · exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hcpos : (0 : ℝ) < ((componentEuclideanBall (latticeComponent 2) 0 ρ).card : ℝ) := by
    nlinarith [hcard, hρ]
  rw [componentBallL2, Real.sqrt_le_left hK, div_le_iff₀ hcpos, hsum1]
  calc ∑ y ∈ latticeBallPoints 0 ρ, f (planarCoarseAnchor ω y) ^ 2
      ≤ S ^ 2 * ∑ y ∈ (latticeBallPoints 0 ρ).image (planarCoarseAnchor ω), f y ^ 2 := hfib
    _ ≤ S ^ 2 * (R ^ 2 * clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - fun _ => a) ^ 2) :=
        mul_le_mul_of_nonneg_left (himage.trans hcl.le) (sq_nonneg S)
    _ = (S * R / ρ * clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - fun _ => a)) ^ 2 * ρ ^ 2 := by
        field_simp
    _ ≤ (S * R / ρ * clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - fun _ => a)) ^ 2 *
          ((componentEuclideanBall (latticeComponent 2) 0 ρ).card : ℝ) :=
        mul_le_mul_of_nonneg_left hcard (sq_nonneg _)

/-- **The `ℓ¹` step**: Cauchy–Schwarz over the fibres of the anchor map and the Lipschitz bound
of `W`. -/
theorem sum_abs_coarse_sub_le (hP : PlanarPartitionEvent ω)
    (h : HasUniqueInfiniteOpenComponent ω) (u : uniqueInfiniteComponent h → ℝ)
    (W : Vertex 2 → ℝ) {ρ R Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hanchor : ∀ y ∈ latticeBallPoints 0 ρ,
      dist (latticeEuclideanEmbedding (planarCoarseAnchor ω y))
        (latticeEuclideanEmbedding (0 : Vertex 2)) < R)
    (hLip : ∀ y ∈ latticeBallPoints 0 ρ, |W (planarCoarseAnchor ω y) - W y| ≤
      Λ * (|((planarCoarseAnchor ω y 0 - y 0 : ℤ) : ℝ)| +
        |((planarCoarseAnchor ω y 1 - y 1 : ℤ) : ℝ)|)) :
    ∑ y ∈ latticeBallPoints 0 ρ, |coarseAtAnchor (uniqueInfiniteComponent h) u y - W y| ≤
      Real.sqrt (∑ y ∈ latticeBallPoints 0 ρ, ((3 : ℝ) ^ (planarPartCube ω y).scale) ^ 2) *
          Real.sqrt (∑ x ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 R,
            (u x - W x.val) ^ 2) +
        2 * Λ * ∑ y ∈ latticeBallPoints 0 ρ, (3 : ℝ) ^ (planarPartCube ω y).scale := by
  classical
  set f : Vertex 2 → ℝ := fun y => Rigidity.Section3.extend (uniqueInfiniteComponent h) u y - W y with hf
  have hsplit : ∀ y, |coarseAtAnchor (uniqueInfiniteComponent h) u y - W y| ≤
      |f (planarCoarseAnchor ω y)| + |W (planarCoarseAnchor ω y) - W y| := fun y => by
    have e : coarseAtAnchor (uniqueInfiniteComponent h) u y - W y =
        f (planarCoarseAnchor ω y) + (W (planarCoarseAnchor ω y) - W y) := by
      simp only [hf, coarseAtAnchor]; ring
    rw [e]; exact abs_add_le _ _
  have h1 := sq_sum_abs_comp_le (latticeBallPoints 0 ρ) (planarCoarseAnchor ω)
    (fun y => ((3 : ℝ) ^ (planarPartCube ω y).scale) ^ 2) f
    fun y _ => card_filter_anchor_eq_le hP _ y
  have himage : ∑ y ∈ (latticeBallPoints 0 ρ).image (planarCoarseAnchor ω), f y ^ 2 ≤
      ∑ x ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 R, (u x - W x.val) ^ 2 := by
    have := sum_le_sum_componentEuclideanBall (uniqueInfiniteComponent h) (S := (latticeBallPoints 0 ρ).image
      (planarCoarseAnchor ω)) (R := R) (fun y hy => by
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
        exact ⟨planarCoarseAnchor_mem_uniqueInfiniteComponent hP h x, hanchor x hx⟩)
      (fun y => f y ^ 2) fun _ => sq_nonneg _
    refine this.trans (le_of_eq (sum_congr rfl fun x _ => ?_))
    simp only [hf, extend_val']
  have hA0 : 0 ≤ ∑ y ∈ latticeBallPoints 0 ρ, ((3 : ℝ) ^ (planarPartCube ω y).scale) ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hfirst : ∑ y ∈ latticeBallPoints 0 ρ, |f (planarCoarseAnchor ω y)| ≤
      Real.sqrt (∑ y ∈ latticeBallPoints 0 ρ, ((3 : ℝ) ^ (planarPartCube ω y).scale) ^ 2) *
        Real.sqrt (∑ x ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 R, (u x - W x.val) ^ 2) := by
    rw [← Real.sqrt_mul hA0]
    apply Real.le_sqrt_of_sq_le
    exact h1.trans (mul_le_mul_of_nonneg_left himage hA0)
  have hsecond : ∑ y ∈ latticeBallPoints 0 ρ, |W (planarCoarseAnchor ω y) - W y| ≤
      2 * Λ * ∑ y ∈ latticeBallPoints 0 ρ, (3 : ℝ) ^ (planarPartCube ω y).scale := by
    rw [mul_sum]
    refine sum_le_sum fun y hy => (hLip y hy).trans ?_
    have hside : ∀ i, |((planarCoarseAnchor ω y i - y i : ℤ) : ℝ)| ≤
        (3 : ℝ) ^ (planarPartCube ω y).scale := fun i => by
      have h := (abs_coarseAnchor_sub_lt hP y i).le
      have e : ((planarPartCube ω y).side : ℝ) = (3 : ℝ) ^ (planarPartCube ω y).scale := by
        simp [TriadicCube.side]
      rw [← e]; exact_mod_cast h
    have := add_le_add (hside 0) (hside 1)
    nlinarith
  calc ∑ y ∈ latticeBallPoints 0 ρ, |coarseAtAnchor (uniqueInfiniteComponent h) u y - W y|
      ≤ ∑ y ∈ latticeBallPoints 0 ρ,
          (|f (planarCoarseAnchor ω y)| + |W (planarCoarseAnchor ω y) - W y|) :=
        sum_le_sum fun y _ => hsplit y
    _ = ∑ y ∈ latticeBallPoints 0 ρ, |f (planarCoarseAnchor ω y)| +
          ∑ y ∈ latticeBallPoints 0 ρ, |W (planarCoarseAnchor ω y) - W y| := sum_add_distrib
    _ ≤ _ := add_le_add hfirst hsecond

end Rigidity.Proofs.Regularity
