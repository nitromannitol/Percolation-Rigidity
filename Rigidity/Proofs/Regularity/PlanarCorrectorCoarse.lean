import Rigidity.Proofs.Regularity.PlanarCorrectorGradient
import Rigidity.Proofs.Regularity.PlanarHarmonicComparison

/-!
# The uniform norm of a function on the planar cluster from its `L²` norm and its gradient

Armstrong and Dario (arXiv:1609.09431v2), Remark after (1.19): the interpolation inequality
between `L²` and `C^{0,1}` on `ℤ² ∩ B_r`, applied to the coarsened function `[w]_𝒫`, and the
comparison of `w` with `[w]_𝒫` (Lemma 3.2), give the uniform bound of `w` on `𝒞_∞ ∩ B_r`.

* `edgeVariationIn_le`: the variation of `w` on the open edges of a set `S` is at most
  `|S|² L` when the increments of `w` along these edges are at most `L`.
* `sum_coarseAnchor_le_of_subset`: the sum of a nonnegative function at the anchors of the
  partition cubes of a set `T` counts each anchor at most `size(□)² ≤ δ²` times.
* `sq_le_of_box`: the interpolation inequality in the form
  `|g(x)|² ≤ 2 (t+1)^{-2} Σ_{x + [0,t]²} g² + 8 t² L²` for `g` with increments at most `L` on the
  box `x + [0,t]²`.
* `abs_le_of_coarse`: `|w(x)| ≤ |S_x|² L + |[w]_𝒫(x)|` at a vertex `x` of an infinite cluster,
  with `S_x` the ninefold of the partition cube of `x`.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.Percolation
open scoped Classical

variable {ω : Configuration 2}

/-- The variation of `w` on the open edges of `S` against the largest increment. -/
theorem edgeVariationIn_le (S : Finset (Vertex 2)) (w : Vertex 2 → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ x ∈ S, ∀ y ∈ S, (openGraph ω).Adj x y → |w x - w y| ≤ L) :
    edgeVariationIn ω S w ≤ (S.card : ℝ) ^ 2 * L := by
  unfold edgeVariationIn
  calc ∑ x ∈ S, ∑ y ∈ S, (if (openGraph ω).Adj x y then |w x - w y| else 0)
      ≤ ∑ _x ∈ S, ∑ _y ∈ S, L := Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => by
        split_ifs with hxy
        · exact h x hx y hy hxy
        · exact hL
    _ = (S.card : ℝ) ^ 2 * L := by
        rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]; ring

theorem card_ninefold_vertices (Q : TriadicCube 2) :
    (Q.ninefold.vertices.card : ℝ) = 81 * ((3 : ℝ) ^ Q.scale) ^ 2 := by
  rw [IntegerCube.card_vertices_eq]
  change (((9 * 3 ^ Q.scale : ℕ) ^ 2 : ℕ) : ℝ) = _
  push_cast
  ring

/-- **The anchors of a set**: the sum of a nonnegative function at the anchors of the partition
cubes of the vertices of `T` is at most `δ²` times its sum over any set containing these anchors. -/
theorem sum_coarseAnchor_le_of_subset (hP : PlanarPartitionEvent ω) (T T' : Finset (Vertex 2))
    (hsub : ∀ y ∈ T, planarCoarseAnchor ω y ∈ T') {φ : Vertex 2 → ℝ} (hφ : ∀ z, 0 ≤ φ z)
    {δ : ℝ} (hδ : ∀ y ∈ T, (3 : ℝ) ^ (planarPartCube ω y).scale ≤ δ) :
    ∑ y ∈ T, φ (planarCoarseAnchor ω y) ≤ δ ^ 2 * ∑ z ∈ T', φ z := by
  have himg : T.image (planarCoarseAnchor ω) ⊆ T' := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    exact hsub y hy
  rw [Finset.sum_comp]
  have hcount : ∀ z ∈ T.image (planarCoarseAnchor ω),
      ((T.filter fun y => planarCoarseAnchor ω y = z).card : ℝ) ≤ δ ^ 2 := by
    intro z hz
    obtain ⟨y₀, hy₀, hy₀z⟩ := Finset.mem_image.1 hz
    have hzQ0 : z ∈ (planarPartCube ω y₀).vertices := by
      rw [← hy₀z]
      exact ((planarPartCube ω y₀).planarAnchor_spec (planarPartCube_meshed hP y₀).1
        (planarPartCube_large hP y₀)).1
    have hQz : planarPartCube ω z = planarPartCube ω y₀ := planarPartCube_eq_of_mem hP hzQ0
    have hle : (T.filter fun y => planarCoarseAnchor ω y = z) ⊆
        (planarPartCube ω z).toIntegerCube.vertices := by
      intro y hy
      obtain ⟨-, hyz⟩ := Finset.mem_filter.1 hy
      have hzQ : z ∈ (planarPartCube ω y).vertices := by
        rw [← hyz]
        exact ((planarPartCube ω y).planarAnchor_spec (planarPartCube_meshed hP y).1
          (planarPartCube_large hP y)).1
      rw [TriadicCube.mem_toIntegerCube_vertices, planarPartCube_eq_of_mem hP hzQ]
      exact (planarPartCube_spec hP y).1
    have hcard := Finset.card_le_card hle
    rw [IntegerCube.card_vertices_eq] at hcard
    have h1 : ((T.filter fun y => planarCoarseAnchor ω y = z).card : ℝ) ≤
        (((planarPartCube ω z).toIntegerCube.size ^ 2 : ℕ) : ℝ) := by exact_mod_cast hcard
    have h2 : (((planarPartCube ω z).toIntegerCube.size ^ 2 : ℕ) : ℝ) =
        ((3 : ℝ) ^ (planarPartCube ω z).scale) ^ 2 := by
      change (((3 ^ (planarPartCube ω z).scale : ℕ) ^ 2 : ℕ) : ℝ) = _
      push_cast; rfl
    rw [h2, hQz] at h1
    exact h1.trans (pow_le_pow_left₀ (by positivity) (hδ y₀ hy₀) 2)
  calc ∑ z ∈ T.image (planarCoarseAnchor ω),
        (T.filter fun y => planarCoarseAnchor ω y = z).card • φ z
      ≤ ∑ z ∈ T.image (planarCoarseAnchor ω), δ ^ 2 * φ z :=
        Finset.sum_le_sum fun z hz => by
          rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (hcount z hz) (hφ z)
    _ = δ ^ 2 * ∑ z ∈ T.image (planarCoarseAnchor ω), φ z := (Finset.mul_sum _ _ _).symm
    _ ≤ δ ^ 2 * ∑ z ∈ T', φ z :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg himg fun z _ _ => hφ z) (sq_nonneg _)

/-- The box `x + [0, t]²`. -/
noncomputable def cornerBox (x : Vertex 2) (t : ℕ) : Finset (Vertex 2) :=
  Fintype.piFinset fun i => Finset.Icc (x i) (x i + t)

theorem mem_cornerBox {x y : Vertex 2} {t : ℕ} :
    y ∈ cornerBox x t ↔ ∀ i, x i ≤ y i ∧ y i ≤ x i + t := by
  simp only [cornerBox, Fintype.mem_piFinset, Finset.mem_Icc]

theorem card_cornerBox (x : Vertex 2) (t : ℕ) : ((cornerBox x t).card : ℝ) = ((t : ℝ) + 1) ^ 2 := by
  have h : ∀ i : Fin 2, (Finset.Icc (x i) (x i + t)).card = t + 1 := fun i => by
    rw [Int.card_Icc]; omega
  rw [cornerBox, Fintype.card_piFinset, Fin.prod_univ_two, h 0, h 1]
  push_cast
  ring

/-- **The interpolation inequality on a box**: if the increments of `g` on `x + [0, t]²` are at most
`L`, then `|g(x)|² ≤ 2 (t+1)^{-2} Σ_{x + [0,t]²} g² + 8 t² L²`. -/
theorem sq_le_of_box (g : Vertex 2 → ℝ) (x : Vertex 2) (t : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ p ∈ cornerBox x t, ∀ l, |g (p + unit l) - g p| ≤ L) :
    g x ^ 2 ≤ 2 / ((t : ℝ) + 1) ^ 2 * ∑ y ∈ cornerBox x t, g y ^ 2 + 8 * (t : ℝ) ^ 2 * L ^ 2 := by
  have hpt : ∀ y ∈ cornerBox x t, g x ^ 2 ≤ 2 * g y ^ 2 + 8 * (t : ℝ) ^ 2 * L ^ 2 := by
    intro y hy
    have hy' := mem_cornerBox.1 hy
    have hb := abs_sub_le_of_grad_le g y x (G := L) fun p hp l => by
      refine h p (mem_cornerBox.2 fun i => ?_) l
      have h1 := hp i
      have h2 := hy' i
      rw [min_eq_right h2.1, max_eq_left h2.1] at h1
      constructor <;> omega
    have hlen : (((|x 0 - y 0| + |x 1 - y 1|) : ℤ) : ℝ) ≤ 2 * t := by
      have h0 := hy' 0
      have h1 := hy' 1
      have : (|x 0 - y 0| + |x 1 - y 1| : ℤ) ≤ 2 * t := by
        rw [abs_sub_comm, abs_of_nonneg (by omega), abs_sub_comm, abs_of_nonneg (by omega)]
        omega
      exact_mod_cast this
    have hb2 : |g x - g y| ≤ 2 * t * L :=
      hb.trans (mul_le_mul_of_nonneg_right hlen hL)
    have : g x ^ 2 ≤ 2 * g y ^ 2 + 2 * (2 * t * L) ^ 2 := by
      have habs := abs_le.1 hb2
      nlinarith [sq_nonneg (g x - 2 * g y), sq_nonneg (g x - g y - 2 * t * L)]
    nlinarith [this]
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_const, nsmul_eq_mul, card_cornerBox, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul, card_cornerBox] at hsum
  have ht : (0 : ℝ) < ((t : ℝ) + 1) ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_add' _ _ _ ht.ne', le_div_iff₀ ht]
  nlinarith [hsum]

/-- **The uniform norm at a vertex of an infinite cluster** from its coarsening: with `S_x` the
ninefold of the partition cube of `x` and the increments of `w` along the open edges of `S_x` at
most `L`, `|w(x)| ≤ |S_x|² L + |[w]_𝒫(x)|`. -/
theorem abs_le_of_coarse (hP : PlanarPartitionEvent ω) {x : Vertex 2}
    (hinf : ((openGraph ω).connectedComponentMk x).supp.Infinite) (w : Vertex 2 → ℝ) {L : ℝ}
    (hL : 0 ≤ L)
    (h : ∀ a ∈ (planarPartCube ω x).ninefold.vertices, ∀ b ∈ (planarPartCube ω x).ninefold.vertices,
      (openGraph ω).Adj a b → |w a - w b| ≤ L) :
    |w x| ≤ ((planarPartCube ω x).ninefold.vertices.card : ℝ) ^ 2 * L +
      |w (planarCoarseAnchor ω x)| := by
  have h1 := abs_sub_coarseAnchor_le hP hinf w
  have h2 := edgeVariationIn_le (ω := ω) _ w hL h
  have h3 := abs_sub_abs_le_abs_sub (w x) (w (planarCoarseAnchor ω x))
  linarith

end Rigidity.Proofs.Regularity
