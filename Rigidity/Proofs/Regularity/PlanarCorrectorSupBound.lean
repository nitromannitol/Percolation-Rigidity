import Rigidity.Proofs.Regularity.PlanarCorrectorCoarse

/-!
# The uniform bound of a function on the planar cluster at one scale

`abs_le_of_scale_bounds` combines the comparison with the coarsening and the interpolation
inequality on the box `x + [0, t]²` (Armstrong and Dario, arXiv:1609.09431v2, Remark after
(1.19)): if on the box `{|z_i| ≤ 3N}` the increments of `w` along open edges are at most `L`, the
partition cubes of `{|y_i| ≤ 2N}` have sides at most `δ ≤ N/10` and `Σ_{|z_i| ≤ 3N} w² ≤ M₂`,
then for every vertex `x` of an infinite cluster with `|x_i| ≤ N` and `t + 1 ≤ N`,
`|w(x)| ≤ (81 δ²)² L + (2 (t+1)^{-2} δ² M₂ + 8 t² ((81 δ²)² L)²)^{1/2}`.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.Percolation
open scoped Classical

variable {ω : Configuration 2}

/-- The box `{z ∈ ℤ² : |z_i| ≤ n}`. -/
noncomputable def centredBox (n : ℕ) : Finset (Vertex 2) :=
  Fintype.piFinset fun _ => Finset.Icc (-(n : ℤ)) n

theorem mem_centredBox {n : ℕ} {z : Vertex 2} : z ∈ centredBox n ↔ ∀ i, |z i| ≤ n := by
  simp only [centredBox, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

/-- The ninefold of the partition cube of a vertex of `{|y_i| ≤ 2N}` lies in `{|z_i| ≤ 3N}` when
the side of the cube is at most `N/10`. -/
theorem abs_le_of_mem_ninefold (hP : PlanarPartitionEvent ω) {N : ℕ} {y z : Vertex 2}
    (hy : ∀ i, |y i| ≤ 2 * N) (hs : 10 * (3 : ℤ) ^ (planarPartCube ω y).scale ≤ N)
    (hz : z ∈ (planarPartCube ω y).ninefold.vertices) : ∀ i, |z i| ≤ 3 * N := by
  intro i
  have h9 := (planarPartCube ω y).two_mul_ninefoldRadius
  have hyc := (planarPartCube ω y).abs_sub_center_le (planarPartCube_spec hP y).1 i
  have hzc := (TriadicCube.mem_ninefold.1 (Finset.mem_coe.2 hz)) i
  have hyi := hy i
  have a1 := abs_sub_le (z i) ((planarPartCube ω y).center i) (y i)
  have a2 := abs_sub_abs_le_abs_sub (z i) (y i)
  rw [abs_sub_comm ((planarPartCube ω y).center i) (y i)] at a1
  have a3 : |z i| ≤ |z i - y i| + |y i| := by linarith
  omega

theorem card_ninefold_le {Q : TriadicCube 2} {δ : ℝ} (hδ : (3 : ℝ) ^ Q.scale ≤ δ) :
    (Q.ninefold.vertices.card : ℝ) ≤ 81 * δ ^ 2 := by
  rw [card_ninefold_vertices]
  have := pow_le_pow_left₀ (by positivity) hδ 2
  linarith

/-- **The uniform bound at one scale.** -/
theorem abs_le_of_scale_bounds (hP : PlanarPartitionEvent ω) (w : Vertex 2 → ℝ) {N t : ℕ}
    (htN : t + 1 ≤ N) {δ L M₂ : ℝ} (hL : 0 ≤ L)
    (hsize : ∀ y : Vertex 2, (∀ i, |y i| ≤ 2 * N) → (3 : ℝ) ^ (planarPartCube ω y).scale ≤ δ)
    (hδN : 10 * δ ≤ N)
    (hgrad : ∀ a b : Vertex 2, (∀ i, |a i| ≤ 3 * N) → (∀ i, |b i| ≤ 3 * N) →
      (openGraph ω).Adj a b → |w a - w b| ≤ L)
    (hM : ∑ z ∈ centredBox (3 * N), w z ^ 2 ≤ M₂) {x : Vertex 2} (hx : ∀ i, |x i| ≤ N)
    (hinf : ((openGraph ω).connectedComponentMk x).supp.Infinite) :
    |w x| ≤ (81 * δ ^ 2) ^ 2 * L +
      √(2 / ((t : ℝ) + 1) ^ 2 * (δ ^ 2 * M₂) + 8 * (t : ℝ) ^ 2 * ((81 * δ ^ 2) ^ 2 * L) ^ 2) := by
  have hint : ∀ y : Vertex 2, (∀ i, |y i| ≤ 2 * N) →
      10 * (3 : ℤ) ^ (planarPartCube ω y).scale ≤ N := by
    intro y hy
    have h1 := hsize y hy
    have h2 : (10 * (3 : ℤ) ^ (planarPartCube ω y).scale : ℝ) ≤ (N : ℝ) := by
      push_cast; linarith
    exact_mod_cast h2
  -- the increments on the ninefold of a cube of `{|y_i| ≤ 2N}`
  have hnine : ∀ y : Vertex 2, (∀ i, |y i| ≤ 2 * N) →
      edgeVariationIn ω (planarPartCube ω y).ninefold.vertices w ≤ (81 * δ ^ 2) ^ 2 * L := by
    intro y hy
    have hcard := card_ninefold_le (hsize y hy)
    refine (edgeVariationIn_le _ w hL fun a ha b hb hab =>
      hgrad a b (abs_le_of_mem_ninefold hP hy (hint y hy) ha)
        (abs_le_of_mem_ninefold hP hy (hint y hy) hb) hab).trans ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2) hL
  have hx2 : ∀ i, |x i| ≤ 2 * N := fun i => by have := hx i; omega
  -- the comparison with the coarsening
  have hc := abs_le_of_coarse hP hinf w hL fun a ha b hb hab =>
    hgrad a b (abs_le_of_mem_ninefold hP hx2 (hint x hx2) ha)
      (abs_le_of_mem_ninefold hP hx2 (hint x hx2) hb) hab
  have hcard := card_ninefold_le (hsize x hx2)
  have hc' : |w x| ≤ (81 * δ ^ 2) ^ 2 * L + |w (planarCoarseAnchor ω x)| :=
    hc.trans (by gcongr)
  -- the interpolation inequality for the coarsening
  set g : Vertex 2 → ℝ := fun y => w (planarCoarseAnchor ω y) with hg
  have hbox : ∀ p ∈ cornerBox x t, ∀ i, |p i| ≤ 2 * N - 1 := by
    intro p hp i
    have h1 := (mem_cornerBox.1 hp) i
    have h2 := hx i
    have h3 := le_abs_self (x i)
    have h4 := neg_abs_le (x i)
    rw [abs_le]
    constructor <;> omega
  have hL3 : ∀ p ∈ cornerBox x t, ∀ l, |g (p + unit l) - g p| ≤ (81 * δ ^ 2) ^ 2 * L := by
    intro p hp l
    have hp2 : ∀ i, |p i| ≤ 2 * N := fun i => by have := hbox p hp i; omega
    have hpl : ∀ i, |(p + unit l) i| ≤ 2 * N := fun i => by
      have := hbox p hp i
      rw [Pi.add_apply, unit_apply_two]
      split_ifs <;> rw [abs_le] at this ⊢ <;> constructor <;> omega
    have hnear : ∀ i, |(p + unit l) i - p i| ≤ 1 := fun i => by
      rw [Pi.add_apply, unit_apply_two]; split_ifs <;> simp
    rcases le_total (planarPartCube ω (p + unit l)).scale (planarPartCube ω p).scale with h | h
    · exact (abs_coarseAnchor_sub_le hP hnear h w).trans (hnine _ hpl)
    · have hnear' : ∀ i, |p i - (p + unit l) i| ≤ 1 := fun i => by
        rw [abs_sub_comm]; exact hnear i
      rw [abs_sub_comm]
      exact (abs_coarseAnchor_sub_le hP hnear' h w).trans (hnine _ hp2)
  have hsq := sq_le_of_box g x t (by positivity) hL3
  have hsum : ∑ y ∈ cornerBox x t, g y ^ 2 ≤ δ ^ 2 * M₂ := by
    have hsub : ∀ y ∈ cornerBox x t, planarCoarseAnchor ω y ∈ centredBox (3 * N) := by
      intro y hy
      have hy2 : ∀ i, |y i| ≤ 2 * N := fun i => by have := hbox y hy i; omega
      rw [mem_centredBox]
      intro i
      have haQ : planarCoarseAnchor ω y ∈ (planarPartCube ω y).vertices :=
        ((planarPartCube ω y).planarAnchor_spec (planarPartCube_meshed hP y).1
          (planarPartCube_large hP y)).1
      have h1 := (planarPartCube ω y).abs_sub_center_le haQ i
      have h2 := (planarPartCube ω y).abs_sub_center_le (planarPartCube_spec hP y).1 i
      have h3 := hint y hy2
      have h4 := hy2 i
      have a1 := abs_sub_le (planarCoarseAnchor ω y i) ((planarPartCube ω y).center i) (y i)
      rw [abs_sub_comm ((planarPartCube ω y).center i) (y i)] at a1
      have a2 := abs_sub_abs_le_abs_sub (planarCoarseAnchor ω y i) (y i)
      push_cast
      omega
    have h := sum_coarseAnchor_le_of_subset hP (cornerBox x t) (centredBox (3 * N)) hsub
      (φ := fun z => w z ^ 2) (fun z => sq_nonneg _)
      (fun y hy => hsize y fun i => by have := hbox y hy i; omega)
    calc ∑ y ∈ cornerBox x t, g y ^ 2 ≤ δ ^ 2 * ∑ z ∈ centredBox (3 * N), w z ^ 2 := h
      _ ≤ δ ^ 2 * M₂ := mul_le_mul_of_nonneg_left hM (sq_nonneg _)
  have hgx : |g x| ≤
      √(2 / ((t : ℝ) + 1) ^ 2 * (δ ^ 2 * M₂) + 8 * (t : ℝ) ^ 2 * ((81 * δ ^ 2) ^ 2 * L) ^ 2) := by
    refine Real.abs_le_sqrt (hsq.trans ?_)
    gcongr
  calc |w x| ≤ (81 * δ ^ 2) ^ 2 * L + |w (planarCoarseAnchor ω x)| := hc'
    _ ≤ _ := by gcongr

end Rigidity.Proofs.Regularity
