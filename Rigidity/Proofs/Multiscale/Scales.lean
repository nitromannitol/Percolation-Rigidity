import Rigidity.Proofs.Multiscale.Boundary

/-!
# The block terms of the extension, scale by scale

Let `ũ` be the extension of `u` from the triadic cube `3^m z + □_m` (corner `P`) to the closed
lattice cube `P + {0, …, 3^m}^d`. For `k ≤ m`, the children of scale `k` of the closed cube are the
closures of the subcubes `3^k j + □_k`, `j ∈ 3^{m-k} z + □_{m-k}`. Three estimates on the mean
square `blockSq` of the block means of `∇ũ` over these children:
* at every scale it is at most the face-weighted mean energy of `ũ` (Jensen and subdivision);
* at the top scale `m ≥ 1` it is at most its value at scale `m - 1`;
* it is at most twice the mean square of the normalized spatial averages `|□_k|⁻¹ ⟨∇u⟩` over the
  subcubes plus `C(d) 3^{-k}` times the mean energy (boundary layers).
-/

namespace Rigidity.Proofs.Multiscale

open LatticeProb LatticeProb.Percolation LatticeHC Matrix

variable {d : ℕ}

/-- The number of children of scale `k` of a cube of scale `n`, `|{0, …, 3^l - 1}^d| = (3^l)^d`. -/
theorem card_triadicIndex (l : ℕ) : (triadicIndex d l).card = (3 ^ l) ^ d := by
  rw [triadicIndex, Fintype.card_piFinset, Finset.prod_const, Finset.card_range, Finset.card_univ,
    Fintype.card_fin]

/-- **Subdivision of the face-weighted mean**: the average over the children of scale `k ≤ m` of
`P + {0, …, 3^m}^d` of their face-weighted means is the face-weighted mean of the parent. -/
theorem avg_cubeAvg_children {k m : ℕ} (hk : k ≤ m) (P : Site d) (f : Edge d → ℝ) :
    ((triadicIndex d (m - k)).card : ℝ)⁻¹ *
        ∑ y ∈ triadicIndex d (m - k), cubeAvg (triadicCorner P k y) (3 ^ k) f =
      cubeAvg P (3 ^ m) f := by
  have hm : 3 ^ m = 3 ^ k * 3 ^ (m - k) := by rw [← pow_add, Nat.add_sub_cancel' hk]
  have hsub := sum_weighted_edgesOf_children P (3 ^ k) (3 ^ (m - k))
    (Nat.one_le_pow _ _ (by norm_num)) (Nat.one_le_pow _ _ (by norm_num)) f
  rw [← hm] at hsub
  simp only [cubeAvg]
  rw [hsub, card_triadicIndex, ← Finset.mul_sum, ← mul_assoc]
  have hc : ((((3 ^ (m - k)) ^ d : ℕ) : ℝ))⁻¹ * (((3 ^ k : ℕ) : ℝ) ^ d)⁻¹ =
      (((3 ^ m : ℕ) : ℝ) ^ d)⁻¹ := by
    rw [hm]
    push_cast
    rw [mul_pow, mul_inv]
    ring
  rw [hc]
  rfl

/-- **Jensen for averages of vectors**: `|avg_y X_y|² ≤ avg_y |X_y|²`. -/
theorem dotProduct_avg_self_le {ι : Type*} (s : Finset ι) (X : ι → Fin d → ℝ) :
    ((s.card : ℝ)⁻¹ • ∑ y ∈ s, X y) ⬝ᵥ ((s.card : ℝ)⁻¹ • ∑ y ∈ s, X y) ≤
      (s.card : ℝ)⁻¹ * ∑ y ∈ s, X y ⬝ᵥ X y := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  simp only [dotProduct, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [show (s.card : ℝ)⁻¹ * ∑ y ∈ s, ∑ i, X y i * X y i =
      ∑ i, (s.card : ℝ)⁻¹ * ∑ y ∈ s, X y i * X y i by rw [Finset.sum_comm, Finset.mul_sum]]
  refine Finset.sum_le_sum fun i _ => ?_
  have h : (∑ y ∈ s, X y i) ^ 2 ≤ (s.card : ℝ) * ∑ y ∈ s, X y i ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hQ : ∑ y ∈ s, X y i * X y i = ∑ y ∈ s, X y i ^ 2 :=
    Finset.sum_congr rfl fun y _ => (sq _).symm
  rw [hQ]
  calc (s.card : ℝ)⁻¹ * (∑ y ∈ s, X y i) * ((s.card : ℝ)⁻¹ * ∑ y ∈ s, X y i)
      = (s.card : ℝ)⁻¹ * (s.card : ℝ)⁻¹ * (∑ y ∈ s, X y i) ^ 2 := by ring
    _ ≤ (s.card : ℝ)⁻¹ * (s.card : ℝ)⁻¹ * ((s.card : ℝ) * ∑ y ∈ s, X y i ^ 2) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = (s.card : ℝ)⁻¹ * ∑ y ∈ s, X y i ^ 2 := by
        field_simp

/-- **Every block term is at most the mean energy**: `blockSq_k(F) ≤ cubeAvg(F²)` for `k ≤ m`. -/
theorem blockSq_le_cubeAvg {k m : ℕ} (hk : k ≤ m) (P : Site d) (F : Edge d → ℝ) :
    blockSq P m k F ≤ cubeAvg P (3 ^ m) (fun e => F e ^ 2) := by
  rw [← avg_cubeAvg_children hk P, blockSq, blockPair]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => ?_) (by positivity)
  exact dotProduct_blockMean_self_le_cubeAvg _ (Nat.one_le_pow _ _ (by norm_num)) F

/-- **The top block term** is at most the block term of the scale below. -/
theorem blockSq_self_le_pred {m : ℕ} (hm : 1 ≤ m) (P : Site d) (F : Edge d → ℝ) :
    blockSq P m m F ≤ blockSq P m (m - 1) F := by
  have h0 : triadicIndex d 0 = {0} := by
    ext y
    simp only [mem_triadicIndex, pow_zero, Nat.lt_one_iff, Finset.mem_singleton]
    exact ⟨fun h => funext h, fun h i => by rw [h]; rfl⟩
  have hc : triadicCorner P m 0 = P := by
    funext i
    simp [triadicCorner]
  have htop : blockSq P m m F = blockMean P (3 ^ m) F ⬝ᵥ blockMean P (3 ^ m) F := by
    rw [blockSq, blockPair, Nat.sub_self, h0, Finset.sum_singleton, Finset.card_singleton, hc]
    simp
  have hsucc := blockMean_succ_eq_avg_children P (m - 1) F
  rw [Nat.sub_add_cancel hm] at hsucc
  have hidx : m - (m - 1) = 1 := by omega
  rw [htop, hsucc, blockSq, blockPair, hidx]
  exact dotProduct_avg_self_le _ _

/-- The children are indexed by `3^l z + □_l`: `y ↦ P' + y` maps `{0, …, 3^l - 1}^d` onto it,
`P'` its corner. -/
theorem sum_triadicIndex_eq_sum_cube {β : Type*} [AddCommMonoid β] (l : ℕ) (z : Vertex d)
    (f : Vertex d → β) :
    ∑ y ∈ triadicIndex d l, f (fun i => cubeCorner l z i + (y i : ℤ)) = ∑ j ∈ cube l z, f j := by
  have hcast : ((3 ^ l : ℕ) : ℤ) = (3 : ℤ) ^ l := by push_cast; rfl
  refine Finset.sum_nbij' (fun y i => cubeCorner l z i + (y i : ℤ))
    (fun j i => (j i - cubeCorner l z i).toNat) (fun y hy => ?_) (fun j hj => ?_)
    (fun y _ => ?_) (fun j hj => ?_) (fun _ _ => rfl)
  · rw [mem_triadicIndex] at hy
    rw [mem_cube_iff_corner]
    intro i
    have := hy i
    have h' : ((y i : ℕ) : ℤ) < ((3 ^ l : ℕ) : ℤ) := by exact_mod_cast this
    omega
  · rw [mem_cube_iff_corner] at hj
    rw [mem_triadicIndex]
    intro i
    obtain ⟨h1, h2⟩ := hj i
    have h3 := Int.toNat_of_nonneg (show 0 ≤ j i - cubeCorner l z i by omega)
    omega
  · funext i
    simp
  · rw [mem_cube_iff_corner] at hj
    funext i
    obtain ⟨h1, _⟩ := hj i
    show cubeCorner l z i + ((j i - cubeCorner l z i).toNat : ℤ) = j i
    rw [Int.toNat_of_nonneg (by omega)]
    ring

/-- The subcubes of scale `k ≤ m` of a subcube index `j ∈ 3^{m-k} z + □_{m-k}` lie in the cube. -/
theorem cube_subset_cube {k m : ℕ} (hk : k ≤ m) {z j : Vertex d} (hj : j ∈ cube (m - k) z) :
    cube k j ⊆ cube m z := by
  intro x hx
  rw [mem_cube_iff_corner] at hx hj ⊢
  intro i
  obtain ⟨h1, h2⟩ := hx i
  obtain ⟨h3, h4⟩ := hj i
  rw [cubeCorner_subcube hk z j i] at h1 h2
  have hm : (3 : ℤ) ^ m = 3 ^ k * 3 ^ (m - k) := by rw [← pow_add, Nat.add_sub_cancel' hk]
  have hpos : (0 : ℤ) ≤ 3 ^ k := by positivity
  have ha : 0 ≤ (3 : ℤ) ^ k * (j i - cubeCorner (m - k) z i) := mul_nonneg hpos (by omega)
  have hb : (3 : ℤ) ^ k * (j i - cubeCorner (m - k) z i) + 3 ^ k ≤ 3 ^ m := by
    rw [hm, ← mul_add_one]
    exact mul_le_mul_of_nonneg_left (by omega) hpos
  constructor <;> omega

/-- The half-open cube of the child of index `y` is the subcube of index `P' + y`. -/
theorem halfOpenCube_triadicCorner {k m : ℕ} (hk : k ≤ m) (z : Vertex d) (y : Fin d → ℕ) :
    halfOpenCube (triadicCorner (cubeCorner m z) k y) (3 ^ k) =
      cube k (fun i => cubeCorner (m - k) z i + (y i : ℤ)) := by
  rw [cube_eq_piFinset, halfOpenCube]
  congr 1
  funext i
  rw [cubeCorner_subcube hk z _ i]
  simp only [triadicCorner, Pi.add_apply, add_sub_cancel_left]
  push_cast
  rfl

/-- The spatial sum over `B` only depends on the values on `B`. -/
theorem gradSum_congr {B : Finset (Vertex d)} {u v : Vertex d → ℝ} (h : ∀ x ∈ B, u x = v x) :
    gradSum B u = gradSum B v := by
  funext j
  simp only [gradSum]
  refine Finset.sum_congr rfl fun x hx => ?_
  split_ifs with h1
  · rw [h x hx, h _ h1]
  · rfl

/-- **The block terms against the spatial averages**: if `v = u` on `3^m z + □_m`, then for
`k ≤ m`, `blockSq_k(∇v) ≤ 2 · subcubeGradMeanSq m z k u + 2 · 12 d 4^d 3^{-k} cubeAvg(|∇v|²)` on
the closed cube `P + {0, …, 3^m}^d`. -/
theorem blockSq_le_of_eqOn {k m : ℕ} (hk : k ≤ m) (z : Vertex d) (u v : Vertex d → ℝ)
    (huv : ∀ x ∈ cube m z, v x = u x) :
    blockSq (cubeCorner m z) m k (fun e => v e.tgt - v e.src) ≤
      2 * subcubeGradMeanSq m z k u + 2 * (12 * d * 4 ^ d) * ((3 : ℝ) ^ k)⁻¹ *
        cubeAvg (cubeCorner m z) (3 ^ m) (fun e => (v e.tgt - v e.src) ^ 2) := by
  have hn0 : 0 ≤ ((triadicIndex d (m - k)).card : ℝ)⁻¹ := by positivity
  have hcastk : (((3 ^ k : ℕ) : ℝ)) = (3 : ℝ) ^ k := by push_cast; rfl
  have hchild : ∀ y ∈ triadicIndex d (m - k),
      blockMean (triadicCorner (cubeCorner m z) k y) (3 ^ k) (fun e => v e.tgt - v e.src) ⬝ᵥ
          blockMean (triadicCorner (cubeCorner m z) k y) (3 ^ k) (fun e => v e.tgt - v e.src) ≤
        2 * ∑ i : Fin d, ((((3 : ℝ) ^ k) ^ d)⁻¹ *
            gradSum (cube k (fun i => cubeCorner (m - k) z i + (y i : ℤ))) u i) ^ 2 +
          2 * (12 * d * 4 ^ d * ((3 : ℝ) ^ k)⁻¹ *
            cubeAvg (triadicCorner (cubeCorner m z) k y) (3 ^ k)
              (fun e => (v e.tgt - v e.src) ^ 2)) := by
    intro y hy
    have hjmem : (fun i => cubeCorner (m - k) z i + (y i : ℤ)) ∈ cube (m - k) z := by
      rw [mem_cube_iff_corner]
      intro i
      have h := (mem_triadicIndex.1 hy) i
      have hcast : ((3 ^ (m - k) : ℕ) : ℤ) = (3 : ℤ) ^ (m - k) := by push_cast; rfl
      have h' : ((y i : ℕ) : ℤ) < ((3 ^ (m - k) : ℕ) : ℤ) := by exact_mod_cast h
      constructor <;> omega
    have hagree : ∀ x ∈ halfOpenCube (triadicCorner (cubeCorner m z) k y) (3 ^ k), v x = u x := by
      intro x hx
      rw [halfOpenCube_triadicCorner hk z y] at hx
      exact huv x (cube_subset_cube hk hjmem hx)
    have herr := sum_sq_blockMean_sub_gradSum_le (triadicCorner (cubeCorner m z) k y)
      (Nat.one_le_pow k 3 (by norm_num)) v
    rw [gradSum_congr hagree, halfOpenCube_triadicCorner hk z y, hcastk] at herr
    calc blockMean (triadicCorner (cubeCorner m z) k y) (3 ^ k) (fun e => v e.tgt - v e.src) ⬝ᵥ
          blockMean (triadicCorner (cubeCorner m z) k y) (3 ^ k) (fun e => v e.tgt - v e.src)
        = ∑ i : Fin d, (blockMean (triadicCorner (cubeCorner m z) k y) (3 ^ k)
            (fun e => v e.tgt - v e.src) i) ^ 2 := by
          simp only [dotProduct, sq]
      _ ≤ ∑ i : Fin d, (2 * ((((3 : ℝ) ^ k) ^ d)⁻¹ *
              gradSum (cube k (fun i => cubeCorner (m - k) z i + (y i : ℤ))) u i) ^ 2 +
            2 * (blockMean (triadicCorner (cubeCorner m z) k y) (3 ^ k)
              (fun e => v e.tgt - v e.src) i - (((3 : ℝ) ^ k) ^ d)⁻¹ *
                gradSum (cube k (fun i => cubeCorner (m - k) z i + (y i : ℤ))) u i) ^ 2) := by
          refine Finset.sum_le_sum fun i _ => ?_
          nlinarith [sq_nonneg (blockMean (triadicCorner (cubeCorner m z) k y) (3 ^ k)
            (fun e => v e.tgt - v e.src) i - 2 * ((((3 : ℝ) ^ k) ^ d)⁻¹ *
              gradSum (cube k (fun i => cubeCorner (m - k) z i + (y i : ℤ))) u i))]
      _ = 2 * ∑ i : Fin d, ((((3 : ℝ) ^ k) ^ d)⁻¹ *
              gradSum (cube k (fun i => cubeCorner (m - k) z i + (y i : ℤ))) u i) ^ 2 +
            2 * ∑ i : Fin d, (blockMean (triadicCorner (cubeCorner m z) k y) (3 ^ k)
              (fun e => v e.tgt - v e.src) i - (((3 : ℝ) ^ k) ^ d)⁻¹ *
                gradSum (cube k (fun i => cubeCorner (m - k) z i + (y i : ℤ))) u i) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left herr (by norm_num : (0 : ℝ) ≤ 2))
  have hS : ((triadicIndex d (m - k)).card : ℝ)⁻¹ * ∑ y ∈ triadicIndex d (m - k),
      ∑ i : Fin d, ((((3 : ℝ) ^ k) ^ d)⁻¹ *
        gradSum (cube k (fun i => cubeCorner (m - k) z i + (y i : ℤ))) u i) ^ 2 =
      subcubeGradMeanSq m z k u := by
    rw [subcubeGradMeanSq_eq hk, card_triadicIndex]
    push_cast
    congr 1
    exact sum_triadicIndex_eq_sum_cube (m - k) z
      (fun j => ∑ i : Fin d, ((((3 : ℝ) ^ k) ^ d)⁻¹ * gradSum (cube k j) u i) ^ 2)
  have hA := avg_cubeAvg_children hk (cubeCorner m z) (fun e => (v e.tgt - v e.src) ^ 2)
  calc blockSq (cubeCorner m z) m k (fun e => v e.tgt - v e.src)
      = ((triadicIndex d (m - k)).card : ℝ)⁻¹ * ∑ y ∈ triadicIndex d (m - k),
          blockMean (triadicCorner (cubeCorner m z) k y) (3 ^ k) (fun e => v e.tgt - v e.src) ⬝ᵥ
            blockMean (triadicCorner (cubeCorner m z) k y) (3 ^ k)
              (fun e => v e.tgt - v e.src) := rfl
    _ ≤ ((triadicIndex d (m - k)).card : ℝ)⁻¹ * ∑ y ∈ triadicIndex d (m - k),
          (2 * ∑ i : Fin d, ((((3 : ℝ) ^ k) ^ d)⁻¹ *
              gradSum (cube k (fun i => cubeCorner (m - k) z i + (y i : ℤ))) u i) ^ 2 +
            2 * (12 * d * 4 ^ d * ((3 : ℝ) ^ k)⁻¹ *
              cubeAvg (triadicCorner (cubeCorner m z) k y) (3 ^ k)
                (fun e => (v e.tgt - v e.src) ^ 2))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hchild) hn0
    _ = 2 * (((triadicIndex d (m - k)).card : ℝ)⁻¹ * ∑ y ∈ triadicIndex d (m - k),
          ∑ i : Fin d, ((((3 : ℝ) ^ k) ^ d)⁻¹ *
            gradSum (cube k (fun i => cubeCorner (m - k) z i + (y i : ℤ))) u i) ^ 2) +
          2 * (12 * d * 4 ^ d) * ((3 : ℝ) ^ k)⁻¹ *
            (((triadicIndex d (m - k)).card : ℝ)⁻¹ * ∑ y ∈ triadicIndex d (m - k),
              cubeAvg (triadicCorner (cubeCorner m z) k y) (3 ^ k)
                (fun e => (v e.tgt - v e.src) ^ 2)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
        ring
    _ = _ := by rw [hS, hA]

end Rigidity.Proofs.Multiscale
