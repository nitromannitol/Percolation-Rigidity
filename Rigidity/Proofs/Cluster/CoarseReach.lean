import Rigidity.Proofs.Cluster.CoarseNear

/-!
# The coarsening error with the reach of the partition

Suppose the region of each vertex `x` of the cluster lies in the `c · size(□_𝒫(x))`-neighbourhood
of its partition cube, but may meet partition cubes much smaller than `□_𝒫(x)`: this happens for
the windows of the planar partition, and for paths from a vertex on the boundary of its partition
cube that leave the cube. Then Lemma 3.2 of Armstrong and Dario holds with the size of the
partition cube of `z` replaced by `3^{ρ(z)}`, where the *reach scale* `ρ(z)` is the largest scale of
a partition cube whose region contains `z`:
`∑_{x ∈ C_*(U)} |w(x) - [w]_𝒫(x)|^s ≤ C^s ∑_{z ∈ C_*(U)} (3^{ρ(z)})^{sd} |∇w 1_{a≠0}|^s(z)`
with `C = (3/2) (2c + 2)^d (2c + 1)^d 2√d`. The partition cubes of a given scale whose
neighbourhoods contain `z` are disjoint and lie in a cube of side `(2c + 2)` times their side around
`z`, so there are at most `(2c + 2)^d` of them, and the sum over the scales up to `ρ(z)` is
geometric.
-/

open LatticeProb.Percolation
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ}

/-- The integer cube of side `(2c + 1) 3^n` around a triadic cube of scale `n`. -/
def TriadicCube.thicken (Q : TriadicCube d) (c : ℕ) : IntegerCube d where
  corner i := Q.toIntegerCube.corner i - c * (Q.toIntegerCube.size : ℤ)
  size := (2 * c + 1) * Q.toIntegerCube.size

theorem TriadicCube.card_thicken (Q : TriadicCube d) (c : ℕ) :
    (Q.thicken c).vertices.card = (2 * c + 1) ^ d * 3 ^ (Q.scale * d) := by
  rw [IntegerCube.card_vertices_eq]
  change ((2 * c + 1) * 3 ^ Q.scale) ^ d = _
  rw [mul_pow, pow_mul]

/-- The integer cube of side `(2c + 2) 3^k` around a vertex. -/
def boxAround (z : Vertex d) (c k : ℕ) : IntegerCube d where
  corner i := z i - (((c + 1) * 3 ^ k : ℕ) : ℤ)
  size := (2 * c + 2) * 3 ^ k

theorem card_boxAround (z : Vertex d) (c k : ℕ) :
    (boxAround z c k).vertices.card = (2 * c + 2) ^ d * 3 ^ (k * d) := by
  rw [IntegerCube.card_vertices_eq]
  change ((2 * c + 2) * 3 ^ k) ^ d = _
  rw [mul_pow, pow_mul]

/-- A triadic cube whose neighbourhood contains `z` lies in the cube around `z` of side `2c + 2`
times its side. -/
theorem TriadicCube.subset_boxAround {Q : TriadicCube d} {c : ℕ} {z : Vertex d}
    (hz : z ∈ (Q.thicken c).vertices) :
    Q.toIntegerCube.vertices ⊆ (boxAround z c Q.scale).vertices := by
  rw [IntegerCube.mem_vertices] at hz
  intro y hy
  rw [IntegerCube.mem_vertices] at hy ⊢
  intro i
  have hs : (Q.toIntegerCube.size : ℤ) = (3 : ℤ) ^ Q.scale := by
    simp only [TriadicCube.toIntegerCube, Nat.cast_pow, Nat.cast_ofNat]
  obtain ⟨h1, h2⟩ := hz i
  obtain ⟨h3, h4⟩ := hy i
  change Q.toIntegerCube.corner i - c * (Q.toIntegerCube.size : ℤ) ≤ z i at h1
  change z i < Q.toIntegerCube.corner i - c * (Q.toIntegerCube.size : ℤ) +
    (((2 * c + 1) * Q.toIntegerCube.size : ℕ) : ℤ) at h2
  change z i - (((c + 1) * 3 ^ Q.scale : ℕ) : ℤ) ≤ y i ∧
    y i < z i - (((c + 1) * 3 ^ Q.scale : ℕ) : ℤ) + (((2 * c + 2) * 3 ^ Q.scale : ℕ) : ℤ)
  push_cast at h2 ⊢
  rw [hs] at h1 h2 h4
  constructor <;> linarith

/-- The contribution of one partition cube to the weight of Lemma 3.2 with the reach scale. -/
private noncomputable def reachTerm (c : ℕ) (s : ℝ) (Q : TriadicCube d) : ℝ :=
  ((2 * c + 1 : ℝ) ^ d * ((3 : ℝ) ^ Q.scale) ^ d) ^ (s - 1)

private theorem reachTerm_nonneg (c : ℕ) (s : ℝ) (Q : TriadicCube d) : 0 ≤ reachTerm c s Q :=
  Real.rpow_nonneg (by positivity) _

private theorem sum_range_pow_le {b : ℝ} (hb : 3 ≤ b) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), b ^ k ≤ 3 / 2 * b ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hbn : 0 ≤ b ^ n := pow_nonneg (by linarith) n
    calc ∑ k ∈ Finset.range (n + 1), b ^ k + b ^ (n + 1) ≤ 3 / 2 * b ^ n + b ^ (n + 1) := by
          linarith
      _ ≤ 3 / 2 * b ^ (n + 1) := by
          rw [pow_succ]
          nlinarith

namespace CoarseData

variable {ω : Configuration d} (P : CoarseData d ω)

/-- The reach scale at `z`: the largest scale of the partition cube of a vertex of the cluster
whose region contains `z`. -/
noncomputable def reachScale (z : Vertex d) : ℕ :=
  (P.cluster.filter fun x => z ∈ P.region x).sup fun x => (P.part x).scale

theorem scale_le_reachScale {x z : Vertex d} (hx : x ∈ P.cluster) (hz : z ∈ P.region x) :
    (P.part x).scale ≤ P.reachScale z :=
  Finset.le_sup (f := fun x => (P.part x).scale) (Finset.mem_filter.2 ⟨hx, hz⟩)

theorem mem_region_self {x : Vertex d} (hx : x ∈ P.cluster) : x ∈ P.region x := by
  obtain ⟨W, hW⟩ := P.joinedWithin_region x hx
  exact (Finset.mem_inter.1 (Finset.mem_coe.1 (hW x W.start_mem_support))).1

/-- The reach scale at a vertex of the cluster is at least the scale of its partition cube. -/
theorem scale_le_reachScale_self {z : Vertex d} (hz : z ∈ P.cluster) :
    (P.part z).scale ≤ P.reachScale z :=
  P.scale_le_reachScale hz (P.mem_region_self hz)

/-- At most `(2c + 2)^d` partition cubes of a given scale have neighbourhoods containing `z`. -/
theorem card_le_of_mem_thicken (I : Finset (TriadicCube d))
    (hI : ∀ Q ∈ I, ∃ x ∈ P.domain, P.part x = Q) {z : Vertex d} {c k : ℕ}
    (hz : ∀ Q ∈ I, z ∈ (Q.thicken c).vertices) (hk : ∀ Q ∈ I, Q.scale = k) :
    I.card ≤ (2 * c + 2) ^ d := by
  have hdisj : (I : Set (TriadicCube d)).PairwiseDisjoint fun Q => Q.toIntegerCube.vertices := by
    intro Q hQ Q' hQ' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨x, hx, rfl⟩ := hI Q hQ
    obtain ⟨x', hx', rfl⟩ := hI Q' hQ'
    have hy₁ : y ∈ (P.part x).vertices := (TriadicCube.mem_toIntegerCube_vertices _ _).1 hy
    have hy₂ : y ∈ (P.part x').vertices := (TriadicCube.mem_toIntegerCube_vertices _ _).1 hy'
    exact hne ((P.part_eq_of_mem x hx y hy₁).symm.trans (P.part_eq_of_mem x' hx' y hy₂))
  have hsub : I.biUnion (fun Q => Q.toIntegerCube.vertices) ⊆ (boxAround z c k).vertices := by
    intro y hy
    obtain ⟨Q, hQ, hyQ⟩ := Finset.mem_biUnion.1 hy
    have h := TriadicCube.subset_boxAround (hz Q hQ) hyQ
    rwa [hk Q hQ] at h
  have hcard := (Finset.card_biUnion hdisj).symm.le.trans (Finset.card_le_card hsub)
  rw [card_boxAround] at hcard
  have hsum : ∑ Q ∈ I, Q.toIntegerCube.vertices.card = I.card * 3 ^ (k * d) := by
    calc ∑ Q ∈ I, Q.toIntegerCube.vertices.card = ∑ _Q ∈ I, 3 ^ (k * d) := by
          refine Finset.sum_congr rfl fun Q hQ => ?_
          rw [IntegerCube.card_vertices_eq]
          change (3 ^ Q.scale) ^ d = _
          rw [hk Q hQ, ← pow_mul]
      _ = I.card * 3 ^ (k * d) := by rw [Finset.sum_const, smul_eq_mul]
  rw [hsum] at hcard
  exact Nat.le_of_mul_le_mul_right hcard (by positivity)

/-- **The weight of Lemma 3.2 with the reach scale.** If the regions lie in the
`c · size`-neighbourhoods of the partition cubes, then
`errorWeight s z ≤ (3/2) (2c + 2)^d ((2c + 1)^d)^{s-1} ((3^{ρ(z)})^d)^s`. -/
theorem errorWeight_le_reach {c : ℕ}
    (hreg : ∀ x ∈ P.cluster, P.region x ∩ P.cluster ⊆ ((P.part x).thicken c).vertices)
    (hd : 1 ≤ d) {s : ℝ} (hs : 1 ≤ s) {z : Vertex d} (hz : z ∈ P.cluster) :
    P.errorWeight s z ≤ 3 / 2 * (2 * c + 2 : ℝ) ^ d * ((2 * c + 1 : ℝ) ^ d) ^ (s - 1) *
      (((3 : ℝ) ^ P.reachScale z) ^ d) ^ s := by
  have hs1 : 0 ≤ s - 1 := by linarith
  set F := P.cluster.filter fun x => z ∈ P.region x with hF
  have hW : P.errorWeight s z = ∑ x ∈ F, ((P.region x ∩ P.cluster).card : ℝ) ^ (s - 1) := by
    rw [errorWeight, hF, Finset.sum_filter]
  have hc : ∀ x ∈ F, ((P.region x ∩ P.cluster).card : ℝ) ^ (s - 1) ≤ reachTerm c s (P.part x) := by
    intro x hx
    have h1 := (Finset.card_le_card (hreg x (Finset.mem_filter.1 hx).1)).trans
      ((P.part x).card_thicken c).le
    have h2 : ((P.region x ∩ P.cluster).card : ℝ) ≤
        (2 * c + 1 : ℝ) ^ d * ((3 : ℝ) ^ (P.part x).scale) ^ d := by
      calc ((P.region x ∩ P.cluster).card : ℝ)
          ≤ (((2 * c + 1) ^ d * 3 ^ ((P.part x).scale * d) : ℕ) : ℝ) := by exact_mod_cast h1
        _ = (2 * c + 1 : ℝ) ^ d * ((3 : ℝ) ^ (P.part x).scale) ^ d := by push_cast; ring
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) h2 hs1
  have hF_maps : ∀ x ∈ F, P.part x ∈ F.image P.part := fun x hx => Finset.mem_image_of_mem _ hx
  -- regroup by partition cubes
  have hstep1 : ∑ x ∈ F, ((P.region x ∩ P.cluster).card : ℝ) ^ (s - 1) ≤
      ∑ Q ∈ F.image P.part, ((3 : ℝ) ^ Q.scale) ^ d * reachTerm c s Q := by
    calc ∑ x ∈ F, ((P.region x ∩ P.cluster).card : ℝ) ^ (s - 1)
        ≤ ∑ x ∈ F, reachTerm c s (P.part x) := Finset.sum_le_sum hc
      _ = ∑ Q ∈ F.image P.part, ∑ x ∈ F.filter (fun x => P.part x = Q), reachTerm c s (P.part x) :=
          (Finset.sum_fiberwise_of_maps_to hF_maps _).symm
      _ ≤ ∑ Q ∈ F.image P.part, ((3 : ℝ) ^ Q.scale) ^ d * reachTerm c s Q := by
          refine Finset.sum_le_sum fun Q hQ => ?_
          obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.1 hQ
          have hconst : ∑ x ∈ F.filter (fun x => P.part x = P.part x₀), reachTerm c s (P.part x) =
              ∑ _x ∈ F.filter (fun x => P.part x = P.part x₀), reachTerm c s (P.part x₀) :=
            Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.1 hx).2]
          rw [hconst, Finset.sum_const, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ (reachTerm_nonneg c s _)
          have hsub : F.filter (fun x => P.part x = P.part x₀) ⊆
              (P.part x₀).toIntegerCube.vertices := by
            intro y hy
            rw [Finset.mem_filter] at hy
            rw [TriadicCube.mem_toIntegerCube_vertices, ← hy.2]
            exact P.mem_part y (P.cluster_subset (Finset.mem_filter.1 hy.1).1)
          have h1 := Finset.card_le_card hsub
          rw [IntegerCube.card_vertices_eq] at h1
          calc ((F.filter fun x => P.part x = P.part x₀).card : ℝ)
              ≤ (((P.part x₀).toIntegerCube.size ^ d : ℕ) : ℝ) := by exact_mod_cast h1
            _ = ((3 : ℝ) ^ (P.part x₀).scale) ^ d := by
                simp only [TriadicCube.toIntegerCube, Nat.cast_pow, Nat.cast_ofNat]
  -- each cube contributes `((2c+1)^d)^{s-1} ((3^k)^d)^s`
  have hterm : ∀ Q : TriadicCube d, ((3 : ℝ) ^ Q.scale) ^ d * reachTerm c s Q =
      ((2 * c + 1 : ℝ) ^ d) ^ (s - 1) * (((3 : ℝ) ^ Q.scale) ^ d) ^ s := by
    intro Q
    have hL : (0 : ℝ) < ((3 : ℝ) ^ Q.scale) ^ d := by positivity
    unfold reachTerm
    rw [Real.mul_rpow (x := (2 * c + 1 : ℝ) ^ d) (by positivity) hL.le,
      Real.rpow_sub_one hL.ne' s]
    calc ((3 : ℝ) ^ Q.scale) ^ d * (((2 * c + 1 : ℝ) ^ d) ^ (s - 1) *
          ((((3 : ℝ) ^ Q.scale) ^ d) ^ s / ((3 : ℝ) ^ Q.scale) ^ d))
        = ((2 * c + 1 : ℝ) ^ d) ^ (s - 1) * ((((3 : ℝ) ^ Q.scale) ^ d) ^ s /
            ((3 : ℝ) ^ Q.scale) ^ d * ((3 : ℝ) ^ Q.scale) ^ d) := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hL.ne']
  -- group the cubes by scale
  set ρ := P.reachScale z
  have hscale_maps : ∀ Q ∈ F.image P.part, Q.scale ∈ Finset.range (ρ + 1) := by
    intro Q hQ
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hQ
    exact Finset.mem_range.2 (Nat.lt_succ_of_le
      (P.scale_le_reachScale (Finset.mem_filter.1 hx).1 (Finset.mem_filter.1 hx).2))
  have hcount : ∀ k ∈ Finset.range (ρ + 1),
      (((F.image P.part).filter fun Q => Q.scale = k).card : ℝ) ≤ (2 * c + 2 : ℝ) ^ d := by
    intro k _
    have h := P.card_le_of_mem_thicken ((F.image P.part).filter fun Q => Q.scale = k)
      (fun Q hQ => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hQ).1
        exact ⟨x, P.cluster_subset (Finset.mem_filter.1 hx).1, rfl⟩)
      (z := z) (c := c) (k := k)
      (fun Q hQ => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hQ).1
        exact hreg x (Finset.mem_filter.1 hx).1
          (Finset.mem_inter.2 ⟨(Finset.mem_filter.1 hx).2, hz⟩))
      (fun Q hQ => (Finset.mem_filter.1 hQ).2)
    exact_mod_cast h
  have hb : (3 : ℝ) ≤ ((3 : ℝ) ^ d) ^ s := by
    have h3d : (3 : ℝ) ≤ (3 : ℝ) ^ d := by
      calc (3 : ℝ) = 3 ^ 1 := (pow_one 3).symm
        _ ≤ 3 ^ d := pow_le_pow_right₀ (by norm_num) hd
    calc (3 : ℝ) ≤ (3 : ℝ) ^ d := h3d
      _ ≤ ((3 : ℝ) ^ d) ^ s := Real.self_le_rpow_of_one_le (by linarith) hs
  have hpowk : ∀ k : ℕ, (((3 : ℝ) ^ k) ^ d) ^ s = (((3 : ℝ) ^ d) ^ s) ^ k := by
    intro k
    rw [Real.rpow_pow_comm (x := (3 : ℝ) ^ d) (by positivity) s k, ← pow_mul, ← pow_mul, mul_comm]
  have hstep2 : ∑ Q ∈ F.image P.part, (((3 : ℝ) ^ Q.scale) ^ d) ^ s ≤
      3 / 2 * (2 * c + 2 : ℝ) ^ d * (((3 : ℝ) ^ ρ) ^ d) ^ s := by
    calc ∑ Q ∈ F.image P.part, (((3 : ℝ) ^ Q.scale) ^ d) ^ s
        = ∑ k ∈ Finset.range (ρ + 1), ∑ Q ∈ (F.image P.part).filter (fun Q => Q.scale = k),
            (((3 : ℝ) ^ Q.scale) ^ d) ^ s :=
          (Finset.sum_fiberwise_of_maps_to hscale_maps _).symm
      _ = ∑ k ∈ Finset.range (ρ + 1),
            (((F.image P.part).filter fun Q => Q.scale = k).card : ℝ) *
              (((3 : ℝ) ^ d) ^ s) ^ k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          have hk : ∑ Q ∈ (F.image P.part).filter (fun Q => Q.scale = k),
              (((3 : ℝ) ^ Q.scale) ^ d) ^ s =
              ∑ _Q ∈ (F.image P.part).filter (fun Q => Q.scale = k), (((3 : ℝ) ^ d) ^ s) ^ k :=
            Finset.sum_congr rfl fun Q hQ => by rw [(Finset.mem_filter.1 hQ).2, hpowk]
          rw [hk, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ Finset.range (ρ + 1), (2 * c + 2 : ℝ) ^ d * (((3 : ℝ) ^ d) ^ s) ^ k :=
          Finset.sum_le_sum fun k hk =>
            mul_le_mul_of_nonneg_right (hcount k hk) (pow_nonneg (by linarith) _)
      _ = (2 * c + 2 : ℝ) ^ d * ∑ k ∈ Finset.range (ρ + 1), (((3 : ℝ) ^ d) ^ s) ^ k := by
          rw [Finset.mul_sum]
      _ ≤ (2 * c + 2 : ℝ) ^ d * (3 / 2 * (((3 : ℝ) ^ d) ^ s) ^ ρ) :=
          mul_le_mul_of_nonneg_left (sum_range_pow_le hb ρ) (by positivity)
      _ = 3 / 2 * (2 * c + 2 : ℝ) ^ d * (((3 : ℝ) ^ ρ) ^ d) ^ s := by
          rw [hpowk]
          ring
  rw [hW]
  calc ∑ x ∈ F, ((P.region x ∩ P.cluster).card : ℝ) ^ (s - 1)
      ≤ ∑ Q ∈ F.image P.part, ((3 : ℝ) ^ Q.scale) ^ d * reachTerm c s Q := hstep1
    _ = ((2 * c + 1 : ℝ) ^ d) ^ (s - 1) * ∑ Q ∈ F.image P.part, (((3 : ℝ) ^ Q.scale) ^ d) ^ s := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun Q _ => hterm Q
    _ ≤ ((2 * c + 1 : ℝ) ^ d) ^ (s - 1) * (3 / 2 * (2 * c + 2 : ℝ) ^ d *
          (((3 : ℝ) ^ ρ) ^ d) ^ s) :=
        mul_le_mul_of_nonneg_left hstep2 (Real.rpow_nonneg (by positivity) _)
    _ = _ := by ring

/-- **Armstrong and Dario, Lemma 3.2, with the reach scale.** If the region of each vertex of the
cluster lies in the `c · size`-neighbourhood of its partition cube, then for `1 ≤ s < ∞`,
`∑_{x ∈ C_*(U)} |w(x) - [w]_𝒫(x)|^s ≤ C^s ∑_{z ∈ C_*(U)} (3^{ρ(z)})^{sd} |∇w 1_{a≠0}|^s(z)`,
with `C = (3/2) (2c + 2)^d (2c + 1)^d 2√d` and `ρ(z) ≥ scale(□_𝒫(z))` the reach scale. -/
theorem sum_abs_sub_coarsen_rpow_le_reach {c : ℕ}
    (hreg : ∀ x ∈ P.cluster, P.region x ∩ P.cluster ⊆ ((P.part x).thicken c).vertices)
    (hd : 1 ≤ d) (w : Vertex d → ℝ) {s : ℝ} (hs : 1 ≤ s) :
    ∑ x ∈ P.cluster, |w x - P.coarsen w x| ^ s ≤
      (3 / 2 * (2 * c + 2 : ℝ) ^ d * (2 * c + 1 : ℝ) ^ d * (2 * √(d : ℝ))) ^ s *
        ∑ z ∈ P.cluster, ((3 : ℝ) ^ P.reachScale z) ^ (s * d) *
          gradNormIn (openGraph ω) P.cluster w z ^ s := by
  refine (P.sum_abs_sub_coarsen_rpow_le_errorWeight w hs).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun z hz => ?_
  have hg := gradNormIn_nonneg (openGraph ω) P.cluster w z
  have hV : vertexVariation ω P.cluster w z ^ s ≤
      (2 * √(d : ℝ)) ^ s * gradNormIn (openGraph ω) P.cluster w z ^ s := by
    rw [← Real.mul_rpow (by positivity) hg]
    exact Real.rpow_le_rpow (vertexVariation_nonneg _ _ _ _)
      (vertexVariation_le_gradNormIn ω P.cluster w z) (by linarith)
  have hW := P.errorWeight_le_reach hreg hd hs hz
  have hA : ((3 : ℝ) ^ P.reachScale z) ^ (s * d) = (((3 : ℝ) ^ P.reachScale z) ^ d) ^ s := by
    rw [mul_comm s, Real.rpow_mul (x := (3 : ℝ) ^ P.reachScale z) (by positivity),
      Real.rpow_natCast]
  rw [hA]
  set A : ℝ := 3 / 2 * (2 * c + 2 : ℝ) ^ d with hAdef
  set B : ℝ := (2 * c + 1 : ℝ) ^ d with hBdef
  set R : ℝ := (((3 : ℝ) ^ P.reachScale z) ^ d) ^ s with hRdef
  set e : ℝ := 2 * √(d : ℝ) with hedef
  set G : ℝ := gradNormIn (openGraph ω) P.cluster w z ^ s with hGdef
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hA1 : 1 ≤ A := by
    have : (1 : ℝ) ≤ (2 * c + 2 : ℝ) ^ d := one_le_pow₀ (by linarith)
    rw [hAdef]
    linarith
  have hB1 : 1 ≤ B := one_le_pow₀ (by linarith)
  have he : 0 ≤ e := by rw [hedef]; positivity
  have hR : 0 ≤ R := Real.rpow_nonneg (by positivity) _
  have hG : 0 ≤ G := Real.rpow_nonneg hg _
  have hV0 : 0 ≤ vertexVariation ω P.cluster w z ^ s :=
    Real.rpow_nonneg (vertexVariation_nonneg _ _ _ _) _
  have hAs : A ≤ A ^ s := Real.self_le_rpow_of_one_le hA1 hs
  have hBs : B ^ (s - 1) ≤ B ^ s := Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)
  have hBs0 : 0 ≤ B ^ (s - 1) := Real.rpow_nonneg (by linarith) _
  calc P.errorWeight s z * vertexVariation ω P.cluster w z ^ s
      ≤ (A * B ^ (s - 1) * R) * (e ^ s * G) :=
        mul_le_mul hW hV hV0 (mul_nonneg (mul_nonneg (by linarith) hBs0) hR)
    _ ≤ (A ^ s * B ^ s * R) * (e ^ s * G) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul hAs hBs hBs0 (Real.rpow_nonneg (by linarith) s)) hR)
          (mul_nonneg (Real.rpow_nonneg he s) hG)
    _ = (A * B * e) ^ s * (R * G) := by
        rw [Real.mul_rpow (x := A * B) (y := e) (mul_nonneg (by linarith) (by linarith)) he,
          Real.mul_rpow (x := A) (y := B) (by linarith) (by linarith)]
        ring

/-- The pair reach scale at `z`: the largest scale of the partition cube of the first vertex of
a pair of lattice neighbours in different partition cubes whose region contains `z`. -/
noncomputable def pairReachScale (z : Vertex d) : ℕ :=
  (P.edgesAcross.filter fun q => z ∈ P.pairRegion q.1 q.2).sup fun q => (P.part q.1).scale

theorem scale_le_pairReachScale {q : Vertex d × Vertex d} (hq : q ∈ P.edgesAcross)
    {z : Vertex d} (hz : z ∈ P.pairRegion q.1 q.2) : (P.part q.1).scale ≤ P.pairReachScale z :=
  Finset.le_sup (f := fun q => (P.part q.1).scale) (Finset.mem_filter.2 ⟨hq, hz⟩)

private theorem pow_sub_one_mul_rpow {b : ℝ} (hb : 0 < b) (hd : 1 ≤ d) (s : ℝ) :
    b ^ (d - 1) * (b ^ d) ^ (s - 1) = b ^ (s * d - 1) := by
  rw [← Real.rpow_natCast b (d - 1), ← Real.rpow_natCast b d, ← Real.rpow_mul hb.le,
    ← Real.rpow_add hb]
  congr 1
  rw [Nat.cast_sub hd, Nat.cast_one]
  ring

/-- **The weight of Lemma 3.3 with the pair reach scale.** If the pair regions lie in the
`c · size`-neighbourhoods of the partition cube of the first vertex, then for `d ≥ 2`,
`gradWeight s z ≤ (3/2) (2c + 2)^d 2d ((2c + 1)^d)^{s-1} (3^{ρ'(z)})^{sd-1}`. -/
theorem gradWeight_le_reach {c : ℕ}
    (hpair : ∀ q ∈ P.edgesAcross,
      P.pairRegion q.1 q.2 ∩ P.cluster ⊆ ((P.part q.1).thicken c).vertices)
    (hd : 2 ≤ d) {s : ℝ} (hs : 1 ≤ s) {z : Vertex d} (hz : z ∈ P.cluster) :
    P.gradWeight s z ≤ 3 / 2 * (2 * c + 2 : ℝ) ^ d * (2 * d) * ((2 * c + 1 : ℝ) ^ d) ^ (s - 1) *
      ((3 : ℝ) ^ P.pairReachScale z) ^ (s * d - 1) := by
  have hs1 : 0 ≤ s - 1 := by linarith
  have hd1 : 1 ≤ d := by omega
  set F := P.edgesAcross.filter fun q => z ∈ P.pairRegion q.1 q.2 with hF
  have hW : P.gradWeight s z =
      ∑ q ∈ F, ((P.pairRegion q.1 q.2 ∩ P.cluster).card : ℝ) ^ (s - 1) := by
    rw [gradWeight, hF, Finset.sum_filter]
  have hc : ∀ q ∈ F, ((P.pairRegion q.1 q.2 ∩ P.cluster).card : ℝ) ^ (s - 1) ≤
      reachTerm c s (P.part q.1) := by
    intro q hq
    have h1 := (Finset.card_le_card (hpair q (Finset.mem_filter.1 hq).1)).trans
      ((P.part q.1).card_thicken c).le
    have h2 : ((P.pairRegion q.1 q.2 ∩ P.cluster).card : ℝ) ≤
        (2 * c + 1 : ℝ) ^ d * ((3 : ℝ) ^ (P.part q.1).scale) ^ d := by
      calc ((P.pairRegion q.1 q.2 ∩ P.cluster).card : ℝ)
          ≤ (((2 * c + 1) ^ d * 3 ^ ((P.part q.1).scale * d) : ℕ) : ℝ) := by exact_mod_cast h1
        _ = (2 * c + 1 : ℝ) ^ d * ((3 : ℝ) ^ (P.part q.1).scale) ^ d := by push_cast; ring
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) h2 hs1
  have hF_maps : ∀ q ∈ F, P.part q.1 ∈ F.image (fun q => P.part q.1) := fun q hq =>
    Finset.mem_image_of_mem (fun q => P.part q.1) hq
  have hstep1 : ∑ q ∈ F, ((P.pairRegion q.1 q.2 ∩ P.cluster).card : ℝ) ^ (s - 1) ≤
      ∑ Q ∈ F.image (fun q => P.part q.1),
        (2 * d * ((3 : ℝ) ^ Q.scale) ^ (d - 1)) * reachTerm c s Q := by
    calc ∑ q ∈ F, ((P.pairRegion q.1 q.2 ∩ P.cluster).card : ℝ) ^ (s - 1)
        ≤ ∑ q ∈ F, reachTerm c s (P.part q.1) := Finset.sum_le_sum hc
      _ = ∑ Q ∈ F.image (fun q => P.part q.1),
            ∑ q ∈ F.filter (fun q => P.part q.1 = Q), reachTerm c s (P.part q.1) :=
          (Finset.sum_fiberwise_of_maps_to hF_maps _).symm
      _ ≤ _ := by
          refine Finset.sum_le_sum fun Q hQ => ?_
          obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.1 hQ
          have hconst : ∑ q ∈ F.filter (fun q => P.part q.1 = P.part q₀.1),
              reachTerm c s (P.part q.1) =
              ∑ _q ∈ F.filter (fun q => P.part q.1 = P.part q₀.1), reachTerm c s (P.part q₀.1) :=
            Finset.sum_congr rfl fun q hq => by rw [(Finset.mem_filter.1 hq).2]
          rw [hconst, Finset.sum_const, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ (reachTerm_nonneg c s _)
          have hsub : F.filter (fun q => P.part q.1 = P.part q₀.1) ⊆
              ((P.part q₀.1).toIntegerCube.vertices ×ˢ P.domain).filter fun q =>
                (nearestNeighborGraph d).Adj q.1 q.2 ∧ q.2 ∉ (P.part q₀.1).vertices := by
            intro q hq
            rw [Finset.mem_filter] at hq
            obtain ⟨hqF, hpart⟩ := hq
            have hqE := (Finset.mem_filter.1 hqF).1
            rw [edgesAcross, Finset.mem_filter, Finset.mem_product] at hqE
            obtain ⟨⟨hx, hy⟩, hadj, hne⟩ := hqE
            rw [Finset.mem_filter, Finset.mem_product, TriadicCube.mem_toIntegerCube_vertices,
              ← hpart]
            exact ⟨⟨P.mem_part _ hx, hy⟩, hadj,
              fun hmem => hne (P.part_eq_of_mem _ hx _ hmem).symm⟩
          have h1 := (Finset.card_le_card hsub).trans ((P.part q₀.1).card_exitPairs_le P.domain)
          calc ((F.filter fun q => P.part q.1 = P.part q₀.1).card : ℝ)
              ≤ ((2 * d * 3 ^ ((P.part q₀.1).scale * (d - 1)) : ℕ) : ℝ) := by exact_mod_cast h1
            _ = 2 * d * ((3 : ℝ) ^ (P.part q₀.1).scale) ^ (d - 1) := by push_cast; ring
  have hterm : ∀ Q : TriadicCube d, (2 * d * ((3 : ℝ) ^ Q.scale) ^ (d - 1)) * reachTerm c s Q =
      2 * d * ((2 * c + 1 : ℝ) ^ d) ^ (s - 1) * ((3 : ℝ) ^ Q.scale) ^ (s * d - 1) := by
    intro Q
    have hb : (0 : ℝ) < (3 : ℝ) ^ Q.scale := by positivity
    unfold reachTerm
    rw [Real.mul_rpow (x := (2 * c + 1 : ℝ) ^ d) (y := ((3 : ℝ) ^ Q.scale) ^ d) (by positivity)
      (by positivity), ← pow_sub_one_mul_rpow hb hd1 s]
    ring
  set ρ := P.pairReachScale z
  have hscale_maps : ∀ Q ∈ F.image (fun q => P.part q.1), Q.scale ∈ Finset.range (ρ + 1) := by
    intro Q hQ
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hQ
    exact Finset.mem_range.2 (Nat.lt_succ_of_le
      (P.scale_le_pairReachScale (Finset.mem_filter.1 hq).1 (Finset.mem_filter.1 hq).2))
  have hcount : ∀ k ∈ Finset.range (ρ + 1),
      (((F.image fun q => P.part q.1).filter fun Q => Q.scale = k).card : ℝ) ≤
        (2 * c + 2 : ℝ) ^ d := by
    intro k _
    have h := P.card_le_of_mem_thicken ((F.image fun q => P.part q.1).filter fun Q => Q.scale = k)
      (fun Q hQ => by
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hQ).1
        have hqE := (Finset.mem_filter.1 hq).1
        rw [edgesAcross, Finset.mem_filter, Finset.mem_product] at hqE
        exact ⟨q.1, hqE.1.1, rfl⟩)
      (z := z) (c := c) (k := k)
      (fun Q hQ => by
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hQ).1
        exact hpair q (Finset.mem_filter.1 hq).1
          (Finset.mem_inter.2 ⟨(Finset.mem_filter.1 hq).2, hz⟩))
      (fun Q hQ => (Finset.mem_filter.1 hQ).2)
    exact_mod_cast h
  have hb : (3 : ℝ) ≤ (3 : ℝ) ^ (s * d - 1) := by
    have hsd : (1 : ℝ) ≤ s * d - 1 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      nlinarith
    calc (3 : ℝ) = 3 ^ (1 : ℝ) := (Real.rpow_one 3).symm
      _ ≤ 3 ^ (s * d - 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hsd
  have hpowk : ∀ k : ℕ, ((3 : ℝ) ^ k) ^ (s * d - 1) = ((3 : ℝ) ^ (s * d - 1)) ^ k := fun k =>
    (Real.rpow_pow_comm (x := (3 : ℝ)) (by norm_num) (s * d - 1) k).symm
  have hstep2 : ∑ Q ∈ F.image (fun q => P.part q.1), ((3 : ℝ) ^ Q.scale) ^ (s * d - 1) ≤
      3 / 2 * (2 * c + 2 : ℝ) ^ d * ((3 : ℝ) ^ ρ) ^ (s * d - 1) := by
    calc ∑ Q ∈ F.image (fun q => P.part q.1), ((3 : ℝ) ^ Q.scale) ^ (s * d - 1)
        = ∑ k ∈ Finset.range (ρ + 1),
            ∑ Q ∈ (F.image fun q => P.part q.1).filter (fun Q => Q.scale = k),
              ((3 : ℝ) ^ Q.scale) ^ (s * d - 1) :=
          (Finset.sum_fiberwise_of_maps_to hscale_maps _).symm
      _ = ∑ k ∈ Finset.range (ρ + 1),
            (((F.image fun q => P.part q.1).filter fun Q => Q.scale = k).card : ℝ) *
              ((3 : ℝ) ^ (s * d - 1)) ^ k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          have hk : ∑ Q ∈ (F.image fun q => P.part q.1).filter (fun Q => Q.scale = k),
              ((3 : ℝ) ^ Q.scale) ^ (s * d - 1) =
              ∑ _Q ∈ (F.image fun q => P.part q.1).filter (fun Q => Q.scale = k),
                ((3 : ℝ) ^ (s * d - 1)) ^ k :=
            Finset.sum_congr rfl fun Q hQ => by rw [(Finset.mem_filter.1 hQ).2, hpowk]
          rw [hk, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ Finset.range (ρ + 1), (2 * c + 2 : ℝ) ^ d * ((3 : ℝ) ^ (s * d - 1)) ^ k :=
          Finset.sum_le_sum fun k hk =>
            mul_le_mul_of_nonneg_right (hcount k hk) (pow_nonneg (by linarith) _)
      _ = (2 * c + 2 : ℝ) ^ d * ∑ k ∈ Finset.range (ρ + 1), ((3 : ℝ) ^ (s * d - 1)) ^ k := by
          rw [Finset.mul_sum]
      _ ≤ (2 * c + 2 : ℝ) ^ d * (3 / 2 * ((3 : ℝ) ^ (s * d - 1)) ^ ρ) :=
          mul_le_mul_of_nonneg_left (sum_range_pow_le hb ρ) (by positivity)
      _ = 3 / 2 * (2 * c + 2 : ℝ) ^ d * ((3 : ℝ) ^ ρ) ^ (s * d - 1) := by
          rw [hpowk]
          ring
  rw [hW]
  calc ∑ q ∈ F, ((P.pairRegion q.1 q.2 ∩ P.cluster).card : ℝ) ^ (s - 1)
      ≤ ∑ Q ∈ F.image (fun q => P.part q.1),
          (2 * d * ((3 : ℝ) ^ Q.scale) ^ (d - 1)) * reachTerm c s Q := hstep1
    _ = 2 * d * ((2 * c + 1 : ℝ) ^ d) ^ (s - 1) *
          ∑ Q ∈ F.image (fun q => P.part q.1), ((3 : ℝ) ^ Q.scale) ^ (s * d - 1) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun Q _ => hterm Q
    _ ≤ 2 * d * ((2 * c + 1 : ℝ) ^ d) ^ (s - 1) *
          (3 / 2 * (2 * c + 2 : ℝ) ^ d * ((3 : ℝ) ^ ρ) ^ (s * d - 1)) :=
        mul_le_mul_of_nonneg_left hstep2 (by positivity)
    _ = _ := by ring

/-- **Armstrong and Dario, Lemma 3.3, with the pair reach scale.** If the pair regions lie in the
`c · size`-neighbourhoods of the partition cube of the first vertex, then for `d ≥ 2` and
`1 ≤ s < ∞`,
`∑_{x ∈ cl_𝒫(U)} |∇[w]_𝒫|^s(x) ≤ C^s ∑_{z ∈ C_*(U)} (3^{ρ'(z)})^{sd-1} |∇w 1_{a≠0}|^s(z)`,
with `C = 2d (3/2) (2c + 2)^d (2c + 1)^d 2√d` and `ρ'` the pair reach scale. -/
theorem sum_gradNormIn_coarsen_rpow_le_reach {c : ℕ}
    (hpair : ∀ q ∈ P.edgesAcross,
      P.pairRegion q.1 q.2 ∩ P.cluster ⊆ ((P.part q.1).thicken c).vertices)
    (hd : 2 ≤ d) (w : Vertex d → ℝ) {s : ℝ} (hs : 1 ≤ s) :
    ∑ x ∈ P.domain, gradNormIn (nearestNeighborGraph d) P.domain (P.coarsen w) x ^ s ≤
      (2 * d * (3 / 2 * (2 * c + 2 : ℝ) ^ d) * (2 * c + 1 : ℝ) ^ d * (2 * √(d : ℝ))) ^ s *
        ∑ z ∈ P.cluster, ((3 : ℝ) ^ P.pairReachScale z) ^ (s * d - 1) *
          gradNormIn (openGraph ω) P.cluster w z ^ s := by
  refine (P.sum_gradNormIn_coarsen_rpow_le_gradWeight w hs).trans ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun z hz => ?_
  have hg := gradNormIn_nonneg (openGraph ω) P.cluster w z
  have hV : vertexVariation ω P.cluster w z ^ s ≤
      (2 * √(d : ℝ)) ^ s * gradNormIn (openGraph ω) P.cluster w z ^ s := by
    rw [← Real.mul_rpow (by positivity) hg]
    exact Real.rpow_le_rpow (vertexVariation_nonneg _ _ _ _)
      (vertexVariation_le_gradNormIn ω P.cluster w z) (by linarith)
  have hV0 : 0 ≤ vertexVariation ω P.cluster w z ^ s :=
    Real.rpow_nonneg (vertexVariation_nonneg _ _ _ _) _
  have hW := P.gradWeight_le_reach hpair hd hs hz
  have hW0 := P.gradWeight_nonneg s z
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set D : ℝ := 2 * d with hDdef
  set A : ℝ := 3 / 2 * (2 * c + 2 : ℝ) ^ d with hAdef
  set B : ℝ := (2 * c + 1 : ℝ) ^ d with hBdef
  set R : ℝ := ((3 : ℝ) ^ P.pairReachScale z) ^ (s * d - 1) with hRdef
  set e : ℝ := 2 * √(d : ℝ) with hedef
  set G : ℝ := gradNormIn (openGraph ω) P.cluster w z ^ s with hGdef
  have hD : 0 < D := by rw [hDdef]; linarith
  have hA1 : 1 ≤ A := by
    have : (1 : ℝ) ≤ (2 * c + 2 : ℝ) ^ d := one_le_pow₀ (by linarith)
    rw [hAdef]
    linarith
  have hB1 : 1 ≤ B := one_le_pow₀ (by linarith)
  have he : 0 ≤ e := by rw [hedef]; positivity
  have hR : 0 ≤ R := Real.rpow_nonneg (by positivity) _
  have hG : 0 ≤ G := Real.rpow_nonneg hg _
  have hAs : A ≤ A ^ s := Real.self_le_rpow_of_one_le hA1 hs
  have hBs : B ^ (s - 1) ≤ B ^ s := Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)
  have hBs0 : 0 ≤ B ^ (s - 1) := Real.rpow_nonneg (by linarith) _
  have hDs0 : 0 ≤ D ^ s := Real.rpow_nonneg hD.le _
  have hDs : D ^ (s - 1) * D = D ^ s := by
    rw [Real.rpow_sub_one hD.ne' s, div_mul_cancel₀ _ hD.ne']
  calc D ^ (s - 1) * (P.gradWeight s z * vertexVariation ω P.cluster w z ^ s)
      ≤ D ^ (s - 1) * ((A * D * B ^ (s - 1) * R) * (e ^ s * G)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hW hV hV0
          (mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hD.le) hBs0) hR))
          (Real.rpow_nonneg hD.le _)
    _ = (D ^ (s - 1) * D) * A * B ^ (s - 1) * e ^ s * (R * G) := by ring
    _ ≤ D ^ s * A ^ s * B ^ s * e ^ s * (R * G) := by
        rw [hDs]
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul (mul_le_mul_of_nonneg_left hAs hDs0) hBs hBs0
            (mul_nonneg hDs0 (Real.rpow_nonneg (by linarith) s)))
          (Real.rpow_nonneg he s)) (mul_nonneg hR hG)
    _ = (D * A * B * e) ^ s * (R * G) := by
        rw [Real.mul_rpow (x := D * A * B) (y := e)
            (mul_nonneg (mul_nonneg hD.le (by linarith)) (by linarith)) he,
          Real.mul_rpow (x := D * A) (y := B) (mul_nonneg hD.le (by linarith)) (by linarith),
          Real.mul_rpow (x := D) (y := A) hD.le (by linarith)]

end CoarseData

end Rigidity.Percolation
