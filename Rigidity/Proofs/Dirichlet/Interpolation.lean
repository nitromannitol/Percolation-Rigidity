import Rigidity.Proofs.Cluster.CoarseInequalities
import Rigidity.Proofs.Dirichlet.Averages
import Rigidity.Proofs.Dirichlet.MesoscopicInterpolation

/-!
# The boundary interpolation of the coarsened function

Given coarse-graining data `𝒫` on a cluster, a function `u` and a set `B` of vertices of the
cluster (the vertices of `C_*(□_m)` on `∂□_m`), the boundary interpolation `w̃` equals `u` on `B`
and the coarsened function `[u]_𝒫` elsewhere. On every lattice edge of the domain,
`|∇w̃| ≤ |∇[u]_𝒫| + |w̃ − [u]_𝒫|` at the two endpoints, so for `s ≥ 1`
`Σ_{edges} |∇w̃|^s ≤ 3^{s-1} (d 2^{s/2} Σ_x |∇[u]_𝒫|^s(x) + 2 d Σ_{z ∈ C_*} |u(z) − [u]_𝒫(z)|^s)`,
and Lemmas 3.2 and 3.3 of Armstrong–Dario with the weighted Hölder inequality bound the right side
by the moments of the partition sizes times `(Σ |∇u 1_{a≠0}|^p)^{s/p}`.

This is Armstrong–Dario, Lemma 6.4 (iii), on the lattice: the function `w̃` is the boundary
datum `w` of the homogenized problem itself (no convolution with a mollifier), so parts (i) and
(ii) of the lemma, which compare `w` with `w̃`, are not needed. The minimal-scale hypothesis
`3^m ≥ 𝓜_t(𝒬)` of the source enters only through the moments of the partition sizes, which are
kept as an explicit factor.
-/

open Finset LatticeProb LatticeProb.Percolation
open scoped Classical

namespace Rigidity.Dirichlet

open Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- The boundary interpolation `w̃ = u` on `B` and `w̃ = [u]_𝒫` elsewhere. -/
def boundaryInterpolation (P : CoarseData d ω) (B : Finset (Vertex d)) (u : Vertex d → ℝ)
    (x : Vertex d) : ℝ :=
  if x ∈ B then u x else P.coarsen u x

theorem boundaryInterpolation_of_mem (P : CoarseData d ω) {B : Finset (Vertex d)}
    (u : Vertex d → ℝ) {x : Vertex d} (hx : x ∈ B) : boundaryInterpolation P B u x = u x := by
  simp [boundaryInterpolation, hx]

theorem boundaryInterpolation_of_not_mem (P : CoarseData d ω) {B : Finset (Vertex d)}
    (u : Vertex d → ℝ) {x : Vertex d} (hx : x ∉ B) :
    boundaryInterpolation P B u x = P.coarsen u x := by
  simp [boundaryInterpolation, hx]

/-- A difference along a lattice edge of the domain is at most `√2` times the magnitude of the
gradient (Armstrong–Dario (1.4)). -/
theorem abs_sub_le_sqrt_two_mul_gradNormIn (S : Finset (Vertex d)) (f : Vertex d → ℝ)
    {x : Vertex d} (j : Fin d) (hx : x + unit j ∈ S) :
    |f (x + unit j) - f x| ≤ √2 * gradNormIn (nearestNeighborGraph d) S f x := by
  have hadj : (nearestNeighborGraph d).Adj x (x + unit j) := ⟨j, Or.inl rfl⟩
  have hterm : (f x - f (x + unit j)) ^ 2 ≤
      ∑ y ∈ S, if (nearestNeighborGraph d).Adj x y then (f x - f y) ^ 2 else 0 := by
    have := Finset.single_le_sum (f := fun y =>
      if (nearestNeighborGraph d).Adj x y then (f x - f y) ^ 2 else 0)
      (fun y _ => by split_ifs <;> positivity) hx
    simpa [hadj] using this
  rw [gradNormIn, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    show (2 : ℝ) * (1 / 2 * ∑ y ∈ S, if (nearestNeighborGraph d).Adj x y then (f x - f y) ^ 2
      else 0) = ∑ y ∈ S, if (nearestNeighborGraph d).Adj x y then (f x - f y) ^ 2 else 0 by ring,
    ← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  calc (f (x + unit j) - f x) ^ 2 = (f x - f (x + unit j)) ^ 2 := by ring
    _ ≤ _ := hterm

/-- **The `L^s` norm of the gradient of the boundary interpolation**: for `B ⊆ C_*` and `s ≥ 1`,
`Σ_{x∈D} Σ_j [x + e_j ∈ D] |∇_j w̃(x)|^s ≤
  3^{s-1} (d 2^{s/2} Σ_{x∈D} |∇[u]_𝒫|^s(x) + 2 d Σ_{z∈C_*} |u(z) − [u]_𝒫(z)|^s)`,
with `D` the domain and `|∇[u]_𝒫|` the magnitude (1.4) on the lattice. -/
theorem sum_abs_grad_boundaryInterpolation_rpow_le (P : CoarseData d ω) {B : Finset (Vertex d)}
    (hB : B ⊆ P.cluster) (u : Vertex d → ℝ) {s : ℝ} (hs : 1 ≤ s) :
    ∑ x ∈ P.domain, ∑ j : Fin d, (if x + unit j ∈ P.domain then
        |boundaryInterpolation P B u (x + unit j) - boundaryInterpolation P B u x| ^ s else 0) ≤
      (3 : ℝ) ^ (s - 1) * ((d : ℝ) * (2 : ℝ) ^ (s / 2) *
          ∑ x ∈ P.domain, gradNormIn (nearestNeighborGraph d) P.domain (P.coarsen u) x ^ s +
        2 * d * ∑ z ∈ P.cluster, |u z - P.coarsen u z| ^ s) := by
  classical
  have hs0 : 0 ≤ s := by linarith
  set D := P.domain
  set c := P.coarsen u
  set δ : Vertex d → ℝ := fun z => if z ∈ B then u z - c z else 0
  set g : Vertex d → ℝ := fun x => gradNormIn (nearestNeighborGraph d) D c x
  have hδ : ∀ z, boundaryInterpolation P B u z = c z + δ z := fun z => by
    simp only [boundaryInterpolation, δ]
    split_ifs <;> ring
  have hδsum : ∀ T : Finset (Vertex d), ∑ z ∈ T, |δ z| ^ s ≤ ∑ z ∈ P.cluster, |u z - c z| ^ s := by
    intro T
    calc ∑ z ∈ T, |δ z| ^ s = ∑ z ∈ T.filter (· ∈ B), |u z - c z| ^ s := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun z _ => ?_
          simp only [δ]
          split_ifs
          · rfl
          · simp [Real.zero_rpow (show s ≠ 0 by linarith)]
      _ ≤ ∑ z ∈ P.cluster, |u z - c z| ^ s :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun z hz => hB (Finset.mem_filter.mp hz).2)
            fun _ _ _ => by positivity
  have hsqrt : (√2 : ℝ) ^ s = (2 : ℝ) ^ (s / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hg0 : ∀ x, 0 ≤ g x := fun x => gradNormIn_nonneg _ _ _ _
  -- pointwise bound on an edge of the domain
  have hpt : ∀ x ∈ D, ∀ j : Fin d, x + unit j ∈ D →
      |boundaryInterpolation P B u (x + unit j) - boundaryInterpolation P B u x| ^ s ≤
        (3 : ℝ) ^ (s - 1) * ((2 : ℝ) ^ (s / 2) * g x ^ s + |δ (x + unit j)| ^ s + |δ x| ^ s) := by
    intro x _ j hxj
    rw [hδ, hδ]
    have hsplit : c (x + unit j) + δ (x + unit j) - (c x + δ x) =
        (c (x + unit j) - c x) + δ (x + unit j) + (-δ x) := by ring
    rw [hsplit]
    have h1 := abs_sub_le_sqrt_two_mul_gradNormIn D c j hxj
    have habs : |(c (x + unit j) - c x) + δ (x + unit j) + (-δ x)| ≤
        √2 * g x + |δ (x + unit j)| + |δ x| := by
      calc |(c (x + unit j) - c x) + δ (x + unit j) + (-δ x)|
          ≤ |(c (x + unit j) - c x) + δ (x + unit j)| + |-δ x| := abs_add_le _ _
        _ ≤ |c (x + unit j) - c x| + |δ (x + unit j)| + |-δ x| := by
            linarith [abs_add_le (c (x + unit j) - c x) (δ (x + unit j))]
        _ ≤ √2 * g x + |δ (x + unit j)| + |δ x| := by rw [abs_neg]; linarith
    calc |(c (x + unit j) - c x) + δ (x + unit j) + (-δ x)| ^ s
        ≤ (√2 * g x + |δ (x + unit j)| + |δ x|) ^ s :=
          Real.rpow_le_rpow (abs_nonneg _) habs hs0
      _ ≤ (3 : ℝ) ^ (s - 1) * ((√2 * g x) ^ s + |δ (x + unit j)| ^ s + |δ x| ^ s) :=
          add_add_rpow_le_of_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (hg0 x))
            (abs_nonneg _) (abs_nonneg _) hs
      _ = (3 : ℝ) ^ (s - 1) * ((2 : ℝ) ^ (s / 2) * g x ^ s + |δ (x + unit j)| ^ s +
            |δ x| ^ s) := by
          rw [Real.mul_rpow (Real.sqrt_nonneg 2) (hg0 x), hsqrt]
  -- the translated sums of `δ`
  have hshift : ∀ j : Fin d, ∑ x ∈ D, (if x + unit j ∈ D then |δ (x + unit j)| ^ s else 0) ≤
      ∑ z ∈ D, |δ z| ^ s := by
    intro j
    rw [← Finset.sum_filter]
    calc ∑ x ∈ D.filter (fun x => x + unit j ∈ D), |δ (x + unit j)| ^ s
        = ∑ y ∈ (D.filter (fun x => x + unit j ∈ D)).map (addRightEmbedding (unit j)),
            |δ y| ^ s := by
          rw [Finset.sum_map]
          rfl
      _ ≤ ∑ z ∈ D, |δ z| ^ s :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => by
            obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
            exact (Finset.mem_filter.mp hx).2) fun _ _ _ => by positivity
  have hA : ∑ x ∈ D, ∑ _j : Fin d, (2 : ℝ) ^ (s / 2) * g x ^ s =
      (d : ℝ) * (2 : ℝ) ^ (s / 2) * ∑ x ∈ D, g x ^ s := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hE : ∑ x ∈ D, ∑ j : Fin d, (if x + unit j ∈ D then |δ (x + unit j)| ^ s else 0) ≤
      (d : ℝ) * ∑ z ∈ P.cluster, |u z - c z| ^ s := by
    rw [Finset.sum_comm]
    calc ∑ j : Fin d, ∑ x ∈ D, (if x + unit j ∈ D then |δ (x + unit j)| ^ s else 0)
        ≤ ∑ _j : Fin d, ∑ z ∈ P.cluster, |u z - c z| ^ s :=
          Finset.sum_le_sum fun j _ => (hshift j).trans (hδsum D)
      _ = (d : ℝ) * ∑ z ∈ P.cluster, |u z - c z| ^ s := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hF : ∑ x ∈ D, ∑ _j : Fin d, |δ x| ^ s ≤ (d : ℝ) * ∑ z ∈ P.cluster, |u z - c z| ^ s := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hδsum D) (Nat.cast_nonneg d)
  have hsplit : ∑ x ∈ D, ∑ j : Fin d, (3 : ℝ) ^ (s - 1) * ((2 : ℝ) ^ (s / 2) * g x ^ s +
      (if x + unit j ∈ D then |δ (x + unit j)| ^ s else 0) + |δ x| ^ s) =
      (3 : ℝ) ^ (s - 1) * (∑ x ∈ D, ∑ _j : Fin d, (2 : ℝ) ^ (s / 2) * g x ^ s +
        ∑ x ∈ D, ∑ j : Fin d, (if x + unit j ∈ D then |δ (x + unit j)| ^ s else 0) +
        ∑ x ∈ D, ∑ _j : Fin d, |δ x| ^ s) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  calc ∑ x ∈ D, ∑ j : Fin d, (if x + unit j ∈ D then
        |boundaryInterpolation P B u (x + unit j) - boundaryInterpolation P B u x| ^ s else 0)
      ≤ ∑ x ∈ D, ∑ j : Fin d, (3 : ℝ) ^ (s - 1) * ((2 : ℝ) ^ (s / 2) * g x ^ s +
          (if x + unit j ∈ D then |δ (x + unit j)| ^ s else 0) + |δ x| ^ s) := by
        refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun j _ => ?_
        split_ifs with hxj
        · exact hpt x hx j hxj
        · exact mul_nonneg (by positivity) (add_nonneg (add_nonneg (mul_nonneg (by positivity)
            (Real.rpow_nonneg (hg0 x) _)) le_rfl) (by positivity))
    _ = (3 : ℝ) ^ (s - 1) * (∑ x ∈ D, ∑ _j : Fin d, (2 : ℝ) ^ (s / 2) * g x ^ s +
          ∑ x ∈ D, ∑ j : Fin d, (if x + unit j ∈ D then |δ (x + unit j)| ^ s else 0) +
          ∑ x ∈ D, ∑ _j : Fin d, |δ x| ^ s) := hsplit
    _ ≤ (3 : ℝ) ^ (s - 1) * ((d : ℝ) * (2 : ℝ) ^ (s / 2) * ∑ x ∈ D, g x ^ s +
          2 * d * ∑ z ∈ P.cluster, |u z - c z| ^ s) := by
        rw [hA]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith [hE, hF]

/-- **Armstrong–Dario, Lemma 6.4 (iii), on the lattice**: for `B ⊆ C_*`, `1 ≤ s < p`, the
bounded-overlap hypotheses of Lemmas 3.2 and 3.3 and a normalization `V > 0` (the volume
`|□_m|`), the normalized `L^s` norm of `∇w̃` is at most
`3^{s-1} (d 2^{s/2} C₃^s 𝔐_{sd−1} + 2 d C₂^s 𝔐_{sd}) (V⁻¹ Σ_{C_*} |∇u 1_{a≠0}|^p)^{s/p}`,
where `𝔐_a = (V⁻¹ Σ_{z ∈ C_*} size(□_𝒫(z))^{a p/(p − s)})^{1 − s/p}` are the moments of the
partition sizes and `C₃ = 2 d N K 3^{md} 2√d`, `C₂ = N' K' 3^{m'd} 2√d` the constants of
Lemmas 3.3 and 3.2. -/
theorem sum_abs_grad_boundaryInterpolation_rpow_div_le (P : CoarseData d ω)
    {B : Finset (Vertex d)} (hB : B ⊆ P.cluster) (u : Vertex d → ℝ) {K N m K' N' m' : ℕ}
    (h3 : P.PairOverlap K N m) (hK : 1 ≤ K) (hN : 1 ≤ N) (h2 : P.RegionOverlap K' N' m')
    (hK' : 1 ≤ K') (hN' : 1 ≤ N') (hd : 1 ≤ d) {s p : ℝ} (hs : 1 ≤ s) (hsp : s < p) {V : ℝ}
    (hV : 0 < V) :
    (∑ x ∈ P.domain, ∑ j : Fin d, (if x + unit j ∈ P.domain then
        |boundaryInterpolation P B u (x + unit j) - boundaryInterpolation P B u x| ^ s
        else 0)) / V ≤
      (3 : ℝ) ^ (s - 1) * ((d : ℝ) * (2 : ℝ) ^ (s / 2) *
          (2 * (d : ℝ) * N * K * 3 ^ (m * d) * (2 * √(d : ℝ))) ^ s *
          ((∑ z ∈ P.cluster, (((3 : ℝ) ^ (P.part z).scale) ^ (s * d - 1)) ^ (p / (p - s))) /
            V) ^ (1 - s / p) +
        2 * d * ((N' : ℝ) * K' * 3 ^ (m' * d) * (2 * √(d : ℝ))) ^ s *
          ((∑ z ∈ P.cluster, (((3 : ℝ) ^ (P.part z).scale) ^ (s * d)) ^ (p / (p - s))) /
            V) ^ (1 - s / p)) *
        ((∑ z ∈ P.cluster, gradNormIn (openGraph ω) P.cluster u z ^ p) / V) ^ (s / p) := by
  have hs0 : 0 < s := by linarith
  set G : Vertex d → ℝ := fun z => gradNormIn (openGraph ω) P.cluster u z
  have hG : ∀ z, 0 ≤ G z := fun z => gradNormIn_nonneg _ _ _ _
  have hGabs : ∀ z (t : ℝ), |G z| ^ t = G z ^ t := fun z t => by rw [abs_of_nonneg (hG z)]
  have hstep := sum_abs_grad_boundaryInterpolation_rpow_le P hB u hs
  have hL3 := P.sum_gradNormIn_coarsen_rpow_le h3 hK hN hd u hs
  have hL2 := P.sum_abs_sub_coarsen_rpow_le h2 hK' hN' u hs
  have hW3 := sum_mul_rpow_div_le P.cluster (fun z => ((3 : ℝ) ^ (P.part z).scale) ^ (s * d - 1))
    G (fun z _ => by positivity) hs0 hsp hV
  have hW2 := sum_mul_rpow_div_le P.cluster (fun z => ((3 : ℝ) ^ (P.part z).scale) ^ (s * d))
    G (fun z _ => by positivity) hs0 hsp hV
  simp only [hGabs] at hW3 hW2
  set C₃ : ℝ := (2 * (d : ℝ) * N * K * 3 ^ (m * d) * (2 * √(d : ℝ))) ^ s
  set C₂ : ℝ := ((N' : ℝ) * K' * 3 ^ (m' * d) * (2 * √(d : ℝ))) ^ s
  set S₃ : ℝ := ∑ z ∈ P.cluster, ((3 : ℝ) ^ (P.part z).scale) ^ (s * d - 1) * G z ^ s
  set S₂ : ℝ := ∑ z ∈ P.cluster, ((3 : ℝ) ^ (P.part z).scale) ^ (s * d) * G z ^ s
  have hC₃ : 0 ≤ C₃ := by positivity
  have hC₂ : 0 ≤ C₂ := by positivity
  have h3s : 0 ≤ (3 : ℝ) ^ (s - 1) := by positivity
  have hA : 0 ≤ (d : ℝ) * (2 : ℝ) ^ (s / 2) := by positivity
  calc (∑ x ∈ P.domain, ∑ j : Fin d, (if x + unit j ∈ P.domain then
        |boundaryInterpolation P B u (x + unit j) - boundaryInterpolation P B u x| ^ s
        else 0)) / V
      ≤ (3 : ℝ) ^ (s - 1) * ((d : ℝ) * (2 : ℝ) ^ (s / 2) * (C₃ * S₃) + 2 * d * (C₂ * S₂)) / V := by
        refine div_le_div_of_nonneg_right (hstep.trans ?_) hV.le
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) h3s
        · exact mul_le_mul_of_nonneg_left hL3 hA
        · exact mul_le_mul_of_nonneg_left hL2 (by positivity)
    _ = (3 : ℝ) ^ (s - 1) * ((d : ℝ) * (2 : ℝ) ^ (s / 2) * C₃ * (S₃ / V) +
          2 * d * C₂ * (S₂ / V)) := by
        field_simp
    _ ≤ _ := by
        rw [mul_assoc ((3 : ℝ) ^ (s - 1))]
        refine mul_le_mul_of_nonneg_left ?_ h3s
        rw [add_mul]
        refine add_le_add ?_ ?_
        · rw [mul_assoc ((d : ℝ) * (2 : ℝ) ^ (s / 2) * C₃)]
          exact mul_le_mul_of_nonneg_left hW3 (by positivity)
        · rw [mul_assoc (2 * (d : ℝ) * C₂)]
          exact mul_le_mul_of_nonneg_left hW2 (by positivity)

end Rigidity.Dirichlet
