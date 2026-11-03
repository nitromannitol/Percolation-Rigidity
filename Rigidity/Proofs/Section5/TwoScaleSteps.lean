import Rigidity.Steps.Section5.TwoScaleExpansion
import Rigidity.Proofs.Section5.ConnectingSet
import Rigidity.Proofs.Section5.GreenSymmetry

/-! # Proposition 5.8: the lattice and corrector steps of the two-scale expansion

Proofs of four steps of the carving of Proposition 5.8 (`Rigidity/Steps/Section5/TwoScaleExpansion.lean`;
corrected draft L1657-1727):

* `normalizedGreenSymmetryStep` (step:5.8-symmetry): `greenSymmetry` (`GreenSymmetry p`, the
  symmetry of `H = G - K(y)`, corrected draft L459, C13/C14);
* `connectedSetRadiusStep` (step:5.8-support): along a path inside a connected finite set `V` the
  `ℓ¹` norm changes by at most one per edge, and a path has fewer than `|V|` edges;
* `forwardDiffEdgeStep` (step:5.8-edge): an open edge is `(z, z + eⱼ)` with `z` one of its
  endpoints, and the increment of `g - Σᵢ ℓᵢ D z i` along it is the `j`-th term of the left side of
  eq. `green-gradient-homogenization`;
* `correctedPlaneGradientStep` (step:5.8-corrector): Theorem 2.5 (`CorrectorQuantitativeInput`) with
  `α = 1` at the origin bounds the gradient of the corrector `χ_{eᵢ} = ℓ_{eᵢ} - xᵢ` on the ball of
  radius `M + |a| + 2` by `C (M + |a| + 2)`, so `Λ = 1 + C (M + 2)` works; `Λ` is `O_{s/2}` since
  `(1 + C (M + 2))^{s/2} ≤ (1 + C)^{2s} + 1 + (M / C)^s`. -/

open MeasureTheory LatticeProb.Percolation Rigidity.Section2 Rigidity.Section5 Rigidity.External
  Rigidity.Steps.Section5

namespace Rigidity.Proofs.Section5

/-! ### step:5.8-symmetry -/

/-- **step:5.8-symmetry** (C13, C14): almost surely the normalized Green function
`H(x, y) = G(x, y) - K(y)` is symmetric; this is `GreenSymmetry p`. -/
theorem normalizedGreenSymmetryStep : NormalizedGreenSymmetryStep :=
  fun hGQ _ hpc hp1 => greenSymmetry hGQ hpc hp1

/-! ### Lattice neighbours -/

/-- Neighbours in an open component are lattice neighbours. -/
private theorem exists_unit_of_adj {ω : Configuration 2} {C : OpenComponent ω} {a b : C}
    (hab : (componentGraph C).Adj a b) :
    ∃ j : Fin 2, b.val = a.val + LatticeProb.unit j ∨ a.val = b.val + LatticeProb.unit j :=
  openGraph_le ω ((C.toSimpleGraph_adj a.2 b.2).1 hab)

/-- A unit step changes each coordinate by at most one and the `ℓ¹` norm by at most one. -/
private theorem l1_add_unit_le (x : Vertex 2) (j : Fin 2) :
    l1 (x + LatticeProb.unit j) ≤ l1 x + 1 ∧ l1 x ≤ l1 (x + LatticeProb.unit j) + 1 := by
  have hu : ∀ i, ((x + LatticeProb.unit j) i : ℝ) = (x i : ℝ) + if i = j then 1 else 0 := by
    intro i
    simp only [LatticeProb.unit, Pi.add_apply, Pi.single_apply]
    split_ifs <;> simp
  have key : ∀ i, |((x + LatticeProb.unit j) i : ℝ)| ≤ |(x i : ℝ)| + (if i = j then 1 else 0) ∧
      |(x i : ℝ)| ≤ |((x + LatticeProb.unit j) i : ℝ)| + (if i = j then 1 else 0) := by
    intro i
    rw [hu i]
    have h0 : (0 : ℝ) ≤ if i = j then 1 else 0 := by split_ifs <;> norm_num
    refine ⟨(abs_add_le _ _).trans (by rw [abs_of_nonneg h0]), ?_⟩
    have := abs_sub_abs_le_abs_sub (x i : ℝ) ((x i : ℝ) + if i = j then 1 else 0)
    rw [show (x i : ℝ) - ((x i : ℝ) + if i = j then 1 else 0) = -(if i = j then 1 else 0) by ring,
      abs_neg, abs_of_nonneg h0] at this
    linarith
  have hsum : ∑ i : Fin 2, (if i = j then (1 : ℝ) else 0) = 1 := by simp
  unfold l1
  constructor
  · calc ∑ i, |((x + LatticeProb.unit j) i : ℝ)|
        ≤ ∑ i, (|(x i : ℝ)| + if i = j then 1 else 0) := Finset.sum_le_sum fun i _ => (key i).1
      _ = ∑ i, |(x i : ℝ)| + 1 := by rw [Finset.sum_add_distrib, hsum]
  · calc ∑ i, |(x i : ℝ)|
        ≤ ∑ i, (|((x + LatticeProb.unit j) i : ℝ)| + if i = j then 1 else 0) :=
          Finset.sum_le_sum fun i _ => (key i).2
      _ = ∑ i, |((x + LatticeProb.unit j) i : ℝ)| + 1 := by rw [Finset.sum_add_distrib, hsum]

/-- The `ℓ¹` norm changes by at most one along an open edge. -/
private theorem l1_le_of_adj {ω : Configuration 2} {C : OpenComponent ω} {a b : C}
    (hab : (componentGraph C).Adj a b) : l1 b.val ≤ l1 a.val + 1 := by
  obtain ⟨j, hj | hj⟩ := exists_unit_of_adj hab
  · rw [hj]; exact (l1_add_unit_le a.val j).1
  · have := (l1_add_unit_le b.val j).2
    rw [← hj] at this
    exact this

/-- Each coordinate changes by at most one along an open edge. -/
private theorem abs_coord_sub_le_of_adj {ω : Configuration 2} {C : OpenComponent ω} {a b : C}
    (hab : (componentGraph C).Adj a b) (i : Fin 2) : |(a.val i : ℝ) - (b.val i : ℝ)| ≤ 1 := by
  have hu : ∀ j, |((LatticeProb.unit j : Vertex 2) i : ℝ)| ≤ 1 := by
    intro j
    simp only [LatticeProb.unit, Pi.single_apply]
    split_ifs <;> simp
  obtain ⟨j, hj | hj⟩ := exists_unit_of_adj hab
  · rw [hj, Pi.add_apply, Int.cast_add, sub_add_cancel_left, abs_neg]
    exact hu j
  · rw [hj, Pi.add_apply, Int.cast_add, add_sub_cancel_left]
    exact hu j

/-- The Euclidean norm of a vertex of `ℤ²` is at most its `ℓ¹` norm. -/
private theorem norm_latticeEuclideanEmbedding_le_l1 (v : Vertex 2) :
    ‖latticeEuclideanEmbedding v‖ ≤ l1 v := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have h0 : ‖latticeEuclideanEmbedding v 0‖ = |(v 0 : ℝ)| := Real.norm_eq_abs _
  have h1 : ‖latticeEuclideanEmbedding v 1‖ = |(v 1 : ℝ)| := Real.norm_eq_abs _
  rw [h0, h1, Real.sqrt_le_left (l1_nonneg v)]
  simp only [l1, Fin.sum_univ_two]
  nlinarith [mul_nonneg (abs_nonneg (v 0 : ℝ)) (abs_nonneg (v 1 : ℝ))]

/-! ### step:5.8-support -/

/-- **step:5.8-support**: a finite set `V` of an open component, connected through its own edges,
has `ℓ¹` diameter at most `|V|`. -/
theorem connectedSetRadiusStep : ConnectedSetRadiusStep := by
  intro ω C V hV a ha b hb
  have hwalk : ∀ (u v : (V : Set C))
      (q : ((componentGraph C).induce (V : Set C)).Walk u v),
      l1 v.1.val ≤ l1 u.1.val + q.length := by
    intro u v q
    induction q with
    | nil => simp
    | @cons u w v hadj q ih =>
      have h1 := l1_le_of_adj (C := C) (a := u.1) (b := w.1) hadj
      rw [SimpleGraph.Walk.length_cons]
      push_cast
      linarith
  obtain ⟨q⟩ := hV ⟨b, hb⟩ ⟨a, ha⟩
  have hlen : q.bypass.length < V.card := by
    simpa using (q.bypass_isPath).length_lt
  have h := hwalk _ _ q.bypass
  have hcast : (q.bypass.length : ℝ) ≤ V.card := by exact_mod_cast hlen.le
  exact h.trans (by linarith)

/-! ### step:5.8-edge -/

/-- The increment of `g - Σᵢ ℓᵢ D z i` along the edge `(z, z + eⱼ)` is the `j`-th term of the left
side of eq. `green-gradient-homogenization` at `z`. -/
private theorem edge_term_eq {ω : Configuration 2} {C : OpenComponent ω} (g : C → ℝ)
    (ℓ : Fin 2 → C → ℝ) (D : C → Fin 2 → ℝ) (z w : C) (j : Fin 2)
    (hfd : ∀ u : C → ℝ, forwardDiff C u z j = u w - u z) :
    forwardDiff C g z j - D z j -
        ∑ i, (forwardDiff C (ℓ i) z j - if i = j then 1 else 0) * D z i =
      g w - g z - ∑ i, (ℓ i w - ℓ i z) * D z i := by
  simp only [hfd, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- **step:5.8-edge**: an open edge `(a, b)` is `(z, z + eⱼ)` with `z ∈ {a, b}`, and
`|g(a) - g(b) - Σᵢ (ℓᵢ(a) - ℓᵢ(b)) D z i|` is the `j`-th term of the left side of eq.
`green-gradient-homogenization` at `z`. -/
theorem forwardDiffEdgeStep : ForwardDiffEdgeStep := by
  intro ω C g ℓ D a b hab
  have hadj : (openGraph ω).Adj a.val b.val := (C.toSimpleGraph_adj a.2 b.2).1 hab
  have hle : ∀ (z : C) (j : Fin 2) (t : ℝ),
      |t| = |forwardDiff C g z j - D z j -
          ∑ i, (forwardDiff C (ℓ i) z j - if i = j then 1 else 0) * D z i| →
      |t| ≤ ∑ j, |forwardDiff C g z j - D z j -
          ∑ i, (forwardDiff C (ℓ i) z j - if i = j then 1 else 0) * D z i| := by
    intro z j t ht
    rw [ht]
    exact Finset.single_le_sum
      (f := fun j => |forwardDiff C g z j - D z j -
        ∑ i, (forwardDiff C (ℓ i) z j - if i = j then 1 else 0) * D z i|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  obtain ⟨j, hj | hj⟩ := exists_unit_of_adj hab
  · have hfd : ∀ u : C → ℝ, forwardDiff C u a j = u b - u a := by
      intro u
      unfold forwardDiff
      rw [dif_pos (by rw [← hj]; exact hadj)]
      congr 2
      exact Subtype.ext hj.symm
    refine ⟨a, Or.inl rfl, hle a j _ ?_⟩
    have hs : ∑ i, (ℓ i b - ℓ i a) * D a i = -∑ i, (ℓ i a - ℓ i b) * D a i := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [edge_term_eq g ℓ D a b j hfd, hs, ← abs_neg]
    congr 1
    ring
  · have hfd : ∀ u : C → ℝ, forwardDiff C u b j = u a - u b := by
      intro u
      unfold forwardDiff
      rw [dif_pos (by rw [← hj]; exact hadj.symm)]
      congr 2
      exact Subtype.ext hj.symm
    exact ⟨b, Or.inr rfl, hle b j _ (by rw [edge_term_eq g ℓ D b a j hfd])⟩

/-! ### step:5.8-corrector -/

/-- `(A + B u)^{s/2} ≤ (A + B)^s + 1 + u^s` for `A, B, u ≥ 0`: with `v = max(u, 1)`,
`(A + B u)^{s/2} ≤ (A + B)^{s/2} v^{s/2} ≤ ((A + B)^s + v^s) / 2`. -/
private theorem rpow_half_affine_le {A B u s : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hu : 0 ≤ u)
    (hs : 0 < s) : (A + B * u) ^ (s / 2) ≤ (A + B) ^ s + 1 + u ^ s := by
  set v := max u 1 with hv
  have hv1 : 1 ≤ v := le_max_right _ _
  have huv : u ≤ v := le_max_left _ _
  have hAB : 0 ≤ A + B := add_nonneg hA hB
  have h1 : A + B * u ≤ (A + B) * v := by nlinarith
  have hsq : ∀ t : ℝ, 0 ≤ t → (t ^ (s / 2)) ^ 2 = t ^ s := by
    intro t ht
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
    norm_num
  have h2 : (A + B * u) ^ (s / 2) ≤ (A + B) ^ (s / 2) * v ^ (s / 2) := by
    rw [← Real.mul_rpow hAB (by linarith)]
    exact Real.rpow_le_rpow (by positivity) h1 (by linarith)
  have h3 : (A + B) ^ (s / 2) * v ^ (s / 2) ≤ ((A + B) ^ s + v ^ s) / 2 := by
    rw [← hsq _ hAB, ← hsq v (by linarith)]
    nlinarith [sq_nonneg ((A + B) ^ (s / 2) - v ^ (s / 2))]
  have h4 : v ^ s ≤ u ^ s + 1 := by
    rcases le_total u 1 with h | h
    · rw [hv, max_eq_right h, Real.one_rpow]
      linarith [Real.rpow_nonneg hu s]
    · rw [hv, max_eq_left h]
      linarith
  have h5 := Real.rpow_nonneg hAB s
  have h6 := Real.rpow_nonneg hu s
  linarith

/-- **step:5.8-corrector**: the gradients of the corrected planes `ℓ_{eᵢ}` grow at most linearly,
`|ℓ_{eᵢ}(a) - ℓ_{eᵢ}(b)| ≤ Λ (1 + |a|)` on the open edges, with `Λ = 1 + C (M + 2) ≤ O_{s/2}(θ)`
for the constant `C` and the minimal scale `M` of Theorem 2.5 at the origin with `α = 1`. -/
theorem correctedPlaneGradientStep : CorrectedPlaneGradientStep := by
  intro hQ p hpc hp1
  obtain ⟨s, K, hs, hK, hM⟩ := hQ 2 le_rfl p hpc hp1 1 one_pos
  obtain ⟨M, hMm, hM0, hMos, hae⟩ := hM 0
  have hΛm : Measurable fun ω => 1 + K * (M ω + 2) :=
    measurable_const.add (measurable_const.mul (hMm.add measurable_const))
  have hint : Integrable (fun ω => Real.exp (Real.rpow (1 + K * (M ω + 2)) (s / 2)))
      (latticeBondLaw 2 p) := by
    refine (hMos.1.const_mul (Real.exp ((1 + 2 * K + K * K) ^ s + 1))).mono'
      (hΛm.pow_const (s / 2)).exp.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    have hMK : max (M ω / K) 0 = M ω / K := max_eq_left (div_nonneg (hM0 ω) hK.le)
    have hbound := rpow_half_affine_le (A := 1 + 2 * K) (B := K * K) (u := M ω / K)
      (by positivity) (by positivity) (div_nonneg (hM0 ω) hK.le) hs
    have heq : 1 + 2 * K + K * K * (M ω / K) = 1 + K * (M ω + 2) := by
      field_simp
      ring
    rw [heq] at hbound
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hMK, ← Real.exp_add]
    simp only [Real.rpow_eq_pow]
    exact Real.exp_le_exp.mpr (by linarith)
  obtain ⟨θ, hθ, hΛos⟩ := exists_isOs_of_integrable (half_pos hs)
    (fun ω => by have := hM0 ω; positivity) hΛm hint
  refine ⟨s / 2, θ, half_pos hs, hθ, fun ω => 1 + K * (M ω + 2), hΛm, hΛos, ?_⟩
  filter_upwards [hae] with ω hω h i ℓ hℓ a b hab
  have e0 : latticeEuclideanEmbedding (0 : Vertex 2) = 0 := by
    ext k
    change ((0 : ℤ) : ℝ) = 0
    simp
  have hq : ∀ v : Vertex 2, ∑ k, (Pi.single i 1 : Fin 2 → ℝ) k * (v k : ℝ) = v i := by
    intro v
    simp [Pi.single_apply]
  have hq1 : ∑ k, |(Pi.single i 1 : Fin 2 → ℝ) k| = 1 := by
    simp [Pi.single_apply, apply_ite]
  have hM0ω := hM0 ω
  have hla := l1_nonneg a.val
  have hlb := l1_le_of_adj hab
  set r : ℝ := M ω + l1 a.val + 2 with hr
  have hball : ∀ v : Vertex 2, l1 v < r →
      ‖latticeEuclideanEmbedding v - latticeEuclideanEmbedding 0‖ < r := fun v hv => by
    rw [e0, sub_zero]
    exact (norm_latticeEuclideanEmbedding_le_l1 v).trans_lt hv
  have key := hω h (Pi.single i 1) ℓ hℓ r (by linarith) a b a b
    (hball _ (by linarith)) (hball _ (by linarith)) (hball _ (by linarith))
    (hball _ (by linarith)) hab
  simp only [hq, hq1, mul_one, Real.rpow_one] at key
  have hχ : |(ℓ a - (a.val i : ℝ)) - (ℓ b - (b.val i : ℝ))| ≤ K * r := by
    linarith [abs_nonneg ((ℓ a - (a.val i : ℝ)) - (ℓ b - (b.val i : ℝ)))]
  have hcoord := abs_coord_sub_le_of_adj hab i
  have htri : |ℓ a - ℓ b| ≤ |(ℓ a - (a.val i : ℝ)) - (ℓ b - (b.val i : ℝ))| +
      |(a.val i : ℝ) - (b.val i : ℝ)| := by
    rw [show ℓ a - ℓ b = ((ℓ a - (a.val i : ℝ)) - (ℓ b - (b.val i : ℝ))) +
      ((a.val i : ℝ) - (b.val i : ℝ)) by ring]
    exact abs_add_le _ _
  have hprod : K * l1 a.val ≤ K * (M ω + 2) * l1 a.val := by
    have : K * l1 a.val * 1 ≤ K * l1 a.val * (M ω + 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hK.le hla)
    linarith
  calc |ℓ a - ℓ b| ≤ K * r + 1 := by linarith
    _ = 1 + K * (M ω + 2) + K * l1 a.val := by rw [hr]; ring
    _ ≤ (1 + K * (M ω + 2)) * (1 + l1 a.val) := by nlinarith

end Rigidity.Proofs.Section5
