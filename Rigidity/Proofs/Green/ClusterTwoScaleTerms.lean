import Rigidity.Proofs.Green.ClusterWeakNorm
import Rigidity.Proofs.Green.ClusterTwoScaleDecomposition

/-!
# The weak norms of the terms of the two-scale expansion (Step 3 of Theorem 5 of Dario–Gu)

Step 3 of the proof of Theorem 5 of Dario–Gu (lines 1488-1540 of the source) bounds the
`H̲^{-1}(V)` norm of each term of the decomposition (3.25) of `(∂_t - ∇·a∇) w` by the product
rule (3.26), the bound (3.27) and the divergence form. This file proves these bounds on a finite set
`V` of the planar cluster for unit conductances, in terms of bounds on the coefficients, for the
decomposition of `timeDeriv_sub_openLaplacian_cutoffTwoScale`:

* `weakNormLe_div_field`: the divergence `Σ_i (H_i(x) - H_i(x - e_i))` of a field carried by the
  open edges has norm at most `|V|^{-1/2} (Σ_{x ∈ V} Σ_i (H_i(x)² + H_i(x - e_i)²))^{1/2}` (the terms
  (3.25)-c1 and e, first lines of (3.30) and (3.32));
* `weakNormLe_time_term`: `Σ_k ∂_t F_k χ_k` ((3.25)-b, first line of (3.29));
* `weakNormLe_flux_term`: `Σ_{k,i} g̃_{k,i} D_i F_k` ((3.25)-d, first line of (3.31));
* `weakNormLe_of_abs_le`: a term bounded by `ε` on `V` has norm at most `|V|^{1/2} ε` ((3.27), for
  the term (3.25)-a);
* `weakNormLe_twoScale_equation`: the sum of the five bounds bounds the norm of `∂_t w - Δ w` on
  `V`, when the corrector equation holds on `int_a(V)` (the conclusion of Step 3 before the bounds
  of Lemma 3.7 on `ū` are inserted).
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green

/-- Only the values on `int_a(V)` enter the weak norm. -/
theorem WeakNormLe.congr_interior {ω : Configuration 2} {V : Finset (Vertex 2)}
    {g g' : Vertex 2 → ℝ} {B : ℝ} (h : WeakNormLe ω V g B)
    (hg : ∀ x ∈ openInterior ω V, g' x = g x) : WeakNormLe ω V g' B := by
  intro v hv
  have e : ∑ x ∈ V, g' x * v x = ∑ x ∈ V, g x * v x := by
    refine Finset.sum_congr rfl fun x hx => ?_
    by_cases hi : x ∈ openInterior ω V
    · rw [hg x hi]
    · rw [hv x hx hi, mul_zero, mul_zero]
  rw [e]
  exact h v hv

/-- A function bounded by `ε` on `V` has `H̲^{-1}(V)` norm at most `|V|^{1/2} ε` ((3.27)). -/
theorem weakNormLe_of_abs_le (ω : Configuration 2) (V : Finset (Vertex 2)) {A : Vertex 2 → ℝ}
    {ε : ℝ} (hε : 0 ≤ ε) (hA : ∀ x ∈ V, |A x| ≤ ε) :
    WeakNormLe ω V A (Real.sqrt V.card * ε) := by
  refine (weakNormLe_sqrt_sum_sq ω V A).mono ?_
  have hsum : ∑ x ∈ V, A x ^ 2 ≤ V.card * ε ^ 2 := by
    calc ∑ x ∈ V, A x ^ 2 ≤ ∑ _x ∈ V, ε ^ 2 := Finset.sum_le_sum fun x hx => by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hA x hx) 2
      _ = V.card * ε ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  calc Real.sqrt (∑ x ∈ V, A x ^ 2) ≤ Real.sqrt (V.card * ε ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt V.card * ε := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hε]

/-- The edge function of a field `H` carried by the edges `{z, z + e_i}`:
`E(x, x + e_i) = H_i(x)`, `E(x, x - e_i) = -H_i(x - e_i)`. -/
noncomputable def fieldEdge (H : Fin 2 → Vertex 2 → ℝ) (x z : Vertex 2) : ℝ :=
  ∑ i : Fin 2, ((if z = x + unit i then H i x else 0) - (if x = z + unit i then H i z else 0))

theorem fieldEdge_swap (H : Fin 2 → Vertex 2 → ℝ) (x z : Vertex 2) :
    fieldEdge H z x = -fieldEdge H x z := by
  unfold fieldEdge
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem sum_ite_add_unit_eq (H : Fin 2 → Vertex 2 → ℝ) (i : Fin 2) (x : Vertex 2)
    (S : Finset (Vertex 2)) :
    ∑ z ∈ S, (if x = z + unit i then H i z else 0) =
      if x - unit i ∈ S then H i (x - unit i) else 0 := by
  rw [← Finset.sum_ite_eq' S (x - unit i) (fun _ => H i (x - unit i))]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases h : z = x - unit i
  · rw [if_pos h, if_pos (by rw [h, sub_add_cancel]), h]
  · rw [if_neg h, if_neg]
    intro h'
    exact h (eq_sub_of_add_eq h'.symm)

theorem sq_sub_add_sub_le (a b c d : ℝ) :
    (a - b + (c - d)) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + (c ^ 2 + d ^ 2)) := by
  nlinarith [sq_nonneg (a - b - (c - d)), sq_nonneg (a + b), sq_nonneg (c + d)]

/-- **The divergence of a field carried by the open edges**: if `H_i(z) = 0` whenever the edge
`{z, z + e_i}` is closed, then `x ↦ Σ_i (H_i(x) - H_i(x - e_i))` has `H̲^{-1}(V)` norm at most
`|V|^{-1/2} (Σ_{x ∈ V} Σ_i (H_i(x)² + H_i(x - e_i)²))^{1/2}`. -/
theorem weakNormLe_div_field (ω : Configuration 2) (V : Finset (Vertex 2))
    {H : Fin 2 → Vertex 2 → ℝ} (hH : ∀ i z, ¬(openGraph ω).Adj z (z + unit i) → H i z = 0) :
    WeakNormLe ω V (fun x => ∑ i : Fin 2, (H i x - H i (x - unit i)))
      ((Real.sqrt V.card)⁻¹ *
        Real.sqrt (∑ x ∈ V, ∑ i : Fin 2, (H i x ^ 2 + H i (x - unit i) ^ 2))) := by
  have hanti : ∀ x ∈ V, ∀ z ∈ V, (openGraph ω).Adj x z → fieldEdge H z x = -fieldEdge H x z :=
    fun x _ z _ _ => fieldEdge_swap H x z
  have hdiv : ∀ x ∈ openInterior ω V, ∑ i : Fin 2, (H i x - H i (x - unit i)) =
      ∑ z ∈ V.filter (fun z => (openGraph ω).Adj x z), fieldEdge H x z := by
    intro x hi
    have hN : V.filter (fun z => (openGraph ω).Adj x z) = (openGraph ω).neighborFinset x := by
      ext z
      rw [SimpleGraph.mem_neighborFinset, Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hi.2 z h, h⟩⟩
    rw [hN]
    unfold fieldEdge
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', sum_ite_add_unit_eq]
    congr 1
    · split_ifs with h
      · rfl
      · rw [SimpleGraph.mem_neighborFinset] at h
        exact hH i x h
    · split_ifs with h
      · rfl
      · rw [SimpleGraph.mem_neighborFinset] at h
        refine hH i (x - unit i) ?_
        rw [sub_add_cancel]
        exact fun h' => h h'.symm
  have hmain := (weakNormLe_sum_antisymm ω V hanti).congr_interior hdiv
  refine hmain.mono ?_
  -- the square of the edge function
  have hsq : ∀ x ∈ V, ∑ z ∈ V.filter (fun z => (openGraph ω).Adj x z), fieldEdge H x z ^ 2 ≤
      4 * ∑ i : Fin 2, (H i x ^ 2 + H i (x - unit i) ^ 2) := by
    intro x _
    set S := V.filter (fun z => (openGraph ω).Adj x z)
    have hpt : ∀ z, fieldEdge H x z ^ 2 ≤ 4 * ∑ i : Fin 2,
        ((if z = x + unit i then H i x ^ 2 else 0) + (if x = z + unit i then H i z ^ 2 else 0)) := by
      intro z
      unfold fieldEdge
      simp only [Fin.sum_univ_two]
      have e : ∀ (p : Prop) [Decidable p] (c : ℝ), (if p then c else 0) ^ 2 =
          if p then c ^ 2 else 0 := by
        intro p _ c
        split_ifs <;> ring
      rw [← e, ← e, ← e, ← e]
      exact sq_sub_add_sub_le _ _ _ _
    calc ∑ z ∈ S, fieldEdge H x z ^ 2
        ≤ ∑ z ∈ S, 4 * ∑ i : Fin 2,
            ((if z = x + unit i then H i x ^ 2 else 0) +
              (if x = z + unit i then H i z ^ 2 else 0)) := Finset.sum_le_sum fun z _ => hpt z
      _ = 4 * ∑ i : Fin 2, ((if x + unit i ∈ S then H i x ^ 2 else 0) +
            (if x - unit i ∈ S then H i (x - unit i) ^ 2 else 0)) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
          congr 1
          exact sum_ite_add_unit_eq (fun j w => H j w ^ 2) i x S
      _ ≤ 4 * ∑ i : Fin 2, (H i x ^ 2 + H i (x - unit i) ^ 2) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by norm_num)
          refine add_le_add ?_ ?_ <;> split_ifs <;> first | exact le_rfl | positivity
  have hX : ∑ x ∈ V, ∑ z ∈ V.filter (fun z => (openGraph ω).Adj x z), fieldEdge H x z ^ 2 ≤
      4 * ∑ x ∈ V, ∑ i : Fin 2, (H i x ^ 2 + H i (x - unit i) ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hsq
  have hX0 : 0 ≤ ∑ x ∈ V, ∑ i : Fin 2, (H i x ^ 2 + H i (x - unit i) ^ 2) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hroot : Real.sqrt (∑ x ∈ V, ∑ z ∈ V.filter (fun z => (openGraph ω).Adj x z),
      fieldEdge H x z ^ 2) ≤
      2 * Real.sqrt (∑ x ∈ V, ∑ i : Fin 2, (H i x ^ 2 + H i (x - unit i) ^ 2)) := by
    calc _ ≤ Real.sqrt (4 * ∑ x ∈ V, ∑ i : Fin 2, (H i x ^ 2 + H i (x - unit i) ^ 2)) :=
          Real.sqrt_le_sqrt hX
      _ = 2 * Real.sqrt (∑ x ∈ V, ∑ i : Fin 2, (H i x ^ 2 + H i (x - unit i) ^ 2)) := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  have hinv : 0 ≤ (Real.sqrt (V.card : ℝ))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  calc (Real.sqrt V.card)⁻¹ * Real.sqrt (∑ x ∈ V,
        ∑ z ∈ V.filter (fun z => (openGraph ω).Adj x z), fieldEdge H x z ^ 2) / 2
      ≤ (Real.sqrt V.card)⁻¹ *
          (2 * Real.sqrt (∑ x ∈ V, ∑ i : Fin 2, (H i x ^ 2 + H i (x - unit i) ^ 2))) / 2 := by
        gcongr
    _ = (Real.sqrt V.card)⁻¹ *
          Real.sqrt (∑ x ∈ V, ∑ i : Fin 2, (H i x ^ 2 + H i (x - unit i) ^ 2)) := by ring

/-- The divergence fields of the two-scale expansion vanish on the closed edges. -/
theorem cutoffField_eq_zero (ω : Configuration 2) (χ : Fin 2 → Vertex 2 → ℝ)
    (U : Vertex 2 → ℝ) (F : Fin 2 → Vertex 2 → ℝ) (i : Fin 2) (z : Vertex 2)
    (h : ¬(openGraph ω).Adj z (z + unit i)) : cutoffField ω χ U F i z = 0 := by
  unfold cutoffField openCond
  rw [if_neg h, zero_mul]

/-- **The term (3.25)-b** (first line of (3.29)): if `|∂_t F_k| ≤ M` and `|∇ ∂_t F_k| ≤ N` on `V`,
then `‖Σ_k ∂_t F_k χ_k‖_{H̲^{-1}(V)} ≤ Σ_k (Σ_V χ_k²)^{1/2} (M + |V|^{1/2} N)`. -/
theorem weakNormLe_time_term (ω : Configuration 2) (V : Finset (Vertex 2))
    (χ : Fin 2 → Vertex 2 → ℝ) {F' : Fin 2 → Vertex 2 → ℝ} {M N : ℝ}
    (hM : ∀ k, ∀ x ∈ V, |F' k x| ≤ M) (hN : ∀ k, ∀ x ∈ V, openGradNorm ω V (F' k) x ≤ N) :
    WeakNormLe ω V (fun x => ∑ k : Fin 2, F' k x * χ k x)
      (∑ k : Fin 2, Real.sqrt (∑ x ∈ V, χ k x ^ 2) * (M + Real.sqrt V.card * N)) := by
  have h := WeakNormLe.sum (ω := ω) (V := V) Finset.univ
    (g := fun k x => χ k x * F' k x)
    (B := fun k => Real.sqrt (∑ x ∈ V, χ k x ^ 2) * (M + Real.sqrt V.card * N))
    fun k _ => (weakNormLe_sqrt_sum_sq ω V (χ k)).mul_right (Real.sqrt_nonneg _) (hM k) (hN k)
  have e : (fun x => ∑ k : Fin 2, F' k x * χ k x) = fun x => ∑ k : Fin 2, χ k x * F' k x := by
    funext x
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [e]
  exact h

/-- **The term (3.25)-d** (first line of (3.31)): if `‖g̃_{k,i}‖_{H̲^{-1}(V)} ≤ a_{k,i}`,
`|D_i F_k| ≤ M` and `|∇ D_i F_k| ≤ N` on `V`, then
`‖Σ_{k,i} g̃_{k,i} D_i F_k‖_{H̲^{-1}(V)} ≤ Σ_{k,i} a_{k,i} (M + |V|^{1/2} N)`. -/
theorem weakNormLe_flux_term (ω : Configuration 2) (V : Finset (Vertex 2)) (σ : ℝ)
    (χ : Fin 2 → Vertex 2 → ℝ) {F : Fin 2 → Vertex 2 → ℝ} {a : Fin 2 → Fin 2 → ℝ} {M N : ℝ}
    (ha : ∀ k i, 0 ≤ a k i) (hflux : ∀ k i, WeakNormLe ω V (centeredFlux ω σ χ k i) (a k i))
    (hM : ∀ k i, ∀ x ∈ V, |fwdDiff i (F k) x| ≤ M)
    (hN : ∀ k i, ∀ x ∈ V, openGradNorm ω V (fwdDiff i (F k)) x ≤ N) :
    WeakNormLe ω V (fun x => ∑ k : Fin 2, ∑ i : Fin 2, centeredFlux ω σ χ k i x * fwdDiff i (F k) x)
      (∑ k : Fin 2, ∑ i : Fin 2, a k i * (M + Real.sqrt V.card * N)) :=
  WeakNormLe.sum Finset.univ fun k _ =>
    WeakNormLe.sum Finset.univ fun i _ =>
      (hflux k i).mul_right (ha k i) (hM k i) (hN k i)

/-- **The conclusion of Step 3** of the proof of Theorem 5 of Dario–Gu (before the bounds on `ū`):
if the corrector equation holds on `int_a(V)`, `∂_t U = (σ/2)(L_in + L_out)` there, and the five
terms of `timeDeriv_sub_openLaplacian_cutoffTwoScale` have `H̲^{-1}(V)` norms at most
`b_a, b_b, b_c, b_e, b_d`, then `‖∂_t w - Δ w‖_{H̲^{-1}(V)} ≤ b_a + b_b + b_c + b_e + b_d`. -/
theorem weakNormLe_twoScale_equation (ω : Configuration 2) (V : Finset (Vertex 2)) (σ : ℝ)
    (χ : Fin 2 → Vertex 2 → ℝ) (U U' Lin Lout : Vertex 2 → ℝ) (F F' : Fin 2 → Vertex 2 → ℝ)
    (hχ : ∀ x ∈ openInterior ω V, ∀ k : Fin 2,
      ∑ i : Fin 2, (openFlux ω χ k i (x - unit i) - openFlux ω χ k i x) = 0)
    (hU' : ∀ x ∈ openInterior ω V, U' x = σ / 2 * (Lin x + Lout x))
    {ba bb bc be bd : ℝ}
    (ha : WeakNormLe ω V (fun x => σ / 2 * (Lin x - ∑ k : Fin 2, fwdDiff k (F k) x)) ba)
    (hb : WeakNormLe ω V (fun x => ∑ k : Fin 2, F' k x * χ k x) bb)
    (hc : WeakNormLe ω V (fun x => σ / 2 * Lout x) bc)
    (he : WeakNormLe ω V
      (fun x => ∑ i : Fin 2, (cutoffField ω χ U F i x - cutoffField ω χ U F i (x - unit i))) be)
    (hd : WeakNormLe ω V
      (fun x => ∑ k : Fin 2, ∑ i : Fin 2, centeredFlux ω σ χ k i x * fwdDiff i (F k) x) bd) :
    WeakNormLe ω V
      (fun x => (U' x + ∑ k : Fin 2, F' k x * χ k x) -
        openLaplacian ω (fun z => U z + ∑ k : Fin 2, F k z * χ k z) x)
      (ba + bb + bc + be + bd) := by
  have hsum := (((ha.add hb).add hc).add he.neg).add hd.neg
  refine hsum.congr_interior fun x hx => ?_
  rw [timeDeriv_sub_openLaplacian_cutoffTwoScale ω σ χ U F x (hχ x hx) (fun k => F' k x)
    (hU' x hx)]
  simp only [Pi.add_apply]
  ring

end Rigidity.Green
