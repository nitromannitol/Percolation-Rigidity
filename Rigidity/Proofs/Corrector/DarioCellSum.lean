import Rigidity.Proofs.Corrector.DarioCellGeometry
import Rigidity.Proofs.Corrector.DarioStepTwoWeight

/-!
# The weighted energy on a cube with the Meyers estimate

Let `v` solve `∇·∇v = ∇·γ` at the vertices of the infinite cluster, `E(u)` be its energy at the
vertices `u` of the cluster (`clusterOpenEnergy`) and `Γ(z) = Σ_i γ(z, i)²` (`edgeSq`). On a cube
`□ = cube k x` carrying the homogeneous Meyers estimate with exponent `ε` and on which a weight `W`
satisfies `Σ_□ W^q ≤ M |□|`, `q` the exponent conjugate to `p = 1 + ε/2`
(`sum_weight_energy_le_of_meyersCube`):

`Σ_{u ∈ □} W(u) E(u) ≤ K (Σ_{z ∈ 3□} E(z) + |□|^{1 - 1/p} Σ_{z ∈ 3□} Γ(z))`.

This is Hölder's inequality with the exponents `q` and `p` followed by the Meyers estimate with a
divergence source (`meyers_source`) for the part of the cluster inside `3□`: the step of the route
through estimate (2) where the higher integrability of the energy absorbs the weight. The constant
`K = 4 M^{1/q} K_M^{1/p}` (`cellConst`) depends only on `ε`, the Meyers constant and `M`.
-/

namespace Rigidity.Corrector

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
open scoped Classical ENNReal InnerProductSpace

/-- The energy of `f` at the vertices of the infinite cluster, `0` elsewhere. -/
noncomputable def clusterOpenEnergy (ω : Configuration 2) (f : Vertex 2 → ℝ) (u : Vertex 2) : ℝ :=
  if ω ∈ infiniteComponentEvent u then openEnergy ω f u else 0

/-- `Γ(z) = Σ_i γ(z, i)²`. -/
noncomputable def edgeSq (γ : EdgeField) (z : Vertex 2) : ℝ := ∑ i : Fin 2, γ (z, i) ^ 2

theorem clusterOpenEnergy_nonneg (ω : Configuration 2) (f : Vertex 2 → ℝ) (u : Vertex 2) :
    0 ≤ clusterOpenEnergy ω f u := by
  unfold clusterOpenEnergy
  split_ifs
  · exact openEnergy_nonneg _ _ _
  · exact le_rfl

theorem edgeSq_nonneg (γ : EdgeField) (z : Vertex 2) : 0 ≤ edgeSq γ z :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The constant `4 M^{1/q} K_M^{1/p}` of the weighted energy on a Meyers cube. -/
noncomputable def cellConst (ε C M : ℝ) : ℝ :=
  4 * M ^ (1 / Real.conjExponent (1 + ε / 2)) *
    ((2 : ℝ) ^ (2 * (1 + ε / 2)) * (C * (2 : ℝ) ^ (2 * (1 + ε / 2)) + 1)) ^ (1 / (1 + ε / 2))

/-- Superadditivity of `t ↦ t^p` for `p ≥ 1`. -/
theorem rpow_add_rpow_le_add_rpow {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 1 ≤ p) :
    a ^ p + b ^ p ≤ (a + b) ^ p := by
  rcases eq_or_lt_of_le (add_nonneg ha hb) with h | h
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    subst ha0 hb0
    simp [Real.zero_rpow (by linarith : p ≠ 0)]
  have hp1 : 0 ≤ p - 1 := by linarith
  have e : ∀ t : ℝ, 0 ≤ t → t ^ p = t * t ^ (p - 1) := fun t ht => by
    rcases eq_or_lt_of_le ht with h0 | h0
    · subst h0; simp [Real.zero_rpow (by linarith : p ≠ 0)]
    · rw [← Real.rpow_one_add' ht (by linarith)]; ring_nf
  rw [e a ha, e b hb, e (a + b) h.le, add_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha (by linarith) hp1) ha)
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hb (by linarith) hp1) hb)

/-- The squared norm of the restriction of `γ` to the open edges inside `U` is at most
`Σ_{z ∈ U} Γ(z)`. -/
theorem norm_restrictField_restrictConfig_sq_le (ω : Configuration 2) (U : Finset (Vertex 2))
    (γ : EdgeField) :
    ‖restrictField (restrictConfig ω U) γ‖ ^ 2 ≤ ∑ z ∈ U, edgeSq γ z := by
  rw [← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
  simp only [Real.inner_apply]
  have hsupp : ∀ a ∉ U ×ˢ (Finset.univ : Finset (Fin 2)),
      restrictField (restrictConfig ω U) γ a * restrictField (restrictConfig ω U) γ a = 0 := by
    intro a ha
    rw [restrictField_apply, if_neg]
    · ring
    · intro h
      exact ha (Finset.mem_product.2 ⟨(edgeOpen_restrictConfig_iff.1 h).2.1, Finset.mem_univ _⟩)
  rw [tsum_eq_sum hsupp, Finset.sum_product]
  refine Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun i _ => ?_
  rw [restrictField_apply]
  split_ifs
  · rw [← sq]
  · simp only [mul_zero]; exact sq_nonneg _

section Meyers

variable {ω : Configuration 2} {γ : EdgeField} {v : Vertex 2 → ℝ}

theorem mem_enl_of_adj_of_mem_cube {k : ℕ} {x u y : Vertex 2} (hu : u ∈ cube k x)
    (h : (openGraph ω).Adj u y) : y ∈ enl 1 k x := by
  rw [enl, mem_box]
  intro i
  have a1 := (mem_box.1 hu) i
  have a2 := abs_sub_le_one_of_adj h i
  have a2' : |u i - y i| ≤ 1 := by exact_mod_cast a2
  have hh : halfSide (k + 1) = 3 * halfSide k + 1 := rfl
  have hh0 := halfSide_nonneg k
  have t := abs_sub_le (y i) (u i) (center k x i)
  rw [abs_sub_comm (y i) (u i)] at t
  linarith

/-- **The weighted energy on a Meyers cube.** -/
theorem sum_weight_energy_le_of_meyersCube
    (hv : ∀ z, ω ∈ infiniteComponentEvent z → openLaplacian ω v z = edgeDiv ω γ z)
    {ε CM : ℝ} (hε : 0 < ε) (hCM : 0 ≤ CM) {k : ℕ} {x : Vertex 2}
    (hMey : GeneralDim.MeyersCube ε CM ω k x) {W : Vertex 2 → ℝ} (hW0 : ∀ u, 0 ≤ W u) {M : ℝ}
    (hM : 0 ≤ M)
    (hWM : ∑ u ∈ cube k x, W u ^ Real.conjExponent (1 + ε / 2) ≤ M * (cube k x).card) :
    ∑ u ∈ cube k x, W u * clusterOpenEnergy ω v u ≤ cellConst ε CM M *
      (∑ z ∈ enl 1 k x, clusterOpenEnergy ω v z +
        ((cube k x).card : ℝ) ^ (1 - 1 / (1 + ε / 2)) * ∑ z ∈ enl 1 k x, edgeSq γ z) := by
  unfold cellConst
  set p : ℝ := 1 + ε / 2 with hp
  have hp1 : 1 < p := by rw [hp]; linarith
  have hp0 : 0 < p := by linarith
  set q := Real.conjExponent p with hq
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp1
  have hq0 : 0 < q := hpq.symm.pos
  have hinv : 1 / q + 1 / p = 1 := by
    rw [one_div, one_div, add_comm]; exact hpq.inv_add_inv_eq_one
  set Cb := cube k x with hCb
  set D := enl 1 k x with hD
  set U₀ := D.filter (fun z => ω ∈ infiniteComponentEvent z) with hU₀
  set cE := clusterEnergy ω U₀ v with hcE
  set E := clusterOpenEnergy ω v with hE
  have hE0 : ∀ z, 0 ≤ E z := clusterOpenEnergy_nonneg ω v
  have hcE0 : ∀ z, 0 ≤ cE z := fun z => clusterEnergy_nonneg ω U₀ v z
  -- the energies on the cube and on its enlargement
  have hEC : ∀ u ∈ Cb, E u = 2 * cE u := by
    intro u hu
    simp only [hE, hcE, clusterOpenEnergy, clusterEnergy]
    by_cases hc : ω ∈ infiniteComponentEvent u
    · have huU : u ∈ U₀ := Finset.mem_filter.2 ⟨cube_subset_enl 1 k x hu, hc⟩
      rw [if_pos hc, if_pos huU]
      unfold clusterGradSq openEnergy
      rw [Finset.filter_true_of_mem]
      · ring
      · intro y hy
        have hadj := (SimpleGraph.mem_neighborFinset _ _ _).1 hy
        exact Finset.mem_filter.2 ⟨mem_enl_of_adj_of_mem_cube hu hadj,
          mem_infiniteComponentEvent_of_adj hadj hc⟩
    · have huU : u ∉ U₀ := fun h => hc (Finset.mem_filter.1 h).2
      rw [if_neg hc, if_neg huU]
      ring
  have hED : ∀ z, cE z ≤ E z := by
    intro z
    simp only [hE, hcE, clusterOpenEnergy, clusterEnergy]
    by_cases hzU : z ∈ U₀
    · have hc := (Finset.mem_filter.1 hzU).2
      rw [if_pos hzU, if_pos hc]
      unfold clusterGradSq openEnergy
      have h1 : ∑ y ∈ ((openGraph ω).neighborFinset z).filter (· ∈ U₀), (v z - v y) ^ 2 ≤
          ∑ y ∈ (openGraph ω).neighborFinset z, (v z - v y) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => sq_nonneg _
      have h0 : 0 ≤ ∑ y ∈ ((openGraph ω).neighborFinset z).filter (· ∈ U₀), (v z - v y) ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      linarith
    · rw [if_neg hzU]
      exact hE0 z
  -- the Meyers estimate with source
  have hmey := meyers_source hε hCM hMey (U₀ := U₀) (Finset.filter_subset _ _)
    (fun z hz y hzy hy => Finset.mem_filter.2 ⟨hy,
      mem_infiniteComponentEvent_of_adj hzy (Finset.mem_filter.1 hz).2⟩) γ
    (fun z hz _ => hv z (Finset.mem_filter.1 hz).2)
  rw [← hp, ← hCb, ← hD, ← hcE] at hmey
  set S := ‖restrictField (restrictConfig ω U₀) γ‖ ^ 2 with hS
  have hS0 : 0 ≤ S := sq_nonneg _
  have hSΓ : S ≤ ∑ z ∈ D, edgeSq γ z :=
    (norm_restrictField_restrictConfig_sq_le ω U₀ γ).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun z _ _ => edgeSq_nonneg γ z)
  -- the cardinalities
  have hC1 : (1 : ℝ) ≤ Cb.card := by
    have : 0 < Cb.card := Finset.card_pos.2 ⟨x, mem_cube_self k x⟩
    exact_mod_cast this
  have hC0 : (0 : ℝ) < Cb.card := by linarith
  have hCD : (Cb.card : ℝ) ≤ D.card := by exact_mod_cast Finset.card_le_card (cube_subset_enl 1 k x)
  have hD0 : (0 : ℝ) < D.card := by linarith
  set KM : ℝ := (2 : ℝ) ^ (2 * p) * (CM * (2 : ℝ) ^ (2 * p) + 1) with hKM
  have hKM0 : 0 ≤ KM := by positivity
  set A := avg D E with hA
  have hA0 : 0 ≤ A := div_nonneg (Finset.sum_nonneg fun z _ => hE0 z) (Nat.cast_nonneg _)
  set B := S / D.card with hB
  have hB0 : 0 ≤ B := div_nonneg hS0 (Nat.cast_nonneg _)
  set T := S * (Cb.card : ℝ) ^ (-(1 / p)) with hT
  have hT0 : 0 ≤ T := mul_nonneg hS0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  -- the Meyers estimate in the form `avg_□ cE^p ≤ K_M (A^p + B^p + T^p)`
  have hAc : avg D cE ≤ A :=
    div_le_div_of_nonneg_right (Finset.sum_le_sum fun z _ => hED z) (Nat.cast_nonneg _)
  have hTp : T ^ p = S ^ p / Cb.card := by
    rw [hT, Real.mul_rpow hS0 (Real.rpow_nonneg (Nat.cast_nonneg _) _), ← Real.rpow_mul
      (Nat.cast_nonneg _), show -(1 / p) * p = -1 by field_simp, Real.rpow_neg_one, div_eq_mul_inv]
  have hmey' : avg Cb (fun z => cE z ^ p) ≤ KM * (A ^ p + B ^ p + T ^ p) := by
    refine hmey.trans (mul_le_mul_of_nonneg_left ?_ hKM0)
    rw [hTp]
    have h0 : 0 ≤ avg D cE := div_nonneg (Finset.sum_nonneg fun z _ => hcE0 z) (Nat.cast_nonneg _)
    have := Real.rpow_le_rpow h0 hAc hp0.le
    linarith
  have hsup : A ^ p + B ^ p + T ^ p ≤ (A + B + T) ^ p := by
    have h1 := rpow_add_rpow_le_add_rpow hA0 hB0 hp1.le
    have h2 := rpow_add_rpow_le_add_rpow (add_nonneg hA0 hB0) hT0 hp1.le
    linarith
  -- the energy in `L^p`
  have hEp : ∑ u ∈ Cb, E u ^ p ≤ (2 : ℝ) ^ p * Cb.card * KM * (A + B + T) ^ p := by
    have e1 : ∑ u ∈ Cb, E u ^ p = (2 : ℝ) ^ p * ∑ u ∈ Cb, cE u ^ p := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [hEC u hu, Real.mul_rpow (by norm_num) (hcE0 u)]
    have e2 : ∑ u ∈ Cb, cE u ^ p = Cb.card * avg Cb (fun z => cE z ^ p) := by
      unfold avg
      field_simp
    rw [e1, e2]
    have h2p : (0 : ℝ) ≤ (2 : ℝ) ^ p := by positivity
    calc (2 : ℝ) ^ p * (Cb.card * avg Cb (fun z => cE z ^ p))
        ≤ (2 : ℝ) ^ p * (Cb.card * (KM * (A ^ p + B ^ p + T ^ p))) := by gcongr
      _ ≤ (2 : ℝ) ^ p * (Cb.card * (KM * (A + B + T) ^ p)) := by gcongr
      _ = _ := by ring
  have hEp' : (∑ u ∈ Cb, E u ^ p) ^ (1 / p) ≤
      2 * (Cb.card : ℝ) ^ (1 / p) * KM ^ (1 / p) * (A + B + T) := by
    have hABT : 0 ≤ A + B + T := add_nonneg (add_nonneg hA0 hB0) hT0
    have h2p : 0 ≤ (2 : ℝ) ^ p := Real.rpow_nonneg (by norm_num) p
    have hCp : 0 ≤ (Cb.card : ℝ) := Nat.cast_nonneg _
    have hsum0 : 0 ≤ ∑ u ∈ Cb, E u ^ p := Finset.sum_nonneg fun u _ => Real.rpow_nonneg (hE0 u) _
    have e1 : ((2 : ℝ) ^ p * Cb.card * KM * (A + B + T) ^ p) ^ (1 / p) =
        ((2 : ℝ) ^ p) ^ (1 / p) * (Cb.card : ℝ) ^ (1 / p) * KM ^ (1 / p) *
          ((A + B + T) ^ p) ^ (1 / p) := by
      rw [Real.mul_rpow (mul_nonneg (mul_nonneg h2p hCp) hKM0) (Real.rpow_nonneg hABT _),
        Real.mul_rpow (mul_nonneg h2p hCp) hKM0, Real.mul_rpow h2p hCp]
    have e2 : ((2 : ℝ) ^ p) ^ (1 / p) = 2 := by
      rw [← Real.rpow_mul (by norm_num), mul_one_div_cancel hp0.ne', Real.rpow_one]
    have e3 : ((A + B + T) ^ p) ^ (1 / p) = A + B + T := by
      rw [← Real.rpow_mul hABT, mul_one_div_cancel hp0.ne', Real.rpow_one]
    calc (∑ u ∈ Cb, E u ^ p) ^ (1 / p)
        ≤ ((2 : ℝ) ^ p * Cb.card * KM * (A + B + T) ^ p) ^ (1 / p) :=
          Real.rpow_le_rpow hsum0 hEp (by positivity)
      _ = 2 * (Cb.card : ℝ) ^ (1 / p) * KM ^ (1 / p) * (A + B + T) := by rw [e1, e2, e3]
  -- Hölder
  have hH := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Cb) hpq.symm (fun u _ => hW0 u)
    (fun u _ => hE0 u)
  have hWq : (∑ u ∈ Cb, W u ^ q) ^ (1 / q) ≤ M ^ (1 / q) * (Cb.card : ℝ) ^ (1 / q) := by
    rw [← Real.mul_rpow hM (Nat.cast_nonneg _)]
    exact Real.rpow_le_rpow (Finset.sum_nonneg fun u _ => Real.rpow_nonneg (hW0 u) _) hWM
      (by positivity)
  have hcard : (Cb.card : ℝ) ^ (1 / q) * (Cb.card : ℝ) ^ (1 / p) = Cb.card := by
    rw [← Real.rpow_add hC0, hinv, Real.rpow_one]
  have hmain : ∑ u ∈ Cb, W u * E u ≤
      2 * M ^ (1 / q) * KM ^ (1 / p) * (Cb.card * (A + B + T)) := by
    refine hH.trans ?_
    have hM0 : 0 ≤ M ^ (1 / q) * (Cb.card : ℝ) ^ (1 / q) := by positivity
    calc (∑ u ∈ Cb, W u ^ q) ^ (1 / q) * (∑ u ∈ Cb, E u ^ p) ^ (1 / p)
        ≤ (M ^ (1 / q) * (Cb.card : ℝ) ^ (1 / q)) *
          (2 * (Cb.card : ℝ) ^ (1 / p) * KM ^ (1 / p) * (A + B + T)) :=
          mul_le_mul hWq hEp' (Real.rpow_nonneg (Finset.sum_nonneg fun u _ =>
            Real.rpow_nonneg (hE0 u) _) _) hM0
      _ = 2 * M ^ (1 / q) * KM ^ (1 / p) *
          (((Cb.card : ℝ) ^ (1 / q) * (Cb.card : ℝ) ^ (1 / p)) * (A + B + T)) := by ring
      _ = _ := by rw [hcard]
  -- the three terms
  have hsumE0 : 0 ≤ ∑ z ∈ D, E z := Finset.sum_nonneg fun z _ => hE0 z
  have hratio : (Cb.card : ℝ) / D.card ≤ 1 := div_le_one_of_le₀ hCD hD0.le
  have hCA : Cb.card * A ≤ ∑ z ∈ D, E z := by
    calc (Cb.card : ℝ) * A = ((Cb.card : ℝ) / D.card) * ∑ z ∈ D, E z := by
          rw [hA]; unfold avg; ring
      _ ≤ 1 * ∑ z ∈ D, E z := mul_le_mul_of_nonneg_right hratio hsumE0
      _ = ∑ z ∈ D, E z := one_mul _
  have hCB : Cb.card * B ≤ S := by
    calc (Cb.card : ℝ) * B = ((Cb.card : ℝ) / D.card) * S := by rw [hB]; ring
      _ ≤ 1 * S := mul_le_mul_of_nonneg_right hratio hS0
      _ = S := one_mul _
  have hp' : 0 ≤ 1 - 1 / p := by
    have : 1 / p < 1 := by rw [div_lt_one hp0]; exact hp1
    linarith
  have hCT : Cb.card * T = (Cb.card : ℝ) ^ (1 - 1 / p) * S := by
    rw [hT, show (1 : ℝ) - 1 / p = 1 + -(1 / p) by ring, Real.rpow_add hC0, Real.rpow_one]
    ring
  have hc1 : 1 ≤ (Cb.card : ℝ) ^ (1 - 1 / p) := Real.one_le_rpow hC1 hp'
  have hS1 : S ≤ (Cb.card : ℝ) ^ (1 - 1 / p) * S := le_mul_of_one_le_left hS0 hc1
  have hfin : Cb.card * (A + B + T) ≤
      2 * (∑ z ∈ D, E z + (Cb.card : ℝ) ^ (1 - 1 / p) * ∑ z ∈ D, edgeSq γ z) := by
    have hX : (Cb.card : ℝ) ^ (1 - 1 / p) * S ≤
        (Cb.card : ℝ) ^ (1 - 1 / p) * ∑ z ∈ D, edgeSq γ z :=
      mul_le_mul_of_nonneg_left hSΓ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have e : (Cb.card : ℝ) * (A + B + T) = Cb.card * A + Cb.card * B + Cb.card * T := by ring
    rw [e]
    linarith
  have hK0 : 0 ≤ 2 * M ^ (1 / q) * KM ^ (1 / p) := by positivity
  calc ∑ u ∈ Cb, W u * E u ≤ 2 * M ^ (1 / q) * KM ^ (1 / p) * (Cb.card * (A + B + T)) := hmain
    _ ≤ 2 * M ^ (1 / q) * KM ^ (1 / p) *
        (2 * (∑ z ∈ D, E z + (Cb.card : ℝ) ^ (1 - 1 / p) * ∑ z ∈ D, edgeSq γ z)) :=
      mul_le_mul_of_nonneg_left hfin hK0
    _ = _ := by ring

/-- **The weighted energy of one child of a cell**: for the cube `cube (n u - 1) u`, either the
cell of `u` itself (`n u = 0`) or a child of it carrying the Meyers estimate. -/
theorem sum_child_weight_energy_le {n : Vertex 2 → ℕ}
    (hv : ∀ z, ω ∈ infiniteComponentEvent z → openLaplacian ω v z = edgeDiv ω γ z)
    {ε CM : ℝ} (hε : 0 < ε) (hCM : 0 ≤ CM)
    (hMey : ∀ x z, 1 ≤ n x → z ∈ cube (n x) x → GeneralDim.MeyersCube ε CM ω (n x - 1) z)
    {W : Vertex 2 → ℝ} (hW0 : ∀ u, 0 ≤ W u) {M : ℝ} (hM : 0 ≤ M)
    (hWM : ∀ x, ∑ u ∈ cube (n x) x, W u ^ Real.conjExponent (1 + ε / 2) ≤
      M * (cube (n x) x).card) (u : Vertex 2) :
    ∑ u' ∈ cube (n u - 1) u, W u' * clusterOpenEnergy ω v u' ≤
      if n u = 0 then M ^ (1 / Real.conjExponent (1 + ε / 2)) * clusterOpenEnergy ω v u else
        cellConst ε CM (9 * M) *
          (∑ z ∈ enl 1 (n u - 1) u, clusterOpenEnergy ω v z +
            ((cube (n u - 1) u).card : ℝ) ^ (1 - 1 / (1 + ε / 2)) *
              ∑ z ∈ enl 1 (n u - 1) u, edgeSq γ z) := by
  have hp1 : 1 < 1 + ε / 2 := by linarith
  have hq0 : 0 < Real.conjExponent (1 + ε / 2) :=
    (Real.HolderConjugate.conjExponent hp1).symm.pos
  split_ifs with h0
  · rw [h0, Nat.zero_sub, cube_zero, Finset.sum_singleton]
    have hw := hWM u
    rw [h0, cube_zero, Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, mul_one] at hw
    have hWle : W u ≤ M ^ (1 / Real.conjExponent (1 + ε / 2)) := by
      have := Real.rpow_le_rpow (Real.rpow_nonneg (hW0 u) _) hw (by positivity :
        (0 : ℝ) ≤ 1 / Real.conjExponent (1 + ε / 2))
      rwa [← Real.rpow_mul (hW0 u), mul_one_div_cancel hq0.ne', Real.rpow_one] at this
    exact mul_le_mul_of_nonneg_right hWle (clusterOpenEnergy_nonneg ω v u)
  · have hk : n u = (n u - 1) + 1 := by omega
    have hMu := hMey u u (by omega) (mem_cube_self _ u)
    refine sum_weight_energy_le_of_meyersCube hv hε hCM hMu hW0 (by positivity) ?_
    have hsub : cube (n u - 1) u ⊆ cube (n u) u := IsCellScale.cube_pred_subset u
    have h1 : ∑ u' ∈ cube (n u - 1) u, W u' ^ Real.conjExponent (1 + ε / 2) ≤
        ∑ u' ∈ cube (n u) u, W u' ^ Real.conjExponent (1 + ε / 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun u' _ _ => Real.rpow_nonneg (hW0 u') _
    have h2 : ((cube (n u) u).card : ℝ) = 9 * (cube (n u - 1) u).card := by
      conv_lhs => rw [hk]
      rw [card_cube_succ]
      norm_num
    calc _ ≤ _ := h1
      _ ≤ M * (cube (n u) u).card := hWM u
      _ = 9 * M * (cube (n u - 1) u).card := by rw [h2]; ring

/-- **The weighted energy over the cells** (the summation of estimate (2) over the partition):
`Σ_u W(u) E(u) ≤ K (Σ_z E(z) + Σ_z (9^{n(z)})^{1 - 1/p} Γ(z))`. -/
theorem tsum_weight_energy_le {n : Vertex 2 → ℕ} (hn : IsCellScale n)
    (hv : ∀ z, ω ∈ infiniteComponentEvent z → openLaplacian ω v z = edgeDiv ω γ z)
    {ε CM : ℝ} (hε : 0 < ε) (hCM : 0 ≤ CM)
    (hMey : ∀ x z, 1 ≤ n x → z ∈ cube (n x) x → GeneralDim.MeyersCube ε CM ω (n x - 1) z)
    {W : Vertex 2 → ℝ} (hW0 : ∀ u, 0 ≤ W u) {M : ℝ} (hM : 0 ≤ M)
    (hWM : ∀ x, ∑ u ∈ cube (n x) x, W u ^ Real.conjExponent (1 + ε / 2) ≤
      M * (cube (n x) x).card) :
    ∑' u, ENNReal.ofReal (W u * clusterOpenEnergy ω v u) ≤
      ENNReal.ofReal (M ^ (1 / Real.conjExponent (1 + ε / 2)) + 48 * cellConst ε CM (9 * M)) *
        (∑' z, ENNReal.ofReal (clusterOpenEnergy ω v z) +
          ∑' z, ENNReal.ofReal (((9 : ℝ) ^ n z) ^ (1 - 1 / (1 + ε / 2)) * edgeSq γ z)) := by
  set α : ℝ := 1 - 1 / (1 + ε / 2) with hα
  have hα0 : 0 ≤ α := by
    have : 1 / (1 + ε / 2) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  set K := cellConst ε CM (9 * M) with hK
  have hK0 : 0 ≤ K := by
    rw [hK]; unfold cellConst; positivity
  set m := M ^ (1 / Real.conjExponent (1 + ε / 2)) with hm
  have hm0 : 0 ≤ m := Real.rpow_nonneg hM _
  set E := clusterOpenEnergy ω v with hE
  have hE0 : ∀ z, 0 ≤ E z := clusterOpenEnergy_nonneg ω v
  have hWE0 : ∀ u, 0 ≤ W u * E u := fun u => mul_nonneg (hW0 u) (hE0 u)
  set F : Vertex 2 → ℝ := fun z => ((9 : ℝ) ^ n z) ^ α * edgeSq γ z with hF
  have hF0 : ∀ z, 0 ≤ F z := fun z => mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (edgeSq_nonneg γ z)
  set c : Vertex 2 → Vertex 2 → ℝ≥0∞ := fun u z =>
    if 1 ≤ n u ∧ z ∈ enl 1 (n u - 1) u then ((cube (n u - 1) u).card : ℝ≥0∞)⁻¹ else 0 with hc
  rw [hn.tsum_eq_tsum_avg]
  have hcard_pos : ∀ u, ((cube (n u - 1) u).card : ℝ≥0∞) ≠ 0 := fun u => by
    have := card_cube_pos (d := 2) (n u - 1) u
    exact_mod_cast (Nat.cast_pos.1 this).ne'
  -- the bound of each average
  have hu : ∀ u, ((cube (n u - 1) u).card : ℝ≥0∞)⁻¹ *
      ∑ u' ∈ cube (n u - 1) u, ENNReal.ofReal (W u' * E u') ≤
      ENNReal.ofReal m * (if n u = 0 then ENNReal.ofReal (E u) else 0) +
        ENNReal.ofReal K * ((∑' z, c u z * ENNReal.ofReal (E z)) +
          ∑' z, c u z * ENNReal.ofReal (F z)) := by
    intro u
    have hb := sum_child_weight_energy_le hv hε hCM hMey hW0 hM hWM u
    rw [← ENNReal.ofReal_sum_of_nonneg fun u' _ => hWE0 u']
    by_cases h0 : n u = 0
    · rw [if_pos h0] at hb
      have hc0 : ∀ z, c u z = 0 := fun z => by
        simp only [hc]; rw [if_neg]; omega
      simp only [hc0, zero_mul, tsum_zero, add_zero, mul_zero]
      rw [if_pos h0]
      have e : cube (n u - 1) u = {u} := by rw [h0, Nat.zero_sub, cube_zero]
      rw [e, Finset.card_singleton, Nat.cast_one, inv_one, one_mul, ← ENNReal.ofReal_mul hm0,
        Finset.sum_singleton]
      rw [e, Finset.sum_singleton] at hb
      exact ENNReal.ofReal_le_ofReal hb
    · rw [if_neg h0] at hb
      rw [if_neg h0, mul_zero, zero_add]
      have hk : n u = (n u - 1) + 1 := by omega
      -- the factor `|□|^α` is at most `(9^{n z})^α` on the enlargement
      have hcz : ∀ z ∈ enl 1 (n u - 1) u,
          ((cube (n u - 1) u).card : ℝ) ^ α * edgeSq γ z ≤ F z := by
        intro z hz
        have hkz := (hn.le_of_mem_enl hk hz).1
        have hcard : ((cube (n u - 1) u).card : ℝ) = (9 : ℝ) ^ (n u - 1) := by
          rw [card_cube, ← pow_mul, mul_comm, pow_mul]; norm_num
        rw [hcard]
        refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity)
          (pow_le_pow_right₀ (by norm_num) hkz) hα0) (edgeSq_nonneg γ z)
      have hsplit : ENNReal.ofReal (K * (∑ z ∈ enl 1 (n u - 1) u, E z +
          ((cube (n u - 1) u).card : ℝ) ^ α * ∑ z ∈ enl 1 (n u - 1) u, edgeSq γ z)) ≤
          ENNReal.ofReal K * (∑ z ∈ enl 1 (n u - 1) u, ENNReal.ofReal (E z) +
            ∑ z ∈ enl 1 (n u - 1) u, ENNReal.ofReal (F z)) := by
        rw [ENNReal.ofReal_mul hK0, ← ENNReal.ofReal_sum_of_nonneg fun z _ => hE0 z,
          ← ENNReal.ofReal_sum_of_nonneg fun z _ => hF0 z,
          ← ENNReal.ofReal_add (Finset.sum_nonneg fun z _ => hE0 z)
            (Finset.sum_nonneg fun z _ => hF0 z)]
        gcongr
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum hcz
      have htsum : ∀ g : Vertex 2 → ℝ≥0∞, ∑' z, c u z * g z =
          ((cube (n u - 1) u).card : ℝ≥0∞)⁻¹ * ∑ z ∈ enl 1 (n u - 1) u, g z := by
        intro g
        rw [Finset.mul_sum, tsum_eq_sum (s := enl 1 (n u - 1) u) fun z hz => by
          simp only [hc]; rw [if_neg (fun h => hz h.2), zero_mul]]
        refine Finset.sum_congr rfl fun z hz => ?_
        simp only [hc]; rw [if_pos ⟨by omega, hz⟩]
      rw [htsum, htsum, ← mul_add, ← mul_assoc, mul_comm (ENNReal.ofReal K), mul_assoc]
      gcongr
      exact (ENNReal.ofReal_le_ofReal hb).trans hsplit
  refine (ENNReal.tsum_le_tsum hu).trans ?_
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_add,
    ENNReal.tsum_comm (f := fun u z => c u z * ENNReal.ofReal (E z)),
    ENNReal.tsum_comm (f := fun u z => c u z * ENNReal.ofReal (F z))]
  simp only [ENNReal.tsum_mul_right]
  have hov : ∀ z, ∑' u, c u z ≤ 48 := fun z => hn.tsum_enl_le z
  have h1 : ∑' u, (if n u = 0 then ENNReal.ofReal (E u) else 0) ≤ ∑' u, ENNReal.ofReal (E u) :=
    ENNReal.tsum_le_tsum fun u => by split_ifs <;> simp
  have h2 : ∀ g : Vertex 2 → ℝ≥0∞, ∑' z, (∑' u, c u z) * g z ≤ 48 * ∑' z, g z := by
    intro g
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun z => by gcongr; exact hov z
  set X := ∑' z, ENNReal.ofReal (E z)
  set Y := ∑' z, ENNReal.ofReal (F z)
  have hsum : ENNReal.ofReal (m + 48 * K) = ENNReal.ofReal m + 48 * ENNReal.ofReal K := by
    rw [ENNReal.ofReal_add hm0 (by positivity), ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [hsum]
  calc ENNReal.ofReal m * ∑' u, (if n u = 0 then ENNReal.ofReal (E u) else 0) +
        ENNReal.ofReal K * (∑' z, (∑' u, c u z) * ENNReal.ofReal (E z) +
          ∑' z, (∑' u, c u z) * ENNReal.ofReal (F z))
      ≤ ENNReal.ofReal m * X + ENNReal.ofReal K * (48 * X + 48 * Y) := by
        gcongr
        · exact h2 _
        · exact h2 _
    _ ≤ ENNReal.ofReal m * X + ENNReal.ofReal m * Y + ENNReal.ofReal K * (48 * X + 48 * Y) := by
        gcongr
        exact le_self_add
    _ = (ENNReal.ofReal m + 48 * ENNReal.ofReal K) * (X + Y) := by ring

end Meyers

end Rigidity.Corrector
