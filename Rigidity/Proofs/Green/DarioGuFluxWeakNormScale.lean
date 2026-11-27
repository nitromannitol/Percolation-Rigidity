import Rigidity.Proofs.Green.DarioGuFluxCoarsening

/-!
# Step 1 of the proof of Proposition B.1 of Dario–Gu at a fixed scale

The deterministic part of Steps 1 and 3 of the proof of Proposition B.1 (Appendix B) in
dimension two: at a configuration of the good set `G` with a partition of the good cubes, for
`r ∈ [3^n, 3^{n+1})` and partition cubes of side at most `L` near `y`, the weak norm bounds of
the centered flux of `ℤ²` (`exists_fluxWeakNormBox`) and of the density (`exists_densityWeakNorm`)
on a set `S ⊇ y + [-3^{n+2}, 3^{n+2}]²` with constants `Y_f, Z_f, Y_d, Z_d` give the weak norm
bound of the centered flux `g̃_{e_k}` on `𝒞_∞ ∩ B_r(y)` (`weakNormLe_of_scale_bounds`):

`‖[g̃_{e_k}]_i‖_{H̲^{-1}(𝒞_∞ ∩ B_r(y))} ≤ max((Y_f + σ Y_d)(1 + L), 5 (Z_f + σ Z_d)(3 + 10L)² L / (2·3^{n-1}))`.

The test function `v` is coarsened (`coarseTest`); the pairing of `g̃` with `v` is the pairing of
`g - (σ/2) δ_{ik} (1_{𝒞_∞} - θ)` with the coarsened function (`ā = σθ/2`, (B.5) of the source,
(B.13)); the norms of the coarsened function are those of `DarioGuFluxCoarsening`, and
`|𝒞_∞ ∩ B_r(y)| ≥ (2·3^{n-1} + 1)²/L²` (`card_mul_le_card_dgClusterBall`) replaces the minimal
scale of the density of the cluster used in the source.
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Poincare Rigidity.Corrector
  Rigidity.Percolation Rigidity.External Rigidity.Proofs.S2
open scoped ENNReal Classical

namespace Rigidity.Green

section Scale

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- On the cluster, the flux of the corrected plane is the edge flux of the corrector. -/
theorem fluxVal_eq_edgeFlux {ω : Configuration 2} (hω : ω ∈ G)
    (h : HasUniqueInfiniteOpenComponent ω) {y : Vertex 2} {χ : Fin 2 → Vertex 2 → ℝ}
    (hχ : IsDGCorrector (uniqueInfiniteComponent h) y χ) (k i : Fin 2) {x : Vertex 2}
    (hx : x ∈ (uniqueInfiniteComponent h).supp) :
    fluxVal hG hGv k ω (x, i) = edgeFlux ω χ k i x := by
  rw [fluxVal_eq_planeFlux hG hGv hω h (hχ k).1, planeFlux, edgeFlux]
  have hhead : edgeHead ((x, i) : LatticeEdge) = x + Pi.single i 1 := rfl
  by_cases hadj : (openGraph ω).Adj x (x + Pi.single i 1)
  · have hc : EdgeOpen ω (x, i) ∧ ((x, i) : LatticeEdge).1 ∈ (uniqueInfiniteComponent h).supp :=
      ⟨hadj, hx⟩
    have hx' : x + Pi.single i 1 ∈ (uniqueInfiniteComponent h).supp :=
      (uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp hx hadj
    rw [if_pos hc, if_pos hadj, hhead, extendComp_of_mem _ _ hx', extendComp_of_mem _ _ hx]
    simp only [Pi.add_apply]
    by_cases hik : i = k
    · subst hik
      simp only [Pi.single_eq_same, if_true]
      push_cast
      ring
    · rw [Pi.single_eq_of_ne (Ne.symm hik), if_neg hik]
      push_cast
      ring
  · have hc : ¬ (EdgeOpen ω (x, i) ∧ ((x, i) : LatticeEdge).1 ∈ (uniqueInfiniteComponent h).supp) :=
      fun hc => hadj hc.1
    rw [if_neg hc, if_neg hadj]

theorem fluxVal_eq_zero_of_not_mem {ω : Configuration 2} (h : HasUniqueInfiniteOpenComponent ω)
    (k i : Fin 2) {x : Vertex 2} (hx : x ∉ (uniqueInfiniteComponent h).supp) :
    fluxVal hG hGv k ω (x, i) = 0 := by
  unfold fluxVal
  rw [if_neg fun hc => hx ((mem_uniqueInfiniteComponent_iff h x).2 hc.2)]

/-- **The centered flux of the cluster through the flux of `ℤ²` and the density**:
`1_{𝒞_∞} g̃ = g - (σ/2) δ_{ik} (1_{𝒞_∞} - θ)` when `ā = σθ/2`. -/
theorem ite_centeredFlux_eq {ω : Configuration 2} (hω : ω ∈ G)
    (h : HasUniqueInfiniteOpenComponent ω) {y : Vertex 2} {χ : Fin 2 → Vertex 2 → ℝ}
    (hχ : IsDGCorrector (uniqueInfiniteComponent h) y χ) (k i : Fin 2) {abar σ θ : ℝ}
    (habar : abar = σ * θ / 2) (x : Vertex 2) :
    (if x ∈ (uniqueInfiniteComponent h).supp then centeredFlux ω σ χ k i x else 0) =
      (fluxVal hG hGv k ω (x, i) - if i = k then abar else 0) -
        σ / 2 * (if i = k then 1 else 0) * clusterDeviation ω θ x := by
  unfold clusterDeviation
  by_cases hx : x ∈ (uniqueInfiniteComponent h).supp
  · rw [if_pos hx, centeredFlux_eq_edgeFlux, fluxVal_eq_edgeFlux hG hGv hω h hχ k i hx,
      Set.indicator_of_mem ((mem_uniqueInfiniteComponent_iff h x).1 hx), habar]
    split_ifs <;> ring
  · rw [if_neg hx, fluxVal_eq_zero_of_not_mem hG hGv h k i hx,
      Set.indicator_of_notMem (fun hc => hx ((mem_uniqueInfiniteComponent_iff h x).2 hc)), habar]
    split_ifs <;> ring

/-- `‖v‖_{H̲¹(V)} = (√|V|)⁻¹ ((√|V|)⁻¹ ‖v‖_{ℓ²(V)}) + (√|V|)⁻¹ ‖∇v‖_{ℓ²(V)}`. -/
theorem clusterH1Norm_eq {ω : Configuration 2} {V : Finset (Vertex 2)} (hV : 0 < V.card)
    (v : Vertex 2 → ℝ) :
    clusterH1Norm ω V v = (Real.sqrt V.card)⁻¹ * ((Real.sqrt V.card)⁻¹ *
      Real.sqrt (∑ x ∈ V, v x ^ 2)) +
        (Real.sqrt V.card)⁻¹ * Real.sqrt (∑ x ∈ V, openGradNorm ω V v x ^ 2) := by
  have hc : (0 : ℝ) < V.card := by exact_mod_cast hV
  unfold clusterH1Norm
  rw [Real.rpow_neg hc.le, ← Real.sqrt_eq_rpow, Real.sqrt_mul (inv_nonneg.2 hc.le),
    Real.sqrt_mul (inv_nonneg.2 hc.le), Real.sqrt_inv]

theorem sqrt_le_mul_sqrt_of_le {X Y c : ℝ} (hc : 0 ≤ c) (h : X ≤ c ^ 2 * Y) :
    Real.sqrt X ≤ c * Real.sqrt Y := by
  calc Real.sqrt X ≤ Real.sqrt (c ^ 2 * Y) := Real.sqrt_le_sqrt h
    _ = c * Real.sqrt Y := by
        rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- **The weak norm of the centered flux on `𝒞_∞ ∩ B_r(y)` at a good scale.** -/
theorem weakNormLe_of_scale_bounds {ω : Configuration 2} (hω : ω ∈ G)
    (h : HasUniqueInfiniteOpenComponent ω) (hP : PlanarPartitionEvent ω) {y : Vertex 2}
    {χ : Fin 2 → Vertex 2 → ℝ} (hχ : IsDGCorrector (uniqueInfiniteComponent h) y χ)
    (k i : Fin 2) {abar σ θ : ℝ} (habar : abar = σ * θ / 2) (hσ : 0 ≤ σ) {r : ℝ} {n L : ℕ}
    (hn : 2 ≤ n) (hr1 : (3 : ℝ) ^ n ≤ r) (hr2 : r < 3 ^ (n + 1)) (hL1 : 1 ≤ L)
    (hL : L ≤ 3 ^ (n - 2))
    (hside : ∀ z ∈ supBox y (2 * 3 ^ (n + 2) + 2), planarSide ω z ≤ L)
    {S : Finset (Vertex 2)} (hS : supBox y (3 ^ (n + 2)) ⊆ S)
    {Yf Zf Yd Zd : ℝ} (hYf : 0 ≤ Yf) (hZf : 0 ≤ Zf) (hYd : 0 ≤ Yd) (hZd : 0 ≤ Zd)
    (hflux : ∀ w : Vertex 2 → ℝ, (∀ x ∉ S, w x = 0) →
      (∀ x ∉ supBox y (2 * 3 ^ (n + 2) + 1), ∀ j : Fin 2, w (x + unit j) = w x) →
      |∑ x ∈ S, (fluxVal hG hGv k ω (x, i) - if i = k then abar else 0) * w x| ≤
        Yf * Real.sqrt (∑ x ∈ S, w x ^ 2) + Zf * Real.sqrt (∑ j : Fin 2,
          ∑ x ∈ supBox y (2 * 3 ^ (n + 2) + 1), (w (x + unit j) - w x) ^ 2))
    (hdens : ∀ w : Vertex 2 → ℝ,
      |∑ x ∈ S, w x * clusterDeviation ω θ x| ≤
        Yd * Real.sqrt (∑ x ∈ S, w x ^ 2) + Zd * Real.sqrt (∑ j : Fin 2,
          ∑ x ∈ supBox y (2 * 3 ^ (n + 2) + 1), (w (x + unit j) - w x) ^ 2)) :
    WeakNormLe ω (dgClusterBall (uniqueInfiniteComponent h) y r) (centeredFlux ω σ χ k i)
      (max ((Yf + σ * Yd) * (1 + L))
        (5 * (Zf + σ * Zd) * (3 + 10 * (L : ℝ)) ^ 2 * L / (2 * 3 ^ (n - 1)))) := by
  set Kc := uniqueInfiniteComponent h with hKc
  set V := dgClusterBall Kc y r with hV
  set T := supBox y (2 * 3 ^ (n + 2) + 1) with hT
  have hLr : (L : ℝ) ≤ 3 ^ (n - 2) := by exact_mod_cast hL
  have h3n : (3 : ℝ) ^ n = 9 * 3 ^ (n - 2) := by
    rw [show n = (n - 2) + 2 by omega, pow_add]
    norm_num
    ring
  have h3n1 : (3 : ℝ) ^ (n - 1) = 3 * 3 ^ (n - 2) := by
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
    ring
  -- the cluster ball lies in the box of radius `3^{n+1}`
  have hVbox : ∀ z ∈ V, ∀ i', |z i' - y i'| ≤ ((3 ^ (n + 1) : ℕ) : ℤ) := by
    intro z hz i'
    rw [hV, mem_dgClusterBall] at hz
    have h1 := latticeDist_ge_abs z y i'
    have h2 : |((z i' - y i' : ℤ) : ℝ)| < (3 : ℝ) ^ (n + 1) := by
      push_cast
      linarith [hz.2]
    have h3 : |z i' - y i'| < ((3 ^ (n + 1) : ℕ) : ℤ) := by
      have : (|z i' - y i'| : ℝ) < ((3 ^ (n + 1) : ℕ) : ℝ) := by push_cast; exact_mod_cast h2
      exact_mod_cast this
    exact h3.le
  have hboxmono : ∀ {a b : ℕ}, a ≤ b → supBox y a ⊆ supBox y b := by
    intro a b hab z hz
    rw [mem_supBox] at hz ⊢
    intro i'
    have := hz i'
    have hab' : (a : ℤ) ≤ b := by exact_mod_cast hab
    linarith
  have h31 : 3 ^ (n + 1) ≤ 2 * 3 ^ (n + 2) + 2 := by
    have : 3 ^ (n + 1) ≤ 3 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hVsub : ∀ z ∈ V, z ∈ supBox y (3 ^ (n + 1)) := fun z hz => mem_supBox.2 (hVbox z hz)
  have hsideV : ∀ z ∈ V, planarSide ω z ≤ L := fun z hz => hside z (hboxmono h31 (hVsub z hz))
  -- the support of the coarsened function
  intro v hv
  set w := coarseTest ω Kc.supp V v with hw
  have hL3 : 3 ^ (n + 1) + L ≤ 3 ^ (n + 2) := by
    have h1 : L ≤ 3 ^ n := hL.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : 3 ^ (n + 2) = 3 * 3 ^ (n + 1) := by ring
    have h3 : 3 ^ (n + 1) = 3 * 3 ^ n := by ring
    omega
  have hsupp : ∀ x, w x ≠ 0 → x ∈ supBox y (3 ^ (n + 2)) := by
    intro x hx
    have h1 := coarseTest_eq_zero_of_far hP (K := Kc.supp) hVbox hsideV v hx
    refine hboxmono hL3 (mem_supBox.2 fun i' => ?_)
    have := h1 i'
    push_cast at this ⊢
    exact this
  have hwS : ∀ x ∉ S, w x = 0 := fun x hx => by
    by_contra hne
    exact hx (hS (hsupp x hne))
  have hwT : ∀ x ∉ T, ∀ j : Fin 2, w (x + unit j) = w x := by
    intro x hx j
    have hx1 : w x = 0 := by
      by_contra hne
      exact hx (hboxmono (by omega) (hsupp x hne))
    have hx2 : w (x + unit j) = 0 := by
      by_contra hne
      have h1 := mem_supBox.1 (hsupp _ hne)
      apply hx
      rw [mem_supBox]
      intro i'
      have h2 := h1 i'
      have h3 := abs_unit_sub_le x j i'
      have : |x i' - y i'| ≤ |(x + unit j) i' - y i'| + |(x + unit j) i' - x i'| := by
        have := abs_sub_le (x i') ((x + unit j) i') (y i')
        rw [abs_sub_comm (x i') ((x + unit j) i')] at this
        linarith
      have h4 : (0 : ℤ) ≤ 3 ^ (n + 2) := by positivity
      push_cast at h2 ⊢
      linarith
    rw [hx1, hx2]
  -- the pairing
  have hVK : ∀ x ∈ V, x ∈ Kc.supp := fun x hx => ((mem_dgClusterBall Kc y x r).1 hx).1
  have hVS : V ⊆ S := fun x hx => hS (hboxmono (Nat.pow_le_pow_right (by norm_num) (by omega))
    (hVsub x hx))
  have hpair : ∑ x ∈ S, (if x ∈ Kc.supp then centeredFlux ω σ χ k i x else 0) * w x =
      ∑ x ∈ V, (if x ∈ Kc.supp then centeredFlux ω σ χ k i x else 0) * v x :=
    sum_mul_coarseTest_eq (ω := ω) hVK hVS v _ (fun x hx => if_neg hx)
  have hV1 : ∑ x ∈ V, centeredFlux ω σ χ k i x * v x =
      ∑ x ∈ S, (fluxVal hG hGv k ω (x, i) - if i = k then abar else 0) * w x -
        σ / 2 * (if i = k then 1 else 0) * ∑ x ∈ S, w x * clusterDeviation ω θ x := by
    have e1 : ∑ x ∈ V, centeredFlux ω σ χ k i x * v x =
        ∑ x ∈ V, (if x ∈ Kc.supp then centeredFlux ω σ χ k i x else 0) * v x :=
      Finset.sum_congr rfl fun x hx => by rw [if_pos (hVK x hx)]
    rw [e1, ← hpair, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ite_centeredFlux_eq hG hGv hω h hχ k i habar x]
    ring
  -- the norms of the coarsened function
  set N0 := Real.sqrt (∑ x ∈ V, v x ^ 2) with hN0
  set N1 := Real.sqrt (∑ x ∈ V, openGradNorm ω V v x ^ 2) with hN1
  have hw0 : Real.sqrt (∑ x ∈ S, w x ^ 2) ≤ (1 + L) * N0 := by
    refine sqrt_le_mul_sqrt_of_le (by positivity) ?_
    refine (sum_sq_coarseTest_le hP Kc.supp hsideV v S).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun x _ => sq_nonneg _)
    have : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    nlinarith
  have hK : ∀ x ∈ Kc.supp, ((openGraph ω).connectedComponentMk x).supp.Infinite := by
    intro x hx
    have : (openGraph ω).connectedComponentMk x = Kc :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hx
    rw [this]
    exact uniqueInfiniteComponent_infinite h
  have hsideT : ∀ x ∈ T, planarSide ω x ≤ L ∧ ∀ j : Fin 2, planarSide ω (x + unit j) ≤ L := by
    intro x hx
    refine ⟨hside x (hboxmono (by omega) hx), fun j => hside _ ?_⟩
    rw [mem_supBox] at hx ⊢
    intro i'
    have h1 := hx i'
    have h2 := abs_unit_sub_le x j i'
    have : |(x + unit j) i' - y i'| ≤ |(x + unit j) i' - x i'| + |x i' - y i'| := by
      have := abs_sub_le ((x + unit j) i') (x i') (y i')
      linarith
    push_cast at h1 ⊢
    linarith
  have hw1 : Real.sqrt (∑ j : Fin 2, ∑ x ∈ T, (w (x + unit j) - w x) ^ 2) ≤
      5 * (3 + 10 * (L : ℝ)) ^ 2 * N1 := by
    refine sqrt_le_mul_sqrt_of_le (by positivity) ?_
    refine (sum_sq_grad_coarseTest_le hP hK hv T hsideT).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun x _ => sq_nonneg _)
    have : (0 : ℝ) ≤ (3 + 10 * (L : ℝ)) ^ 4 := by positivity
    nlinarith
  -- the size of `V`
  set m := 3 ^ (n - 1) with hm
  have hmr : 2 * ((m : ℝ) + L) < r := by
    rw [hm]
    push_cast
    rw [h3n1]
    rw [h3n] at hr1
    linarith [pow_pos (by norm_num : (0 : ℝ) < 3) (n - 2)]
  have hsidem : ∀ z ∈ supBox y m, planarSide ω z ≤ L := fun z hz =>
    hside z (hboxmono (by
      have : 3 ^ (n - 1) ≤ 3 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega) hz)
  have hcard := card_mul_le_card_dgClusterBall hP h y hmr hsidem
  have hcard' : ((2 * m + 1 : ℕ) : ℝ) ^ 2 ≤ (L : ℝ) ^ 2 * V.card := hcard
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL1
  have hVpos : 0 < V.card := by
    rcases Nat.eq_zero_or_pos V.card with h0 | h0
    · rw [h0] at hcard'
      simp only [Nat.cast_zero, mul_zero] at hcard'
      have : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) ^ 2 := by positivity
      linarith
    · exact h0
  have hcR : (0 : ℝ) < V.card := by exact_mod_cast hVpos
  have hsqrtV : 2 * (m : ℝ) / L ≤ Real.sqrt V.card := by
    have h1 : (2 * (m : ℝ)) ^ 2 ≤ ((2 * m + 1 : ℕ) : ℝ) ^ 2 := by
      push_cast
      nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    calc 2 * (m : ℝ) / L = Real.sqrt ((2 * (m : ℝ) / L) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt V.card := Real.sqrt_le_sqrt (by
          rw [div_pow, div_le_iff₀ (by positivity)]
          linarith)
  -- the conclusion
  rw [clusterH1Norm_eq hVpos]
  set B := max ((Yf + σ * Yd) * (1 + L))
    (5 * (Zf + σ * Zd) * (3 + 10 * (L : ℝ)) ^ 2 * L / (2 * 3 ^ (n - 1))) with hB
  have hδ : |σ / 2 * (if i = k then (1 : ℝ) else 0)| ≤ σ := by
    split_ifs
    · rw [mul_one, abs_of_nonneg (by positivity)]
      linarith
    · rw [mul_zero, abs_zero]
      exact hσ
  have hNw0 : 0 ≤ Real.sqrt (∑ x ∈ S, w x ^ 2) := Real.sqrt_nonneg _
  have hNw1 : 0 ≤ Real.sqrt (∑ j : Fin 2, ∑ x ∈ T, (w (x + unit j) - w x) ^ 2) :=
    Real.sqrt_nonneg _
  have hmain : ∑ x ∈ V, centeredFlux ω σ χ k i x * v x ≤
      (Yf + σ * Yd) * (1 + L) * N0 + (Zf + σ * Zd) * (5 * (3 + 10 * (L : ℝ)) ^ 2) * N1 := by
    rw [hV1]
    have hf := hflux w hwS hwT
    have hd := hdens w
    have habs : ∑ x ∈ S, (fluxVal hG hGv k ω (x, i) - (if i = k then abar else 0)) * w x -
        σ / 2 * (if i = k then 1 else 0) * ∑ x ∈ S, w x * clusterDeviation ω θ x ≤
        |∑ x ∈ S, (fluxVal hG hGv k ω (x, i) - (if i = k then abar else 0)) * w x| +
          σ * |∑ x ∈ S, w x * clusterDeviation ω θ x| := by
      have h1 := le_abs_self (∑ x ∈ S, (fluxVal hG hGv k ω (x, i) -
        (if i = k then abar else 0)) * w x)
      have h2 : -(σ / 2 * (if i = k then 1 else 0) * ∑ x ∈ S, w x * clusterDeviation ω θ x) ≤
          σ * |∑ x ∈ S, w x * clusterDeviation ω θ x| := by
        have := neg_abs_le (σ / 2 * (if i = k then (1 : ℝ) else 0) *
          ∑ x ∈ S, w x * clusterDeviation ω θ x)
        rw [abs_mul] at this
        have h3 := mul_le_mul_of_nonneg_right hδ (abs_nonneg (∑ x ∈ S, w x *
          clusterDeviation ω θ x))
        linarith
      linarith
    refine habs.trans ?_
    have hσd := mul_le_mul_of_nonneg_left hd hσ
    calc |∑ x ∈ S, (fluxVal hG hGv k ω (x, i) - (if i = k then abar else 0)) * w x| +
          σ * |∑ x ∈ S, w x * clusterDeviation ω θ x|
        ≤ (Yf * Real.sqrt (∑ x ∈ S, w x ^ 2) +
            Zf * Real.sqrt (∑ j : Fin 2, ∑ x ∈ T, (w (x + unit j) - w x) ^ 2)) +
          σ * (Yd * Real.sqrt (∑ x ∈ S, w x ^ 2) +
            Zd * Real.sqrt (∑ j : Fin 2, ∑ x ∈ T, (w (x + unit j) - w x) ^ 2)) :=
          add_le_add hf hσd
      _ = (Yf + σ * Yd) * Real.sqrt (∑ x ∈ S, w x ^ 2) +
          (Zf + σ * Zd) * Real.sqrt (∑ j : Fin 2, ∑ x ∈ T, (w (x + unit j) - w x) ^ 2) := by
          ring
      _ ≤ (Yf + σ * Yd) * ((1 + L) * N0) + (Zf + σ * Zd) * (5 * (3 + 10 * (L : ℝ)) ^ 2 * N1) :=
          add_le_add (mul_le_mul_of_nonneg_left hw0 (by positivity))
            (mul_le_mul_of_nonneg_left hw1 (by positivity))
      _ = (Yf + σ * Yd) * (1 + L) * N0 + (Zf + σ * Zd) * (5 * (3 + 10 * (L : ℝ)) ^ 2) * N1 := by
          ring
  have hN0n : 0 ≤ N0 := Real.sqrt_nonneg _
  have hN1n : 0 ≤ N1 := Real.sqrt_nonneg _
  have ha : (Yf + σ * Yd) * (1 + L) ≤ B := le_max_left _ _
  have hb : (Zf + σ * Zd) * (5 * (3 + 10 * (L : ℝ)) ^ 2) ≤ B * Real.sqrt V.card := by
    have h1 : 5 * (Zf + σ * Zd) * (3 + 10 * (L : ℝ)) ^ 2 * L / (2 * 3 ^ (n - 1)) ≤ B :=
      le_max_right _ _
    have hm0 : (0 : ℝ) < 2 * 3 ^ (n - 1) := by positivity
    have hmm : (m : ℝ) = 3 ^ (n - 1) := by rw [hm]; push_cast; ring
    rw [div_le_iff₀ hm0] at h1
    have hsq : 2 * (3 : ℝ) ^ (n - 1) ≤ L * Real.sqrt V.card := by
      rw [← hmm]
      have := hsqrtV
      rw [div_le_iff₀ hL0] at this
      linarith
    have hB0 : 0 ≤ B := le_trans (by positivity) ha
    have h3 := mul_le_mul_of_nonneg_left hsq hB0
    have h2 : (Zf + σ * Zd) * (5 * (3 + 10 * (L : ℝ)) ^ 2) * L ≤ (B * Real.sqrt V.card) * L := by
      linarith
    exact le_of_mul_le_mul_right h2 hL0
  calc (V.card : ℝ)⁻¹ * ∑ x ∈ V, centeredFlux ω σ χ k i x * v x
      ≤ (V.card : ℝ)⁻¹ * ((Yf + σ * Yd) * (1 + L) * N0 +
          (Zf + σ * Zd) * (5 * (3 + 10 * (L : ℝ)) ^ 2) * N1) :=
        mul_le_mul_of_nonneg_left hmain (inv_nonneg.2 hcR.le)
    _ ≤ (V.card : ℝ)⁻¹ * (B * N0 + B * Real.sqrt V.card * N1) := by
        refine mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right ha hN0n)
          (mul_le_mul_of_nonneg_right hb hN1n)) (inv_nonneg.2 hcR.le)
    _ = B * ((Real.sqrt V.card)⁻¹ * ((Real.sqrt V.card)⁻¹ * N0) +
          (Real.sqrt V.card)⁻¹ * N1) := by
        have hs : 0 < Real.sqrt V.card := Real.sqrt_pos.2 hcR
        have hss : Real.sqrt V.card * Real.sqrt V.card = V.card := Real.mul_self_sqrt hcR.le
        have hVinv : (V.card : ℝ)⁻¹ = (Real.sqrt V.card)⁻¹ * (Real.sqrt V.card)⁻¹ := by
          rw [← mul_inv, hss]
        have h1 : (Real.sqrt V.card)⁻¹ * Real.sqrt V.card = 1 := inv_mul_cancel₀ hs.ne'
        rw [hVinv]
        calc (Real.sqrt V.card)⁻¹ * (Real.sqrt V.card)⁻¹ * (B * N0 + B * Real.sqrt V.card * N1)
            = B * ((Real.sqrt V.card)⁻¹ * ((Real.sqrt V.card)⁻¹ * N0)) +
                B * ((Real.sqrt V.card)⁻¹ * N1) * ((Real.sqrt V.card)⁻¹ * Real.sqrt V.card) := by
              ring
          _ = _ := by rw [h1, mul_one, mul_add]

end Scale

end Rigidity.Green
