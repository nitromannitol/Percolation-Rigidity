import Rigidity.Proofs.Green.GeneralFluxCoarsening
import Rigidity.Proofs.Green.GeneralFluxBox
import Rigidity.Proofs.Green.DarioGuFluxWeakNormScale

/-!
# Step 1 of the proof of Proposition B.1 of Dario–Gu at a fixed scale, on `ℤ^d`

The extension of `DarioGuFluxWeakNormScale.lean` from `ℤ²` to `ℤ^d`: at a configuration of the
good set `G` with a partition of the good cubes, for `r ∈ [3^n, 3^{n+1})` and partition cubes of
side at most `L` near `y`, the weak norm bounds of the centered flux of `ℤ^d`
(`exists_fluxWeakNormBoxD`) and of the density (`exists_densityWeakNormD`) on a set
`S ⊇ y + [-3^{n+2}, 3^{n+2}]^d` with constants `Y_f, Z_f, Y_d, Z_d` give the weak norm bound of the
centered flux `g̃_{e_k}` on `𝒞_∞ ∩ B_r(y)` (`weakNormLeD_of_scale_bounds`):

`‖[g̃_{e_k}]_i‖_{H̲^{-1}(𝒞_∞ ∩ B_r(y))} ≤
  max((Y_f + σ Y_d)(1 + L)^d, (Z_f + σ Z_d) 3d (3 + 6L)^d (L^d/(2m)^d)^{1/2})`

for every `m ≥ 1` with `d (m + L) < r`. The test function `v` is coarsened (`coarseTestD`); the
pairing of `g̃` with `v` is the pairing of `g - (σ/2) δ_{ik} (1_{𝒞_∞} - θ)` with the coarsened
function (`ā = σθ/2`, (B.5) of the source, (eq:2149fr)). The factor `|V|^{-1/d}` of the norm
(1.32) is at least `|V|^{-1/2}` for `d ≥ 2`, and `|𝒞_∞ ∩ B_r(y)| ≥ (2m + 1)^d/L^d`
(`card_mul_le_card_dgClusterBallD`) replaces the minimal scale of the density of the cluster used
in the source.
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.S2
  Rigidity.Poincare.GeneralDim
open scoped ENNReal Classical

namespace Rigidity.Green.GeneralFlux

variable {d : ℕ}

section Scale

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

theorem fluxValD_eq_zero_of_not_mem {ω : Configuration d} (h : HasUniqueInfiniteOpenComponent ω)
    (k i : Fin d) {x : Vertex d} (hx : x ∉ (uniqueInfiniteComponent h).supp) :
    fluxValD hG hGv k ω x i = 0 := by
  unfold fluxValD
  rw [if_neg fun hc => hx ((mem_uniqueInfiniteComponent_iff h x).2 hc.2)]

/-- **The centered flux of the cluster through the flux of `ℤ^d` and the density**:
`1_{𝒞_∞} g̃ = g - (σ/2) δ_{ik} (1_{𝒞_∞} - θ)` when `ā = σθ/2`. -/
theorem ite_centeredFluxD_eq {ω : Configuration d} (hω : ω ∈ G)
    (h : HasUniqueInfiniteOpenComponent ω) {y : Vertex d} {χ : Fin d → Vertex d → ℝ}
    (hχ : IsDGCorrectorD (uniqueInfiniteComponent h) y χ) (k i : Fin d) {abar σ θ : ℝ}
    (habar : abar = σ * θ / 2) (x : Vertex d) :
    (if x ∈ (uniqueInfiniteComponent h).supp then centeredFluxD ω σ χ k i x else 0) =
      (fluxValD hG hGv k ω x i - if i = k then abar else 0) -
        σ / 2 * (if i = k then 1 else 0) * clusterDeviationD ω θ x := by
  unfold clusterDeviationD
  by_cases hx : x ∈ (uniqueInfiniteComponent h).supp
  · rw [if_pos hx, centeredFluxD_eq_fluxValD hG hGv hω h hχ σ k i hx,
      Set.indicator_of_mem ((mem_uniqueInfiniteComponent_iff h x).1 hx), habar]
    split_ifs <;> ring
  · rw [if_neg hx, fluxValD_eq_zero_of_not_mem hG hGv h k i hx,
      Set.indicator_of_notMem (fun hc => hx ((mem_uniqueInfiniteComponent_iff h x).2 hc)), habar]
    split_ifs <;> ring

/-- `‖v‖_{H̲¹(V)} = |V|^{-1/d} ((√|V|)⁻¹ ‖v‖_{ℓ²(V)}) + (√|V|)⁻¹ ‖∇v‖_{ℓ²(V)}`. -/
theorem clusterH1NormD_eq {ω : Configuration d} {V : Finset (Vertex d)} (v : Vertex d → ℝ) :
    clusterH1NormD ω V v = (V.card : ℝ) ^ (-(1 / d : ℝ)) * ((Real.sqrt V.card)⁻¹ *
      Real.sqrt (∑ x ∈ V, v x ^ 2)) +
        (Real.sqrt V.card)⁻¹ * Real.sqrt (∑ x ∈ V, openGradNormD ω V v x ^ 2) := by
  have hc : (0 : ℝ) ≤ V.card := Nat.cast_nonneg _
  unfold clusterH1NormD
  rw [Real.sqrt_mul (inv_nonneg.2 hc), Real.sqrt_mul (inv_nonneg.2 hc), Real.sqrt_inv]

/-- `|V|^{-1/2} ≤ |V|^{-1/d}` for `|V| ≥ 1` and `d ≥ 2`. -/
theorem inv_sqrt_le_rpow_neg (hd : 2 ≤ d) {c : ℝ} (hc : 1 ≤ c) :
    (Real.sqrt c)⁻¹ ≤ c ^ (-(1 / d : ℝ)) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by linarith)]
  refine Real.rpow_le_rpow_of_exponent_le hc ?_
  rw [neg_le_neg_iff]
  exact one_div_le_one_div_of_le (by norm_num) hd'

/-- **The weak norm of the centered flux on `𝒞_∞ ∩ B_r(y)` at a good scale.** -/
theorem weakNormLeD_of_scale_bounds (hd : 2 ≤ d) {ω : Configuration d} (hω : ω ∈ G)
    (h : HasUniqueInfiniteOpenComponent ω) (hP : PartitionEvent ω) {y : Vertex d}
    {χ : Fin d → Vertex d → ℝ} (hχ : IsDGCorrectorD (uniqueInfiniteComponent h) y χ)
    (k i : Fin d) {abar σ θ : ℝ} (habar : abar = σ * θ / 2) (hσ : 0 ≤ σ) {r : ℝ} {n L m : ℕ}
    (hr2 : r < 3 ^ (n + 1)) (hL1 : 1 ≤ L) (hL : L ≤ 3 ^ n) (hm1 : 1 ≤ m) (hmn : m ≤ 3 ^ n)
    (hmr : (d : ℝ) * ((m : ℝ) + L) < r)
    (hside : ∀ z ∈ supBox y (2 * 3 ^ (n + 2) + 2), partSide ω z ≤ L)
    {S : Finset (Vertex d)} (hS : supBox y (3 ^ (n + 2)) ⊆ S)
    {Yf Zf Yd Zd : ℝ} (hYf : 0 ≤ Yf) (hZf : 0 ≤ Zf) (hYd : 0 ≤ Yd) (hZd : 0 ≤ Zd)
    (hflux : ∀ w : Vertex d → ℝ, (∀ x ∉ S, w x = 0) →
      (∀ x ∉ supBox y (2 * 3 ^ (n + 2) + 1), ∀ j : Fin d, w (x + unit j) = w x) →
      |∑ x ∈ S, (fluxValD hG hGv k ω x i - if i = k then abar else 0) * w x| ≤
        Yf * Real.sqrt (∑ x ∈ S, w x ^ 2) + Zf * Real.sqrt (∑ j : Fin d,
          ∑ x ∈ supBox y (2 * 3 ^ (n + 2) + 1), (w (x + unit j) - w x) ^ 2))
    (hdens : ∀ w : Vertex d → ℝ,
      |∑ x ∈ S, w x * clusterDeviationD ω θ x| ≤
        Yd * Real.sqrt (∑ x ∈ S, w x ^ 2) + Zd * Real.sqrt (∑ j : Fin d,
          ∑ x ∈ supBox y (2 * 3 ^ (n + 2) + 1), (w (x + unit j) - w x) ^ 2)) :
    WeakNormLeD ω (dgClusterBallD (uniqueInfiniteComponent h) y r) (centeredFluxD ω σ χ k i)
      (max ((Yf + σ * Yd) * (1 + (L : ℝ)) ^ d)
        ((Zf + σ * Zd) * (3 * d * (3 + 6 * (L : ℝ)) ^ d) *
          Real.sqrt ((L : ℝ) ^ d / (2 * (m : ℝ)) ^ d))) := by
  set Kc := uniqueInfiniteComponent h with hKc
  set V := dgClusterBallD Kc y r with hV
  set T := supBox y (2 * 3 ^ (n + 2) + 1) with hT
  have hd0 : 0 < d := by omega
  -- the cluster ball lies in the box of radius `3^{n+1}`
  have hVbox : ∀ z ∈ V, ∀ i', |z i' - y i'| ≤ ((3 ^ (n + 1) : ℕ) : ℤ) := by
    intro z hz i'
    rw [hV, mem_dgClusterBallD] at hz
    have h1 := Rigidity.Corrector.GeneralDim.abs_coord_le_norm (z - y) i'
    rw [LatticeProb.Percolation.latticeEuclideanEmbedding_sub, ← dist_eq_norm] at h1
    have h2 : ((|z i' - y i'| : ℤ) : ℝ) < ((3 ^ (n + 1) : ℕ) : ℝ) := by
      have e : ((|z i' - y i'| : ℤ) : ℝ) = |(((z - y) i' : ℤ) : ℝ)| := by
        simp [Int.cast_abs]
      rw [e]
      push_cast
      linarith [hz.2]
    have h3 : |z i' - y i'| < ((3 ^ (n + 1) : ℕ) : ℤ) := by exact_mod_cast h2
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
  have hsideV : ∀ z ∈ V, partSide ω z ≤ L := fun z hz => hside z (hboxmono h31 (hVsub z hz))
  -- the support of the coarsened function
  intro v hv
  set w := coarseTestD ω Kc.supp V v with hw
  have hL3 : 3 ^ (n + 1) + L ≤ 3 ^ (n + 2) := by
    have h2 : 3 ^ (n + 2) = 3 * 3 ^ (n + 1) := by ring
    have h3 : 3 ^ (n + 1) = 3 * 3 ^ n := by ring
    omega
  have hsupp : ∀ x, w x ≠ 0 → x ∈ supBox y (3 ^ (n + 2)) := by
    intro x hx
    have h1 := coarseTestD_eq_zero_of_far hP (K := Kc.supp) hVbox hsideV v hx
    refine hboxmono hL3 (mem_supBox.2 fun i' => ?_)
    have := h1 i'
    push_cast at this ⊢
    exact this
  have hwS : ∀ x ∉ S, w x = 0 := fun x hx => by
    by_contra hne
    exact hx (hS (hsupp x hne))
  have hwT : ∀ x ∉ T, ∀ j : Fin d, w (x + unit j) = w x := by
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
      have h3 := abs_unit_sub_leD x j i'
      have : |x i' - y i'| ≤ |(x + unit j) i' - y i'| + |(x + unit j) i' - x i'| := by
        have := abs_sub_le (x i') ((x + unit j) i') (y i')
        rw [abs_sub_comm (x i') ((x + unit j) i')] at this
        linarith
      have h4 : (0 : ℤ) ≤ 3 ^ (n + 2) := by positivity
      push_cast at h2 ⊢
      linarith
    rw [hx1, hx2]
  -- the pairing
  have hVK : ∀ x ∈ V, x ∈ Kc.supp := fun x hx => ((mem_dgClusterBallD Kc y x r).1 hx).1
  have hVS : V ⊆ S := fun x hx => hS (hboxmono (Nat.pow_le_pow_right (by norm_num) (by omega))
    (hVsub x hx))
  have hpair : ∑ x ∈ S, (if x ∈ Kc.supp then centeredFluxD ω σ χ k i x else 0) * w x =
      ∑ x ∈ V, (if x ∈ Kc.supp then centeredFluxD ω σ χ k i x else 0) * v x :=
    sum_mul_coarseTestD_eq (ω := ω) hVK hVS v _ (fun x hx => if_neg hx)
  have hV1 : ∑ x ∈ V, centeredFluxD ω σ χ k i x * v x =
      ∑ x ∈ S, (fluxValD hG hGv k ω x i - if i = k then abar else 0) * w x -
        σ / 2 * (if i = k then 1 else 0) * ∑ x ∈ S, w x * clusterDeviationD ω θ x := by
    have e1 : ∑ x ∈ V, centeredFluxD ω σ χ k i x * v x =
        ∑ x ∈ V, (if x ∈ Kc.supp then centeredFluxD ω σ χ k i x else 0) * v x :=
      Finset.sum_congr rfl fun x hx => by rw [if_pos (hVK x hx)]
    rw [e1, ← hpair, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ite_centeredFluxD_eq hG hGv hω h hχ k i habar x]
    ring
  -- the norms of the coarsened function
  set N0 := Real.sqrt (∑ x ∈ V, v x ^ 2) with hN0
  set N1 := Real.sqrt (∑ x ∈ V, openGradNormD ω V v x ^ 2) with hN1
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hw0 : Real.sqrt (∑ x ∈ S, w x ^ 2) ≤ (1 + (L : ℝ)) ^ d * N0 := by
    refine sqrt_le_mul_sqrt_of_le (by positivity) ?_
    refine (sum_sq_coarseTestD_le hP Kc.supp hsideV v S).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun x _ => sq_nonneg _)
    have hX2 : 1 + (L : ℝ) ≤ (1 + (L : ℝ)) ^ d := le_self_pow₀ (by linarith) (by omega)
    have hXL : (L : ℝ) ^ d ≤ (1 + (L : ℝ)) ^ d :=
      pow_le_pow_left₀ (Nat.cast_nonneg L) (by linarith) d
    nlinarith
  have hK : ∀ x ∈ Kc.supp, ω ∈ infiniteComponentEvent x := fun x hx =>
    (mem_uniqueInfiniteComponent_iff h x).1 hx
  have hsideT : ∀ x ∈ T, partSide ω x ≤ L ∧ ∀ j : Fin d, partSide ω (x + unit j) ≤ L := by
    intro x hx
    refine ⟨hside x (hboxmono (by omega) hx), fun j => hside _ ?_⟩
    rw [mem_supBox] at hx ⊢
    intro i'
    have h1 := hx i'
    have h2 := abs_unit_sub_leD x j i'
    have : |(x + unit j) i' - y i'| ≤ |(x + unit j) i' - x i'| + |x i' - y i'| := by
      have := abs_sub_le ((x + unit j) i') (x i') (y i')
      linarith
    push_cast at h1 ⊢
    linarith
  have hw1 : Real.sqrt (∑ j : Fin d, ∑ x ∈ T, (w (x + unit j) - w x) ^ 2) ≤
      3 * d * (3 + 6 * (L : ℝ)) ^ d * N1 := by
    refine sqrt_le_mul_sqrt_of_le (by positivity) ?_
    refine (sum_sq_grad_coarseTestD_le hd0 hP hK hv T hsideT).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun x _ => sq_nonneg _)
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
    have hP0 : 0 ≤ (3 + 6 * (L : ℝ)) ^ (2 * d) := by positivity
    have e : (3 * d * (3 + 6 * (L : ℝ)) ^ d) ^ 2 = 9 * d * d * (3 + 6 * (L : ℝ)) ^ (2 * d) := by
      ring
    rw [e]
    have : 9 * (d : ℝ) ≤ 9 * d * d := by nlinarith
    exact mul_le_mul_of_nonneg_right this hP0
  -- the size of `V`
  have hsidem : ∀ z ∈ supBox y m, partSide ω z ≤ L := fun z hz =>
    hside z (hboxmono (by
      have : 3 ^ n ≤ 3 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega) hz)
  have hcard := card_mul_le_card_dgClusterBallD hd0 hP h y hmr hsidem
  have hcard' : ((2 * m + 1 : ℕ) : ℝ) ^ d ≤ (L : ℝ) ^ d * V.card := hcard
  have hL0 : (0 : ℝ) < L := by linarith
  have hLd : (0 : ℝ) < (L : ℝ) ^ d := by positivity
  have hm0 : (0 : ℝ) < 2 * (m : ℝ) := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    linarith
  have hVpos : 0 < V.card := by
    rcases Nat.eq_zero_or_pos V.card with h0 | h0
    · rw [h0] at hcard'
      simp only [Nat.cast_zero, mul_zero] at hcard'
      have : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) ^ d := by positivity
      linarith
    · exact h0
  have hcR : (0 : ℝ) < V.card := by exact_mod_cast hVpos
  have hc1 : (1 : ℝ) ≤ V.card := by exact_mod_cast hVpos
  have hsqrtV : Real.sqrt ((2 * (m : ℝ)) ^ d / (L : ℝ) ^ d) ≤ Real.sqrt V.card := by
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_iff₀ hLd]
    have h1 : (2 * (m : ℝ)) ^ d ≤ ((2 * m + 1 : ℕ) : ℝ) ^ d :=
      pow_le_pow_left₀ hm0.le (by push_cast; linarith) d
    linarith
  -- the conclusion
  set B := max ((Yf + σ * Yd) * (1 + (L : ℝ)) ^ d)
    ((Zf + σ * Zd) * (3 * d * (3 + 6 * (L : ℝ)) ^ d) *
      Real.sqrt ((L : ℝ) ^ d / (2 * (m : ℝ)) ^ d)) with hB
  have hδ : |σ / 2 * (if i = k then (1 : ℝ) else 0)| ≤ σ := by
    split_ifs
    · rw [mul_one, abs_of_nonneg (by positivity)]
      linarith
    · rw [mul_zero, abs_zero]
      exact hσ
  have hmain : ∑ x ∈ V, centeredFluxD ω σ χ k i x * v x ≤
      (Yf + σ * Yd) * (1 + (L : ℝ)) ^ d * N0 +
        (Zf + σ * Zd) * (3 * d * (3 + 6 * (L : ℝ)) ^ d) * N1 := by
    rw [hV1]
    have hf := hflux w hwS hwT
    have hdd := hdens w
    have habs : ∑ x ∈ S, (fluxValD hG hGv k ω x i - (if i = k then abar else 0)) * w x -
        σ / 2 * (if i = k then 1 else 0) * ∑ x ∈ S, w x * clusterDeviationD ω θ x ≤
        |∑ x ∈ S, (fluxValD hG hGv k ω x i - (if i = k then abar else 0)) * w x| +
          σ * |∑ x ∈ S, w x * clusterDeviationD ω θ x| := by
      have h1 := le_abs_self (∑ x ∈ S, (fluxValD hG hGv k ω x i -
        (if i = k then abar else 0)) * w x)
      have h2 : -(σ / 2 * (if i = k then 1 else 0) * ∑ x ∈ S, w x * clusterDeviationD ω θ x) ≤
          σ * |∑ x ∈ S, w x * clusterDeviationD ω θ x| := by
        have := neg_abs_le (σ / 2 * (if i = k then (1 : ℝ) else 0) *
          ∑ x ∈ S, w x * clusterDeviationD ω θ x)
        rw [abs_mul] at this
        have h3 := mul_le_mul_of_nonneg_right hδ (abs_nonneg (∑ x ∈ S, w x *
          clusterDeviationD ω θ x))
        linarith
      linarith
    refine habs.trans ?_
    have hσd := mul_le_mul_of_nonneg_left hdd hσ
    calc |∑ x ∈ S, (fluxValD hG hGv k ω x i - (if i = k then abar else 0)) * w x| +
          σ * |∑ x ∈ S, w x * clusterDeviationD ω θ x|
        ≤ (Yf * Real.sqrt (∑ x ∈ S, w x ^ 2) +
            Zf * Real.sqrt (∑ j : Fin d, ∑ x ∈ T, (w (x + unit j) - w x) ^ 2)) +
          σ * (Yd * Real.sqrt (∑ x ∈ S, w x ^ 2) +
            Zd * Real.sqrt (∑ j : Fin d, ∑ x ∈ T, (w (x + unit j) - w x) ^ 2)) :=
          add_le_add hf hσd
      _ = (Yf + σ * Yd) * Real.sqrt (∑ x ∈ S, w x ^ 2) +
          (Zf + σ * Zd) * Real.sqrt (∑ j : Fin d, ∑ x ∈ T, (w (x + unit j) - w x) ^ 2) := by
          ring
      _ ≤ (Yf + σ * Yd) * ((1 + (L : ℝ)) ^ d * N0) +
          (Zf + σ * Zd) * (3 * d * (3 + 6 * (L : ℝ)) ^ d * N1) :=
          add_le_add (mul_le_mul_of_nonneg_left hw0 (by positivity))
            (mul_le_mul_of_nonneg_left hw1 (by positivity))
      _ = _ := by ring
  have hN0n : 0 ≤ N0 := Real.sqrt_nonneg _
  have hN1n : 0 ≤ N1 := Real.sqrt_nonneg _
  have ha : (Yf + σ * Yd) * (1 + (L : ℝ)) ^ d ≤ B := le_max_left _ _
  have hB0 : 0 ≤ B := le_trans (by positivity) ha
  have hb : (Zf + σ * Zd) * (3 * d * (3 + 6 * (L : ℝ)) ^ d) ≤ B * Real.sqrt V.card := by
    have h1 : (Zf + σ * Zd) * (3 * d * (3 + 6 * (L : ℝ)) ^ d) *
        Real.sqrt ((L : ℝ) ^ d / (2 * (m : ℝ)) ^ d) ≤ B := le_max_right _ _
    have hone : Real.sqrt ((L : ℝ) ^ d / (2 * (m : ℝ)) ^ d) *
        Real.sqrt ((2 * (m : ℝ)) ^ d / (L : ℝ) ^ d) = 1 := by
      rw [← Real.sqrt_mul (by positivity), div_mul_div_comm, mul_comm ((L : ℝ) ^ d),
        div_self (by positivity), Real.sqrt_one]
    have hA0 : 0 ≤ (Zf + σ * Zd) * (3 * d * (3 + 6 * (L : ℝ)) ^ d) := by positivity
    calc (Zf + σ * Zd) * (3 * d * (3 + 6 * (L : ℝ)) ^ d)
        = (Zf + σ * Zd) * (3 * d * (3 + 6 * (L : ℝ)) ^ d) *
            Real.sqrt ((L : ℝ) ^ d / (2 * (m : ℝ)) ^ d) *
            Real.sqrt ((2 * (m : ℝ)) ^ d / (L : ℝ) ^ d) := by rw [mul_assoc _ (Real.sqrt _), hone,
              mul_one]
      _ ≤ B * Real.sqrt V.card :=
          mul_le_mul h1 hsqrtV (Real.sqrt_nonneg _) hB0
  have hs : 0 < Real.sqrt V.card := Real.sqrt_pos.2 hcR
  have hrp := inv_sqrt_le_rpow_neg hd hc1
  rw [clusterH1NormD_eq]
  calc (V.card : ℝ)⁻¹ * ∑ x ∈ V, centeredFluxD ω σ χ k i x * v x
      ≤ (V.card : ℝ)⁻¹ * ((Yf + σ * Yd) * (1 + (L : ℝ)) ^ d * N0 +
          (Zf + σ * Zd) * (3 * d * (3 + 6 * (L : ℝ)) ^ d) * N1) :=
        mul_le_mul_of_nonneg_left hmain (inv_nonneg.2 hcR.le)
    _ ≤ (V.card : ℝ)⁻¹ * (B * N0 + B * Real.sqrt V.card * N1) := by
        refine mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right ha hN0n)
          (mul_le_mul_of_nonneg_right hb hN1n)) (inv_nonneg.2 hcR.le)
    _ = B * ((Real.sqrt V.card)⁻¹ * ((Real.sqrt V.card)⁻¹ * N0) +
          (Real.sqrt V.card)⁻¹ * N1) := by
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
    _ ≤ B * ((V.card : ℝ) ^ (-(1 / d : ℝ)) * ((Real.sqrt V.card)⁻¹ * N0) +
          (Real.sqrt V.card)⁻¹ * N1) := by
        refine mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_right hrp
            (mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) hN0n)) le_rfl) hB0

end Scale

end Rigidity.Green.GeneralFlux
