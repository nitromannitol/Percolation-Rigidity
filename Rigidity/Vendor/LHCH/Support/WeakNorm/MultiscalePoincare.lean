/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/WeakNorm/MultiscalePoincare.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Support.WeakNorm.AverageDotProduct
import Rigidity.Vendor.LHCH.Support.WeakNorm.BlockMean
import Rigidity.Vendor.LHCH.Support.WeakNorm.BlockMeanSubdivision
import Rigidity.Vendor.LHCH.Support.WeakNorm.BlockOscGrad
import Rigidity.Vendor.LHCH.Support.WeakNorm.CoarseGraining
import Rigidity.Vendor.LHCH.Support.WeakNorm.CutoffIdentity
import Rigidity.Vendor.LHCH.Support.WeakNorm.Multiscale
import Rigidity.Vendor.LHCH.Support.WeakNorm.MultiscaleDuality
import Rigidity.Vendor.LHCH.Support.WeakNorm.ReflectPeriodic
import Rigidity.Vendor.LHCH.Support.WeakNorm.Reflection
import Rigidity.Vendor.LHCH.Support.WeakNorm.TorusCalculus
import Rigidity.Vendor.LHCH.Support.WeakNorm.TorusEnergy
import Rigidity.Vendor.LHCH.Support.WeakNorm.TorusEven
import Rigidity.Vendor.LHCH.Support.WeakNorm.TorusH2
import Rigidity.Vendor.LHCH.Support.WeakNorm.TorusNeumann
import Rigidity.Vendor.LHCH.Support.WeakNorm.TorusPairing
import Rigidity.Vendor.LHCH.Support.WeakNorm.TorusParts
import Rigidity.Vendor.LHCH.Support.WeakNorm.TorusPoincare
import Rigidity.Vendor.LHCH.Support.WeakNorm.TorusVertexPairing
import Rigidity.Vendor.LHCH.Support.WeakNorm.TriadicRegroup
import Rigidity.Vendor.LHCH.Support.WeakNorm.UnitScale
import Rigidity.Vendor.LHCH.Support.WeakNorm.UnitTerm

/-!
# The lattice multiscale Poincaré inequality

The lattice form of AK25 Lemma A.2: for
`u` with vertex-weighted mean zero on `□_n`, its vertex-weighted `L²` norm is at most `C(d)(Σ_{k≤n}
3^k blockSq_k(∇u)^{1/2} + cubeAvg(|∇u|²)^{1/2})`. Reflect `u` to the torus, solve the Neumann
problem there with an even solution `w`, write `‖u‖² = cubeAvg(∇u·∇w)` through the pairing
identities, and bound it by the multiscale duality, with the block oscillations and the unit-scale
term of `∇w` controlled by its second differences (the discrete `H²` identity) and the top term by
the energy of `w`.
-/

open LatticeProb Matrix

noncomputable section

namespace LatticeHC

variable {d : ℕ}

/-- **Jensen for block means**: for `L ≥ 1`, `|(F)_□|² ≤ cubeAvg(F²)`. In each direction the face
weights of the edges of `□` sum to `L^d` (`sum_faceWeight_eq`), so the block mean in that direction
is a weighted average and the square of a weighted average is at most the average of the squares. -/
theorem dotProduct_blockMean_self_le_cubeAvg (z : Site d) {L : ℕ} (hL : 1 ≤ L)
    (F : Edge d → ℝ) :
    blockMean z L F ⬝ᵥ blockMean z L F ≤ cubeAvg z L (fun e => F e ^ 2) := by
  classical
  have hfw : ∀ e : Edge d, 0 ≤ faceWeight z L e := fun e => pow_nonneg (by norm_num) _
  have hLd : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < L := by exact_mod_cast hL
    positivity
  have hsplit : cubeAvg z L (fun e => F e ^ 2) = ∑ j : Fin d, ((L : ℝ) ^ d)⁻¹ *
      ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j), faceWeight z L e * F e ^ 2 := by
    rw [cubeAvg, ← Finset.mul_sum,
      ← Finset.sum_fiberwise (edgesOf z L) (fun e => e.2)]
  rw [hsplit]
  refine Finset.sum_le_sum fun j _ => ?_
  have hJ : (∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j), faceWeight z L e * F e) ^ 2 ≤
      (L : ℝ) ^ d *
        ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j), faceWeight z L e * F e ^ 2 := by
    rw [← sum_faceWeight_eq z hL j]
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun e _ => hfw e)
      (fun e _ => mul_nonneg (hfw e) (sq_nonneg _)) (fun e _ => le_of_eq ?_)
    ring
  simp only [blockMean]
  calc ((L : ℝ) ^ d)⁻¹ * (∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j), faceWeight z L e * F e) *
        (((L : ℝ) ^ d)⁻¹ * ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j), faceWeight z L e * F e)
      = (((L : ℝ) ^ d)⁻¹) ^ 2 *
        (∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j), faceWeight z L e * F e) ^ 2 := by ring
    _ ≤ (((L : ℝ) ^ d)⁻¹) ^ 2 * ((L : ℝ) ^ d *
        ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j), faceWeight z L e * F e ^ 2) :=
        mul_le_mul_of_nonneg_left hJ (sq_nonneg _)
    _ = ((L : ℝ) ^ d)⁻¹ *
        ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j), faceWeight z L e * F e ^ 2 := by
      field_simp

/-- The difference of the reflection of `u` along the edge `(x, i)` is the reflection of the
gradient of `u`. -/
theorem reflectFun_add_unit_sub_reflectFun (N : ℕ) (hN : 0 < N) (u : Site d → ℝ) (x : Site d)
    (i : Fin d) :
    reflectFun N u (x + unit i) - reflectFun N u x = reflectEdgeField N (edgeGrad u) (x, i) :=
  congrFun (edgeGrad_reflectFun N hN u) (x, i)

/-- The sum over the period box of the square of a reflected function is `2^d` times the
vertex-weighted sum of its square on the cube. -/
theorem sum_torusBox_reflectFun_sq (N : ℕ) (hN : 0 < N) (u : Site d → ℝ) :
    ∑ x ∈ torusBox d N, reflectFun N u x ^ 2 =
      2 ^ d * ∑ y ∈ latticeCube 0 N, vertexWeight N y * u y ^ 2 := by
  have h := sum_torusBox_reflectFun_mul N hN u u
  simp only [← sq, mul_assoc] at h
  exact h

/-- The reflection of a function with vertex-weighted mean zero has mean zero over the period
box. -/
theorem sum_torusBox_reflectFun_eq_zero (N : ℕ) (hN : 0 < N) (u : Site d → ℝ)
    (hmean : ∑ y ∈ latticeCube 0 N, vertexWeight N y * u y = 0) :
    ∑ x ∈ torusBox d N, reflectFun N u x = 0 := by
  have h := sum_torusBox_reflectFun_mul N hN u (fun _ => 1)
  simp only [mul_one, reflectFun] at h ⊢
  rw [h, hmean, mul_zero]

/-- **The even torus solution pairs `u` with itself** (steps 1 and 2 of the route to the lattice
multiscale Poincaré inequality): there is `C(d)` such that for `N ≥ 1` and every `u` with
vertex-weighted mean zero on `□ = {0, …, N}^d` there is `w` with
`Σ_{e ⊂ □} w_□(e) ∇w(e) ∇u(e) = Σ_y w_v(y) u(y)²` (the identity `‖u‖² = cubeAvg(∇w·∇u)`),
`Σ_{x ∈ □} Σ_{i,j} (∇_i∇_j w)² ≤ 2^d Σ_y w_v(y) u(y)²` and
`Σ_{e ⊂ □} w_□(e) |∇w(e)|² ≤ C N² Σ_y w_v(y) u(y)²`. The function `w` is the even periodic
solution of `∇*∇ w̃ = ũ` on the torus for the reflection `ũ` of `u`; the pairing identities
transfer sums over the torus to the cube. -/
theorem exists_pairing_eq_vertex_sq_hessian_energy_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 0 < N → ∀ u : Site d → ℝ,
      ∑ y ∈ latticeCube 0 N, vertexWeight N y * u y = 0 →
      ∃ w : Site d → ℝ,
        ∑ e ∈ edgesOf 0 N, faceWeight 0 N e * ((w e.tgt - w e.src) * (u e.tgt - u e.src)) =
          ∑ y ∈ latticeCube 0 N, vertexWeight N y * u y ^ 2 ∧
        ∑ x ∈ latticeCube 0 N, ∑ i : Fin d, ∑ j : Fin d, secondDiff w i j x ^ 2 ≤
          2 ^ d * ∑ y ∈ latticeCube 0 N, vertexWeight N y * u y ^ 2 ∧
        ∑ e ∈ edgesOf 0 N, faceWeight 0 N e * (w e.tgt - w e.src) ^ 2 ≤
          C * (N : ℝ) ^ 2 * ∑ y ∈ latticeCube 0 N, vertexWeight N y * u y ^ 2 := by
  obtain ⟨C₃, hC₃, henergy⟩ := exists_sum_grad_sq_le_of_latticeLaplacian_eq (d := d)
  refine ⟨4 * C₃, by positivity, fun N hN u hmean => ?_⟩
  have hper : IsTorusPeriodic N (reflectFun N u) := isTorusPeriodic_reflectFun N u
  have heven : ∀ x (k : Fin d), reflectFun N u (reflectSite k x) = reflectFun N u x :=
    fun x k => reflectFun_reflectSite N hN u k x
  have hsum := sum_torusBox_reflectFun_eq_zero N hN u hmean
  obtain ⟨w, hwper, hwev, hlap⟩ :=
    exists_even_isTorusPeriodic_latticeLaplacian_eq N hN (reflectFun N u) hper heven hsum
  have hgw : edgeGrad w = reflectEdgeField N (edgeGrad w) := by
    have h := edgeGrad_reflectFun N hN w
    rwa [← funext (eq_reflectFun_of_even N hN w hwper hwev)] at h
  have hvert := sum_torusBox_reflectFun_sq N hN u
  have h2d : (0 : ℝ) < 2 ^ d := by positivity
  refine ⟨w, ?_, ?_, ?_⟩
  · have hparts := sum_mul_latticeLaplacian_eq N hN (reflectFun N u) w hper hwper
    have hpair := sum_torusBox_reflectEdgeField_mul N hN (edgeGrad u) (edgeGrad w)
    have hL : ∑ x ∈ torusBox d N, reflectFun N u x * latticeLaplacian w x =
        ∑ x ∈ torusBox d N, reflectFun N u x ^ 2 :=
      Finset.sum_congr rfl fun x _ => by rw [hlap x, sq]
    have hR : ∑ x ∈ torusBox d N, ∑ i : Fin d,
        (reflectFun N u (x + unit i) - reflectFun N u x) * (w (x + unit i) - w x) =
        ∑ x ∈ torusBox d N, ∑ j : Fin d, reflectEdgeField N (edgeGrad u) (x, j) *
          reflectEdgeField N (edgeGrad w) (x, j) := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
      rw [reflectFun_add_unit_sub_reflectFun N hN u x i, ← hgw]
      rfl
    rw [hL, hR, hpair, hvert] at hparts
    have := mul_left_cancel₀ h2d.ne' hparts.symm
    rw [← this]
    refine Finset.sum_congr rfl fun e _ => ?_
    unfold edgeGrad
    ring
  · have hH := sum_latticeLaplacian_sq_eq N hN w hwper
    have hsub : latticeCube 0 N ⊆ torusBox d N := by
      intro x hx
      rw [mem_latticeCube_iff_coord] at hx
      simp only [torusBox, Fintype.mem_piFinset, Finset.mem_Ico]
      intro i
      have h := hx i
      simp only [Pi.zero_apply, zero_add] at h
      have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
      omega
    calc _ ≤ ∑ x ∈ torusBox d N, ∑ i : Fin d, ∑ j : Fin d, secondDiff w i j x ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ =>
            Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
      _ = ∑ x ∈ torusBox d N, latticeLaplacian w x ^ 2 := hH.symm
      _ = ∑ x ∈ torusBox d N, reflectFun N u x ^ 2 :=
          Finset.sum_congr rfl fun x _ => by rw [hlap x]
      _ = _ := hvert
  · have hen := henergy N hN (reflectFun N u) w hper hwper hsum hlap
    have hpair := sum_torusBox_reflectEdgeField_mul N hN (edgeGrad w) (edgeGrad w)
    have hL : ∑ x ∈ torusBox d N, ∑ i : Fin d, (w (x + unit i) - w x) ^ 2 =
        ∑ x ∈ torusBox d N, ∑ j : Fin d, reflectEdgeField N (edgeGrad w) (x, j) *
          reflectEdgeField N (edgeGrad w) (x, j) := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
      rw [← hgw, sq]
      rfl
    rw [hL, hpair, hvert] at hen
    refine le_of_mul_le_mul_left ?_ h2d
    calc 2 ^ d * ∑ e ∈ edgesOf 0 N, faceWeight 0 N e * (w e.tgt - w e.src) ^ 2
        = 2 ^ d * ∑ e ∈ edgesOf 0 N, faceWeight 0 N e * edgeGrad w e * edgeGrad w e := by
          congr 1
          refine Finset.sum_congr rfl fun e _ => ?_
          unfold edgeGrad
          ring
      _ ≤ C₃ * (2 * (N : ℝ)) ^ 2 * (2 ^ d * ∑ y ∈ latticeCube 0 N, vertexWeight N y * u y ^ 2) :=
          hen
      _ = 2 ^ d * (4 * C₃ * (N : ℝ) ^ 2 * ∑ y ∈ latticeCube 0 N, vertexWeight N y * u y ^ 2) := by
          ring

/-- **Cauchy–Schwarz for dot products**: `|x · y| ≤ (x · x)^{1/2} (y · y)^{1/2}`. -/
theorem abs_dotProduct_le_sqrt_mul_sqrt {n : ℕ} (x y : Fin n → ℝ) :
    |x ⬝ᵥ y| ≤ Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by
  have hxx : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  rw [← Real.sqrt_mul hxx]
  refine Real.abs_le_sqrt ?_
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  simpa only [dotProduct, sq] using h

/-- **The unit-scale term is controlled by the Hessian average**: if the average of the squared
second differences of `w` over `□_n` is at most `2^d a`, the unit-scale term of the duality of `∇w`
against `G` is at most `C a^{1/2} (cubeAvg G²)^{1/2}`, with `C = C(d)`. -/
theorem exists_abs_unit_term_le_sqrt_mul :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (w : Site d → ℝ) (G : Edge d → ℝ) (a : ℝ), 0 ≤ a →
      (((3 : ℝ) ^ n) ^ d)⁻¹ *
          ∑ x ∈ latticeCube 0 (3 ^ n), ∑ i : Fin d, ∑ j : Fin d, secondDiff w i j x ^ 2 ≤
        2 ^ d * a →
      |((triadicIndex d n).card : ℝ)⁻¹ * ∑ y ∈ triadicIndex d n,
          (cubeAvg (triadicCorner 0 0 y) 1 (fun e => (w e.tgt - w e.src) * G e) -
            blockMean (triadicCorner 0 0 y) 1 (fun e => w e.tgt - w e.src) ⬝ᵥ
              blockMean (triadicCorner 0 0 y) 1 G)| ≤
        C * Real.sqrt a * Real.sqrt (cubeAvg 0 (3 ^ n) (fun e => G e ^ 2)) := by
  obtain ⟨C₂, hC₂, hunit⟩ := exists_abs_unit_term_le (d := d)
  refine ⟨C₂ * Real.sqrt (2 ^ d), by positivity, fun n w G a ha hH => ?_⟩
  refine (hunit n w G).trans ?_
  have h1 : Real.sqrt ((((3 : ℝ) ^ n) ^ d)⁻¹ * ∑ x ∈ latticeCube 0 (3 ^ n), ∑ i : Fin d,
      ∑ j : Fin d, secondDiff w i j x ^ 2) ≤ Real.sqrt (2 ^ d) * Real.sqrt a := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hH
  calc _ ≤ C₂ * (Real.sqrt (2 ^ d) * Real.sqrt a) *
        Real.sqrt (cubeAvg 0 (3 ^ n) (fun e => G e ^ 2)) := by gcongr
    _ = _ := by ring

/-- **The block oscillations are controlled by the Hessian average**: if the average of the squared
second differences of `w` over `□_n` is at most `2^d a`, then
`blockOsc_k(∇w)^{1/2} ≤ C 3^k a^{1/2}`, with `C = C(d)`. -/
theorem exists_sqrt_blockOsc_grad_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n k : ℕ), k < n → ∀ (w : Site d → ℝ) (a : ℝ), 0 ≤ a →
      (((3 : ℝ) ^ n) ^ d)⁻¹ *
          ∑ x ∈ latticeCube 0 (3 ^ n), ∑ i : Fin d, ∑ j : Fin d, secondDiff w i j x ^ 2 ≤
        2 ^ d * a →
      Real.sqrt (blockOsc 0 n k (fun e => w e.tgt - w e.src)) ≤ C * Real.sqrt a * 3 ^ k := by
  obtain ⟨C₁, hC₁, hosc⟩ := exists_blockOsc_grad_le (d := d)
  refine ⟨Real.sqrt (C₁ * 2 ^ d), by positivity, fun n k hkn w a ha hH => ?_⟩
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  calc _ ≤ C₁ * (3 : ℝ) ^ (2 * k) * ((((3 : ℝ) ^ n) ^ d)⁻¹ * ∑ x ∈ latticeCube 0 (3 ^ n),
        ∑ i : Fin d, ∑ j : Fin d, secondDiff w i j x ^ 2) := hosc n k hkn w
    _ ≤ C₁ * (3 : ℝ) ^ (2 * k) * (2 ^ d * a) := mul_le_mul_of_nonneg_left hH (by positivity)
    _ = (Real.sqrt (C₁ * 2 ^ d) * Real.sqrt a * 3 ^ k) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt ha]
        ring

/-- **The top-scale term**: if `cubeAvg(F²) ≤ C (3^n)² a`, then
`|(F)_□ · (G)_□| ≤ C^{1/2} a^{1/2} 3^n blockSq_n(G)^{1/2}` on `□_n` (Cauchy–Schwarz, Jensen for
the block mean of `F`, and `(G)_□ · (G)_□ = blockSq_n(G)`). -/
theorem abs_blockMean_dotProduct_le (n : ℕ) (F G : Edge d → ℝ) {C a : ℝ} (hC : 0 ≤ C)
    (ha : 0 ≤ a) (h : cubeAvg 0 (3 ^ n) (fun e => F e ^ 2) ≤ C * ((3 : ℝ) ^ n) ^ 2 * a) :
    |blockMean 0 (3 ^ n) F ⬝ᵥ blockMean 0 (3 ^ n) G| ≤
      Real.sqrt C * Real.sqrt a * ((3 : ℝ) ^ n * Real.sqrt (blockSq 0 n n G)) := by
  have hbu : blockMean 0 (3 ^ n) G ⬝ᵥ blockMean 0 (3 ^ n) G = blockSq 0 n n G :=
    (blockPair_self 0 n G G).symm
  have h1 : Real.sqrt (blockMean 0 (3 ^ n) F ⬝ᵥ blockMean 0 (3 ^ n) F) ≤
      Real.sqrt C * Real.sqrt a * 3 ^ n := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    calc _ ≤ C * ((3 : ℝ) ^ n) ^ 2 * a :=
          (dotProduct_blockMean_self_le_cubeAvg 0 (Nat.one_le_pow _ _ (by norm_num)) F).trans h
      _ = _ := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hC, Real.sq_sqrt ha]
        ring
  refine (abs_dotProduct_le_sqrt_mul_sqrt _ _).trans ?_
  rw [hbu]
  calc _ ≤ (Real.sqrt C * Real.sqrt a * 3 ^ n) * Real.sqrt (blockSq 0 n n G) := by gcongr
    _ = _ := by ring

/-- The final division: if `a ≤ a^{1/2} X` and `X ≤ C A` with `C ≥ 0`, then `a^{1/2} ≤ C A`. -/
theorem sqrt_le_of_le_sqrt_mul {a X Y : ℝ} (ha : 0 ≤ a) (hY : 0 ≤ Y)
    (h : a ≤ Real.sqrt a * X) (hX : X ≤ Y) : Real.sqrt a ≤ Y := by
  by_cases hs : 0 < Real.sqrt a
  · refine le_of_mul_le_mul_left ?_ hs
    calc Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha
      _ ≤ Real.sqrt a * X := h
      _ ≤ Real.sqrt a * Y := mul_le_mul_of_nonneg_left hX (Real.sqrt_nonneg _)
  · rw [le_antisymm (not_lt.1 hs) (Real.sqrt_nonneg _)]
    exact hY

/-- **The lattice multiscale Poincaré inequality** (the lattice form of AK25
Lemma A.2): there is `C(d)` such that for every `n` and every `u` with vertex-weighted mean zero on
`□_n = {0, …, 3^n}^d`, the vertex-weighted `L²` norm of `u` is at most
`C (Σ_{k≤n} 3^k blockSq_k(∇u)^{1/2} + (cubeAvg |∇u|²)^{1/2})`. Route: reflect `u` to the torus,
solve the Neumann problem there with an even solution `w`, write `‖u‖² = cubeAvg(∇u·∇w)` by the
pairing identities, and bound it by the multiscale duality, the block oscillations of `∇w` by its
second differences, the discrete `H²` identity and the energy bound for `w`. -/
theorem exists_vertexNorm_le_multiscale :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (u : Site d → ℝ),
      ∑ y ∈ latticeCube 0 (3 ^ n), vertexWeight (3 ^ n) y * u y = 0 →
      Real.sqrt ((((3 : ℝ) ^ n) ^ d)⁻¹ *
          ∑ y ∈ latticeCube 0 (3 ^ n), vertexWeight (3 ^ n) y * u y ^ 2) ≤
        C * (∑ k ∈ Finset.range (n + 1),
            (3 : ℝ) ^ k * Real.sqrt (blockSq 0 n k (fun e => u e.tgt - u e.src)) +
          Real.sqrt (cubeAvg 0 (3 ^ n) (fun e => (u e.tgt - u e.src) ^ 2))) := by
  obtain ⟨C₁, hC₁, hunit⟩ := exists_abs_unit_term_le_sqrt_mul (d := d)
  obtain ⟨C₂, hC₂, hosc⟩ := exists_sqrt_blockOsc_grad_le (d := d)
  obtain ⟨C₃, hC₃, hsol⟩ := exists_pairing_eq_vertex_sq_hessian_energy_le (d := d)
  refine ⟨C₁ + C₂ + Real.sqrt C₃, by positivity, fun n u hmean => ?_⟩
  have hN : 0 < 3 ^ n := by positivity
  have hNr : (((3 ^ n : ℕ) : ℝ)) = (3 : ℝ) ^ n := by push_cast; rfl
  obtain ⟨w, hpair, hhess, henergy⟩ := hsol (3 ^ n) hN u hmean
  rw [hNr] at henergy
  have hvw : ∀ y : Site d, 0 ≤ vertexWeight (3 ^ n) y := fun y => pow_nonneg (by norm_num) _
  have hS0 : 0 ≤ ∑ y ∈ latticeCube 0 (3 ^ n), vertexWeight (3 ^ n) y * u y ^ 2 :=
    Finset.sum_nonneg fun y _ => mul_nonneg (hvw y) (sq_nonneg _)
  have hK0 : 0 < (((3 : ℝ) ^ n) ^ d)⁻¹ := by positivity
  set S := ∑ y ∈ latticeCube 0 (3 ^ n), vertexWeight (3 ^ n) y * u y ^ 2 with hS
  set K : ℝ := (((3 : ℝ) ^ n) ^ d)⁻¹ with hK
  set a : ℝ := K * S with ha
  have ha0 : 0 ≤ a := mul_nonneg hK0.le hS0
  set F : Edge d → ℝ := fun e => w e.tgt - w e.src with hF
  set G : Edge d → ℝ := fun e => u e.tgt - u e.src with hG
  -- the identity `‖u‖² = cubeAvg (∇w · ∇u)`
  have hmain : cubeAvg 0 (3 ^ n) (fun e => F e * G e) = a := by
    simp only [cubeAvg, hNr]
    rw [hpair]
  -- the second differences of `w`
  have hH : K * ∑ x ∈ latticeCube 0 (3 ^ n), ∑ i : Fin d, ∑ j : Fin d,
      secondDiff w i j x ^ 2 ≤ 2 ^ d * a := by
    calc _ ≤ K * (2 ^ d * S) := mul_le_mul_of_nonneg_left hhess hK0.le
      _ = 2 ^ d * a := by rw [ha]; ring
  -- the energy of `w`
  have hbw : cubeAvg 0 (3 ^ n) (fun e => F e ^ 2) ≤ C₃ * ((3 : ℝ) ^ n) ^ 2 * a := by
    simp only [cubeAvg, hNr]
    calc K * ∑ e ∈ edgesOf 0 (3 ^ n), faceWeight 0 (3 ^ n) e * F e ^ 2
        ≤ K * (C₃ * ((3 : ℝ) ^ n) ^ 2 * S) := mul_le_mul_of_nonneg_left henergy hK0.le
      _ = C₃ * ((3 : ℝ) ^ n) ^ 2 * a := by rw [ha]; ring
  have hdual := abs_cubeAvg_mul_sub_le (0 : Site d) n F G
  have hu := hunit n w G a ha0 hH
  have htop := abs_blockMean_dotProduct_le n F G hC₃ ha0 hbw
  have hos : ∑ k ∈ Finset.range n, Real.sqrt (blockOsc 0 n k F) * Real.sqrt (blockSq 0 n k G) ≤
      C₂ * Real.sqrt a * ∑ k ∈ Finset.range n, (3 : ℝ) ^ k * Real.sqrt (blockSq 0 n k G) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    calc _ ≤ (C₂ * Real.sqrt a * 3 ^ k) * Real.sqrt (blockSq 0 n k G) :=
          mul_le_mul_of_nonneg_right (hosc n k (Finset.mem_range.1 hk) w a ha0 hH)
            (Real.sqrt_nonneg _)
      _ = _ := by ring
  have h1 := le_abs_self ((cubeAvg 0 (3 ^ n) fun e => F e * G e) -
    blockMean 0 (3 ^ n) F ⬝ᵥ blockMean 0 (3 ^ n) G)
  have h2 := le_abs_self (blockMean 0 (3 ^ n) F ⬝ᵥ blockMean 0 (3 ^ n) G)
  rw [hmain] at h1 hdual
  rw [Finset.sum_range_succ]
  refine sqrt_le_of_le_sqrt_mul ha0 (by positivity) (X := Real.sqrt C₃ *
    ((3 : ℝ) ^ n * Real.sqrt (blockSq 0 n n G)) + C₁ * Real.sqrt (cubeAvg 0 (3 ^ n)
      (fun e => G e ^ 2)) + C₂ * ∑ k ∈ Finset.range n,
        (3 : ℝ) ^ k * Real.sqrt (blockSq 0 n k G)) ?_ ?_
  · nlinarith
  · have hB1 : 0 ≤ ∑ k ∈ Finset.range n, (3 : ℝ) ^ k * Real.sqrt (blockSq 0 n k G) :=
      Finset.sum_nonneg fun k _ => by positivity
    have hT : 0 ≤ (3 : ℝ) ^ n * Real.sqrt (blockSq 0 n n G) := by positivity
    have hQ0 : 0 ≤ Real.sqrt (cubeAvg 0 (3 ^ n) (fun e => G e ^ 2)) := Real.sqrt_nonneg _
    have h3 := Real.sqrt_nonneg C₃
    nlinarith [mul_nonneg hC₁ hB1, mul_nonneg hC₁ hT, mul_nonneg hC₂ hT, mul_nonneg hC₂ hQ0,
      mul_nonneg h3 hB1, mul_nonneg h3 hQ0]

end LatticeHC

end
