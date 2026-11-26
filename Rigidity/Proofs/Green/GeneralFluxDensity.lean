import Rigidity.Proofs.Green.GeneralFluxDyadic
import Rigidity.Proofs.Green.GeneralFluxTriadic
import Rigidity.Proofs.Green.DarioGuDensityWeakNorm

/-!
# The weak norm of the density of the infinite cluster on unions of triadic cubes of `ℤ^d`

The extension of `DarioGuDensityWeakNorm.lean` from `ℤ²` to `ℤ^d`, Step 2 of the proof of
Proposition B.1 of Dario–Gu (Appendix B): the `H̲^{-1}` norm of `1_{𝒞_∞} - θ(p)` on a union `S` of
triadic cubes of scale `K`, through the multiscale Poincaré inequality on the triadic cubes of
`ℤ^d` (`Rigidity.Proofs.Multiscale.multiscalePoincare_holds`) and the concentration of the density
in triadic cubes (Proposition A.1, `Rigidity.Proofs.S2.cluster_density_concentration`,
`O_s(C 3^{-dk/2})` on the cubes of scale `k`). In the lattice form used here
(`exists_densityWeakNormD`): for every `w` and `T ⊇ S`,

`|Σ_S w (1_{𝒞_∞} - θ)| ≤ Y ‖w‖_{ℓ²(S)} + Z ‖∇w‖_{ℓ²(T)}`

with `E[Y^q] ≤ (A √|S| 3^{-dK/2} q^κ)^q` and `E[Z^q] ≤ (A (K + 1) √|S| q^κ)^q` (the scale `k`
contributes `3^{k+1} 3^{-dk/2} ≤ 3`).
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Corrector Rigidity.External
  Rigidity.Proofs.S2
open scoped ENNReal Classical

namespace Rigidity.Green.GeneralFlux

variable {d : ℕ} {p : unitInterval}

/-! ### Triadic cubes -/

theorem multiscale_cube_eqD (k : ℕ) (j : Vertex d) :
    Rigidity.Proofs.Multiscale.cube k j = triadicCubeFinset d k j := by
  ext x
  rw [Rigidity.Proofs.Multiscale.mem_cube_iff]
  simp only [triadicCubeFinset, Fintype.mem_piFinset, Finset.mem_Icc]
  refine forall_congr' fun i => ?_
  have hQ := three_pow_eq_two_mul_half_add_one k
  rw [abs_lt]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> omega
  · rintro ⟨h1, h2⟩
    constructor <;> omega

/-- **The Poincaré inequality on a triadic cube** of scale `k`. -/
theorem exists_sum_sq_sub_cubeMean_leD :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ (k : ℕ) (j : Vertex d) (u : Vertex d → ℝ),
      ∑ x ∈ triadicCubeFinset d k j, (u x - cubeMean u k j) ^ 2 ≤
        CP * 9 ^ k * ∑ x ∈ triadicCubeFinset d k j, ∑ i : Fin d, (u (x + unit i) - u x) ^ 2 := by
  obtain ⟨C, hC0, hMP⟩ := Rigidity.Proofs.Multiscale.multiscalePoincare_holds d
  refine ⟨C ^ 2, sq_nonneg C, fun k j u => ?_⟩
  have h := hMP k k (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) le_rfl j u
  simp only [Finset.Ico_self, Finset.sum_empty, mul_zero, add_zero, multiscale_cube_eqD] at h
  have hcard : ((triadicCubeFinset d k j).card : ℝ) = (3 ^ d) ^ k := card_triadicCubeFinsetD k j
  rw [hcard] at h
  have hmean : Rigidity.Proofs.Multiscale.finsetMean (triadicCubeFinset d k j) u =
      cubeMean u k j := by
    rw [Rigidity.Proofs.Multiscale.finsetMean, hcard, cubeMean]
    ring
  rw [hmean] at h
  have h9 : (0 : ℝ) < (3 ^ d) ^ k := by positivity
  set E := ∑ x ∈ triadicCubeFinset d k j,
    Rigidity.Proofs.Multiscale.gradNormSq (triadicCubeFinset d k j) u x with hE
  have hgrad : E ≤ ∑ x ∈ triadicCubeFinset d k j, ∑ i : Fin d, (u (x + unit i) - u x) ^ 2 := by
    rw [hE, Rigidity.Proofs.Multiscale.sum_gradNormSq]
    unfold Rigidity.Proofs.Multiscale.edgeEnergy
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun i _ => ?_
    split_ifs
    · exact le_rfl
    · exact sq_nonneg _
  have hg0 : 0 ≤ E := by
    rw [hE, Rigidity.Proofs.Multiscale.sum_gradNormSq]
    unfold Rigidity.Proofs.Multiscale.edgeEnergy
    exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun i _ => by
      split_ifs
      · exact sq_nonneg _
      · exact le_rfl
  set V := ∑ x ∈ triadicCubeFinset d k j, (u x - cubeMean u k j) ^ 2 with hV
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun x _ => sq_nonneg _
  have ha : 0 ≤ ((3 ^ d) ^ k : ℝ)⁻¹ * V := by positivity
  have hb : 0 ≤ ((3 ^ d) ^ k : ℝ)⁻¹ * E := by positivity
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [Real.sq_sqrt ha, mul_pow, Real.sq_sqrt hb, mul_pow] at h2
  have e3 : ((3 : ℝ) ^ k) ^ 2 = 9 ^ k := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [e3] at h2
  have h3 : V ≤ C ^ 2 * 9 ^ k * E := by
    have := mul_le_mul_of_nonneg_left h2 h9.le
    calc V = (3 ^ d) ^ k * (((3 ^ d) ^ k)⁻¹ * V) := by
          rw [← mul_assoc, mul_inv_cancel₀ h9.ne', one_mul]
      _ ≤ (3 ^ d) ^ k * (C ^ 2 * 9 ^ k * (((3 ^ d) ^ k)⁻¹ * E)) := this
      _ = C ^ 2 * 9 ^ k * E * ((3 ^ d) ^ k * ((3 ^ d) ^ k)⁻¹) := by ring
      _ = C ^ 2 * 9 ^ k * E := by rw [mul_inv_cancel₀ h9.ne', mul_one]
  exact h3.trans (mul_le_mul_of_nonneg_left hgrad (by positivity))

/-- Regrouping a sum over a union of cubes cube by cube. -/
theorem sum_eq_sum_cubes {β : Type*} [AddCommMonoid β] {k : ℕ} {S : Finset (Vertex d)}
    (hS : IsCubeUnion k S) (g : Vertex d → β) :
    ∑ x ∈ S, g x = ∑ j ∈ S.image (cubeIndex k), ∑ x ∈ triadicCubeFinset d k j, g x := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem (cubeIndex k) hx)]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [filter_cubeIndex_eq hS hj]

theorem cubeIndex_eq_of_mem {k : ℕ} {j x : Vertex d} (hx : x ∈ triadicCubeFinset d k j) :
    cubeIndex k x = j := (mem_triadicCubeFinset_iff k x j).1 hx

/-- The averages on the cubes do not increase the `ℓ²` norm. -/
theorem sum_sq_cubeMean_le {k : ℕ} {S : Finset (Vertex d)} (hS : IsCubeUnion k S)
    (f : Vertex d → ℝ) :
    ∑ x ∈ S, cubeMean f k (cubeIndex k x) ^ 2 ≤ ∑ x ∈ S, f x ^ 2 := by
  rw [sum_eq_sum_cubes hS, sum_eq_sum_cubes hS (fun x => f x ^ 2)]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Finset.sum_congr rfl fun x hx => by rw [cubeIndex_eq_of_mem hx], Finset.sum_const,
    nsmul_eq_mul, card_triadicCubeFinsetD]
  have hcs := sq_sum_le_card_mul_sum_sq (s := triadicCubeFinset d k j) (f := f)
  rw [card_triadicCubeFinsetD] at hcs
  have h9 : (0 : ℝ) < (3 ^ d) ^ k := by positivity
  unfold cubeMean
  rw [div_pow, ← mul_div_assoc, show ((3 : ℝ) ^ d) ^ k * (∑ x ∈ triadicCubeFinset d k j, f x) ^ 2 /
      ((3 ^ d) ^ k) ^ 2 = (∑ x ∈ triadicCubeFinset d k j, f x) ^ 2 / (3 ^ d) ^ k by
    field_simp, div_le_iff₀ h9]
  linarith

/-- The average of a function minus a function constant on the larger cubes. -/
theorem cubeMean_sub_succ (w : Vertex d → ℝ) (k : ℕ) (j : Vertex d) :
    cubeMean (fun x => w x - cubeMean w (k + 1) (cubeIndex (k + 1) x)) k j =
      cubeMean w k j - cubeMean w (k + 1) (cubeIndex 1 j) := by
  have h9 : (0 : ℝ) < (3 ^ d) ^ k := by positivity
  have hc : ∀ x ∈ triadicCubeFinset d k j,
      cubeMean w (k + 1) (cubeIndex (k + 1) x) = cubeMean w (k + 1) (cubeIndex 1 j) :=
    fun x hx => by rw [cubeIndex_succ, cubeIndex_eq_of_mem hx]
  have hconst : ∑ x ∈ triadicCubeFinset d k j, cubeMean w (k + 1) (cubeIndex (k + 1) x) =
      (3 ^ d) ^ k * cubeMean w (k + 1) (cubeIndex 1 j) := by
    rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, card_triadicCubeFinsetD]
  calc cubeMean (fun x => w x - cubeMean w (k + 1) (cubeIndex (k + 1) x)) k j
      = (∑ x ∈ triadicCubeFinset d k j, w x -
          ∑ x ∈ triadicCubeFinset d k j, cubeMean w (k + 1) (cubeIndex (k + 1) x)) / (3 ^ d) ^ k := by
        rw [cubeMean, Finset.sum_sub_distrib]
    _ = (∑ x ∈ triadicCubeFinset d k j, w x - (3 ^ d) ^ k * cubeMean w (k + 1) (cubeIndex 1 j)) /
          (3 ^ d) ^ k := by rw [hconst]
    _ = cubeMean w k j - cubeMean w (k + 1) (cubeIndex 1 j) := by
        rw [sub_div, mul_div_cancel_left₀ _ h9.ne']
        rfl

/-! ### The deterministic bound -/

theorem sqSum_le_of_sum_le {S : Finset (Vertex d)} {F G : Vertex d → ℝ}
    (h : ∑ x ∈ S, F x ^ 2 ≤ ∑ x ∈ S, G x ^ 2) : sqSum S F ≤ sqSum S G := by
  unfold sqSum
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => sq_nonneg _),
    ← ENNReal.ofReal_sum_of_nonneg (fun x _ => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal h

theorem sqSum_abs (S : Finset (Vertex d)) (F : Vertex d → ℝ) :
    sqSum S (fun x => |F x|) = sqSum S F := by
  unfold sqSum
  simp only [sq_abs]

/-- **The multiscale bound of the pairing with a test function** on a union of cubes. -/
theorem ofReal_abs_sum_mul_le_density {CP : ℝ} (hCP0 : 0 ≤ CP)
    (hCP : ∀ (k : ℕ) (j : Vertex d) (u : Vertex d → ℝ),
      ∑ x ∈ triadicCubeFinset d k j, (u x - cubeMean u k j) ^ 2 ≤
        CP * 9 ^ k * ∑ x ∈ triadicCubeFinset d k j, ∑ i : Fin d, (u (x + unit i) - u x) ^ 2)
    {K : ℕ} {S T : Finset (Vertex d)} (hS : IsCubeUnion K S) (hST : S ⊆ T)
    (w h : Vertex d → ℝ) :
    ENNReal.ofReal |∑ x ∈ S, w x * h x| ≤
      sqSum S (fun x => cubeMean h K (cubeIndex K x)) ^ (1 / 2 : ℝ) * sqSum S w ^ (1 / 2 : ℝ) +
        (∑ k ∈ Finset.range K, sqSum S (fun x => cubeMean h k (cubeIndex k x)) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (Real.sqrt CP * 3 ^ (k + 1))) * gradSqSum T w ^ (1 / 2 : ℝ) := by
  have hm := abs_sum_mul_le_multiscale hS w h
  set A := ∑ x ∈ S, |cubeMean w K (cubeIndex K x)| * |cubeMean h K (cubeIndex K x)| with hA
  set B : ℕ → ℝ := fun k => ∑ x ∈ S,
    |cubeMean w k (cubeIndex k x) - cubeMean w (k + 1) (cubeIndex (k + 1) x)| *
      |cubeMean h k (cubeIndex k x)| with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun x _ => by positivity
  have hB0 : ∀ k, 0 ≤ B k := fun k => Finset.sum_nonneg fun x _ => by positivity
  -- the top term
  have htop : ENNReal.ofReal A ≤
      sqSum S (fun x => cubeMean h K (cubeIndex K x)) ^ (1 / 2 : ℝ) * sqSum S w ^ (1 / 2 : ℝ) := by
    have h1 := ofReal_abs_sum_mul_le_sqSum S (fun x => |cubeMean h K (cubeIndex K x)|)
      (fun x => |cubeMean w K (cubeIndex K x)|)
    rw [sqSum_abs, sqSum_abs] at h1
    have e : abs (∑ x ∈ S, |cubeMean h K (cubeIndex K x)| * |cubeMean w K (cubeIndex K x)|) =
        A := by
      rw [abs_of_nonneg (Finset.sum_nonneg fun x _ => by positivity), hA]
      exact Finset.sum_congr rfl fun x _ => mul_comm _ _
    rw [e] at h1
    refine h1.trans (mul_le_mul_right (ENNReal.rpow_le_rpow
      (sqSum_le_of_sum_le (sum_sq_cubeMean_le hS w)) (by norm_num)) _)
  -- the steps
  have hgradS : ∑ x ∈ S, ∑ i : Fin d, ENNReal.ofReal ((w (x + unit i) - w x) ^ 2) ≤
      gradSqSum T w := by
    unfold gradSqSum
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset hST
  have hstep : ∀ k ∈ Finset.range K, ENNReal.ofReal (B k) ≤
      sqSum S (fun x => cubeMean h k (cubeIndex k x)) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal (Real.sqrt CP * 3 ^ (k + 1)) * gradSqSum T w ^ (1 / 2 : ℝ) := by
    intro k hk
    have hkK : k + 1 ≤ K := Finset.mem_range.1 hk
    have hS1 : IsCubeUnion (k + 1) S := hS.mono hkK
    have hSk : IsCubeUnion k S := hS.mono (by omega)
    set D : Vertex d → ℝ := fun x =>
      cubeMean w k (cubeIndex k x) - cubeMean w (k + 1) (cubeIndex (k + 1) x) with hD
    have h1 := ofReal_abs_sum_mul_le_sqSum S (fun x => |cubeMean h k (cubeIndex k x)|)
      (fun x => |D x|)
    rw [sqSum_abs, sqSum_abs] at h1
    have e : abs (∑ x ∈ S, |cubeMean h k (cubeIndex k x)| * |D x|) = B k := by
      rw [abs_of_nonneg (Finset.sum_nonneg fun x _ => by positivity), hB]
      exact Finset.sum_congr rfl fun x _ => mul_comm _ _
    rw [e] at h1
    -- the oscillation between the scales `k` and `k + 1`
    have hD1 : ∑ x ∈ S, D x ^ 2 ≤
        ∑ x ∈ S, (w x - cubeMean w (k + 1) (cubeIndex (k + 1) x)) ^ 2 := by
      have hc := sum_sq_cubeMean_le hSk (fun x => w x - cubeMean w (k + 1) (cubeIndex (k + 1) x))
      refine le_of_eq_of_le (Finset.sum_congr rfl fun x _ => ?_) hc
      rw [cubeMean_sub_succ]
      simp only [hD, cubeIndex_succ k x]
    have hD2 : ∑ x ∈ S, (w x - cubeMean w (k + 1) (cubeIndex (k + 1) x)) ^ 2 ≤
        CP * 9 ^ (k + 1) * ∑ x ∈ S, ∑ i : Fin d, (w (x + unit i) - w x) ^ 2 := by
      rw [sum_eq_sum_cubes hS1, sum_eq_sum_cubes hS1 (fun x => ∑ i : Fin d,
        (w (x + unit i) - w x) ^ 2), Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [Finset.sum_congr rfl fun x hx => by rw [cubeIndex_eq_of_mem hx]]
      exact hCP (k + 1) j w
    have hD3 : sqSum S D ≤ ENNReal.ofReal (CP * 9 ^ (k + 1)) * gradSqSum T w := by
      unfold sqSum
      rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => sq_nonneg _)]
      refine (ENNReal.ofReal_le_ofReal (hD1.trans hD2)).trans ?_
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg
        (fun x _ => Finset.sum_nonneg fun i _ => sq_nonneg _)]
      refine mul_le_mul_right ((Finset.sum_le_sum fun x _ => ?_).trans hgradS) _
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
    have hsqrt : (ENNReal.ofReal (CP * 9 ^ (k + 1)) * gradSqSum T w) ^ (1 / 2 : ℝ) =
        ENNReal.ofReal (Real.sqrt CP * 3 ^ (k + 1)) * gradSqSum T w ^ (1 / 2 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ofReal_rpow_half _ (by positivity),
        Real.sqrt_mul hCP0, show (9 : ℝ) ^ (k + 1) = (3 ^ (k + 1)) ^ 2 by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num, Real.sqrt_sq (by positivity)]
    calc ENNReal.ofReal (B k)
        ≤ sqSum S (fun x => cubeMean h k (cubeIndex k x)) ^ (1 / 2 : ℝ) * sqSum S D ^ (1 / 2 : ℝ) :=
          h1
      _ ≤ sqSum S (fun x => cubeMean h k (cubeIndex k x)) ^ (1 / 2 : ℝ) *
            (ENNReal.ofReal (CP * 9 ^ (k + 1)) * gradSqSum T w) ^ (1 / 2 : ℝ) :=
          mul_le_mul_right (ENNReal.rpow_le_rpow hD3 (by norm_num)) _
      _ = _ := by rw [hsqrt, mul_assoc]
  calc ENNReal.ofReal |∑ x ∈ S, w x * h x|
      ≤ ENNReal.ofReal (A + ∑ k ∈ Finset.range K, B k) := ENNReal.ofReal_le_ofReal hm
    _ = ENNReal.ofReal A + ∑ k ∈ Finset.range K, ENNReal.ofReal (B k) := by
        rw [ENNReal.ofReal_add hA0 (Finset.sum_nonneg fun k _ => hB0 k),
          ENNReal.ofReal_sum_of_nonneg fun k _ => hB0 k]
    _ ≤ _ := by
        rw [Finset.sum_mul]
        exact add_le_add htop (Finset.sum_le_sum hstep)

/-! ### The random part -/

/-- The weight of the cubes of scale `k` of `S`. -/
noncomputable def cubeWeight (S : Finset (Vertex d)) (k : ℕ) (j : Vertex d) : ℝ≥0∞ :=
  if j ∈ S.image (cubeIndex k) then ENNReal.ofReal ((3 ^ d) ^ k) else 0

theorem sqSum_cubeMean_eq {k : ℕ} {S : Finset (Vertex d)} (hS : IsCubeUnion k S)
    (h : Vertex d → ℝ) :
    sqSum S (fun x => cubeMean h k (cubeIndex k x)) =
      ∑' j, ENNReal.ofReal (cubeMean h k j ^ 2) * cubeWeight S k j := by
  simp only [sqSum]
  rw [sum_eq_sum_cubes hS, tsum_eq_sum (s := S.image (cubeIndex k)) fun j hj => by
    rw [cubeWeight, if_neg hj, mul_zero]]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hc : ∀ x ∈ triadicCubeFinset d k j, ENNReal.ofReal (cubeMean h k (cubeIndex k x) ^ 2) =
      ENNReal.ofReal (cubeMean h k j ^ 2) := fun x hx => by rw [cubeIndex_eq_of_mem hx]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, cubeWeight, if_pos hj, mul_comm]
  congr 1
  rw [← ENNReal.ofReal_natCast]
  congr 1
  exact_mod_cast card_triadicCubeFinsetD k j

theorem tsum_cubeWeight {k : ℕ} {S : Finset (Vertex d)} (hS : IsCubeUnion k S) :
    ∑' j, cubeWeight S k j = ENNReal.ofReal S.card := by
  rw [tsum_eq_sum (s := S.image (cubeIndex k)) fun j hj => by rw [cubeWeight, if_neg hj]]
  have hc : (S.card : ℝ) = ∑ j ∈ S.image (cubeIndex k), ((3 : ℝ) ^ d) ^ k := by
    have h1 := sum_eq_sum_cubes hS (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h1
    rw [h1]
    exact Finset.sum_congr rfl fun j _ => card_triadicCubeFinsetD k j
  rw [hc, ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity]
  exact Finset.sum_congr rfl fun j hj => by rw [cubeWeight, if_pos hj]

theorem rpow_neg_density_eq (C : ℝ) (k : ℕ) :
    C * (3 : ℝ) ^ (-((d : ℝ) * (k : ℝ)) / 2) = C / (3 : ℝ) ^ ((d : ℝ) * k / 2) := by
  rw [neg_div, Real.rpow_neg (by norm_num), ← div_eq_mul_inv]

/-- `3^{k+1} ≤ 3 · 3^{dk/2}` for `d ≥ 2`. -/
theorem three_pow_succ_le (hd : 2 ≤ d) (k : ℕ) :
    (3 : ℝ) ^ (k + 1) ≤ 3 * (3 : ℝ) ^ ((d : ℝ) * k / 2) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ ((d : ℝ) * k / 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  rw [pow_succ]
  linarith

/-- **Step 2 of the proof of Proposition B.1 of Dario–Gu, on `ℤ^d`.** -/
theorem exists_densityWeakNormD [NeZero d] (hd : 2 ≤ d) (hpc : criticalProbability d < (p : ℝ))
    (hp1 : (p : ℝ) < 1) :
    ∃ A κ : ℝ, 0 < A ∧ 0 < κ ∧ ∀ (K : ℕ) (S : Finset (Vertex d)), IsCubeUnion K S →
      ∃ Y Z : Configuration d → ℝ≥0∞, Measurable Y ∧ Measurable Z ∧
        GrowthMomentsD p Y (A * Real.sqrt S.card / (3 : ℝ) ^ ((d : ℝ) * K / 2)) κ ∧
        GrowthMomentsD p Z (A * (K + 1) * Real.sqrt S.card) κ ∧
        ∀ (ω : Configuration d) (T : Finset (Vertex d)) (w : Vertex d → ℝ), S ⊆ T →
          ENNReal.ofReal |∑ x ∈ S, w x * clusterDeviationD ω (theta d p) x| ≤
            Y ω * sqSum S w ^ (1 / 2 : ℝ) + Z ω * gradSqSum T w ^ (1 / 2 : ℝ) := by
  obtain ⟨C₁, hC₁, hA1⟩ := cluster_density_concentration d hd p hpc hp1
  obtain ⟨CP, hCP0, hCP⟩ := exists_sum_sq_sub_cubeMean_leD
  set θ := theta d p with hθ
  obtain ⟨s₀, hs₀, hs₀e⟩ : ∃ s₀ : ℝ, 0 < s₀ ∧
      s₀ = 2 * ((d : ℝ) - 1) / (3 * (d : ℝ) ^ 2 + 2 * (d : ℝ) - 1) := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    exact ⟨_, div_pos (by linarith) (by nlinarith), rfl⟩
  set κ := 1 / s₀ with hκ
  have hκ0 : 0 < κ := by positivity
  obtain ⟨B₀, hB₀0, hB₀⟩ : ∃ B₀ : ℝ, 0 < B₀ ∧ B₀ = 2 * C₁ * (1 / s₀) ^ (1 / s₀) :=
    ⟨_, by positivity, rfl⟩
  have h2κ : (0 : ℝ) < 2 ^ κ := by positivity
  have hmom : ∀ (k : ℕ) (j : Vertex d), GrowthMomentsD p
      (fun ω => ENNReal.ofReal |cubeMean (clusterDeviationD ω θ) k j|)
        (B₀ / (3 : ℝ) ^ ((d : ℝ) * k / 2)) κ := by
    intro k j
    have h := hA1 k j
    rw [rpow_neg_density_eq] at h
    simp only [← cubeMean_clusterDeviationD] at h
    rw [← hs₀e] at h
    have h' := growthMomentsD_of_isOsBond (fun ω => abs_nonneg _) hs₀ (by positivity) h
    refine h'.of_le (by positivity) (le_of_eq ?_) le_rfl
    rw [hB₀]
    ring
  have hXm : ∀ (k : ℕ) (j : Vertex d), Measurable fun ω => cubeMean (clusterDeviationD ω θ) k j :=
    fun k j => measurable_cubeMean_clusterDeviationD θ k j
  refine ⟨B₀ * 2 ^ κ * (1 + 3 * Real.sqrt CP), κ, by positivity, hκ0, fun K S hS => ?_⟩
  set Yk : ℕ → Configuration d → ℝ≥0∞ := fun k ω =>
    (∑' j, ENNReal.ofReal (cubeMean (clusterDeviationD ω θ) k j ^ 2) * cubeWeight S k j) ^
      (1 / 2 : ℝ) with hYk
  have hYkm : ∀ k, Measurable (Yk k) := fun k =>
    (Measurable.tsum fun j => (((hXm k j).pow_const 2).ennreal_ofReal).mul_const _).pow_const _
  have hYmom : ∀ k ≤ K, GrowthMomentsD p (Yk k)
      (Real.sqrt S.card * (B₀ / (3 : ℝ) ^ ((d : ℝ) * k / 2)) * 2 ^ κ) κ := by
    intro k hk
    exact growthMoments_sqrt_weighted_tsum (X := fun j ω => cubeMean (clusterDeviationD ω θ) k j)
      (fun j => hXm k j) (by positivity) hκ0.le (fun j => hmom k j) (Nat.cast_nonneg _)
      (le_of_eq (tsum_cubeWeight (hS.mono hk)))
  set Z : Configuration d → ℝ≥0∞ := fun ω =>
    ∑ k ∈ Finset.range K, Yk k ω * ENNReal.ofReal (Real.sqrt CP * 3 ^ (k + 1)) with hZ
  have hZm : Measurable Z := Finset.measurable_sum _ fun k _ => (hYkm k).mul_const _
  refine ⟨Yk K, Z, hYkm K, hZm, ?_, ?_, ?_⟩
  · refine (hYmom K le_rfl).of_le (by positivity) ?_ le_rfl
    have h3 : (0 : ℝ) < (3 : ℝ) ^ ((d : ℝ) * K / 2) := by positivity
    have hS0 : 0 ≤ Real.sqrt S.card := Real.sqrt_nonneg _
    calc Real.sqrt S.card * (B₀ / (3 : ℝ) ^ ((d : ℝ) * K / 2)) * 2 ^ κ =
          B₀ * 2 ^ κ * Real.sqrt S.card / (3 : ℝ) ^ ((d : ℝ) * K / 2) := by
          ring
      _ ≤ B₀ * 2 ^ κ * (1 + 3 * Real.sqrt CP) * Real.sqrt S.card /
          (3 : ℝ) ^ ((d : ℝ) * K / 2) := by
          rw [div_le_div_iff_of_pos_right h3]
          have h1 : B₀ * 2 ^ κ ≤ B₀ * 2 ^ κ * (1 + 3 * Real.sqrt CP) :=
            le_mul_of_one_le_right (by positivity) (by
              have : 0 ≤ 3 * Real.sqrt CP := by positivity
              linarith)
          exact mul_le_mul_of_nonneg_right h1 hS0
  · have hterm : ∀ k ∈ Finset.range K, GrowthMomentsD p
        (fun ω => Yk k ω * ENNReal.ofReal (Real.sqrt CP * 3 ^ (k + 1)))
        (3 * Real.sqrt CP * B₀ * 2 ^ κ * Real.sqrt S.card) κ := by
      intro k hk
      have hkK : k ≤ K := (Finset.mem_range.1 hk).le
      have h := (hYmom k hkK).const_mul (c := Real.sqrt CP * 3 ^ (k + 1)) (by positivity)
        (by positivity)
      refine (h.mono fun ω => le_of_eq (mul_comm _ _)).of_le (by positivity) ?_ le_rfl
      have h3 : (0 : ℝ) < (3 : ℝ) ^ ((d : ℝ) * k / 2) := by positivity
      have h4 := three_pow_succ_le hd k
      have e : Real.sqrt CP * 3 ^ (k + 1) * (Real.sqrt S.card *
          (B₀ / (3 : ℝ) ^ ((d : ℝ) * k / 2)) * 2 ^ κ) =
          (Real.sqrt CP * B₀ * 2 ^ κ * Real.sqrt S.card) *
            (3 ^ (k + 1) / (3 : ℝ) ^ ((d : ℝ) * k / 2)) := by ring
      rw [e]
      have h5 : (3 : ℝ) ^ (k + 1) / (3 : ℝ) ^ ((d : ℝ) * k / 2) ≤ 3 := by
        rw [div_le_iff₀ h3]
        exact h4
      calc Real.sqrt CP * B₀ * 2 ^ κ * Real.sqrt S.card *
            (3 ^ (k + 1) / (3 : ℝ) ^ ((d : ℝ) * k / 2))
          ≤ Real.sqrt CP * B₀ * 2 ^ κ * Real.sqrt S.card * 3 :=
            mul_le_mul_of_nonneg_left h5 (by positivity)
        _ = 3 * Real.sqrt CP * B₀ * 2 ^ κ * Real.sqrt S.card := by ring
    have hsum := GrowthMomentsD.finsetSum (Finset.range K)
      (fun k => (hYkm k).mul_const (ENNReal.ofReal (Real.sqrt CP * 3 ^ (k + 1)))) (by positivity)
      hterm
    refine hsum.of_le (by positivity) ?_ le_rfl
    rw [Finset.card_range]
    have hS0 : 0 ≤ Real.sqrt S.card := Real.sqrt_nonneg _
    have hc : 0 ≤ B₀ * 2 ^ κ * Real.sqrt S.card := by positivity
    have hK : (K : ℝ) ≤ K + 1 := by linarith
    calc (K : ℝ) * (3 * Real.sqrt CP * B₀ * 2 ^ κ * Real.sqrt S.card)
        = (K : ℝ) * (3 * Real.sqrt CP) * (B₀ * 2 ^ κ * Real.sqrt S.card) := by ring
      _ ≤ (K + 1) * (1 + 3 * Real.sqrt CP) * (B₀ * 2 ^ κ * Real.sqrt S.card) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul hK (by linarith) (by positivity)
            (by positivity)) hc
      _ = B₀ * 2 ^ κ * (1 + 3 * Real.sqrt CP) * (K + 1) * Real.sqrt S.card := by ring
  · intro ω T w hST
    have key := ofReal_abs_sum_mul_le_density hCP0 hCP hS hST w (clusterDeviationD ω θ)
    refine key.trans (le_of_eq ?_)
    rw [sqSum_cubeMean_eq hS]
    congr 2
    rw [hZ]
    exact Finset.sum_congr rfl fun k hk => by
      rw [sqSum_cubeMean_eq (hS.mono (Finset.mem_range.1 hk).le)]

end Rigidity.Green.GeneralFlux
