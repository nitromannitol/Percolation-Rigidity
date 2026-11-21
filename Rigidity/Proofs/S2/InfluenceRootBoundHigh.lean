import Rigidity.Proofs.S2.InfluenceRadiusTail
import Rigidity.Proofs.S2.DensityResamplingEnergy
import Rigidity.Proofs.S2.TriadicCubeGeometry
import Rigidity.Proofs.S2.InfluenceFactorialGrowth
import Rigidity.Proofs.Percolation.BondShellExponential

/-!
# Summable influence roots in dimension at least three

Above the critical point in dimension `d ≥ 3`, the `r`-th roots of the `L^{2r}` moments of the
single-bond influences on the infinite-cluster count of a triadic cube of size `3^m` are summable
over the bonds, with sum at most `C r^{3d+2} (3^m + 1)^d`. The factorial moment bounds give
roots at most `L r^{2d}` for every bond, the bonds in the `n`-th shell around the cube have roots
at most `L r^{2d} e^{-cn/r}`, and the shell kernel at rate `c/r` is at most `E r^{d+2}`.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External

variable {d : ℕ}

/-- The factorial majorant of the squared-influence moments has root growth of order `2d`. -/
theorem influence_factorial_root_growth_dim (hd : 1 ≤ d) (a A a' A' B : ℝ)
    (ha : 0 < a) (hA : 0 < A) (ha' : 0 < a') (hA' : 0 < A') (hB : 0 < B) :
    ∃ L : ℝ, 0 < L ∧ ∀ r : ℕ, 1 ≤ r →
      ((4 : ℝ) ^ (2 * r + 1) * (((d * (2 * r)).factorial : ℝ) / a ^ (d * (2 * r))) * A +
        Real.sqrt ((4 : ℝ) ^ (2 * (2 * r) + 1) *
          (((d * (2 * (2 * r))).factorial : ℝ) / a' ^ (d * (2 * (2 * r)))) * A') *
          Real.sqrt B + 1) ^ (1 / (r : ℝ)) ≤ L * (r : ℝ) ^ (2 * d) := by
  obtain ⟨L1, hL1, hfac1⟩ := factorial_moment_le_order_pow a A ha hA
  obtain ⟨L2, hL2, hfac2⟩ := factorial_moment_le_order_pow a' A' ha' hA'
  let L0 : ℝ := max 1 (max L1 L2)
  let L : ℝ := (4 * d * L0) ^ (2 * d) * (2 + Real.sqrt B)
  have hL01 : 1 ≤ L0 := le_max_left _ _
  have hL0 : 0 < L0 := zero_lt_one.trans_le hL01
  have h1 : L1 ≤ L0 := (le_max_left _ _).trans (le_max_right _ _)
  have h2 : L2 ≤ L0 := (le_max_right _ _).trans (le_max_right _ _)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L, hL, fun r hr => ?_⟩
  let x : ℝ := 4 * d * L0 * (r : ℝ)
  let N : ℕ := d * (2 * r)
  let N' : ℕ := d * (2 * (2 * r))
  let Q : ℝ := (4 : ℝ) ^ (2 * r + 1) * ((N.factorial : ℝ) / a ^ N) * A
  let T : ℝ := (4 : ℝ) ^ (2 * (2 * r) + 1) * ((N'.factorial : ℝ) / a' ^ N') * A'
  let K : ℝ := Q + Real.sqrt T * Real.sqrt B + 1
  have hu1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hu : (0 : ℝ) < r := zero_lt_one.trans_le hu1
  have hdu : 0 ≤ (d : ℝ) * (r : ℝ) := by positivity
  have hdLu : 1 ≤ (d : ℝ) * L0 * r := by
    have h1 : (1 : ℝ) * 1 ≤ d * L0 := mul_le_mul hdR hL01 zero_le_one (by positivity)
    have h2 : (1 : ℝ) * 1 * 1 ≤ d * L0 * r := mul_le_mul h1 hu1 zero_le_one (by positivity)
    linarith
  have hx1 : 1 ≤ x := by dsimp only [x]; nlinarith
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hN : 1 ≤ N := Nat.mul_pos (by omega) (by omega)
  have hN' : 1 ≤ N' := Nat.mul_pos (by omega) (by omega)
  have hpref : (4 : ℝ) ^ (2 * r + 1) ≤ (4 : ℝ) ^ (N + 1) := by
    apply pow_le_pow_right₀ (by norm_num)
    have h1 := Nat.mul_le_mul_right (2 * r) hd
    simp only [one_mul] at h1
    exact Nat.add_le_add_right h1 1
  have hpref' : (4 : ℝ) ^ (2 * (2 * r) + 1) ≤ (4 : ℝ) ^ (N' + 1) := by
    apply pow_le_pow_right₀ (by norm_num)
    have h1 := Nat.mul_le_mul_right (2 * (2 * r)) hd
    simp only [one_mul] at h1
    exact Nat.add_le_add_right h1 1
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hQ : Q ≤ x ^ N := by
    have hQ' : Q ≤ (L1 * (N : ℝ)) ^ N := by
      have hpre := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpref
          (by positivity : 0 ≤ (N.factorial : ℝ) / a ^ N)) hA.le
      exact hpre.trans (hfac1 N hN)
    have hbase : L1 * (N : ℝ) ≤ x := by
      dsimp only [x, N]
      push_cast
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) hdu, mul_nonneg hL0.le hdu]
    exact hQ'.trans (pow_le_pow_left₀ (by positivity) hbase _)
  have hT : T ≤ x ^ N' := by
    have hT' : T ≤ (L2 * (N' : ℝ)) ^ N' := by
      have hpre := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpref'
          (by positivity : 0 ≤ (N'.factorial : ℝ) / a' ^ N')) hA'.le
      exact hpre.trans (hfac2 N' hN')
    have hbase : L2 * (N' : ℝ) ≤ x := by
      dsimp only [x, N']
      push_cast
      nlinarith [mul_nonneg (sub_nonneg.mpr h2) hdu, mul_nonneg hL0.le hdu]
    exact hT'.trans (pow_le_pow_left₀ (by positivity) hbase _)
  have hNN : N' = N * 2 := by dsimp only [N, N']; ring
  have hsqrt : Real.sqrt T ≤ x ^ N := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, hT.trans_eq ?_⟩
    rw [hNN, pow_mul]
  have hxpow : 1 ≤ x ^ N := one_le_pow₀ hx1
  have hcoef : 1 ≤ 2 + Real.sqrt B := by linarith [Real.sqrt_nonneg B]
  have hcoefpow : 2 + Real.sqrt B ≤ (2 + Real.sqrt B) ^ r :=
    le_self_pow₀ hcoef (by omega)
  have hNr : x ^ N = (x ^ (2 * d)) ^ r := by
    rw [← pow_mul]
    congr 1
    dsimp only [N]
    ring
  have hKbound : K ≤ (x ^ (2 * d) * (2 + Real.sqrt B)) ^ r := by
    calc
      K ≤ x ^ N * (2 + Real.sqrt B) := by
        dsimp only [K]
        have hmul := mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg B)
        nlinarith
      _ ≤ x ^ N * (2 + Real.sqrt B) ^ r :=
        mul_le_mul_of_nonneg_left hcoefpow (by positivity)
      _ = (x ^ (2 * d)) ^ r * (2 + Real.sqrt B) ^ r := by rw [hNr]
      _ = (x ^ (2 * d) * (2 + Real.sqrt B)) ^ r := (mul_pow _ _ _).symm
  have hbase0 : 0 ≤ x ^ (2 * d) * (2 + Real.sqrt B) := by positivity
  have ht0 : 0 ≤ 1 / (r : ℝ) := by positivity
  have hroot := Real.rpow_le_rpow hK0 hKbound ht0
  have hrootEq : ((x ^ (2 * d) * (2 + Real.sqrt B)) ^ r) ^ (1 / (r : ℝ)) =
      x ^ (2 * d) * (2 + Real.sqrt B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase0]
    have hu0 : (r : ℝ) ≠ 0 := ne_of_gt hu
    simp only [mul_one_div, div_self hu0, Real.rpow_one]
  rw [hrootEq] at hroot
  change K ^ (1 / (r : ℝ)) ≤ L * (r : ℝ) ^ (2 * d)
  calc
    _ ≤ x ^ (2 * d) * (2 + Real.sqrt B) := hroot
    _ = L * (r : ℝ) ^ (2 * d) := by dsimp only [L, x]; rw [mul_pow]; ring

/-- A larger order exponent weakens a summable influence-root bound. -/
theorem DensityInfluenceRootBound.mono {p : unitInterval} {β β' : ℕ} (hββ' : β ≤ β')
    (h : DensityInfluenceRootBound d p β) : DensityInfluenceRootBound d p β' := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C, hC, fun r hr m k => ⟨(hbound r hr m k).1, (hbound r hr m k).2.trans ?_⟩⟩
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hpow : (r : ℝ) ^ β ≤ (r : ℝ) ^ β' := pow_le_pow_right₀ hr1 hββ'
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC.le) (by positivity)

/-- Above the critical point in dimension at least three, the influence moment roots are
summable with sum at most `C r^{3d+2} (3^m + 1)^d`. -/
theorem densityInfluenceRootBound_of_three_le [NeZero d] (hd : 3 ≤ d) {p : unitInterval}
    (hp : criticalProbability d < (p : ℝ)) :
    DensityInfluenceRootBound d p (3 * d + 2) := by
  classical
  obtain ⟨a, A, ha, hA, hmoment⟩ := density_influence_polynomial_moment hd hp
  obtain ⟨a', A', b, B, ha', hA', hb, hB, hspatial⟩ := density_influence_spatial_moment hd hp
  obtain ⟨L, hL, hrootGrowth⟩ :=
    influence_factorial_root_growth_dim (d := d) (by omega) a A a' A' B ha hA ha' hA' hB
  let c : ℝ := b / 2
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨E, hE, hkernelGrowth⟩ := Rigidity.Percolation.exp_shell_kernel_order_growth d hc
  let C : ℝ := 2 * d * 3 ^ d * L * E
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun r hr m k => ?_⟩
  let s : ℕ := 2 * r
  let Q : ℝ := (4 : ℝ) ^ (s + 1) * (((d * s).factorial : ℝ) / a ^ (d * s)) * A
  let T : ℝ := (4 : ℝ) ^ (2 * s + 1) *
    (((d * (2 * s)).factorial : ℝ) / a' ^ (d * (2 * s))) * A'
  let K : ℝ := Q + Real.sqrt T * Real.sqrt B + 1
  let t : ℝ := 1 / (r : ℝ)
  let q : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ d * Real.exp (-(c * t) * n)
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hq0 : 0 ≤ ∑' n, q n := tsum_nonneg fun n => by dsimp [q]; positivity
  have hroot : K ^ t ≤ L * (r : ℝ) ^ (2 * d) := hrootGrowth r hr
  have hkernel : 1 + ∑' n, q n ≤ E * (r : ℝ) ^ (d + 2) := (hkernelGrowth r hr).2
  let μ := (latticeBondLaw d p).prod (latticeBondLaw d p)
  let z : Vertex d := fun i => (3 : ℤ) ^ m * k i
  let R : ℕ := 3 ^ m
  let f : Bond d → ℝ := fun e => ∫ q : Configuration d × Configuration d,
    |(infiniteClusterCount (triadicCube d m k) q.1 : ℝ) -
      (infiniteClusterCount (triadicCube d m k) (resampleBond q.1 q.2 e) : ℝ)| ^ s ∂μ
  have hf (e : Bond d) : 0 ≤ f e := integral_nonneg fun q => pow_nonneg (abs_nonneg _) _
  have hglobal (e : Bond d) : f e ≤ K := by
    have h := (hmoment m k e s hs).2
    have hQK : Q ≤ K := by
      dsimp [K]; nlinarith [mul_nonneg (Real.sqrt_nonneg T) (Real.sqrt_nonneg B)]
    exact h.trans hQK
  have hdecay (n : ℕ) (hn : 1 ≤ n) (e : Bond d)
      (he : e ∈ Rigidity.Percolation.bondShell d z R n) :
      f e ≤ K * Real.exp (-c * n) := by
    obtain ⟨i, hsep⟩ := Rigidity.Percolation.bondShell_separated z R n e he
    have hsep' : ∀ x ∈ triadicCube d m k, ∀ y ∈ e.val,
        (n : ℝ) ≤ |(x i : ℝ) - (y i : ℝ)| :=
      fun x hx => hsep x (triadicCube_subset_cubeAt m k hx)
    have h := (hspatial m k e s hs i n hsep').2
    have hsqrt : Real.sqrt (B * Real.exp (-(b * n))) =
        Real.sqrt B * Real.exp (-c * n) := by
      rw [Real.sqrt_mul hB.le, ← Real.exp_half]
      congr 1
      dsimp [c]
      ring
    rw [hsqrt] at h
    have hTK : Real.sqrt T * Real.sqrt B ≤ K := by dsimp [K]; linarith
    exact h.trans (by
      calc
        _ = (Real.sqrt T * Real.sqrt B) * Real.exp (-c * n) := by ring
        _ ≤ K * Real.exp (-c * n) :=
          mul_le_mul_of_nonneg_right hTK (Real.exp_pos _).le)
  obtain ⟨_, hfs, hsum⟩ := Rigidity.Percolation.summable_bond_shells_exp_rpow z R f K c t
    hK.le hc ht hf hglobal hdecay
  refine ⟨hfs, hsum.trans ?_⟩
  change 2 * d * 3 ^ d * ((R : ℝ) + 1) ^ d * K ^ t * (1 + ∑' n, q n) ≤
    C * (r : ℝ) ^ (3 * d + 2) * ((R : ℝ) + 1) ^ d
  have hprod : K ^ t * (1 + ∑' n, q n) ≤
      (L * (r : ℝ) ^ (2 * d)) * (E * (r : ℝ) ^ (d + 2)) :=
    mul_le_mul hroot hkernel (by linarith) (by positivity)
  have hvol : 0 ≤ 2 * (d : ℝ) * 3 ^ d * ((R : ℝ) + 1) ^ d := by positivity
  calc
    _ = (2 * (d : ℝ) * 3 ^ d * ((R : ℝ) + 1) ^ d) * (K ^ t * (1 + ∑' n, q n)) := by ring
    _ ≤ (2 * (d : ℝ) * 3 ^ d * ((R : ℝ) + 1) ^ d) *
        ((L * (r : ℝ) ^ (2 * d)) * (E * (r : ℝ) ^ (d + 2))) :=
      mul_le_mul_of_nonneg_left hprod hvol
    _ = _ := by dsimp only [C]; ring

end Rigidity.Proofs.S2
