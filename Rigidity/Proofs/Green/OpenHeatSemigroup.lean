import Rigidity.Proofs.Green.LazyCarneVaropoulos
import LatticeProb.Analysis.KernelPowersCS

/-!
# Symmetry, mass and the semigroup property of the heat kernel

For a locally finite graph with degrees at most `D > 0`, the powers `Qⁿ` of the lazy kernel are
the powers of the symmetric stochastic kernel `lazyKernel` (`lazyPow_eq_kernelPow`), so they are
symmetric, have rows of mass one and satisfy `Q^{m+n} = Qᵐ Qⁿ` (Lattice-Probability,
`kernelPow_symm`, `kernelPow_hasSum`, `kernelPow_add`). Averaging over the Poisson number of steps
and the binomial identity `Pois(D(s+t)) = Pois(Ds) * Pois(Dt)` give, for `s, t ≥ 0`,

* `vsrwHeat_symm`: `p_t(x, y) = p_t(y, x)`;
* `hasSum_vsrwHeat`: `Σ_y p_t(x, y) = 1`;
* `hasSum_vsrwHeat_mul`: `Σ_y p_s(x, y) p_t(y, z) = p_{s+t}(x, z)` (the semigroup property used in
  Dario–Gu, (4.48) and in the Duhamel formula (4.6)),

and `p_t(x, y) = 0` when `y` is not reachable from `x` (`vsrwHeat_eq_zero_of_not_reachable`).
-/

open scoped Classical ENNReal
open Finset

namespace Rigidity.Green

variable {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] (D : ℕ)

/-- The lazy kernel `Q(x, z) = (1 - deg x / D) 1_{x = z} + 1_{x ∼ z} / D`. -/
noncomputable def lazyKernel (x z : V) : ℝ :=
  (if x = z then 1 - (G.degree x : ℝ) / D else 0) + (if G.Adj x z then 1 / (D : ℝ) else 0)

variable {G D}

theorem lazyKernel_eq_zero_of_notMem {x z : V} (h : z ∉ insert x (G.neighborFinset x)) :
    lazyKernel G D x z = 0 := by
  simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or] at h
  have hxz : x ≠ z := fun e => h.1 e.symm
  simp [lazyKernel, hxz, h.2]

theorem tsum_lazyKernel_mul (f : V → ℝ) (x : V) :
    ∑' z, lazyKernel G D x z * f z =
      (1 - (G.degree x : ℝ) / D) * f x + 1 / (D : ℝ) * ∑ z ∈ G.neighborFinset x, f z := by
  rw [tsum_eq_sum (s := insert x (G.neighborFinset x)) (fun z hz => by
    rw [lazyKernel_eq_zero_of_notMem hz, zero_mul])]
  have hx : x ∉ G.neighborFinset x := by simp
  rw [Finset.sum_insert hx]
  have h1 : lazyKernel G D x x = 1 - (G.degree x : ℝ) / D := by simp [lazyKernel]
  have h2 : ∀ z ∈ G.neighborFinset x, lazyKernel G D x z * f z = 1 / (D : ℝ) * f z := by
    intro z hz
    rw [SimpleGraph.mem_neighborFinset] at hz
    simp [lazyKernel, hz, hz.ne]
  rw [h1, Finset.sum_congr rfl h2, ← Finset.mul_sum]

theorem summable_lazyKernel (x : V) : Summable (lazyKernel G D x) :=
  summable_of_ne_finset_zero (s := insert x (G.neighborFinset x))
    (fun _ hz => lazyKernel_eq_zero_of_notMem hz)

theorem hasSum_lazyKernel (hD : 0 < D) (x : V) : HasSum (lazyKernel G D x) 1 := by
  have h := tsum_lazyKernel_mul (G := G) (D := D) (fun _ => 1) x
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree]
    at h
  rw [(summable_lazyKernel x).hasSum_iff, h]
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  field_simp
  ring

theorem lazyKernel_nonneg (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) (x z : V) :
    0 ≤ lazyKernel G D x z := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have h1 : 0 ≤ 1 - (G.degree x : ℝ) / D := by
    rw [sub_nonneg, div_le_one hD']
    exact_mod_cast hdeg x
  unfold lazyKernel
  apply add_nonneg
  · split_ifs <;> [exact h1; exact le_rfl]
  · split_ifs <;> [positivity; exact le_rfl]

theorem lazyKernel_symm (x z : V) : lazyKernel G D x z = lazyKernel G D z x := by
  by_cases h : x = z
  · subst h
    rfl
  · by_cases ha : G.Adj x z
    · simp [lazyKernel, h, Ne.symm h, ha, ha.symm]
    · have hb : ¬ G.Adj z x := fun hb => ha hb.symm
      simp [lazyKernel, h, Ne.symm h, ha, hb]

theorem kernelPow_one_eq (K : V → V → ℝ) : LatticeProb.kernelPow K 1 = K := by
  funext u v
  simp [LatticeProb.kernelPow, LatticeProb.kernelComp, ite_mul]

/-- `Qⁿ` is the `n`-th power of the lazy kernel. -/
theorem lazyPow_eq_kernelPow (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) (n : ℕ) :
    lazyPow G D n = LatticeProb.kernelPow (lazyKernel G D) n := by
  induction n with
  | zero =>
    funext x y
    simp [lazyPow_zero, LatticeProb.kernelPow]
  | succ n ih =>
    funext x y
    have h := LatticeProb.kernelPow_add (lazyKernel_nonneg hD hdeg) (hasSum_lazyKernel hD) 1 n x y
    rw [Nat.add_comm 1 n, kernelPow_one_eq, ← ih] at h
    rw [h, lazyPow_succ, tsum_lazyKernel_mul]

theorem lazyPow_symm (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) (n : ℕ) (x y : V) :
    lazyPow G D n x y = lazyPow G D n y x := by
  rw [lazyPow_eq_kernelPow hD hdeg]
  exact LatticeProb.kernelPow_symm (lazyKernel_nonneg hD hdeg) (hasSum_lazyKernel hD)
    lazyKernel_symm n x y

theorem hasSum_lazyPow_of_degree_le (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) (n : ℕ) (x : V) :
    HasSum (lazyPow G D n x) 1 := by
  rw [lazyPow_eq_kernelPow hD hdeg]
  exact LatticeProb.kernelPow_hasSum (lazyKernel_nonneg hD hdeg) (hasSum_lazyKernel hD) n x

theorem lazyPow_add (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) (m n : ℕ) (x z : V) :
    lazyPow G D (m + n) x z = ∑' y, lazyPow G D m x y * lazyPow G D n y z := by
  simp only [lazyPow_eq_kernelPow hD hdeg]
  exact LatticeProb.kernelPow_add (lazyKernel_nonneg hD hdeg) (hasSum_lazyKernel hD) m n x z

theorem summable_lazyPow_mul (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) (m n : ℕ) (x z : V) :
    Summable fun y => lazyPow G D m x y * lazyPow G D n y z :=
  (hasSum_lazyPow_of_degree_le hD hdeg m x).summable.of_nonneg_of_le
    (fun y => mul_nonneg (lazyPow_mem_Icc hD hdeg m x y).1 (lazyPow_mem_Icc hD hdeg n y z).1)
    (fun y => mul_le_of_le_one_right (lazyPow_mem_Icc hD hdeg m x y).1
      (lazyPow_mem_Icc hD hdeg n y z).2)

/-- `Pois(D(s + t)) = Pois(Ds) * Pois(Dt)`. -/
theorem poissonWeight_add (s t : ℝ) (N : ℕ) :
    poissonWeight D (s + t) N =
      ∑ kl ∈ antidiagonal N, poissonWeight D s kl.1 * poissonWeight D t kl.2 := by
  unfold poissonWeight
  have h : ((D : ℝ) * (s + t)) ^ N =
      ∑ kl ∈ antidiagonal N, ((N.choose kl.1 : ℕ) : ℝ) * ((D * s) ^ kl.1 * (D * t) ^ kl.2) := by
    rw [mul_add, (Commute.all _ _).add_pow']
    simp only [nsmul_eq_mul]
  rw [h, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  obtain ⟨k, l⟩ := kl
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
  subst hkl
  rw [Nat.cast_add_choose, show -(D : ℝ) * (s + t) = -D * s + -D * t by ring, Real.exp_add]
  have hk : ((k.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hl : ((l.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hkl : (((k + l).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-! ### The heat kernel -/

theorem vsrwHeat_symm (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) (t : ℝ) (x y : V) :
    vsrwHeat G D t x y = vsrwHeat G D t y x := by
  simp only [vsrwHeat, lazyPow_symm hD hdeg _ x y]

theorem ofReal_vsrwHeat (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {t : ℝ} (ht : 0 ≤ t)
    (x y : V) :
    ENNReal.ofReal (vsrwHeat G D t x y) =
      ∑' n, ENNReal.ofReal (poissonWeight D t n) * ENNReal.ofReal (lazyPow G D n x y) := by
  rw [vsrwHeat, ENNReal.ofReal_tsum_of_nonneg
    (fun n => mul_nonneg (poissonWeight_nonneg ht n) (lazyPow_mem_Icc hD hdeg n x y).1)
    (summable_vsrwHeat hD hdeg t x y)]
  exact tsum_congr fun n => ENNReal.ofReal_mul (poissonWeight_nonneg ht n)

theorem tsum_ofReal_lazyPow (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) (n : ℕ) (x : V) :
    ∑' y, ENNReal.ofReal (lazyPow G D n x y) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun y => (lazyPow_mem_Icc hD hdeg n x y).1)
    (hasSum_lazyPow_of_degree_le hD hdeg n x).summable, (hasSum_lazyPow_of_degree_le hD hdeg n x).tsum_eq,
    ENNReal.ofReal_one]

theorem tsum_ofReal_poissonWeight {t : ℝ} (ht : 0 ≤ t) :
    ∑' n, ENNReal.ofReal (poissonWeight D t n) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (poissonWeight_nonneg ht)
    (hasSum_poissonWeight t).summable, (hasSum_poissonWeight t).tsum_eq, ENNReal.ofReal_one]

/-- The rows of the heat kernel have mass one. -/
theorem hasSum_vsrwHeat (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {t : ℝ} (ht : 0 ≤ t)
    (x : V) : HasSum (fun y => vsrwHeat G D t x y) 1 := by
  have hE : ∑' y, ENNReal.ofReal (vsrwHeat G D t x y) = 1 := by
    simp_rw [ofReal_vsrwHeat hD hdeg ht]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, tsum_ofReal_lazyPow hD hdeg, mul_one]
    exact tsum_ofReal_poissonWeight ht
  have hs : Summable fun y => vsrwHeat G D t x y := by
    have := ENNReal.summable_toReal (f := fun y => ENNReal.ofReal (vsrwHeat G D t x y))
      (by rw [hE]; exact ENNReal.one_ne_top)
    simpa [ENNReal.toReal_ofReal (vsrwHeat_nonneg hD hdeg ht x _)] using this
  rw [hs.hasSum_iff]
  have := ENNReal.ofReal_tsum_of_nonneg (fun y => vsrwHeat_nonneg hD hdeg ht x y) hs
  rw [hE, ← ENNReal.ofReal_one] at this
  exact (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg fun y => vsrwHeat_nonneg hD hdeg ht x y)
    zero_le_one).1 this

theorem summable_vsrwHeat_mul (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {s t : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) (x z : V) :
    Summable fun y => vsrwHeat G D s x y * vsrwHeat G D t y z :=
  (hasSum_vsrwHeat hD hdeg hs x).summable.of_nonneg_of_le
    (fun y => mul_nonneg (vsrwHeat_nonneg hD hdeg hs x y) (vsrwHeat_nonneg hD hdeg ht y z))
    (fun y => mul_le_of_le_one_right (vsrwHeat_nonneg hD hdeg hs x y)
      (vsrwHeat_le_one hD hdeg ht y z))

theorem tsum_ofReal_lazyPow_mul (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) (m n : ℕ) (x z : V) :
    ∑' y, ENNReal.ofReal (lazyPow G D m x y) * ENNReal.ofReal (lazyPow G D n y z) =
      ENNReal.ofReal (lazyPow G D (m + n) x z) := by
  rw [lazyPow_add hD hdeg, ENNReal.ofReal_tsum_of_nonneg
    (fun y => mul_nonneg (lazyPow_mem_Icc hD hdeg m x y).1 (lazyPow_mem_Icc hD hdeg n y z).1)
    (summable_lazyPow_mul hD hdeg m n x z)]
  exact tsum_congr fun y => (ENNReal.ofReal_mul (lazyPow_mem_Icc hD hdeg m x y).1).symm

/-- **The semigroup property**: `Σ_y p_s(x, y) p_t(y, z) = p_{s+t}(x, z)` for `s, t ≥ 0`. -/
theorem hasSum_vsrwHeat_mul (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {s t : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) (x z : V) :
    HasSum (fun y => vsrwHeat G D s x y * vsrwHeat G D t y z) (vsrwHeat G D (s + t) x z) := by
  have hsum := summable_vsrwHeat_mul hD hdeg hs ht x z
  rw [hsum.hasSum_iff]
  have h0 : ∀ y, 0 ≤ vsrwHeat G D s x y * vsrwHeat G D t y z :=
    fun y => mul_nonneg (vsrwHeat_nonneg hD hdeg hs x y) (vsrwHeat_nonneg hD hdeg ht y z)
  refine (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg h0)
    (vsrwHeat_nonneg hD hdeg (add_nonneg hs ht) x z)).1 ?_
  rw [ENNReal.ofReal_tsum_of_nonneg h0 hsum]
  simp_rw [ENNReal.ofReal_mul (vsrwHeat_nonneg hD hdeg hs x _), ofReal_vsrwHeat hD hdeg hs,
    ofReal_vsrwHeat hD hdeg ht, ofReal_vsrwHeat hD hdeg (add_nonneg hs ht)]
  simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  conv_lhs => arg 1; ext m; rw [ENNReal.tsum_comm]
  -- the sum over `y` of `a_m Qᵐ(x, y) b_n Qⁿ(y, z)` is `a_m b_n Q^{m+n}(x, z)`
  have hy : ∀ m n : ℕ, ∑' y, ENNReal.ofReal (poissonWeight D s m) *
      ENNReal.ofReal (lazyPow G D m x y) *
        (ENNReal.ofReal (poissonWeight D t n) * ENNReal.ofReal (lazyPow G D n y z)) =
      ENNReal.ofReal (poissonWeight D s m) * ENNReal.ofReal (poissonWeight D t n) *
        ENNReal.ofReal (lazyPow G D (m + n) x z) := by
    intro m n
    rw [← tsum_ofReal_lazyPow_mul hD hdeg m n x z, ← ENNReal.tsum_mul_left]
    exact tsum_congr fun y => by ring
  simp_rw [hy]
  rw [← ENNReal.tsum_prod (f := fun m n => ENNReal.ofReal (poissonWeight D s m) *
    ENNReal.ofReal (poissonWeight D t n) * ENNReal.ofReal (lazyPow G D (m + n) x z)),
    ← (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun N => ?_
  rw [tsum_fintype]
  change ∑ kl : ↥(antidiagonal N), (fun kl : ℕ × ℕ => ENNReal.ofReal (poissonWeight D s kl.1) *
    ENNReal.ofReal (poissonWeight D t kl.2) * ENNReal.ofReal (lazyPow G D (kl.1 + kl.2) x z))
      kl.val = _
  rw [Finset.sum_coe_sort (antidiagonal N) (fun kl => ENNReal.ofReal (poissonWeight D s kl.1) *
    ENNReal.ofReal (poissonWeight D t kl.2) * ENNReal.ofReal (lazyPow G D (kl.1 + kl.2) x z))]
  rw [Finset.sum_congr rfl (g := fun kl => ENNReal.ofReal (poissonWeight D s kl.1 *
      poissonWeight D t kl.2) * ENNReal.ofReal (lazyPow G D N x z)) (fun kl hkl => by
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
    rw [hkl, ENNReal.ofReal_mul (poissonWeight_nonneg hs _)]),
    ← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun kl _ =>
      mul_nonneg (poissonWeight_nonneg hs _) (poissonWeight_nonneg ht _)),
    ← poissonWeight_add]

/-- A nonzero entry of the heat kernel joins points of one connected component. -/
theorem vsrwHeat_eq_zero_of_not_reachable {x y : V} (h : ¬ G.Reachable x y) (t : ℝ) :
    vsrwHeat G D t x y = 0 := by
  have : ∀ n, lazyPow G D n x y = 0 := fun n => by
    by_contra hne
    obtain ⟨q, -⟩ := exists_walk_of_lazyPow_ne_zero n x y hne
    exact h ⟨q⟩
  simp [vsrwHeat, this]

/-! ### The planar heat kernel -/

theorem openHeat_symm (ω : LatticeProb.Percolation.Configuration 2) (t : ℝ)
    (x y : LatticeProb.Percolation.Vertex 2) : openHeat ω t x y = openHeat ω t y x :=
  vsrwHeat_symm (by norm_num) (openGraph_degree_le_four ω) t x y

theorem hasSum_openHeat (ω : LatticeProb.Percolation.Configuration 2) {t : ℝ} (ht : 0 ≤ t)
    (x : LatticeProb.Percolation.Vertex 2) : HasSum (fun y => openHeat ω t x y) 1 :=
  hasSum_vsrwHeat (by norm_num) (openGraph_degree_le_four ω) ht x

theorem hasSum_openHeat_mul (ω : LatticeProb.Percolation.Configuration 2) {s t : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) (x z : LatticeProb.Percolation.Vertex 2) :
    HasSum (fun y => openHeat ω s x y * openHeat ω t y z) (openHeat ω (s + t) x z) :=
  hasSum_vsrwHeat_mul (by norm_num) (openGraph_degree_le_four ω) hs ht x z

theorem openHeat_eq_zero_of_not_reachable (ω : LatticeProb.Percolation.Configuration 2)
    {x y : LatticeProb.Percolation.Vertex 2} (h : ¬ (LatticeProb.Percolation.openGraph ω).Reachable x y)
    (t : ℝ) : openHeat ω t x y = 0 :=
  vsrwHeat_eq_zero_of_not_reachable h t

end Rigidity.Green
