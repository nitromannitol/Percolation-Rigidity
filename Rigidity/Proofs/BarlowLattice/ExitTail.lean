import Rigidity.Proofs.BarlowLattice.ExitTime
import Rigidity.Proofs.BarlowLattice.MeanDisplacement

/-!
# The tail of exit times

This file proves Lemma 3.5, Lemma 3.6 (in its generating-function form) and Proposition 3.7 of
Barlow (*Random walks on supercritical percolation clusters*, Ann. Probab. 32 (2004)) for the
lazy walk `X` with kernel `Q` whose Poisson average is the heat kernel `bondHeat` on `ℤ^d`:

* `discMean ω z k = E^z |X_k - z|` is `1`-Lipschitz in `k` (`discMean_succ_le`,
  `le_discMean_succ`) and is controlled by the continuous mean displacement:
  `E^z |X_k - z| ≤ M(z, k/(2d)) + 6 √k` (`discMean_le_meanDist_add`);
* **Lemma 3.5**: `(r - M̄) P^x(σ(x, r) ≤ n) ≤ E^x |X_{2n} - x|` if `E^z |X_k - z| ≤ M̄` for
  `n ≤ k ≤ 2n` at the points `z` with `|z - x| < r + 1` (`exitProb_clBall_le`), proved by optional
  stopping of the space-time function `(j, w) ↦ E^w |X_{2n - j} - x|`;
* **Lemma 3.6 and Proposition 3.7**: if `P^z(σ(z, r) ≤ k) ≤ 1/2 + a k` for `k ≤ N` at every centre
  `z` of a region, then `P^x(σ(x, m(r + 1)) ≤ N) ≤ e^{8aN} (3/4)^m`
  (`exitProb_clBall_le_exp`); the source iterates successive exit times and applies Lemma 3.6
  (Barlow–Bass); here the generating function `E[s^σ]` is submultiplicative along nested balls
  (`exitGen_clBall_le_pow`).
-/

open scoped Classical
open Finset LatticeProb.Percolation Rigidity.Green Rigidity.WeakPoincare

namespace Rigidity.BarlowLattice

variable {d : ℕ}

variable [NeZero d] {ω : Configuration d}

omit [NeZero d] in
/-- The triangle inequality in the form `|x - z| ≤ |y - z| + |y - x|`. -/
theorem latticeDist_triangle' (x y z : Vertex d) :
    latticeDist x z ≤ latticeDist y z + latticeDist y x := by
  have h := latticeDist_triangle x y z
  rw [latticeDist_comm x y] at h
  linarith

/-- The points of the component `K` at Euclidean distance `< r` from `x`. -/
def clBall {ω : Configuration d} (K : OpenComponent ω) (x : Vertex d) (r : ℝ) : Set (Vertex d) :=
  {w | w ∈ K.supp ∧ latticeDist w x < r}

omit [NeZero d] in
theorem mem_clBall {K : OpenComponent ω} {x w : Vertex d} {r : ℝ} :
    w ∈ clBall K x r ↔ w ∈ K.supp ∧ latticeDist w x < r := Iff.rfl

omit [NeZero d] in
theorem mem_supp_of_adj {K : OpenComponent ω} {v z : Vertex d} (hv : v ∈ K.supp)
    (h : (openGraph ω).Adj v z) : z ∈ K.supp := by
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hv ⊢
  rw [← hv]
  exact (SimpleGraph.ConnectedComponent.sound h.reachable).symm

/-- A smaller set is left earlier: `P(σ_A ≤ n) ≤ P(σ_{A'} ≤ n)` for `A' ⊆ A`. -/
theorem exitProb_anti {A A' : Set (Vertex d)} (hA : A' ⊆ A) :
    ∀ n w, exitProb ω A n w ≤ exitProb ω A' n w := by
  intro n
  induction n with
  | zero =>
    intro w
    by_cases hw : w ∈ A'
    · rw [exitProb_zero_of_mem hw, exitProb_zero_of_mem (hA hw)]
    · rw [exitProb_of_notMem hw]
      exact (exitProb_mem_Icc A 0 w).2
  | succ n ih =>
    intro w
    by_cases hw : w ∈ A'
    · rw [exitProb_succ_of_mem hw, exitProb_succ_of_mem (hA hw)]
      exact lazyStep_mono fun z _ => ih z
    · rw [exitProb_of_notMem hw]
      exact (exitProb_mem_Icc A _ w).2

/-! ### The action of `Qᵏ` on functions -/

/-- `(Qᵏ g)(w) = Σ_y Qᵏ(w, y) g(y)`. -/
noncomputable def applyPow (ω : Configuration d) (k : ℕ) (g : Vertex d → ℝ) (w : Vertex d) : ℝ :=
  ∑' y, lazyPow (openGraph ω) (2 * d) k w y * g y

omit [NeZero d] in
theorem summable_lazyPow_mul_any (k : ℕ) (w : Vertex d) (g : Vertex d → ℝ) :
    Summable fun y => lazyPow (openGraph ω) (2 * d) k w y * g y :=
  summable_of_ne_finset_zero (s := LatticeProb.Graph.ballFinset (openGraph ω) w k) fun y hy => by
    rw [lazyPow_eq_zero_of_notMem_ballFinset (G := openGraph ω) (D := 2 * d) w y k hy, zero_mul]

omit [NeZero d] in
theorem applyPow_zero (g : Vertex d → ℝ) (w : Vertex d) : applyPow ω 0 g w = g w := by
  unfold applyPow
  have e : (fun y => lazyPow (openGraph ω) (2 * d) 0 w y * g y) = fun y => if y = w then g w else 0 := by
    funext y
    rw [lazyPow_zero]
    by_cases h : y = w
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [e, tsum_ite_eq]

omit [NeZero d] in
theorem applyPow_succ (k : ℕ) (g : Vertex d → ℝ) (w : Vertex d) :
    applyPow ω (k + 1) g w = lazyStep ω (applyPow ω k g) w := by
  unfold applyPow
  have e : ∀ y, lazyPow (openGraph ω) (2 * d) (k + 1) w y * g y =
      lazyStep ω (fun z => lazyPow (openGraph ω) (2 * d) k z y * g y) w := by
    intro y
    rw [lazyPow_succ_eq_lazyStep, mul_comm, ← lazyStep_const_mul]
    congr 1
    funext z
    ring
  rw [tsum_congr e, tsum_lazyStep (fun z y => lazyPow (openGraph ω) (2 * d) k z y * g y)
    (fun z => summable_lazyPow_mul_any k z g) w]

omit [NeZero d] in
theorem applyPow_lazyStep (g : Vertex d → ℝ) :
    ∀ k w, applyPow ω k (lazyStep ω g) w = applyPow ω (k + 1) g w := by
  intro k
  induction k with
  | zero =>
    intro w
    rw [applyPow_zero, applyPow_succ]
    congr 1
    funext z
    rw [applyPow_zero]
  | succ k ih =>
    intro w
    rw [applyPow_succ, applyPow_succ (k + 1)]
    congr 1
    funext z
    exact ih z

theorem applyPow_mono {g g' : Vertex d → ℝ} (h : ∀ y, g y ≤ g' y) (k : ℕ) (w : Vertex d) :
    applyPow ω k g w ≤ applyPow ω k g' w :=
  Summable.tsum_le_tsum (fun y => mul_le_mul_of_nonneg_left (h y)
    (lazyPow_mem_Icc two_mul_dim_pos (openGraph_degree_le_two_mul ω) k w y).1)
    (summable_lazyPow_mul_any k w g) (summable_lazyPow_mul_any k w g')

theorem applyPow_add_const (g : Vertex d → ℝ) (c : ℝ) (k : ℕ) (w : Vertex d) :
    applyPow ω k (fun y => g y + c) w = applyPow ω k g w + c := by
  unfold applyPow
  have hs := hasSum_lazyPow_of_degree_le (G := openGraph ω) (D := 2 * d) two_mul_dim_pos
    (openGraph_degree_le_two_mul ω) k w
  have e : (fun y => lazyPow (openGraph ω) (2 * d) k w y * (g y + c)) =
      fun y => lazyPow (openGraph ω) (2 * d) k w y * g y + c * lazyPow (openGraph ω) (2 * d) k w y := by
    funext y
    ring
  rw [e, (summable_lazyPow_mul_any k w g).tsum_add (hs.summable.mul_left c), tsum_mul_left,
    hs.tsum_eq, mul_one]

theorem applyPow_const_sub (g : Vertex d → ℝ) (c : ℝ) (k : ℕ) (w : Vertex d) :
    applyPow ω k (fun y => c - g y) w = c - applyPow ω k g w := by
  have h := applyPow_add_const (ω := ω) (fun y => -g y) c k w
  have e1 : (fun y => -g y + c) = fun y => c - g y := funext fun y => by ring
  rw [e1] at h
  rw [h]
  unfold applyPow
  have e2 : (fun y => lazyPow (openGraph ω) (2 * d) k w y * -g y) =
      fun y => -(lazyPow (openGraph ω) (2 * d) k w y * g y) := funext fun y => by ring
  rw [e2, tsum_neg]
  ring

theorem applyPow_nonneg {g : Vertex d → ℝ} (h : ∀ y, 0 ≤ g y) (k : ℕ) (w : Vertex d) :
    0 ≤ applyPow ω k g w :=
  tsum_nonneg fun y => mul_nonneg
    (lazyPow_mem_Icc two_mul_dim_pos (openGraph_degree_le_two_mul ω) k w y).1 (h y)

/-! ### The discrete mean displacement -/

/-- `E^z |X_k - z|` for the lazy walk. -/
noncomputable def discMean (ω : Configuration d) (z : Vertex d) (k : ℕ) : ℝ :=
  applyPow ω k (fun y => latticeDist z y) z

theorem discMean_nonneg (z : Vertex d) (k : ℕ) : 0 ≤ discMean ω z k :=
  applyPow_nonneg (fun y => latticeDist_nonneg z y) k z

omit [NeZero d] in
theorem latticeDist_sub_le_of_mem {z u v : Vertex d} (hu : u ∈ (openGraph ω).neighborFinset v) :
    |latticeDist z u - latticeDist z v| ≤ 1 := by
  have h1 := latticeDist_triangle' u v z
  have h2 := latticeDist_triangle' v u z
  have h3 := latticeDist_le_one_of_mem_neighborFinset (ω := ω) hu
  have h4 := latticeDist_comm u v
  rw [latticeDist_comm z u, latticeDist_comm z v]
  rw [abs_le]
  constructor <;> linarith

theorem abs_lazyStep_latticeDist_sub_le (z v : Vertex d) :
    |lazyStep ω (fun y => latticeDist z y) v - latticeDist z v| ≤ 1 := by
  unfold lazyStep
  have hD : (0 : ℝ) < ((2 * d : ℕ) : ℝ) := by exact_mod_cast two_mul_dim_pos
  have e : (1 - ((openGraph ω).degree v : ℝ) / ((2 * d : ℕ) : ℝ)) * latticeDist z v +
      1 / ((2 * d : ℕ) : ℝ) * ∑ u ∈ (openGraph ω).neighborFinset v, latticeDist z u -
        latticeDist z v =
      1 / ((2 * d : ℕ) : ℝ) *
        ∑ u ∈ (openGraph ω).neighborFinset v, (latticeDist z u - latticeDist z v) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, (openGraph ω).card_neighborFinset_eq_degree,
      nsmul_eq_mul]
    field_simp
    ring
  rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / ((2 * d : ℕ) : ℝ))]
  have h1 : |∑ u ∈ (openGraph ω).neighborFinset v, (latticeDist z u - latticeDist z v)| ≤
      ∑ _u ∈ (openGraph ω).neighborFinset v, (1 : ℝ) :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun u hu => latticeDist_sub_le_of_mem hu)
  rw [Finset.sum_const, (openGraph ω).card_neighborFinset_eq_degree, nsmul_eq_mul, mul_one] at h1
  have h2 : ((openGraph ω).degree v : ℝ) ≤ ((2 * d : ℕ) : ℝ) := by
    exact_mod_cast openGraph_degree_le_two_mul ω v
  rw [one_div_mul_eq_div, div_le_one hD]
  linarith

theorem discMean_succ_le (z : Vertex d) (k : ℕ) : discMean ω z (k + 1) ≤ discMean ω z k + 1 := by
  unfold discMean
  rw [← applyPow_lazyStep, ← applyPow_add_const]
  exact applyPow_mono (fun y => by
    have := abs_lazyStep_latticeDist_sub_le (ω := ω) z y
    rw [abs_le] at this
    linarith) k z

theorem le_discMean_succ (z : Vertex d) (k : ℕ) : discMean ω z k ≤ discMean ω z (k + 1) + 1 := by
  unfold discMean
  rw [← applyPow_lazyStep, ← applyPow_add_const]
  exact applyPow_mono (fun y => by
    have := abs_lazyStep_latticeDist_sub_le (ω := ω) z y
    rw [abs_le] at this
    linarith) k z

omit [NeZero d] in
theorem discMean_zero (z : Vertex d) : discMean ω z 0 = 0 := by
  rw [discMean, applyPow_zero]
  simp [latticeDist]

theorem discMean_le_add_abs (z : Vertex d) (k n : ℕ) :
    discMean ω z k ≤ discMean ω z n + |(n : ℝ) - k| := by
  rcases le_total n k with hnk | hkn
  · have h : ∀ j : ℕ, discMean ω z (n + j) ≤ discMean ω z n + j := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have := discMean_succ_le (ω := ω) z (n + j)
        rw [← add_assoc] at *
        push_cast
        linarith
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnk
    refine (h j).trans ?_
    push_cast
    rw [show (n : ℝ) - (n + j) = -j by ring, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
  · have h : ∀ j : ℕ, discMean ω z k ≤ discMean ω z (k + j) + j := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have := le_discMean_succ (ω := ω) z (k + j)
        rw [← add_assoc]
        push_cast
        linarith
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkn
    refine (h j).trans ?_
    push_cast
    rw [show (k : ℝ) + j - k = j by ring, abs_of_nonneg (Nat.cast_nonneg _)]

theorem discMean_le_self (z : Vertex d) (k : ℕ) : discMean ω z k ≤ k := by
  have := discMean_le_add_abs (ω := ω) z k 0
  rw [discMean_zero] at this
  simpa using this

/-- **Tonelli**: `M(z, t) = Σ_n Pois_{4t}(n) E^z |X_n - z|`. -/
theorem meanDist_eq_tsum {t : ℝ} (ht : 0 ≤ t) (z : Vertex d) :
    meanDist ω z t = ∑' n, poissonWeight (2 * d) t n * discMean ω z n := by
  have hdeg := openGraph_degree_le_two_mul ω
  have hsumR : Summable fun n => poissonWeight (2 * d) t n * discMean ω z n := by
    refine ((hasSum_poissonWeight_mul_real_pow (2 * d) t 2).summable).of_nonneg_of_le
      (fun n => mul_nonneg (poissonWeight_nonneg ht n) (discMean_nonneg z n)) fun n => ?_
    refine mul_le_mul_of_nonneg_left ((discMean_le_self z n).trans ?_) (poissonWeight_nonneg ht n)
    exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  have hsumL := summable_latticeDist_mul_bondHeat (ω := ω) ht z
  have h0L : ∀ y, 0 ≤ latticeDist z y * bondHeat ω t z y :=
    fun y => mul_nonneg (latticeDist_nonneg z y) (bondHeat_nonneg ω ht z y)
  have h0R : ∀ n, 0 ≤ poissonWeight (2 * d) t n * discMean ω z n :=
    fun n => mul_nonneg (poissonWeight_nonneg ht n) (discMean_nonneg z n)
  refine (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg h0L) (tsum_nonneg h0R)).1 ?_
  rw [ENNReal.ofReal_tsum_of_nonneg h0L hsumL, ENNReal.ofReal_tsum_of_nonneg h0R hsumR]
  have hL : ∀ y, ENNReal.ofReal (latticeDist z y * bondHeat ω t z y) =
      ∑' n, ENNReal.ofReal (poissonWeight (2 * d) t n) *
        (ENNReal.ofReal (lazyPow (openGraph ω) (2 * d) n z y) * ENNReal.ofReal (latticeDist z y)) := by
    intro y
    rw [ENNReal.ofReal_mul (latticeDist_nonneg z y), mul_comm, bondHeat,
      ofReal_vsrwHeat two_mul_dim_pos hdeg ht, ← ENNReal.tsum_mul_right]
    exact tsum_congr fun n => by ring
  have hR : ∀ n, ENNReal.ofReal (poissonWeight (2 * d) t n * discMean ω z n) =
      ENNReal.ofReal (poissonWeight (2 * d) t n) *
        ∑' y, (ENNReal.ofReal (lazyPow (openGraph ω) (2 * d) n z y) * ENNReal.ofReal (latticeDist z y)) := by
    intro n
    rw [ENNReal.ofReal_mul (poissonWeight_nonneg ht n)]
    congr 1
    rw [discMean, applyPow, ENNReal.ofReal_tsum_of_nonneg (fun y => mul_nonneg
      (lazyPow_mem_Icc two_mul_dim_pos hdeg n z y).1 (latticeDist_nonneg z y))
      (summable_lazyPow_mul_any n z _)]
    exact tsum_congr fun y => ENNReal.ofReal_mul (lazyPow_mem_Icc two_mul_dim_pos hdeg n z y).1
  simp_rw [hL, hR, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_comm

omit [NeZero d] in
/-- `Σ_n Pois_λ(n) |n - λ| ≤ 6 √λ` for `λ = 2dt ≥ 1`. -/
theorem tsum_poissonWeight_mul_abs_le {t : ℝ} (ht : 1 ≤ 2 * d * t) :
    Summable (fun n => poissonWeight (2 * d) t n * |(n : ℝ) - 2 * d * t|) ∧
      ∑' n, poissonWeight (2 * d) t n * |(n : ℝ) - 2 * d * t| ≤ 6 * Real.sqrt (2 * d * t) := by
  set l := 2 * d * t with hl
  have ht0 : 0 ≤ t := by nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hl0 : 0 < l := by linarith
  set θ := 1 / Real.sqrt l with hθ
  have hsq : 0 < Real.sqrt l := Real.sqrt_pos.2 hl0
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one hsq]
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt ht
  have hθl : l * θ ^ 2 = 1 := by
    rw [hθ, div_pow, Real.sq_sqrt hl0.le]
    field_simp
  -- the exponential moments
  have hexp : ∀ u : ℝ, |u| ≤ 1 → HasSum (fun n => poissonWeight (2 * d) t n * Real.exp (u * n))
      (Real.exp (l * (Real.exp u - 1))) := by
    intro u _
    have h := hasSum_poissonWeight_mul_real_pow (2 * d) t (Real.exp u)
    have e : (fun n => poissonWeight (2 * d) t n * Real.exp u ^ n) =
        fun n => poissonWeight (2 * d) t n * Real.exp (u * n) := by
      funext n
      rw [← Real.exp_nat_mul, mul_comm (n : ℝ) u]
    rw [e] at h
    have e2 : ((2 * d : ℕ) : ℝ) * t * (Real.exp u - 1) = l * (Real.exp u - 1) := by
      rw [hl]; push_cast; ring
    rw [e2] at h
    exact h
  have hp := hexp θ (by rw [abs_of_pos hθ0]; exact hθ1)
  have hm := hexp (-θ) (by rw [abs_neg, abs_of_pos hθ0]; exact hθ1)
  have hpt : ∀ n : ℕ, poissonWeight (2 * d) t n * |(n : ℝ) - l| ≤
      (Real.exp (-θ * l) * (poissonWeight (2 * d) t n * Real.exp (θ * n)) +
        Real.exp (θ * l) * (poissonWeight (2 * d) t n * Real.exp (-θ * n))) / θ := by
    intro n
    have hw := poissonWeight_nonneg (D := 2 * d) ht0 n
    have key : |(n : ℝ) - l| ≤ (Real.exp (θ * (n - l)) + Real.exp (-θ * (n - l))) / θ := by
      rw [le_div_iff₀ hθ0]
      rcases le_total 0 ((n : ℝ) - l) with h | h
      · rw [abs_of_nonneg h]
        have := Real.add_one_le_exp (θ * (n - l))
        have := Real.exp_pos (-θ * (n - l))
        nlinarith
      · rw [abs_of_nonpos h]
        have := Real.add_one_le_exp (-θ * (n - l))
        have := Real.exp_pos (θ * (n - l))
        nlinarith
    have e1 : Real.exp (θ * (n - l)) = Real.exp (-θ * l) * Real.exp (θ * n) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-θ * (n - l)) = Real.exp (θ * l) * Real.exp (-θ * n) := by
      rw [← Real.exp_add]; ring_nf
    rw [e1, e2] at key
    calc poissonWeight (2 * d) t n * |(n : ℝ) - l|
        ≤ poissonWeight (2 * d) t n * ((Real.exp (-θ * l) * Real.exp (θ * n) +
            Real.exp (θ * l) * Real.exp (-θ * n)) / θ) := mul_le_mul_of_nonneg_left key hw
      _ = _ := by ring
  have hsumB := ((hp.summable.mul_left (Real.exp (-θ * l))).add
    (hm.summable.mul_left (Real.exp (θ * l)))).div_const θ
  have hsum : Summable fun n => poissonWeight (2 * d) t n * |(n : ℝ) - l| :=
    hsumB.of_nonneg_of_le (fun n => mul_nonneg (poissonWeight_nonneg ht0 n) (abs_nonneg _)) hpt
  refine ⟨hsum, ?_⟩
  have hle := Summable.tsum_le_tsum hpt hsum hsumB
  rw [tsum_div_const, (hp.summable.mul_left _).tsum_add (hm.summable.mul_left _), tsum_mul_left,
    tsum_mul_left, hp.tsum_eq, hm.tsum_eq] at hle
  -- `e^{-θl} e^{l(e^θ - 1)} ≤ e^{lθ²} = e`, and the same for `-θ`
  have hb1 : Real.exp (-θ * l) * Real.exp (l * (Real.exp θ - 1)) ≤ Real.exp 1 := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have h := Real.abs_exp_sub_one_sub_id_le (by rw [abs_of_pos hθ0]; exact hθ1 : |θ| ≤ 1)
    rw [abs_le] at h
    nlinarith
  have hb2 : Real.exp (θ * l) * Real.exp (l * (Real.exp (-θ) - 1)) ≤ Real.exp 1 := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have h := Real.abs_exp_sub_one_sub_id_le
      (by rw [abs_neg, abs_of_pos hθ0]; exact hθ1 : |-θ| ≤ 1)
    rw [abs_le] at h
    nlinarith
  have he3 : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have hfin : (Real.exp (-θ * l) * Real.exp (l * (Real.exp θ - 1)) +
      Real.exp (θ * l) * Real.exp (l * (Real.exp (-θ) - 1))) / θ ≤ 6 * Real.sqrt l := by
    rw [div_le_iff₀ hθ0, hθ]
    have : Real.sqrt l * (1 / Real.sqrt l) = 1 := by field_simp
    nlinarith
  exact hle.trans hfin

/-- `E^z |X_k - z| ≤ M(z, k/(2d)) + 6 √k` for `k ≥ 1`. -/
theorem discMean_le_meanDist_add (z : Vertex d) {k : ℕ} (hk : 1 ≤ k) :
    discMean ω z k ≤ meanDist ω z (k / (2 * d)) + 6 * Real.sqrt k := by
  set t : ℝ := k / (2 * d) with ht
  have hd0 : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have ht4 : 2 * d * t = k := by rw [ht]; field_simp
  have ht0 : 0 ≤ t := by positivity
  have hk1 : (1 : ℝ) ≤ 2 * d * t := by rw [ht4]; exact_mod_cast hk
  obtain ⟨hsA, hA⟩ := tsum_poissonWeight_mul_abs_le hk1
  have hs := hasSum_poissonWeight (D := 2 * d) t
  have hsumR : Summable fun n => poissonWeight (2 * d) t n * discMean ω z n := by
    refine ((hasSum_poissonWeight_mul_real_pow (2 * d) t 2).summable).of_nonneg_of_le
      (fun n => mul_nonneg (poissonWeight_nonneg ht0 n) (discMean_nonneg z n)) fun n => ?_
    refine mul_le_mul_of_nonneg_left ((discMean_le_self z n).trans ?_) (poissonWeight_nonneg ht0 n)
    exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  have hpt : ∀ n, poissonWeight (2 * d) t n * discMean ω z k ≤
      poissonWeight (2 * d) t n * discMean ω z n + poissonWeight (2 * d) t n * |(n : ℝ) - 2 * d * t| := by
    intro n
    rw [← mul_add, ht4]
    exact mul_le_mul_of_nonneg_left (discMean_le_add_abs z k n) (poissonWeight_nonneg ht0 n)
  have hle := Summable.tsum_le_tsum hpt (hs.summable.mul_right _) (hsumR.add hsA)
  rw [tsum_mul_right, hs.tsum_eq, one_mul, hsumR.tsum_add hsA, ← meanDist_eq_tsum ht0] at hle
  have hsq : Real.sqrt (2 * d * t) = Real.sqrt k := by rw [ht4]
  rw [hsq] at hA
  linarith

/-! ### Lemma 3.5 -/

/-- `E^z |X_k - x| ≥ |z - x| - E^z |X_k - z|`. -/
theorem applyPow_latticeDist_ge (x z : Vertex d) (k : ℕ) :
    latticeDist x z - discMean ω z k ≤ applyPow ω k (fun y => latticeDist x y) z := by
  unfold discMean
  rw [← applyPow_const_sub]
  refine applyPow_mono (fun y => ?_) k z
  have := latticeDist_triangle' x y z
  have h2 := latticeDist_comm y x
  have h3 := latticeDist_comm z y
  linarith

/-- **Barlow 2004, Lemma 3.5** (discrete form): if `E^z |X_k - z| ≤ M̄` for `n ≤ k ≤ 2n` at the
points with `|z - x| < r + 1`, then `(r - M̄) P^x(σ(x, r) ≤ n) ≤ E^x |X_{2n} - x|`. -/
theorem exitProb_clBall_le {K : OpenComponent ω} {x : Vertex d} (hx : x ∈ K.supp) {r Mb : ℝ}
    {n : ℕ} (hr0 : 0 < r)
    (hMb : ∀ z ∈ K.supp, latticeDist z x < r + 1 → ∀ k, n ≤ k → k ≤ 2 * n → discMean ω z k ≤ Mb) :
    (r - Mb) * exitProb ω (clBall K x r) n x ≤ discMean ω x (2 * n) := by
  have key := mul_exitProb_le (ω := ω) (A := clBall K x r) (n := n) (c := r - Mb)
    (h := fun j w => applyPow ω (2 * n - j) (fun y => latticeDist x y) w)
    (fun j hj w _ => by
      have e : 2 * n - j = (2 * n - (j + 1)) + 1 := by omega
      show lazyStep ω (applyPow ω (2 * n - (j + 1)) (fun y => latticeDist x y)) w ≤
        applyPow ω (2 * n - j) (fun y => latticeDist x y) w
      rw [e, applyPow_succ])
    (fun j _ w _ => applyPow_nonneg (fun y => latticeDist_nonneg x y) _ w)
    (fun j hj z hz ⟨v, hv, hvz⟩ => by
      show r - Mb ≤ applyPow ω (2 * n - j) (fun y => latticeDist x y) z
      rw [mem_clBall] at hv
      have hzK : z ∈ K.supp := mem_supp_of_adj hv.1 hvz
      have hzx : latticeDist z x < r + 1 := by
        have h1 := latticeDist_triangle' z v x
        have h2 := latticeDist_le_one_of_mem_neighborFinset (ω := ω)
          (((openGraph ω).mem_neighborFinset v z).2 hvz)
        linarith [hv.2]
      have hge := applyPow_latticeDist_ge (ω := ω) x z (2 * n - j)
      have hb := hMb z hzK hzx (2 * n - j) (by omega) (by omega)
      have hzr : r ≤ latticeDist x z := by
        rw [mem_clBall] at hz
        have : ¬ latticeDist z x < r := fun h => hz ⟨hzK, h⟩
        rw [latticeDist_comm]
        exact le_of_not_gt this
      linarith)
    n le_rfl x (Or.inl (by rw [mem_clBall]; simp [latticeDist]; exact ⟨hx, hr0⟩))
  rw [Nat.sub_self] at key
  simpa [discMean] using key

/-! ### Lemma 3.6 and Proposition 3.7 -/

omit [NeZero d] in
theorem clBall_zero_eq (K : OpenComponent ω) (x : Vertex d) : clBall K x 0 = ∅ := by
  ext w
  simp [mem_clBall, not_lt.2 (latticeDist_nonneg w x)]

/-- **Submultiplicativity along nested balls**: if `E^z[s^{σ(z, r)}; σ ≤ N] ≤ Λ` at every centre `z`
within `D` of `x₀`, then `E^x[s^{σ(x, m(r+1))}; σ ≤ N] ≤ Λ^m` when `|x - x₀| + m(r + 1) ≤ D`. -/
theorem exitGen_clBall_le_pow {K : OpenComponent ω} {x0 : Vertex d} {D r Λ s : ℝ} {N : ℕ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hΛ : 0 ≤ Λ) (hr : 0 < r)
    (hone : ∀ z ∈ K.supp, latticeDist z x0 ≤ D → exitGen ω (clBall K z r) s N z ≤ Λ) :
    ∀ m : ℕ, ∀ x ∈ K.supp, latticeDist x x0 + m * (r + 1) ≤ D →
      exitGen ω (clBall K x (m * (r + 1))) s N x ≤ Λ ^ m := by
  intro m
  induction m with
  | zero =>
    intro x _ _
    simp only [Nat.cast_zero, zero_mul, pow_zero]
    rw [clBall_zero_eq, exitGen_of_notMem (Set.notMem_empty x)]
  | succ m ih =>
    intro x hxK hx
    set A := clBall K x (((m + 1 : ℕ) : ℝ) * (r + 1)) with hA
    set B := clBall K x r with hB
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hBA : B ⊆ A := by
      intro w hw
      rw [hB, mem_clBall] at hw
      rw [hA, mem_clBall]
      refine ⟨hw.1, ?_⟩
      push_cast
      nlinarith [hw.2]
    have hbd : ∀ z ∉ B, (∃ v ∈ B, (openGraph ω).Adj v z) → ∀ m' ≤ N,
        exitGen ω A s m' z ≤ Λ ^ m := by
      intro z _ ⟨v, hv, hvz⟩ m' hm'
      rw [hB, mem_clBall] at hv
      have hzK : z ∈ K.supp := mem_supp_of_adj hv.1 hvz
      have hzx : latticeDist z x < r + 1 := by
        have h1 := latticeDist_triangle' z v x
        have h2 := latticeDist_le_one_of_mem_neighborFinset (ω := ω)
          (((openGraph ω).mem_neighborFinset v z).2 hvz)
        linarith [hv.2]
      have hsub : clBall K z (m * (r + 1)) ⊆ A := by
        intro w hw
        rw [mem_clBall] at hw
        rw [hA, mem_clBall]
        refine ⟨hw.1, ?_⟩
        have := latticeDist_triangle' w z x
        rw [latticeDist_comm z w] at this
        push_cast
        nlinarith [hw.2]
      have hzD : latticeDist z x0 + m * (r + 1) ≤ D := by
        have := latticeDist_triangle' z x x0
        rw [latticeDist_comm x z] at this
        push_cast at hx
        nlinarith
      calc exitGen ω A s m' z ≤ exitGen ω A s N z := exitGen_mono hs0 hm' z
        _ ≤ exitGen ω (clBall K z (m * (r + 1))) s N z := exitGen_anti hsub hs0 hs1 N z
        _ ≤ Λ ^ m := ih z hzK hzD
    have hxD : latticeDist x x0 ≤ D := by
      have : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * (r + 1) := by positivity
      linarith
    have h := exitGen_le_mul_of_subset hBA hs0 hbd N le_rfl x
      (Or.inl (by rw [hB, mem_clBall]; simp [latticeDist]; exact ⟨hxK, hr⟩))
    calc exitGen ω A s N x ≤ Λ ^ m * exitGen ω B s N x := h
      _ ≤ Λ ^ m * Λ := mul_le_mul_of_nonneg_left (hone x hxK hxD) (pow_nonneg hΛ m)
      _ = Λ ^ (m + 1) := (pow_succ Λ m).symm

/-- **Barlow 2004, Lemma 3.6 and Proposition 3.7** (discrete form): if
`P^z(σ(z, r) ≤ k) ≤ 1/2 + a k` for `k ≤ N` at every centre `z` within `D` of `x₀`, with
`0 < a ≤ 1/8`, then `P^x(σ(x, m(r + 1)) ≤ N) ≤ e^{8aN} (3/4)^m` when `|x - x₀| + m(r + 1) ≤ D`. -/
theorem exitProb_clBall_le_exp {K : OpenComponent ω} {x0 x : Vertex d} {D r a : ℝ} {N m : ℕ}
    (hr : 0 < r) (ha0 : 0 < a) (ha : a ≤ 1 / 8)
    (hone : ∀ z ∈ K.supp, latticeDist z x0 ≤ D → ∀ k ≤ N,
      exitProb ω (clBall K z r) k z ≤ 1 / 2 + a * k)
    (hxK : x ∈ K.supp) (hx : latticeDist x x0 + m * (r + 1) ≤ D) :
    exitProb ω (clBall K x (m * (r + 1))) N x ≤ Real.exp (8 * a * N) * (3 / 4) ^ m := by
  set θ := 4 * a with hθ
  set s := 1 - θ with hs
  have hθ0 : 0 < θ := by positivity
  have hθ2 : θ ≤ 1 / 2 := by linarith
  have hs0 : 0 ≤ s := by linarith
  have hs1 : s < 1 := by linarith
  have hspos : 0 < s := by linarith
  have hΛ : a * (s / (1 - s)) ≤ 1 / 4 := by
    rw [hs, sub_sub_cancel, hθ]
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have hone' : ∀ z ∈ K.supp, latticeDist z x0 ≤ D → exitGen ω (clBall K z r) s N z ≤ 3 / 4 := by
    intro z hzK hz
    have := exitGen_le_of_exitProb_le (ω := ω) (clBall K z r) hs0 hs1 ha0.le (hone z hzK hz)
    linarith
  have hit := exitGen_clBall_le_pow (ω := ω) hs0 hs1.le (by norm_num) hr hone' m x hxK hx
  have hlow := pow_mul_exitProb_le_exitGen (ω := ω) (clBall K x (m * (r + 1))) hs0 hs1.le N x
  have hsN : 0 < s ^ N := pow_pos hspos N
  have hinv : (s ^ N)⁻¹ ≤ Real.exp (8 * a * N) := by
    have h1 : s⁻¹ ≤ 1 + 2 * θ := by
      rw [inv_le_iff_one_le_mul₀ hspos]
      nlinarith
    have h2 : 1 + 2 * θ ≤ Real.exp (2 * θ) := by linarith [Real.add_one_le_exp (2 * θ)]
    calc (s ^ N)⁻¹ = (s⁻¹) ^ N := (inv_pow s N).symm
      _ ≤ Real.exp (2 * θ) ^ N := pow_le_pow_left₀ (inv_nonneg.2 hs0) (h1.trans h2) N
      _ = Real.exp (8 * a * N) := by
          rw [← Real.exp_nat_mul, hθ]
          ring_nf
  calc exitProb ω (clBall K x (m * (r + 1))) N x
      = (s ^ N)⁻¹ * (s ^ N * exitProb ω (clBall K x (m * (r + 1))) N x) := by
        field_simp
    _ ≤ (s ^ N)⁻¹ * (3 / 4) ^ m :=
        mul_le_mul_of_nonneg_left (hlow.trans hit) (inv_nonneg.2 hsN.le)
    _ ≤ Real.exp (8 * a * N) * (3 / 4) ^ m :=
        mul_le_mul_of_nonneg_right hinv (by positivity)

end Rigidity.BarlowLattice
