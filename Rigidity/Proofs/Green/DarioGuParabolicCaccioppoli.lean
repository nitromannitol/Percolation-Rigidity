import Rigidity.Proofs.Green.DarioGuParabolicInputs
import LatticeProb.Network.Caccioppoli
import PercolationClusterHomogenization.Proofs.Cluster.Caccioppoli

/-!
# The parabolic Caccioppoli inequality on the planar cluster

**Dario–Gu, Proposition 2.9** (lines 1006-1019 of the source): *There exists a finite positive
constant `C` such that, for each point `y ∈ ℤ^d`, each radius `R ≥ 1` and each function
`u : I_R × (𝒞_∞ ∩ B_R(y)) → ℝ` which is `a`-caloric, i.e., which is a solution of
`∂_t u - ∇·a∇u = 0` in `I_R × (𝒞_∞ ∩ B_R(y))`, one has
`‖∇u‖_{L²(I_{R/2} × (𝒞_∞ ∩ B_{R/2}(y)))} ≤ (C/R) ‖u - (u)_{I_R × (𝒞_∞ ∩ B_R(y))}‖_{L²(I_R × (𝒞_∞ ∩ B_R(y)))}`.*
The source omits the proof ("the proof follows the standard arguments of the Caccioppoli
inequality; the fact that the function `u` is defined on the infinite cluster does not affect the
proof and we omit the details").

Here it is proved for unit conductances on any open component of a planar configuration, with the
gradient over the open edges from `𝒞_∞ ∩ B_{R/2}(y)` into `𝒞_∞ ∩ B_R(y)` (for `R > 2` these are
all the open edges at these vertices). The proof is the standard one:

* `two_mul_sum_restrict`: summation by parts for the Laplacian restricted to a finite set;
* `energy_le_neg_deriv_add`: with `E(t) = Σ η² (u - m)²`, the weighted energy
  `D(t) = Σ_x η(x)² Σ_{z ∼ x} (u(z) - u(x))²` is at most `-2 E'(t) + 32 ℓ² Σ (u - m)²` when `η` varies
  by at most `ℓ` along edges (the pointwise inequality of the elliptic Caccioppoli inequality);
* `parabolic_caccioppoli_of_cutoff`: integration against the time cutoff `(t - a)/(b - a)`;
* `darioGuCaccioppoliTwo_holds`: the cutoff `η = 1` on `B_{R/2}` vanishing at distance `R - 2`.
-/

open MeasureTheory Finset LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open scoped Classical

namespace Rigidity.Green

variable {ω : Configuration 2}

/-- `|∇v|_V(x) = Σ_{z ∈ V, z ∼ x} |v(z) - v(x)|`, over the open edges from `x` into `V`. -/
noncomputable def clusterGradAt (ω : Configuration 2) (V : Finset (Vertex 2))
    (v : Vertex 2 → ℝ) (x : Vertex 2) : ℝ :=
  ∑ z ∈ V, if (openGraph ω).Adj x z then |v z - v x| else 0

/-- The mean `(u)_{I_R × (𝒞_∞ ∩ B_R(y))}`. -/
noncomputable def parMean {ω : Configuration 2} (K : OpenComponent ω) (y : Vertex 2) (R : ℝ)
    (u : ℝ → Vertex 2 → ℝ) : ℝ :=
  (R ^ 2 * (clusterBall K y R).card)⁻¹ * ∫ t in Set.Ioc (-R ^ 2) 0, ∑ x ∈ clusterBall K y R, u t x

/-- **Dario–Gu, Proposition 2.9** (parabolic Caccioppoli inequality), in dimension two, for every
open component, with the gradient over the open edges from `𝒞_∞ ∩ B_{R/2}(y)` into
`𝒞_∞ ∩ B_R(y)`. -/
def DarioGuCaccioppoliTwo : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (ω : Configuration 2) (K : OpenComponent ω) (y : Vertex 2) (R : ℝ), 1 ≤ R →
    ∀ u : ℝ → Vertex 2 → ℝ, IsClusterCaloric ω (clusterBall K y R) (-R ^ 2) 0 u →
      Real.sqrt (∫ t in Set.Ioc (-(R / 2) ^ 2) 0, ∑ x ∈ clusterBall K y (R / 2),
          clusterGradAt ω (clusterBall K y R) (u t) x ^ 2) ≤
        C / R * Real.sqrt (∫ t in Set.Ioc (-R ^ 2) 0, ∑ x ∈ clusterBall K y R,
          (u t x - parMean K y R u) ^ 2)

/-! ### Summation by parts and the degree bound -/

/-- Summation by parts for the Laplacian restricted to `V`. -/
theorem two_mul_sum_restrict (V : Finset (Vertex 2)) (f v : Vertex 2 → ℝ) :
    2 * ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then f x * (v z - v x) else 0) =
      -∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then (f z - f x) * (v z - v x) else 0) := by
  have hswap : ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then f x * (v z - v x) else 0) =
      ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then f z * (v x - v z) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => ?_
    have e : (openGraph ω).Adj z x ↔ (openGraph ω).Adj x z := (openGraph ω).adj_comm z x
    simp only [e]
  rw [two_mul]
  nth_rewrite 2 [hswap]
  rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  split_ifs <;> ring

/-- Symmetry of the double sum over the open edges inside `V`. -/
theorem sum_restrict_swap (V : Finset (Vertex 2)) (g : Vertex 2 → ℝ) :
    ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then g z else 0) =
      ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then g x else 0) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => ?_
  have e : (openGraph ω).Adj z x ↔ (openGraph ω).Adj x z := (openGraph ω).adj_comm z x
  simp only [e]

/-- Each vertex has at most four open neighbours in `V`. -/
theorem card_filter_adj_le_four (V : Finset (Vertex 2)) (x : Vertex 2) :
    ((V.filter fun z => (openGraph ω).Adj x z).card : ℝ) ≤ 4 := by
  have h2 : (V.filter fun z => (openGraph ω).Adj x z).card ≤ 4 := by
    refine (Finset.card_le_card fun z hz => ?_).trans
      (((openGraph ω).card_neighborFinset_eq_degree x).le.trans (openGraph_degree_le_four ω x))
    rw [Finset.mem_filter] at hz
    exact (SimpleGraph.mem_neighborFinset _ _ _).2 hz.2
  exact_mod_cast h2

theorem sum_restrict_le_four (V : Finset (Vertex 2)) {g : Vertex 2 → ℝ} (hg : ∀ x, 0 ≤ g x) :
    ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then g x else 0) ≤ 4 * ∑ x ∈ V, g x := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  have h1 : ∑ z ∈ V, (if (openGraph ω).Adj x z then g x else 0) =
      (V.filter fun z => (openGraph ω).Adj x z).card * g x := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [h1]
  have h3 := card_filter_adj_le_four (ω := ω) V x
  exact mul_le_mul_of_nonneg_right h3 (hg x)

/-- At a vertex whose open neighbours lie in `V`, the Laplacian is the restricted one. -/
theorem openLaplacian_eq_restrict {V : Finset (Vertex 2)} {x : Vertex 2}
    (hnb : ∀ z, (openGraph ω).Adj x z → z ∈ V) (v : Vertex 2 → ℝ) :
    openLaplacian ω v x = ∑ z ∈ V, if (openGraph ω).Adj x z then v z - v x else 0 := by
  rw [← Finset.sum_filter]
  unfold openLaplacian
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext z
  rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
  exact ⟨fun h => ⟨hnb z h, h⟩, fun h => h.2⟩

/-! ### The energy inequality at a fixed time -/

/-- The restricted Laplacian `Σ_{z ∈ V, z ∼ x} (v(z) - v(x))`. -/
noncomputable def restrictLap (ω : Configuration 2) (V : Finset (Vertex 2)) (v : Vertex 2 → ℝ)
    (x : Vertex 2) : ℝ :=
  ∑ z ∈ V, if (openGraph ω).Adj x z then v z - v x else 0

/-- **Energy inequality.** `Σ_x η² Σ_{z ∼ x} (v z - v x)² ≤ -4 Σ_x η² v L v + 32 ℓ² Σ v²`. -/
theorem energy_le_neg_deriv_add (V : Finset (Vertex 2)) (v η : Vertex 2 → ℝ) {ℓ : ℝ}
    (hηlip : ∀ x z, (openGraph ω).Adj x z → |η x - η z| ≤ ℓ) :
    ∑ x ∈ V, η x ^ 2 * ∑ z ∈ V, (if (openGraph ω).Adj x z then (v z - v x) ^ 2 else 0) ≤
      -(4 * ∑ x ∈ V, η x ^ 2 * v x * restrictLap ω V v x) + 32 * ℓ ^ 2 * ∑ x ∈ V, v x ^ 2 := by
  set f : Vertex 2 → ℝ := fun x => η x ^ 2 * v x with hf
  -- the pointwise inequality
  have hpt : ∀ x ∈ V, η x ^ 2 * ∑ z ∈ V, (if (openGraph ω).Adj x z then (v z - v x) ^ 2 else 0) ≤
      ∑ z ∈ V, (if (openGraph ω).Adj x z then (2 * ((f z - f x) * (v z - v x)) +
        4 * ((v x ^ 2 + v z ^ 2) * ℓ ^ 2)) else 0) := by
    intro x _
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun z _ => ?_
    split_ifs with hxz
    · have h1 := LatticeProb.Network.caccioppoli_pointwise (v x) (v z) (η x) (η z)
      have h2 : (η x - η z) ^ 2 ≤ ℓ ^ 2 := by
        have := hηlip x z hxz
        have h0 : 0 ≤ ℓ := (abs_nonneg _).trans this
        calc (η x - η z) ^ 2 = |η x - η z| ^ 2 := (sq_abs _).symm
          _ ≤ ℓ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      have h3 : 0 ≤ v x ^ 2 + v z ^ 2 := by positivity
      have h4 := mul_le_mul_of_nonneg_left h2 h3
      simp only [hf]
      nlinarith
    · simp
  have hsum := Finset.sum_le_sum hpt
  -- the two terms
  have hA : ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then (f z - f x) * (v z - v x) else 0) =
      -(2 * ∑ x ∈ V, η x ^ 2 * v x * restrictLap ω V v x) := by
    have := two_mul_sum_restrict (ω := ω) V f v
    have e : ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then f x * (v z - v x) else 0) =
        ∑ x ∈ V, η x ^ 2 * v x * restrictLap ω V v x := by
      refine Finset.sum_congr rfl fun x _ => ?_
      unfold restrictLap
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      split_ifs <;> simp [hf]
    rw [e] at this
    linarith
  have hB : ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then (v x ^ 2 + v z ^ 2) else 0) ≤
      8 * ∑ x ∈ V, v x ^ 2 := by
    have e1 : ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then (v x ^ 2 + v z ^ 2) else 0) =
        ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then v x ^ 2 else 0) +
          ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then v z ^ 2 else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun z _ => ?_
      split_ifs <;> ring
    rw [e1, sum_restrict_swap (ω := ω) V (fun z => v z ^ 2)]
    have := sum_restrict_le_four (ω := ω) V (g := fun x => v x ^ 2) (fun x => sq_nonneg _)
    linarith
  have hsplit : ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then (2 * ((f z - f x) * (v z - v x)) +
      4 * ((v x ^ 2 + v z ^ 2) * ℓ ^ 2)) else 0) =
      2 * ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then (f z - f x) * (v z - v x) else 0) +
        4 * ℓ ^ 2 * ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then (v x ^ 2 + v z ^ 2) else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    split_ifs <;> ring
  rw [hsplit, hA] at hsum
  have hℓ : 0 ≤ 4 * ℓ ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hB hℓ
  linarith

/-! ### Integration in time -/

theorem continuousOn_sum_restrict {V : Finset (Vertex 2)} {a b : ℝ} {g : Vertex 2 → Vertex 2 → ℝ → ℝ}
    (hg : ∀ x ∈ V, ∀ z ∈ V, ContinuousOn (g x z) (Set.Icc a b)) :
    ContinuousOn (fun t => ∑ x ∈ V, ∑ z ∈ V, if (openGraph ω).Adj x z then g x z t else 0)
      (Set.Icc a b) := by
  refine continuousOn_finsetSum _ fun x hx => continuousOn_finsetSum _ fun z hz => ?_
  by_cases h : (openGraph ω).Adj x z
  · simp only [h, if_true]
    exact hg x hx z hz
  · simp only [h, if_false]
    exact continuousOn_const

/-- **The parabolic Caccioppoli inequality with cutoffs.** For `u` caloric at the vertices of `V`
whose open neighbours lie in `V`, `η ∈ [0, 1]` vanishing off these vertices and varying by at most
`ℓ` along open edges, and the time cutoff `(t - a)/(b - a)`,
`∫_a^b (t-a)/(b-a) Σ_x η(x)² Σ_{z ∼ x} (u(t,z) - u(t,x))² dt ≤ (2/(b-a) + 32ℓ²) ∫_a^b Σ_x (u(t,x) - m)² dt`. -/
theorem parabolic_caccioppoli_of_cutoff {V : Finset (Vertex 2)} {a b : ℝ} (hab : a < b)
    {u : ℝ → Vertex 2 → ℝ} (hu : IsClusterCaloric ω V a b u) {η : Vertex 2 → ℝ} {ℓ : ℝ}
    (m : ℝ) (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1)
    (hηint : ∀ x, η x ≠ 0 → x ∈ V ∧ ∀ z, (openGraph ω).Adj x z → z ∈ V)
    (hηlip : ∀ x z, (openGraph ω).Adj x z → |η x - η z| ≤ ℓ) :
    ∫ t in a..b, (t - a) / (b - a) * ∑ x ∈ V, η x ^ 2 * ∑ z ∈ V,
        (if (openGraph ω).Adj x z then (u t z - u t x) ^ 2 else 0) ≤
      (2 / (b - a) + 32 * ℓ ^ 2) * ∫ t in a..b, ∑ x ∈ V, (u t x - m) ^ 2 := by
  have hba : 0 < b - a := by linarith
  have hℓ : 0 ≤ ℓ ^ 2 := sq_nonneg ℓ
  set D : ℝ → ℝ := fun t => ∑ x ∈ V, η x ^ 2 * ∑ z ∈ V,
    (if (openGraph ω).Adj x z then (u t z - u t x) ^ 2 else 0) with hD
  set E : ℝ → ℝ := fun t => ∑ x ∈ V, η x ^ 2 * (u t x - m) ^ 2 with hE
  set E' : ℝ → ℝ := fun t => ∑ x ∈ V, η x ^ 2 * (2 * (u t x - m) *
    restrictLap ω V (fun z => u t z - m) x) with hE'
  set S : ℝ → ℝ := fun t => ∑ x ∈ V, (u t x - m) ^ 2 with hS
  set ζ : ℝ → ℝ := fun t => (t - a) / (b - a) with hζ
  have hcu : ∀ x ∈ V, ContinuousOn (fun t => u t x) (Set.Icc a b) := hu.1
  -- continuity
  have hDc : ContinuousOn D (Set.Icc a b) := by
    refine continuousOn_finsetSum _ fun x hx => continuousOn_const.mul ?_
    refine continuousOn_finsetSum _ fun z hz => ?_
    by_cases h : (openGraph ω).Adj x z
    · simp only [h, if_true]
      exact ((hcu z hz).sub (hcu x hx)).pow 2
    · simp only [h, if_false]
      exact continuousOn_const
  have hEc : ContinuousOn E (Set.Icc a b) := continuousOn_finsetSum _ fun x hx =>
    continuousOn_const.mul (((hcu x hx).sub continuousOn_const).pow 2)
  have hSc : ContinuousOn S (Set.Icc a b) := continuousOn_finsetSum _ fun x hx =>
    ((hcu x hx).sub continuousOn_const).pow 2
  have hE'c : ContinuousOn E' (Set.Icc a b) := by
    refine continuousOn_finsetSum _ fun x hx => continuousOn_const.mul
      ((continuousOn_const.mul ((hcu x hx).sub continuousOn_const)).mul ?_)
    unfold restrictLap
    refine continuousOn_finsetSum _ fun z hz => ?_
    by_cases h : (openGraph ω).Adj x z
    · simp only [h, if_true]
      exact ((hcu z hz).sub continuousOn_const).sub ((hcu x hx).sub continuousOn_const)
    · simp only [h, if_false]
      exact continuousOn_const
  have hζc : ContinuousOn ζ (Set.Icc a b) :=
    ((continuous_id.sub continuous_const).div_const _).continuousOn
  have huIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab.le
  have hint : ∀ {F : ℝ → ℝ}, ContinuousOn F (Set.Icc a b) →
      IntervalIntegrable F volume a b := fun hF => by
    apply ContinuousOn.intervalIntegrable
    rwa [huIcc]
  -- the derivative of the energy
  have hEd : ∀ s ∈ Set.Ioo a b, HasDerivAt E (E' s) s := by
    intro s hs
    have hterm : ∀ x ∈ V, HasDerivAt (fun t => η x ^ 2 * (u t x - m) ^ 2)
        (η x ^ 2 * (2 * (u s x - m) * restrictLap ω V (fun z => u s z - m) x)) s := by
      intro x _
      by_cases hx : η x = 0
      · simp only [hx]
        simpa using hasDerivAt_const s (0 : ℝ)
      · obtain ⟨hxV, hnb⟩ := hηint x hx
        have hd := hu.2 x hxV hnb s hs
        rw [openLaplacian_eq_restrict hnb] at hd
        have hL : (∑ z ∈ V, if (openGraph ω).Adj x z then u s z - u s x else 0) =
            restrictLap ω V (fun z => u s z - m) x := by
          unfold restrictLap
          refine Finset.sum_congr rfl fun z _ => ?_
          split_ifs <;> ring
        rw [hL] at hd
        refine (((hd.sub_const m).pow 2).const_mul (η x ^ 2)).congr_deriv ?_
        norm_num
    exact HasDerivAt.fun_sum hterm
  -- the energy inequality at each time
  have hpt : ∀ t, D t ≤ -(2 * E' t) + 32 * ℓ ^ 2 * S t := by
    intro t
    have h := energy_le_neg_deriv_add (ω := ω) V (fun x => u t x - m) η hηlip
    have e1 : ∑ x ∈ V, η x ^ 2 * ∑ z ∈ V, (if (openGraph ω).Adj x z then
        ((u t z - m) - (u t x - m)) ^ 2 else 0) = D t := by
      simp only [hD]
      refine Finset.sum_congr rfl fun x _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun z _ => ?_
      split_ifs <;> ring
    have e2 : 4 * ∑ x ∈ V, η x ^ 2 * (u t x - m) * restrictLap ω V (fun z => u t z - m) x =
        2 * E' t := by
      simp only [hE', Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    rw [e1, e2] at h
    exact h
  have iD : IntervalIntegrable (fun t => ζ t * D t) volume a b := hint (hζc.mul hDc)
  have iE : IntervalIntegrable E volume a b := hint hEc
  have iS : IntervalIntegrable S volume a b := hint hSc
  have iZE : IntervalIntegrable (fun t => ζ t * E' t) volume a b := hint (hζc.mul hE'c)
  -- integration by parts in time
  have hF : ∫ t in a..b, (1 / (b - a) * E t + ζ t * E' t) = ζ b * E b - ζ a * E a := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le (hζc.mul hEc)
      (fun s hs => ?_) ((iE.const_mul (1 / (b - a))).add iZE)
    have hζd : HasDerivAt ζ (1 / (b - a)) s := by
      rw [hζ]
      simpa using ((hasDerivAt_id s).sub_const a).div_const (b - a)
    exact hζd.mul (hEd s hs)
  have hζa : ζ a = 0 := by simp [hζ]
  have hζb : ζ b = 1 := by
    simp only [hζ]
    exact div_self hba.ne'
  have hEb : 0 ≤ E b := Finset.sum_nonneg fun x _ => by positivity
  rw [hζa, hζb, intervalIntegral.integral_add (iE.const_mul (1 / (b - a))) iZE,
    intervalIntegral.integral_const_mul] at hF
  -- the bound
  have hζ0 : ∀ t ∈ Set.Icc a b, 0 ≤ ζ t := fun t ht => div_nonneg (by linarith [ht.1]) hba.le
  have hζ1 : ∀ t ∈ Set.Icc a b, ζ t ≤ 1 := fun t ht => by
    simp only [hζ]
    rw [div_le_one hba]
    linarith [ht.2]
  have hES : ∀ t, E t ≤ S t := fun t => Finset.sum_le_sum fun x _ => by
    have h1 : η x ^ 2 ≤ 1 := by nlinarith [hη0 x, hη1 x]
    have h2 : 0 ≤ (u t x - m) ^ 2 := sq_nonneg _
    nlinarith
  have hS0 : ∀ t, 0 ≤ S t := fun t => Finset.sum_nonneg fun x _ => sq_nonneg _
  have step1 : ∫ t in a..b, ζ t * D t ≤
      ∫ t in a..b, (32 * ℓ ^ 2 * S t - 2 * (ζ t * E' t)) := by
    refine intervalIntegral.integral_mono_on hab.le iD
      ((iS.const_mul (32 * ℓ ^ 2)).sub (iZE.const_mul 2)) fun t ht => ?_
    have h1 := hpt t
    have h2 := hζ0 t ht
    have h3 := hζ1 t ht
    have h4 : ζ t * D t ≤ ζ t * (-(2 * E' t) + 32 * ℓ ^ 2 * S t) :=
      mul_le_mul_of_nonneg_left h1 h2
    have h5 : ζ t * (32 * ℓ ^ 2 * S t) ≤ 32 * ℓ ^ 2 * S t := by
      have := mul_le_mul_of_nonneg_right h3
        (mul_nonneg (by positivity : (0 : ℝ) ≤ 32 * ℓ ^ 2) (hS0 t))
      linarith
    nlinarith
  rw [intervalIntegral.integral_sub (iS.const_mul (32 * ℓ ^ 2)) (iZE.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at step1
  have hEint : ∫ t in a..b, E t ≤ ∫ t in a..b, S t :=
    intervalIntegral.integral_mono_on hab.le iE iS fun t _ => hES t
  have hdiv : 0 ≤ 1 / (b - a) := div_nonneg zero_le_one hba.le
  have key : -(2 * ∫ t in a..b, ζ t * E' t) ≤ 2 / (b - a) * ∫ t in a..b, S t := by
    have h1 : ∫ t in a..b, ζ t * E' t = E b - 1 / (b - a) * ∫ t in a..b, E t := by linarith
    rw [h1]
    have h2 := mul_le_mul_of_nonneg_left hEint hdiv
    have e : 2 / (b - a) = 2 * (1 / (b - a)) := by ring
    rw [e]
    nlinarith
  calc ∫ t in a..b, (t - a) / (b - a) * ∑ x ∈ V, η x ^ 2 * ∑ z ∈ V,
        (if (openGraph ω).Adj x z then (u t z - u t x) ^ 2 else 0)
      = ∫ t in a..b, ζ t * D t := rfl
    _ ≤ 32 * ℓ ^ 2 * (∫ t in a..b, S t) - 2 * ∫ t in a..b, ζ t * E' t := step1
    _ ≤ 2 / (b - a) * (∫ t in a..b, S t) + 32 * ℓ ^ 2 * ∫ t in a..b, S t := by linarith
    _ = (2 / (b - a) + 32 * ℓ ^ 2) * ∫ t in a..b, ∑ x ∈ V, (u t x - m) ^ 2 := by ring

/-! ### The cutoff and the inequality on balls -/

theorem clusterGradAt_sq_le (V : Finset (Vertex 2)) (v : Vertex 2 → ℝ) (x : Vertex 2) :
    clusterGradAt ω V v x ^ 2 ≤
      4 * ∑ z ∈ V, (if (openGraph ω).Adj x z then (v z - v x) ^ 2 else 0) := by
  unfold clusterGradAt
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  have h1 := sq_sum_le_card_mul_sum_sq (s := V.filter fun z => (openGraph ω).Adj x z)
    (f := fun z => |v z - v x|)
  have h2 := card_filter_adj_le_four (ω := ω) V x
  simp only [sq_abs] at h1
  have h3 : 0 ≤ ∑ z ∈ V.filter (fun z => (openGraph ω).Adj x z), (v z - v x) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith

theorem latticeDist_le_two_of_adj {x z : Vertex 2} (h : (openGraph ω).Adj x z) :
    latticeDist x z ≤ 2 := by
  have h0 : |((x 0 - z 0 : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast Rigidity.Proofs.Cluster.abs_sub_le_one_of_openGraph_adj h 0
  have h1 : |((x 1 - z 1 : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast Rigidity.Proofs.Cluster.abs_sub_le_one_of_openGraph_adj h 1
  push_cast at h0 h1
  rw [abs_le] at h0 h1
  have hsq := latticeDist_sq x z
  have hd := latticeDist_nonneg x z
  nlinarith

theorem mem_supp_iff_of_adj {K : OpenComponent ω} {x z : Vertex 2} (h : (openGraph ω).Adj x z) :
    x ∈ K.supp ↔ z ∈ K.supp := by
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.mem_supp_iff]
  have e : (openGraph ω).connectedComponentMk x = (openGraph ω).connectedComponentMk z :=
    SimpleGraph.ConnectedComponent.eq.2 h.reachable
  rw [e]

theorem abs_maxZeroMinOne_sub_le (a b : ℝ) :
    |max 0 (min 1 a) - max 0 (min 1 b)| ≤ |a - b| := by
  have h1 := neg_abs_le (a - b)
  have h2 := le_abs_self (a - b)
  rw [abs_le]
  simp only [max_def, min_def]
  split_ifs <;> constructor <;> linarith

/-- The cutoff `η = 1` on `B_{R/2}(y)`, vanishing at distance `R - 2` from `y` and off `K`. -/
noncomputable def caccCutoff (K : OpenComponent ω) (y : Vertex 2) (R : ℝ) (x : Vertex 2) : ℝ :=
  if x ∈ K.supp then max 0 (min 1 ((R - 2 - latticeDist x y) / (R / 2 - 2))) else 0

theorem caccCutoff_nonneg (K : OpenComponent ω) (y : Vertex 2) (R : ℝ) (x : Vertex 2) :
    0 ≤ caccCutoff K y R x := by
  unfold caccCutoff
  split_ifs <;> simp

theorem caccCutoff_le_one (K : OpenComponent ω) (y : Vertex 2) (R : ℝ) (x : Vertex 2) :
    caccCutoff K y R x ≤ 1 := by
  unfold caccCutoff
  split_ifs
  · exact max_le zero_le_one (min_le_left _ _)
  · exact zero_le_one

theorem caccCutoff_interior (K : OpenComponent ω) (y : Vertex 2) {R : ℝ} (hden : 0 < R / 2 - 2)
    (x : Vertex 2) (hx : caccCutoff K y R x ≠ 0) :
    x ∈ clusterBall K y R ∧ ∀ z, (openGraph ω).Adj x z → z ∈ clusterBall K y R := by
  unfold caccCutoff at hx
  split_ifs at hx with hxK
  · have hpos : 0 < (R - 2 - latticeDist x y) / (R / 2 - 2) := by
      by_contra hle
      push Not at hle
      apply hx
      exact max_eq_left ((min_le_right _ _).trans hle)
    have hd : latticeDist x y < R - 2 := by
      have := (div_pos_iff_of_pos_right hden).1 hpos
      linarith
    refine ⟨mem_clusterBall.2 ⟨hxK, by linarith⟩, fun z hz => mem_clusterBall.2
      ⟨(mem_supp_iff_of_adj hz).1 hxK, ?_⟩⟩
    have h1 := latticeDist_triangle z x y
    have h2 := latticeDist_le_two_of_adj hz
    linarith
  · exact absurd rfl hx

theorem caccCutoff_lip (K : OpenComponent ω) (y : Vertex 2) {R : ℝ} (hden : 0 < R / 2 - 2)
    (x z : Vertex 2) (hxz : (openGraph ω).Adj x z) :
    |caccCutoff K y R x - caccCutoff K y R z| ≤ 2 / (R / 2 - 2) := by
  unfold caccCutoff
  by_cases hxK : x ∈ K.supp
  · have hzK : z ∈ K.supp := (mem_supp_iff_of_adj hxz).1 hxK
    rw [if_pos hxK, if_pos hzK]
    refine (abs_maxZeroMinOne_sub_le _ _).trans ?_
    rw [← sub_div, abs_div, abs_of_pos hden, div_le_div_iff_of_pos_right hden]
    have h1 := latticeDist_triangle x z y
    have h2 := latticeDist_triangle z x y
    have h3 := latticeDist_le_two_of_adj hxz
    have h4 := latticeDist_comm x z
    rw [abs_le]
    constructor <;> linarith
  · have hzK : z ∉ K.supp := fun h => hxK ((mem_supp_iff_of_adj hxz).2 h)
    rw [if_neg hxK, if_neg hzK]
    simp only [sub_self, abs_zero]
    positivity

theorem caccCutoff_eq_one (K : OpenComponent ω) (y : Vertex 2) {R : ℝ} (hden : 0 < R / 2 - 2)
    (x : Vertex 2) (hx : x ∈ clusterBall K y (R / 2)) : caccCutoff K y R x = 1 := by
  obtain ⟨hxK, hxd⟩ := mem_clusterBall.1 hx
  unfold caccCutoff
  rw [if_pos hxK]
  have h1 : 1 ≤ (R - 2 - latticeDist x y) / (R / 2 - 2) := by
    rw [le_div_iff₀ hden]
    linarith
  rw [min_eq_left h1, max_eq_right zero_le_one]

theorem integrableOn_of_continuousOn {F : ℝ → ℝ} {a b : ℝ} (hF : ContinuousOn F (Set.Icc a b)) :
    IntegrableOn F (Set.Ioc a b) volume :=
  (hF.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self

/-- **Dario–Gu, Proposition 2.9** holds, with `C = 128`. -/
theorem darioGuCaccioppoliTwo_holds : DarioGuCaccioppoliTwo := by
  refine ⟨128, by norm_num, fun ω K y R hR u hu => ?_⟩
  set V := clusterBall K y R with hV
  set W := clusterBall K y (R / 2) with hW
  set m := parMean K y R u with hm
  set S : ℝ → ℝ := fun t => ∑ x ∈ V, (u t x - m) ^ 2 with hS
  set G : ℝ → ℝ := fun t => ∑ x ∈ W, clusterGradAt ω V (u t) x ^ 2 with hG
  have hR0 : 0 < R := by linarith
  have hWV : W ⊆ V := clusterBall_mono (by linarith)
  have hcu : ∀ x ∈ V, ContinuousOn (fun t => u t x) (Set.Icc (-R ^ 2) 0) := hu.1
  have hSc : ContinuousOn S (Set.Icc (-R ^ 2) 0) := continuousOn_finsetSum _ fun x hx =>
    ((hcu x hx).sub continuousOn_const).pow 2
  have hS0 : ∀ t, 0 ≤ S t := fun t => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hG0 : ∀ t, 0 ≤ G t := fun t => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsub : Set.Icc (-(R / 2) ^ 2) 0 ⊆ Set.Icc (-R ^ 2) 0 := by
    intro t ht
    exact ⟨le_trans (by nlinarith) ht.1, ht.2⟩
  have hGc : ContinuousOn G (Set.Icc (-(R / 2) ^ 2) 0) := by
    refine continuousOn_finsetSum _ fun x hx => ?_
    refine ContinuousOn.pow ?_ 2
    unfold clusterGradAt
    refine continuousOn_finsetSum _ fun z hz => ?_
    by_cases h : (openGraph ω).Adj x z
    · simp only [h, if_true]
      exact (((hcu z hz).mono hsub).sub ((hcu x (hWV hx)).mono hsub)).abs
    · simp only [h, if_false]
      exact continuousOn_const
  have hIS : IntegrableOn S (Set.Ioc (-R ^ 2) 0) volume := integrableOn_of_continuousOn hSc
  have hIG : IntegrableOn G (Set.Ioc (-(R / 2) ^ 2) 0) volume := integrableOn_of_continuousOn hGc
  have hIoc : Set.Ioc (-(R / 2) ^ 2) 0 ⊆ Set.Ioc (-R ^ 2) 0 := fun t ht =>
    ⟨lt_of_le_of_lt (by nlinarith) ht.1, ht.2⟩
  -- the squared inequality
  suffices h : ∫ t in Set.Ioc (-(R / 2) ^ 2) 0, G t ≤
      (128 / R) ^ 2 * ∫ t in Set.Ioc (-R ^ 2) 0, S t by
    calc Real.sqrt (∫ t in Set.Ioc (-(R / 2) ^ 2) 0, G t)
        ≤ Real.sqrt ((128 / R) ^ 2 * ∫ t in Set.Ioc (-R ^ 2) 0, S t) := Real.sqrt_le_sqrt h
      _ = 128 / R * Real.sqrt (∫ t in Set.Ioc (-R ^ 2) 0, S t) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hSint0 : 0 ≤ ∫ t in Set.Ioc (-R ^ 2) 0, S t := setIntegral_nonneg measurableSet_Ioc
    fun t _ => hS0 t
  rcases lt_or_ge R 8 with hR8 | hR8
  · -- small radii: the gradient is bounded by the values
    have hpt : ∀ t, G t ≤ 64 * S t := by
      intro t
      set v : Vertex 2 → ℝ := fun x => u t x - m with hv
      have h1 : ∀ x ∈ W, clusterGradAt ω V (u t) x ^ 2 ≤
          8 * ∑ z ∈ V, (if (openGraph ω).Adj x z then v x ^ 2 + v z ^ 2 else 0) := by
        intro x _
        refine (clusterGradAt_sq_le (ω := ω) V (u t) x).trans ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_le_sum fun z _ => ?_
        split_ifs
        · simp only [hv]
          nlinarith [sq_nonneg (u t z - m + (u t x - m))]
        · simp
      have h2 : ∑ x ∈ W, ∑ z ∈ V, (if (openGraph ω).Adj x z then v x ^ 2 + v z ^ 2 else 0) ≤
          ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then v x ^ 2 + v z ^ 2 else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg hWV fun x _ _ =>
          Finset.sum_nonneg fun z _ => by split_ifs <;> positivity
      have h3 : ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then v x ^ 2 + v z ^ 2 else 0) ≤
          8 * ∑ x ∈ V, v x ^ 2 := by
        have e1 : ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then v x ^ 2 + v z ^ 2 else 0) =
            ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then v x ^ 2 else 0) +
              ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then v z ^ 2 else 0) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun z _ => ?_
          split_ifs <;> ring
        rw [e1, sum_restrict_swap (ω := ω) V (fun z => v z ^ 2)]
        have := sum_restrict_le_four (ω := ω) V (g := fun x => v x ^ 2) (fun x => sq_nonneg _)
        linarith
      have h4 := Finset.sum_le_sum h1
      rw [← Finset.mul_sum] at h4
      simp only [hG, hS]
      have e : ∑ x ∈ V, v x ^ 2 = ∑ x ∈ V, (u t x - m) ^ 2 := rfl
      linarith
    have hI1 : ∫ t in Set.Ioc (-(R / 2) ^ 2) 0, G t ≤
        ∫ t in Set.Ioc (-(R / 2) ^ 2) 0, 64 * S t :=
      setIntegral_mono_on hIG ((hIS.mono_set hIoc).const_mul 64) measurableSet_Ioc
        fun t _ => hpt t
    have hI2 : ∫ t in Set.Ioc (-(R / 2) ^ 2) 0, 64 * S t ≤
        ∫ t in Set.Ioc (-R ^ 2) 0, 64 * S t :=
      setIntegral_mono_set (hIS.const_mul 64)
        (Filter.Eventually.of_forall fun t => by have := hS0 t; positivity)
        (Filter.Eventually.of_forall hIoc)
    simp only [integral_const_mul] at hI1 hI2
    have hc : (64 : ℝ) ≤ (128 / R) ^ 2 := by
      rw [div_pow, le_div_iff₀ (by positivity)]
      nlinarith
    have := mul_le_mul_of_nonneg_right hc hSint0
    linarith
  · -- large radii: the cutoff
    set η := caccCutoff (ω := ω) K y R with hη
    set ℓ : ℝ := 2 / (R / 2 - 2) with hℓ
    have hden : 0 < R / 2 - 2 := by linarith
    have hη0 : ∀ x, 0 ≤ η x := caccCutoff_nonneg K y R
    have hη1 : ∀ x, η x ≤ 1 := caccCutoff_le_one K y R
    have hηint : ∀ x, η x ≠ 0 → x ∈ V ∧ ∀ z, (openGraph ω).Adj x z → z ∈ V :=
      caccCutoff_interior K y hden
    have hηlip : ∀ x z, (openGraph ω).Adj x z → |η x - η z| ≤ ℓ := caccCutoff_lip K y hden
    have hηW : ∀ x ∈ W, η x = 1 := caccCutoff_eq_one K y hden
    -- the cutoff inequality
    have hab : -R ^ 2 < 0 := by nlinarith
    have hmain := parabolic_caccioppoli_of_cutoff (ω := ω) hab hu m hη0 hη1 hηint hηlip
    set D : ℝ → ℝ := fun t => ∑ x ∈ V, η x ^ 2 * ∑ z ∈ V,
      (if (openGraph ω).Adj x z then (u t z - u t x) ^ 2 else 0) with hD
    set ζ : ℝ → ℝ := fun t => (t - -R ^ 2) / (0 - -R ^ 2) with hζ
    have hDc : ContinuousOn D (Set.Icc (-R ^ 2) 0) := by
      refine continuousOn_finsetSum _ fun x hx => continuousOn_const.mul ?_
      refine continuousOn_finsetSum _ fun z hz => ?_
      by_cases h : (openGraph ω).Adj x z
      · simp only [h, if_true]
        exact ((hcu z hz).sub (hcu x hx)).pow 2
      · simp only [h, if_false]
        exact continuousOn_const
    have hζc : ContinuousOn ζ (Set.Icc (-R ^ 2) 0) :=
      ((continuous_id.sub continuous_const).div_const _).continuousOn
    have hD0 : ∀ t, 0 ≤ D t := fun t => Finset.sum_nonneg fun x _ =>
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun z _ => by split_ifs <;> positivity)
    have hIZD : IntegrableOn (fun t => 16 / 3 * (ζ t * D t)) (Set.Ioc (-R ^ 2) 0) volume :=
      (integrableOn_of_continuousOn (hζc.mul hDc)).const_mul _
    -- the gradient on `W` is controlled by `D`
    have hpt : ∀ t ∈ Set.Ioc (-(R / 2) ^ 2) 0, G t ≤ 16 / 3 * (ζ t * D t) := by
      intro t ht
      have h1 : G t ≤ 4 * D t := by
        simp only [hG, hD]
        calc ∑ x ∈ W, clusterGradAt ω V (u t) x ^ 2
            ≤ ∑ x ∈ W, 4 * ∑ z ∈ V,
                (if (openGraph ω).Adj x z then (u t z - u t x) ^ 2 else 0) :=
              Finset.sum_le_sum fun x _ => clusterGradAt_sq_le (ω := ω) V (u t) x
          _ = 4 * ∑ x ∈ W, η x ^ 2 * ∑ z ∈ V,
                (if (openGraph ω).Adj x z then (u t z - u t x) ^ 2 else 0) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun x hx => ?_
              rw [hηW x hx]
              ring
          _ ≤ 4 * ∑ x ∈ V, η x ^ 2 * ∑ z ∈ V,
                (if (openGraph ω).Adj x z then (u t z - u t x) ^ 2 else 0) := by
              refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hWV
                fun x _ _ => mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun z _ => ?_))
                (by norm_num)
              split_ifs <;> positivity
      have h2 : 3 / 4 ≤ ζ t := by
        simp only [hζ]
        rw [le_div_iff₀ (by nlinarith)]
        nlinarith [ht.1]
      have h3 := hD0 t
      nlinarith
    have hI1 : ∫ t in Set.Ioc (-(R / 2) ^ 2) 0, G t ≤
        ∫ t in Set.Ioc (-(R / 2) ^ 2) 0, 16 / 3 * (ζ t * D t) :=
      setIntegral_mono_on hIG (hIZD.mono_set hIoc) measurableSet_Ioc hpt
    have hζ0 : ∀ t ∈ Set.Ioc (-R ^ 2) 0, 0 ≤ ζ t := fun t ht => by
      simp only [hζ]
      exact div_nonneg (by linarith [ht.1]) (by nlinarith)
    have hI2 : ∫ t in Set.Ioc (-(R / 2) ^ 2) 0, 16 / 3 * (ζ t * D t) ≤
        ∫ t in Set.Ioc (-R ^ 2) 0, 16 / 3 * (ζ t * D t) :=
      setIntegral_mono_set hIZD
        ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht => by
          have := hζ0 t ht
          have := hD0 t
          positivity))
        (Filter.Eventually.of_forall hIoc)
    simp only [integral_const_mul] at hI1 hI2
    have hmain' : ∫ t in Set.Ioc (-R ^ 2) 0, ζ t * D t ≤
        (2 / (0 - -R ^ 2) + 32 * ℓ ^ 2) * ∫ t in Set.Ioc (-R ^ 2) 0, S t := by
      have h := hmain
      rw [intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_of_le hab.le] at h
      exact h
    have hℓ2 : ℓ ^ 2 ≤ 64 / R ^ 2 := by
      have h1 : ℓ ≤ 8 / R := by
        simp only [hℓ]
        rw [div_le_div_iff₀ hden hR0]
        linarith
      have h0 : 0 ≤ ℓ := by simp only [hℓ]; positivity
      calc ℓ ^ 2 ≤ (8 / R) ^ 2 := pow_le_pow_left₀ h0 h1 2
        _ = 64 / R ^ 2 := by ring
    have hconst : 16 / 3 * (2 / (0 - -R ^ 2) + 32 * ℓ ^ 2) ≤ (128 / R) ^ 2 := by
      have e : 2 / (0 - -R ^ 2) = 2 / R ^ 2 := by ring
      rw [e]
      have hR2 : 0 < R ^ 2 := by positivity
      have h2 : 16 / 3 * (2 / R ^ 2 + 32 * (64 / R ^ 2)) ≤ (128 / R) ^ 2 := by
        rw [div_pow, show 16 / 3 * (2 / R ^ 2 + 32 * (64 / R ^ 2)) = (16 / 3 * 2050) / R ^ 2 by
          ring]
        exact div_le_div_of_nonneg_right (by norm_num) hR2.le
      nlinarith
    have h3 := mul_le_mul_of_nonneg_left hmain' (by norm_num : (0 : ℝ) ≤ 16 / 3)
    have h4 := mul_le_mul_of_nonneg_right hconst hSint0
    linarith

end Rigidity.Green
