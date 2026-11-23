import Rigidity.Proofs.Green.PlanarHeatKernelInputs
import Rigidity.Proofs.Green.LazyHeatMass
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Heat decay of periodic functions of mean zero

Dario, Lemma 3.2, Step 3: for a function `f` on `ℤ²` which is `L`-periodic with mean zero over a
period, `Φ_t * f` decays like `exp(-16 t / L²)`. As in the source, by the discrete Fourier
transform: the characters `ψ_{a,b}(y) = exp(2πi (a y₁ + b y₂)/L)` are eigenfunctions of the heat
kernel of `ℤ²`, `Φ_t * ψ_{a,b} = exp(-t λ_{a,b}) ψ_{a,b}` with
`λ_{a,b} = 2(1 - cos(2πa/L)) + 2(1 - cos(2πb/L)) ≥ 16/L²` for `(a, b) ≠ 0`, and the indicator of a
residue class modulo `L` is the average of the characters against it.

* `hasSum_lazyPow_mul_eigen`, `hasSum_vsrwHeat_mul_eigen`: an eigenfunction `u` of the lazy kernel
  with eigenvalue `μ` satisfies `Σ_y p_t(x, y) u(y) = e^{D t (μ - 1)} u(x)`;
* `sum_range_exp_mul_eq`: `Σ_{a < L} e^{2πi a m / L} = L` if `L ∣ m` and `0` otherwise;
* `abs_tsum_openHeat_mul_le`: `|Σ_y Φ(t, x, y) g(y mod L)| ≤ e^{-16 t/L²} Σ_w |g(w)|` for every
  `g : (ℤ/L)² → ℝ` of sum zero;
* `abs_tsum_openHeat_mul_periodic_le`, `abs_tsum_openHeat_mul_periodic_le_exp`: the same for
  `L`-periodic functions of sum zero over `{0, …, L-1}²`, and the form used by Dario, with
  `L = 3^k`, `t = r²` and `9^k ≤ r`: `|Φ_{r²} * f(x)| ≤ e^{-16 r} Σ_{period} |f|`.
-/

open scoped Classical
open Finset

namespace Rigidity.Green

section Eigen

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {D : ℕ}

/-- **The lazy kernel on an eigenfunction**: if `(1 - deg x/D) u(x) + D⁻¹ Σ_{z ∼ x} u(z) = μ u(x)`
for every `x`, then `Σ_y Qⁿ(x, y) u(y) = μⁿ u(x)`. -/
theorem hasSum_lazyPow_mul_eigen {u : V → ℂ} {μ : ℂ}
    (heig : ∀ x, (1 - (G.degree x : ℂ) / D) * u x +
      1 / (D : ℂ) * ∑ z ∈ G.neighborFinset x, u z = μ * u x) (n : ℕ) (x : V) :
    HasSum (fun y => (lazyPow G D n x y : ℂ) * u y) (μ ^ n * u x) := by
  induction n generalizing x with
  | zero =>
    have e : (fun y => (lazyPow G D 0 x y : ℂ) * u y) = fun y => if y = x then u x else 0 := by
      funext y
      rw [lazyPow_zero]
      by_cases hxy : x = y
      · subst hxy
        simp
      · rw [if_neg hxy, if_neg (Ne.symm hxy)]
        simp
    rw [e, pow_zero, one_mul]
    exact hasSum_ite_eq x (u x)
  | succ n ih =>
    have h1 := (ih x).mul_left (1 - (G.degree x : ℂ) / D)
    have h2 := (hasSum_sum fun z (_ : z ∈ G.neighborFinset x) => ih z).mul_left (1 / (D : ℂ))
    have h := h1.add h2
    have e : (fun y => (lazyPow G D (n + 1) x y : ℂ) * u y) = fun y =>
        (1 - (G.degree x : ℂ) / D) * ((lazyPow G D n x y : ℂ) * u y) +
          1 / (D : ℂ) * ∑ z ∈ G.neighborFinset x, (lazyPow G D n z y : ℂ) * u y := by
      funext y
      rw [lazyPow_succ]
      push_cast
      rw [← Finset.sum_mul]
      ring
    have hv : (1 - (G.degree x : ℂ) / D) * (μ ^ n * u x) +
        1 / (D : ℂ) * ∑ z ∈ G.neighborFinset x, μ ^ n * u z = μ ^ (n + 1) * u x := by
      rw [← Finset.mul_sum]
      linear_combination (μ ^ n) * heig x
    rw [e, ← hv]
    exact h

/-- The Poisson weights against a geometric sequence: `Σ_n w_n μⁿ c = e^{D t (μ - 1)} c`. -/
theorem hasSum_poissonWeight_mul_pow (D : ℕ) (t : ℝ) (μ c : ℂ) :
    HasSum (fun n => (poissonWeight D t n : ℂ) * (μ ^ n * c))
      (Complex.exp ((D : ℂ) * t * (μ - 1)) * c) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp ((D : ℂ) * t * μ)).mul_left
    (Complex.exp (-((D : ℂ) * t)) * c)
  rw [← Complex.exp_eq_exp_ℂ] at h
  have e1 : Complex.exp (-((D : ℂ) * t)) * c * Complex.exp ((D : ℂ) * t * μ) =
      Complex.exp ((D : ℂ) * t * (μ - 1)) * c := by
    rw [mul_right_comm, ← Complex.exp_add]
    congr 2
    ring
  rw [e1] at h
  refine h.congr_fun fun n => ?_
  simp only [poissonWeight]
  push_cast
  rw [mul_pow, mul_pow]
  ring

theorem summable_poissonWeight_mul_lazyPow (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {t : ℝ}
    (ht : 0 ≤ t) (x : V) :
    Summable fun q : ℕ × V => poissonWeight D t q.1 * lazyPow G D q.1 x q.2 := by
  have hnn : 0 ≤ fun q : ℕ × V => poissonWeight D t q.1 * lazyPow G D q.1 x q.2 := fun q =>
    mul_nonneg (poissonWeight_nonneg ht _) (lazyPow_mem_Icc hD hdeg _ _ _).1
  have hrow : ∀ n, ∑' y, poissonWeight D t n * lazyPow G D n x y = poissonWeight D t n :=
    fun n => by rw [((hasSum_lazyPow hD n x).mul_left (poissonWeight D t n)).tsum_eq, mul_one]
  rw [summable_prod_of_nonneg hnn]
  exact ⟨fun n => ((hasSum_lazyPow hD n x).mul_left (poissonWeight D t n)).summable,
    (hasSum_poissonWeight t).summable.congr fun n => (hrow n).symm⟩

/-- **The heat kernel on an eigenfunction**: `Σ_y p_t(x, y) u(y) = e^{D t (μ - 1)} u(x)` for a
bounded eigenfunction `u` of the lazy kernel with eigenvalue `μ`. -/
theorem hasSum_vsrwHeat_mul_eigen (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {u : V → ℂ}
    (hu : ∀ y, ‖u y‖ ≤ 1) {μ : ℂ}
    (heig : ∀ x, (1 - (G.degree x : ℂ) / D) * u x +
      1 / (D : ℂ) * ∑ z ∈ G.neighborFinset x, u z = μ * u x) {t : ℝ} (ht : 0 ≤ t) (x : V) :
    HasSum (fun y => (vsrwHeat G D t x y : ℂ) * u y)
      (Complex.exp ((D : ℂ) * t * (μ - 1)) * u x) := by
  have hFs : Summable fun q : ℕ × V =>
      (poissonWeight D t q.1 : ℂ) * ((lazyPow G D q.1 x q.2 : ℂ) * u q.2) := by
    refine (summable_poissonWeight_mul_lazyPow hD hdeg ht x).of_norm_bounded fun q => ?_
    rw [norm_mul, norm_mul, Complex.norm_of_nonneg (poissonWeight_nonneg ht _),
      Complex.norm_of_nonneg (lazyPow_mem_Icc hD hdeg _ _ _).1]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (lazyPow_mem_Icc hD hdeg _ _ _).1
      (hu _)) (poissonWeight_nonneg ht _)
  have hval := (hFs.hasSum.prod_fiberwise fun n =>
    (hasSum_lazyPow_mul_eigen heig n x).mul_left (poissonWeight D t n : ℂ)).unique
      (hasSum_poissonWeight_mul_pow D t μ (u x))
  have hfib2 : ∀ y, HasSum (fun n => (poissonWeight D t n : ℂ) *
      ((lazyPow G D n x y : ℂ) * u y)) ((vsrwHeat G D t x y : ℂ) * u y) := by
    intro y
    have h := (Complex.hasSum_ofReal.2 (summable_vsrwHeat hD hdeg t x y).hasSum).mul_right (u y)
    refine h.congr_fun fun n => ?_
    push_cast
    ring
  have h2 := ((Equiv.prodComm V ℕ).hasSum_iff.2 hFs.hasSum).prod_fiberwise fun y => hfib2 y
  rw [hval] at h2
  exact h2

end Eigen

end Rigidity.Green

namespace Rigidity.Corrector

open LatticeProb LatticeProb.Percolation Rigidity.Green

/-- The neighbours of `x` in the lattice with every bond open. -/
theorem neighborFinset_allOpen (x : Vertex 2) :
    (openGraph (allOpen 2)).neighborFinset x = nbrFinset x := by
  ext y
  rw [SimpleGraph.mem_neighborFinset, ← Graph.Zd.neighborFinset_eq, SimpleGraph.mem_neighborFinset,
    openGraph_allOpen]

theorem degree_allOpen (x : Vertex 2) : (openGraph (allOpen 2)).degree x = 4 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_allOpen, Graph.Zd.card_nbrFinset]

theorem sum_neighborFinset_allOpen (x : Vertex 2) (u : Vertex 2 → ℂ) :
    ∑ z ∈ (openGraph (allOpen 2)).neighborFinset x, u z =
      ∑ i : Fin 2, (u (x + unit i) + u (x - unit i)) := by
  rw [neighborFinset_allOpen, nbrFinset, sum_biUnion]
  · refine sum_congr rfl fun i _ => ?_
    rw [sum_pair]
    intro h
    have := congrFun h i
    simp only [unit, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same] at this
    omega
  · intro i _ j _ hij
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
    rintro a (rfl | rfl) (h | h) <;>
      · have h1 := congrFun h i
        have h2 := congrFun h j
        simp [unit, Pi.single_eq_same, Pi.single_eq_of_ne, hij] at h1 h2

/-- The character `ψ(y) = exp(i (θ₀ y₀ + θ₁ y₁))` of `ℤ²`. -/
noncomputable def latticeChar (θ : Fin 2 → ℝ) (y : Vertex 2) : ℂ :=
  Complex.exp (((θ 0 * y 0 + θ 1 * y 1 : ℝ) : ℂ) * Complex.I)

theorem norm_latticeChar (θ : Fin 2 → ℝ) (y : Vertex 2) : ‖latticeChar θ y‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem latticeChar_add_unit (θ : Fin 2 → ℝ) (y : Vertex 2) (i : Fin 2) (s : ℤ) :
    latticeChar θ (y + s • unit i) =
      latticeChar θ y * Complex.exp (((θ i * s : ℝ) : ℂ) * Complex.I) := by
  rw [latticeChar, latticeChar, ← Complex.exp_add]
  congr 1
  fin_cases i <;> simp [unit] <;> ring

/-- The characters are eigenfunctions of the lazy kernel of `ℤ²`, with eigenvalue
`(cos θ₀ + cos θ₁)/2`. -/
theorem latticeChar_eigen (θ : Fin 2 → ℝ) (x : Vertex 2) :
    (1 - ((openGraph (allOpen 2)).degree x : ℂ) / (4 : ℕ)) * latticeChar θ x +
      1 / ((4 : ℕ) : ℂ) * ∑ z ∈ (openGraph (allOpen 2)).neighborFinset x, latticeChar θ z =
      (((Real.cos (θ 0) + Real.cos (θ 1)) / 2 : ℝ) : ℂ) * latticeChar θ x := by
  have hp : ∀ i : Fin 2, latticeChar θ (x + unit i) + latticeChar θ (x - unit i) =
      latticeChar θ x * (2 * (Real.cos (θ i) : ℂ)) := by
    intro i
    have h1 := latticeChar_add_unit θ x i 1
    have h2 := latticeChar_add_unit θ x i (-1)
    rw [one_smul] at h1
    rw [neg_smul, one_smul, ← sub_eq_add_neg] at h2
    rw [h1, h2, ← mul_add, Complex.ofReal_cos]
    congr 1
    rw [Complex.cos, Int.cast_one, mul_one, Int.cast_neg, Int.cast_one, mul_neg_one,
      Complex.ofReal_neg, neg_mul]
    ring
  rw [degree_allOpen, sum_neighborFinset_allOpen, Fin.sum_univ_two, hp 0, hp 1]
  push_cast
  ring

/-- `Σ_y Φ(t, x, y) ψ(y) = e^{-t λ} ψ(x)` with `λ = 2(1 - cos θ₀) + 2(1 - cos θ₁)`. -/
theorem hasSum_openHeat_mul_latticeChar (θ : Fin 2 → ℝ) {t : ℝ} (ht : 0 ≤ t) (x : Vertex 2) :
    HasSum (fun y => (openHeat (allOpen 2) t x y : ℂ) * latticeChar θ y)
      (((Real.exp (-(t * (2 * (1 - Real.cos (θ 0)) + 2 * (1 - Real.cos (θ 1))))) : ℝ) : ℂ) *
        latticeChar θ x) := by
  have h := hasSum_vsrwHeat_mul_eigen (G := openGraph (allOpen 2)) (D := 4) (by norm_num)
    (openGraph_degree_le_four _) (fun y => (norm_latticeChar θ y).le) (latticeChar_eigen θ) ht x
  have e : ((4 : ℕ) : ℂ) * t * ((((Real.cos (θ 0) + Real.cos (θ 1)) / 2 : ℝ) : ℂ) - 1) =
      ((-(t * (2 * (1 - Real.cos (θ 0)) + 2 * (1 - Real.cos (θ 1)))) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [e, ← Complex.ofReal_exp] at h
  exact h

/-- **Orthogonality of the roots of unity**: `Σ_{a < L} e^{2πi a m / L} = L 1_{L ∣ m}`. -/
theorem sum_range_exp_mul_eq {L : ℕ} (hL : 0 < L) (m : ℤ) :
    ∑ a ∈ range L, Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * m) / L) =
      if (L : ℤ) ∣ m then (L : ℂ) else 0 := by
  have hζ := Complex.isPrimitiveRoot_exp L hL.ne'
  have hterm : ∀ a : ℕ, Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * m) / L) =
      (Complex.exp (2 * Real.pi * Complex.I / L) ^ m) ^ a := by
    intro a
    rw [← zpow_natCast, ← zpow_mul, ← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  simp_rw [hterm]
  split_ifs with h
  · rw [(hζ.zpow_eq_one_iff_dvd m).2 h]
    simp
  · have hne : Complex.exp (2 * Real.pi * Complex.I / L) ^ m ≠ 1 := fun h' =>
      h ((hζ.zpow_eq_one_iff_dvd m).1 h')
    have hL1 : (Complex.exp (2 * Real.pi * Complex.I / L) ^ m) ^ L = 1 := by
      rw [← zpow_natCast, ← zpow_mul]
      exact (hζ.zpow_eq_one_iff_dvd _).2 (dvd_mul_left _ _)
    rw [geom_sum_eq hne, hL1, sub_self, zero_div]

/-- The angle `2πa/L`. -/
noncomputable def charAngle (L a : ℕ) : ℝ := 2 * Real.pi * a / L

theorem exp_charAngle (L a : ℕ) (m : ℤ) :
    Complex.exp (((charAngle L a * m : ℝ) : ℂ) * Complex.I) =
      Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * m) / L) := by
  congr 1
  rw [charAngle]
  push_cast
  ring

/-- `1 - cos(2πa/L) ≥ 8/L²` for `0 < a < L`. -/
theorem one_sub_cos_charAngle_ge {L a : ℕ} (ha : 0 < a) (haL : a < L) :
    8 / (L : ℝ) ^ 2 ≤ 1 - Real.cos (charAngle L a) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast (ha.trans haL)
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
  have hpi := Real.pi_pos
  -- `cos(2πa/L) ≤ cos(2π/L)`
  have hcos : Real.cos (charAngle L a) ≤ Real.cos (2 * Real.pi / L) := by
    have key : ∀ b : ℕ, 0 < b → 2 * b ≤ L →
        Real.cos (2 * Real.pi * b / L) ≤ Real.cos (2 * Real.pi / L) := by
      intro b hb hbL
      have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
      have hbL' : (2 * b : ℝ) ≤ L := by exact_mod_cast hbL
      refine Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) ?_ ?_
      · rw [div_le_iff₀ hL]
        nlinarith
      · exact div_le_div_of_nonneg_right (by nlinarith) hL.le
    by_cases h2 : 2 * a ≤ L
    · exact key a ha h2
    · have hLa : 0 < L - a := by omega
      have h3 : 2 * (L - a) ≤ L := by omega
      have e : Real.cos (charAngle L a) = Real.cos (2 * Real.pi * ((L - a : ℕ) : ℝ) / L) := by
        rw [charAngle, ← Real.cos_two_pi_sub, Nat.cast_sub haL.le]
        congr 1
        field_simp
      rw [e]
      exact key _ hLa h3
  -- `1 - cos(2π/L) = 2 sin²(π/L) ≥ 8/L²`
  have hsin : 2 / Real.pi * (Real.pi / L) ≤ Real.sin (Real.pi / L) :=
    Real.mul_le_sin (by positivity) (by rw [div_le_div_iff₀ hL (by norm_num)]; nlinarith)
  have hsin' : 2 / (L : ℝ) ≤ Real.sin (Real.pi / L) := by
    have : 2 / Real.pi * (Real.pi / L) = 2 / L := by field_simp
    linarith
  have hid : 1 - Real.cos (2 * Real.pi / L) = 2 * Real.sin (Real.pi / L) ^ 2 := by
    have := Real.cos_sq_add_sin_sq (Real.pi / L)
    rw [show 2 * Real.pi / L = 2 * (Real.pi / L) by ring, Real.cos_two_mul]
    linarith
  have h2L : (0 : ℝ) ≤ 2 / L := by positivity
  have hsq : (2 / (L : ℝ)) ^ 2 ≤ Real.sin (Real.pi / L) ^ 2 := pow_le_pow_left₀ h2L hsin' 2
  have h8 : 8 / (L : ℝ) ^ 2 = 2 * (2 / L) ^ 2 := by field_simp; ring
  linarith

/-- `λ_{a,b} ≥ 16/L²` for `(a, b) ≠ 0` with `a, b < L`. -/
theorem charEigen_ge {L a b : ℕ} (haL : a < L) (hbL : b < L) (hab : (a, b) ≠ (0, 0)) :
    16 / (L : ℝ) ^ 2 ≤ 2 * (1 - Real.cos (charAngle L a)) + 2 * (1 - Real.cos (charAngle L b)) := by
  have h0a : 0 ≤ 1 - Real.cos (charAngle L a) := by linarith [Real.cos_le_one (charAngle L a)]
  have h0b : 0 ≤ 1 - Real.cos (charAngle L b) := by linarith [Real.cos_le_one (charAngle L b)]
  rcases Nat.eq_zero_or_pos a with ha | ha
  · have hb : 0 < b := by
      rcases Nat.eq_zero_or_pos b with hb | hb
      · exact absurd (by rw [ha, hb]) hab
      · exact hb
    have := one_sub_cos_charAngle_ge hb hbL
    have e : (16 : ℝ) / L ^ 2 = 2 * (8 / L ^ 2) := by ring
    linarith
  · have := one_sub_cos_charAngle_ge ha haL
    have e : (16 : ℝ) / L ^ 2 = 2 * (8 / L ^ 2) := by ring
    linarith

/-- The exponent `λ_{a,b} = 2(1 - cos(2πa/L)) + 2(1 - cos(2πb/L))`. -/
noncomputable def charEigen (L a b : ℕ) : ℝ :=
  2 * (1 - Real.cos (charAngle L a)) + 2 * (1 - Real.cos (charAngle L b))

/-- The phase `exp(-i (2πa w₁ + 2πb w₂)/L)` of a residue class `w`. -/
noncomputable def charPhase (L a b : ℕ) (w : ZMod L × ZMod L) : ℂ :=
  Complex.exp (((-(charAngle L a * (w.1.val : ℤ) + charAngle L b * (w.2.val : ℤ)) : ℝ) : ℂ) *
    Complex.I)

theorem norm_charPhase (L a b : ℕ) (w : ZMod L × ZMod L) : ‖charPhase L a b w‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem charPhase_zero (L : ℕ) (w : ZMod L × ZMod L) : charPhase L 0 0 w = 1 := by
  simp [charPhase, charAngle]

/-- **The indicator of a residue class is an average of characters**:
`1_{y ≡ w} = L⁻² Σ_{a, b < L} ψ_{a,b}(y) exp(-i (2πa w₁ + 2πb w₂)/L)`. -/
theorem indicator_eq_sum_latticeChar {L : ℕ} [NeZero L] (y : Vertex 2) (w : ZMod L × ZMod L) :
    (if ((y 0 : ZMod L), (y 1 : ZMod L)) = w then (1 : ℂ) else 0) =
      ((L : ℂ) ^ 2)⁻¹ * ∑ a ∈ range L, ∑ b ∈ range L,
        latticeChar ![charAngle L a, charAngle L b] y * charPhase L a b w := by
  have hL : 0 < L := NeZero.pos L
  have hLc : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hL.ne'
  have hfac : ∀ a b : ℕ, latticeChar ![charAngle L a, charAngle L b] y * charPhase L a b w =
      Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * ((y 0 - w.1.val : ℤ) : ℂ)) / L) *
        Complex.exp (2 * Real.pi * Complex.I * ((b : ℂ) * ((y 1 - w.2.val : ℤ) : ℂ)) / L) := by
    intro a b
    rw [← exp_charAngle, ← exp_charAngle, latticeChar, charPhase, ← Complex.exp_add,
      ← Complex.exp_add]
    congr 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast
    ring
  simp_rw [hfac, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [sum_range_exp_mul_eq hL, sum_range_exp_mul_eq hL]
  have e0 : ((L : ℤ) ∣ y 0 - (w.1.val : ℤ)) ↔ (y 0 : ZMod L) = w.1 := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, eq_comm, Int.cast_natCast, ZMod.natCast_zmod_val]
  have e1 : ((L : ℤ) ∣ y 1 - (w.2.val : ℤ)) ↔ (y 1 : ZMod L) = w.2 := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, eq_comm, Int.cast_natCast, ZMod.natCast_zmod_val]
  by_cases h0 : (y 0 : ZMod L) = w.1
  · by_cases h1 : (y 1 : ZMod L) = w.2
    · rw [if_pos (Prod.ext h0 h1), if_pos (e0.2 h0), if_pos (e1.2 h1), ← pow_two,
        inv_mul_cancel₀ (pow_ne_zero 2 hLc)]
    · rw [if_neg (fun h => h1 (congrArg Prod.snd h)), if_neg (fun h => h1 (e1.1 h)), mul_zero,
        mul_zero]
  · rw [if_neg (fun h => h0 (congrArg Prod.fst h)), if_neg (fun h => h0 (e0.1 h)), zero_mul,
      mul_zero]

/-- The heat kernel on the characters `ψ_{a,b}`. -/
theorem hasSum_openHeat_mul_char (L a b : ℕ) {t : ℝ} (ht : 0 ≤ t) (x : Vertex 2) :
    HasSum (fun y => (openHeat (allOpen 2) t x y : ℂ) *
        latticeChar ![charAngle L a, charAngle L b] y)
      ((Real.exp (-(t * charEigen L a b)) : ℝ) * latticeChar ![charAngle L a, charAngle L b] x) := by
  have h := hasSum_openHeat_mul_latticeChar ![charAngle L a, charAngle L b] ht x
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  exact h

/-- **Dario, Lemma 3.2, Step 3**: for `g : (ℤ/L)² → ℝ` of sum zero,
`|Σ_y Φ(t, x, y) g(y mod L)| ≤ e^{-16 t/L²} Σ_w |g(w)|`. -/
theorem abs_tsum_openHeat_mul_le {L : ℕ} [NeZero L] (g : ZMod L × ZMod L → ℝ)
    (hg : ∑ w, g w = 0) {t : ℝ} (ht : 0 ≤ t) (x : Vertex 2) :
    |∑' y, openHeat (allOpen 2) t x y * g ((y 0 : ZMod L), (y 1 : ZMod L))| ≤
      Real.exp (-(16 * t / (L : ℝ) ^ 2)) * ∑ w, |g w| := by
  have hL : 0 < L := NeZero.pos L
  have hdeg := openGraph_degree_le_four (allOpen 2)
  have hp0 : ∀ y, 0 ≤ openHeat (allOpen 2) t x y := fun y =>
    vsrwHeat_nonneg (by norm_num) hdeg ht x y
  -- the complex sum, character by character
  have hsum : HasSum (fun y => ((openHeat (allOpen 2) t x y *
      g ((y 0 : ZMod L), (y 1 : ZMod L)) : ℝ) : ℂ))
      (∑ w, (g w : ℂ) * (((L : ℂ) ^ 2)⁻¹ * ∑ a ∈ range L, ∑ b ∈ range L,
        charPhase L a b w * ((Real.exp (-(t * charEigen L a b)) : ℝ) *
          latticeChar ![charAngle L a, charAngle L b] x))) := by
    have hrep : ∀ y, ((openHeat (allOpen 2) t x y * g ((y 0 : ZMod L), (y 1 : ZMod L)) : ℝ) : ℂ) =
        ∑ w, (g w : ℂ) * (((L : ℂ) ^ 2)⁻¹ * ∑ a ∈ range L, ∑ b ∈ range L,
          charPhase L a b w * ((openHeat (allOpen 2) t x y : ℂ) *
            latticeChar ![charAngle L a, charAngle L b] y)) := by
      intro y
      have hfy : (g ((y 0 : ZMod L), (y 1 : ZMod L)) : ℂ) = ∑ w, (g w : ℂ) *
          (if ((y 0 : ZMod L), (y 1 : ZMod L)) = w then (1 : ℂ) else 0) := by
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [Complex.ofReal_mul, hfy, Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [indicator_eq_sum_latticeChar]
      have hin : (openHeat (allOpen 2) t x y : ℂ) * ∑ a ∈ range L, ∑ b ∈ range L,
          latticeChar ![charAngle L a, charAngle L b] y * charPhase L a b w =
          ∑ a ∈ range L, ∑ b ∈ range L, charPhase L a b w *
            ((openHeat (allOpen 2) t x y : ℂ) * latticeChar ![charAngle L a, charAngle L b] y) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring
      rw [← hin]
      ring
    rw [funext hrep]
    exact hasSum_sum fun w _ => ((hasSum_sum fun a _ => hasSum_sum fun b _ =>
      (hasSum_openHeat_mul_char L a b ht x).mul_left (charPhase L a b w)).mul_left
        (((L : ℂ) ^ 2)⁻¹)).mul_left (g w : ℂ)
  -- the real sum
  have hpsum : Summable fun y => openHeat (allOpen 2) t x y := by
    have h1 : ∑' y, ENNReal.ofReal (openHeat (allOpen 2) t x y) = 1 :=
      tsum_ofReal_vsrwHeat (by norm_num) hdeg ht x
    refine (ENNReal.summable_toReal (by rw [h1]; exact ENNReal.one_ne_top)).congr fun y =>
      ENNReal.toReal_ofReal (hp0 y)
  have hfb : ∀ y : Vertex 2, |g ((y 0 : ZMod L), (y 1 : ZMod L))| ≤ ∑ w, |g w| := fun y =>
    Finset.single_le_sum (f := fun w => |g w|) (fun w _ => abs_nonneg _) (Finset.mem_univ _)
  have hreal : Summable fun y => openHeat (allOpen 2) t x y * g ((y 0 : ZMod L), (y 1 : ZMod L)) := by
    refine (hpsum.mul_right (∑ w, |g w|)).of_norm_bounded fun y => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp0 y)]
    exact mul_le_mul_of_nonneg_left (hfb y) (hp0 y)
  have heq := (Complex.hasSum_ofReal.2 hreal.hasSum).unique hsum
  rw [← Real.norm_eq_abs, ← Complex.norm_real, heq]
  -- regroup by characters
  have hregroup : ∑ w, (g w : ℂ) * (((L : ℂ) ^ 2)⁻¹ * ∑ a ∈ range L, ∑ b ∈ range L,
        charPhase L a b w * ((Real.exp (-(t * charEigen L a b)) : ℝ) *
          latticeChar ![charAngle L a, charAngle L b] x)) =
      ((L : ℂ) ^ 2)⁻¹ * ∑ a ∈ range L, ∑ b ∈ range L,
        (∑ w, (g w : ℂ) * charPhase L a b w) * ((Real.exp (-(t * charEigen L a b)) : ℝ) *
          latticeChar ![charAngle L a, charAngle L b] x) := by
    have hcomm : ∀ F : ZMod L × ZMod L → ℕ → ℕ → ℂ,
        (∑ w, ∑ a ∈ range L, ∑ b ∈ range L, F w a b) =
          ∑ a ∈ range L, ∑ b ∈ range L, ∑ w, F w a b := fun F => by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    calc ∑ w, (g w : ℂ) * (((L : ℂ) ^ 2)⁻¹ * ∑ a ∈ range L, ∑ b ∈ range L,
          charPhase L a b w * ((Real.exp (-(t * charEigen L a b)) : ℝ) *
            latticeChar ![charAngle L a, charAngle L b] x))
        = ∑ w, ∑ a ∈ range L, ∑ b ∈ range L, ((L : ℂ) ^ 2)⁻¹ * ((g w : ℂ) * charPhase L a b w *
            ((Real.exp (-(t * charEigen L a b)) : ℝ) *
              latticeChar ![charAngle L a, charAngle L b] x)) := by
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          ring
      _ = ∑ a ∈ range L, ∑ b ∈ range L, ∑ w, ((L : ℂ) ^ 2)⁻¹ * ((g w : ℂ) * charPhase L a b w *
            ((Real.exp (-(t * charEigen L a b)) : ℝ) *
              latticeChar ![charAngle L a, charAngle L b] x)) := hcomm _
      _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
  rw [hregroup]
  have hterm : ∀ a ∈ range L, ∀ b ∈ range L,
      ‖(∑ w, (g w : ℂ) * charPhase L a b w) * ((Real.exp (-(t * charEigen L a b)) : ℝ) *
          latticeChar ![charAngle L a, charAngle L b] x)‖ ≤
        Real.exp (-(16 * t / (L : ℝ) ^ 2)) * ∑ w, |g w| := by
    intro a ha b hb
    rw [mem_range] at ha hb
    by_cases hab : (a, b) = (0, 0)
    · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 hab
      simp_rw [charPhase_zero, mul_one]
      rw [← Complex.ofReal_sum, hg, Complex.ofReal_zero, zero_mul, norm_zero]
      positivity
    · have hlam : 16 / (L : ℝ) ^ 2 ≤ charEigen L a b := charEigen_ge ha hb hab
      have hc' : ‖∑ w, (g w : ℂ) * charPhase L a b w‖ ≤ ∑ w, |g w| := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => ?_)
        rw [norm_mul, norm_charPhase, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [norm_mul, norm_mul, norm_latticeChar, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
      refine mul_le_mul (Real.exp_le_exp.2 ?_) hc' (norm_nonneg _) (Real.exp_pos _).le
      have e : 16 * t / (L : ℝ) ^ 2 = t * (16 / (L : ℝ) ^ 2) := by ring
      rw [e]
      exact neg_le_neg (mul_le_mul_of_nonneg_left hlam ht)
  have hL2 : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  calc ((L : ℝ) ^ 2)⁻¹ * ‖∑ a ∈ range L, ∑ b ∈ range L,
        (∑ w, (g w : ℂ) * charPhase L a b w) * ((Real.exp (-(t * charEigen L a b)) : ℝ) *
          latticeChar ![charAngle L a, charAngle L b] x)‖
      ≤ ((L : ℝ) ^ 2)⁻¹ * ∑ a ∈ range L, ∑ b ∈ range L,
          Real.exp (-(16 * t / (L : ℝ) ^ 2)) * ∑ w, |g w| := by
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum
          fun a ha => (norm_sum_le _ _).trans (Finset.sum_le_sum fun b hb => hterm a ha b hb)))
          (by positivity)
    _ = Real.exp (-(16 * t / (L : ℝ) ^ 2)) * ∑ w, |g w| := by
        rw [Finset.sum_const, Finset.sum_const, card_range, nsmul_eq_mul, nsmul_eq_mul,
          ← mul_assoc (L : ℝ) (L : ℝ), ← pow_two, ← mul_assoc, inv_mul_cancel₀ hL2.ne', one_mul]

/-- The representative `(w₁.val, w₂.val) ∈ {0, …, L-1}²` of a residue class modulo `L`. -/
def residueRep {L : ℕ} (w : ZMod L × ZMod L) : Vertex 2 := ![(w.1.val : ℤ), (w.2.val : ℤ)]

/-- **Dario, Lemma 3.2, Step 3, for periodic functions**: if `f` is `L`-periodic in both
directions with sum zero over `{0, …, L-1}²`, then `|Φ_t * f(x)| ≤ e^{-16t/L²} Σ_{period} |f|`. -/
theorem abs_tsum_openHeat_mul_periodic_le {L : ℕ} [NeZero L] {f : Vertex 2 → ℝ}
    (hper : ∀ y z : Vertex 2, (∀ i, (L : ℤ) ∣ y i - z i) → f y = f z)
    (h0 : ∑ w : ZMod L × ZMod L, f (residueRep w) = 0) {t : ℝ} (ht : 0 ≤ t) (x : Vertex 2) :
    |∑' y, openHeat (allOpen 2) t x y * f y| ≤
      Real.exp (-(16 * t / (L : ℝ) ^ 2)) * ∑ w : ZMod L × ZMod L, |f (residueRep w)| := by
  have key : ∀ a : ℤ, (L : ℤ) ∣ a - (((a : ZMod L)).val : ℤ) := fun a => by
    rw [ZMod.val_intCast]
    exact ⟨a / L, by have := Int.mul_ediv_add_emod a L; linarith⟩
  have hf : ∀ y, f y = f (residueRep ((y 0 : ZMod L), (y 1 : ZMod L))) := by
    intro y
    refine hper _ _ fun i => ?_
    fin_cases i
    · exact key (y 0)
    · exact key (y 1)
  have e : (fun y => openHeat (allOpen 2) t x y * f y) =
      fun y => openHeat (allOpen 2) t x y * f (residueRep ((y 0 : ZMod L), (y 1 : ZMod L))) :=
    funext fun y => by rw [← hf y]
  rw [e]
  exact abs_tsum_openHeat_mul_le (fun w => f (residueRep w)) h0 ht x

/-- **Dario, Lemma 3.2, Step 3, as used**: for `f` which is `3^k`-periodic with sum zero over a
period and `9^k ≤ r`, `|Φ_{r²} * f(x)| ≤ e^{-16 r} Σ_{period} |f|`. -/
theorem abs_tsum_openHeat_mul_periodic_le_exp {k : ℕ} {f : Vertex 2 → ℝ}
    (hper : ∀ y z : Vertex 2, (∀ i, ((3 ^ k : ℕ) : ℤ) ∣ y i - z i) → f y = f z)
    (h0 : ∑ w : ZMod (3 ^ k) × ZMod (3 ^ k), f (residueRep w) = 0) {r : ℝ} (hr : 0 < r)
    (hkr : (9 : ℝ) ^ k ≤ r) (x : Vertex 2) :
    |∑' y, openHeat (allOpen 2) (r ^ 2) x y * f y| ≤
      Real.exp (-(16 * r)) * ∑ w : ZMod (3 ^ k) × ZMod (3 ^ k), |f (residueRep w)| := by
  have h := abs_tsum_openHeat_mul_periodic_le hper h0 (sq_nonneg r) x
  refine h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_)
    (Finset.sum_nonneg fun w _ => abs_nonneg _))
  have hL : (((3 ^ k : ℕ) : ℝ)) ^ 2 = (9 : ℝ) ^ k := by
    push_cast
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [hL, neg_le_neg_iff, le_div_iff₀ (by positivity)]
  nlinarith

end Rigidity.Corrector
