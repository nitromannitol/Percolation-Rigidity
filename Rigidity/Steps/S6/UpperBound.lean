import Rigidity.Steps.S6.SlowMixing
import Rigidity.Proofs.S6.Fourier
import Rigidity.Proofs.S6.FiniteGroup
import Rigidity.External.SmoothingParameter

/-! Carving of step:6.5-upper (`UpperBoundStep`, single-exit form) into steps.

Paper: `paper/percolation-harmonic-corrected.tex` L2948-2951; the gap and its repair are recorded in
`Rigidity/Steps/S6/SlowMixing.lean`. The route is that of D. C. Jerison, L. Levine and J. Pike,
*Mixing time and eigenvalues of the abelian sandpile Markov chain* (arXiv 1511.00666), Proposition
3.6, Theorem 3.8, Theorem 4.1 and the proof of Theorem 4.3, run on the multigraph obtained by
wiring the outside of `V` into a sink, with the sink term controlled by the harmonicity at a site
with a single exit edge. The only literature input is `External.MicciancioRegevSmoothing`
(Micciancio-Regev Lemma 3.3 = JLP Lemma 4.2).

The wired graph has vertex set `V ∪ {sink}`, encoded as `Option V` (`none` is the sink). The
columns `b_x = Δ̃ e_x`, `x ∈ V`, of its Laplacian (`wiredColumn`) span the hyperplane `Σ y = 0`
of `ℝ^{V ∪ {sink}}`; the dual lattice of the lattice they generate parametrises the characters of
the sandpile group: `y ↦ ([f] ↦ e^{2πi Σ_x f(x) (y(x) - y(sink))})`.

Steps:
* `LatticeCorrespondenceStep`: every character is `[1_x] ↦ e^{2πiθ(x)}` with `Δ_V θ ∈ ℤ^V`.
* `PhaseBoundStep` (JLP (11), Theorem 3.8): a phase vector `θ` with `Δ_V θ ∈ ℤ^V` is represented
  by a dual lattice point `y` with `‖y‖² ≤ C m (1 - |λ_θ|)`, given a site with one exit edge.
* `WiredLaplacianStep`: for `V ⊂ 𝒞_∞` the columns `b_x` are linearly independent and span
  `Σ y = 0`.

Proved here: the column bound `‖b_x‖ ≤ 3d + 1` (`norm_wiredColumn_le`), the transfer of
`MicciancioRegevSmoothing` to finite index types (`smoothing_of_fintype`), and the summation over
characters (`upperBound_of_steps`, JLP Theorem 4.1 and the proof of Theorem 4.3), using the proved
`fourierStep` and `finiteGroupStep`. -/

open LatticeProb.Percolation Rigidity.Section6 Classical

namespace Rigidity.Steps.S6

variable {d : ℕ}

/-! ### Objects -/

/-- The column at `x ∈ V` of the Laplacian of the wired graph `V ∪ {sink}` (`none` is the sink):
`deg(x)` at `x`, `-1` at each open neighbour of `x` in `V`, and minus the number of open edges
leaving `V` at `x` at the sink. -/
noncomputable def wiredColumn (ω : Configuration d) (V : Finset (Vertex d)) (x : V) :
    EuclideanSpace ℝ (Option V) :=
  WithLp.toLp 2 fun o => Option.elim o (-((exitNeighbors ω V x).card : ℝ)) fun y =>
    if y = x then ((openGraph ω).degree x.val : ℝ)
    else if (openGraph ω).Adj x.val y.val then -1 else 0

@[simp]
theorem wiredColumn_none (ω : Configuration d) (V : Finset (Vertex d)) (x : V) :
    wiredColumn ω V x none = -((exitNeighbors ω V x).card : ℝ) :=
  rfl

@[simp]
theorem wiredColumn_some (ω : Configuration d) (V : Finset (Vertex d)) (x y : V) :
    wiredColumn ω V x (some y) = if y = x then ((openGraph ω).degree x.val : ℝ)
      else if (openGraph ω).Adj x.val y.val then -1 else 0 :=
  rfl

/-- The toppling Laplacian `Δ_V` acting on real functions on `V`. -/
noncomputable def realToppling (ω : Configuration d) (V : Finset (Vertex d)) (θ : V → ℝ)
    (x : V) : ℝ :=
  ((openGraph ω).degree x.val : ℝ) * θ x -
    ∑ y : V, if (openGraph ω).Adj x.val y.val then θ y else 0

/-- `λ_θ = |V|⁻¹ Σ_{x ∈ V} e^{2πiθ(x)}`: the eigenvalue of the chain at the character with
phases `θ`. -/
noncomputable def phaseEigenvalue (V : Finset (Vertex d)) (θ : V → ℝ) : ℂ :=
  (V.card : ℂ)⁻¹ * ∑ x : V, Complex.exp (((2 * Real.pi * θ x : ℝ) : ℂ) * Complex.I)

/-- The dual of the lattice generated over ℤ by `b`, inside the real span of `b`, for arbitrary finite
index types (`External.dualLattice` is the case of `Fin k` vectors in `ℝ^{Fin N}`). -/
def dualLatticeOf {ι κ : Type*} [Fintype ι] (b : κ → EuclideanSpace ℝ ι) :
    Set (EuclideanSpace ℝ ι) :=
  {y | y ∈ Submodule.span ℝ (Set.range b) ∧ ∀ i, ∃ z : ℤ, inner ℝ y (b i) = z}

/-! ### Steps -/

/-- step:6.5-upper, characters (JLP Section 3, multiplicative harmonic functions): a character
of the finite sandpile group is `[1_x] ↦ e^{2πiθ(x)}` for a phase vector `θ : V → ℝ` with
`Δ_V θ ∈ ℤ^V`. (`|χ| = 1` on a finite group; `χ` kills `[Δ_V 1_x]`, and `Δ_V` is symmetric.) -/
def LatticeCorrespondenceStep (d : ℕ) : Prop :=
  ∀ (ω : Configuration d) (V : Finset (Vertex d)), Finite (SandpileGroup ω V) →
    ∀ χ : AddChar (SandpileGroup ω V) ℂ, ∃ θ : V → ℝ,
      (∀ x, χ (chip ω V x) = Complex.exp (((2 * Real.pi * θ x : ℝ) : ℂ) * Complex.I)) ∧
        ∀ x, ∃ k : ℤ, realToppling ω V θ x = k

/-- step:6.5-upper, phase bound (JLP (11) and Theorem 3.8, single-exit form). Let some site `w`
of `V` have exactly one open edge leaving `V`, and `Δ_V θ ∈ ℤ^V`. Write `λ_θ = r e^{2πiτ}`,
`|τ| ≤ 1/2`, and `θ ≡ τ + z` mod `ℤ^V` with `|z(x)| ≤ 1/2`; then `1 - r ≥ 8|z|²/m`
(`1 - cos 2πz ≥ 8z²`), the harmonicity at `w` gives `τ + (deg(w) z(w) - Σ_{u ∈ V, u ∼ w} z(u)) ∈ ℤ`,
so `|τ| ≤ 4d|z|`, and the orthogonal projection `y` of `(τ + z, 0)` onto `Σ y = 0` has
`‖y‖² ≤ ‖(z, -τ)‖² ≤ (1 + 16d²)|z|²`. The point `y` is in the dual lattice of the wired columns
and represents `θ`: `y(x) - y(sink) ≡ θ(x)` mod `1`. -/
def PhaseBoundStep (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (ω : Configuration d) (V : Finset (Vertex d)),
    (∃ x ∈ V, (exitNeighbors ω V x).card = 1) → ∀ θ : V → ℝ,
      (∀ x, ∃ k : ℤ, realToppling ω V θ x = k) →
      ∃ y : EuclideanSpace ℝ (Option V), ∑ o, y o = 0 ∧
        (∀ x, ∃ k : ℤ, inner ℝ y (wiredColumn ω V x) = k) ∧
        (∀ x, ∃ k : ℤ, y (some x) - y none = θ x + k) ∧
        ‖y‖ ^ 2 ≤ C * V.card * (1 - ‖phaseEigenvalue V θ‖)

/-- step:6.5-upper, wired Laplacian (paper L2829-2830): for a finite `V ⊂ 𝒞_∞`, `Δ_V` is
nonsingular (every cluster of `V` has an open edge leaving `V`), so the wired columns are
linearly independent; they lie in the hyperplane `Σ y = 0`, of dimension `|V|`, hence span it. -/
def WiredLaplacianStep (d : ℕ) : Prop :=
  ∀ (ω : Configuration d) (h : HasUniqueInfiniteOpenComponent ω) (V : Finset (Vertex d)),
    (∀ x ∈ V, x ∈ (uniqueInfiniteComponent h).supp) →
      LinearIndependent ℝ (wiredColumn ω V) ∧
        ∀ y : EuclideanSpace ℝ (Option V), ∑ o, y o = 0 →
          y ∈ Submodule.span ℝ (Set.range (wiredColumn ω V))

/-! ### Proved ingredients -/

/-- `‖b_x‖² = e(x)² + deg(x)² + #{u ∈ V : u ∼ x} ≤ 2 deg(x)² ≤ 8d²`. -/
theorem norm_wiredColumn_le (ω : Configuration d) (V : Finset (Vertex d)) (x : V) :
    ‖wiredColumn ω V x‖ ≤ 3 * d + 1 := by
  classical
  have hsum : ∀ y : V, (wiredColumn ω V x (some y)) ^ 2 =
      (if y = x then ((openGraph ω).degree x.val : ℝ) ^ 2 else 0) +
        if (openGraph ω).Adj x.val y.val then 1 else 0 := by
    intro y
    rw [wiredColumn_some]
    by_cases hy : y = x
    · have ha : ¬ (openGraph ω).Adj x.val y.val := by
        rw [hy]
        exact (openGraph ω).loopless.irrefl _
      rw [if_pos hy, if_pos hy, if_neg ha]
      ring
    · by_cases ha : (openGraph ω).Adj x.val y.val <;> simp [hy, ha]
  set D := (openGraph ω).degree x.val with hDdef
  set e := (exitNeighbors ω V x).card with hedef
  set A := (Finset.univ.filter fun y : V => (openGraph ω).Adj x.val y.val).card with hAdef
  have hcount : e + A ≤ D := by
    have h1 : A ≤ (((openGraph ω).neighborFinset x.val).filter (· ∈ V)).card :=
      Finset.card_le_card_of_injOn Subtype.val (fun y hy => by
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hy
        simp [SimpleGraph.mem_neighborFinset, hy]) Subtype.val_injective.injOn
    have h2 := Finset.card_filter_add_card_filter_not
      (s := (openGraph ω).neighborFinset x.val) (· ∈ V)
    rw [SimpleGraph.card_neighborFinset_eq_degree] at h2
    simp only [hedef, exitNeighbors]
    omega
  have hD : D ≤ 2 * d := openGraph_degree_le ω x.val
  have hsq : ‖wiredColumn ω V x‖ ^ 2 = (e : ℝ) ^ 2 + (D : ℝ) ^ 2 + A := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_option]
    simp only [Real.norm_eq_abs, sq_abs, hsum, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.sum_boole, wiredColumn_none, neg_sq]
    ring
  have hle : ‖wiredColumn ω V x‖ ^ 2 ≤ (3 * d + 1 : ℝ) ^ 2 := by
    rw [hsq]
    have h1 : (e : ℝ) + A ≤ D := by exact_mod_cast hcount
    have h2 : (D : ℝ) ≤ 2 * d := by exact_mod_cast hD
    have h3 : (A : ℝ) ≤ (A : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos A with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ A := by exact_mod_cast h
        nlinarith
    have he : (0 : ℝ) ≤ e := Nat.cast_nonneg _
    have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg _
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hle

/-- `External.MicciancioRegevSmoothing` for vectors indexed by a finite type `κ` in
`ℝ^ι`, `ι` finite: transport along `ι ≃ Fin N`, `κ ≃ Fin k`. -/
theorem smoothing_of_fintype (hMR : External.MicciancioRegevSmoothing) {ι κ : Type*} [Fintype ι]
    [Fintype κ] (b : κ → EuclideanSpace ℝ ι) (hb : LinearIndependent ℝ b) (r : ℝ)
    (hr : ∀ i, ‖b i‖ ≤ r) (ε : ℝ) (hε : 0 < ε) (s : ℝ)
    (hs : Real.sqrt (Real.log (2 * Fintype.card κ * (1 + 1 / ε)) / Real.pi) * r ≤ s) :
    Summable (fun y : {y // y ∈ dualLatticeOf b ∧ y ≠ 0} =>
        Real.exp (-(Real.pi * s ^ 2 * ‖(y : EuclideanSpace ℝ ι)‖ ^ 2))) ∧
      ∑' y : {y // y ∈ dualLatticeOf b ∧ y ≠ 0},
        Real.exp (-(Real.pi * s ^ 2 * ‖(y : EuclideanSpace ℝ ι)‖ ^ 2)) ≤ ε := by
  classical
  set eκ := Fintype.equivFin κ
  set L := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin ι)
  set b' : Fin (Fintype.card κ) → EuclideanSpace ℝ (Fin (Fintype.card ι)) :=
    fun j => L (b (eκ.symm j)) with hb'def
  have hb' : LinearIndependent ℝ b' :=
    (hb.comp _ eκ.symm.injective).map' L.toLinearEquiv.toLinearMap L.toLinearEquiv.ker
  obtain ⟨hsum, hle⟩ := hMR _ _ b' hb' r (fun j => (L.norm_map _).trans_le (hr _)) ε hε s hs
  have hrange : Set.range b' = L '' Set.range b := by
    ext v
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨b (eκ.symm j), ⟨_, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨eκ i, by simp [hb'def]⟩
  have hmem : ∀ y, y ∈ dualLatticeOf b ∧ y ≠ 0 ↔ L y ∈ External.dualLattice b' ∧ L y ≠ 0 := by
    intro y
    have hspan : L y ∈ Submodule.span ℝ (Set.range b') ↔ y ∈ Submodule.span ℝ (Set.range b) := by
      rw [hrange, ← LinearIsometryEquiv.coe_toLinearEquiv, ← LinearEquiv.coe_toLinearMap,
        Submodule.span_image, Submodule.mem_map_equiv]
      simp
    have hinner : (∀ j, ∃ z : ℤ, inner ℝ (L y) (b' j) = z) ↔ ∀ i, ∃ z : ℤ, inner ℝ y (b i) = z := by
      simp only [hb'def, LinearIsometryEquiv.inner_map_map]
      constructor
      · intro h i
        simpa using h (eκ i)
      · intro h j
        exact h _
    simp only [dualLatticeOf, External.dualLattice, Set.mem_setOf_eq, hspan, hinner,
      ne_eq, LinearIsometryEquiv.map_eq_zero_iff]
  let E : {y // y ∈ dualLatticeOf b ∧ y ≠ 0} ≃ {y // y ∈ External.dualLattice b' ∧ y ≠ 0} :=
    L.toEquiv.subtypeEquiv hmem
  have hcomp : (fun y : {y // y ∈ External.dualLattice b' ∧ y ≠ 0} =>
      Real.exp (-(Real.pi * s ^ 2 * ‖(y : EuclideanSpace ℝ (Fin (Fintype.card ι)))‖ ^ 2))) ∘ E =
      fun y : {y // y ∈ dualLatticeOf b ∧ y ≠ 0} =>
        Real.exp (-(Real.pi * s ^ 2 * ‖(y : EuclideanSpace ℝ ι)‖ ^ 2)) := by
    funext y
    simp only [Function.comp_apply]
    rw [show ((E y : _) : EuclideanSpace ℝ (Fin (Fintype.card ι))) = L y from rfl, L.norm_map]
  refine ⟨?_, ?_⟩
  · rw [← hcomp]
    exact E.summable_iff.2 hsum
  · rw [← hcomp]
    exact (E.tsum_eq (fun y : {y // y ∈ External.dualLattice b' ∧ y ≠ 0} =>
      Real.exp (-(Real.pi * s ^ 2 * ‖(y : EuclideanSpace ℝ (Fin (Fintype.card ι)))‖ ^ 2)))).trans_le
      hle

/-- Characters of the sandpile group agreeing on the chips `[1_x]` are equal. -/
theorem addChar_ext_chip {ω : Configuration d} {V : Finset (Vertex d)}
    {χ ψ : AddChar (SandpileGroup ω V) ℂ} (h : ∀ x, χ (chip ω V x) = ψ (chip ω V x)) : χ = ψ := by
  classical
  ext g
  induction g using QuotientAddGroup.induction_on with
  | H f =>
    have hf : (QuotientAddGroup.mk f : SandpileGroup ω V) = ∑ x, f x • chip ω V x := by
      have hsingle : ∀ x, Pi.single x (f x) = f x • (Pi.single x 1 : V → ℤ) := by
        intro x
        ext y
        by_cases hy : y = x
        · subst hy
          simp
        · simp [hy]
      conv_lhs => rw [← Finset.univ_sum_single f]
      simp only [hsingle, chip]
      rw [← QuotientAddGroup.mk'_apply, map_sum]
      simp
    rw [hf, Proofs.S6.addChar_map_sum_eq_prod, Proofs.S6.addChar_map_sum_eq_prod]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [AddChar.map_zsmul_eq_zpow, AddChar.map_zsmul_eq_zpow, h x]

/-- `e^{2πi(a + k)} = e^{2πia}` for an integer `k`. -/
theorem cexp_two_pi_add_int (a : ℝ) (k : ℤ) :
    Complex.exp (((2 * Real.pi * (a + k) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((2 * Real.pi * a : ℝ) : ℂ) * Complex.I) := by
  have : (((2 * Real.pi * (a + k) : ℝ) : ℂ) * Complex.I) =
      ((2 * Real.pi * a : ℝ) : ℂ) * Complex.I + k * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `a^{2t} ≤ e^{-2t(1-a)}` for `0 ≤ a`. -/
theorem pow_two_mul_le_exp {a : ℝ} (ha : 0 ≤ a) (t : ℕ) :
    a ^ (2 * t) ≤ Real.exp (-(2 * t * (1 - a))) := by
  calc a ^ (2 * t) ≤ Real.exp (a - 1) ^ (2 * t) := by
        refine pow_le_pow_left₀ ha ?_ _
        linarith [Real.add_one_le_exp (a - 1)]
    _ = Real.exp (-(2 * t * (1 - a))) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring

/-! ### Assembly -/

/-- step:6.5-upper (single-exit form) from its steps and Micciancio-Regev: JLP Theorem 4.1 and
the proof of Theorem 4.3. By `fourierStep`, `‖P^t - U‖₂² = Σ_{χ ≠ 1} |λ_χ|^{2t}`; each `χ ≠ 1`
gives a nonzero dual lattice point `y_χ` (injectively) with `|λ_χ|^{2t} ≤ e^{-2t(1 - |λ_χ|)}
≤ e^{-π s² ‖y_χ‖²}`, `π s² = (3d + 1)² log(2m(1 + 1/ε))`, and the Gaussian sum over the nonzero
dual lattice points is at most `ε` (columns of norm `≤ 3d + 1`). -/
theorem upperBound_of_steps (hMR : External.MicciancioRegevSmoothing)
    (hLC : LatticeCorrespondenceStep d) (hPB : PhaseBoundStep d) (hWL : WiredLaplacianStep d) :
    UpperBoundStep d := by
  obtain ⟨C, hC, hPB⟩ := hPB
  refine ⟨C * (3 * d + 1) ^ 2 / 2, by positivity, ?_⟩
  intro ω h n V hV hexit ε hε t ht
  classical
  obtain ⟨w, hwV, hw⟩ := hexit
  have hVne : V.Nonempty := ⟨w, hwV⟩
  have hfin : Finite (SandpileGroup ω V) := Proofs.S6.finiteGroupStep ω h V hV.2.1
  letI : Fintype (SandpileGroup ω V) := Fintype.ofFinite _
  rw [Proofs.S6.fourierStep ω V hVne hfin t]
  obtain ⟨hli, hspan⟩ := hWL ω h V hV.2.1
  set m : ℕ := V.card with hmdef
  have hm : (0 : ℝ) < m := by exact_mod_cast hVne.card_pos
  -- each character gives a dual lattice point
  have key : ∀ χ : AddChar (SandpileGroup ω V) ℂ, ∃ y : EuclideanSpace ℝ (Option V),
      y ∈ dualLatticeOf (wiredColumn ω V) ∧
      (∀ x, χ (chip ω V x) =
        Complex.exp (((2 * Real.pi * (y (some x) - y none) : ℝ) : ℂ) * Complex.I)) ∧
      ‖y‖ ^ 2 ≤ C * m * (1 - ‖chainEigenvalue ω V χ‖) := by
    intro χ
    obtain ⟨θ, hχ, hθ⟩ := hLC ω V hfin χ
    obtain ⟨y, hy0, hyint, hyθ, hyn⟩ := hPB ω V ⟨w, hwV, hw⟩ θ hθ
    refine ⟨y, ⟨hspan y hy0, hyint⟩, fun x => ?_, ?_⟩
    · obtain ⟨k, hk⟩ := hyθ x
      rw [hχ x, hk, cexp_two_pi_add_int]
    · have : chainEigenvalue ω V χ = phaseEigenvalue V θ := by
        simp only [chainEigenvalue, phaseEigenvalue, hχ]
      rwa [this]
  choose Φ hΦmem hΦchip hΦnorm using key
  have hΦinj : Function.Injective Φ := by
    intro χ ψ hχψ
    exact addChar_ext_chip fun x => by rw [hΦchip χ x, hΦchip ψ x, hχψ]
  have hΦne : ∀ χ, χ ≠ 1 → Φ χ ≠ 0 := by
    intro χ hχ h0
    refine hχ (addChar_ext_chip fun x => ?_)
    rw [hΦchip χ x, h0, AddChar.one_apply]
    simp
  -- the scale
  set L : ℝ := Real.log (2 * m * (1 + 1 / ε)) with hLdef
  have hL : 0 ≤ L := by
    refine Real.log_nonneg ?_
    have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hVne.card_pos
    have h2 : (0 : ℝ) ≤ 1 / ε := by positivity
    nlinarith
  set s : ℝ := Real.sqrt (L / Real.pi) * (3 * d + 1) with hsdef
  have hps : Real.pi * s ^ 2 = L * (3 * d + 1) ^ 2 := by
    rw [hsdef, mul_pow, Real.sq_sqrt (div_nonneg hL Real.pi_pos.le)]
    field_simp
  have hps2 : Real.pi * s ^ 2 * (C * m) ≤ 2 * t := by
    rw [hps]
    have : C * (3 * d + 1) ^ 2 / 2 * m * L ≤ t := ht
    nlinarith
  obtain ⟨hsum, hle⟩ := smoothing_of_fintype hMR (wiredColumn ω V) hli (3 * d + 1)
    (norm_wiredColumn_le ω V) ε hε s (by rw [Fintype.card_coe])
  set F : {y // y ∈ dualLatticeOf (wiredColumn ω V) ∧ y ≠ 0} → ℝ :=
    fun y => Real.exp (-(Real.pi * s ^ 2 * ‖(y : EuclideanSpace ℝ (Option V))‖ ^ 2)) with hFdef
  let g : {χ : AddChar (SandpileGroup ω V) ℂ // χ ≠ 1} →
      {y // y ∈ dualLatticeOf (wiredColumn ω V) ∧ y ≠ 0} :=
    fun χ => ⟨Φ χ, hΦmem χ, hΦne χ χ.2⟩
  have hginj : Function.Injective g := by
    intro χ ψ hχψ
    exact Subtype.ext (hΦinj (congrArg Subtype.val hχψ))
  have hterm : ∀ χ : {χ : AddChar (SandpileGroup ω V) ℂ // χ ≠ 1},
      ‖chainEigenvalue ω V χ‖ ^ (2 * t) ≤ F (g χ) := by
    intro χ
    have hn := hΦnorm χ
    have h1 : 0 ≤ 1 - ‖chainEigenvalue ω V χ‖ := by
      have : 0 ≤ C * m * (1 - ‖chainEigenvalue ω V χ‖) := (sq_nonneg _).trans hn
      exact nonneg_of_mul_nonneg_right this (by positivity)
    refine (pow_two_mul_le_exp (norm_nonneg _) t).trans (Real.exp_le_exp.2 ?_)
    have hs0 : 0 ≤ Real.pi * s ^ 2 := by positivity
    have : Real.pi * s ^ 2 * ‖Φ χ‖ ^ 2 ≤ 2 * t * (1 - ‖chainEigenvalue ω V χ‖) :=
      calc Real.pi * s ^ 2 * ‖Φ χ‖ ^ 2
          ≤ Real.pi * s ^ 2 * (C * m * (1 - ‖chainEigenvalue ω V χ‖)) :=
            mul_le_mul_of_nonneg_left hn hs0
        _ = Real.pi * s ^ 2 * (C * m) * (1 - ‖chainEigenvalue ω V χ‖) := by ring
        _ ≤ 2 * t * (1 - ‖chainEigenvalue ω V χ‖) := mul_le_mul_of_nonneg_right hps2 h1
    simpa [hFdef, g] using this
  simp_rw [finsum_eq_if]
  rw [finsum_eq_sum_of_fintype, ← Finset.sum_filter,
    Finset.sum_subtype (Finset.univ.filter fun χ : AddChar (SandpileGroup ω V) ℂ => χ ≠ 1)
      (p := fun χ => χ ≠ 1) (by simp)]
  calc ∑ χ : {χ : AddChar (SandpileGroup ω V) ℂ // χ ≠ 1}, ‖chainEigenvalue ω V χ‖ ^ (2 * t)
      ≤ ∑ χ : {χ : AddChar (SandpileGroup ω V) ℂ // χ ≠ 1}, F (g χ) :=
        Finset.sum_le_sum fun χ _ => hterm χ
    _ = ∑' χ : {χ : AddChar (SandpileGroup ω V) ℂ // χ ≠ 1}, (F ∘ g) χ :=
        (tsum_fintype _).symm
    _ ≤ ∑' y, F y := tsum_comp_le_tsum_of_inj hsum (fun _ => (Real.exp_pos _).le) hginj
    _ ≤ ε := hle

end Rigidity.Steps.S6
