import Rigidity.Steps.Section5.RenormalizedDomination
import LatticeProb.Prob.Percolation.LSSThinVacuity

/-!
# Lemma 5.23, step `step:5.23-domination`: domination of a `1`-dependent planar field

This file proves `Rigidity.Steps.Section5.OneDependentDominationStep`: a `1`-dependent field on
`ℤ²` (for the `ℓ^∞` distance, dependency graph of degree `Δ = 8`) whose sites are closed with
probability at most `ε` dominates on increasing events the product Bernoulli field of every
density `q ≤ (1 - 4 ε^(1/16))₊`.  This is Theorem 1.3 of Liggett, Schonmann and Stacey,
*Domination by product measures*, Ann. Probab. 25 (1997), with explicit non-optimal constants;
no literature input is used.

The proof follows the LSS argument.

* Thinning (`thin_claim`): let `Y` be an independent product Bernoulli field of density `α` and
  `Z = X ∧ Y`.  For `v ∉ W` and every pattern `ζ` of `Z` on `W`,
  `P[X_v = 0, Z_W = ζ] ≤ δ P[Z_W = ζ]`, by strong induction on `W`: split `W` into the
  `ℓ^∞`-neighbours `N` of `v` (at most `8`) and the far sites `F`; `1`-dependence gives
  `P[X_v = 0, Z_W = ζ] ≤ ε P[Z_F = ζ_F]`, and the thinning gives
  `P[Z_W = ζ] ≥ (1 - α)^8 (1 - 8δ) P[Z_F = ζ_F]` by the induction hypothesis on `F`.  The field
  `Y` is integrated out: `P[Z_W = ζ | X] = ∏_{w ∈ W} P[X_w ∧ Y_w = ζ_w]` (`thinWeight`).
* Sequential domination on finite volumes (`lintegral_bitProduct_le`): the conditional
  probabilities `P[Z_v = 1 | Z_W = ζ] ≥ α (1 - δ)` give, by induction on the finite set of sites,
  `∫ f d(Bernoulli q) ≤ ∫ f dZ` for every nondecreasing `f` of finitely many sites.
* Extension to all measurable increasing events (`denseLower_of_finite`): inner regularity of
  the product Bernoulli field and compactness of `{0,1}^{ℤ²}`.
* `Z ≤ X` pointwise, so the law of `Z` is below the law `ν` of `X` on increasing events.
-/

open MeasureTheory ProbabilityTheory LatticeProb.Percolation
open scoped ENNReal

namespace Rigidity.Proofs.Section5

namespace LSSDomination

variable {S : Type} [DecidableEq S]

/-- The cylinder event of the configurations that agree with the pattern `ζ` on `W`. -/
def cyl (W : Finset S) (ζ : S → Bool) : Set (S → Bool) := {ω | ∀ w ∈ W, ω w = ζ w}

omit [DecidableEq S] in
theorem measurableSet_coord (v : S) (b : Bool) : MeasurableSet {ω : S → Bool | ω v = b} :=
  measurableSet_eq_fun (measurable_pi_apply v) measurable_const

omit [DecidableEq S] in
theorem indicator_coord_of {x : S → Bool} {v : S} {b : Bool} (h : x v = b) (f : (S → Bool) → ℝ≥0∞) :
    {x : S → Bool | x v = b}.indicator f x = f x :=
  Set.indicator_of_mem (show x ∈ {x : S → Bool | x v = b} from h) f

omit [DecidableEq S] in
theorem indicator_coord_of_ne {x : S → Bool} {v : S} {b : Bool} (h : ¬ x v = b)
    (f : (S → Bool) → ℝ≥0∞) : {x : S → Bool | x v = b}.indicator f x = 0 :=
  Set.indicator_of_notMem (show x ∉ {x : S → Bool | x v = b} from h) f

omit [DecidableEq S] in
theorem measurableSet_cyl (W : Finset S) (ζ : S → Bool) : MeasurableSet (cyl W ζ) := by
  have : cyl W ζ = ⋂ w ∈ W, {ω : S → Bool | ω w = ζ w} := by ext ω; simp [cyl]
  rw [this]
  exact Finset.measurableSet_biInter W fun w _ => measurableSet_coord w (ζ w)

/-- The extension by `false` of a pattern on a finite set. -/
def extendFalse (I : Finset S) (u : I → Bool) : S → Bool :=
  fun s => if h : s ∈ I then u ⟨s, h⟩ else false

theorem dependsOn_eq_comp {β : Type*} {I : Finset S} {f : (S → Bool) → β}
    (hf : DependsOn f (I : Set S)) :
    f = (fun u => f (extendFalse I u)) ∘ (fun ω (i : I) => ω i) := by
  funext ω
  exact hf fun i hi => by simp [extendFalse, Finset.mem_coe.mp hi]

theorem measurable_of_dependsOn {β : Type*} [MeasurableSpace β] {I : Finset S}
    {f : (S → Bool) → β} (hf : DependsOn f (I : Set S)) : Measurable f := by
  rw [dependsOn_eq_comp hf]
  exact (measurable_of_finite _).comp (measurable_pi_lambda _ fun i => measurable_pi_apply _)

/-- Independence of the restrictions to `I` and `J` factorizes the integral of the product of a
function of the sites of `I` with a function of the sites of `J`. -/
theorem lintegral_mul_of_indepFun {μ : Measure (S → Bool)} {I J : Finset S}
    (hind : IndepFun (fun ω (i : I) => ω i) (fun ω (j : J) => ω j) μ)
    {f g : (S → Bool) → ℝ≥0∞} (hf : DependsOn f (I : Set S)) (hg : DependsOn g (J : Set S)) :
    ∫⁻ ω, f ω * g ω ∂μ = (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, g ω ∂μ := by
  have h := hind.comp (measurable_of_finite (fun u : I → Bool => f (extendFalse I u)))
    (measurable_of_finite (fun u : J → Bool => g (extendFalse J u)))
  rw [← dependsOn_eq_comp hf, ← dependsOn_eq_comp hg] at h
  exact lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (measurable_of_dependsOn hf)
    (measurable_of_dependsOn hg) h

/-- The pattern of a finite set `T`: its indicator function. -/
def pat (T : Finset S) : S → Bool := fun s => decide (s ∈ T)

/-- A function of the sites of `W` is the sum over the patterns of `W` of its values times the
indicators of the corresponding cylinder events. -/
theorem eq_sum_cyl {W : Finset S} {h : (S → Bool) → ℝ≥0∞} (hh : DependsOn h (W : Set S))
    (ω : S → Bool) :
    h ω = ∑ T ∈ W.powerset, (cyl W (pat T)).indicator (fun _ => h (pat T)) ω := by
  rw [Finset.sum_eq_single (W.filter fun s => ω s = true)]
  · have hmem : ω ∈ cyl W (pat (W.filter fun s => ω s = true)) := by
      intro w hw
      cases hωw : ω w <;> simp [pat, hw, hωw]
    rw [Set.indicator_of_mem hmem]
    exact hh fun w hw => hmem w hw
  · intro T hT hne
    refine Set.indicator_of_notMem (fun hmem => hne ?_) _
    ext s
    simp only [Finset.mem_filter]
    constructor
    · intro hs
      have hsW := Finset.mem_powerset.mp hT hs
      refine ⟨hsW, ?_⟩
      simpa [pat, hs] using hmem s hsW
    · rintro ⟨hsW, hωs⟩
      have := hmem s hsW
      simpa [pat, hωs] using this
  · intro hn
    exact absurd (Finset.mem_powerset.mpr (Finset.filter_subset _ _)) hn

/-- The cylinder lower bound on the conditional probabilities of an open site, integrated
against a nonnegative function of the sites of `W`. -/
theorem cond_lintegral {μ : Measure (S → Bool)} {q : ℝ≥0∞}
    (hcond : ∀ (W : Finset S) (v : S), v ∉ W → ∀ ζ : S → Bool,
      q * μ (cyl W ζ) ≤ μ (cyl W ζ ∩ {ω | ω v = true}))
    {W : Finset S} {v : S} (hv : v ∉ W) {h : (S → Bool) → ℝ≥0∞}
    (hh : DependsOn h (W : Set S)) :
    q * ∫⁻ ω, h ω ∂μ ≤ ∫⁻ ω, {ω | ω v = true}.indicator h ω ∂μ := by
  have hind : ∀ ω, {ω | ω v = true}.indicator h ω = ∑ T ∈ W.powerset,
      (cyl W (pat T) ∩ {ω | ω v = true}).indicator (fun _ => h (pat T)) ω := by
    intro ω
    by_cases hω : ω v = true
    · rw [Set.indicator_of_mem (show ω ∈ {ω : S → Bool | ω v = true} from hω), eq_sum_cyl hh ω]
      refine Finset.sum_congr rfl fun T _ => ?_
      by_cases hc : ω ∈ cyl W (pat T)
      · rw [Set.indicator_of_mem hc, Set.indicator_of_mem (Set.mem_inter hc hω)]
      · rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem fun hm => hc hm.1]
    · rw [Set.indicator_of_notMem (show ω ∉ {ω : S → Bool | ω v = true} from hω)]
      exact (Finset.sum_eq_zero fun T _ => Set.indicator_of_notMem (fun hm => hω hm.2) _).symm
  have h1 : ∫⁻ ω, h ω ∂μ = ∑ T ∈ W.powerset, h (pat T) * μ (cyl W (pat T)) := by
    rw [lintegral_congr fun ω => eq_sum_cyl hh ω, lintegral_finsetSum _ fun T _ =>
      measurable_const.indicator (measurableSet_cyl W _)]
    exact Finset.sum_congr rfl fun T _ => lintegral_indicator_const (measurableSet_cyl W _) _
  have h2 : ∫⁻ ω, {ω | ω v = true}.indicator h ω ∂μ =
      ∑ T ∈ W.powerset, h (pat T) * μ (cyl W (pat T) ∩ {ω | ω v = true}) := by
    rw [lintegral_congr hind, lintegral_finsetSum _ fun T _ =>
      measurable_const.indicator ((measurableSet_cyl W _).inter (measurableSet_coord v true))]
    exact Finset.sum_congr rfl fun T _ =>
      lintegral_indicator_const ((measurableSet_cyl W _).inter (measurableSet_coord v true)) _
  rw [h1, h2, Finset.mul_sum]
  refine Finset.sum_le_sum fun T _ => ?_
  rw [mul_left_comm]
  gcongr
  exact hcond W v hv _

omit [DecidableEq S] in
theorem bitProduct_coord (p : NNReal) (hp : p ≤ 1) (v : S) (b : Bool) :
    bitProduct p hp S {ω | ω v = b} = bernoulli p hp {b} := by
  have : {ω : S → Bool | ω v = b} = Set.pi (({v} : Finset S) : Set S) (fun _ => {b}) := by
    ext ω; simp
  rw [this, bitProduct, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _),
    Finset.prod_singleton]

theorem bernoulli_true (p : NNReal) (hp : p ≤ 1) : bernoulli p hp {true} = p := by
  have h := bernoulliFieldPlanar_oneSite p hp (0, 0)
  rw [bernoulliFieldPlanar, bitProduct_coord] at h
  rw [h, ENNReal.ofReal_coe_nnreal]

theorem bernoulli_false (p : NNReal) (hp : p ≤ 1) : bernoulli p hp {false} = 1 - (p : ℝ≥0∞) := by
  have hc : ({false} : Set Bool) = {true}ᶜ := by ext b; cases b <;> simp
  rw [hc, prob_compl_eq_one_sub (measurableSet_singleton _), bernoulli_true]

theorem dependsOn_update {β : Type*} {Λ : Finset S} {v : S} {f : (S → Bool) → β}
    (hf : DependsOn f ((insert v Λ : Finset S) : Set S)) (b : Bool) :
    DependsOn (fun ω => f (Function.update ω v b)) (Λ : Set S) := by
  intro x y hxy
  apply hf
  intro i hi
  by_cases hiv : i = v
  · subst hiv; simp
  · rw [Function.update_of_ne hiv, Function.update_of_ne hiv]
    exact hxy i (by simpa [hiv] using hi)

/-- Under the product Bernoulli field, a function of the sites of `insert v Λ` integrates as the
mixture of its two sections at `v`. -/
theorem lintegral_bitProduct_split (q : NNReal) (hq : q ≤ 1) {Λ : Finset S} {v : S} (hv : v ∉ Λ)
    {f : (S → Bool) → ℝ≥0∞} (hf : DependsOn f ((insert v Λ : Finset S) : Set S)) :
    ∫⁻ ω, f ω ∂(bitProduct q hq S) =
      (1 - (q : ℝ≥0∞)) * ∫⁻ ω, f (Function.update ω v false) ∂(bitProduct q hq S) +
        (q : ℝ≥0∞) * ∫⁻ ω, f (Function.update ω v true) ∂(bitProduct q hq S) := by
  have hdep := dependsOn_update hf
  have hind : IndepFun (fun ω (i : ({v} : Finset S)) => ω i) (fun ω (j : Λ) => ω j)
      (bitProduct q hq S) :=
    (iIndepFun_infinitePi (X := fun _ (a : Bool) => a) (fun _ => measurable_id)).indepFun_finset
      {v} Λ (Finset.disjoint_singleton_left.mpr hv) (fun i => measurable_pi_apply i)
  have hcoord : ∀ b, DependsOn ({ω : S → Bool | ω v = b}.indicator (1 : (S → Bool) → ℝ≥0∞))
      (({v} : Finset S) : Set S) := by
    intro b x y hxy
    have : x v = y v := hxy v (by simp)
    simp [Set.indicator_apply, this]
  have hpt : ∀ ω, f ω = {ω : S → Bool | ω v = false}.indicator 1 ω * f (Function.update ω v false)
      + {ω : S → Bool | ω v = true}.indicator 1 ω * f (Function.update ω v true) := by
    intro ω
    have h0 : Function.update ω v (ω v) = ω := Function.update_eq_self v ω
    cases hω : ω v <;> rw [hω] at h0 <;> simp [hω, h0]
  have hmeas : Measurable fun ω : S → Bool =>
      {ω : S → Bool | ω v = false}.indicator (1 : (S → Bool) → ℝ≥0∞) ω *
        f (Function.update ω v false) :=
    (measurable_of_dependsOn (hcoord false)).mul (measurable_of_dependsOn (hdep false))
  rw [lintegral_congr hpt, lintegral_add_left hmeas,
    lintegral_mul_of_indepFun hind (hcoord false) (hdep false),
    lintegral_mul_of_indepFun hind (hcoord true) (hdep true),
    lintegral_indicator_one (measurableSet_coord v false),
    lintegral_indicator_one (measurableSet_coord v true), bitProduct_coord, bitProduct_coord,
    bernoulli_false, bernoulli_true]

/-- **Sequential domination on finite volumes.**  If, under `μ`, every cylinder event of a finite
set `W` leaves a further site `v` open with conditional probability at least `q`, then every
nondecreasing function of finitely many sites has a larger `μ`-integral than under the product
Bernoulli field of density `q`. -/
theorem lintegral_bitProduct_le {μ : Measure (S → Bool)} [IsProbabilityMeasure μ] (q : NNReal)
    (hq : q ≤ 1) (hcond : ∀ (W : Finset S) (v : S), v ∉ W → ∀ ζ : S → Bool,
      (q : ℝ≥0∞) * μ (cyl W ζ) ≤ μ (cyl W ζ ∩ {ω | ω v = true}))
    (Λ : Finset S) : ∀ f : (S → Bool) → ℝ≥0∞, Monotone f → DependsOn f (Λ : Set S) →
      ∫⁻ ω, f ω ∂(bitProduct q hq S) ≤ ∫⁻ ω, f ω ∂μ := by
  induction Λ using Finset.induction_on with
  | empty =>
    intro f _ hf
    have hc : ∀ ω, f ω = f (fun _ => false) := fun ω => hf (by simp)
    rw [lintegral_congr hc, lintegral_congr hc, lintegral_const, lintegral_const, measure_univ,
      measure_univ]
  | insert v Λ hv ih =>
    intro f hmono hf
    have hdep := dependsOn_update hf
    obtain ⟨f0, hf0⟩ : ∃ f0 : (S → Bool) → ℝ≥0∞, ∀ ω, f0 ω = f (Function.update ω v false) :=
      ⟨_, fun _ => rfl⟩
    obtain ⟨f1, hf1⟩ : ∃ f1 : (S → Bool) → ℝ≥0∞, ∀ ω, f1 ω = f (Function.update ω v true) :=
      ⟨_, fun _ => rfl⟩
    have hd0 : DependsOn f0 (Λ : Set S) := fun x y hxy => by rw [hf0, hf0]; exact hdep false hxy
    have hd1 : DependsOn f1 (Λ : Set S) := fun x y hxy => by rw [hf1, hf1]; exact hdep true hxy
    have hm0 : Monotone f0 := fun x y hxy => by
      rw [hf0, hf0]; exact hmono (update_le_update_iff.mpr ⟨le_rfl, fun j _ => hxy j⟩)
    have hm1 : Monotone f1 := fun x y hxy => by
      rw [hf1, hf1]; exact hmono (update_le_update_iff.mpr ⟨le_rfl, fun j _ => hxy j⟩)
    have h01 : ∀ ω, f0 ω ≤ f1 ω := fun ω => by
      rw [hf0, hf1]
      exact hmono (update_le_update_iff.mpr ⟨Bool.false_le _, fun j _ => le_rfl⟩)
    have hq1 : (q : ℝ≥0∞) ≤ 1 := by exact_mod_cast hq
    obtain ⟨g, hg⟩ : ∃ g : (S → Bool) → ℝ≥0∞, ∀ ω, g ω = (1 - (q : ℝ≥0∞)) * f0 ω + q * f1 ω :=
      ⟨_, fun _ => rfl⟩
    have hgmono : Monotone g := fun x y hxy => by
      rw [hg, hg]
      gcongr
      · exact hm0 hxy
      · exact hm1 hxy
    have hgdep : DependsOn g (Λ : Set S) := fun x y hxy => by rw [hg, hg, hd0 hxy, hd1 hxy]
    obtain ⟨h, hh⟩ : ∃ h : (S → Bool) → ℝ≥0∞, ∀ ω, h ω = f1 ω - f0 ω := ⟨_, fun _ => rfl⟩
    have hhdep : DependsOn h (Λ : Set S) := fun x y hxy => by rw [hh, hh, hd0 hxy, hd1 hxy]
    have hgpt : ∀ ω, g ω = f0 ω + q * h ω := by
      intro ω
      rw [hg, hh]
      calc (1 - (q : ℝ≥0∞)) * f0 ω + q * f1 ω
          = (1 - (q : ℝ≥0∞)) * f0 ω + q * (f0 ω + (f1 ω - f0 ω)) := by
            rw [add_tsub_cancel_of_le (h01 ω)]
        _ = ((1 - (q : ℝ≥0∞)) + q) * f0 ω + q * (f1 ω - f0 ω) := by ring
        _ = f0 ω + q * (f1 ω - f0 ω) := by rw [tsub_add_cancel_of_le hq1, one_mul]
    have hfpt : ∀ ω, f ω = f0 ω + {ω | ω v = true}.indicator h ω := by
      intro ω
      have h0 : Function.update ω v (ω v) = ω := Function.update_eq_self v ω
      cases hω : ω v
      · rw [hω] at h0
        rw [Set.indicator_of_notMem (by simp [hω]), add_zero, hf0, h0]
      · rw [hω] at h0
        rw [Set.indicator_of_mem (by simp [hω]), hh, add_tsub_cancel_of_le (h01 ω), hf1, h0]
    calc ∫⁻ ω, f ω ∂(bitProduct q hq S)
        = (1 - (q : ℝ≥0∞)) * ∫⁻ ω, f0 ω ∂(bitProduct q hq S) +
            q * ∫⁻ ω, f1 ω ∂(bitProduct q hq S) := by
          rw [lintegral_bitProduct_split q hq hv hf]
          simp only [hf0, hf1]
      _ = ∫⁻ ω, g ω ∂(bitProduct q hq S) := by
          rw [lintegral_congr hg, lintegral_add_left ((measurable_of_dependsOn hd0).const_mul _),
            lintegral_const_mul _ (measurable_of_dependsOn hd0),
            lintegral_const_mul _ (measurable_of_dependsOn hd1)]
      _ ≤ ∫⁻ ω, g ω ∂μ := ih g hgmono hgdep
      _ ≤ ∫⁻ ω, f ω ∂μ := by
          rw [lintegral_congr hgpt, lintegral_congr hfpt,
            lintegral_add_left (measurable_of_dependsOn hd0),
            lintegral_add_left (measurable_of_dependsOn hd0),
            lintegral_const_mul _ (measurable_of_dependsOn hhdep)]
          gcongr
          exact cond_lintegral hcond hv hhdep


/-! ### From finite volumes to all increasing events -/

/-- The box `[-n, n]²` of the planar carrier. -/
noncomputable def box (n : ℕ) : Finset PlanarCarrier := Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n

theorem box_mono (n : ℕ) : box n ⊆ box (n + 1) := by
  intro i hi
  simp only [box, Finset.mem_product, Finset.mem_Icc] at hi ⊢
  push_cast
  omega

theorem mem_box (i : PlanarCarrier) : i ∈ box (max i.1.natAbs i.2.natAbs) := by
  simp only [box, Finset.mem_product, Finset.mem_Icc]
  push_cast
  have := le_abs_self i.1; have := neg_abs_le i.1
  have := le_abs_self i.2; have := neg_abs_le i.2
  omega

/-- **Finite-volume domination gives the dense domination.**  If every nondecreasing function of
finitely many sites has a larger integral under `μ` than under `B`, then every measurable
increasing event has a larger `μ`-probability.  The proof approximates the event from inside by
compact sets (inner regularity) and a compact set `K` from outside by the increasing cylinder
events `{ω | ∃ κ ∈ K, κ ≤ ω on [-n, n]²}`, whose intersection lies in the event by compactness. -/
theorem denseLower_of_finite {B μ : Measure (PlanarCarrier → Bool)} [IsProbabilityMeasure B]
    [IsProbabilityMeasure μ]
    (h : ∀ (Λ : Finset PlanarCarrier) (f : (PlanarCarrier → Bool) → ℝ≥0∞), Monotone f →
      DependsOn f (Λ : Set PlanarCarrier) → ∫⁻ ω, f ω ∂B ≤ ∫⁻ ω, f ω ∂μ) :
    DenseLower B μ := by
  intro C hC hinc
  rw [hC.measure_eq_iSup_isCompact B]
  refine iSup₂_le fun K hKC => iSup_le fun hK => ?_
  obtain ⟨A, hA⟩ : ∃ A : ℕ → Set (PlanarCarrier → Bool),
      A = fun n => {ω | ∃ κ ∈ K, ∀ i ∈ box n, κ i ≤ ω i} := ⟨_, rfl⟩
  have hAdep : ∀ n, DependsOn ((A n).indicator (1 : (PlanarCarrier → Bool) → ℝ≥0∞))
      (box n : Set PlanarCarrier) := by
    intro n x y hxy
    have hiff : x ∈ A n ↔ y ∈ A n := by
      subst hA
      constructor <;> rintro ⟨κ, hκ, hle⟩ <;> refine ⟨κ, hκ, fun i hi => ?_⟩
      · rw [← hxy i hi]; exact hle i hi
      · rw [hxy i hi]; exact hle i hi
    by_cases hx : x ∈ A n
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hiff.mp hx)]; rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem fun hy => hx (hiff.mpr hy)]
  have hAmono : ∀ n, Monotone ((A n).indicator (1 : (PlanarCarrier → Bool) → ℝ≥0∞)) := by
    intro n x y hxy
    by_cases hx : x ∈ A n
    · have hy : y ∈ A n := by
        subst hA
        obtain ⟨κ, hκ, hle⟩ := hx
        exact ⟨κ, hκ, fun i hi => (hle i hi).trans (hxy i)⟩
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]; exact le_rfl
    · rw [Set.indicator_of_notMem hx]; simp
  have hAmeas : ∀ n, MeasurableSet (A n) := by
    intro n
    have hm := measurable_of_dependsOn (hAdep n)
    have : A n = (A n).indicator (1 : (PlanarCarrier → Bool) → ℝ≥0∞) ⁻¹' {1} := by
      ext ω; by_cases hω : ω ∈ A n <;> simp [hω]
    rw [this]; exact hm (measurableSet_singleton 1)
  have hKA : ∀ n, K ⊆ A n := fun n κ hκ => by subst hA; exact ⟨κ, hκ, fun i _ => le_rfl⟩
  have hBA : ∀ n, B (A n) ≤ μ (A n) := by
    intro n
    have := h (box n) _ (hAmono n) (hAdep n)
    rwa [lintegral_indicator_one (hAmeas n), lintegral_indicator_one (hAmeas n)] at this
  have hanti : Antitone A := by
    refine antitone_nat_of_succ_le fun n ω hω => ?_
    subst hA
    obtain ⟨κ, hκ, hle⟩ := hω
    exact ⟨κ, hκ, fun i hi => hle i (box_mono n hi)⟩
  have hinter : (⋂ n, A n) ⊆ C := by
    intro ω hω
    rw [Set.mem_iInter] at hω
    have hclosed : ∀ n, IsClosed {κ : PlanarCarrier → Bool | ∀ i ∈ box n, κ i ≤ ω i} := by
      intro n
      have : {κ : PlanarCarrier → Bool | ∀ i ∈ box n, κ i ≤ ω i} =
          ⋂ i ∈ box n, (fun κ : PlanarCarrier → Bool => κ i) ⁻¹' {b | b ≤ ω i} := by
        ext κ; simp
      rw [this]
      exact isClosed_biInter fun i _ => (isClosed_discrete _).preimage (continuous_apply i)
    have hne : (⋂ n, (K ∩ {κ : PlanarCarrier → Bool | ∀ i ∈ box n, κ i ≤ ω i})).Nonempty := by
      refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _ ?_ ?_ ?_ ?_
      · intro n κ hκ
        exact ⟨hκ.1, fun i hi => hκ.2 i (box_mono n hi)⟩
      · intro n
        have := hω n
        subst hA
        obtain ⟨κ, hκ, hle⟩ := this
        exact ⟨κ, hκ, hle⟩
      · exact hK.inter_right (hclosed 0)
      · intro n; exact hK.isClosed.inter (hclosed n)
    obtain ⟨κ, hκ⟩ := hne
    rw [Set.mem_iInter] at hκ
    refine hinc κ ω (hKC (hκ 0).1) fun s hs => ?_
    have := (hκ _).2 s (mem_box s)
    rw [hs] at this
    revert this
    cases ω s <;> decide
  calc B K ≤ ⨅ n, B (A n) := le_iInf fun n => measure_mono (hKA n)
    _ ≤ ⨅ n, μ (A n) := iInf_mono hBA
    _ = μ (⋂ n, A n) :=
        (hanti.measure_iInter (fun n => (hAmeas n).nullMeasurableSet)
          ⟨0, measure_ne_top _ _⟩).symm
    _ ≤ μ C := measure_mono hinter


/-! ### The thinned field of a `1`-dependent field -/

/-- The `ℓ^∞` neighbours of a site `v` among the sites of `W`. -/
def nearSites (W : Finset PlanarCarrier) (v : PlanarCarrier) : Finset PlanarCarrier :=
  W.filter fun w => max |v.1 - w.1| |v.2 - w.2| ≤ 1

/-- The sites of `W` at `ℓ^∞` distance at least `2` of a site `v`. -/
def farSites (W : Finset PlanarCarrier) (v : PlanarCarrier) : Finset PlanarCarrier :=
  W.filter fun w => ¬ max |v.1 - w.1| |v.2 - w.2| ≤ 1

/-- A site has at most `8` neighbours for the `ℓ^∞` distance of `ℤ²`. -/
theorem card_nearSites_le (W : Finset PlanarCarrier) {v : PlanarCarrier} (hv : v ∉ W) :
    (nearSites W v).card ≤ 8 := by
  have hsub : nearSites W v ⊆
      (Finset.Icc (v.1 - 1) (v.1 + 1) ×ˢ Finset.Icc (v.2 - 1) (v.2 + 1)).erase v := by
    intro w hw
    rw [nearSites, Finset.mem_filter] at hw
    rw [Finset.mem_erase, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨fun h => hv (h ▸ hw.1), ?_⟩
    have h1 := hw.2
    rw [max_le_iff, abs_le, abs_le] at h1
    omega
  calc (nearSites W v).card ≤ _ := Finset.card_le_card hsub
    _ = 8 := by
      rw [Finset.card_erase_of_mem (by simp), Finset.card_product, Int.card_Icc, Int.card_Icc,
        show v.1 + 1 + 1 - (v.1 - 1) = 3 by ring, show v.2 + 1 + 1 - (v.2 - 1) = 3 by ring]
      rfl

/-- The thinning kernel: the probability that `a ∧ Y = c` for a Bernoulli variable `Y` of
density `α`. -/
noncomputable def thinK (α : NNReal) (a c : Bool) : ℝ≥0∞ :=
  if a then (if c then (α : ℝ≥0∞) else 1 - (α : ℝ≥0∞)) else (if c then 0 else 1)

theorem thinK_le_one {α : NNReal} (hα : α ≤ 1) (a c : Bool) : thinK α a c ≤ 1 := by
  have : (α : ℝ≥0∞) ≤ 1 := by exact_mod_cast hα
  cases a <;> cases c <;> simp [thinK, this]

theorem thinK_true_ge {α : NNReal} (hα2 : 1 - (α : ℝ≥0∞) ≤ α) (c : Bool) :
    1 - (α : ℝ≥0∞) ≤ thinK α true c := by
  cases c <;> simp [thinK, hα2]

theorem bernoulli_and {α : NNReal} (hα : α ≤ 1) (a c : Bool) :
    bernoulli α hα {b | (a && b) = c} = thinK α a c := by
  cases a <;> cases c
  · rw [show {b : Bool | (false && b) = false} = Set.univ by ext b; simp, measure_univ]; rfl
  · simp [thinK]
  · rw [show {b : Bool | (true && b) = false} = {false} by ext b; simp, bernoulli_false]; rfl
  · rw [show {b : Bool | (true && b) = true} = {true} by ext b; simp, bernoulli_true]; rfl

/-- The weight of the thinned pattern `ζ` on `W` given the configuration `x`: the probability
that `x ∧ Y` agrees with `ζ` on `W`, for a product Bernoulli field `Y` of density `α`. -/
noncomputable def thinWeight (α : NNReal) (W : Finset PlanarCarrier) (ζ x : PlanarCarrier → Bool) :
    ℝ≥0∞ :=
  ∏ w ∈ W, thinK α (x w) (ζ w)

theorem thinWeight_dependsOn (α : NNReal) (W : Finset PlanarCarrier) (ζ : PlanarCarrier → Bool) :
    DependsOn (thinWeight α W ζ) (W : Set PlanarCarrier) := fun x y hxy =>
  Finset.prod_congr rfl fun w hw => by rw [hxy w hw]

theorem thinWeight_le_one {α : NNReal} (hα : α ≤ 1) (W : Finset PlanarCarrier)
    (ζ x : PlanarCarrier → Bool) : thinWeight α W ζ x ≤ 1 :=
  Finset.prod_le_one' fun _ _ => thinK_le_one hα _ _

theorem lintegral_thinWeight_ne_top {ν : Measure (PlanarCarrier → Bool)} [IsProbabilityMeasure ν]
    {α : NNReal} (hα : α ≤ 1) (W : Finset PlanarCarrier) (ζ : PlanarCarrier → Bool) :
    ∫⁻ x, thinWeight α W ζ x ∂ν ≠ ∞ := by
  refine ne_top_of_le_ne_top (b := ∫⁻ _, 1 ∂ν) (by simp) (lintegral_mono fun x => ?_)
  exact thinWeight_le_one hα W ζ x

theorem indicator_coord_dependsOn (v : PlanarCarrier) (b : Bool) :
    DependsOn ({x : PlanarCarrier → Bool | x v = b}.indicator (1 : (PlanarCarrier → Bool) → ℝ≥0∞))
      (({v} : Finset PlanarCarrier) : Set PlanarCarrier) := by
  intro x y hxy
  have : x v = y v := hxy v (by simp)
  simp [Set.indicator_apply, this]

/-- **The thinned conditional bound** (Liggett, Schonmann and Stacey, proof of Theorem 1.3).  For
a `1`-dependent field `ν` with closed sites of probability at most `ε`, thinned by an independent
Bernoulli field of density `α`, a site `v` outside `W` is closed in the field `x` with
conditional probability at most `δ` given any pattern of the thinned field on `W`. -/
theorem thin_claim {ν : Measure (PlanarCarrier → Bool)} [IsProbabilityMeasure ν]
    (hν : KDependentPlanar 1 ν) {ε δ : ℝ≥0∞} (hε : ∀ z, ν {ω | ω z = false} ≤ ε)
    {α : NNReal} (hα : α ≤ 1) (hα2 : 1 - (α : ℝ≥0∞) ≤ α) (hδ : δ ≠ ∞) (hεδ : ε ≤ δ)
    (hkey : ε + 8 * δ * ((1 - (α : ℝ≥0∞)) ^ 8 * δ) ≤ δ * (1 - (α : ℝ≥0∞)) ^ 8)
    (W : Finset PlanarCarrier) : ∀ v ∉ W, ∀ ζ : PlanarCarrier → Bool,
      ∫⁻ x, {x | x v = false}.indicator (thinWeight α W ζ) x ∂ν ≤
        δ * ∫⁻ x, thinWeight α W ζ x ∂ν := by
  induction W using Finset.strongInduction with
  | H W ih =>
  intro v hv ζ
  have hsplit : ∀ x, thinWeight α W ζ x =
      thinWeight α (nearSites W v) ζ x * thinWeight α (farSites W v) ζ x := fun x =>
    (Finset.prod_filter_mul_prod_filter_not W _ _).symm
  have hfar : ∀ i ∈ ({v} : Finset PlanarCarrier), ∀ j ∈ farSites W v,
      ((1 : ℕ) : ℤ) < max |i.1 - j.1| |i.2 - j.2| := by
    intro i hi j hj
    rw [Finset.mem_singleton] at hi
    subst hi
    rw [farSites, Finset.mem_filter] at hj
    push_cast
    exact lt_of_not_ge hj.2
  have hFdep := thinWeight_dependsOn α (farSites W v) ζ
  have hFm := measurable_of_dependsOn hFdep
  have hU : ∫⁻ x, {x | x v = false}.indicator (thinWeight α W ζ) x ∂ν ≤
      ε * ∫⁻ x, thinWeight α (farSites W v) ζ x ∂ν := by
    calc ∫⁻ x, {x | x v = false}.indicator (thinWeight α W ζ) x ∂ν
        ≤ ∫⁻ x, {x : PlanarCarrier → Bool | x v = false}.indicator 1 x *
            thinWeight α (farSites W v) ζ x ∂ν := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x v = false
          · rw [indicator_coord_of hx, indicator_coord_of hx, Pi.one_apply, one_mul, hsplit]
            exact mul_le_of_le_one_left' (thinWeight_le_one hα _ _ _)
          · rw [indicator_coord_of_ne hx, indicator_coord_of_ne hx, zero_mul]
      _ = ν {x | x v = false} * ∫⁻ x, thinWeight α (farSites W v) ζ x ∂ν := by
          rw [lintegral_mul_of_indepFun (hν {v} (farSites W v) hfar)
            (indicator_coord_dependsOn v false) hFdep,
            lintegral_indicator_one (measurableSet_coord v false)]
      _ ≤ ε * ∫⁻ x, thinWeight α (farSites W v) ζ x ∂ν := by gcongr; exact hε v
  by_cases hNe : nearSites W v = ∅
  · have hFW : farSites W v = W :=
      Finset.filter_true_of_mem (Finset.filter_eq_empty_iff.mp hNe)
    rw [hFW] at hU
    calc _ ≤ ε * _ := hU
      _ ≤ δ * _ := by gcongr
  have hFW : farSites W v ⊂ W := by
    refine Finset.filter_ssubset.mpr ?_
    obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.mpr hNe
    rw [nearSites, Finset.mem_filter] at hw
    exact ⟨w, hw.1, not_not.mpr hw.2⟩
  have hwF : ∀ w ∈ nearSites W v, w ∉ farSites W v := fun w hw hwF =>
    (Finset.mem_filter.mp hwF).2 (Finset.mem_filter.mp hw).2
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0∞, c = (1 - (α : ℝ≥0∞)) ^ 8 := ⟨_, rfl⟩
  have hscal : ∀ x, c ≤ thinWeight α (nearSites W v) ζ x + c * ∑ w ∈ nearSites W v,
      {x : PlanarCarrier → Bool | x w = false}.indicator 1 x := by
    intro x
    by_cases hall : ∀ w ∈ nearSites W v, x w = true
    · refine le_trans ?_ le_self_add
      calc c ≤ (1 - (α : ℝ≥0∞)) ^ (nearSites W v).card := by
            rw [hc]; exact pow_le_pow_right_of_le_one' tsub_le_self (card_nearSites_le W hv)
        _ = ∏ w ∈ nearSites W v, (1 - (α : ℝ≥0∞)) := (Finset.prod_const _).symm
        _ ≤ thinWeight α (nearSites W v) ζ x :=
            Finset.prod_le_prod' fun w hw => by rw [hall w hw]; exact thinK_true_ge hα2 _
    · push Not at hall
      obtain ⟨w, hw, hxw⟩ := hall
      refine le_trans ?_ le_add_self
      refine le_mul_of_one_le_right' ?_
      calc (1 : ℝ≥0∞) = {x : PlanarCarrier → Bool | x w = false}.indicator 1 x := by
            rw [indicator_coord_of (show x w = false by simpa using hxw)]; rfl
        _ ≤ _ := Finset.single_le_sum (f := fun w => {x : PlanarCarrier → Bool | x w = false}.indicator
              (1 : (PlanarCarrier → Bool) → ℝ≥0∞) x) (fun _ _ => zero_le) hw
  have hpt : ∀ x, c * thinWeight α (farSites W v) ζ x ≤ thinWeight α W ζ x +
      c * ∑ w ∈ nearSites W v, {x | x w = false}.indicator (thinWeight α (farSites W v) ζ) x := by
    intro x
    calc c * thinWeight α (farSites W v) ζ x
        ≤ (thinWeight α (nearSites W v) ζ x + c * ∑ w ∈ nearSites W v,
            {x : PlanarCarrier → Bool | x w = false}.indicator 1 x) *
            thinWeight α (farSites W v) ζ x := by gcongr; exact hscal x
      _ = _ := by
          rw [add_mul, hsplit, mul_assoc, Finset.sum_mul]
          congr 2
          refine Finset.sum_congr rfl fun w _ => ?_
          by_cases hx : x w = false
          · rw [indicator_coord_of hx, indicator_coord_of hx, Pi.one_apply, one_mul]
          · rw [indicator_coord_of_ne hx, indicator_coord_of_ne hx, zero_mul]
  have hindm : ∀ w, Measurable ({x : PlanarCarrier → Bool | x w = false}.indicator
      (thinWeight α (farSites W v) ζ)) := fun w => hFm.indicator (measurableSet_coord w false)
  obtain ⟨a, ha⟩ : ∃ a, a = ∫⁻ x, thinWeight α (farSites W v) ζ x ∂ν := ⟨_, rfl⟩
  have hL : c * a ≤ ∫⁻ x, thinWeight α W ζ x ∂ν + c * (8 * δ * a) := by
    calc c * a = ∫⁻ x, c * thinWeight α (farSites W v) ζ x ∂ν := by
          rw [lintegral_const_mul _ hFm, ha]
      _ ≤ ∫⁻ x, (thinWeight α W ζ x + c * ∑ w ∈ nearSites W v,
            {x | x w = false}.indicator (thinWeight α (farSites W v) ζ) x) ∂ν := lintegral_mono hpt
      _ = ∫⁻ x, thinWeight α W ζ x ∂ν + c * ∑ w ∈ nearSites W v,
            ∫⁻ x, {x | x w = false}.indicator (thinWeight α (farSites W v) ζ) x ∂ν := by
          rw [lintegral_add_left (measurable_of_dependsOn (thinWeight_dependsOn α W ζ)),
            lintegral_const_mul _ (Finset.measurable_sum _ fun w _ => hindm w),
            lintegral_finsetSum _ fun w _ => hindm w]
      _ ≤ ∫⁻ x, thinWeight α W ζ x ∂ν + c * ∑ w ∈ nearSites W v, δ * a := by
          gcongr with w hw
          rw [ha]; exact ih _ hFW w (hwF w hw) ζ
      _ ≤ ∫⁻ x, thinWeight α W ζ x ∂ν + c * (8 * δ * a) := by
          have hcard : ((nearSites W v).card : ℝ≥0∞) * (δ * a) ≤ 8 * δ * a := by
            rw [mul_assoc]
            gcongr
            exact_mod_cast card_nearSites_le W hv
          rw [Finset.sum_const, nsmul_eq_mul]
          exact add_le_add le_rfl (mul_le_mul' le_rfl hcard)
  have hafin : a ≠ ∞ := ha ▸ lintegral_thinWeight_ne_top hα _ ζ
  have hcfin : c ≠ ∞ := by rw [hc]; exact ENNReal.pow_ne_top (ENNReal.sub_ne_top ENNReal.one_ne_top)
  rw [← ha] at hU
  have h1 : ε * a + 8 * δ * (c * δ) * a ≤ δ * ∫⁻ x, thinWeight α W ζ x ∂ν + 8 * δ * (c * δ) * a := by
    calc ε * a + 8 * δ * (c * δ) * a = (ε + 8 * δ * (c * δ)) * a := by ring
      _ ≤ δ * c * a := by gcongr; rw [hc]; exact hkey
      _ = δ * (c * a) := by ring
      _ ≤ δ * (∫⁻ x, thinWeight α W ζ x ∂ν + c * (8 * δ * a)) := by gcongr
      _ = δ * ∫⁻ x, thinWeight α W ζ x ∂ν + 8 * δ * (c * δ) * a := by ring
  have hfin : 8 * δ * (c * δ) * a ≠ ∞ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hδ)
      (ENNReal.mul_ne_top hcfin hδ)) hafin
  exact hU.trans (ENNReal.le_of_add_le_add_right hfin h1)

/-! ### The law of the thinned field -/

theorem measurable_thin : Measurable fun p : (PlanarCarrier → Bool) × (PlanarCarrier → Bool) =>
    fun s => p.1 s && p.2 s := by
  refine measurable_pi_lambda _ fun s => ?_
  have h1 : Measurable fun c : (PlanarCarrier → Bool) × (PlanarCarrier → Bool) => (c.1 s, c.2 s) :=
    ((measurable_pi_apply s).comp measurable_fst).prodMk ((measurable_pi_apply s).comp measurable_snd)
  exact (measurable_of_countable (fun r : Bool × Bool => r.1 && r.2)).comp h1

/-- The law of the thinned field `x ∧ y`, for `x` of law `ν` and an independent product
Bernoulli field `y` of density `α`. -/
noncomputable def thinLaw (ν : Measure (PlanarCarrier → Bool)) (α : NNReal) (hα : α ≤ 1) :
    Measure (PlanarCarrier → Bool) :=
  (ν.prod (bernoulliFieldPlanar α hα)).map fun p => fun s => p.1 s && p.2 s

instance thinLaw.instIsProbabilityMeasure (ν : Measure (PlanarCarrier → Bool))
    [IsProbabilityMeasure ν] (α : NNReal) (hα : α ≤ 1) : IsProbabilityMeasure (thinLaw ν α hα) :=
  Measure.isProbabilityMeasure_map measurable_thin.aemeasurable

/-- The cylinder probabilities of the thinned field are the integrated thinning weights. -/
theorem thinLaw_cyl (ν : Measure (PlanarCarrier → Bool)) {α : NNReal} (hα : α ≤ 1)
    (W : Finset PlanarCarrier) (ζ : PlanarCarrier → Bool) :
    thinLaw ν α hα (cyl W ζ) = ∫⁻ x, thinWeight α W ζ x ∂ν := by
  rw [thinLaw, Measure.map_apply measurable_thin (measurableSet_cyl W ζ),
    Measure.prod_apply (measurable_thin (measurableSet_cyl W ζ))]
  refine lintegral_congr fun x => ?_
  have : Prod.mk x ⁻¹' ((fun p : (PlanarCarrier → Bool) × (PlanarCarrier → Bool) =>
      fun s => p.1 s && p.2 s) ⁻¹' cyl W ζ) =
      Set.pi (W : Set PlanarCarrier) (fun w => {b | (x w && b) = ζ w}) := by
    ext y; simp [cyl, Set.mem_pi]
  rw [this, bernoulliFieldPlanar, bitProduct,
    Measure.infinitePi_pi _ (fun _ _ => MeasurableSet.of_discrete)]
  exact Finset.prod_congr rfl fun w _ => bernoulli_and hα _ _

/-- The thinned field is below the field: its law gives every increasing event a smaller
probability. -/
theorem thinLaw_le (ν : Measure (PlanarCarrier → Bool)) [IsProbabilityMeasure ν] {α : NNReal}
    (hα : α ≤ 1) {C : Set (PlanarCarrier → Bool)} (hC : MeasurableSet C)
    (hinc : LatticeProb.StrassenAux.IsIncreasingSet C) : thinLaw ν α hα C ≤ ν C := by
  rw [thinLaw, Measure.map_apply measurable_thin hC]
  calc (ν.prod (bernoulliFieldPlanar α hα))
        ((fun p : (PlanarCarrier → Bool) × (PlanarCarrier → Bool) =>
          fun s => p.1 s && p.2 s) ⁻¹' C)
      ≤ (ν.prod (bernoulliFieldPlanar α hα)) (C ×ˢ Set.univ) := by
        refine measure_mono fun p hp => ⟨hinc _ _ hp fun s hs => ?_, trivial⟩
        simp only [Bool.and_eq_true] at hs
        exact hs.1
    _ = ν C := by rw [Measure.prod_prod, measure_univ, mul_one]

/-- The conditional lower bound of the thinned field: given any pattern on `W`, a site `v ∉ W`
of the thinned field is open with conditional probability at least `q` when
`q + α δ ≤ α`. -/
theorem thinLaw_cond {ν : Measure (PlanarCarrier → Bool)} [IsProbabilityMeasure ν]
    (hν : KDependentPlanar 1 ν) {ε δ : ℝ≥0∞} (hε : ∀ z, ν {ω | ω z = false} ≤ ε)
    {α : NNReal} (hα : α ≤ 1) (hα2 : 1 - (α : ℝ≥0∞) ≤ α) (hδ : δ ≠ ∞) (hεδ : ε ≤ δ)
    (hkey : ε + 8 * δ * ((1 - (α : ℝ≥0∞)) ^ 8 * δ) ≤ δ * (1 - (α : ℝ≥0∞)) ^ 8)
    {q : NNReal} (hq : (q : ℝ≥0∞) + α * δ ≤ α) :
    ∀ (W : Finset PlanarCarrier) (v : PlanarCarrier), v ∉ W → ∀ ζ : PlanarCarrier → Bool,
      (q : ℝ≥0∞) * thinLaw ν α hα (cyl W ζ) ≤ thinLaw ν α hα (cyl W ζ ∩ {ω | ω v = true}) := by
  intro W v hv ζ
  have hne : ∀ w ∈ W, w ≠ v := fun w hw h => hv (h ▸ hw)
  have hcylv : cyl W ζ ∩ {ω | ω v = true} = cyl (insert v W) (Function.update ζ v true) := by
    ext ω
    simp only [cyl, Set.mem_inter_iff, Set.mem_setOf_eq, Finset.forall_mem_insert,
      Function.update_self]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2, fun w hw => ?_⟩
      rw [Function.update_of_ne (hne w hw)]
      exact h1 w hw
    · rintro ⟨h2, h1⟩
      refine ⟨fun w hw => ?_, h2⟩
      have := h1 w hw
      rwa [Function.update_of_ne (hne w hw)] at this
  have hGm := measurable_of_dependsOn (thinWeight_dependsOn α W ζ)
  have hw' : ∀ x, thinWeight α (insert v W) (Function.update ζ v true) x =
      α * {x : PlanarCarrier → Bool | x v = true}.indicator (thinWeight α W ζ) x := by
    intro x
    rw [thinWeight, Finset.prod_insert hv, Function.update_self]
    have : ∏ w ∈ W, thinK α (x w) (Function.update ζ v true w) = thinWeight α W ζ x :=
      Finset.prod_congr rfl fun w hw => by rw [Function.update_of_ne (hne w hw)]
    rw [this]
    cases hx : x v
    · rw [indicator_coord_of_ne (by simp [hx])]; simp [thinK]
    · rw [indicator_coord_of hx]; simp [thinK]
  have hpt : ∀ x, thinWeight α W ζ x =
      {x : PlanarCarrier → Bool | x v = true}.indicator (thinWeight α W ζ) x +
        {x : PlanarCarrier → Bool | x v = false}.indicator (thinWeight α W ζ) x := by
    intro x
    cases hx : x v
    · rw [indicator_coord_of_ne (by simp [hx]), indicator_coord_of hx, zero_add]
    · rw [indicator_coord_of hx, indicator_coord_of_ne (by simp [hx]), add_zero]
  rw [hcylv, thinLaw_cyl, thinLaw_cyl, lintegral_congr hw',
    lintegral_const_mul _ (hGm.indicator (measurableSet_coord v true)), lintegral_congr hpt,
    lintegral_add_left (hGm.indicator (measurableSet_coord v true))]
  have hclaim := thin_claim hν hε hα hα2 hδ hεδ hkey W v hv ζ
  rw [lintegral_congr hpt, lintegral_add_left (hGm.indicator (measurableSet_coord v true))]
    at hclaim
  obtain ⟨T, hT⟩ : ∃ T, T = ∫⁻ x, {x : PlanarCarrier → Bool | x v = true}.indicator
      (thinWeight α W ζ) x ∂ν := ⟨_, rfl⟩
  obtain ⟨Fz, hFz⟩ : ∃ Fz, Fz = ∫⁻ x, {x : PlanarCarrier → Bool | x v = false}.indicator
      (thinWeight α W ζ) x ∂ν := ⟨_, rfl⟩
  rw [← hT, ← hFz] at hclaim ⊢
  have hTF : T + Fz ≠ ∞ := by
    rw [hT, hFz, ← lintegral_add_left (hGm.indicator (measurableSet_coord v true)),
      ← lintegral_congr hpt]
    exact lintegral_thinWeight_ne_top hα W ζ
  have hα1 : (α : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have h1 : (q : ℝ≥0∞) * (T + Fz) + α * δ * (T + Fz) ≤ α * T + α * δ * (T + Fz) := by
    calc (q : ℝ≥0∞) * (T + Fz) + α * δ * (T + Fz) = ((q : ℝ≥0∞) + α * δ) * (T + Fz) := by ring
      _ ≤ α * (T + Fz) := by gcongr
      _ = α * T + α * Fz := by ring
      _ ≤ α * T + α * (δ * (T + Fz)) := by gcongr
      _ = α * T + α * δ * (T + Fz) := by ring
  exact ENNReal.le_of_add_le_add_right (ENNReal.mul_ne_top (ENNReal.mul_ne_top hα1 hδ) hTF) h1

end LSSDomination

open LSSDomination

/-- **Step `step:5.23-domination`** (Liggett, Schonmann and Stacey, Theorem 1.3, for the
`ℓ^∞` dependency graph of `ℤ²`, `Δ = 8`), with `C₀ = 4` and `a = 1/16`: a `1`-dependent field on
`ℤ²` whose sites are closed with probability at most `ε` dominates on increasing events the
product Bernoulli field of every density `q ≤ (1 - 4 ε^(1/16))₊`. -/
theorem oneDependentDominationStep : Rigidity.Steps.Section5.OneDependentDominationStep := by
  refine ⟨4, 1 / 16, by norm_num, by norm_num, ?_⟩
  intro ν hνP hdep ε hε0 hεz q hq hqle
  haveI := hνP
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ε ^ (1 / 16 : ℝ) := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := ht ▸ Real.rpow_nonneg hε0 _
  have ht16 : t ^ 16 = ε := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hε0]; norm_num
  rw [← ht] at hqle
  by_cases hsmall : t ≤ 1 / 4
  swap
  · have hq0 : q = 0 := by
      rw [Real.toNNReal_of_nonpos (by linarith)] at hqle
      exact nonpos_iff_eq_zero.mp hqle
    subst hq0
    exact denseLower_of_finite fun Λ f hf hfd =>
      lintegral_bitProduct_le 0 hq (fun W v _ ζ => by simp) Λ f hf hfd
  obtain ⟨s, hs⟩ : ∃ s : NNReal, (s : ℝ) = t := ⟨⟨t, ht0⟩, rfl⟩
  have hs1 : s ≤ 1 := by rw [← NNReal.coe_le_coe, hs]; push_cast; linarith
  have hαr : ((1 - s : NNReal) : ℝ) = 1 - t := by rw [NNReal.coe_sub hs1, hs]; rfl
  have hα : 1 - s ≤ 1 := tsub_le_self
  have h1α : 1 - ((1 - s : NNReal) : ℝ≥0∞) = s := by
    rw [ENNReal.coe_sub, ENNReal.coe_one,
      ENNReal.sub_sub_cancel ENNReal.one_ne_top (by exact_mod_cast hs1)]
  have h8 : t ^ 8 ≤ 1 / 32 := by
    calc t ^ 8 ≤ (1 / 4) ^ 8 := pow_le_pow_left₀ ht0 hsmall 8
      _ ≤ 1 / 32 := by norm_num
  have ht8 : t ^ 8 ≤ t := by
    calc t ^ 8 = t * t ^ 7 := by ring
      _ ≤ t * 1 := by gcongr; exact pow_le_one₀ ht0 (by linarith)
      _ = t := mul_one t
  have heps : ENNReal.ofReal ε = ((s ^ 16 : NNReal) : ℝ≥0∞) := by
    rw [← ht16, ← hs, ENNReal.ofReal_pow (NNReal.coe_nonneg s), ENNReal.ofReal_coe_nnreal, ENNReal.coe_pow]
  have hεz' : ∀ z, ν {ω | ω z = false} ≤ ((s ^ 16 : NNReal) : ℝ≥0∞) := fun z => heps ▸ hεz z
  have hα2 : 1 - ((1 - s : NNReal) : ℝ≥0∞) ≤ ((1 - s : NNReal) : ℝ≥0∞) := by
    rw [h1α]
    have : s ≤ 1 - s := by rw [← NNReal.coe_le_coe, hαr, hs]; linarith
    exact_mod_cast this
  have hεδ : ((s ^ 16 : NNReal) : ℝ≥0∞) ≤ ((2 * s ^ 8 : NNReal) : ℝ≥0∞) := by
    have : s ^ 16 ≤ 2 * s ^ 8 := by
      rw [← NNReal.coe_le_coe]; push_cast; rw [hs]
      nlinarith [pow_nonneg ht0 8, mul_le_mul_of_nonneg_right h8 (pow_nonneg ht0 8)]
    exact_mod_cast this
  have hkey : ((s ^ 16 : NNReal) : ℝ≥0∞) + 8 * ((2 * s ^ 8 : NNReal) : ℝ≥0∞) *
      ((1 - ((1 - s : NNReal) : ℝ≥0∞)) ^ 8 * ((2 * s ^ 8 : NNReal) : ℝ≥0∞)) ≤
      ((2 * s ^ 8 : NNReal) : ℝ≥0∞) * (1 - ((1 - s : NNReal) : ℝ≥0∞)) ^ 8 := by
    rw [h1α]
    have : s ^ 16 + 8 * (2 * s ^ 8) * (s ^ 8 * (2 * s ^ 8)) ≤ 2 * s ^ 8 * s ^ 8 := by
      rw [← NNReal.coe_le_coe]; push_cast; rw [hs]
      nlinarith [pow_nonneg ht0 8, pow_nonneg ht0 16,
        mul_le_mul_of_nonneg_right h8 (pow_nonneg ht0 16)]
    exact_mod_cast this
  have hqE : (q : ℝ≥0∞) + ((1 - s : NNReal) : ℝ≥0∞) * ((2 * s ^ 8 : NNReal) : ℝ≥0∞) ≤
      ((1 - s : NNReal) : ℝ≥0∞) := by
    have hqr : (q : ℝ) ≤ 1 - 4 * t := by
      have := NNReal.coe_le_coe.mpr hqle
      rwa [Real.coe_toNNReal _ (by linarith)] at this
    have : q + (1 - s) * (2 * s ^ 8) ≤ 1 - s := by
      rw [← NNReal.coe_le_coe, NNReal.coe_add, NNReal.coe_mul, hαr]
      push_cast; rw [hs]
      nlinarith
    exact_mod_cast this
  have hcond := thinLaw_cond hdep hεz' hα hα2 ENNReal.coe_ne_top hεδ hkey hqE
  have hdense : DenseLower (bernoulliFieldPlanar q hq) (thinLaw ν (1 - s) hα) :=
    denseLower_of_finite fun Λ f hf hfd => lintegral_bitProduct_le q hq hcond Λ f hf hfd
  exact fun C hC hinc => (hdense C hC hinc).trans (thinLaw_le ν hα hC hinc)


/-- Lemma 5.23 from Proposition 2.3, Kesten's crossing estimate and the three remaining steps:
the Liggett-Schonmann-Stacey step is `oneDependentDominationStep`. -/
theorem renormalizedDomination_of_steps' {p : unitInterval}
    (hW : Rigidity.External.WellConnectedInput) (hK : Rigidity.External.KestenRectangleCrossing)
    (hpc : criticalProbability 2 < (p : ℝ)) (hV : Rigidity.Steps.Section5.VeryGoodProbabilityStep)
    (hM : Rigidity.Steps.Section5.RenormFieldMeasurableStep)
    (hD : Rigidity.Steps.Section5.RenormFieldOneDependentStep) :
    Rigidity.Section5.RenormalizedDominationStmt p :=
  Rigidity.Steps.Section5.renormalizedDomination_of_steps hW hK hpc hV hM hD
    oneDependentDominationStep

end Rigidity.Proofs.Section5
