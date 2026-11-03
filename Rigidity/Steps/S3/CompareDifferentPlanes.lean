import Rigidity.Draft.Section3Statements
import LatticeProb.External.SupercriticalBondCorrectorInput
import LatticeProb.External.SupercriticalBondUniquenessInput
import LatticeProb.Prob.Percolation.GreenColumnEvent
import LatticeProb.Prob.Percolation.CorrectedPlaneAlgebra

/-!
# Lemma 3.3: the steps of the comparison of corrected planes on different clusters

Lemma 3.3 (paper L876-907 of the corrected draft) compares the corrected planes `ℓ_p` of the
unique infinite cluster `C_∞` and `ℓ'_p` of the cluster `C'_∞` from which a finite
non-disconnecting set `B` of edges has been removed. It is carved into five steps.

* `step:3.3-flip-cluster` (paper L895): removing the edges of `B` leaves a unique infinite
  cluster with the same vertices.
* `step:3.3-flip-corrector` (paper L888-893, Lemma 2.1 applied to the full-measure event of the
  qualitative corrector input): almost surely, after closing any finite set of bonds, every slope
  still has a unique corrected plane normalized at a vertex of the infinite cluster.
* `step:3.3-green-laplacian` (paper L903-907): `Δ_{C_∞} ∇_y G(·, e) = δ_y - δ_x` and
  `Δ_{C_∞} ℓ'_p = ∑_{e ∈ B} (δ_x - δ_y) (ℓ'_p(y) - ℓ'_p(x))`, so that
  `ℓ'_p + ∑_{e ∈ B} ∇_y G(·, e) (ℓ'_p(y) - ℓ'_p(x))` is harmonic on `C_∞`.
* `step:3.3-green-sublinear` (paper L899-900, there from Proposition 2.6): a Green column grows
  sublinearly. With the normalization at infinity built into `IsGreenColumn`, this is elementary.
* `step:3.3-liouville` (paper L889, L896): almost surely, a sublinear harmonic function on `C_∞`
  is constant (Theorem 2.4 at order zero).

Sublinear growth is expressed as `componentSlopeAsymptotics C 0`: on Euclidean balls of radius
`R` the function is `o(R)` uniformly. The existence of the infinite cluster and of the Green
columns, and the corrected planes on `C_∞`, are the cited inputs.
-/

namespace Rigidity.Steps.S3

open MeasureTheory LatticeProb.Percolation Rigidity.Section3

variable {d : ℕ}

open scoped Classical in
/-- The Green function on a cluster `C` with pole `x` evaluated at `z`, from a family `G` of
Green columns (`G y` has its pole at `y`), extended by zero off the cluster. -/
noncomputable def greenFunction {ω : Configuration d} (C : OpenComponent ω) (G : C → C → ℝ)
    (x z : Vertex d) : ℝ :=
  extend C (fun y => if hx : x ∈ C.supp then G ⟨x, hx⟩ y else 0) z

/-- The Green dipole of an edge `{x, y}` evaluated at `z`, where `g x z` is the Green function at
`z` with pole `x`: the gradient `g x z - g y z` of the Green function along the edge, times
`w y - w x`. It is symmetric in `x` and `y`. -/
noncomputable def greenDipole (g : Vertex d → Vertex d → ℝ) (w : Vertex d → ℝ) (z : Vertex d) :
    Sym2 (Vertex d) → ℝ :=
  Sym2.lift ⟨fun x y => (g x z - g y z) * (w y - w x), fun x y => by ring⟩

/-- Step `step:3.3-flip-cluster` (paper L895): closing the bonds of a finite set `B` whose removal
does not disconnect the unique infinite cluster leaves a unique infinite cluster, with the same
vertices. -/
def FlipClusterStep (d : ℕ) : Prop :=
  ∀ (ω : Configuration d) (h : HasUniqueInfiniteOpenComponent ω) (B : Finset (Bond d)),
    (∀ x ∈ (uniqueInfiniteComponent h).supp, ∀ y ∈ (uniqueInfiniteComponent h).supp,
      (openGraph (closeBonds B ω)).Reachable x y) →
    ∃ h' : HasUniqueInfiniteOpenComponent (closeBonds B ω),
      (uniqueInfiniteComponent h').supp = (uniqueInfiniteComponent h).supp

/-- Step `step:3.3-flip-corrector` (paper L888-893): Lemma 2.1 applied to the full-measure event
of the qualitative corrector input. Almost surely, after closing any finite set `B` of bonds,
every slope has a unique corrected plane on the unique infinite cluster normalized at any of its
vertices. -/
def FlipCorrectorStep (d : ℕ) [NeZero d] (p : unitInterval) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw d p, ∀ (B : Finset (Bond d))
    (h' : HasUniqueInfiniteOpenComponent (closeBonds B ω)) (q : Fin d → ℝ)
    (o : uniqueInfiniteComponent h'),
      ∃! u : uniqueInfiniteComponent h' → ℝ,
        IsCorrectedPlane (uniqueInfiniteComponent h') q u ∧ u o = 0

/-- Step `step:3.3-green-laplacian` (paper L903-907): let `B` be a finite set of open bonds with
endpoints in a cluster `C`, and `C'` a cluster with the same vertices after closing `B`. For a
harmonic function `ℓ'` on `C'` and a family `G` of Green columns on `C`, the function
`ℓ' + ∑_{e ∈ B} ∇_y G(·, e) (ℓ'(y) - ℓ'(x))` is harmonic on `C`. -/
def GreenLaplacianStep (d : ℕ) (hd : 2 ≤ d) : Prop :=
  ∀ (ω : Configuration d) (C : OpenComponent ω) (B : Finset (Bond d)),
    (∀ e ∈ B, ω e = true ∧ ∀ z ∈ (e : Sym2 (Vertex d)), z ∈ C.supp) →
    ∀ C' : OpenComponent (closeBonds B ω), C'.supp = C.supp →
    ∀ u' : C' → ℝ, (∀ x, componentLaplacian C' u' x = 0) →
    ∀ G : C → C → ℝ, (∀ y, IsGreenColumn d hd C y (G y)) →
    ∀ z : C, componentLaplacian C (fun x => extend C' u' x.val +
      ∑ e ∈ B, greenDipole (greenFunction C G) (extend C' u') x.val e.val) z = 0

/-- Step `step:3.3-green-sublinear` (paper L899-900, there from Proposition 2.6): a Green column on
a cluster grows sublinearly. -/
def GreenColumnSublinearStep (d : ℕ) (hd : 2 ≤ d) : Prop :=
  ∀ (ω : Configuration d) (C : OpenComponent ω) (y : C) (g : C → ℝ),
    IsGreenColumn d hd C y g → componentSlopeAsymptotics C 0 g

/-- Step `step:3.3-liouville` (paper L889, L896): almost surely, every sublinear harmonic function
on the unique infinite cluster is constant (Theorem 2.4 at order zero, Armstrong–Dario). -/
def SublinearLiouvilleStep (d : ℕ) [NeZero d] (p : unitInterval) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw d p, ∀ (h : HasUniqueInfiniteOpenComponent ω)
    (v : uniqueInfiniteComponent h → ℝ),
    (∀ x, componentLaplacian (uniqueInfiniteComponent h) v x = 0) →
    componentSlopeAsymptotics (uniqueInfiniteComponent h) 0 v → ∃ c : ℝ, ∀ x, v x = c

/-- The summand of Lemma 3.3 is the difference of the Green dipoles at its two points. -/
theorem compareSummand_eq_greenDipole_sub (g : Vertex d → Vertex d → ℝ) (w : Vertex d → ℝ)
    (a b : Vertex d) (e : Sym2 (Vertex d)) :
    compareSummand g w a b e = greenDipole g w a e - greenDipole g w b e := by
  induction e using Sym2.ind with
  | _ x y => simp only [compareSummand, greenDipole, Sym2.lift_mk]; ring

/-- The Laplacian of a cluster is additive. -/
theorem componentLaplacian_sub {ω : Configuration d} (C : OpenComponent ω) (u v : C → ℝ)
    (x : C) :
    componentLaplacian C (fun y => u y - v y) x =
      componentLaplacian C u x - componentLaplacian C v x := by
  simp only [componentLaplacian, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Slope asymptotics are compatible with differences. -/
theorem componentSlopeAsymptotics_sub {ω : Configuration d} (C : OpenComponent ω)
    {p q : Fin d → ℝ} {u v : C → ℝ} (hu : componentSlopeAsymptotics C p u)
    (hv : componentSlopeAsymptotics C q v) :
    componentSlopeAsymptotics C (p - q) (fun x => u x - v x) := by
  have h := componentSlopeAsymptotics_add C hu (componentSlopeAsymptotics_smul C hv (-1))
  rw [neg_one_smul, ← sub_eq_add_neg] at h
  convert h using 1
  funext x
  simp [sub_eq_add_neg]

/-- A finite sum of sublinear functions is sublinear. -/
theorem componentSlopeAsymptotics_zero_sum {ω : Configuration d} (C : OpenComponent ω)
    {ι : Type*} (s : Finset ι) (f : ι → C → ℝ)
    (hf : ∀ i ∈ s, componentSlopeAsymptotics C 0 (f i)) :
    componentSlopeAsymptotics C 0 (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty] using (isCorrectedPlane_const C 0).2
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    have h := componentSlopeAsymptotics_add C (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
    rw [add_zero] at h
    exact h

/-- Slope asymptotics transfer between two clusters with the same vertices. -/
theorem componentSlopeAsymptotics_extend {ω ω' : Configuration d} {C : OpenComponent ω}
    {C' : OpenComponent ω'} (hsupp : C'.supp = C.supp) {q : Fin d → ℝ} {u' : C' → ℝ}
    (hu' : componentSlopeAsymptotics C' q u') :
    componentSlopeAsymptotics C q (fun x => extend C' u' x.val) := by
  intro ε hε
  obtain ⟨R₀, hR₀, hR⟩ := hu' ε hε
  refine ⟨R₀, hR₀, fun R hRR x hx => ?_⟩
  have hx' : x.val ∈ C'.supp := by rw [hsupp]; exact x.property
  have hball : (⟨x.val, hx'⟩ : C') ∈ componentEuclideanBall C' 0 R := by
    rw [mem_componentEuclideanBall] at hx ⊢
    exact hx
  have hext : extend C' u' x.val = u' ⟨x.val, hx'⟩ := dif_pos hx'
  beta_reduce
  rw [hext]
  exact hR R hRR _ hball

/-- The Green dipole of an edge with both endpoints in the cluster is sublinear. -/
theorem greenDipole_sublinear {hd : 2 ≤ d} (hsub : GreenColumnSublinearStep d hd)
    {ω : Configuration d} (C : OpenComponent ω) (G : C → C → ℝ)
    (hG : ∀ y, IsGreenColumn d hd C y (G y)) (w : Vertex d → ℝ) (s : Sym2 (Vertex d))
    (hs : ∀ z ∈ s, z ∈ C.supp) :
    componentSlopeAsymptotics C 0 (fun x => greenDipole (greenFunction C G) w x.val s) := by
  induction s using Sym2.ind with
  | _ x₀ y₀ =>
    have hx₀ : x₀ ∈ C.supp := hs x₀ (Sym2.mem_mk_left x₀ y₀)
    have hy₀ : y₀ ∈ C.supp := hs y₀ (Sym2.mem_mk_right x₀ y₀)
    have h := componentSlopeAsymptotics_smul C (componentSlopeAsymptotics_sub C
      (hsub ω C _ _ (hG ⟨x₀, hx₀⟩)) (hsub ω C _ _ (hG ⟨y₀, hy₀⟩))) (w y₀ - w x₀)
    rw [sub_zero, smul_zero] at h
    convert h using 1
    funext x
    have hxC : (x : Vertex d) ∈ C.supp := x.2
    simp only [greenDipole, greenFunction, Section3.extend, Sym2.lift_mk, hxC, hx₀, hy₀,
      dite_true, Pi.smul_apply, smul_eq_mul]
    ring

/-- If every slope has a unique corrected plane normalized at a vertex `o`, corrected planes
exist and are unique up to additive constants. -/
theorem correctedPlane_exists_unique_add_const {ω : Configuration d} (C : OpenComponent ω)
    (q : Fin d → ℝ) (o : C) (h : ∃! u : C → ℝ, IsCorrectedPlane C q u ∧ u o = 0) :
    (∃ u, IsCorrectedPlane C q u) ∧
      ∀ u v, IsCorrectedPlane C q u → IsCorrectedPlane C q v → ∃ c : ℝ, ∀ x, u x = v x + c := by
  refine ⟨⟨_, h.exists.choose_spec.1⟩, fun u v hu hv => ⟨u o - v o, fun x => ?_⟩⟩
  have hshift : ∀ w, IsCorrectedPlane C q w →
      IsCorrectedPlane C q (fun x => w x - w o) ∧ (fun x => w x - w o) o = 0 := by
    intro w hw
    refine ⟨?_, sub_self _⟩
    have h' := isCorrectedPlane_sub C hw (isCorrectedPlane_const C (w o))
    rw [sub_zero] at h'
    exact h'
  have hx := congrFun (h.unique (hshift u hu) (hshift v hv)) x
  linarith

/-- Lemma 3.3 follows from its five steps, the existence and uniqueness of the infinite cluster,
the qualitative corrector input and the existence of the Green columns. -/
theorem compareDifferentPlanes_of_steps [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (huniq : LatticeProb.External.SupercriticalBondUniqueness)
    (hcorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hgreen : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hcluster : FlipClusterStep d) (hflip : FlipCorrectorStep d p)
    (hlap : GreenLaplacianStep d hd) (hsub : GreenColumnSublinearStep d hd)
    (hliou : SublinearLiouvilleStep d p) :
    Section3.CompareDifferentPlanesStmt d hd p := by
  filter_upwards [ae_unique_green_column_for_all_poles hgreen huniq d hd p hpc hp1,
    hcorr d hd p hpc hp1, hflip, hliou] with ω hGω hCω hFω hLω
  obtain ⟨h, hGh⟩ := hGω
  refine ⟨h, fun B hB hconn => ?_⟩
  obtain ⟨h', hsupp⟩ := hcluster ω h B hconn
  obtain ⟨o, ho⟩ := (uniqueInfiniteComponent_infinite h).nonempty
  have ho' : o ∈ (uniqueInfiniteComponent h').supp := by rw [hsupp]; exact ho
  refine ⟨h', hsupp, ⟨fun y => (hGh h y).exists.choose,
    fun y => (hGh h y).exists.choose_spec⟩, fun q => ?_⟩
  obtain ⟨hex, hun⟩ := correctedPlane_exists_unique_add_const _ q ⟨o, ho⟩ ((hCω h).1 q ⟨o, ho⟩)
  obtain ⟨hex', hun'⟩ := correctedPlane_exists_unique_add_const _ q ⟨o, ho'⟩ (hFω B h' q ⟨o, ho'⟩)
  refine ⟨hex, hun, hex', hun', fun u u' hu hu' G hG a b _ => ?_⟩
  obtain ⟨hhu, hsu⟩ := (isCorrectedPlane_iff_harmonic_and_slope_asymptotics _ q u).1 hu
  obtain ⟨hhu', hsu'⟩ := (isCorrectedPlane_iff_harmonic_and_slope_asymptotics _ q u').1 hu'
  -- `v = ℓ_p - ℓ'_p - ∑_{e ∈ B} ∇_y G(·, e) (ℓ'_p(y) - ℓ'_p(x))` is harmonic and sublinear.
  have hharm : ∀ z, componentLaplacian (uniqueInfiniteComponent h)
      (fun x => u x - extend _ u' x.val - ∑ e ∈ B,
        greenDipole (greenFunction _ G) (extend _ u') x.val e.val) z = 0 := by
    intro z
    have hlapz := hlap ω _ B hB _ hsupp u' hhu' G hG z
    rw [show (fun x => u x - extend _ u' x.val - ∑ e ∈ B,
        greenDipole (greenFunction _ G) (extend _ u') x.val e.val) =
        fun x => u x - (extend _ u' x.val + ∑ e ∈ B,
          greenDipole (greenFunction _ G) (extend _ u') x.val e.val) from
      funext fun x => by ring, componentLaplacian_sub, hlapz, hhu z, sub_zero]
  have hsl := componentSlopeAsymptotics_sub _
    (componentSlopeAsymptotics_sub _ hsu (componentSlopeAsymptotics_extend hsupp hsu'))
    (componentSlopeAsymptotics_zero_sum _ B _
      fun e he => greenDipole_sublinear hsub _ G hG (extend _ u') e.val (hB e he).2)
  rw [sub_self, sub_zero] at hsl
  obtain ⟨c, hc⟩ := hLω h _ hharm hsl
  have ha := hc a
  have hb := hc b
  show _ = ∑ e ∈ B, compareSummand (greenFunction _ G) (extend _ u') a.val b.val e.val
  simp only [compareSummand_eq_greenDipole_sub, Finset.sum_sub_distrib]
  linarith

end Rigidity.Steps.S3
