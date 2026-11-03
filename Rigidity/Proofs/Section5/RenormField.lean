import Rigidity.Steps.Section5.RenormalizedDomination

/-!
# Lemma 5.23: measurability and `1`-dependence of the renormalized percolation process

Steps `step:5.23-measurable` and `step:5.23-one-dependence` of Lemma 5.23
(`lemma:renormalized-domination`, corrected draft L2213-2217, L2244-2250), with no literature
input.

The event that `x + Q_r` is very good is determined by the bonds with both endpoints in
`x + Q_{r + 2⌊r/10⌋}` (`isVeryGood_congr`): its largest clusters, its good subcubes and its Kesten
channels are read off the open edges inside the cube, its bands, and the subcubes of radius at most
`r/10` meeting it. Each site of the renormalized field is then a function of finitely many bonds,
hence measurable. For `r = ⌊11R/10⌋` the radius `r + 2⌊r/10⌋` is at most `2R`, so the cubes of two
sites at `ℓ^∞` distance at least `2` are disjoint (their centres are `2(2R + 1)` apart in some
coordinate), and the restrictions of the field to two such sets of sites are functions of disjoint
sets of bonds, independent under the product law.
-/

open MeasureTheory ProbabilityTheory LatticeProb.Percolation

namespace Rigidity.Proofs.Section5

open Rigidity.Section5

/-- The bonds with both endpoints in `D`. -/
def bondsIn (D : Set (Vertex 2)) : Set (Bond 2) := {e | ∀ v ∈ e.1, v ∈ D}

theorem bondOfAdjacent_mem_bondsIn {D : Set (Vertex 2)} {y z : Vertex 2}
    (h : (nearestNeighborGraph 2).Adj y z) (hy : y ∈ D) (hz : z ∈ D) :
    bondOfAdjacent h ∈ bondsIn D := by
  intro v hv
  rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption

/-- The open edges inside `B` only depend on the bonds inside a set `D ⊇ B`. -/
theorem openIn_eq_of_eqOn {ω ω' : Configuration 2} {B D : Set (Vertex 2)} (hBD : B ⊆ D)
    (h : ∀ e ∈ bondsIn D, ω e = ω' e) : openIn ω B = openIn ω' B := by
  ext y z
  simp only [openIn, openGraph_adj_iff]
  constructor
  · rintro ⟨⟨hyz, ho⟩, hy, hz⟩
    exact ⟨⟨hyz, (h _ (bondOfAdjacent_mem_bondsIn hyz (hBD hy) (hBD hz))) ▸ ho⟩, hy, hz⟩
  · rintro ⟨⟨hyz, ho⟩, hy, hz⟩
    exact ⟨⟨hyz, (h _ (bondOfAdjacent_mem_bondsIn hyz (hBD hy) (hBD hz))).symm ▸ ho⟩, hy, hz⟩

theorem cubeAt_mono (x : Vertex 2) {r r' : ℕ} (h : r ≤ r') : cubeAt x r ⊆ cubeAt x r' :=
  fun _ hy i => (hy i).trans (by exact_mod_cast h)

/-- A cube of radius `M ≤ r/10` meeting `x + Q_r` lies in `x + Q_{r + 2⌊r/10⌋}`. -/
theorem cubeAt_subset_of_meets {x z : Vertex 2} {r M : ℕ} (hM : (M : ℝ) ≤ r / 10)
    (hne : (cubeAt z M ∩ cubeAt x r).Nonempty) : cubeAt z M ⊆ cubeAt x (r + 2 * (r / 10)) := by
  obtain ⟨w, hwz, hwx⟩ := hne
  have hM' : M ≤ r / 10 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have : (M : ℝ) * 10 ≤ r := by linarith
    exact_mod_cast this
  intro y hy i
  have h1 := abs_le.mp (hy i)
  have h2 := abs_le.mp (hwz i)
  have h3 := abs_le.mp (hwx i)
  have hM'' : (M : ℤ) ≤ ((r / 10 : ℕ) : ℤ) := by exact_mod_cast hM'
  rw [abs_le]
  push_cast
  constructor <;> linarith

/-- **Locality of very good cubes.** Whether `x + Q_r` is very good depends only on the bonds with
both endpoints in `x + Q_{r + 2⌊r/10⌋}`. -/
theorem isVeryGood_congr {ω ω' : Configuration 2} {x : Vertex 2} {r : ℕ}
    (h : ∀ e ∈ bondsIn (cubeAt x (r + 2 * (r / 10))), ω e = ω' e) :
    IsVeryGood ω x r ↔ IsVeryGood ω' x r := by
  have key : ∀ ω ω' : Configuration 2,
      (∀ e ∈ bondsIn (cubeAt x (r + 2 * (r / 10))), ω e = ω' e) →
        IsVeryGood ω x r → IsVeryGood ω' x r := by
    intro ω ω' h
    have hsub : ∀ B ⊆ cubeAt x (r + 2 * (r / 10)), openIn ω B = openIn ω' B :=
      fun B hB => openIn_eq_of_eqOn hB h
    have hcube : cubeAt x r ⊆ cubeAt x (r + 2 * (r / 10)) := cubeAt_mono x (by omega)
    have hch : ∀ i k, HasKestenChannels ω x r i k → HasKestenChannels ω' x r i k := by
      intro i k hk j hj
      obtain ⟨y, z, hy, hz, hyi, hzi, hr⟩ := hk j hj
      refine ⟨y, z, hy, hz, hyi, hzi, ?_⟩
      rwa [← hsub _ (Set.Subset.trans (fun _ hv => hv.1) hcube)]
    rintro ⟨⟨h1, hcross, hgood⟩, hch0, hch1⟩
    refine ⟨⟨h1, ?_, fun z M hM1 hM2 hne => ?_⟩, hch _ _ hch0, hch _ _ hch1⟩
    · unfold IsCrossingCube IsLargestClusterIn at hcross ⊢
      rwa [← hsub _ hcube]
    · have hz := hgood z M hM1 hM2 hne
      unfold IsGoodSubcube IsLargestClusterIn at hz ⊢
      rwa [← hsub _ (cubeAt_subset_of_meets hM2 hne)]
  exact ⟨key ω ω' h, key ω' ω fun e he => (h e he).symm⟩

theorem finite_cubeAt (x : Vertex 2) (r : ℕ) : (cubeAt x r).Finite := by
  refine (Set.finite_Icc (x - fun _ => (r : ℤ)) (x + fun _ => (r : ℤ))).subset fun y hy => ?_
  refine ⟨fun i => ?_, fun i => ?_⟩ <;>
  · have := abs_le.mp (hy i)
    simp only [Pi.sub_apply, Pi.add_apply]
    linarith

theorem finite_bondsIn {D : Set (Vertex 2)} (hD : D.Finite) : (bondsIn D).Finite := by
  refine (hD.toFinset.sym2.finite_toSet.preimage Subtype.val_injective.injOn).subset
    fun e he => ?_
  simp only [Set.mem_preimage, Finset.mem_coe, Finset.mem_sym2_iff, Set.Finite.mem_toFinset]
  exact he

/-- An event determined by the bonds of a finite set is measurable. -/
theorem measurableSet_of_eqOn {S : Set (Configuration 2)} {E : Set (Bond 2)} (hE : E.Finite)
    (h : ∀ ω ω' : Configuration 2, (∀ e ∈ E, ω e = ω' e) → ω ∈ S → ω' ∈ S) :
    MeasurableSet S := by
  haveI := hE.to_subtype
  let ρ : Configuration 2 → (E → Bool) := fun ω e => ω e
  have hρ : Measurable ρ := measurable_pi_lambda _ fun e => measurable_pi_apply _
  have hS : S = ρ ⁻¹' (ρ '' S) := by
    ext ω
    refine ⟨fun hω => ⟨ω, hω, rfl⟩, ?_⟩
    rintro ⟨ω', hω', hρω⟩
    exact h ω' ω (fun e he => congrFun hρω ⟨e, he⟩) hω'
  rw [hS]
  exact hρ (Set.toFinite _).measurableSet

/-- The event that `x + Q_r` is very good is measurable. -/
theorem measurableSet_isVeryGood (x : Vertex 2) (r : ℕ) :
    MeasurableSet {ω : Configuration 2 | IsVeryGood ω x r} :=
  measurableSet_of_eqOn (finite_bondsIn (finite_cubeAt x (r + 2 * (r / 10))))
    fun _ _ h hω => (isVeryGood_congr h).mp hω

/-- **Step `step:5.23-measurable`.** The renormalized percolation process is measurable. -/
theorem renormFieldMeasurableStep : Steps.Section5.RenormFieldMeasurableStep := by
  intro R
  refine measurable_pi_lambda _ fun z => measurable_to_bool ?_
  convert measurableSet_isVeryGood (renormCentre R z) (11 * R / 10) using 1
  ext ω
  simp [renormField]

/-- The radius of the cube of bonds on which the renormalized site depends. -/
def renormRadius (R : ℕ) : ℕ := 11 * R / 10 + 2 * (11 * R / 10 / 10)

theorem renormRadius_le (R : ℕ) : renormRadius R ≤ 2 * R := by
  unfold renormRadius
  omega

/-- The cubes of radius `renormRadius R` around the centres of two renormalized sites at `ℓ^∞`
distance at least `2` are disjoint. -/
theorem not_mem_cubeAt_renormCentre {R : ℕ} {i j : PlanarCarrier}
    (hij : (1 : ℤ) < max |i.1 - j.1| |i.2 - j.2|) {v : Vertex 2}
    (hi : v ∈ cubeAt (renormCentre R i) (renormRadius R)) :
    v ∉ cubeAt (renormCentre R j) (renormRadius R) := by
  intro hj
  have hρ : ((renormRadius R : ℕ) : ℤ) ≤ 2 * R := by exact_mod_cast renormRadius_le R
  have hA : (0 : ℤ) < 2 * R + 1 := by positivity
  have hsep : ∀ (a b : ℤ) (k : Fin 2), renormCentre R i k = (2 * R + 1) * a →
      renormCentre R j k = (2 * R + 1) * b → 1 < |a - b| → False := by
    intro a b k ha hb hab
    have h1 := abs_le.mp (hi k)
    have h2 := abs_le.mp (hj k)
    rw [ha] at h1
    rw [hb] at h2
    rcases lt_abs.mp hab with hab | hab
    · nlinarith
    · nlinarith
  rcases lt_max_iff.mp hij with h | h
  · exact hsep i.1 j.1 0 (by simp [renormCentre]) (by simp [renormCentre]) h
  · exact hsep i.2 j.2 1 (by simp [renormCentre]) (by simp [renormCentre]) h

/-- The bonds on which the renormalized sites of `I` depend. -/
noncomputable def renormBonds (R : ℕ) (I : Finset PlanarCarrier) : Finset (Bond 2) :=
  (finite_bondsIn ((I : Set PlanarCarrier).toFinite.biUnion
    fun i _ => finite_cubeAt (renormCentre R i) (renormRadius R))).toFinset

theorem mem_renormBonds {R : ℕ} {I : Finset PlanarCarrier} {i : PlanarCarrier} (hi : i ∈ I)
    {e : Bond 2} (he : e ∈ bondsIn (cubeAt (renormCentre R i) (renormRadius R))) :
    e ∈ renormBonds R I := by
  rw [renormBonds, Set.Finite.mem_toFinset]
  exact fun v hv => Set.mem_biUnion (Finset.mem_coe.mpr hi) (he v hv)

theorem disjoint_renormBonds {R : ℕ} {I J : Finset PlanarCarrier}
    (hIJ : ∀ i ∈ I, ∀ j ∈ J, (1 : ℤ) < max |i.1 - j.1| |i.2 - j.2|) :
    Disjoint (renormBonds R I) (renormBonds R J) := by
  rw [Finset.disjoint_left]
  intro e heI heJ
  rw [renormBonds, Set.Finite.mem_toFinset] at heI heJ
  obtain ⟨a, b, hab, -⟩ := e.2
  have ha : a ∈ e.1 := hab ▸ Sym2.mem_mk_left a b
  obtain ⟨i, hi, hai⟩ := Set.mem_iUnion₂.mp (heI a ha)
  obtain ⟨j, hj, haj⟩ := Set.mem_iUnion₂.mp (heJ a ha)
  exact not_mem_cubeAt_renormCentre (hIJ i hi j hj) hai haj

/-- The sites of `I` of the renormalized field, as a function of the bonds of `renormBonds R I`. -/
noncomputable def renormLocal (R : ℕ) (I : Finset PlanarCarrier) (ξ : renormBonds R I → Bool) :
    I → Bool :=
  fun i => renormField R (fun e => if h : e ∈ renormBonds R I then ξ ⟨e, h⟩ else true) i

theorem renormField_restrict_eq (R : ℕ) (I : Finset PlanarCarrier) :
    (fun ω : Configuration 2 => fun i : I => renormField R ω i) =
      renormLocal R I ∘ fun ω (e : renormBonds R I) => ω e := by
  funext ω i
  simp only [Function.comp, renormLocal, renormField]
  refine decide_eq_decide.mpr (isVeryGood_congr fun e he => ?_)
  rw [dif_pos (mem_renormBonds i.2 he)]

/-- **Step `step:5.23-one-dependence`.** The renormalized percolation process is `1`-dependent
for the `ℓ^∞` distance of `ℤ²`. -/
theorem renormFieldOneDependentStep : Steps.Section5.RenormFieldOneDependentStep := by
  intro p R I J hIJ
  rw [indepFun_map_iff_of_measurable (renormFieldMeasurableStep R)
    (measurable_finsetRestrict_planar I) (measurable_finsetRestrict_planar J)]
  have hind := ((latticeBondLaw_iIndepFun (d := 2) p).indepFun_finset (renormBonds R I)
    (renormBonds R J) (disjoint_renormBonds hIJ) fun e => measurable_pi_apply e).comp
    (measurable_of_finite (renormLocal R I)) (measurable_of_finite (renormLocal R J))
  convert hind using 1
  · exact renormField_restrict_eq R I
  · exact renormField_restrict_eq R J

end Rigidity.Proofs.Section5
