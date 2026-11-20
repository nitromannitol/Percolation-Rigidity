import Rigidity.Percolation.BondSeedProduct

/-!
# Seed exploration with branching histories

The exposed bonds may depend on a finite exploration history. A fresh seed on
each history gives a uniform one-step contraction of survival probability.
-/

namespace Rigidity.Percolation

open Function LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External
open scoped MeasureTheory

/-- A finite measurable partition of the current survival event can use a
different exposed bond set and a different fresh seed on each branch. -/
theorem measureReal_survival_step_le_of_fresh_seed_histories {d : ℕ} {ι : Type*}
    [Fintype ι] (p : unitInterval) (N : ℕ) (F : ι → Set (Bond d))
    (U : ι → Set (Vertex d)) (hU : ∀ i, (U i).Finite)
    (hN : ∀ i, (finite_localBonds (hU i)).toFinset.card ≤ N)
    (hfresh : ∀ i, Disjoint (localBonds (U i)) (F i))
    (A : ι → Set (Configuration d)) {G H : Set (Configuration d)}
    (hA : ∀ i, MeasurableSet[bondSigma (F i)] (A i))
    (hGA : ∀ i, MeasurableSet[bondSigma (F i)] (G ∩ A i))
    (hH : MeasurableSet H) (hcover : G ⊆ ⋃ i, A i)
    (hpair : Pairwise (Disjoint on A)) (hHG : H ⊆ G)
    (hfail : ∀ i, Disjoint (H ∩ A i) (fullyOpenRegion (U i))) :
    (latticeBondLaw d p).real H ≤
      (1 - (p : ℝ) ^ N) * (latticeBondLaw d p).real G := by
  classical
  let μ := latticeBondLaw d p
  let δ : ℝ := (p : ℝ) ^ N
  have hbranch : ∀ i, μ.real (H ∩ A i) ≤ (1 - δ) * μ.real (G ∩ A i) := by
    intro i
    have hcond : ∀ᵐ ω ∂μ.restrict (G ∩ A i),
        δ ≤ μ[(fullyOpenRegion (U i)).indicator (fun _ => (1 : ℝ)) | bondSigma (F i)] ω := by
      have heq := condExp_indicator_eq_of_disjoint_bonds p (hfresh i)
        (measurableSet_fullyOpenRegion_localBond (U i))
      filter_upwards [ae_restrict_of_ae heq] with ω hω
      rw [hω]
      exact latticeBondLaw_real_fullyOpenRegion_lower p (U i) (hU i) N (hN i)
    have hHAm : MeasurableSet (H ∩ A i) := hH.inter (bondSigma_le (F i) _ (hA i))
    have hUm : MeasurableSet (fullyOpenRegion (U i)) :=
      bondSigma_le (localBonds (U i)) _ (measurableSet_fullyOpenRegion_localBond (U i))
    have hupper := condExp_indicator_le_one_sub_of_disjoint μ (bondSigma_le (F i))
      hHAm hUm (hfail i) δ hcond
    exact measureReal_le_mul_of_condExp_indicator_le μ (bondSigma_le (F i)) (hGA i)
      hHAm (Set.inter_subset_inter_left _ hHG) (1 - δ) hupper
  have hGpartition : (⋃ i, G ∩ A i) = G := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨i, hG, _⟩
      exact hG
    · intro hG
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hG)
      exact ⟨i, hG, hi⟩
  have hdisj : Pairwise (Disjoint on fun i => G ∩ A i) := by
    intro i j hij
    exact (hpair hij).mono Set.inter_subset_right Set.inter_subset_right
  have hGm : ∀ i, MeasurableSet (G ∩ A i) :=
    fun i => bondSigma_le (F i) _ (hGA i)
  have hHcover : H ⊆ ⋃ i, H ∩ A i := by
    intro ω hω
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover (hHG hω))
    exact Set.mem_iUnion.mpr ⟨i, hω, hi⟩
  calc
    μ.real H ≤ μ.real (⋃ i, H ∩ A i) := measureReal_mono hHcover (measure_ne_top _ _)
    _ ≤ ∑ i, μ.real (H ∩ A i) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ i, (1 - δ) * μ.real (G ∩ A i) := Finset.sum_le_sum fun i _ => hbranch i
    _ = (1 - δ) * μ.real G := by
      rw [← Finset.mul_sum, ← measureReal_iUnion_fintype hdisj hGm, hGpartition]

/-- Repeated tests of fresh seeds along finite branching histories have a
geometric survival bound. The exposed bonds may differ between histories. -/
theorem measureReal_survival_le_of_fresh_seed_histories {d : ℕ} (ι : ℕ → Type*)
    [∀ n, Fintype (ι n)] (p : unitInterval) (N : ℕ)
    (F : ∀ n, ι n → Set (Bond d)) (U : ∀ n, ι n → Set (Vertex d))
    (hU : ∀ n i, (U n i).Finite)
    (hN : ∀ n i, (finite_localBonds (hU n i)).toFinset.card ≤ N)
    (hfresh : ∀ n i, Disjoint (localBonds (U n i)) (F n i))
    (A : ∀ n, ι n → Set (Configuration d)) (G : ℕ → Set (Configuration d))
    (hA : ∀ n i, MeasurableSet[bondSigma (F n i)] (A n i))
    (hGA : ∀ n i, MeasurableSet[bondSigma (F n i)] (G n ∩ A n i))
    (hG : ∀ n, MeasurableSet (G n)) (hcover : ∀ n, G n ⊆ ⋃ i, A n i)
    (hpair : ∀ n, Pairwise (Disjoint on A n)) (hdecr : ∀ n, G (n + 1) ⊆ G n)
    (hfail : ∀ n i, Disjoint (G (n + 1) ∩ A n i) (fullyOpenRegion (U n i))) :
    ∀ n, (latticeBondLaw d p).real (G n) ≤ (1 - (p : ℝ) ^ N) ^ n := by
  have hq : 0 ≤ 1 - (p : ℝ) ^ N :=
    sub_nonneg.mpr (pow_le_one₀ p.property.1 p.property.2)
  intro n
  induction n with
  | zero =>
    simpa only [pow_zero] using (measureReal_le_one (μ := latticeBondLaw d p) (s := G 0))
  | succ n ih =>
    have hstep := measureReal_survival_step_le_of_fresh_seed_histories p N (F n) (U n)
      (hU n) (hN n) (hfresh n) (A n) (hA n) (hGA n) (hG (n + 1)) (hcover n)
      (hpair n) (hdecr n) (hfail n)
    exact hstep.trans (by simpa only [pow_succ, mul_comm] using
      mul_le_mul_of_nonneg_left ih hq)

/-- The branching-history bound remains valid when each history and exposed
bond set also depend on an independent base configuration. -/
theorem measureReal_prod_survival_le_of_fresh_seed_histories {d : ℕ} (ι : ℕ → Type*)
    [∀ n, Fintype (ι n)] (q r : unitInterval) (N : ℕ)
    (F : Configuration d → ∀ n, ι n → Set (Bond d))
    (U : Configuration d → ∀ n, ι n → Set (Vertex d))
    (hU : ∀ b n i, (U b n i).Finite)
    (hN : ∀ b n i, (finite_localBonds (hU b n i)).toFinset.card ≤ N)
    (hfresh : ∀ b n i, Disjoint (localBonds (U b n i)) (F b n i))
    (A : Configuration d → ∀ n, ι n → Set (Configuration d))
    (G : ℕ → Set (Configuration d × Configuration d))
    (hA : ∀ b n i, MeasurableSet[bondSigma (F b n i)] (A b n i))
    (hGA : ∀ b n i, MeasurableSet[bondSigma (F b n i)]
      ((Prod.mk b ⁻¹' G n) ∩ A b n i))
    (hG : ∀ n, MeasurableSet (G n))
    (hcover : ∀ b n, Prod.mk b ⁻¹' G n ⊆ ⋃ i, A b n i)
    (hpair : ∀ b n, Pairwise (Disjoint on A b n)) (hdecr : ∀ n, G (n + 1) ⊆ G n)
    (hfail : ∀ b n i, Disjoint ((Prod.mk b ⁻¹' G (n + 1)) ∩ A b n i)
      (fullyOpenRegion (U b n i))) :
    ∀ n, ((latticeBondLaw d q).prod (latticeBondLaw d r)).real (G n) ≤
      (1 - (r : ℝ) ^ N) ^ n := by
  intro n
  apply measureReal_prod_le_of_sections (latticeBondLaw d q) (latticeBondLaw d r)
    (hG n) (pow_nonneg (sub_nonneg.mpr (pow_le_one₀ r.property.1 r.property.2)) n)
  intro b
  exact measureReal_survival_le_of_fresh_seed_histories ι r N (F b) (U b) (hU b)
    (hN b) (hfresh b) (A b) (fun n => Prod.mk b ⁻¹' G n) (hA b) (hGA b)
    (fun n => measurable_prodMk_left (hG n)) (hcover b) (hpair b)
    (fun n => Set.preimage_mono (hdecr n)) (hfail b) n

end Rigidity.Percolation
