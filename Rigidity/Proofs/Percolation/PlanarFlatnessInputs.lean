import Rigidity.Proofs.Percolation.PlanarFiniteVolumeClose
import Rigidity.Proofs.Percolation.PlanarNablaAffine
import Rigidity.Proofs.Percolation.PlanarNuEnergyDefect
import Rigidity.Proofs.Percolation.PlanarNuIncrements
import Rigidity.Proofs.Multiscale.Affine

/-!
# The inputs of Lemmas 5.8 and 5.9 of Armstrong and Dario in dimension two

Lemmas 5.8 (flatness) and 5.9 (decay of `ω`) of Armstrong and Dario are deduced from Lemma 5.7
(the weak convergence of the spatial averages of the coarsened gradients of the minimizers of
`μ`), Lemma 5.5 (the spatial averages of the coarsened gradients are almost additive) and the
bounds (4.24), (4.25) on the energy of the coarsened minimizers. We state these as they are
printed, in dimension two, in the vocabulary of the planar modules.

* `PlanarWeakConvergence`: display (5.25) of Lemma 5.7,
  `E[| |□|⁻¹ ⟨∇[u(·, □, q)]_P⟩_□ - ā_{□_n}⁻¹ q |²] ≤ C |q|² (τ_n + 3^{-n/4})`
  for every triadic cube `□` of scale `n` (Armstrong and Dario state it for `□_n` and use it for
  every `z + □_n`, the law of `μ` being stationary).
* `PlanarRestrictQuadCoarsenMu`, `PlanarRestrictQuadCoarsenNu`: display (5.12) of Lemma 5.5, for
  `m, n` with `n ∈ [(9/10) m, m)`, every cube `□` of scale `m` and every slope,
  `E[3^{-2(m-n)} |□_n|⁻² ∑_z |⟨∇[u(·, □, q)]_P⟩_{z+□_n} - ⟨∇[u(·, z+□_n, q)]_P⟩_{z+□_n}|²]
    ≤ C |q|² (∑_{k=n}^{m-1} τ_k + 3^{-n/4})`,
  and likewise for the maximizers `v` of `ν`. Armstrong and Dario print the upper limit `m + 1`
  in (5.12); their proof (the last display of the proof of Lemma 5.5) and the application in the
  proof of Lemma 5.8 give `m - 1`, which is the form stated here.
* `PlanarCoarseGradMomentMu`, `PlanarCoarseGradMomentNu`: the bounds (4.24), (4.25) on the
  `L²` norms of the coarsened gradients, in expectation: for every `δ > 0`,
  `E[|□|⁻¹ ∫_□ |∇[u(·, □, q)]_P|²] ≤ C(δ) |q|² size(□)^δ`.

The minimizers `planarMuMinimizer` and the maximizers `planarNuSolution` vanish off the partition
event and for unresolved cubes. For `μ` this is the convention of Armstrong and Dario that
`u(·, □, q) = 0` when `□` is not in `P_*`; for `ν` the convention `v(·, □, p) = 0` off `P_*` is the
choice of this formalization. The bounds on
expectations are bounds on the expectations of random variables; for the quantities of Lemma 5.5
and of (4.24), (4.25), whose measurability is not proved here, the measurability is part of the
statement.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical Matrix

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- The spatial sum `⟨∇w⟩_V · e_j` of the gradient of a function over the lattice edges of a
triadic cube `V` in direction `e_j`. -/
noncomputable def cubeGradSum (V : TriadicCube 2) (w : Vertex 2 → ℝ) (j : Fin 2) : ℝ :=
  Rigidity.Proofs.Multiscale.gradSum V.toIntegerCube.vertices w j

/-- The normalized spatial average `|V|⁻¹ ⟨e_j, ∇[u(·, V, q)]_P⟩_V` of the coarsened gradient of
the minimizer of `μ(V, q)`. -/
noncomputable def planarMuGradAvg (ω : Configuration 2) (V : TriadicCube 2) (q : Fin 2 → ℝ)
    (j : Fin 2) : ℝ :=
  coarsePairing ω V (Pi.single j 1) (planarMuMinimizer ω V q) / V.volume

/-- The maximizer `v(·, U, p)` of `ν(U, p)` on the partition event and for a resolved cube, and
zero otherwise (a choice of this formalization for cubes outside `P_*`). -/
noncomputable def planarNuSolution (ω : Configuration 2) (U : TriadicCube 2) (p : Fin 2 → ℝ) :
    ClusterFun ω U :=
  if PlanarPartitionEvent ω ∧ PlanarResolved ω U then planarNuMaximizer ω U p else 0

/-- The normalized spatial average `|V|⁻¹ ⟨e_j, ∇[v(·, V, p)]_P⟩_V` of the coarsened gradient of
the maximizer of `ν(V, p)`. -/
noncomputable def planarNuGradAvg (ω : Configuration 2) (V : TriadicCube 2) (p : Fin 2 → ℝ)
    (j : Fin 2) : ℝ :=
  coarsePairing ω V (Pi.single j 1) (planarNuSolution ω V p) / V.volume

/-- **Lemma 5.7 of Armstrong and Dario** (display (5.25), in dimension two), for every triadic
cube `V` of scale `n`:
`E[∑_j (|V|⁻¹ ⟨e_j, ∇[u(·, V, q)]_P⟩_V - (ā_{□_n}⁻¹ q)_j)²] ≤ C |q|² (τ_n + 3^{-n/4})`. -/
def PlanarWeakConvergence (p : unitInterval) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : TriadicCube 2) (q : Fin 2 → ℝ),
    ∫⁻ ω, ENNReal.ofReal (∑ j : Fin 2,
        (planarMuGradAvg ω V q j - (planarAhomInvFinite p V.scale *ᵥ q) j) ^ 2)
        ∂(latticeBondLaw 2 p) ≤
      ENNReal.ofReal (C * (q 0 ^ 2 + q 1 ^ 2) *
        (planarTau p V.scale + (3 : ℝ) ^ (-(V.scale : ℝ) / 4)))

/-- The quantity of display (5.12) for `μ`: the mean over the subcubes `V` of scale `n` of `U` of
`∑_j ((⟨∇[u(·, U, q)]_P⟩_V - ⟨∇[u(·, V, q)]_P⟩_V) · e_j / |V|)²`. -/
noncomputable def planarMuRestrictError (ω : Configuration 2) (U : TriadicCube 2) (n : ℕ)
    (q : Fin 2 → ℝ) : ℝ :=
  ((subcubesAt U n).card : ℝ)⁻¹ * ∑ V ∈ subcubesAt U n, ∑ j : Fin 2,
    ((cubeGradSum V (coarsen ω U (planarMuMinimizer ω U q)) j -
      coarsePairing ω V (Pi.single j 1) (planarMuMinimizer ω V q)) / V.volume) ^ 2

/-- The quantity of display (5.12) for `ν`. -/
noncomputable def planarNuRestrictError (ω : Configuration 2) (U : TriadicCube 2) (n : ℕ)
    (p : Fin 2 → ℝ) : ℝ :=
  ((subcubesAt U n).card : ℝ)⁻¹ * ∑ V ∈ subcubesAt U n, ∑ j : Fin 2,
    ((cubeGradSum V (coarsen ω U (planarNuSolution ω U p)) j -
      coarsePairing ω V (Pi.single j 1) (planarNuSolution ω V p)) / V.volume) ^ 2

/-- **Lemma 5.5 of Armstrong and Dario for `μ`** (display (5.12), first term, in dimension two).
-/
def PlanarRestrictQuadCoarsenMu (p : unitInterval) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : TriadicCube 2) (n : ℕ), 9 * U.scale ≤ 10 * n → n < U.scale →
    ∀ q : Fin 2 → ℝ,
      AEMeasurable (fun ω => planarMuRestrictError ω U n q) (latticeBondLaw 2 p) ∧
      ∫⁻ ω, ENNReal.ofReal (planarMuRestrictError ω U n q) ∂(latticeBondLaw 2 p) ≤
        ENNReal.ofReal (C * (q 0 ^ 2 + q 1 ^ 2) *
          (∑ k ∈ Finset.Ico n U.scale, planarTau p k + (3 : ℝ) ^ (-(n : ℝ) / 4)))

/-- **Lemma 5.5 of Armstrong and Dario for `ν`** (display (5.12), second term, in dimension
two). -/
def PlanarRestrictQuadCoarsenNu (p : unitInterval) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : TriadicCube 2) (n : ℕ), 9 * U.scale ≤ 10 * n → n < U.scale →
    ∀ ξ : Fin 2 → ℝ,
      AEMeasurable (fun ω => planarNuRestrictError ω U n ξ) (latticeBondLaw 2 p) ∧
      ∫⁻ ω, ENNReal.ofReal (planarNuRestrictError ω U n ξ) ∂(latticeBondLaw 2 p) ≤
        ENNReal.ofReal (C * (ξ 0 ^ 2 + ξ 1 ^ 2) *
          (∑ k ∈ Finset.Ico n U.scale, planarTau p k + (3 : ℝ) ^ (-(n : ℝ) / 4)))

/-- The normalized energy `|U|⁻¹ ∑_{x ∈ U} |∇[w]_P|²(x)` of the coarsening of a function on the
cluster of `U`, the gradient being taken on the lattice points of `U`. -/
noncomputable def coarseEnergy (ω : Configuration 2) (U : TriadicCube 2) (w : ClusterFun ω U) :
    ℝ :=
  U.volume⁻¹ * ∑ x ∈ U.toIntegerCube.vertices,
    Rigidity.Proofs.Multiscale.gradNormSq U.toIntegerCube.vertices (coarsen ω U w) x

/-- **The energy of the coarsened minimizers of `μ`** (Armstrong and Dario, (4.24), in
expectation, in dimension two). -/
def PlanarCoarseGradMomentMu (p : unitInterval) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : TriadicCube 2) (q : Fin 2 → ℝ),
    AEMeasurable (fun ω => coarseEnergy ω U (planarMuMinimizer ω U q)) (latticeBondLaw 2 p) ∧
    ∫⁻ ω, ENNReal.ofReal (coarseEnergy ω U (planarMuMinimizer ω U q)) ∂(latticeBondLaw 2 p) ≤
      ENNReal.ofReal (C * (q 0 ^ 2 + q 1 ^ 2) * (3 : ℝ) ^ (δ * U.scale))

/-- **The energy of the coarsened maximizers of `ν`** (Armstrong and Dario, (4.25), in
expectation, in dimension two). -/
def PlanarCoarseGradMomentNu (p : unitInterval) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : TriadicCube 2) (ξ : Fin 2 → ℝ),
    AEMeasurable (fun ω => coarseEnergy ω U (planarNuSolution ω U ξ)) (latticeBondLaw 2 p) ∧
    ∫⁻ ω, ENNReal.ofReal (coarseEnergy ω U (planarNuSolution ω U ξ)) ∂(latticeBondLaw 2 p) ≤
      ENNReal.ofReal (C * (ξ 0 ^ 2 + ξ 1 ^ 2) * (3 : ℝ) ^ (δ * U.scale))

/-- The coarse pairing with `e_j` is the spatial sum of the gradient of the coarsening. -/
theorem coarsePairing_single_eq_cubeGradSum (U : TriadicCube 2) (u : ClusterFun ω U)
    (j : Fin 2) :
    coarsePairing ω U (Pi.single j 1) u = cubeGradSum U (coarsen ω U u) j := by
  rw [coarsePairing_apply, cubeGradSum, Rigidity.Proofs.Multiscale.gradSum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single j (fun i _ hij => by simp [hij]) (by simp)]
  simp only [Pi.single_eq_same, one_mul, coarsen]
  rfl

/-- The subcubes of scale `k ≤ m` of the cube of scale `m` and index `z` are the cubes of scale
`k` whose indices lie in the cube of scale `m - k` and index `z`. -/
theorem subcubesAt_eq_image {m k : ℕ} (hk : k ≤ m) (z : Vertex 2) :
    subcubesAt (⟨m, z⟩ : TriadicCube 2) k =
      (Rigidity.Proofs.Multiscale.cube (m - k) z).image fun j => (⟨k, j⟩ : TriadicCube 2) := by
  ext V
  simp only [subcubesAt, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(scaleCube k x).index, ?_, ?_⟩
    · rw [← Rigidity.Proofs.Multiscale.pow_mul_mem_cube_iff hk]
      have hc : (fun i => 3 ^ k * (scaleCube k x).index i) ∈ (scaleCube k x).vertices := by
        intro i
        have hs : (scaleCube k x).side = 3 ^ k := by
          rw [TriadicCube.side, scale_scaleCube]
        rw [hs]
        simp only [sub_self, mul_zero, abs_zero]
        positivity
      have hsub := scaleCube_subset (U := ⟨m, z⟩) hk ((TriadicCube.mem_toIntegerCube_vertices _ _).1
        hx) hc
      exact (TriadicCube.mem_toIntegerCube_vertices _ _).2 hsub
    · exact TriadicCube.ext (scale_scaleCube k x).symm rfl
  · rintro ⟨j, hj, rfl⟩
    have hj' := (Rigidity.Proofs.Multiscale.pow_mul_mem_cube_iff hk z j).2 hj
    refine ⟨fun i => 3 ^ k * j i, hj', ?_⟩
    refine TriadicCube.eq_of_mem_of_scale_eq (scale_scaleCube k _) (mem_scaleCube k _) ?_
    intro i
    change |2 * (3 ^ k * j i - (3 : ℤ) ^ k * j i)| < (3 : ℤ) ^ k
    simp only [sub_self, mul_zero, abs_zero]
    positivity

/-- A sum over the subcubes of scale `k ≤ m` is a sum over their indices. -/
theorem sum_subcubesAt_eq {β : Type*} [AddCommMonoid β] {m k : ℕ} (hk : k ≤ m) (z : Vertex 2)
    (F : TriadicCube 2 → β) :
    ∑ V ∈ subcubesAt (⟨m, z⟩ : TriadicCube 2) k, F V =
      ∑ j ∈ Rigidity.Proofs.Multiscale.cube (m - k) z, F ⟨k, j⟩ := by
  rw [subcubesAt_eq_image hk z, Finset.sum_image]
  intro a _ b _ h
  exact congrArg TriadicCube.index h

theorem card_subcubesAt_eq {m k : ℕ} (hk : k ≤ m) (z : Vertex 2) :
    (subcubesAt (⟨m, z⟩ : TriadicCube 2) k).card =
      (Rigidity.Proofs.Multiscale.centers m z k).card := by
  have h := sum_subcubesAt_eq (β := ℕ) hk z fun _ => 1
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  rw [h, Rigidity.Proofs.Multiscale.card_centers hk, Rigidity.Proofs.Multiscale.card_cube]

/-- The coarse pairing of a minimizer of `μ` vanishes off the partition event and for an
unresolved cube, and is the polarization of `-|V| μ(V, ·)` otherwise; as a function of the
configuration it is a combination of integrable functions. -/
theorem planarMuGradAvg_eq (V : TriadicCube 2) (q : Fin 2 → ℝ) (j : Fin 2) :
    (fun ω => planarMuGradAvg ω V q j) = fun ω =>
      (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then -planarMu ω V (Pi.single j 1 + q)
        else 0) -
      (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then -planarMu ω V (Pi.single j 1)
        else 0) -
      (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then -planarMu ω V q else 0) := by
  funext ω
  rw [planarMuGradAvg]
  by_cases h : PlanarPartitionEvent ω ∧ PlanarResolved ω V
  · rw [if_pos h, if_pos h, if_pos h, coarsePairing_planarMuMinimizer h.1 h.2]
    field_simp [V.volume_pos.ne']
    ring
  · rw [if_neg h, if_neg h, if_neg h]
    have h0 : planarMuMinimizer ω V q = 0 := by rw [planarMuMinimizer, dif_neg h]
    rw [h0, map_zero]
    simp

theorem aemeasurable_planarMuGradAvg {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (V : TriadicCube 2) (q : Fin 2 → ℝ) (j : Fin 2) :
    AEMeasurable (fun ω => planarMuGradAvg ω V q j) (latticeBondLaw 2 p) := by
  rw [planarMuGradAvg_eq]
  exact (((integrable_neg_planarMu_indicator hpc V _).sub
    (integrable_neg_planarMu_indicator hpc V _)).sub
    (integrable_neg_planarMu_indicator hpc V q)).aemeasurable

/-- The entries of the finite-volume matrices `ā_{□_n}⁻¹` are bounded uniformly in `n`. -/
theorem exists_abs_planarAhomInvFinite_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (i j : Fin 2), |planarAhomInvFinite p n i j| ≤ K := by
  obtain ⟨C, hC, h⟩ := exists_lintegral_neg_planarMu_le hpc
  have hb : ∀ (n : ℕ) (q : Fin 2 → ℝ), 0 ≤ planarMuMean p n q ∧
      planarMuMean p n q ≤ C.toReal * (|q 0| + |q 1|) ^ 2 := by
    intro n q
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) (h ⟨n, 0⟩ q)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
    exact this
  refine ⟨2 * C.toReal * 4 + 2 * C.toReal, by positivity, fun n i j => ?_⟩
  have h10 := hb n ![1, 0]
  have h01 := hb n ![0, 1]
  have h11 := hb n ![1, 1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, abs_one, abs_zero] at h10 h01 h11
  norm_num at h10 h01 h11
  have hC0 : 0 ≤ C.toReal := ENNReal.toReal_nonneg
  fin_cases i <;> fin_cases j <;>
    simp only [planarAhomInvFinite, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one]
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith

end Rigidity.Percolation
