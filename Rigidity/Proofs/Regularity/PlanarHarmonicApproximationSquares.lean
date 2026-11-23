import Rigidity.Proofs.Regularity.PlanarOrderZero
import Rigidity.Proofs.Percolation.PlanarCubeEnergy

/-!
# Armstrong–Dario, Lemma 7.1, in dimension two, from the estimates on squares

The proof of Lemma 7.1 of Armstrong and Dario (arXiv:1609.09431v2) consists of three estimates on
the triadic cube `□_j` for `3^j` above the minimal scale, followed by an iteration (Step 4):

* (7.7), the harmonic approximation of the coarsening on `□_j` (Steps 1 and 2):
  `inf_{w ∈ Ā(□_j)} ‖[u]_𝒫 - w‖_{L̲²(□_j)} ≤ C₁ 3^{-j α} Γ_{j + 3}`;
* (7.8), the comparison of `u` with its coarsening (Step 3), in `L²`:
  `3^{-j} ‖u - [u]_𝒫‖_{L²(C_*(□_j))} ≤ K₂ 3^{-j} Γ_{j + 3}`;
* the bound of Step 2 for constant `w = a`:
  `‖[u]_𝒫 - a‖_{L̲²(□_j)} ≤ K₃ 3^{-j-3} ‖u - a‖_{L²(C_*(□_{j + 3}))}`;

where `Γ_j = inf_a 3^{-j} ‖u - a‖_{L²(C_*(□_j))}` (`clusterSquareOsc`), `C_*(□_j)` being the
cluster `clusterVertices ω ⟨j, 0⟩` of the square. `PlanarSquareEstimates` collects them, and
`planarHarmonicApproximationAt_of_squareEstimates` derives the form `PlanarHarmonicApproximationAt`
of Lemma 7.1 used in the proof of Lemma 7.3, under the two inclusions of the clusters used in the
source: `C_*(□_j) ⊆ 𝒞_∞` and `𝒞_∞ ∩ B_r ⊆ C_*(□_{m + 1})` when `B_r ⊆ □_m`, above the minimal
scale.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.S2

/-- The triangle inequality for normalized `ℓ²` sums. -/
theorem sqrt_sum_sq_add_le {ι : Type*} (S : Finset ι) {c : ℝ} (hc : 0 < c) (g h : ι → ℝ) :
    Real.sqrt ((∑ x ∈ S, (g x + h x) ^ 2) / c) ≤
      Real.sqrt ((∑ x ∈ S, g x ^ 2) / c) + Real.sqrt ((∑ x ∈ S, h x ^ 2) / c) := by
  set a := ∑ x ∈ S, g x ^ 2 with hadef
  set b := ∑ x ∈ S, h x ^ 2 with hbdef
  have ha : 0 ≤ a := sum_nonneg fun _ _ => sq_nonneg _
  have hb : 0 ≤ b := sum_nonneg fun _ _ => sq_nonneg _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S g h
  have hp : ∑ x ∈ S, g x * h x ≤ Real.sqrt a * Real.sqrt b := by
    rw [← Real.sqrt_mul ha]
    refine (le_abs_self _).trans ?_
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hcs
  have hexp : ∑ x ∈ S, (g x + h x) ^ 2 = a + 2 * ∑ x ∈ S, g x * h x + b := by
    have e : ∀ x, (g x + h x) ^ 2 = g x ^ 2 + 2 * (g x * h x) + h x ^ 2 := fun x => by ring
    simp_rw [e]
    rw [sum_add_distrib, sum_add_distrib, ← mul_sum]
  rw [Real.sqrt_div' _ hc.le, Real.sqrt_div' _ hc.le, Real.sqrt_div' _ hc.le, ← add_div]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  rw [Real.sqrt_le_left (by positivity), hexp]
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, hp]

/-- The normalized `ℓ²` norm `3^{-j} ‖g‖_{ℓ²(C_*(□_j))}` on the cluster of the square `□_j`. -/
noncomputable def clusterSquareL2 (ω : Configuration 2) (j : ℕ) (g : Vertex 2 → ℝ) : ℝ :=
  Real.sqrt ((∑ x ∈ clusterVertices ω ⟨j, 0⟩, g x ^ 2) / 3 ^ (2 * j))

/-- The oscillation `Γ_j = inf_a 3^{-j} ‖u - a‖_{ℓ²(C_*(□_j))}` of a function on a cluster. -/
noncomputable def clusterSquareOsc {ω : Configuration 2} (C : OpenComponent ω) (u : C → ℝ)
    (j : ℕ) : ℝ :=
  ⨅ a : ℝ, clusterSquareL2 ω j (fun x => Rigidity.Section3.extend C u x - a)

/-- The estimates of the proof of Armstrong–Dario, Lemma 7.1, on the square `□_j`: (7.7), the
`L²` form of (7.8), and the bound of Step 2 for constant `w`. -/
def PlanarSquareEstimates {ω : Configuration 2} (C : OpenComponent ω) (C₁ K₂ K₃ α : ℝ) (j : ℕ)
    (u : C → ℝ) : Prop :=
  squareHarmonicDist j (planarCoarse C u) ≤ C₁ / ((3 : ℝ) ^ j) ^ α * clusterSquareOsc C u (j + 3) ∧
    clusterSquareL2 ω j (fun x => Rigidity.Section3.extend C u x - planarCoarse C u x) ≤
      K₂ / 3 ^ j * clusterSquareOsc C u (j + 3) ∧
    ∀ a : ℝ, squareL2 j (fun y => planarCoarse C u y - a) ≤
      K₃ * clusterSquareL2 ω (j + 3) (fun x => Rigidity.Section3.extend C u x - a)

theorem clusterSquareL2_nonneg (ω : Configuration 2) (j : ℕ) (g : Vertex 2 → ℝ) :
    0 ≤ clusterSquareL2 ω j g :=
  Real.sqrt_nonneg _

theorem clusterSquareL2_add_le (ω : Configuration 2) (j : ℕ) (g h : Vertex 2 → ℝ) :
    clusterSquareL2 ω j (fun x => g x + h x) ≤ clusterSquareL2 ω j g + clusterSquareL2 ω j h := by
  unfold clusterSquareL2
  exact sqrt_sum_sq_add_le _ (by positivity) g h

theorem clusterSquareOsc_nonneg {ω : Configuration 2} (C : OpenComponent ω) (u : C → ℝ)
    (j : ℕ) : 0 ≤ clusterSquareOsc C u j :=
  le_ciInf fun _ => clusterSquareL2_nonneg _ _ _

theorem clusterSquareOsc_le_clusterSquareL2 {ω : Configuration 2} (C : OpenComponent ω)
    (u : C → ℝ) (j : ℕ) (a : ℝ) :
    clusterSquareOsc C u j ≤ clusterSquareL2 ω j (fun x => Rigidity.Section3.extend C u x - a) :=
  ciInf_le ⟨0, fun _ ⟨_, h⟩ => h ▸ clusterSquareL2_nonneg _ _ _⟩ a

theorem extend_val {ω : Configuration 2} (C : OpenComponent ω) (u : C → ℝ) (x : C) :
    Rigidity.Section3.extend C u x.val = u x := by
  simp [Rigidity.Section3.extend]

theorem mem_square_of_mem_clusterVertices {ω : Configuration 2} {j : ℕ} {x : Vertex 2}
    (hx : x ∈ clusterVertices ω ⟨j, 0⟩) : x ∈ triadicCubeFinset 2 j 0 := by
  have h1 : x ∈ (⟨j, 0⟩ : TriadicCube 2).vertices := (mem_clusterVertices.1 hx).1
  rw [mem_square_iff]
  intro i
  have h : |2 * (x i - (⟨j, 0⟩ : TriadicCube 2).side * (⟨j, 0⟩ : TriadicCube 2).index i)| <
      (⟨j, 0⟩ : TriadicCube 2).side := h1 i
  simp only [TriadicCube.side, Pi.zero_apply, mul_zero, sub_zero] at h
  obtain ⟨h₁, h₂⟩ := abs_lt.1 h
  have h₁' : -((3 : ℝ) ^ j) < 2 * (x i : ℝ) := by exact_mod_cast h₁
  have h₂' : 2 * (x i : ℝ) < (3 : ℝ) ^ j := by exact_mod_cast h₂
  rw [abs_lt]; constructor <;> linarith

/-- The cluster of a square against its square. -/
theorem clusterSquareL2_le_squareL2 (ω : Configuration 2) (j : ℕ) (g : Vertex 2 → ℝ) :
    clusterSquareL2 ω j g ≤ squareL2 j g := by
  unfold clusterSquareL2 squareL2
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact sum_le_sum_of_subset_of_nonneg (fun x hx => mem_square_of_mem_clusterVertices hx)
    fun _ _ _ => sq_nonneg _

/-- The cluster of `□_j` inside the cluster ball `C ∩ B_ρ`, `3^j ≤ ρ`: for every `a`,
`3^{-j} ‖u - a‖_{ℓ²(C_*(□_j))} ≤ (ρ / 3^j) ρ^{-1} ‖u - a‖_{ℓ²(C ∩ B_ρ)}`. -/
theorem clusterSquareL2_le_clusterBallVolumeL2 {ω : Configuration 2} (C : OpenComponent ω)
    (u : C → ℝ) {j : ℕ} {ρ : ℝ} (hsub : ∀ x ∈ clusterVertices ω ⟨j, 0⟩, x ∈ C.supp)
    (hρ : (3 : ℝ) ^ j ≤ ρ) (a : ℝ) :
    clusterSquareL2 ω j (fun x => Rigidity.Section3.extend C u x - a) ≤
      ρ / 3 ^ j * clusterBallVolumeL2 C ρ (u - fun _ => a) := by
  classical
  have h3 : (0 : ℝ) < 3 ^ j := by positivity
  have hρ0 : 0 < ρ := h3.trans_le hρ
  set G : Vertex 2 → ℝ := fun x => Rigidity.Section3.extend C u x - a with hG
  have hsum : ∑ x ∈ clusterVertices ω ⟨j, 0⟩, G x ^ 2 ≤
      ∑ x ∈ componentEuclideanBall C 0 ρ, (u x - a) ^ 2 := by
    have e : ∑ x ∈ componentEuclideanBall C 0 ρ, (u x - a) ^ 2 =
        ∑ y ∈ (componentEuclideanBall C 0 ρ).image Subtype.val, G y ^ 2 := by
      rw [sum_image fun _ _ _ _ h => Subtype.val_injective h]
      refine sum_congr rfl fun x _ => ?_
      simp only [hG, extend_val]
    rw [e]
    refine sum_le_sum_of_subset_of_nonneg (fun y hy => ?_) fun _ _ _ => sq_nonneg _
    rw [mem_image]
    refine ⟨⟨y, hsub y hy⟩, ?_, rfl⟩
    rw [mem_componentEuclideanBall]
    exact (dist_lt_of_mem_square (mem_square_of_mem_clusterVertices hy)).trans_le hρ
  have hS : 0 ≤ ∑ x ∈ componentEuclideanBall C 0 ρ, (u x - a) ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have e2 : ρ / 3 ^ j * clusterBallVolumeL2 C ρ (u - fun _ => a) =
      Real.sqrt ((∑ x ∈ componentEuclideanBall C 0 ρ, (u x - a) ^ 2) / 3 ^ (2 * j)) := by
    unfold clusterBallVolumeL2
    simp only [Pi.sub_apply]
    rw [← Real.sqrt_sq (div_nonneg hρ0.le h3.le), ← Real.sqrt_mul (sq_nonneg _)]
    congr 1
    rw [div_pow, pow_mul', div_mul_div_comm, mul_comm (ρ ^ 2),
      mul_div_mul_right _ _ (pow_ne_zero 2 hρ0.ne')]
  rw [e2]
  unfold clusterSquareL2
  exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hsum (by positivity))

/-- The oscillation on the cluster of `□_j` against the cluster ball `C ∩ B_ρ`, `3^j ≤ ρ`. -/
theorem clusterSquareOsc_le {ω : Configuration 2} (C : OpenComponent ω) (u : C → ℝ) {j : ℕ}
    {ρ : ℝ} (hsub : ∀ x ∈ clusterVertices ω ⟨j, 0⟩, x ∈ C.supp) (hρ : (3 : ℝ) ^ j ≤ ρ) :
    clusterSquareOsc C u j ≤ ρ / 3 ^ j * ⨅ a : ℝ, clusterBallVolumeL2 C ρ (u - fun _ => a) := by
  have h3 : (0 : ℝ) < 3 ^ j := by positivity
  have hρ0 : 0 < ρ := h3.trans_le hρ
  rw [Real.mul_iInf_of_nonneg (by positivity)]
  exact le_ciInf fun a => (clusterSquareOsc_le_clusterSquareL2 C u j a).trans
    (clusterSquareL2_le_clusterBallVolumeL2 C u hsub hρ a)

/-- A ball between `□_{m - 2}` and `□_m`: for `1 ≤ r`, `2 r ≤ 3^m < 6 r`, the normalized norm on
the lattice ball `B_r` is at most `9` times the one on `□_m`. -/
theorem componentBallL2_le_nine_squareL2 {r : ℝ} {m : ℕ} (hr : 1 ≤ r) (hm1 : 2 * r ≤ 3 ^ m)
    (hm2 : (3 : ℝ) ^ m < 6 * r) (g : Vertex 2 → ℝ) :
    componentBallL2 (latticeComponent 2) 0 r (fun x => g x.val) ≤ 9 * squareL2 m g := by
  have hsub : ∀ y : Vertex 2,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex 2)) < r →
        y ∈ triadicCubeFinset 2 m 0 := fun y hy => mem_square_of_dist_lt (by linarith)
  have hm9 : (3 : ℝ) ^ m ≤ 9 * 3 ^ (m - 2) := by
    rcases Nat.lt_or_ge m 2 with h | h
    · have : m - 2 = 0 := by omega
      rw [this, pow_zero, mul_one]
      calc (3 : ℝ) ^ m ≤ 3 ^ 1 := pow_le_pow_right₀ (by norm_num) (by omega)
        _ ≤ 9 := by norm_num
    · have : (3 : ℝ) ^ m = 3 ^ 2 * 3 ^ (m - 2) := by rw [← pow_add]; congr 1; omega
      rw [this]; norm_num
  have hj : (3 : ℝ) ^ (m - 2) ≤ r := by
    rcases Nat.lt_or_ge m 2 with h | h
    · have : m - 2 = 0 := by omega
      rw [this, pow_zero]; exact hr
    · have : (3 : ℝ) ^ m = 3 ^ 2 * 3 ^ (m - 2) := by rw [← pow_add]; congr 1; omega
      rw [this] at hm2; norm_num at hm2; linarith
  have hratio : (3 : ℝ) ^ m / 3 ^ (m - 2) ≤ 9 := by
    rw [div_le_iff₀ (by positivity)]; exact hm9
  exact (componentBallL2_le_squareL2 hsub hj g).trans
    (mul_le_mul_of_nonneg_right hratio (squareL2_nonneg _ _))

/-- A larger `E` in the harmonic approximation hypothesis. -/
theorem HarmonicApproximation.mono_E {F : Type*} [AddCommGroup F] {N : ℝ → AddGroupSeminorm F}
    {Abar : ℝ → Set F} {P₀ : AddSubgroup F} {A α X R E E' : ℝ} {u : F} (hX : 0 ≤ X)
    (h : HarmonicApproximation N Abar P₀ A α X R E u) (hE : E ≤ E') :
    HarmonicApproximation N Abar P₀ A α X R E' u := by
  intro r hr hrR
  have hr0 : 0 ≤ r := hX.trans hr
  refine (h r hr hrR).trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hr0 _))
  have := div_le_div_of_nonneg_right hE hr0
  linarith

/-- The comparison (ii) of `planarHarmonicApproximationAt_of_squareEstimates` at one radius. -/
theorem coarseComparison_of_squareEstimates {ω : Configuration 2} (C : OpenComponent ω)
    (u : C → ℝ) {L K₂ K A X₀ R r : ℝ} (hL : 1 ≤ L) (hA : 4374 * L ≤ A) (hK₂ : 0 ≤ K₂)
    (hK2 : K₂ * A / 162 ≤ K) (hX₀r : X₀ ≤ r) (hr1 : 1 ≤ r) (hAr : A * r ≤ R)
    (hsub : ∀ j : ℕ, X₀ ≤ 3 ^ j → ∀ x ∈ clusterVertices ω ⟨j, 0⟩, x ∈ C.supp)
    (hgeo : ∀ (m : ℕ) (r : ℝ), X₀ ≤ r → 2 * r ≤ 3 ^ m → ∀ x : C,
      dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding (0 : Vertex 2)) < r →
        x.val ∈ clusterVertices ω ⟨m + 1, 0⟩)
    (hS3 : ∀ j : ℕ, X₀ ≤ 3 ^ j → L * 3 ^ (j + 3) ≤ R →
      clusterSquareL2 ω j (fun x => Rigidity.Section3.extend C u x - planarCoarse C u x) ≤
        K₂ / 3 ^ j * clusterSquareOsc C u (j + 3)) :
    clusterBallVolumeL2 C r (u - fun x => planarCoarse C u x.val) ≤
      K / r * ⨅ a : ℝ, clusterBallVolumeL2 C (A * r) (u - fun _ => a) := by
  have hr0 : 0 < r := by linarith
  have hA0 : 0 < A := by linarith
  obtain ⟨m, hm1, hm2⟩ := exists_three_pow_near hr1
  have h3m : (0 : ℝ) < 3 ^ m := by positivity
  have hX₀m : X₀ ≤ 3 ^ m := by linarith
  have e4 : (3 : ℝ) ^ (m + 4) = 81 * 3 ^ m := by ring
  have e1 : (3 : ℝ) ^ (m + 1 + 3) = 81 * 3 ^ m := by ring
  have hdom : L * 3 ^ (m + 1 + 3) ≤ R := by
    rw [e1]
    have h1 := mul_le_mul_of_nonneg_left hm2.le (by positivity : (0 : ℝ) ≤ 81 * L)
    have h2 := mul_le_mul_of_nonneg_right hA hr0.le
    have hLr : 0 ≤ L * r := by positivity
    linarith
  have hX₀m1 : X₀ ≤ 3 ^ (m + 1) :=
    hX₀m.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have hX₀m4 : X₀ ≤ 3 ^ (m + 4) :=
    hX₀m.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have hS3 := hS3 (m + 1) hX₀m1 hdom
  have hm4Ar : (3 : ℝ) ^ (m + 4) ≤ A * r := by
    rw [e4]
    have h2 := mul_le_mul_of_nonneg_right hA hr0.le
    have h3 : r ≤ L * r := le_mul_of_one_le_left hr0.le hL
    linarith
  have hΓ := clusterSquareOsc_le C u (hsub (m + 4) hX₀m4) hm4Ar
  -- the cluster ball `C ∩ B_r` inside `C_*(□_{m + 1})`
  have hsum : ∑ x ∈ componentEuclideanBall C 0 r,
      (u x - planarCoarse C u x.val) ^ 2 ≤
      ∑ x ∈ clusterVertices ω ⟨m + 1, 0⟩,
        (Rigidity.Section3.extend C u x - planarCoarse C u x) ^ 2 := by
    have e : ∑ x ∈ componentEuclideanBall C 0 r, (u x - planarCoarse C u x.val) ^ 2 =
        ∑ y ∈ (componentEuclideanBall C 0 r).image Subtype.val,
          (Rigidity.Section3.extend C u y - planarCoarse C u y) ^ 2 := by
      rw [sum_image fun _ _ _ _ h => Subtype.val_injective h]
      refine sum_congr rfl fun x _ => ?_
      simp only [extend_val]
    rw [e]
    refine sum_le_sum_of_subset_of_nonneg (fun y hy => ?_) fun _ _ _ => sq_nonneg _
    rw [mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hgeo m r hX₀r hm1 x ((mem_componentEuclideanBall C 0 r x).1 hx)
  have h31 : (0 : ℝ) < 3 ^ (m + 1) := by positivity
  have hcmp : clusterBallVolumeL2 C r (u - fun x => planarCoarse C u x.val) ≤
      3 ^ (m + 1) / r *
        clusterSquareL2 ω (m + 1) (fun x => Rigidity.Section3.extend C u x - planarCoarse C u x) := by
    have e : 3 ^ (m + 1) / r *
        clusterSquareL2 ω (m + 1) (fun x => Rigidity.Section3.extend C u x - planarCoarse C u x) =
        Real.sqrt ((∑ x ∈ clusterVertices ω ⟨m + 1, 0⟩,
          (Rigidity.Section3.extend C u x - planarCoarse C u x) ^ 2) / r ^ 2) := by
      unfold clusterSquareL2
      rw [← Real.sqrt_sq (div_nonneg h31.le hr0.le), ← Real.sqrt_mul (sq_nonneg _)]
      congr 1
      rw [div_pow, pow_mul', div_mul_div_comm, mul_comm ((3 ^ (m + 1)) ^ 2),
        mul_div_mul_right _ _ (pow_ne_zero 2 h31.ne')]
    rw [e]
    unfold clusterBallVolumeL2
    simp only [Pi.sub_apply]
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hsum (sq_nonneg _))
  have hm4 : A * r / 3 ^ (m + 4) ≤ A / 162 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num), e4]
    have := mul_le_mul_of_nonneg_left hm1 (by positivity : (0 : ℝ) ≤ 81 * A)
    linarith
  have hI0 := iInf_clusterBallVolumeL2_nonneg C (A * r) u
  have hΓ0 := clusterSquareOsc_nonneg C u (m + 4)
  have e5 : m + 1 + 3 = m + 4 := by ring
  rw [e5] at hS3
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ, I = ⨅ a : ℝ, clusterBallVolumeL2 C (A * r) (u - fun _ => a) :=
    ⟨_, rfl⟩
  rw [← hIdef] at hΓ hI0 ⊢
  have s1 := hcmp.trans (mul_le_mul_of_nonneg_left hS3 (by positivity))
  have s3 : (3 : ℝ) ^ (m + 1) / r * (K₂ / 3 ^ (m + 1) * clusterSquareOsc C u (m + 4)) =
      K₂ / r * clusterSquareOsc C u (m + 4) := by
    rw [show (3 : ℝ) ^ (m + 1) / r * (K₂ / 3 ^ (m + 1) * clusterSquareOsc C u (m + 4)) =
      K₂ / r * clusterSquareOsc C u (m + 4) * (3 ^ (m + 1) / 3 ^ (m + 1)) by ring,
      div_self h31.ne', mul_one]
  rw [s3] at s1
  have hK₂r : 0 ≤ K₂ / r := div_nonneg hK₂ hr0.le
  have s4 := mul_le_mul_of_nonneg_left hΓ hK₂r
  have s5 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm4 hI0) hK₂r
  have s6 : K₂ / r * (A / 162 * I) = K₂ * A / 162 / r * I := by ring
  have s7 := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hK2 hr0.le) hI0
  exact s1.trans (s4.trans (s5.trans ((le_of_eq s6).trans s7)))

/-- The bound (iii) of `planarHarmonicApproximationAt_of_squareEstimates` at one radius. -/
theorem coarseBound_of_squareEstimates {ω : Configuration 2} (C : OpenComponent ω)
    (u : C → ℝ) {L K₃ K A X₀ R r : ℝ} (hL : 1 ≤ L) (hA : 4374 * L ≤ A) (hK₃ : 0 ≤ K₃)
    (hK3 : K₃ * A / 6 ≤ K) (hX₀r : X₀ ≤ r) (hr1 : 1 ≤ r) (hAr : A * r ≤ R)
    (hsub : ∀ j : ℕ, X₀ ≤ 3 ^ j → ∀ x ∈ clusterVertices ω ⟨j, 0⟩, x ∈ C.supp)
    (hS2 : ∀ j : ℕ, X₀ ≤ 3 ^ j → L * 3 ^ (j + 3) ≤ R → ∀ a : ℝ,
      squareL2 j (fun y => planarCoarse C u y - a) ≤
        K₃ * clusterSquareL2 ω (j + 3) (fun x => Rigidity.Section3.extend C u x - a)) (a : ℝ) :
    componentBallL2 (latticeComponent 2) 0 r (fun x => planarCoarse C u x.val - a) ≤
      K * clusterBallVolumeL2 C (A * r) (u - fun _ => a) := by
  have hr0 : 0 < r := by linarith
  have hA0 : 0 < A := by linarith
  obtain ⟨m, hm1, hm2⟩ := exists_three_pow_near hr1
  have h3m : (0 : ℝ) < 3 ^ m := by positivity
  have hX₀m : X₀ ≤ 3 ^ m := by linarith
  have e3 : (3 : ℝ) ^ (m + 3) = 27 * 3 ^ m := by ring
  have hdom : L * 3 ^ (m + 3) ≤ R := by
    rw [e3]
    have h1 := mul_le_mul_of_nonneg_left hm2.le (by positivity : (0 : ℝ) ≤ 27 * L)
    have h2 := mul_le_mul_of_nonneg_right hA hr0.le
    have hLr : 0 ≤ L * r := by positivity
    linarith
  have hX₀m3 : X₀ ≤ 3 ^ (m + 3) :=
    hX₀m.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have hS2 := hS2 m hX₀m hdom a
  have hm3Ar : (3 : ℝ) ^ (m + 3) ≤ A * r := by
    rw [e3]
    have h2 := mul_le_mul_of_nonneg_right hA hr0.le
    have h3 : r ≤ L * r := le_mul_of_one_le_left hr0.le hL
    linarith
  have hc := clusterSquareL2_le_clusterBallVolumeL2 C u (hsub (m + 3) hX₀m3) hm3Ar a
  have hball := componentBallL2_le_nine_squareL2 hr1 hm1 hm2 (fun y => planarCoarse C u y - a)
  have hm3 : A * r / 3 ^ (m + 3) ≤ A / 54 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num), e3]
    have := mul_le_mul_of_nonneg_left hm1 (by positivity : (0 : ℝ) ≤ 27 * A)
    linarith
  have hV0 := clusterBallVolumeL2_nonneg C (A * r) (u - fun _ => a)
  calc componentBallL2 (latticeComponent 2) 0 r (fun x => planarCoarse C u x.val - a)
      ≤ 9 * squareL2 m (fun y => planarCoarse C u y - a) := hball
    _ ≤ 9 * (K₃ * clusterSquareL2 ω (m + 3) (fun x => Rigidity.Section3.extend C u x - a)) :=
        mul_le_mul_of_nonneg_left hS2 (by norm_num)
    _ ≤ 9 * (K₃ * (A * r / 3 ^ (m + 3) * clusterBallVolumeL2 C (A * r) (u - fun _ => a))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc hK₃) (by norm_num)
    _ ≤ 9 * (K₃ * (A / 54 * clusterBallVolumeL2 C (A * r) (u - fun _ => a))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hm3 hV0) hK₃) (by norm_num)
    _ = K₃ * A / 6 * clusterBallVolumeL2 C (A * r) (u - fun _ => a) := by ring
    _ ≤ K * clusterBallVolumeL2 C (A * r) (u - fun _ => a) :=
        mul_le_mul_of_nonneg_right hK3 hV0

/-- **Armstrong–Dario, Lemma 7.1, in dimension two, from the estimates on squares.** If, above a
scale `X₀ ≥ 1`, the clusters of the squares lie in `C`, the cluster balls `C ∩ B_r` with
`B_r ⊆ □_m` lie in `C_*(□_{m + 1})`, and every `u` harmonic on `C ∩ B_R` satisfies
`PlanarSquareEstimates` on the squares `□_j` with `L 3^{j + 3} ≤ R`, then `C` satisfies
`PlanarHarmonicApproximationAt` with `A = 4374 L`, the exponent `α / 2`, a constant `K` depending
on `L, K₂, K₃`, above the scale `max X₀ (squareScale A L C₁ K₂ α)`. -/
theorem planarHarmonicApproximationAt_of_squareEstimates {L C₁ K₂ K₃ α : ℝ} (hL : 1 ≤ L)
    (hC₁ : 0 ≤ C₁) (hK₂ : 0 ≤ K₂) (hK₃ : 0 ≤ K₃) (hα : 0 < α) {ω : Configuration 2}
    (C : OpenComponent ω) {X₀ : ℝ} (hX₀ : 1 ≤ X₀)
    (hsub : ∀ j : ℕ, X₀ ≤ 3 ^ j → ∀ x ∈ clusterVertices ω ⟨j, 0⟩, x ∈ C.supp)
    (hgeo : ∀ (m : ℕ) (r : ℝ), X₀ ≤ r → 2 * r ≤ 3 ^ m → ∀ x : C,
      dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding (0 : Vertex 2)) < r →
        x.val ∈ clusterVertices ω ⟨m + 1, 0⟩)
    (hest : ∀ R : ℝ, ∀ u : C → ℝ, IsHarmonicInBall C R u → ∀ j : ℕ, X₀ ≤ 3 ^ j →
      L * 3 ^ (j + 3) ≤ R → PlanarSquareEstimates C C₁ K₂ K₃ α j u) :
    PlanarHarmonicApproximationAt C (4374 * L) (α / 2)
      (max 1 (max (K₂ * (4374 * L) / 162) (K₃ * (4374 * L) / 6)))
      (max X₀ (squareScale (4374 * L) L C₁ K₂ α)) := by
  classical
  set A := 4374 * L with hAdef
  set K := max 1 (max (K₂ * A / 162) (K₃ * A / 6)) with hKdef
  set X := max X₀ (squareScale A L C₁ K₂ α) with hXdef
  have hA : 4374 * L ≤ A := le_of_eq hAdef.symm
  have hA0 : 0 < A := by linarith
  have hX₀X : X₀ ≤ X := by rw [hXdef]; exact le_max_left _ _
  have hsX : squareScale A L C₁ K₂ α ≤ X := by rw [hXdef]; exact le_max_right _ _
  have hX1 : 1 ≤ X := hX₀.trans hX₀X
  have hK1 : 1 ≤ K := by rw [hKdef]; exact le_max_left _ _
  have hK2 : K₂ * A / 162 ≤ K := by rw [hKdef]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hK3 : K₃ * A / 6 ≤ K := by rw [hKdef]; exact (le_max_right _ _).trans (le_max_right _ _)
  intro R hR u hu
  have hR0 : 0 < R := lt_of_lt_of_le (mul_pos hA0 (by linarith)) hR
  set B := ⨅ a : ℝ, clusterBallVolumeL2 C R (u - fun _ => a) with hBdef
  have hB0 : 0 ≤ B := iInf_clusterBallVolumeL2_nonneg C R u
  refine ⟨?_, ?_, ?_⟩
  · -- the harmonic approximation hypothesis on the balls of the lattice
    have H2 : ∀ j : ℕ, X₀ ≤ 3 ^ j → L * 3 ^ (j + 3) ≤ R →
        clusterSquareOsc C u j ≤ squareOsc j (planarCoarse C u) +
          K₂ / 3 ^ j * clusterSquareOsc C u (j + 3) := by
      intro j hj hjR
      have hS3 := (hest R u hu j hj hjR).2.1
      have hle : ∀ a : ℝ, clusterSquareOsc C u j - K₂ / 3 ^ j * clusterSquareOsc C u (j + 3) ≤
          squareL2 j (fun y => planarCoarse C u y - a) := by
        intro a
        have h1 := clusterSquareOsc_le_clusterSquareL2 C u j a
        have e : (fun x => Rigidity.Section3.extend C u x - a) = fun x =>
            (planarCoarse C u x - a) + (Rigidity.Section3.extend C u x - planarCoarse C u x) := by
          funext x; ring
        rw [e] at h1
        have h2 := clusterSquareL2_add_le ω j (fun x => planarCoarse C u x - a)
          (fun x => Rigidity.Section3.extend C u x - planarCoarse C u x)
        have h3 := clusterSquareL2_le_squareL2 ω j (fun y => planarCoarse C u y - a)
        linarith
      have := le_ciInf hle
      unfold squareOsc
      linarith
    have H3 : ∀ j : ℕ, X₀ ≤ 3 ^ j → L * 3 ^ j ≤ R → clusterSquareOsc C u j ≤ R / 3 ^ j * B := by
      intro j hj hjR
      have h3 : (0 : ℝ) < 3 ^ j := by positivity
      have h4 := mul_le_mul_of_nonneg_right hL h3.le
      exact clusterSquareOsc_le C u (hsub j hj) (by linarith)
    have hHA := harmonicApproximation_of_squares (f := planarCoarse C u) (Γ := clusterSquareOsc C u)
      (clusterSquareOsc_nonneg C u) hL hA hC₁ hK₂ hα hX₀X hsX hB0
      (fun m hm hmR => (hest R u hu m hm hmR).1) H2 H3
    refine hHA.mono_E (by linarith) ?_
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (le_mul_of_one_le_left hB0 hK1) hR0.le
  · intro r hr hrA
    exact coarseComparison_of_squareEstimates C u hL hA hK₂ hK2 (hX₀X.trans hr) (hX1.trans hr)
      (by rw [le_div_iff₀ hA0] at hrA; linarith) hsub hgeo
      (fun j hj hjR => (hest R u hu j hj hjR).2.1)
  · intro r hr hrA a
    exact coarseBound_of_squareEstimates C u hL hA hK₃ hK3 (hX₀X.trans hr) (hX1.trans hr)
      (by rw [le_div_iff₀ hA0] at hrA; linarith) hsub
      (fun j hj hjR => (hest R u hu j hj hjR).2.2) a

end Rigidity.Proofs.Regularity
