import Rigidity.Proofs.Regularity.PlanarHarmonicApproximationBalls
import Rigidity.Proofs.Regularity.MesoscopicRegularity

/-!
# The order-zero decay on a planar cluster from Lemma 7.1

Armstrong and Dario (arXiv:1609.09431v2) deduce the order-zero regularity of Theorem 2 (iii),
`k = 0`, from Lemma 7.1 through Lemmas 7.2 and 7.3. In dimension two, with the form
`PlanarHarmonicApproximationAt` of Lemma 7.1 on a cluster `C` above a scale `X` and a lower bound
`|C ∩ B_s| ≥ κ s²` for `s ≥ M₀`, this file proves the order-zero decay with constants
(`exists_planarOrderZeroDecay`): above `A² max(X, M₀, c₁)`, every `u` harmonic on `C ∩ B_R` is
within `K' (r / R) ‖u‖_{L̲²(C ∩ B_R)}` of one constant on every `C ∩ B_r`, `r ≤ R / 2`.

The steps follow the proof of Lemma 7.3 for `k = 0`:

* the iteration of Lemma 7.2 and the Campanato argument on the balls of the lattice
  (`armstrongDario_orderZero_origin_latticeHarmonic`) give one constant `c` with
  `‖[u]_𝒫 - c‖_{L̲²(B_t)} ≤ C₀ (A t / R) B` for `t ≤ R / (2A)`, `B` bounding
  `D_0(R / A) + (R / A) E` by the bound of Step 2 of Lemma 7.1;
* the comparison (7.4) of `u` with `[u]_𝒫` gives, for the oscillation `Γ(t)` of `u` on `C ∩ B_t`,
  `Γ(t) ≤ K t^{-1} Γ(A t) + 5 C₀ A (t / R) B`, which is iterated over the radii `A^k t` up to `R`
  (`le_sum_prod_of_step`, Step 1 of the proof of Lemma 7.3);
* the large radii `r > R / (2A²)` use the size of the constant `c`.

The normalizations: `clusterBallVolumeL2 C r` is `r^{-1} ‖·‖_{L²(C ∩ B_r)}`, compared with the
normalized norms on the cluster balls (`clusterBallVolumeL2_le_componentBallL2`,
`componentBallL2_le_of_card`) and with those on the balls of the lattice
(`clusterBallVolumeL2_le_lattice`).
-/

namespace Rigidity.Proofs.Regularity

open Finset MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S2

variable {ω : Configuration 2}

section Cluster

variable (C : OpenComponent ω)

theorem clusterBallVolumeL2_nonneg (r : ℝ) (f : C → ℝ) : 0 ≤ clusterBallVolumeL2 C r f :=
  Real.sqrt_nonneg _

theorem clusterBallVolumeL2_add_le {r : ℝ} (hr : 0 ≤ r) (f g : C → ℝ) :
    clusterBallVolumeL2 C r (f + g) ≤ clusterBallVolumeL2 C r f + clusterBallVolumeL2 C r g := by
  rw [clusterBallVolumeL2_eq C hr, clusterBallVolumeL2_eq C hr, clusterBallVolumeL2_eq C hr,
    ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  have := map_add_le_add (componentBallSeminorm C 0 r) f g
  simpa only [componentBallSeminorm_apply] using this

/-- `r^{-1} ‖f‖_{L²(C ∩ B_s)} ≤ (t / s) t^{-1} ‖f‖_{L²(C ∩ B_t)}` for `0 < s ≤ t`. -/
theorem clusterBallVolumeL2_le_of_le {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (f : C → ℝ) :
    clusterBallVolumeL2 C s f ≤ t / s * clusterBallVolumeL2 C t f := by
  have ht : 0 < t := hs.trans_le hst
  have hsum : ∑ x ∈ componentEuclideanBall C 0 s, f x ^ 2 ≤
      ∑ x ∈ componentEuclideanBall C 0 t, f x ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (componentEuclideanBall_mono C 0 hst) fun _ _ _ => sq_nonneg _
  have e : t / s * clusterBallVolumeL2 C t f =
      Real.sqrt ((∑ x ∈ componentEuclideanBall C 0 t, f x ^ 2) / s ^ 2) := by
    unfold clusterBallVolumeL2
    rw [← Real.sqrt_sq (div_nonneg ht.le hs.le), ← Real.sqrt_mul (sq_nonneg _)]
    congr 1
    rw [div_pow, div_mul_div_comm, mul_comm (t ^ 2), mul_div_mul_right _ _ (pow_ne_zero 2 ht.ne')]
  rw [e]
  unfold clusterBallVolumeL2
  exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hsum (sq_nonneg _))

/-- A cluster ball against the ball of the lattice: for `s ≥ 1`,
`s^{-1} ‖g‖_{L²(C ∩ B_s)} ≤ 5 ‖g‖_{L̲²(B_s ∩ ℤ²)}`. -/
theorem clusterBallVolumeL2_le_lattice {s : ℝ} (hs : 1 ≤ s) (g : Vertex 2 → ℝ) :
    clusterBallVolumeL2 C s (fun x => g x.val) ≤
      5 * componentBallL2 (latticeComponent 2) 0 s (fun x => g x.val) := by
  have hs0 : 0 < s := by linarith
  have himg : ∑ x ∈ componentEuclideanBall C 0 s, g x.val ^ 2 ≤
      ∑ x ∈ componentEuclideanBall (latticeComponent 2) 0 s, g x.val ^ 2 := by
    rw [sum_latticeBall_eq,
      ← sum_image (f := fun y => g y ^ 2) (fun _ _ _ _ h => Subtype.val_injective h)]
    refine sum_le_sum_of_subset_of_nonneg (fun y hy => ?_) fun _ _ _ => sq_nonneg _
    rw [mem_image_latticeBall]
    rw [mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact (mem_componentEuclideanBall C 0 s x).1 hx
  rw [sum_sq_eq_card_mul_componentBallL2_sq (latticeComponent 2) 0 s
    (fun x : latticeComponent 2 => g x.val)] at himg
  have hcard := card_componentEuclideanBall_le (latticeComponent 2) 0 hs0.le
  set N := componentBallL2 (latticeComponent 2) 0 s (fun x => g x.val) with hNdef
  have hN : 0 ≤ N := componentBallL2_nonneg _ _ _ _
  unfold clusterBallVolumeL2
  rw [Real.sqrt_le_left (by positivity), div_le_iff₀ (by positivity)]
  have h7 : 0 ≤ (s - 1) * (7 * s + 3) * N ^ 2 :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)
  calc ∑ x ∈ componentEuclideanBall C 0 s, g x.val ^ 2
      ≤ ((componentEuclideanBall (latticeComponent 2) 0 s).card : ℝ) * N ^ 2 := himg
    _ ≤ (2 * s + 3) ^ 2 * N ^ 2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ ≤ (5 * N) ^ 2 * s ^ 2 := by nlinarith

/-- For `s ≥ 1`, `s^{-1} ‖f‖_{L²(C ∩ B_s)} ≤ 5 ‖f‖_{L̲²(C ∩ B_s)}`. -/
theorem clusterBallVolumeL2_le_componentBallL2 {s : ℝ} (hs : 1 ≤ s) (f : C → ℝ) :
    clusterBallVolumeL2 C s f ≤ 5 * componentBallL2 C 0 s f := by
  rw [clusterBallVolumeL2_eq C (by linarith)]
  apply mul_le_mul_of_nonneg_right _ (componentBallL2_nonneg _ _ _ _)
  rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ (by positivity)]
  have hcard := card_componentEuclideanBall_le C 0 (by linarith : (0 : ℝ) ≤ s)
  nlinarith

/-- **Density.** If `|C ∩ B_s| ≥ κ s²`, then
`‖f‖_{L̲²(C ∩ B_s)} ≤ κ^{-1/2} s^{-1} ‖f‖_{L²(C ∩ B_s)}`. -/
theorem componentBallL2_le_of_card {s κ : ℝ} (hs : 0 < s) (hκ : 0 < κ)
    (hcard : κ * s ^ 2 ≤ (componentEuclideanBall C 0 s).card) (f : C → ℝ) :
    componentBallL2 C 0 s f ≤ Real.sqrt (1 / κ) * clusterBallVolumeL2 C s f := by
  have hcpos : (0 : ℝ) < (componentEuclideanBall C 0 s).card :=
    lt_of_lt_of_le (by positivity) hcard
  unfold componentBallL2 clusterBallVolumeL2
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  rw [div_le_iff₀ hcpos]
  have hT : 0 ≤ ∑ x ∈ componentEuclideanBall C 0 s, f x ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hs2 : (s : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hs.ne'
  calc ∑ x ∈ componentEuclideanBall C 0 s, f x ^ 2
      = 1 / κ * ((∑ x ∈ componentEuclideanBall C 0 s, f x ^ 2) / s ^ 2) * (κ * s ^ 2) := by
        rw [show 1 / κ * ((∑ x ∈ componentEuclideanBall C 0 s, f x ^ 2) / s ^ 2) * (κ * s ^ 2) =
          (∑ x ∈ componentEuclideanBall C 0 s, f x ^ 2) * (κ / κ) * (s ^ 2 / s ^ 2) by ring,
          div_self hκ.ne', div_self hs2, mul_one, mul_one]
    _ ≤ 1 / κ * ((∑ x ∈ componentEuclideanBall C 0 s, f x ^ 2) / s ^ 2) *
          (componentEuclideanBall C 0 s).card :=
        mul_le_mul_of_nonneg_left hcard (by positivity)

theorem iInf_clusterBallVolumeL2_le (r : ℝ) (u : C → ℝ) (c : ℝ) :
    (⨅ a : ℝ, clusterBallVolumeL2 C r (u - fun _ => a)) ≤
      clusterBallVolumeL2 C r (u - fun _ => c) :=
  ciInf_le ⟨0, fun _ ⟨_, h⟩ => h ▸ clusterBallVolumeL2_nonneg C _ _⟩ c

theorem iInf_clusterBallVolumeL2_nonneg (r : ℝ) (u : C → ℝ) :
    0 ≤ ⨅ a : ℝ, clusterBallVolumeL2 C r (u - fun _ => a) :=
  le_ciInf fun _ => clusterBallVolumeL2_nonneg C _ _

theorem IsHarmonicInBall.mono {C : OpenComponent ω} {R R' : ℝ} {u : C → ℝ}
    (h : IsHarmonicInBall C R u) (hR : R' ≤ R) : IsHarmonicInBall C R' u :=
  fun x hx hnb => h x (componentEuclideanBall_mono C 0 hR hx) fun y hy =>
    componentEuclideanBall_mono C 0 hR (hnb y hy)

end Cluster

theorem componentBallL2_lattice_const {r : ℝ} (hr : 0 < r) (c : ℝ) :
    componentBallL2 (latticeComponent 2) 0 r (fun _ => c) = |c| := by
  have hmem : (⟨0, mem_latticeComponent_supp 0⟩ : latticeComponent 2) ∈
      componentEuclideanBall (latticeComponent 2) 0 r := by
    rw [mem_componentEuclideanBall]; simpa using hr
  have hcard : (0 : ℝ) < (componentEuclideanBall (latticeComponent 2) 0 r).card := by
    exact_mod_cast card_pos.2 ⟨_, hmem⟩
  unfold componentBallL2
  rw [sum_const, nsmul_eq_mul, mul_div_assoc, mul_comm, div_mul_cancel₀ _ hcard.ne',
    Real.sqrt_sq_eq_abs]

/-- **The iteration of Step 1 of the proof of Lemma 7.3.** If `Γ_i ≤ D_i + ρ_i Γ_{i + 1}` for
`i < n`, `ρ ≥ 0`, then `Γ_0 ≤ ∑_{k < n} (∏_{i < k} ρ_i) D_k + (∏_{i < n} ρ_i) Γ_n`. -/
theorem le_sum_prod_of_step {Γ D ρ : ℕ → ℝ} (hρ : ∀ i, 0 ≤ ρ i) :
    ∀ n : ℕ, (∀ i < n, Γ i ≤ D i + ρ i * Γ (i + 1)) →
      Γ 0 ≤ ∑ k ∈ range n, (∏ i ∈ range k, ρ i) * D k + (∏ i ∈ range n, ρ i) * Γ n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro h
    have h1 := ih fun i hi => h i (by omega)
    have h2 := h n (by omega)
    have hp : 0 ≤ ∏ i ∈ range n, ρ i := prod_nonneg fun i _ => hρ i
    have h3 := mul_le_mul_of_nonneg_left h2 hp
    rw [sum_range_succ, prod_range_succ]
    nlinarith [h1, h3]

theorem prod_range_le_pow {ρ : ℕ → ℝ} {q : ℝ} (h0 : ∀ i, 0 ≤ ρ i) (hq : ∀ i, ρ i ≤ q) (k : ℕ) :
    ∏ i ∈ range k, ρ i ≤ q ^ k := by
  calc ∏ i ∈ range k, ρ i ≤ ∏ _i ∈ range k, q :=
        prod_le_prod (fun i _ => h0 i) fun i _ => hq i
    _ = q ^ k := by rw [prod_const, card_range]

/-- **The iteration of Step 1 of the proof of Lemma 7.3 over the radii `A^k s`.** If
`Γ(t) ≤ D t / R + K t^{-1} Γ(A t)` for `t ∈ [X₁, R / (2 A)]`, `Γ ≥ 0` and `Γ(t) ≤ (R / t) V` for
`t ≤ R`, with `2 K A ≤ X₁`, then `Γ(s) ≤ (s / R) (2 D + 4 A² V)` for `s ∈ [X₁, R / (2 A)]`. -/
theorem le_of_geometric_step {Γ : ℝ → ℝ} {A K X₁ R D V : ℝ} (hA : 1 < A) (hK : 0 ≤ K)
    (hX₁ : 0 < X₁) (hKA : 2 * K * A ≤ X₁) (hD : 0 ≤ D) (hV : 0 ≤ V) (hR : 0 < R)
    (hΓ0 : ∀ t, 0 ≤ Γ t) (htop : ∀ t, 0 < t → t ≤ R → Γ t ≤ R / t * V)
    (hstep : ∀ t, X₁ ≤ t → t ≤ R / (2 * A) → Γ t ≤ D * (t / R) + K / t * Γ (A * t))
    {s : ℝ} (hs : X₁ ≤ s) (hsR : s ≤ R / (2 * A)) :
    Γ s ≤ s / R * (2 * D + 4 * A ^ 2 * V) := by
  classical
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := hA.le
  have hs0 : 0 < s := hX₁.trans_le hs
  have hsR2 : s ≤ R / 2 :=
    hsR.trans (div_le_div_of_nonneg_left hR.le (by norm_num) (by linarith))
  have hexn : ∃ n : ℕ, R / 2 < A ^ (n + 1) * s := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (R / 2 / s) hA
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ hs0] at hn
    have h1 : A ^ n ≤ A ^ (n + 1) := pow_le_pow_right₀ hA1 (by omega)
    have := mul_le_mul_of_nonneg_right h1 hs0.le
    linarith
  obtain ⟨n, hnspec, hnmin⟩ : ∃ n : ℕ, R / 2 < A ^ (n + 1) * s ∧
      ∀ k < n, ¬ R / 2 < A ^ (k + 1) * s :=
    ⟨Nat.find hexn, Nat.find_spec hexn, fun k hk => Nat.find_min hexn hk⟩
  have hnle : A ^ n * s ≤ R / 2 := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, pow_zero, one_mul]; exact hsR2
    · have h := hnmin (n - 1) (by omega)
      push Not at h
      rwa [show n - 1 + 1 = n by omega] at h
  have hpowpos : ∀ i : ℕ, 0 < A ^ i * s := fun i => by positivity
  have hstepi : ∀ i < n, Γ (A ^ i * s) ≤
      D * (A ^ i * s / R) + K / (A ^ i * s) * Γ (A ^ (i + 1) * s) := by
    intro i hi
    have hi1 : X₁ ≤ A ^ i * s := hs.trans (le_mul_of_one_le_left hs0.le (one_le_pow₀ hA1))
    have hi2 : A ^ i * s ≤ R / (2 * A) := by
      have h1 : A ^ (i + 1) * s ≤ A ^ n * s :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA1 (by omega)) hs0.le
      have e : A ^ (i + 1) * s = A * (A ^ i * s) := by ring
      rw [e] at h1
      rw [le_div_iff₀ (by positivity)]
      linarith
    have h := hstep (A ^ i * s) hi1 hi2
    have e : A * (A ^ i * s) = A ^ (i + 1) * s := by ring
    rw [e] at h
    exact h
  have hρ0 : ∀ i, 0 ≤ K / (A ^ i * s) := fun i => div_nonneg hK (hpowpos i).le
  have hit := le_sum_prod_of_step (Γ := fun i => Γ (A ^ i * s))
    (D := fun i => D * (A ^ i * s / R)) (ρ := fun i => K / (A ^ i * s)) hρ0 n hstepi
  simp only [pow_zero, one_mul] at hit
  have hq0 : 0 ≤ K * A / s := by positivity
  have hq : K * A / s ≤ 1 / 2 := by
    rw [div_le_iff₀ hs0]; linarith
  have hρle : ∀ i, K / (A ^ i * s) ≤ K / s := fun i =>
    div_le_div_of_nonneg_left hK hs0 (le_mul_of_one_le_left hs0.le (one_le_pow₀ hA1))
  have hsum : ∑ k ∈ range n, (∏ i ∈ range k, K / (A ^ i * s)) * (D * (A ^ k * s / R)) ≤
      2 * D * (s / R) := by
    calc ∑ k ∈ range n, (∏ i ∈ range k, K / (A ^ i * s)) * (D * (A ^ k * s / R))
        ≤ ∑ k ∈ range n, (K / s) ^ k * (D * (A ^ k * s / R)) :=
          sum_le_sum fun k _ => mul_le_mul_of_nonneg_right
            (prod_range_le_pow hρ0 hρle k) (by positivity)
      _ = D * (s / R) * ∑ k ∈ range n, (K * A / s) ^ k := by
          rw [mul_sum]
          refine sum_congr rfl fun k _ => ?_
          ring
      _ ≤ D * (s / R) * 2 :=
          mul_le_mul_of_nonneg_left (sum_pow_le_two hq0 hq n) (by positivity)
      _ = 2 * D * (s / R) := by ring
  have hlast : (∏ i ∈ range n, K / (A ^ i * s)) * Γ (A ^ n * s) ≤ 4 * A ^ 2 * (s / R) * V := by
    have hT0 := hpowpos n
    have hTR : A ^ n * s ≤ R := hnle.trans (by linarith)
    have hRT : R < 2 * A * (A ^ n * s) := by
      have e : A ^ (n + 1) * s = A * (A ^ n * s) := by ring
      rw [e] at hnspec; linarith
    have hΓT := htop _ hT0 hTR
    have hP := prod_range_le_pow hρ0 hρle n
    have hKs : (K / s) ^ n * A ^ n ≤ 1 := by
      rw [← mul_pow]
      have e : K / s * A = K * A / s := by ring
      rw [e]
      exact pow_le_one₀ hq0 (by linarith)
    have hKs0 : 0 ≤ (K / s) ^ n := by positivity
    have hRR : R * R ≤ (2 * A * (A ^ n * s)) * (2 * A * (A ^ n * s)) :=
      mul_self_le_mul_self hR.le hRT.le
    have key : (K / s) ^ n * R * V * R ≤ 4 * A ^ 2 * s * V * (A ^ n * s) := by
      calc (K / s) ^ n * R * V * R = (K / s) ^ n * V * (R * R) := by ring
        _ ≤ (K / s) ^ n * V * ((2 * A * (A ^ n * s)) * (2 * A * (A ^ n * s))) := by gcongr
        _ = 4 * A ^ 2 * V * (A ^ n * s) * ((K / s) ^ n * A ^ n * s) := by ring
        _ ≤ 4 * A ^ 2 * V * (A ^ n * s) * (1 * s) := by gcongr
        _ = 4 * A ^ 2 * s * V * (A ^ n * s) := by ring
    have hlhs : (K / s) ^ n * (R / (A ^ n * s) * V) =
        (K / s) ^ n * R * V * R / ((A ^ n * s) * R) := by
      rw [show (K / s) ^ n * R * V * R / ((A ^ n * s) * R) =
        (K / s) ^ n * (R / (A ^ n * s) * V) * (R / R) by ring, div_self hR.ne', mul_one]
    have hrhs : 4 * A ^ 2 * (s / R) * V =
        4 * A ^ 2 * s * V * (A ^ n * s) / ((A ^ n * s) * R) := by
      rw [show 4 * A ^ 2 * s * V * (A ^ n * s) / ((A ^ n * s) * R) =
        4 * A ^ 2 * (s / R) * V * ((A ^ n * s) / (A ^ n * s)) by ring, div_self hT0.ne', mul_one]
    calc (∏ i ∈ range n, K / (A ^ i * s)) * Γ (A ^ n * s)
        ≤ (K / s) ^ n * (R / (A ^ n * s) * V) := mul_le_mul hP hΓT (hΓ0 _) hKs0
      _ ≤ 4 * A ^ 2 * (s / R) * V := by
          rw [hlhs, hrhs]
          exact div_le_div_of_nonneg_right key (by positivity)
  calc Γ s ≤ _ := hit
    _ ≤ 2 * D * (s / R) + 4 * A ^ 2 * (s / R) * V := add_le_add hsum hlast
    _ = s / R * (2 * D + 4 * A ^ 2 * V) := by ring

/-- The small radii of `exists_planarOrderZeroDecay`. -/
theorem small_radius_bound {K A r R D V G Γa : ℝ} (hK : 0 ≤ K) (hA : 0 < A) (hr1 : 1 ≤ r)
    (hR : 0 < R) (hD : 0 ≤ D) (hV : 0 ≤ V) (hG : G ≤ K / r * Γa + D * (r / R))
    (hΓa : Γa ≤ A * r / R * (2 * D + 4 * A ^ 2 * V)) :
    G ≤ r / R * (K * A * (2 * D + 4 * A ^ 2 * V) + D) := by
  have hr0 : 0 < r := by linarith
  have hZ : 0 ≤ 2 * D + 4 * A ^ 2 * V := by positivity
  have h1 : K / r * Γa ≤ K / r * (A * r / R * (2 * D + 4 * A ^ 2 * V)) :=
    mul_le_mul_of_nonneg_left hΓa (by positivity)
  have e : K / r * (A * r / R * (2 * D + 4 * A ^ 2 * V)) =
      K * A / R * (2 * D + 4 * A ^ 2 * V) * (r / r) := by ring
  rw [e, div_self hr0.ne', mul_one] at h1
  have h3 : K * A / R ≤ r * (K * A) / R :=
    div_le_div_of_nonneg_right (le_mul_of_one_le_left (by positivity) hr1) hR.le
  have h4 := mul_le_mul_of_nonneg_right h3 hZ
  have e5 : r * (K * A) / R * (2 * D + 4 * A ^ 2 * V) =
      r / R * (K * A * (2 * D + 4 * A ^ 2 * V)) := by ring
  have e6 : r / R * (K * A * (2 * D + 4 * A ^ 2 * V) + D) =
      r / R * (K * A * (2 * D + 4 * A ^ 2 * V)) + D * (r / R) := by ring
  linarith

/-- The conclusion of `exists_planarOrderZeroDecay` at one radius `r ∈ [A² X₁, R / 2]`, from the
step of the iteration, its outcome on the radii `[X₁, R / (2A)]` and the size of the constant. -/
theorem orderZero_conclusion {ω : Configuration 2} (C : OpenComponent ω) (u : C → ℝ)
    {A K κ C₀ b k₁ k₂ X₁ M₀ R c : ℝ} (hA1 : 1 ≤ A) (hK : 0 ≤ K) (hκ : 0 < κ) (hb0 : 0 < b)
    (hC₀ : 0 < C₀) (hk₁ : k₁ = K * A * (10 * C₀ * A * b + 20 * A ^ 2) + 5 * C₀ * A * b)
    (hk₂ : k₂ = 2 * A ^ 2 * (10 * A ^ 2 + 5 * C₀ * b / 2 + 50 * K)) (hX₁1 : 1 ≤ X₁)
    (hMX₁ : M₀ ≤ X₁) (hR0 : 0 < R) (hN0 : 0 ≤ componentBallL2 C 0 R u)
    (hV0 : 0 ≤ clusterBallVolumeL2 C R u)
    (hVN : clusterBallVolumeL2 C R u ≤ 5 * componentBallL2 C 0 R u)
    (hcstep : ∀ t : ℝ, X₁ ≤ t → t ≤ R / (2 * A) →
      clusterBallVolumeL2 C t (u - fun _ => c) ≤
        5 * C₀ * A * b * componentBallL2 C 0 R u * (t / R) +
          K / t * ⨅ a : ℝ, clusterBallVolumeL2 C (A * t) (u - fun _ => a))
    (hΓ : ∀ s : ℝ, X₁ ≤ s → s ≤ R / (2 * A) →
      (⨅ a : ℝ, clusterBallVolumeL2 C s (u - fun _ => a)) ≤
        s / R * (2 * (5 * C₀ * A * b * componentBallL2 C 0 R u) +
          4 * A ^ 2 * clusterBallVolumeL2 C R u))
    (hcabs : |c| ≤ C₀ * b * componentBallL2 C 0 R u / 2 + 2 * K * clusterBallVolumeL2 C R u)
    (hdens : ∀ s : ℝ, M₀ ≤ s → κ * s ^ 2 ≤ (componentEuclideanBall C 0 s).card)
    {r : ℝ} (hr : A ^ 2 * X₁ ≤ r) (hrR : r ≤ R / 2) :
    componentBallL2 C 0 r (u - fun _ => c) ≤
      Real.sqrt (1 / κ) * (k₁ + k₂) * (r / R) * componentBallL2 C 0 R u := by
  have hA0 : 0 < A := by linarith
  have hX₁0 : 0 < X₁ := by linarith
  have hA2 : 1 ≤ A ^ 2 := one_le_pow₀ hA1
  have hA2X₁ : X₁ ≤ A ^ 2 * X₁ := le_mul_of_one_le_left hX₁0.le hA2
  have hk₁0 : 0 ≤ k₁ := by rw [hk₁]; positivity
  have hk₂0 : 0 ≤ k₂ := by rw [hk₂]; positivity
  have hr1 : 1 ≤ r := hX₁1.trans (hA2X₁.trans hr)
  have hr0 : 0 < r := by linarith
  have hMr : M₀ ≤ r := hMX₁.trans (hA2X₁.trans hr)
  have hdensr := componentBallL2_le_of_card C hr0 hκ (hdens r hMr) (u - fun _ => c)
  set N := componentBallL2 C 0 R u with hNdef
  set V := clusterBallVolumeL2 C R u with hVdef
  have hmain : clusterBallVolumeL2 C r (u - fun _ => c) ≤ (k₁ + k₂) * (r / R) * N := by
    have e2 : (k₁ + k₂) * (r / R) * N = k₁ * (r / R) * N + k₂ * (r / R) * N := by ring
    have h5 : 0 ≤ k₂ * (r / R) * N := by positivity
    have h6 : 0 ≤ k₁ * (r / R) * N := by positivity
    rcases le_or_gt r (R / (2 * A ^ 2)) with hsmall | hlarge
    · have hAA : 2 * A ≤ 2 * A ^ 2 := by nlinarith
      have hrA : r ≤ R / (2 * A) :=
        hsmall.trans (div_le_div_of_nonneg_left hR0.le (by positivity) hAA)
      have hXr : X₁ ≤ r := hA2X₁.trans hr
      have h1 := hcstep r hXr hrA
      have hAr1 : X₁ ≤ A * r := hXr.trans (le_mul_of_one_le_left hr0.le hA1)
      have hAr2 : A * r ≤ R / (2 * A) := by
        rw [le_div_iff₀ (by positivity)]
        rw [le_div_iff₀ (by positivity)] at hsmall
        have : A * r * (2 * A) = r * (2 * A ^ 2) := by ring
        linarith
      have h2 := hΓ (A * r) hAr1 hAr2
      have h3 := small_radius_bound hK hA0 hr1 hR0 (by positivity) hV0
        (h1.trans (le_of_eq (add_comm _ _))) h2
      have h4 : r / R * (K * A * (2 * (5 * C₀ * A * b * N) + 4 * A ^ 2 * V) +
          5 * C₀ * A * b * N) ≤
          r / R * (K * A * (2 * (5 * C₀ * A * b * N) + 4 * A ^ 2 * (5 * N)) +
            5 * C₀ * A * b * N) := by
        gcongr
      have e : r / R * (K * A * (2 * (5 * C₀ * A * b * N) + 4 * A ^ 2 * (5 * N)) +
          5 * C₀ * A * b * N) = k₁ * (r / R) * N := by rw [hk₁]; ring
      linarith
    · have hsplit : (u - fun _ => c) = u + fun _ => -c := by funext x; simp [sub_eq_add_neg]
      rw [hsplit]
      refine (clusterBallVolumeL2_add_le C hr0.le _ _).trans ?_
      have h1 := clusterBallVolumeL2_le_of_le C hr0 (by linarith : r ≤ R) u
      have hRr : R / r ≤ 2 * A ^ 2 := by
        rw [div_le_iff₀ hr0]
        rw [div_lt_iff₀ (by positivity)] at hlarge
        linarith
      have h2 := clusterBallVolumeL2_le_lattice C hr1 (fun _ => -c)
      rw [componentBallL2_lattice_const hr0, abs_neg] at h2
      have hrR' : 1 ≤ 2 * A ^ 2 * (r / R) := by
        rw [div_lt_iff₀ (by positivity)] at hlarge
        rw [mul_div_assoc', le_div_iff₀ hR0]
        linarith
      have h3 := mul_le_mul_of_nonneg_right hRr hV0
      have hW0 : 0 ≤ 2 * A ^ 2 * V + 5 * (C₀ * b * N / 2 + 2 * K * V) := by positivity
      have h4 := mul_le_mul_of_nonneg_right hrR' hW0
      have h5' : 2 * A ^ 2 * (r / R) * (2 * A ^ 2 * V + 5 * (C₀ * b * N / 2 + 2 * K * V)) ≤
          2 * A ^ 2 * (r / R) * (2 * A ^ 2 * (5 * N) + 5 * (C₀ * b * N / 2 + 2 * K * (5 * N))) := by
        gcongr
      have e : 2 * A ^ 2 * (r / R) * (2 * A ^ 2 * (5 * N) +
          5 * (C₀ * b * N / 2 + 2 * K * (5 * N))) = k₂ * (r / R) * N := by rw [hk₂]; ring
      have h7 : clusterBallVolumeL2 C r u + clusterBallVolumeL2 C r (fun _ => -c) ≤
          2 * A ^ 2 * V + 5 * (C₀ * b * N / 2 + 2 * K * V) := by
        have := mul_le_mul_of_nonneg_left hcabs (by norm_num : (0 : ℝ) ≤ 5)
        linarith
      linarith
  calc componentBallL2 C 0 r (u - fun _ => c)
      ≤ Real.sqrt (1 / κ) * clusterBallVolumeL2 C r (u - fun _ => c) := hdensr
    _ ≤ Real.sqrt (1 / κ) * ((k₁ + k₂) * (r / R) * N) :=
        mul_le_mul_of_nonneg_left hmain (Real.sqrt_nonneg _)
    _ = Real.sqrt (1 / κ) * (k₁ + k₂) * (r / R) * N := by ring

set_option maxHeartbeats 400000 in
/-- **The order-zero decay with constants on a planar cluster** (Armstrong–Dario, proof of
Lemma 7.3 for `k = 0`, from Lemmas 7.1 and 7.2). The constants `c₁, K'` depend only on
`A, α, K, κ`. -/
theorem exists_planarOrderZeroDecay {A α K κ : ℝ} (hA : 2 ≤ A) (hα : 0 < α) (hK : 0 ≤ K)
    (hκ : 0 < κ) :
    ∃ c₁ K' : ℝ, 1 ≤ c₁ ∧ 0 < K' ∧ ∀ {ω : Configuration 2} (C : OpenComponent ω) (X M₀ : ℝ),
      1 ≤ X → PlanarHarmonicApproximationAt C A α K X →
      (∀ s : ℝ, M₀ ≤ s → κ * s ^ 2 ≤ (componentEuclideanBall C 0 s).card) →
      ∀ R : ℝ, 2 * (A ^ 2 * max (max X M₀) c₁) ≤ R → ∀ u : C → ℝ, IsHarmonicInBall C R u →
        ∃ c : ℝ, ∀ r : ℝ, A ^ 2 * max (max X M₀) c₁ ≤ r → r ≤ R / 2 →
          componentBallL2 C 0 r (u - fun _ => c) ≤ K' * (r / R) * componentBallL2 C 0 R u := by
  classical
  obtain ⟨C₀, hC₀, hcamp⟩ := armstrongDario_orderZero_origin_latticeHarmonic 2 hA hα
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ,
      c₁ = max C₀ (max (latticeHRScale 2) (max (24 * Real.sqrt 2) (max 1 (2 * K * A)))) :=
    ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 5 * K * (1 + A) + 1 := ⟨_, rfl⟩
  obtain ⟨k₁, hk₁⟩ : ∃ k₁ : ℝ, k₁ = K * A * (10 * C₀ * A * b + 20 * A ^ 2) + 5 * C₀ * A * b :=
    ⟨_, rfl⟩
  obtain ⟨k₂, hk₂⟩ : ∃ k₂ : ℝ, k₂ = 2 * A ^ 2 * (10 * A ^ 2 + 5 * C₀ * b / 2 + 50 * K) :=
    ⟨_, rfl⟩
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hb1 : 1 ≤ b := by
    have : 0 ≤ 5 * K * (1 + A) := by positivity
    rw [hb]; linarith
  have hb0 : 0 < b := by linarith
  have hk₁0 : 0 ≤ k₁ := by rw [hk₁]; positivity
  have hk₂pos : 0 < k₂ := by rw [hk₂]; positivity
  have hc₁1 : 1 ≤ c₁ := by rw [hc₁]; simp
  have hc₁C₀ : C₀ ≤ c₁ := by rw [hc₁]; simp
  have hc₁HR : latticeHRScale 2 ≤ c₁ := by rw [hc₁]; simp
  have hc₁24 : 24 * Real.sqrt 2 ≤ c₁ := by rw [hc₁]; simp
  have hc₁KA : 2 * K * A ≤ c₁ := by rw [hc₁]; simp
  refine ⟨c₁, Real.sqrt (1 / κ) * (k₁ + k₂), hc₁1, by positivity, ?_⟩
  intro ω C X M₀ hX1 hHA hdens R hR u hu
  obtain ⟨X₁, hX₁def⟩ : ∃ X₁ : ℝ, X₁ = max (max X M₀) c₁ := ⟨_, rfl⟩
  rw [← hX₁def] at hR ⊢
  have hXX₁ : X ≤ X₁ := by rw [hX₁def]; simp
  have hMX₁ : M₀ ≤ X₁ := by rw [hX₁def]; simp
  have hcX₁ : c₁ ≤ X₁ := by rw [hX₁def]; exact le_max_right _ _
  have hC₀X₁ : C₀ ≤ X₁ := hc₁C₀.trans hcX₁
  have hHRX₁ : latticeHRScale 2 ≤ X₁ := hc₁HR.trans hcX₁
  have h24X₁ : 24 * Real.sqrt ((2 : ℕ) : ℝ) ≤ X₁ := by
    have e : Real.sqrt ((2 : ℕ) : ℝ) = Real.sqrt 2 := by norm_num
    rw [e]; exact hc₁24.trans hcX₁
  have hX₁1 : 1 ≤ X₁ := hc₁1.trans hcX₁
  have hKAX₁ : 2 * K * A ≤ X₁ := hc₁KA.trans hcX₁
  have hX₁0 : 0 < X₁ := by linarith
  have hA2 : 1 ≤ A ^ 2 := one_le_pow₀ hA1
  have hA2X₁ : X₁ ≤ A ^ 2 * X₁ := le_mul_of_one_le_left hX₁0.le hA2
  have hR0 : 0 < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  by_cases hN : componentBallL2 C 0 R u = 0
  · refine ⟨0, fun r hr hrR => ?_⟩
    have hz := (componentBallL2_eq_zero_iff C 0 R u).1 hN
    have hr0 : componentBallL2 C 0 r (u - fun _ => (0 : ℝ)) = 0 := by
      rw [componentBallL2_eq_zero_iff]
      intro x hx
      have hxR : x ∈ componentEuclideanBall C 0 R :=
        componentEuclideanBall_mono C 0 (by linarith) hx
      simp [hz x hxR]
    rw [hr0, hN, mul_zero]
  have hNpos : 0 < componentBallL2 C 0 R u :=
    lt_of_le_of_ne (componentBallL2_nonneg _ _ _ _) (Ne.symm hN)
  have hV0 : 0 ≤ clusterBallVolumeL2 C R u := clusterBallVolumeL2_nonneg _ _ _
  have hVN : clusterBallVolumeL2 C R u ≤ 5 * componentBallL2 C 0 R u :=
    clusterBallVolumeL2_le_componentBallL2 C hR1 u
  have hB0 : 0 < b * componentBallL2 C 0 R u := mul_pos hb0 hNpos
  have hsub0 : ∀ g : C → ℝ, (g - fun _ => (0 : ℝ)) = g := fun g => by funext x; simp
  -- the two radii
  have hR₂ : A * (R / A) = R := by
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hA0.ne', mul_one]
  have hR₂0 : 0 < R / A := by positivity
  have hR₂R : R / A ≤ R := div_le_self hR0.le hA1
  have hAX₁R₂ : A * X₁ ≤ R / A := by
    rw [le_div_iff₀ hA0]
    have : A * X₁ * A = A ^ 2 * X₁ := by ring
    rw [this]; linarith
  have hX₁R₂ : X₁ ≤ R / A := (le_mul_of_one_le_left hX₁0.le hA1).trans hAX₁R₂
  have hAXR₂ : A * X ≤ R / A := (mul_le_mul_of_nonneg_left hXX₁ hA0.le).trans hAX₁R₂
  have hAXR : A * X ≤ R := hAXR₂.trans hR₂R
  obtain ⟨happ₂, -, -⟩ := hHA (R / A) hAXR₂ u (hu.mono hR₂R)
  obtain ⟨-, hii, hiii⟩ := hHA R hAXR u hu
  have happ₂' : HarmonicApproximation (componentBallSeminorm (latticeComponent 2) 0)
      (latticeHarmonicClass 0) (clusterConstants (latticeComponent 2)) A α X₁ (R / A)
      (K / (R / A) * ⨅ a : ℝ, clusterBallVolumeL2 C (R / A) (u - fun _ => a))
      (fun x : latticeComponent 2 => planarCoarse C u x.val) :=
    fun r hr hrR => happ₂ r (hXX₁.trans hr) hrR
  -- the bound `B` on `D_0(R / A) + (R / A) E`
  have hD0 : ballExcess (componentBallSeminorm (latticeComponent 2) 0)
      (clusterConstants (latticeComponent 2)) (R / A)
      (fun x : latticeComponent 2 => planarCoarse C u x.val) ≤
        5 * K * componentBallL2 C 0 R u := by
    have h1 := ballExcess_le_self (componentBallSeminorm (latticeComponent 2) (0 : Vertex 2))
      (clusterConstants (latticeComponent 2)) (R / A)
      (fun x : latticeComponent 2 => planarCoarse C u x.val)
    have h2 := hiii (R / A) (hXX₁.trans hX₁R₂) le_rfl 0
    rw [hR₂, hsub0] at h2
    simp only [sub_zero] at h2
    rw [componentBallSeminorm_apply] at h1
    have h3 := mul_le_mul_of_nonneg_left hVN hK
    linarith
  have hE₂0 : 0 ≤ K / (R / A) * ⨅ a : ℝ, clusterBallVolumeL2 C (R / A) (u - fun _ => a) :=
    mul_nonneg (div_nonneg hK hR₂0.le) (iInf_clusterBallVolumeL2_nonneg C _ _)
  have hE₂ : R / A * (K / (R / A) * ⨅ a : ℝ, clusterBallVolumeL2 C (R / A) (u - fun _ => a)) ≤
      5 * K * A * componentBallL2 C 0 R u := by
    have h1 := iInf_clusterBallVolumeL2_le C (R / A) u 0
    rw [hsub0] at h1
    have h2 := clusterBallVolumeL2_le_of_le C hR₂0 hR₂R u
    have hRR₂ : R / (R / A) = A := by
      rw [div_div_eq_mul_div, mul_comm, mul_div_assoc, div_self hR0.ne', mul_one]
    rw [hRR₂] at h2
    have e : R / A * (K / (R / A) * ⨅ a : ℝ, clusterBallVolumeL2 C (R / A) (u - fun _ => a)) =
        K * ⨅ a : ℝ, clusterBallVolumeL2 C (R / A) (u - fun _ => a) := by
      rw [← mul_assoc, mul_div_assoc', mul_comm (R / A) K, mul_div_assoc,
        div_self hR₂0.ne', mul_one]
    rw [e]
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hK
    have h4 := mul_le_mul_of_nonneg_left hVN (mul_nonneg hK hA0.le)
    nlinarith
  have hBsum : ballExcess (componentBallSeminorm (latticeComponent 2) 0)
      (clusterConstants (latticeComponent 2)) (R / A)
      (fun x : latticeComponent 2 => planarCoarse C u x.val) +
      R / A * (K / (R / A) * ⨅ a : ℝ, clusterBallVolumeL2 C (R / A) (u - fun _ => a)) ≤
        b * componentBallL2 C 0 R u := by
    rw [hb]; nlinarith
  have hX₁R₂A : X₁ ≤ R / A / A := by rw [le_div_iff₀ hA0]; linarith
  obtain ⟨φ, ⟨c, hc⟩, hφ⟩ := hcamp 0 (R / A) X₁ _ _ hX₁1 (max_le hHRX₁ h24X₁) hX₁R₂A hE₂0
    happ₂' _ hB0 hBsum
  have hφeq : ((fun x : latticeComponent 2 => planarCoarse C u x.val) - φ) =
      fun x => planarCoarse C u x.val - c := by
    funext x; simp [hc x]
  -- the coarsened function is close to `c` on the balls of the lattice
  have hφ' : ∀ t : ℝ, X₁ ≤ t → t ≤ R / (2 * A) →
      componentBallL2 (latticeComponent 2) 0 t (fun x => planarCoarse C u x.val - c) ≤
        C₀ * A * b * componentBallL2 C 0 R u * (t / R) := by
    intro t ht htR
    have h := hφ t (max_le ht (hC₀X₁.trans ht))
      (by linarith [show R / A / 2 = R / (2 * A) by ring])
    rw [hφeq] at h
    have e : t / (R / A) = A * (t / R) := by rw [div_div_eq_mul_div]; ring
    rw [e] at h
    linarith [h]
  -- the step of the iteration
  have hcstep : ∀ t : ℝ, X₁ ≤ t → t ≤ R / (2 * A) →
      clusterBallVolumeL2 C t (u - fun _ => c) ≤
        5 * C₀ * A * b * componentBallL2 C 0 R u * (t / R) +
          K / t * ⨅ a : ℝ, clusterBallVolumeL2 C (A * t) (u - fun _ => a) := by
    intro t ht htR
    have ht1 : 1 ≤ t := hX₁1.trans ht
    have htA : t ≤ R / A := htR.trans (div_le_div_of_nonneg_left hR0.le hA0 (by linarith))
    have hsplit : (u - fun _ => c) =
        (u - fun x => planarCoarse C u x.val) + fun x => planarCoarse C u x.val - c := by
      funext x; simp only [Pi.add_apply, Pi.sub_apply]; ring
    rw [hsplit]
    refine (clusterBallVolumeL2_add_le C (by linarith) _ _).trans ?_
    have h1 := hii t (hXX₁.trans ht) htA
    have h2 := clusterBallVolumeL2_le_lattice C ht1 (fun y => planarCoarse C u y - c)
    have h3 := hφ' t ht htR
    linarith
  -- the iteration over the radii `A^k s`
  have hΓ : ∀ s : ℝ, X₁ ≤ s → s ≤ R / (2 * A) →
      (⨅ a : ℝ, clusterBallVolumeL2 C s (u - fun _ => a)) ≤
        s / R * (2 * (5 * C₀ * A * b * componentBallL2 C 0 R u) +
          4 * A ^ 2 * clusterBallVolumeL2 C R u) := by
    intro s hs hsR
    refine le_of_geometric_step (Γ := fun t => ⨅ a : ℝ, clusterBallVolumeL2 C t (u - fun _ => a))
      (by linarith) hK hX₁0 hKAX₁ (by positivity) hV0 hR0
      (fun t => iInf_clusterBallVolumeL2_nonneg C t u) ?_ ?_ hs hsR
    · intro t ht htR
      have h1 := iInf_clusterBallVolumeL2_le C t u 0
      rw [hsub0] at h1
      exact h1.trans (clusterBallVolumeL2_le_of_le C ht htR u)
    · intro t ht htR
      exact (iInf_clusterBallVolumeL2_le C t u c).trans (hcstep t ht htR)
  -- the size of the constant `c`
  have hr₀0 : 0 < R / (2 * A) := by positivity
  have hcabs : |c| ≤ C₀ * b * componentBallL2 C 0 R u / 2 + 2 * K * clusterBallVolumeL2 C R u := by
    have hr₀X : X₁ ≤ R / (2 * A) := by
      rw [le_div_iff₀ (by positivity)]
      have hAA : A ≤ A ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_right hAA hX₁0.le
      linarith
    have hconst := componentBallL2_lattice_const hr₀0 c
    have htri : componentBallL2 (latticeComponent 2) 0 (R / (2 * A)) (fun _ => c) ≤
        componentBallL2 (latticeComponent 2) 0 (R / (2 * A))
            (fun x : latticeComponent 2 => planarCoarse C u x.val) +
          componentBallL2 (latticeComponent 2) 0 (R / (2 * A))
            (fun x => planarCoarse C u x.val - c) := by
      have h := map_sub_le_add (componentBallSeminorm (latticeComponent 2) 0 (R / (2 * A)))
        (fun x : latticeComponent 2 => planarCoarse C u x.val)
        (fun x => planarCoarse C u x.val - c)
      simp only [componentBallSeminorm_apply] at h
      have e : ((fun x : latticeComponent 2 => planarCoarse C u x.val) -
          fun x => planarCoarse C u x.val - c) = fun _ => c := by
        funext x; simp
      rwa [e] at h
    have h1 : componentBallL2 (latticeComponent 2) 0 (R / (2 * A))
        (fun x : latticeComponent 2 => planarCoarse C u x.val) ≤
          2 * K * clusterBallVolumeL2 C R u := by
      have hr₀A : R / (2 * A) ≤ R / A := div_le_div_of_nonneg_left hR0.le hA0 (by linarith)
      have h := hiii (R / (2 * A)) (hXX₁.trans hr₀X) hr₀A 0
      rw [hsub0] at h
      simp only [sub_zero] at h
      have e : A * (R / (2 * A)) = R / 2 := by
        rw [show A * (R / (2 * A)) = R / 2 * (A / A) by ring, div_self hA0.ne', mul_one]
      rw [e] at h
      have h2 := clusterBallVolumeL2_le_of_le C (by positivity : (0 : ℝ) < R / 2)
        (by linarith : R / 2 ≤ R) u
      have e2 : R / (R / 2) = 2 := by
        rw [div_div_eq_mul_div, mul_comm, mul_div_assoc, div_self hR0.ne', mul_one]
      rw [e2] at h2
      have h3 := mul_le_mul_of_nonneg_left h2 hK
      linarith
    have h2 := hφ' (R / (2 * A)) hr₀X le_rfl
    have e : C₀ * A * b * componentBallL2 C 0 R u * (R / (2 * A) / R) =
        C₀ * b * componentBallL2 C 0 R u / 2 := by
      rw [show C₀ * A * b * componentBallL2 C 0 R u * (R / (2 * A) / R) =
        C₀ * b * componentBallL2 C 0 R u / 2 * (A / A) * (R / R) by ring,
        div_self hA0.ne', div_self hR0.ne', mul_one, mul_one]
    rw [e] at h2
    rw [← hconst]; linarith
  -- the conclusion
  exact ⟨c, fun r hr hrR => orderZero_conclusion C u hA1 hK hκ hb0 hC₀ hk₁ hk₂ hX₁1 hMX₁
    hR0 hNpos.le hV0 hVN hcstep hΓ hcabs hdens hr hrR⟩

end Rigidity.Proofs.Regularity
