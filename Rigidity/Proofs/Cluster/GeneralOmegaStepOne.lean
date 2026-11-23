import Rigidity.Proofs.Cluster.GeneralFiniteVolumeMatrix

/-!
# The decrease of `D_n` along `τ_n`, in every dimension

Following Step 1 of the proof of Lemma 5.10 of Armstrong and Dario, let

`D_n = ∑ᵢ (E[ν(□_n, eᵢ)] - E[μ(□_n, ā_{□_n} eᵢ)] - eᵢ · ā_{□_n} eᵢ)` (`cubeOmegaD`).

Testing the minimum characterization of `ā_{□_{n+1}} eᵢ` with `ā_{□_n} eᵢ` gives
`D_{n+1} ≤ D_n - ∑ᵢ J_n(eᵢ) - ∑ᵢ I_n(ā_{□_n} eᵢ)` (`cubeOmegaD_succ_le`), where `I_n`, `J_n` are the
increments of `E[-μ]` and `E[ν]`. These are quadratic forms whose negative parts are at most
`C 3^{-n/4} |q|²` (displays (4.48) and (4.49)); after adding `C 3^{-n/4} |q|²` they are
nonnegative, and a nonnegative quadratic form `g` satisfies
`∑ᵢ g(eᵢ) ≤ d (∑ᵢ |B eᵢ|²) ∑ⱼ g(A eⱼ)` whenever `A B = 1`. Comparing the sums over the bases
`(eᵢ)`, `(ā_{□_n} eᵢ)` and `(ā⁻¹ eᵢ)` with the bounds of display (5.22) on `ā_{□_n}` gives, for
`n ≥ N`,

`D_{n+1} ≤ D_n - c τ_n + C 3^{-n/4}`

(`exists_cubeOmegaD_succ_le`, display (5.45) of Step 1 of the proof of Lemma 5.10 of
Armstrong and Dario, in every dimension `d ≥ 2`).
-/

open MeasureTheory Filter Topology LatticeProb LatticeProb.Percolation Rigidity.External
open scoped ENNReal Classical Matrix

namespace Rigidity.Percolation

variable {d : ℕ}

/-- Adding a multiple of `|q|²` to a quadratic function of the slope keeps it quadratic. -/
theorem IsSlopeQuadratic.add_mul_sum_sq {g : (Fin d → ℝ) → ℝ} (hg : IsSlopeQuadratic g)
    (K : ℝ) : IsSlopeQuadratic fun q => g q + K * ∑ i, q i ^ 2 :=
  hg.add (isSlopeQuadratic_sum_sq.const_mul K)

/-- A function with `g(q) ≥ -K |q|₁²` is nonnegative after adding `d K |q|²`. -/
theorem add_mul_sum_sq_nonneg_of_neg_le {g : (Fin d → ℝ) → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ q, -(K * (∑ i, |q i|) ^ 2) ≤ g q) (q : Fin d → ℝ) :
    0 ≤ g q + d * K * ∑ i, q i ^ 2 := by
  have h1 := h q
  have h2 := mul_le_mul_of_nonneg_left (sq_sum_abs_le_card_mul q) hK
  linarith

/-- **Changing the basis in a sum of values of a nonnegative quadratic function**: when
`A B = 1`, `∑ᵢ g(eᵢ) ≤ d (∑ᵢ |B eᵢ|²) ∑ⱼ g(A eⱼ)`. -/
theorem IsSlopeQuadratic.sum_single_le_of_nonneg {g : (Fin d → ℝ) → ℝ} (hg : IsSlopeQuadratic g)
    (h0 : ∀ x, 0 ≤ g x) {A B : Matrix (Fin d) (Fin d) ℝ} (hAB : A * B = 1) :
    ∑ i, g (Pi.single i 1) ≤
      d * (∑ i, ∑ a, (B *ᵥ Pi.single i 1) a ^ 2) * ∑ j, g (A *ᵥ Pi.single j 1) := by
  have hc := hg.comp_mulVec A
  have hi : ∀ i, g (Pi.single i 1) ≤
      d * (∑ a, (B *ᵥ Pi.single i 1) a ^ 2) * ∑ j, g (A *ᵥ Pi.single j 1) := fun i => by
    have h := hc.le_of_nonneg (fun x => h0 _) (B *ᵥ Pi.single i 1)
    rwa [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec] at h
  calc ∑ i, g (Pi.single i 1) ≤ ∑ i, d * (∑ a, (B *ᵥ Pi.single i 1) a ^ 2) *
        ∑ j, g (A *ᵥ Pi.single j 1) := Finset.sum_le_sum fun i _ => hi i
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- **The columns of the inverse of a coercive matrix**: from `c |q|² ≤ (1/2) q · B q` and
`B A = 1`, `|A eⱼ|² ≤ 1 / (4 c²)`. -/
theorem sum_sq_mulVec_single_le_of_le {A B : Matrix (Fin d) (Fin d) ℝ} {c : ℝ} (hc : 0 < c)
    (hB : ∀ q : Fin d → ℝ, c * ∑ i, q i ^ 2 ≤ 1 / 2 * ∑ i, q i * (B *ᵥ q) i)
    (hBA : B * A = 1) (j : Fin d) :
    ∑ i, (A *ᵥ Pi.single j 1) i ^ 2 ≤ 1 / (4 * c ^ 2) := by
  set y := A *ᵥ Pi.single j 1 with hy
  set S := ∑ i, y i ^ 2 with hS
  have hBy : B *ᵥ y = Pi.single j 1 := by
    rw [hy, Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
  have e : ∑ i, y i * (Pi.single j 1 : Fin d → ℝ) i = y j := by
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
    simp
  have h := hB y
  rw [hBy, e] at h
  have h2 : y j ^ 2 ≤ S :=
    Finset.single_le_sum (f := fun i => y i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h3 : (c * S) ^ 2 ≤ (1 / 2 * y j) ^ 2 := pow_le_pow_left₀ (by positivity) h 2
  have h4 : 4 * c ^ 2 * S ^ 2 ≤ S := by nlinarith
  rw [le_div_iff₀ (by positivity)]
  by_contra hlt
  rw [not_le] at hlt
  have hSpos : 0 < S := by nlinarith [sq_nonneg c]
  nlinarith [mul_lt_mul_of_pos_left hlt hSpos]

/-- The polarization coefficients of a function with `0 ≤ g(x) ≤ C |x|²` are at most `4 C` in
absolute value. -/
theorem slopePolar_sq_le {g : (Fin d → ℝ) → ℝ} {C : ℝ} (h0 : ∀ x, 0 ≤ g x)
    (hup : ∀ x, g x ≤ C * ∑ i, x i ^ 2) (a i : Fin d) : slopePolar g a i ^ 2 ≤ (4 * C) ^ 2 := by
  have hs : ∀ b : Fin d, ∑ k, (Pi.single b 1 : Fin d → ℝ) k ^ 2 = 1 := fun b => by
    rw [Finset.sum_eq_single b (fun k _ hk => by simp [hk]) (by simp)]
    simp
  have ha := hup (Pi.single a 1)
  have hi := hup (Pi.single i 1)
  rw [hs] at ha hi
  have hC : 0 ≤ C := by linarith [h0 (Pi.single a 1)]
  have hai := (hup (Pi.single a 1 + Pi.single i 1)).trans
    (mul_le_mul_of_nonneg_left (sum_sq_single_add_single_le a i) hC)
  have h1 := h0 (Pi.single a 1)
  have h2 := h0 (Pi.single i 1)
  have h3 := h0 (Pi.single a 1 + Pi.single i 1)
  unfold slopePolar
  exact sq_le_sq' (by linarith) (by linarith)

/-- **Step 1 of the proof of Lemma 5.10** (Armstrong and Dario, display (5.45), every
dimension `d ≥ 2`): there are `c > 0`, `C` and `N` with, for every `n ≥ N`,
`D_{n+1} ≤ D_n - c τ_n + C 3^{-n/4}`. -/
theorem exists_cubeOmegaD_succ_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      cubeOmegaD (d := d) p (n + 1) ≤ cubeOmegaD (d := d) p n - c * cubeTau (d := d) p n +
        C * (1 / √(√((3 : ℝ) ^ n))) := by
  obtain ⟨c₀, C₀, hc₀, -, N₁, hN₁⟩ := exists_cubeAhomInvFinite_bounds hd hpc
  obtain ⟨N₂, hN₂⟩ := exists_cubeAhomInvFinite_mul_cubeAhomFinite hd hpc
  obtain ⟨C₁, hC₁, hup⟩ := exists_lintegral_neg_cubeMu_le hd hpc
  obtain ⟨Cμ, hCμ, cμ, hcμ, hIμ⟩ := exists_neg_le_cubeMuIncrement hd hpc
  obtain ⟨Cν, hCν, hJν⟩ := exists_neg_le_cubeNuIncrement hd hpc
  set F := ∑ i : Fin d, ∑ a, ((cubeAhom p)⁻¹ *ᵥ Pi.single i 1) a ^ 2 with hFdef
  have hF0 : 0 ≤ F := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ => sq_nonneg _
  set H := (d : ℝ) * (d * d * (4 * (C₁ * d)) ^ 2) + 1 with hHdef
  have hH : 0 < H := by positivity
  set Kμ := Cμ * (1 + 1 / cμ) with hKμ
  have hKμ0 : 0 ≤ Kμ := by positivity
  set G := 1 / (4 * c₀ ^ 2) with hG
  have hG0 : 0 ≤ G := by positivity
  refine ⟨min (1 / H) (1 / (d * F + 1)), by positivity, d * Kμ * d * G + d * Cν * d,
    by positivity, max N₁ N₂, fun n hn => ?_⟩
  obtain ⟨hinv, hinv'⟩ := hN₂ n (le_of_max_le_right hn)
  obtain ⟨hinv1, -⟩ := hN₂ (n + 1) (by have := le_of_max_le_right hn; omega)
  have hb := hN₁ n (le_of_max_le_left hn)
  set A := cubeAhomFinite (d := d) p n with hAdef
  set B := cubeAhomInvFinite (d := d) p n with hBdef
  set E := 1 / √(√((3 : ℝ) ^ n)) with hEdef
  have hE0 : 0 ≤ E := by positivity
  have hstep := cubeOmegaD_succ_le hd hpc hinv1
  -- the `μ` part
  set K₁ := Kμ * E with hK₁
  have hK₁0 : 0 ≤ K₁ := mul_nonneg hKμ0 hE0
  have hI : ∀ q : Fin d → ℝ, -(K₁ * (∑ i, |q i|) ^ 2) ≤ cubeMuIncrement p n q := fun q => by
    have h1 := hIμ n q
    have h2 := exp_neg_mul_three_pow_le hcμ n
    have hq : 0 ≤ (∑ i, |q i|) ^ 2 := sq_nonneg _
    have h3 : Cμ * ((∑ i, |q i|) ^ 2 * (E + Real.exp (-cμ * (3 : ℝ) ^ n))) ≤
        K₁ * (∑ i, |q i|) ^ 2 := by
      have h4 : E + Real.exp (-cμ * (3 : ℝ) ^ n) ≤ (1 + 1 / cμ) * E := by linarith
      have h5 := mul_le_mul_of_nonneg_left h4 (mul_nonneg hCμ hq)
      calc Cμ * ((∑ i, |q i|) ^ 2 * (E + Real.exp (-cμ * (3 : ℝ) ^ n))) =
            Cμ * (∑ i, |q i|) ^ 2 * (E + Real.exp (-cμ * (3 : ℝ) ^ n)) := by ring
        _ ≤ Cμ * (∑ i, |q i|) ^ 2 * ((1 + 1 / cμ) * E) := h5
        _ = K₁ * (∑ i, |q i|) ^ 2 := by rw [hK₁, hKμ]; ring
    linarith
  set gI : (Fin d → ℝ) → ℝ := fun q => cubeMuIncrement p n q + d * K₁ * ∑ i, q i ^ 2 with hgI
  have hgI0 : ∀ q, 0 ≤ gI q := add_mul_sum_sq_nonneg_of_neg_le hK₁0 hI
  have hgIq : IsSlopeQuadratic gI :=
    ((isSlopeQuadratic_cubeMuMean hd hpc n).sub
      (isSlopeQuadratic_cubeMuMean hd hpc (n + 1))).add_mul_sum_sq _
  have htr := hgIq.sum_single_le_of_nonneg hgI0 hinv'
  have hs : ∀ b : Fin d, ∑ k, (Pi.single b 1 : Fin d → ℝ) k ^ 2 = 1 := fun b => by
    rw [Finset.sum_eq_single b (fun k _ hk => by simp [hk]) (by simp)]
    simp
  have hupn : ∀ x : Fin d → ℝ, cubeMuMean p n x ≤ C₁ * d * ∑ i, x i ^ 2 := fun x => by
    have h1 : cubeMuMean p n x ≤ C₁ * (∑ i, |x i|) ^ 2 :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) (hup ⟨n, 0⟩ x)
    have h2 := mul_le_mul_of_nonneg_left (sq_sum_abs_le_card_mul x) hC₁
    linarith
  have hBcol : ∀ i a : Fin d, (B *ᵥ Pi.single i 1) a ^ 2 ≤ (4 * (C₁ * d)) ^ 2 := fun i a => by
    have e : (B *ᵥ Pi.single i 1) a = slopePolar (cubeMuMean (d := d) p n) a i := by
      rw [Matrix.mulVec_single_one]
      rfl
    rw [e]
    exact slopePolar_sq_le (fun x => ENNReal.toReal_nonneg)
      (fun x => (hupn x).trans_eq (by ring)) a i
  have hBsum : (d : ℝ) * ∑ i, ∑ a, (B *ᵥ Pi.single i 1) a ^ 2 ≤ H := by
    have h1 : ∑ i : Fin d, ∑ a : Fin d, (B *ᵥ Pi.single i 1) a ^ 2 ≤
        ∑ _i : Fin d, ∑ _a : Fin d, (4 * (C₁ * d)) ^ 2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ => hBcol i a
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) d)
    rw [hHdef]
    nlinarith
  have hAcol : ∀ j : Fin d, ∑ i, (A *ᵥ Pi.single j 1) i ^ 2 ≤ G := fun j =>
    sum_sq_mulVec_single_le_of_le hc₀ (fun q => (hb q).1) hinv j
  have hsumA0 : 0 ≤ ∑ j, gI (A *ᵥ Pi.single j 1) := Finset.sum_nonneg fun j _ => hgI0 _
  have hτμ : cubeMuTau (d := d) p n ≤ ∑ i, gI (Pi.single i 1) := by
    refine Finset.sum_le_sum fun i _ => max_le ?_ (hgI0 _)
    simp only [hgI, hs]
    nlinarith
  have hμpart : -∑ i, cubeMuIncrement p n (A *ᵥ Pi.single i 1) ≤
      -(cubeMuTau (d := d) p n / H) + d * K₁ * d * G := by
    have k1 : cubeMuTau (d := d) p n ≤ H * ∑ j, gI (A *ᵥ Pi.single j 1) :=
      hτμ.trans (htr.trans (mul_le_mul_of_nonneg_right hBsum hsumA0))
    have k2 : ∑ j, gI (A *ᵥ Pi.single j 1) ≤
        ∑ i, cubeMuIncrement p n (A *ᵥ Pi.single i 1) + d * K₁ * d * G := by
      simp only [hgI]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      have h1 : ∑ j, ∑ i, (A *ᵥ Pi.single j 1) i ^ 2 ≤ ∑ _j : Fin d, G :=
        Finset.sum_le_sum fun j _ => hAcol j
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ d * K₁)
      linarith
    have k3 : cubeMuTau (d := d) p n / H ≤ ∑ j, gI (A *ᵥ Pi.single j 1) := by
      rw [div_le_iff₀ hH]
      linarith
    linarith
  -- the `ν` part
  set K₂ := Cν * E with hK₂
  have hK₂0 : 0 ≤ K₂ := mul_nonneg hCν hE0
  have hJ : ∀ ξ : Fin d → ℝ, -(K₂ * (∑ i, |ξ i|) ^ 2) ≤ cubeNuIncrement p n ξ := fun ξ => by
    have h1 := hJν n ξ
    have h2 := one_div_sqrt_three_pow_le n
    have hq : 0 ≤ Cν * (∑ i, |ξ i|) ^ 2 := by positivity
    have h3 := mul_le_mul_of_nonneg_left h2 hq
    have e : Cν * (∑ i, |ξ i|) ^ 2 / √3 ^ n = Cν * (∑ i, |ξ i|) ^ 2 * (1 / √3 ^ n) := by ring
    rw [e] at h1
    have e2 : Cν * (∑ i, |ξ i|) ^ 2 * E = K₂ * (∑ i, |ξ i|) ^ 2 := by rw [hK₂]; ring
    linarith
  set gJ : (Fin d → ℝ) → ℝ := fun ξ => cubeNuIncrement p n ξ + d * K₂ * ∑ i, ξ i ^ 2 with hgJ
  have hgJ0 : ∀ ξ, 0 ≤ gJ ξ := add_mul_sum_sq_nonneg_of_neg_le hK₂0 hJ
  have hgJq : IsSlopeQuadratic gJ :=
    ((isSlopeQuadratic_cubeNuMean p n).sub (isSlopeQuadratic_cubeNuMean p (n + 1))).add_mul_sum_sq _
  have hsumJ0 : 0 ≤ ∑ j, gJ (Pi.single j 1) := Finset.sum_nonneg fun j _ => hgJ0 _
  have hτν : cubeNuTau (d := d) p n ≤ d * F * ∑ j, gJ (Pi.single j 1) := by
    have h1 : ∀ i : Fin d, max (cubeNuIncrement p n ((cubeAhom p)⁻¹ *ᵥ Pi.single i 1)) 0 ≤
        d * (∑ a, ((cubeAhom p)⁻¹ *ᵥ Pi.single i 1) a ^ 2) * ∑ j, gJ (Pi.single j 1) := by
      intro i
      refine (max_le ?_ (hgJ0 _)).trans (hgJq.le_of_nonneg hgJ0 _)
      simp only [hgJ]
      have : 0 ≤ d * K₂ * ∑ a, ((cubeAhom p)⁻¹ *ᵥ Pi.single i 1) a ^ 2 := by positivity
      linarith
    calc cubeNuTau (d := d) p n ≤ ∑ i : Fin d,
          d * (∑ a, ((cubeAhom p)⁻¹ *ᵥ Pi.single i 1) a ^ 2) * ∑ j, gJ (Pi.single j 1) :=
          Finset.sum_le_sum fun i _ => h1 i
      _ = d * F * ∑ j, gJ (Pi.single j 1) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hνpart : -∑ i : Fin d, cubeNuIncrement p n (Pi.single i 1) ≤
      -(cubeNuTau (d := d) p n / (d * F + 1)) + d * K₂ * d := by
    have e : ∑ j : Fin d, gJ (Pi.single j 1) = ∑ i : Fin d, cubeNuIncrement p n (Pi.single i 1) + d * K₂ * d := by
      simp only [hgJ, hs, mul_one]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring
    have k3 : cubeNuTau (d := d) p n / (d * F + 1) ≤ ∑ j, gJ (Pi.single j 1) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  -- conclusion
  have hτμ0 := cubeMuTau_nonneg (d := d) p n
  have hτν0 := cubeNuTau_nonneg (d := d) p n
  set c := min (1 / H) (1 / (d * F + 1)) with hc
  have hcμ' : c * cubeMuTau (d := d) p n ≤ cubeMuTau (d := d) p n / H :=
    calc c * cubeMuTau (d := d) p n ≤ 1 / H * cubeMuTau (d := d) p n :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hτμ0
      _ = cubeMuTau (d := d) p n / H := by ring
  have hcν' : c * cubeNuTau (d := d) p n ≤ cubeNuTau (d := d) p n / (d * F + 1) :=
    calc c * cubeNuTau (d := d) p n ≤ 1 / (d * F + 1) * cubeNuTau (d := d) p n :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hτν0
      _ = cubeNuTau (d := d) p n / (d * F + 1) := by ring
  have herr : d * K₁ * d * G + d * K₂ * d = (d * Kμ * d * G + d * Cν * d) * E := by
    rw [hK₁, hK₂]
    ring
  have htau : cubeTau (d := d) p n = cubeMuTau (d := d) p n + cubeNuTau (d := d) p n := rfl
  rw [htau, mul_add]
  linarith

end Rigidity.Percolation
