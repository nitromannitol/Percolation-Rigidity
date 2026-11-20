import Rigidity.Proofs.Percolation.PlanarTriadicPartition
import Rigidity.Percolation.RestrictedReachability

/-!
# Meshed triadic cubes in the plane

A triadic cube `Q` of side `s = 3ⁿ` is meshed when every integer square of side between `s` and
`9s` contained in the square of side `9s` centred at the centre of `Q` carries a strip mesh of width
`⌊s/100⌋`. Meshed cubes form a measurable random family, and Kesten's rectangle crossing estimate
bounds the probability that a cube is not meshed by `C exp(-c s)`. The stopping construction of
good cubes therefore yields a partition of `ℤ²` (Armstrong and Dario, Proposition 2.1) all of whose
cubes and their ancestors are meshed, which gives local connectivity of the infinite cluster at the
scale of the partition.
-/

open MeasureTheory Filter LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

/-- Half the side, `(9s - 1)/2`, of the square of side `9s` around a triadic cube of side `s`. -/
def TriadicCube.ninefoldRadius (Q : TriadicCube 2) : ℤ := (9 * 3 ^ Q.scale - 1) / 2

/-- The integer squares of side between `s` and `9s` inside the square of side `9s` centred at the
centre of a triadic cube of side `s`. -/
noncomputable def TriadicCube.planarSquares (Q : TriadicCube 2) : Finset (IntegerCube 2) :=
  ((((Finset.Icc (Q.center 0 - Q.ninefoldRadius) (Q.center 0 + Q.ninefoldRadius)) ×ˢ
      (Finset.Icc (Q.center 1 - Q.ninefoldRadius) (Q.center 1 + Q.ninefoldRadius))) ×ˢ
      Finset.Icc (3 ^ Q.scale) (9 * 3 ^ Q.scale)).image
    (fun x : (ℤ × ℤ) × ℕ => (⟨![x.1.1, x.1.2], x.2⟩ : IntegerCube 2))).filter
    (fun R => ∀ i, R.corner i + R.size ≤ Q.center i + Q.ninefoldRadius + 1)

/-- Membership in the squares around a triadic cube. -/
theorem TriadicCube.mem_planarSquares {Q : TriadicCube 2} {R : IntegerCube 2} :
    R ∈ Q.planarSquares ↔ 3 ^ Q.scale ≤ R.size ∧ R.size ≤ 9 * 3 ^ Q.scale ∧
      ∀ i, Q.center i - Q.ninefoldRadius ≤ R.corner i ∧
        R.corner i + R.size ≤ Q.center i + Q.ninefoldRadius + 1 := by
  constructor
  · intro hR
    obtain ⟨hR, hin⟩ := Finset.mem_filter.1 hR
    obtain ⟨⟨⟨a, b⟩, k⟩, hx, rfl⟩ := Finset.mem_image.1 hR
    simp only [Finset.mem_product, Finset.mem_Icc] at hx
    obtain ⟨⟨⟨ha1, ha2⟩, hb1, hb2⟩, hk1, hk2⟩ := hx
    refine ⟨hk1, hk2, fun i => ⟨?_, hin i⟩⟩
    fin_cases i
    · simpa using ha1
    · simpa using hb1
  · rintro ⟨hk1, hk2, hc⟩
    have hpos : 1 ≤ 3 ^ Q.scale := Nat.one_le_pow _ _ (by norm_num)
    refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨((R.corner 0, R.corner 1), R.size), ?_, ?_⟩,
      fun i => (hc i).2⟩
    · have h0 := hc 0
      have h1 := hc 1
      simp only [Finset.mem_product, Finset.mem_Icc]
      refine ⟨⟨⟨h0.1, by omega⟩, h1.1, by omega⟩, hk1, hk2⟩
    · cases R with
      | mk corner size =>
        simp only [IntegerCube.mk.injEq, and_true]
        funext i
        fin_cases i <;> rfl

/-- A triadic cube is meshed when all its surrounding squares carry strip meshes of width
`⌊s/100⌋`. -/
def TriadicCube.planarMeshed (Q : TriadicCube 2) (ω : Configuration 2) : Prop :=
  ∀ R ∈ Q.planarSquares, PlanarMesh ω R (3 ^ Q.scale / 100)

/-- The random family of meshed triadic cubes. -/
def planarMeshedFamily (ω : Configuration 2) : Set (TriadicCube 2) :=
  {Q | Q.planarMeshed ω}

/-- Connectivity inside a fixed region is a measurable event, in the form of open walks. -/
theorem measurableSet_reachIn (S : Set (Vertex 2)) (a b : Vertex 2) :
    MeasurableSet {ω : Configuration 2 | ReachIn ω S a b} := by
  by_cases ha : a ∈ S
  · have heq : {ω : Configuration 2 | ReachIn ω S a b} =
        {ω | (openIn ω S).Reachable a b} := by
      ext ω
      exact ⟨reachIn_reachable_openIn, reachIn_of_reachable_openIn ha⟩
    rw [heq]
    exact measurableSet_openIn_reachable S a b
  · have heq : {ω : Configuration 2 | ReachIn ω S a b} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => ha h.start_mem
    rw [heq]
    exact MeasurableSet.empty

/-- A strip mesh is a measurable event. -/
theorem measurableSet_planarMesh (R : IntegerCube 2) (w : ℕ) :
    MeasurableSet {ω : Configuration 2 | PlanarMesh ω R w} := by
  apply measurableSet_setOf.2
  refine Measurable.and ?_ ?_
  · refine Measurable.forall fun r => measurable_const.imp (measurable_const.imp ?_)
    exact Measurable.exists fun a => Measurable.exists fun b =>
      (measurableSet_setOf.1 (measurableSet_reachIn _ a b)).and measurable_const
  · refine Measurable.forall fun r => measurable_const.imp (measurable_const.imp ?_)
    exact Measurable.exists fun a => Measurable.exists fun b =>
      (measurableSet_setOf.1 (measurableSet_reachIn _ a b)).and measurable_const

/-- Meshedness of a fixed triadic cube is a measurable event. -/
theorem measurableSet_mem_planarMeshedFamily (Q : TriadicCube 2) :
    MeasurableSet {ω : Configuration 2 | Q ∈ planarMeshedFamily ω} := by
  change MeasurableSet {ω | ∀ R ∈ Q.planarSquares, PlanarMesh ω R (3 ^ Q.scale / 100)}
  have heq : {ω : Configuration 2 | ∀ R ∈ Q.planarSquares, PlanarMesh ω R (3 ^ Q.scale / 100)} =
      ⋂ R ∈ Q.planarSquares, {ω | PlanarMesh ω R (3 ^ Q.scale / 100)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
  rw [heq]
  exact Finset.measurableSet_biInter _ fun R _ => measurableSet_planarMesh R _

/-- A polynomial factor `(s + 1)^k` costs half of an exponential rate. -/
theorem add_one_pow_mul_exp_neg_le (k : ℕ) {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    (s + 1) ^ k * Real.exp (-(a * s)) ≤
      (max 1 (2 * (k + 1) / a)) ^ k * Real.exp (-(a / 2 * s)) := by
  set M := max 1 (2 * (k + 1) / a)
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMk : 2 * (k + 1) / a ≤ M := le_max_right _ _
  have hk : (0 : ℝ) < k + 1 := by positivity
  set t : ℝ := a * s / (2 * (k + 1)) with htdef
  have ht0 : 0 ≤ t := by positivity
  have hlin : s + 1 ≤ M * (t + 1) := by
    have hs' : s ≤ M * t := by
      have : 2 * (k + 1) / a * t = s := by
        rw [htdef]
        field_simp
      calc s = 2 * (k + 1) / a * t := this.symm
        _ ≤ M * t := by gcongr
    nlinarith
  have hexp : (t + 1) ^ k ≤ Real.exp (a / 2 * s) := by
    have h := Real.add_one_le_exp t
    calc (t + 1) ^ k ≤ Real.exp t ^ k := pow_le_pow_left₀ (by positivity) h k
      _ = Real.exp (k * t) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (a / 2 * s) := by
        apply Real.exp_le_exp.2
        rw [htdef, ← mul_div_assoc, div_le_iff₀ (by positivity)]
        have hnn : 0 ≤ a * s := by positivity
        nlinarith
  have hpow : (s + 1) ^ k ≤ M ^ k * Real.exp (a / 2 * s) := by
    calc (s + 1) ^ k ≤ (M * (t + 1)) ^ k := pow_le_pow_left₀ (by linarith) hlin k
      _ = M ^ k * (t + 1) ^ k := mul_pow M (t + 1) k
      _ ≤ M ^ k * Real.exp (a / 2 * s) := by gcongr
  calc (s + 1) ^ k * Real.exp (-(a * s)) ≤ M ^ k * Real.exp (a / 2 * s) * Real.exp (-(a * s)) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = M ^ k * Real.exp (-(a / 2 * s)) := by
      rw [mul_assoc, ← Real.exp_add]
      ring_nf

/-- The number of squares around a triadic cube is polynomial in its side. -/
theorem TriadicCube.card_planarSquares_le (Q : TriadicCube 2) :
    (Q.planarSquares.card : ℝ) ≤ (9 * (3 : ℝ) ^ Q.scale + 1) ^ 2 * (8 * (3 : ℝ) ^ Q.scale + 1) := by
  have hcard : Q.planarSquares.card ≤ (9 * 3 ^ Q.scale + 1) ^ 2 * (8 * 3 ^ Q.scale + 1) := by
    refine (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans ?_)
    rw [Finset.card_product, Finset.card_product, Int.card_Icc, Int.card_Icc, Nat.card_Icc]
    have hr : 2 * Q.ninefoldRadius ≤ 9 * 3 ^ Q.scale - 1 := by
      unfold TriadicCube.ninefoldRadius
      omega
    have h1 : (Q.center 0 + Q.ninefoldRadius + 1 - (Q.center 0 - Q.ninefoldRadius)).toNat ≤
        9 * 3 ^ Q.scale + 1 := by
      have : ((9 * 3 ^ Q.scale : ℕ) : ℤ) = 9 * 3 ^ Q.scale := by push_cast; ring
      omega
    have h2 : (Q.center 1 + Q.ninefoldRadius + 1 - (Q.center 1 - Q.ninefoldRadius)).toNat ≤
        9 * 3 ^ Q.scale + 1 := by
      have : ((9 * 3 ^ Q.scale : ℕ) : ℤ) = 9 * 3 ^ Q.scale := by push_cast; ring
      omega
    calc _ ≤ (9 * 3 ^ Q.scale + 1) * (9 * 3 ^ Q.scale + 1) * (9 * 3 ^ Q.scale + 1 - 3 ^ Q.scale) :=
          Nat.mul_le_mul (Nat.mul_le_mul h1 h2) le_rfl
      _ ≤ _ := by
        rw [sq]
        apply Nat.mul_le_mul le_rfl
        omega
  have h := (Nat.cast_le (α := ℝ)).2 hcard
  push_cast at h
  exact h

/-- **Meshed planar cubes.** For `p > p_c(2)`, triadic cubes of side at least `3⁷` fail to be meshed
with probability at most `C exp(-c · 3ⁿ)`. -/
theorem measure_not_planarMeshed_le {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ Q : TriadicCube 2, 7 ≤ Q.scale →
      latticeBondLaw 2 p {ω | Q ∉ planarMeshedFamily ω} ≤
        ENNReal.ofReal (C * Real.exp (-c * (3 : ℝ) ^ Q.scale)) := by
  obtain ⟨C₀, c₀, hC₀, hc₀, hmesh⟩ := measure_not_planarMesh_le hpc
  set a : ℝ := c₀ / 100 with hadef
  have ha : 0 < a := by positivity
  set M : ℝ := (max 1 (2 * ((5 : ℕ) + 1) / a)) ^ 5
  have hM : 0 ≤ M := by positivity
  set K : ℝ := 2 * 9 ^ 2 * 9 ^ 2 * 8 * C₀ * Real.exp c₀ * M with hKdef
  refine ⟨K, a / 2, by positivity, by positivity, fun Q hQ => ?_⟩
  set w := 3 ^ Q.scale / 100 with hwdef
  set s : ℝ := (3 : ℝ) ^ Q.scale with hsdef
  have hs0 : 0 ≤ s := by positivity
  have hwlow : s / 100 - 1 ≤ (w : ℝ) := by
    have h : 3 ^ Q.scale < 100 * (w + 1) := by
      have := Nat.lt_mul_div_succ (3 ^ Q.scale) (show 0 < 100 by norm_num)
      omega
    have h' : ((3 ^ Q.scale : ℕ) : ℝ) < 100 * ((w : ℝ) + 1) := by exact_mod_cast h
    push_cast at h'
    linarith
  have hexpw : Real.exp (-(c₀ * w)) ≤ Real.exp c₀ * Real.exp (-(a * s)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    rw [hadef]
    nlinarith
  set f : ℝ := 2 * ((9 * s + 1) * (C₀ * (9 * s + 1) * Real.exp (-(c₀ * w)))) with hfdef
  have hterm : ∀ R ∈ Q.planarSquares,
      latticeBondLaw 2 p {ω | ¬ PlanarMesh ω R w} ≤ ENNReal.ofReal f := by
    intro R hR
    refine (hmesh R w).trans (ENNReal.ofReal_le_ofReal ?_)
    have hRs : (R.size : ℝ) ≤ 9 * s := by
      have := (TriadicCube.mem_planarSquares.1 hR).2.1
      have h' : (R.size : ℝ) ≤ ((9 * 3 ^ Q.scale : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h'
      exact h'
    have he : 0 ≤ Real.exp (-(c₀ * w)) := (Real.exp_pos _).le
    rw [hfdef]
    have h1 : (R.size : ℝ) + 1 ≤ 9 * s + 1 := by linarith
    have h0 : (0 : ℝ) ≤ (R.size : ℝ) + 1 := by positivity
    gcongr
  have hsub : {ω | Q ∉ planarMeshedFamily ω} ⊆
      ⋃ R ∈ Q.planarSquares, {ω | ¬ PlanarMesh ω R w} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, planarMeshedFamily, TriadicCube.planarMeshed, not_forall] at hω
    obtain ⟨R, hR, hfail⟩ := hω
    exact Set.mem_biUnion hR hfail
  refine (measure_mono hsub).trans ((measure_biUnion_le_card_mul _ _ _ hterm).trans
    (ENNReal.ofReal_le_ofReal ?_))
  have hcard := Q.card_planarSquares_le
  rw [← hsdef] at hcard
  have hpoly := add_one_pow_mul_exp_neg_le 5 ha hs0
  have hf0 : 0 ≤ f := by rw [hfdef]; positivity
  have hpow : (9 * s + 1) ^ 2 * (8 * s + 1) * (9 * s + 1) ^ 2 ≤
      9 ^ 2 * 9 ^ 2 * 8 * (s + 1) ^ 5 := by
    have h1 : 9 * s + 1 ≤ 9 * (s + 1) := by linarith
    have h2 : 8 * s + 1 ≤ 8 * (s + 1) := by linarith
    calc (9 * s + 1) ^ 2 * (8 * s + 1) * (9 * s + 1) ^ 2
        ≤ (9 * (s + 1)) ^ 2 * (8 * (s + 1)) * (9 * (s + 1)) ^ 2 := by gcongr
      _ = 9 ^ 2 * 9 ^ 2 * 8 * (s + 1) ^ 5 := by ring
  calc (Q.planarSquares.card : ℝ) * f
      ≤ (9 * s + 1) ^ 2 * (8 * s + 1) * f := mul_le_mul_of_nonneg_right hcard hf0
    _ = 2 * C₀ * ((9 * s + 1) ^ 2 * (8 * s + 1) * (9 * s + 1) ^ 2) * Real.exp (-(c₀ * w)) := by
      rw [hfdef]; ring
    _ ≤ 2 * C₀ * (9 ^ 2 * 9 ^ 2 * 8 * (s + 1) ^ 5) * (Real.exp c₀ * Real.exp (-(a * s))) := by
      gcongr
    _ = 2 * 9 ^ 2 * 9 ^ 2 * 8 * C₀ * Real.exp c₀ * ((s + 1) ^ 5 * Real.exp (-(a * s))) := by
      ring
    _ ≤ 2 * 9 ^ 2 * 9 ^ 2 * 8 * C₀ * Real.exp c₀ * (M * Real.exp (-(a / 2 * s))) := by
      gcongr
    _ = K * Real.exp (-(a / 2) * s) := by rw [hKdef]; ring_nf

/-- **The planar partition of meshed good cubes** (Armstrong and Dario, Proposition 2.1, in
dimension two, with meshed cubes as well-connected cubes). -/
theorem planar_meshed_partition_estimates {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    let G : Configuration 2 → Set (TriadicCube 2) := fun ω =>
      TriadicCube.goodOfWellConnected (planarMeshedFamily ω)
    (∀ᵐ ω ∂(latticeBondLaw 2 p), ∀ x : Vertex 2,
      ∃! Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping (G ω)) ∧
    (∃ θ : ℝ, 0 < θ ∧ ∀ x : Vertex 2,
      Integrable (fun ω => Real.exp (TriadicCube.stoppingSize (G ω) x / θ)) (latticeBondLaw 2 p) ∧
      (∫ ω, Real.exp (TriadicCube.stoppingSize (G ω) x / θ) ∂(latticeBondLaw 2 p)) ≤ 2) ∧
    (∃ K k : ℝ, 0 < K ∧ 0 < k ∧ ∀ (A : TriadicCube 2) (n : ℕ),
      (latticeBondLaw 2 p) {ω | ∃ x ∈ A.boundaryInterior n, ∃ Q R : TriadicCube 2,
        x ∈ Q.vertices ∧ x ∈ R.vertices ∧ Q.IsMaximalStopping (G ω) ∧
          R.IsMaximalStopping (TriadicCube.localGoodCentered (G ω) A.vertices) ∧ Q ≠ R} ≤
        ENNReal.ofReal (K * (3 : ℝ) ^ ((A.scale : ℝ) - n) *
          Real.exp (-k * (3 : ℝ) ^ n))) := by
  obtain ⟨C, c, hC, hc, hlarge⟩ := measure_not_planarMeshed_le hpc
  have hall := TriadicCube.measure_le_exp_of_large_scale (latticeBondLaw 2 p)
    (fun Q => {ω | Q ∉ planarMeshedFamily ω}) 7 C c hC hc hlarge
  set B : ℝ := C + Real.exp (c * (3 : ℝ) ^ 7) with hBdef
  have hB : 0 ≤ B := by positivity
  exact TriadicCube.wellConnected_partition_estimates (by norm_num) (latticeBondLaw 2 p)
    planarMeshedFamily measurableSet_mem_planarMeshedFamily (ENNReal.ofReal B)
    ENNReal.ofReal_ne_top c hc (fun Q => by
      rw [← ENNReal.ofReal_mul hB]
      exact hall Q)

end Rigidity.Percolation
