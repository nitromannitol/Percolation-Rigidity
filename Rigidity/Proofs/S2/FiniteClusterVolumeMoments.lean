import Rigidity.Percolation.Pisztora.FiniteClusters
import Rigidity.Proofs.S2.FiniteClusterMoment
import Rigidity.Proofs.S2.InfluenceMoment

/-!
# Moments of finite clusters above the critical point in dimension at least three

Above the critical point in dimension `d ≥ 3`, a finite open cluster has at least `n` vertices
with probability at most `C exp(-c n^{1/d})`. Hence the size `|𝒞_x|` of the finite cluster of a
vertex (zero for an infinite cluster) satisfies `E[exp(a |𝒞_x|^{1/d})] ≤ C` uniformly in `x`,
and `E[|𝒞_x|^r] ≤ (dr)! a^{-dr} C`. The single-bond influences on the infinite-cluster count of a
triadic cube, bounded by four finite-cluster sizes, inherit these factorial moment bounds.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

variable {d : ℕ}

/-- The vertex set of the component of `x` is the set of vertices reachable from `x`. -/
theorem component_supp_eq_reachable (ω : Configuration d) (x : Vertex d) :
    ((openGraph ω).connectedComponentMk x).supp = {y | (openGraph ω).Reachable x y} := by
  ext y
  simp only [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq,
    Set.mem_setOf_eq]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- A supercritical finite-cluster size has a uniform exponential moment of its `d`-th root. -/
theorem finiteComponent_exp_root_moment [NeZero d] (hd : 3 ≤ d) {p : unitInterval}
    (hp : criticalProbability d < (p : ℝ)) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∀ x : Vertex d,
      Integrable (fun ω => Real.exp
          (a * ((finiteComponentVertices ω x).card : ℝ) ^ (d : ℝ)⁻¹)) (latticeBondLaw d p) ∧
      (∫ ω, Real.exp (a * ((finiteComponentVertices ω x).card : ℝ) ^ (d : ℝ)⁻¹)
          ∂latticeBondLaw d p) ≤ C := by
  obtain ⟨C, c, hC, hc, htail⟩ := Rigidity.Percolation.exists_finite_cluster_card_le hd hp
  have hd0 : (0 : ℝ) < (d : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast (show 0 < d by omega))
  let b : ℕ → ℝ := fun n => (C + 1) * Real.exp (-(c / 2 * (n : ℝ) ^ (d : ℝ)⁻¹))
  have hb0 : ∀ n, 0 ≤ b n := fun n => by dsimp [b]; positivity
  have hbs : Summable b :=
    (Rigidity.Proofs.S3.summable_exp_neg_mul_rpow (half_pos hc) hd0).mul_left (C + 1)
  let B := (∑' n, b n) + 1
  have hB : 0 < B := by dsimp [B]; linarith [show 0 ≤ ∑' n, b n from tsum_nonneg hb0]
  refine ⟨c / 2, B, by positivity, hB, fun x => ?_⟩
  let X : Configuration d → ℕ := fun ω => (finiteComponentVertices ω x).card
  let g : ℕ → ℝ := fun n => Real.exp (c / 2 * (n : ℝ) ^ (d : ℝ)⁻¹)
  have hXm : Measurable X := measurable_finiteComponent_size x
  have hmass : ∀ n : ℕ, latticeBondLaw d p {ω | X ω = n} ≤
      ENNReal.ofReal ((C + 1) * Real.exp (-(c * (n : ℝ) ^ (d : ℝ)⁻¹))) := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp only [Nat.cast_zero, Real.zero_rpow hd0.ne', mul_zero, neg_zero, Real.exp_zero,
        mul_one]
      calc
        _ ≤ (latticeBondLaw d p) Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
        _ ≤ ENNReal.ofReal (C + 1) := by rw [ENNReal.one_le_ofReal]; linarith
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      refine (measure_mono ?_).trans ((htail x n).trans (ENNReal.ofReal_le_ofReal ?_))
      · intro ω hω
        change X ω = n at hω
        have hsize : ((openGraph ω).connectedComponentMk x).supp.ncard = n := by
          simpa only [X, card_finiteComponentVertices] using hω
        have hf : ((openGraph ω).connectedComponentMk x).supp.Finite := by
          by_contra hnot
          have hz := (Set.not_finite.mp hnot).ncard
          omega
        rw [component_supp_eq_reachable] at hsize hf
        exact ⟨hf, hsize.ge⟩
      · gcongr
        linarith
  have hterm : ∀ n, ENNReal.ofReal (g n) * latticeBondLaw d p {ω | X ω = n} ≤
      ENNReal.ofReal (b n) := by
    intro n
    refine (mul_le_mul_right (hmass n) _).trans ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    dsimp only [g, b]
    calc
      _ = (C + 1) * Real.exp (c / 2 * (n : ℝ) ^ (d : ℝ)⁻¹ - c * (n : ℝ) ^ (d : ℝ)⁻¹) := by
        rw [sub_eq_add_neg, Real.exp_add]
        ring
      _ = (C + 1) * Real.exp (-(c / 2 * (n : ℝ) ^ (d : ℝ)⁻¹)) := by congr 1; congr 1; ring
      _ ≤ _ := le_rfl
  have hlin : ∫⁻ ω, ‖g (X ω)‖ₑ ∂latticeBondLaw d p ≤ ENNReal.ofReal B := by
    rw [← lintegral_map (f := fun n => ‖g n‖ₑ) measurable_from_nat hXm, lintegral_countable']
    calc
      _ = ∑' n, ENNReal.ofReal (g n) * latticeBondLaw d p {ω | X ω = n} := by
        congr 1
        ext n
        rw [Real.enorm_eq_ofReal (Real.exp_pos _).le,
          Measure.map_apply hXm (measurableSet_singleton n)]
        rfl
      _ ≤ ∑' n, ENNReal.ofReal (b n) := ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal (∑' n, b n) := (ENNReal.ofReal_tsum_of_nonneg hb0 hbs).symm
      _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (by dsimp [B]; linarith)
  have hint : Integrable (fun ω => g (X ω)) (latticeBondLaw d p) :=
    ⟨((measurable_from_nat (f := g)).comp hXm).aestronglyMeasurable,
      hlin.trans_lt ENNReal.ofReal_lt_top⟩
  refine ⟨hint, ?_⟩
  have hreal : ENNReal.ofReal (∫ ω, g (X ω) ∂latticeBondLaw d p) ≤ ENNReal.ofReal B := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)]
    simpa only [g, Real.enorm_eq_ofReal (Real.exp_pos _).le] using hlin
  exact (ENNReal.ofReal_le_ofReal_iff hB.le).1 hreal

/-- An exponential bound on the `d`-th root controls integer powers. -/
theorem pow_le_factorial_mul_exp_root {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (hd : d ≠ 0)
    (r : ℕ) :
    x ^ r ≤ ((d * r).factorial : ℝ) / a ^ (d * r) * Real.exp (a * x ^ (d : ℝ)⁻¹) := by
  have hf : (0 : ℝ) < ((d * r).factorial : ℝ) := by positivity
  have hpow : 0 < a ^ (d * r) := pow_pos ha _
  have h := Real.pow_div_factorial_le_exp (a * x ^ (d : ℝ)⁻¹) (by positivity) (d * r)
  have hs : (a * x ^ (d : ℝ)⁻¹) ^ (d * r) = a ^ (d * r) * x ^ r := by
    rw [mul_pow]
    congr 1
    rw [pow_mul, Real.rpow_inv_natCast_pow hx hd]
  rw [hs] at h
  have h' : a ^ (d * r) * x ^ r ≤ Real.exp (a * x ^ (d : ℝ)⁻¹) * ((d * r).factorial : ℝ) :=
    (div_le_iff₀ hf).1 h
  calc
    x ^ r ≤ (Real.exp (a * x ^ (d : ℝ)⁻¹) * ((d * r).factorial : ℝ)) / a ^ (d * r) :=
      (le_div_iff₀ hpow).2 (by simpa [mul_comm] using h')
    _ = _ := by ring

/-- All integer moments of a supercritical finite-cluster size satisfy a uniform factorial
bound. -/
theorem finiteComponent_polynomial_moment [NeZero d] (hd : 3 ≤ d) {p : unitInterval}
    (hp : criticalProbability d < (p : ℝ)) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∀ r : ℕ, ∀ x : Vertex d,
      Integrable (fun ω => ((finiteComponentVertices ω x).card : ℝ) ^ r)
          (latticeBondLaw d p) ∧
      (∫ ω, ((finiteComponentVertices ω x).card : ℝ) ^ r ∂latticeBondLaw d p) ≤
        ((d * r).factorial : ℝ) / a ^ (d * r) * C := by
  obtain ⟨a, C, ha, hC, hmoment⟩ := finiteComponent_exp_root_moment hd hp
  refine ⟨a, C, ha, hC, fun r x => ?_⟩
  obtain ⟨hExp, hExpBound⟩ := hmoment x
  let K : ℝ := ((d * r).factorial : ℝ) / a ^ (d * r)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hBound (ω : Configuration d) :
      ((finiteComponentVertices ω x).card : ℝ) ^ r ≤
        K * Real.exp (a * ((finiteComponentVertices ω x).card : ℝ) ^ (d : ℝ)⁻¹) :=
    pow_le_factorial_mul_exp_root ha (Nat.cast_nonneg _) (NeZero.ne d) r
  have hMaj : Integrable
      (fun ω => K * Real.exp (a * ((finiteComponentVertices ω x).card : ℝ) ^ (d : ℝ)⁻¹))
      (latticeBondLaw d p) := hExp.const_mul K
  have hInt : Integrable (fun ω => ((finiteComponentVertices ω x).card : ℝ) ^ r)
      (latticeBondLaw d p) := by
    refine hMaj.mono' (((measurable_from_nat (f := fun n : ℕ => (n : ℝ) ^ r)).comp
      (measurable_finiteComponent_size x)).aestronglyMeasurable) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _)]
    exact hBound ω
  refine ⟨hInt, ?_⟩
  calc
    _ ≤ ∫ ω, K * Real.exp (a * ((finiteComponentVertices ω x).card : ℝ) ^ (d : ℝ)⁻¹)
        ∂latticeBondLaw d p := integral_mono hInt hMaj hBound
    _ = K * ∫ ω, Real.exp (a * ((finiteComponentVertices ω x).card : ℝ) ^ (d : ℝ)⁻¹)
        ∂latticeBondLaw d p := integral_const_mul _ _
    _ ≤ K * C := mul_le_mul_of_nonneg_left hExpBound hK

/-- Single-bond influences on the triadic infinite-cluster count have uniform factorial moment
bounds. -/
theorem density_influence_polynomial_moment [NeZero d] (hd : 3 ≤ d) {p : unitInterval}
    (hp : criticalProbability d < (p : ℝ)) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∀ (m : ℕ) (k : Vertex d) (e : Bond d) (r : ℕ),
      1 ≤ r →
      Integrable (fun q : Configuration d × Configuration d =>
        |(infiniteClusterCount (triadicCube d m k) q.1 : ℝ) -
          (infiniteClusterCount (triadicCube d m k) (resampleBond q.1 q.2 e) : ℝ)| ^ r)
        ((latticeBondLaw d p).prod (latticeBondLaw d p)) ∧
      (∫ q : Configuration d × Configuration d,
        |(infiniteClusterCount (triadicCube d m k) q.1 : ℝ) -
          (infiniteClusterCount (triadicCube d m k) (resampleBond q.1 q.2 e) : ℝ)| ^ r
        ∂((latticeBondLaw d p).prod (latticeBondLaw d p))) ≤
          (4 : ℝ) ^ (r + 1) * (((d * r).factorial : ℝ) / a ^ (d * r)) * C := by
  classical
  obtain ⟨a, C, ha, hC, hmoment⟩ := finiteComponent_polynomial_moment hd hp
  refine ⟨a, C, ha, hC, fun m k e r hr => ?_⟩
  refine ⟨integrable_count_influence_pow p m k e r, ?_⟩
  let μ := latticeBondLaw d p
  let ν := μ.prod μ
  let S : Finset (Vertex d × Fin 2) := e.val.toFinset ×ˢ Finset.univ
  let F (i : Vertex d × Fin 2) (q : Configuration d × Configuration d) : ℝ :=
    if i.2 = 0 then (finiteComponentVertices q.1 i.1).card
    else (finiteComponentVertices (resampleBond q.1 q.2 e) i.1).card
  let K : ℝ := ((d * r).factorial : ℝ) / a ^ (d * r)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hEpos : 0 < e.val.toFinset.card := by
    rw [Sym2.card_toFinset]
    split_ifs <;> omega
  have hEmax : e.val.toFinset.card ≤ 2 := by
    rw [Sym2.card_toFinset]
    split_ifs <;> omega
  have hSpos : 0 < S.card := by
    dsimp [S]
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    omega
  have hSmax : S.card ≤ 4 := by
    dsimp [S]
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    omega
  have hS : S.Nonempty := Finset.card_pos.mp hSpos
  have hFnonneg (i : Vertex d × Fin 2) (q : Configuration d × Configuration d) :
      0 ≤ F i q := by dsimp [F]; split_ifs <;> positivity
  have hFint (i : Vertex d × Fin 2) : Integrable (fun q => F i q ^ r) ν := by
    have hbase := (hmoment r i.1).1
    by_cases hi : i.2 = 0
    · have hP : MeasurePreserving (fun q : Configuration d × Configuration d => q.1) ν μ :=
        measurePreserving_fst
      simpa only [F, hi, if_pos, Function.comp_def] using hP.integrable_comp_of_integrable hbase
    · have hP : MeasurePreserving (fun q : Configuration d × Configuration d =>
          resampleBond q.1 q.2 e) ν μ := measurePreserving_resampleBond d p e
      simpa only [F, hi, if_false, Function.comp_def] using
        hP.integrable_comp_of_integrable hbase
  have hFbound (i : Vertex d × Fin 2) : (∫ q, F i q ^ r ∂ν) ≤ K * C := by
    have hbase := (hmoment r i.1).1
    have hmap (T : Configuration d × Configuration d → Configuration d)
        (hP : MeasurePreserving T ν μ) :
        (∫ q, ((finiteComponentVertices (T q) i.1).card : ℝ) ^ r ∂ν) =
          ∫ ω, ((finiteComponentVertices ω i.1).card : ℝ) ^ r ∂μ := by
      have hm : AEStronglyMeasurable
          (fun ω : Configuration d => ((finiteComponentVertices ω i.1).card : ℝ) ^ r)
          (Measure.map T ν) := by rw [hP.map_eq]; exact hbase.aestronglyMeasurable
      have heq := integral_map hP.measurable.aemeasurable hm
      rw [hP.map_eq] at heq
      exact heq.symm
    by_cases hi : i.2 = 0
    · simpa only [F, hi, if_pos] using
        (hmap (fun q => q.1) measurePreserving_fst).le.trans (hmoment r i.1).2
    · simpa only [F, hi, if_false] using
        (hmap (fun q => resampleBond q.1 q.2 e) (measurePreserving_resampleBond d p e)).le.trans
          (hmoment r i.1).2
  have hpoint (q : Configuration d × Configuration d) :
      |(infiniteClusterCount (triadicCube d m k) q.1 : ℝ) -
        (infiniteClusterCount (triadicCube d m k) (resampleBond q.1 q.2 e) : ℝ)| ≤
          ∑ i ∈ S, F i q := by
    have h := abs_infiniteClusterCount_resampleBond_le m k q.1 q.2 e
    simpa only [S, F, Finset.sum_product, Fin.sum_univ_two, Fin.isValue, ↓reduceIte,
      zero_ne_one, one_ne_zero] using h
  have hpointPow (q : Configuration d × Configuration d) :
      |(infiniteClusterCount (triadicCube d m k) q.1 : ℝ) -
        (infiniteClusterCount (triadicCube d m k) (resampleBond q.1 q.2 e) : ℝ)| ^ r ≤
          (4 : ℝ) ^ r * ∑ i ∈ S, F i q ^ r := by
    calc
      _ ≤ (∑ i ∈ S, F i q) ^ r := pow_le_pow_left₀ (abs_nonneg _) (hpoint q) r
      _ ≤ (S.card : ℝ) ^ r * ∑ i ∈ S, F i q ^ r :=
        sum_pow_le_card_pow_mul_sum S hS (fun i => F i q) (fun i _ => hFnonneg i q) r hr
      _ ≤ (4 : ℝ) ^ r * ∑ i ∈ S, F i q ^ r := by
        apply mul_le_mul_of_nonneg_right
        · exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hSmax) r
        · exact Finset.sum_nonneg fun i _ => pow_nonneg (hFnonneg i q) _
  have hsumInt : Integrable (fun q => ∑ i ∈ S, F i q ^ r) ν :=
    integrable_finsetSum S (fun i _ => hFint i)
  have hmajInt : Integrable (fun q => (4 : ℝ) ^ r * ∑ i ∈ S, F i q ^ r) ν :=
    hsumInt.const_mul _
  have hsumBound : (∑ i ∈ S, ∫ q, F i q ^ r ∂ν) ≤ (S.card : ℝ) * (K * C) := by
    calc
      _ ≤ ∑ _i ∈ S, K * C := Finset.sum_le_sum fun i _ => hFbound i
      _ = _ := by simp
  have hIC : 0 ≤ K * C := mul_nonneg hK hC.le
  calc
    _ ≤ ∫ q, (4 : ℝ) ^ r * ∑ i ∈ S, F i q ^ r ∂ν :=
      integral_mono (integrable_count_influence_pow p m k e r) hmajInt hpointPow
    _ = (4 : ℝ) ^ r * ∑ i ∈ S, ∫ q, F i q ^ r ∂ν := by
      rw [integral_const_mul, integral_finsetSum S (fun i _ => hFint i)]
    _ ≤ (4 : ℝ) ^ r * ((S.card : ℝ) * (K * C)) :=
      mul_le_mul_of_nonneg_left hsumBound (by positivity)
    _ ≤ (4 : ℝ) ^ r * (4 * (K * C)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hSmax) hIC) (by positivity)
    _ = _ := by dsimp [K]; rw [pow_succ]; ring

end Rigidity.Proofs.S2
