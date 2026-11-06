import MixedKernelConstructionC3SupportV015
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

section C4NativeCarleman
open MeasureTheory
open scoped ContDiff
open EnergyBridge ConnectionError MetricOperator MetricVolume

/-- T7a: the native classical divergence operator is literally the generic `Lop` of its
entries. -/
theorem divCoeffGrad_eq_Lop (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (u : R3 → ℝ) (x : R3) :
    divCoeffGrad A u x = OAI.AnisotropicCalderon.Lop (fun i k z => A z i k) u x := rfl

/-- T7: strict-weight Carleman estimate for the LITERAL native first operator
`coordinateFluxDivergence (metricDivergenceFlux (g1(lam ·)) w)`, unchanged phase `ϑ`,
Euclidean volume, constants chosen before `τ` and `w`. Hypotheses: signed-`m` coordinate strict
pseudo-convexity of `ϑ` for the native principal coefficient on the compact `K`. -/
theorem strict_weight_carleman_native_first (S : KnownSideSourceData) (lam : ℝ)
    {ϑ : R3 → ℝ} (hϑ : ContDiff ℝ ∞ ϑ) {K : Set R3} (hK : IsCompact K) (m : ℝ)
    (htan : ∀ x ∈ K, ∀ ξ : Fin 3 → ℝ, ξ ≠ 0 →
      ∑ j, StrictWeightCarleman.phaseField (fun i k z => dilatedFirstPrincipal S lam z i k)
        ϑ j x * ξ j = 0 →
      0 < OAI.AnisotropicCalderon.Mgrad (fun i k z => dilatedFirstPrincipal S lam z i k)
          (StrictWeightCarleman.phaseField (fun i k z => dilatedFirstPrincipal S lam z i k) ϑ)
          x ξ +
        4 * m * OAI.AnisotropicCalderon.quad (fun i k z => dilatedFirstPrincipal S lam z i k)
          x ξ)
    (hnor : ∀ x ∈ K, 0 < 2 * ∑ j,
      StrictWeightCarleman.phaseField (fun i k z => dilatedFirstPrincipal S lam z i k) ϑ j x *
        OAI.AnisotropicCalderon.pd j
          (StrictWeightCarleman.phaseNorm (fun i k z => dilatedFirstPrincipal S lam z i k) ϑ) x -
      4 * m * StrictWeightCarleman.phaseNorm (fun i k z => dilatedFirstPrincipal S lam z i k)
        ϑ x) :
    ∃ C τ0 : ℝ, 0 < C ∧ 1 ≤ τ0 ∧ ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ, ContDiff ℝ ∞ w →
      HasCompactSupport w → tsupport w ⊆ K →
      τ * (∫ x, ∑ i, OAI.AnisotropicCalderon.pd i (fun y => Real.exp (τ * ϑ y) * w y) x ^ 2) +
        τ ^ 3 * (∫ x, (Real.exp (τ * ϑ x) * w x) ^ 2) ≤
        C * ∫ x, Real.exp (2 * (τ * ϑ x)) *
          coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) w) x ^ 2 := by
  have ha : ∀ i k, ContDiff ℝ ∞ (fun z => dilatedFirstPrincipal S lam z i k) := fun i k =>
    (contDiff_principalCoefficient_entry S.g1 S.g1_admissible i k).comp
      (contDiff_id.const_smul lam)
  have hsymm : ∀ i k, (fun z => dilatedFirstPrincipal S lam z i k) =
      (fun z => dilatedFirstPrincipal S lam z k i) := fun i k => funext fun z => by
    have h := (principalCoefficient_posDef S.g1 S.g1_admissible (lam • z)).isHermitian.apply k i
    show principalCoefficient S.g1 (lam • z) i k = principalCoefficient S.g1 (lam • z) k i
    simpa using h
  obtain ⟨C, τ0, hC, hτ0, hest⟩ :=
    StrictWeightCarleman.strict_weight_carleman_of_coordinate_strictness ha hsymm hϑ hK m
      htan hnor
  refine ⟨C, τ0, hC, hτ0, fun τ hτ w hw hwc hKw => ?_⟩
  have h := hest τ hτ w hw hwc hKw
  have hop : ∀ x, coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) w) x =
      OAI.AnisotropicCalderon.Lop (fun i k z => dilatedFirstPrincipal S lam z i k) w x :=
    fun x => by rw [coordinateFluxDivergence_eq_divCoeffGrad]; rfl
  simp only [hop]
  exact h

/-- J4-first: the T9 point criterion for the INVERSE metric `(g1(lam ·))⁻¹` at `p` (NOT for the
principal matrix) yields, through the exact J3 transport with `ρ = vol(g1(lam ·)) > 0` and T9,
a closed ball and constants chosen before `τ`, `w` for the LITERAL first native operator. -/
theorem local_strict_weight_carleman_native_first (S : KnownSideSourceData) (lam : ℝ)
    {ϑ : R3 → ℝ} (hϑ : ContDiff ℝ ∞ ϑ) (p : R3)
    (hN : 0 < StrictWeightCarleman.phaseNorm (fun i k z => (S.g1 (lam • z))⁻¹ i k) ϑ p)
    (hstrict : ∀ ξ : Fin 3 → ℝ, ξ ≠ 0 →
      ∑ j, StrictWeightCarleman.phaseField (fun i k z => (S.g1 (lam • z))⁻¹ i k) ϑ j p * ξ j = 0 →
      0 < OAI.AnisotropicCalderon.Mgrad (fun i k z => (S.g1 (lam • z))⁻¹ i k)
          (StrictWeightCarleman.phaseField (fun i k z => (S.g1 (lam • z))⁻¹ i k) ϑ) p ξ +
        4 * ((∑ j, StrictWeightCarleman.phaseField (fun i k z => (S.g1 (lam • z))⁻¹ i k) ϑ j p *
          OAI.AnisotropicCalderon.pd j
            (StrictWeightCarleman.phaseNorm (fun i k z => (S.g1 (lam • z))⁻¹ i k) ϑ) p) /
          (2 * StrictWeightCarleman.phaseNorm (fun i k z => (S.g1 (lam • z))⁻¹ i k) ϑ p)) *
          OAI.AnisotropicCalderon.quad (fun i k z => (S.g1 (lam • z))⁻¹ i k) p ξ) :
    ∃ r C τ0 : ℝ, 0 < r ∧ 0 < C ∧ 1 ≤ τ0 ∧ ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ,
      ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ Metric.closedBall p r →
      τ * (∫ x, ∑ i, OAI.AnisotropicCalderon.pd i (fun y => Real.exp (τ * ϑ y) * w y) x ^ 2) +
        τ ^ 3 * (∫ x, (Real.exp (τ * ϑ x) * w x) ^ 2) ≤
        C * ∫ x, Real.exp (2 * (τ * ϑ x)) *
          coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) w) x ^ 2 := by
  have hinv : ∀ i k, ContDiff ℝ ∞ (fun z => (S.g1 (lam • z))⁻¹ i k) := fun i k =>
    (contDiff_metric_inverse_entry S.g1 S.g1_admissible i k).comp (contDiff_id.const_smul lam)
  have hρs : ContDiff ℝ ∞ (fun z => vol S.g1 (lam • z)) :=
    (contDiff_vol S.g1 S.g1_admissible).comp (contDiff_id.const_smul lam)
  have hρp : 0 < vol S.g1 (lam • p) :=
    Real.sqrt_pos.mpr (S.g1_admissible.posDef (lam • p)).det_pos
  obtain ⟨hN', hst'⟩ := StrictWeightCarleman.point_strictness_smul
    (b := fun i k z => dilatedFirstPrincipal S lam z i k) (ρ := fun z => vol S.g1 (lam • z))
    (a := fun i k z => (S.g1 (lam • z))⁻¹ i k) (fun i k z => rfl) hρs hinv hϑ p hρp hN hstrict
  have ha : ∀ i k, ContDiff ℝ ∞ (fun z => dilatedFirstPrincipal S lam z i k) := fun i k =>
    (contDiff_principalCoefficient_entry S.g1 S.g1_admissible i k).comp
      (contDiff_id.const_smul lam)
  have hsymm : ∀ i k, (fun z => dilatedFirstPrincipal S lam z i k) =
      (fun z => dilatedFirstPrincipal S lam z k i) := fun i k => funext fun z => by
    have h := (principalCoefficient_posDef S.g1 S.g1_admissible (lam • z)).isHermitian.apply k i
    show principalCoefficient S.g1 (lam • z) i k = principalCoefficient S.g1 (lam • z) k i
    simpa using h
  obtain ⟨_m, r, C, τ0, hr, hC, hτ0, hest⟩ :=
    StrictWeightCarleman.local_strict_weight_carleman_of_point_strictness ha hsymm hϑ p hN' hst'
  refine ⟨r, C, τ0, hr, hC, hτ0, fun τ hτ w hw hwc hKw => ?_⟩
  have h := hest τ hτ w hw hwc hKw
  have hop : ∀ x, coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) w) x =
      OAI.AnisotropicCalderon.Lop (fun i k z => dilatedFirstPrincipal S lam z i k) w x :=
    fun x => by rw [coordinateFluxDivergence_eq_divCoeffGrad]; rfl
  simp only [hop]
  exact h

end C4NativeCarleman

section C4NativeCarlemanSecond
open MeasureTheory
open scoped ContDiff
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
open ConformalDepth

/-- The positive smooth factor of the literal normalized second operator over `Lop`. -/
def secondOperatorFactor (S : KnownSideSourceData) (L lam : ℝ) (x : R3) : ℝ :=
  normalizedSecondLaplacianScalarJoint S.g1 S.g2 L (lam, x) * (vol (dilatedMetric S.g2 lam) x)⁻¹

theorem dilatedSecond_vol_pos (S : KnownSideSourceData) (lam : ℝ) (x : R3) :
    0 < vol (dilatedMetric S.g2 lam) x :=
  Real.sqrt_pos.mpr (dilatedMetric_posDef S.g2 S.g2_admissible lam x).det_pos

theorem secondOperatorFactor_pos (S : KnownSideSourceData) (L lam : ℝ) (x : R3) :
    0 < secondOperatorFactor S L lam x :=
  mul_pos (normalizedSecondLaplacianScalarJoint_pos S.g1 S.g2 S.g1_admissible S.g2_admissible L
    (lam, x)) (inv_pos.mpr (dilatedSecond_vol_pos S lam x))

theorem continuous_secondOperatorFactor (S : KnownSideSourceData) (L lam : ℝ) :
    Continuous (secondOperatorFactor S L lam) := by
  have htr : Continuous (fun x : R3 => referenceNormalizationTraceFamily S.g1 S.g2 L (lam, x)) :=
    (contDiff_referenceNormalizationTraceFamily S.g1 S.g2 S.g1_admissible S.g2_admissible
      L).continuous.comp (continuous_const.prodMk continuous_id)
  have hvol : Continuous (fun x : R3 => vol (dilatedMetric S.g2 lam) x) :=
    (continuous_vol S.g2 S.g2_admissible).comp (continuous_const_smul lam)
  have hs : Continuous (fun x : R3 => normalizedSecondLaplacianScalarJoint S.g1 S.g2 L (lam, x)) := by
    unfold normalizedSecondLaplacianScalarJoint
    exact continuous_const.div htr (fun x => (referenceNormalizationTraceFamily_pos S.g1 S.g2
      S.g1_admissible S.g2_admissible L (lam, x)).ne')
  unfold secondOperatorFactor
  exact hs.mul (hvol.inv₀ (fun x => (dilatedSecond_vol_pos S lam x).ne'))

/-- T8: strict-weight Carleman estimate for the LITERAL normalized second operator
`normalizedSecondLaplacian S.g1 S.g2 L lam`, unchanged phase, Euclidean volume, constants before
`τ` and `w`; the positive factor is removed only through its explicit compact lower bound. -/
theorem strict_weight_carleman_native_second (S : KnownSideSourceData) (L lam : ℝ)
    {ϑ : R3 → ℝ} (hϑ : ContDiff ℝ ∞ ϑ) {K : Set R3} (hK : IsCompact K) (m : ℝ)
    (htan : ∀ x ∈ K, ∀ ξ : Fin 3 → ℝ, ξ ≠ 0 →
      ∑ j, StrictWeightCarleman.phaseField
        (fun i k z => principalCoefficient (dilatedMetric S.g2 lam) z i k) ϑ j x * ξ j = 0 →
      0 < OAI.AnisotropicCalderon.Mgrad
          (fun i k z => principalCoefficient (dilatedMetric S.g2 lam) z i k)
          (StrictWeightCarleman.phaseField
            (fun i k z => principalCoefficient (dilatedMetric S.g2 lam) z i k) ϑ) x ξ +
        4 * m * OAI.AnisotropicCalderon.quad
          (fun i k z => principalCoefficient (dilatedMetric S.g2 lam) z i k) x ξ)
    (hnor : ∀ x ∈ K, 0 < 2 * ∑ j,
      StrictWeightCarleman.phaseField
        (fun i k z => principalCoefficient (dilatedMetric S.g2 lam) z i k) ϑ j x *
        OAI.AnisotropicCalderon.pd j (StrictWeightCarleman.phaseNorm
          (fun i k z => principalCoefficient (dilatedMetric S.g2 lam) z i k) ϑ) x -
      4 * m * StrictWeightCarleman.phaseNorm
        (fun i k z => principalCoefficient (dilatedMetric S.g2 lam) z i k) ϑ x) :
    ∃ C τ0 : ℝ, 0 < C ∧ 1 ≤ τ0 ∧ ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ, ContDiff ℝ ∞ w →
      HasCompactSupport w → tsupport w ⊆ K →
      τ * (∫ x, ∑ i, OAI.AnisotropicCalderon.pd i (fun y => Real.exp (τ * ϑ y) * w y) x ^ 2) +
        τ ^ 3 * (∫ x, (Real.exp (τ * ϑ x) * w x) ^ 2) ≤
        C * ∫ x, Real.exp (2 * (τ * ϑ x)) * normalizedSecondLaplacian S.g1 S.g2 L lam w x ^ 2 := by
  have ha : ∀ i k, ContDiff ℝ ∞
      (fun z => principalCoefficient (dilatedMetric S.g2 lam) z i k) :=
    contDiff_dilatedSecondPrincipal S lam
  have hsymm : ∀ i k, (fun z => principalCoefficient (dilatedMetric S.g2 lam) z i k) =
      (fun z => principalCoefficient (dilatedMetric S.g2 lam) z k i) := fun i k => funext fun z => by
    have h := (principalCoefficient_posDef S.g2 S.g2_admissible (lam • z)).isHermitian.apply k i
    show principalCoefficient S.g2 (lam • z) i k = principalCoefficient S.g2 (lam • z) k i
    simpa using h
  obtain ⟨C0, τ0, hC0, hτ0, hest⟩ :=
    StrictWeightCarleman.strict_weight_carleman_of_coordinate_strictness ha hsymm hϑ hK m
      htan hnor
  obtain ⟨β0, hβ0, hβ⟩ := StrictWeightCarleman.exists_pos_lower_on_compact hK
    (continuous_secondOperatorFactor S L lam).continuousOn
    (fun x _ => secondOperatorFactor_pos S L lam x)
  refine ⟨C0 / β0 ^ 2, τ0, div_pos hC0 (pow_pos hβ0 2), hτ0, fun τ hτ w hw hwc hKw => ?_⟩
  have h := hest τ hτ w hw hwc hKw
  set a2 : Fin 3 → Fin 3 → R3 → ℝ :=
    fun i k z => principalCoefficient (dilatedMetric S.g2 lam) z i k with ha2
  have hop : ∀ x, normalizedSecondLaplacian S.g1 S.g2 L lam w x =
      secondOperatorFactor S L lam x * OAI.AnisotropicCalderon.Lop a2 w x := fun x => by
    rw [Geometry.normalizedSecondLaplacian_eq_mul_fluxDiv, coordinateFluxDivergence_eq_divCoeffGrad]
    rfl
  have hLc : Continuous (OAI.AnisotropicCalderon.Lop a2 w) :=
    (StrictWeightCarleman.contDiff_Lop ha hw).continuous
  have hvan : ∀ x ∉ tsupport w, OAI.AnisotropicCalderon.Lop a2 w x = 0 := by
    intro x hx
    have h0 := OAI.AnisotropicCalderon.Sop_vanish (a := a2) (X := fun _ _ => 0)
      (q := fun _ => 0) (θ := fun _ => 0) ha (fun _ => contDiff_const) contDiff_const
      contDiff_const hw hx
    simpa [OAI.AnisotropicCalderon.Sop] using h0
  have hexpc : Continuous (fun x => Real.exp (2 * (τ * ϑ x))) := by
    have := hϑ.continuous
    fun_prop
  have hI1 : Integrable (fun x => Real.exp (2 * (τ * ϑ x)) *
      OAI.AnisotropicCalderon.Lop a2 w x ^ 2) :=
    OAI.AnisotropicCalderon.integrable_of_vanish (hexpc.mul (hLc.pow 2)) hwc
      (fun x hx => by simp [hvan x hx])
  have hI2 : Integrable (fun x => Real.exp (2 * (τ * ϑ x)) *
      normalizedSecondLaplacian S.g1 S.g2 L lam w x ^ 2) := by
    simp only [hop]
    exact OAI.AnisotropicCalderon.integrable_of_vanish
      (hexpc.mul (((continuous_secondOperatorFactor S L lam).mul hLc).pow 2)) hwc
      (fun x hx => by simp [hvan x hx])
  have hpt : ∀ x, Real.exp (2 * (τ * ϑ x)) * OAI.AnisotropicCalderon.Lop a2 w x ^ 2 ≤
      (β0 ^ 2)⁻¹ * (Real.exp (2 * (τ * ϑ x)) *
        normalizedSecondLaplacian S.g1 S.g2 L lam w x ^ 2) := by
    intro x
    rw [hop]
    have he : 0 ≤ Real.exp (2 * (τ * ϑ x)) := (Real.exp_pos _).le
    by_cases hx : x ∈ K
    · have hb := hβ x hx
      have hb2 : β0 ^ 2 ≤ secondOperatorFactor S L lam x ^ 2 := pow_le_pow_left₀ hβ0.le hb 2
      have key : β0 ^ 2 * OAI.AnisotropicCalderon.Lop a2 w x ^ 2 ≤
          (secondOperatorFactor S L lam x * OAI.AnisotropicCalderon.Lop a2 w x) ^ 2 := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right hb2 (sq_nonneg _)
      have hβ2 : 0 < β0 ^ 2 := pow_pos hβ0 2
      rw [inv_mul_eq_div, le_div_iff₀ hβ2]
      linarith [mul_le_mul_of_nonneg_left key he]
    · rw [hvan x (fun h => hx (hKw h))]
      simp
  have hmono := integral_mono hI1 (hI2.const_mul _) hpt
  rw [integral_const_mul] at hmono
  calc _ ≤ C0 * ∫ x, Real.exp (2 * (τ * ϑ x)) * OAI.AnisotropicCalderon.Lop a2 w x ^ 2 := h
    _ ≤ C0 * ((β0 ^ 2)⁻¹ * ∫ x, Real.exp (2 * (τ * ϑ x)) *
          normalizedSecondLaplacian S.g1 S.g2 L lam w x ^ 2) :=
        mul_le_mul_of_nonneg_left hmono hC0.le
    _ = C0 / β0 ^ 2 * ∫ x, Real.exp (2 * (τ * ϑ x)) *
          normalizedSecondLaplacian S.g1 S.g2 L lam w x ^ 2 := by ring

/-- T8 tail as a reusable step: a `Lop` estimate for the second principal coefficient on a
compact `K` becomes one for the LITERAL normalized second operator, with `β0 > 0` (compact lower
bound of the explicit positive factor on `K`) chosen before `τ` and `w`. -/
theorem native_second_of_Lop_estimate (S : KnownSideSourceData) (L lam : ℝ)
    {ϑ : R3 → ℝ} (hϑ : ContDiff ℝ ∞ ϑ) {K : Set R3} (hK : IsCompact K) {C0 τ0 : ℝ}
    (hC0 : 0 < C0)
    (hest : ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ, ContDiff ℝ ∞ w →
      HasCompactSupport w → tsupport w ⊆ K →
      τ * (∫ x, ∑ i, OAI.AnisotropicCalderon.pd i (fun y => Real.exp (τ * ϑ y) * w y) x ^ 2) +
        τ ^ 3 * (∫ x, (Real.exp (τ * ϑ x) * w x) ^ 2) ≤
        C0 * ∫ x, Real.exp (2 * (τ * ϑ x)) * OAI.AnisotropicCalderon.Lop
          (fun i k z => principalCoefficient (dilatedMetric S.g2 lam) z i k) w x ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ, ContDiff ℝ ∞ w →
      HasCompactSupport w → tsupport w ⊆ K →
      τ * (∫ x, ∑ i, OAI.AnisotropicCalderon.pd i (fun y => Real.exp (τ * ϑ y) * w y) x ^ 2) +
        τ ^ 3 * (∫ x, (Real.exp (τ * ϑ x) * w x) ^ 2) ≤
        C * ∫ x, Real.exp (2 * (τ * ϑ x)) * normalizedSecondLaplacian S.g1 S.g2 L lam w x ^ 2 := by
  have ha : ∀ i k, ContDiff ℝ ∞
      (fun z => principalCoefficient (dilatedMetric S.g2 lam) z i k) :=
    contDiff_dilatedSecondPrincipal S lam
  obtain ⟨β0, hβ0, hβ⟩ := StrictWeightCarleman.exists_pos_lower_on_compact hK
    (continuous_secondOperatorFactor S L lam).continuousOn
    (fun x _ => secondOperatorFactor_pos S L lam x)
  refine ⟨C0 / β0 ^ 2, div_pos hC0 (pow_pos hβ0 2), fun τ hτ w hw hwc hKw => ?_⟩
  have h := hest τ hτ w hw hwc hKw
  set a2 : Fin 3 → Fin 3 → R3 → ℝ :=
    fun i k z => principalCoefficient (dilatedMetric S.g2 lam) z i k with ha2
  have hop : ∀ x, normalizedSecondLaplacian S.g1 S.g2 L lam w x =
      secondOperatorFactor S L lam x * OAI.AnisotropicCalderon.Lop a2 w x := fun x => by
    rw [Geometry.normalizedSecondLaplacian_eq_mul_fluxDiv, coordinateFluxDivergence_eq_divCoeffGrad]
    rfl
  have hLc : Continuous (OAI.AnisotropicCalderon.Lop a2 w) :=
    (StrictWeightCarleman.contDiff_Lop ha hw).continuous
  have hvan : ∀ x ∉ tsupport w, OAI.AnisotropicCalderon.Lop a2 w x = 0 := by
    intro x hx
    have h0 := OAI.AnisotropicCalderon.Sop_vanish (a := a2) (X := fun _ _ => 0)
      (q := fun _ => 0) (θ := fun _ => 0) ha (fun _ => contDiff_const) contDiff_const
      contDiff_const hw hx
    simpa [OAI.AnisotropicCalderon.Sop] using h0
  have hexpc : Continuous (fun x => Real.exp (2 * (τ * ϑ x))) := by
    have := hϑ.continuous
    fun_prop
  have hI1 : Integrable (fun x => Real.exp (2 * (τ * ϑ x)) *
      OAI.AnisotropicCalderon.Lop a2 w x ^ 2) :=
    OAI.AnisotropicCalderon.integrable_of_vanish (hexpc.mul (hLc.pow 2)) hwc
      (fun x hx => by simp [hvan x hx])
  have hI2 : Integrable (fun x => Real.exp (2 * (τ * ϑ x)) *
      normalizedSecondLaplacian S.g1 S.g2 L lam w x ^ 2) := by
    simp only [hop]
    exact OAI.AnisotropicCalderon.integrable_of_vanish
      (hexpc.mul (((continuous_secondOperatorFactor S L lam).mul hLc).pow 2)) hwc
      (fun x hx => by simp [hvan x hx])
  have hpt : ∀ x, Real.exp (2 * (τ * ϑ x)) * OAI.AnisotropicCalderon.Lop a2 w x ^ 2 ≤
      (β0 ^ 2)⁻¹ * (Real.exp (2 * (τ * ϑ x)) *
        normalizedSecondLaplacian S.g1 S.g2 L lam w x ^ 2) := by
    intro x
    rw [hop]
    have he : 0 ≤ Real.exp (2 * (τ * ϑ x)) := (Real.exp_pos _).le
    by_cases hx : x ∈ K
    · have hb := hβ x hx
      have hb2 : β0 ^ 2 ≤ secondOperatorFactor S L lam x ^ 2 := pow_le_pow_left₀ hβ0.le hb 2
      have key : β0 ^ 2 * OAI.AnisotropicCalderon.Lop a2 w x ^ 2 ≤
          (secondOperatorFactor S L lam x * OAI.AnisotropicCalderon.Lop a2 w x) ^ 2 := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right hb2 (sq_nonneg _)
      have hβ2 : 0 < β0 ^ 2 := pow_pos hβ0 2
      rw [inv_mul_eq_div, le_div_iff₀ hβ2]
      linarith [mul_le_mul_of_nonneg_left key he]
    · rw [hvan x (fun h => hx (hKw h))]
      simp
  have hmono := integral_mono hI1 (hI2.const_mul _) hpt
  rw [integral_const_mul] at hmono
  calc _ ≤ C0 * ∫ x, Real.exp (2 * (τ * ϑ x)) * OAI.AnisotropicCalderon.Lop a2 w x ^ 2 := h
    _ ≤ C0 * ((β0 ^ 2)⁻¹ * ∫ x, Real.exp (2 * (τ * ϑ x)) *
          normalizedSecondLaplacian S.g1 S.g2 L lam w x ^ 2) :=
        mul_le_mul_of_nonneg_left hmono hC0.le
    _ = C0 / β0 ^ 2 * ∫ x, Real.exp (2 * (τ * ϑ x)) *
          normalizedSecondLaplacian S.g1 S.g2 L lam w x ^ 2 := by ring

/-- J4-second: the T9 point criterion for the INVERSE dilated second metric at `p` yields, via the
exact J3 transport (`ρ = vol > 0`), T9 and the compact factor bound on T9's ball, a strict-weight
Carleman estimate for the LITERAL normalized second operator; constants before `τ`, `w`. -/
theorem local_strict_weight_carleman_native_second (S : KnownSideSourceData) (L lam : ℝ)
    {ϑ : R3 → ℝ} (hϑ : ContDiff ℝ ∞ ϑ) (p : R3)
    (hN : 0 < StrictWeightCarleman.phaseNorm
      (fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k) ϑ p)
    (hstrict : ∀ ξ : Fin 3 → ℝ, ξ ≠ 0 →
      ∑ j, StrictWeightCarleman.phaseField
        (fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k) ϑ j p * ξ j = 0 →
      0 < OAI.AnisotropicCalderon.Mgrad (fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k)
          (StrictWeightCarleman.phaseField
            (fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k) ϑ) p ξ +
        4 * ((∑ j, StrictWeightCarleman.phaseField
              (fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k) ϑ j p *
            OAI.AnisotropicCalderon.pd j (StrictWeightCarleman.phaseNorm
              (fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k) ϑ) p) /
          (2 * StrictWeightCarleman.phaseNorm
            (fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k) ϑ p)) *
          OAI.AnisotropicCalderon.quad (fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k) p ξ) :
    ∃ r C τ0 : ℝ, 0 < r ∧ 0 < C ∧ 1 ≤ τ0 ∧ ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ,
      ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ Metric.closedBall p r →
      τ * (∫ x, ∑ i, OAI.AnisotropicCalderon.pd i (fun y => Real.exp (τ * ϑ y) * w y) x ^ 2) +
        τ ^ 3 * (∫ x, (Real.exp (τ * ϑ x) * w x) ^ 2) ≤
        C * ∫ x, Real.exp (2 * (τ * ϑ x)) * normalizedSecondLaplacian S.g1 S.g2 L lam w x ^ 2 := by
  have hinv : ∀ i k, ContDiff ℝ ∞ (fun z => (dilatedMetric S.g2 lam z)⁻¹ i k) := fun i k =>
    (contDiff_metric_inverse_entry S.g2 S.g2_admissible i k).comp (contDiff_id.const_smul lam)
  have hρs : ContDiff ℝ ∞ (fun z => vol (dilatedMetric S.g2 lam) z) :=
    (contDiff_vol S.g2 S.g2_admissible).comp (contDiff_id.const_smul lam)
  obtain ⟨hN', hst'⟩ := StrictWeightCarleman.point_strictness_smul
    (b := fun i k z => principalCoefficient (dilatedMetric S.g2 lam) z i k)
    (ρ := fun z => vol (dilatedMetric S.g2 lam) z)
    (a := fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k) (fun i k z => rfl) hρs hinv hϑ p
    (dilatedSecond_vol_pos S lam p) hN hstrict
  have ha : ∀ i k, ContDiff ℝ ∞
      (fun z => principalCoefficient (dilatedMetric S.g2 lam) z i k) :=
    contDiff_dilatedSecondPrincipal S lam
  have hsymm : ∀ i k, (fun z => principalCoefficient (dilatedMetric S.g2 lam) z i k) =
      (fun z => principalCoefficient (dilatedMetric S.g2 lam) z k i) := fun i k => funext fun z => by
    have h := (principalCoefficient_posDef S.g2 S.g2_admissible (lam • z)).isHermitian.apply k i
    show principalCoefficient S.g2 (lam • z) i k = principalCoefficient S.g2 (lam • z) k i
    simpa using h
  obtain ⟨_m, r, C0, τ0, hr, hC0, hτ0, hest⟩ :=
    StrictWeightCarleman.local_strict_weight_carleman_of_point_strictness ha hsymm hϑ p hN' hst'
  obtain ⟨C, hC, hfin⟩ := native_second_of_Lop_estimate S L lam hϑ
    (isCompact_closedBall p r) hC0 hest
  exact ⟨r, C, τ0, hr, hC, hτ0, hfin⟩

/-- J2∘J4-first: source metric strictness of the coordinate Christoffel Hessian of the SAME
dilated metric `g1(lam ·)` at `p` (unit form), with `∇ϑ(p) ≠ 0`, gives the local strict-weight
Carleman estimate for the LITERAL first operator. All matrix premises come from admissibility. -/
theorem local_strict_weight_carleman_native_first_of_metric_strictness (S : KnownSideSourceData)
    (lam : ℝ) {ϑ : R3 → ℝ} (hϑ : ContDiff ℝ ∞ ϑ) (p : R3)
    (hdϑ : (fun k => OAI.AnisotropicCalderon.pd k ϑ p) ≠ 0)
    (hsrc : ∀ v : Fin 3 → ℝ, ∑ i, ∑ j, S.g1 (lam • p) i j * v i * v j = 1 →
      ∑ i, ∑ j, S.g1 (lam • p) i j *
        StrictWeightCarleman.phaseField (fun i k z => (S.g1 (lam • z))⁻¹ i k) ϑ i p * v j = 0 →
      0 < (∑ i, ∑ j, StrictWeightCarleman.christoffelHess (fun i j z => S.g1 (lam • z) i j)
            (fun i k z => (S.g1 (lam • z))⁻¹ i k) ϑ p i j *
          StrictWeightCarleman.phaseField (fun i k z => (S.g1 (lam • z))⁻¹ i k) ϑ i p *
          StrictWeightCarleman.phaseField (fun i k z => (S.g1 (lam • z))⁻¹ i k) ϑ j p) /
        StrictWeightCarleman.phaseNorm (fun i k z => (S.g1 (lam • z))⁻¹ i k) ϑ p +
        ∑ i, ∑ j, StrictWeightCarleman.christoffelHess (fun i j z => S.g1 (lam • z) i j)
          (fun i k z => (S.g1 (lam • z))⁻¹ i k) ϑ p i j * v i * v j) :
    ∃ r C τ0 : ℝ, 0 < r ∧ 0 < C ∧ 1 ≤ τ0 ∧ ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ,
      ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ Metric.closedBall p r →
      τ * (∫ x, ∑ i, OAI.AnisotropicCalderon.pd i (fun y => Real.exp (τ * ϑ y) * w y) x ^ 2) +
        τ ^ 3 * (∫ x, (Real.exp (τ * ϑ x) * w x) ^ 2) ≤
        C * ∫ x, Real.exp (2 * (τ * ϑ x)) *
          coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) w) x ^ 2 := by
  have hinv : ∀ i k, ContDiff ℝ ∞ (fun z => (S.g1 (lam • z))⁻¹ i k) := fun i k =>
    (contDiff_metric_inverse_entry S.g1 S.g1_admissible i k).comp (contDiff_id.const_smul lam)
  have hsymmA : ∀ i k, (fun z => (S.g1 (lam • z))⁻¹ i k) = (fun z => (S.g1 (lam • z))⁻¹ k i) :=
    fun i k => funext fun z => by
      have h := (S.g1_admissible.posDef (lam • z)).inv.isHermitian.apply k i
      simpa using h
  have hg : ∀ i j, DifferentiableAt ℝ (fun y => S.g1 (lam • y) i j) p := fun i j =>
    (((S.g1_admissible.smooth i j).comp (contDiff_id.const_smul lam)).differentiable
      (by simp)) p
  have hpd := S.g1_admissible.posDef (lam • p)
  obtain ⟨hN, hcrit⟩ := StrictWeightCarleman.point_criterion_of_metric_strictness
    (A := fun i k z => (S.g1 (lam • z))⁻¹ i k) (G := fun i j z => S.g1 (lam • z) i j)
    hinv hϑ hsymmA p
    (fun r i j => fderiv_inverseMetric_entry_apply (fun y => S.g1 (lam • y)) p
      (EuclideanSpace.single r 1) hg hpd i j)
    (fun i k => by
      have hm := Matrix.mul_nonsing_inv (S.g1 (lam • p)) (isUnit_iff_ne_zero.mpr hpd.det_pos.ne')
      have := congrFun (congrFun hm i) k
      simpa [Matrix.mul_apply, Matrix.one_apply] using this)
    (fun v hv => by
      have := hpd.dotProduct_mulVec_pos hv
      convert this using 1
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]; ring)
    hdϑ hsrc
  exact local_strict_weight_carleman_native_first S lam hϑ p hN hcrit

/-- J2∘J4-second: the same for the LITERAL normalized second operator and the SAME dilated
second metric `dilatedMetric S.g2 lam`. -/
theorem local_strict_weight_carleman_native_second_of_metric_strictness
    (S : KnownSideSourceData) (L lam : ℝ) {ϑ : R3 → ℝ} (hϑ : ContDiff ℝ ∞ ϑ) (p : R3)
    (hdϑ : (fun k => OAI.AnisotropicCalderon.pd k ϑ p) ≠ 0)
    (hsrc : ∀ v : Fin 3 → ℝ, ∑ i, ∑ j, dilatedMetric S.g2 lam p i j * v i * v j = 1 →
      ∑ i, ∑ j, dilatedMetric S.g2 lam p i j * StrictWeightCarleman.phaseField
        (fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k) ϑ i p * v j = 0 →
      0 < (∑ i, ∑ j, StrictWeightCarleman.christoffelHess
            (fun i j z => dilatedMetric S.g2 lam z i j)
            (fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k) ϑ p i j *
          StrictWeightCarleman.phaseField (fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k) ϑ i p *
          StrictWeightCarleman.phaseField (fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k) ϑ j p) /
        StrictWeightCarleman.phaseNorm (fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k) ϑ p +
        ∑ i, ∑ j, StrictWeightCarleman.christoffelHess
          (fun i j z => dilatedMetric S.g2 lam z i j)
          (fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k) ϑ p i j * v i * v j) :
    ∃ r C τ0 : ℝ, 0 < r ∧ 0 < C ∧ 1 ≤ τ0 ∧ ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ,
      ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ Metric.closedBall p r →
      τ * (∫ x, ∑ i, OAI.AnisotropicCalderon.pd i (fun y => Real.exp (τ * ϑ y) * w y) x ^ 2) +
        τ ^ 3 * (∫ x, (Real.exp (τ * ϑ x) * w x) ^ 2) ≤
        C * ∫ x, Real.exp (2 * (τ * ϑ x)) * normalizedSecondLaplacian S.g1 S.g2 L lam w x ^ 2 := by
  have hinv : ∀ i k, ContDiff ℝ ∞ (fun z => (dilatedMetric S.g2 lam z)⁻¹ i k) := fun i k =>
    (contDiff_metric_inverse_entry S.g2 S.g2_admissible i k).comp (contDiff_id.const_smul lam)
  have hsymmA : ∀ i k, (fun z => (dilatedMetric S.g2 lam z)⁻¹ i k) =
      (fun z => (dilatedMetric S.g2 lam z)⁻¹ k i) :=
    fun i k => funext fun z => by
      have h := (dilatedMetric_posDef S.g2 S.g2_admissible lam z).inv.isHermitian.apply k i
      simpa using h
  have hg : ∀ i j, DifferentiableAt ℝ (fun y => dilatedMetric S.g2 lam y i j) p := fun i j =>
    ((dilatedMetric_smooth_entries S.g2 S.g2_admissible lam i j).differentiable (by simp)) p
  have hpd := dilatedMetric_posDef S.g2 S.g2_admissible lam p
  obtain ⟨hN, hcrit⟩ := StrictWeightCarleman.point_criterion_of_metric_strictness
    (A := fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k)
    (G := fun i j z => dilatedMetric S.g2 lam z i j)
    hinv hϑ hsymmA p
    (fun r i j => fderiv_inverseMetric_entry_apply (dilatedMetric S.g2 lam) p
      (EuclideanSpace.single r 1) hg hpd i j)
    (fun i k => by
      have hm := Matrix.mul_nonsing_inv (dilatedMetric S.g2 lam p)
        (isUnit_iff_ne_zero.mpr hpd.det_pos.ne')
      have := congrFun (congrFun hm i) k
      simpa [Matrix.mul_apply, Matrix.one_apply] using this)
    (fun v hv => by
      have := hpd.dotProduct_mulVec_pos hv
      convert this using 1
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]; ring)
    hdϑ hsrc
  exact local_strict_weight_carleman_native_second S L lam hϑ p hN hcrit

/-- J0: the supplied `MetricVolume.metricHessianMatrix` entries ARE the coordinate Christoffel
Hessian (smooth entries, positive definite everywhere, smooth phase). -/
theorem metricHessianMatrix_eq_christoffelHess (g : MatrixField)
    (hs : ∀ i j, ContDiff ℝ ∞ (fun y => g y i j)) (hp : ∀ y, (g y).PosDef)
    {ϑ : R3 → ℝ} (hϑ : ContDiff ℝ ∞ ϑ) (x : R3) (i j : Fin 3) :
    metricHessianMatrix g ϑ x i j = StrictWeightCarleman.christoffelHess
      (fun i j y => g y i j) (fun i k y => (g y)⁻¹ i k) ϑ x i j := by
  have hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x := fun i j =>
    ((hs i j).differentiable (by simp)) x
  have hgs : ∀ a b, (fun y => g y a b) = (fun y => g y b a) := fun a b => funext fun y => by
    have h := (hp y).isHermitian.apply b a
    simpa using h
  have hf : DifferentiableAt ℝ (fderiv ℝ ϑ) x :=
    ((hϑ.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x
  have hH : metricHessianMatrix g ϑ x i j =
      fderiv ℝ (fderiv ℝ ϑ) x (coordinateVector i) (coordinateVector j) -
        ∑ k : Fin 3, metricChristoffel g x i j k * fderiv ℝ ϑ x (coordinateVector k) := by
    show RadiusProfile.coordinateHessian ϑ
      (fun X Y => ConnectionError.coordinateConnectionField
        (ConnectionError.inverseMetricField (MetricOperator.metricOperatorField g))
        (MetricOperator.metricOperatorField g) x X Y) x (coordinateVector i)
        (coordinateVector j) = _
    unfold RadiusProfile.coordinateHessian
    rw [covector_coordinate_sum (fderiv ℝ ϑ x)]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    unfold metricChristoffel
    simp only [ConnectionError.coordinateConnectionField_apply,
      inverseMetricField_eq_matrix_inverse_of_posDef g x (hp x)]
  have h2 : OAI.AnisotropicCalderon.pd i (OAI.AnisotropicCalderon.pd j ϑ) x =
      fderiv ℝ (fderiv ℝ ϑ) x (coordinateVector i) (coordinateVector j) :=
    derivative_covector_entry ϑ x (coordinateVector i) hf j
  rw [hH]
  unfold StrictWeightCarleman.christoffelHess
  rw [h2]
  simp only [metricChristoffel_eq g x hg]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [OAI.AnisotropicCalderon.pd, coordinateVector]
  rw [hgs c j, hgs c i, hgs j i]
  ring

/-- J0∘J2∘J4-first: strictness of the SUPPLIED metric Hessian of the SAME dilated first metric. -/
theorem local_strict_weight_carleman_native_first_of_metricHessian (S : KnownSideSourceData)
    (lam : ℝ) {ϑ : R3 → ℝ} (hϑ : ContDiff ℝ ∞ ϑ) (p : R3)
    (hdϑ : (fun k => OAI.AnisotropicCalderon.pd k ϑ p) ≠ 0)
    (hsrc : ∀ v : Fin 3 → ℝ, ∑ i, ∑ j, S.g1 (lam • p) i j * v i * v j = 1 →
      ∑ i, ∑ j, S.g1 (lam • p) i j *
        StrictWeightCarleman.phaseField (fun i k z => (S.g1 (lam • z))⁻¹ i k) ϑ i p * v j = 0 →
      0 < (∑ i, ∑ j, metricHessianMatrix (dilatedMetric S.g1 lam) ϑ p i j *
          StrictWeightCarleman.phaseField (fun i k z => (S.g1 (lam • z))⁻¹ i k) ϑ i p *
          StrictWeightCarleman.phaseField (fun i k z => (S.g1 (lam • z))⁻¹ i k) ϑ j p) /
        StrictWeightCarleman.phaseNorm (fun i k z => (S.g1 (lam • z))⁻¹ i k) ϑ p +
        ∑ i, ∑ j, metricHessianMatrix (dilatedMetric S.g1 lam) ϑ p i j * v i * v j) :
    ∃ r C τ0 : ℝ, 0 < r ∧ 0 < C ∧ 1 ≤ τ0 ∧ ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ,
      ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ Metric.closedBall p r →
      τ * (∫ x, ∑ i, OAI.AnisotropicCalderon.pd i (fun y => Real.exp (τ * ϑ y) * w y) x ^ 2) +
        τ ^ 3 * (∫ x, (Real.exp (τ * ϑ x) * w x) ^ 2) ≤
        C * ∫ x, Real.exp (2 * (τ * ϑ x)) *
          coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) w) x ^ 2 := by
  have hJ0 : ∀ i j, StrictWeightCarleman.christoffelHess (fun i j z => S.g1 (lam • z) i j)
      (fun i k z => (S.g1 (lam • z))⁻¹ i k) ϑ p i j =
      metricHessianMatrix (dilatedMetric S.g1 lam) ϑ p i j := fun i j =>
    (metricHessianMatrix_eq_christoffelHess (dilatedMetric S.g1 lam)
      (dilatedMetric_smooth_entries S.g1 S.g1_admissible lam)
      (dilatedMetric_posDef S.g1 S.g1_admissible lam) hϑ p i j).symm
  exact local_strict_weight_carleman_native_first_of_metric_strictness S lam hϑ p hdϑ
    (fun v h1 h2 => by simp only [hJ0]; exact hsrc v h1 h2)

/-- J0∘J2∘J4-second: strictness of the SUPPLIED metric Hessian of the SAME dilated second
metric gives the local estimate for the LITERAL normalized second operator. -/
theorem local_strict_weight_carleman_native_second_of_metricHessian
    (S : KnownSideSourceData) (L lam : ℝ) {ϑ : R3 → ℝ} (hϑ : ContDiff ℝ ∞ ϑ) (p : R3)
    (hdϑ : (fun k => OAI.AnisotropicCalderon.pd k ϑ p) ≠ 0)
    (hsrc : ∀ v : Fin 3 → ℝ, ∑ i, ∑ j, dilatedMetric S.g2 lam p i j * v i * v j = 1 →
      ∑ i, ∑ j, dilatedMetric S.g2 lam p i j * StrictWeightCarleman.phaseField
        (fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k) ϑ i p * v j = 0 →
      0 < (∑ i, ∑ j, metricHessianMatrix (dilatedMetric S.g2 lam) ϑ p i j *
          StrictWeightCarleman.phaseField (fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k) ϑ i p *
          StrictWeightCarleman.phaseField (fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k) ϑ j p) /
        StrictWeightCarleman.phaseNorm (fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k) ϑ p +
        ∑ i, ∑ j, metricHessianMatrix (dilatedMetric S.g2 lam) ϑ p i j * v i * v j) :
    ∃ r C τ0 : ℝ, 0 < r ∧ 0 < C ∧ 1 ≤ τ0 ∧ ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ,
      ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ Metric.closedBall p r →
      τ * (∫ x, ∑ i, OAI.AnisotropicCalderon.pd i (fun y => Real.exp (τ * ϑ y) * w y) x ^ 2) +
        τ ^ 3 * (∫ x, (Real.exp (τ * ϑ x) * w x) ^ 2) ≤
        C * ∫ x, Real.exp (2 * (τ * ϑ x)) * normalizedSecondLaplacian S.g1 S.g2 L lam w x ^ 2 := by
  have hJ0 : ∀ i j, StrictWeightCarleman.christoffelHess
      (fun i j z => dilatedMetric S.g2 lam z i j)
      (fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k) ϑ p i j =
      metricHessianMatrix (dilatedMetric S.g2 lam) ϑ p i j := fun i j =>
    (metricHessianMatrix_eq_christoffelHess (dilatedMetric S.g2 lam)
      (dilatedMetric_smooth_entries S.g2 S.g2_admissible lam)
      (dilatedMetric_posDef S.g2 S.g2_admissible lam) hϑ p i j).symm
  exact local_strict_weight_carleman_native_second_of_metric_strictness S L lam hϑ p hdϑ
    (fun v h1 h2 => by simp only [hJ0]; exact hsrc v h1 h2)

end C4NativeCarlemanSecond

section C4LocalNativePhase

open Set Metric Filter MeasureTheory
open scoped ContDiff Topology
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
open ConformalDepth OAI.AnisotropicCalderon.MixedKernelConstructionTask.Geometry

/-- A locally smooth phase has a globally smooth representative on a ball about the point. -/
theorem exists_smooth_phase_eqOn_ball {ϑ : R3 → ℝ} {Ω : Set R3}
    (hΩ : IsOpen Ω) (hϑ : ContDiffOn ℝ ∞ ϑ Ω) (p : R3) (hp : p ∈ Ω) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball p ρ ⊆ Ω ∧ ∃ Θ : R3 → ℝ,
      ContDiff ℝ ∞ Θ ∧ Set.EqOn Θ ϑ (Metric.ball p ρ) := by
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.mp hΩ p hp
  set ρ : ℝ := ε / 4 with hρdef
  have hρ : 0 < ρ := by positivity
  let χ : ContDiffBump p := ⟨ρ, 2 * ρ, hρ, by linarith⟩
  set Θ : R3 → ℝ := fun y => χ y * ϑ y with hΘdef
  have hsub : tsupport Θ ⊆ Ω := by
    refine (tsupport_mul_subset_left (f := fun y => χ y) (g := ϑ)).trans ?_
    rw [χ.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by linarith : 2 * ρ < ε)).trans hεΩ
  have hΘΩ : ContDiffOn ℝ ∞ Θ Ω := (χ.contDiff (n := ⊤)).contDiffOn.mul hϑ
  have hΘ : ContDiff ℝ ∞ Θ := by
    refine contDiff_of_contDiffOn_union_of_isOpen hΘΩ (t := (tsupport Θ)ᶜ)
      ((contDiffOn_const (c := (0 : ℝ))).congr fun x hx => image_eq_zero_of_notMem_tsupport hx)
      ?_ hΩ (isClosed_tsupport Θ).isOpen_compl
    ext x; by_cases hx : x ∈ tsupport Θ
    · simp [hsub hx]
    · simp [hx]
  refine ⟨ρ, hρ, (Metric.ball_subset_ball (by linarith : ρ ≤ ε)).trans hεΩ, Θ, hΘ, ?_⟩
  intro y hy
  have h1 : χ y = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
  simp only [hΘdef, h1, one_mul]

/-- The actual metric Hessian depends only on the local germ of its scalar argument. -/
theorem metricHessianMatrix_congr_of_eventuallyEq (g : MatrixField) {ϑ Θ : R3 → ℝ}
    {p : R3} (h : Θ =ᶠ[nhds p] ϑ) (i j : Fin 3) :
    metricHessianMatrix g Θ p i j = metricHessianMatrix g ϑ p i j := by
  have h1 : fderiv ℝ Θ =ᶠ[nhds p] fderiv ℝ ϑ := h.fderiv
  simp only [metricHessianMatrix, RadiusProfile.coordinateHessian, h.fderiv_eq, h1.fderiv_eq]

/-- The literal first operator estimate for an unchanged locally smooth metric-strict phase. -/
theorem local_strict_weight_carleman_native_first_of_metricHessian_of_local_phase (S : KnownSideSourceData)
    (lam : ℝ) {ϑ : R3 → ℝ} {Ω : Set R3} (hΩ : IsOpen Ω)
    (hϑ : ContDiffOn ℝ ∞ ϑ Ω) (p : R3) (hp : p ∈ Ω)
    (hdϑ : (fun k => OAI.AnisotropicCalderon.pd k ϑ p) ≠ 0)
    (hsrc : ∀ v : Fin 3 → ℝ, ∑ i, ∑ j, S.g1 (lam • p) i j * v i * v j = 1 →
      ∑ i, ∑ j, S.g1 (lam • p) i j *
        StrictWeightCarleman.phaseField (fun i k z => (S.g1 (lam • z))⁻¹ i k) ϑ i p * v j = 0 →
      0 < (∑ i, ∑ j, metricHessianMatrix (dilatedMetric S.g1 lam) ϑ p i j *
          StrictWeightCarleman.phaseField (fun i k z => (S.g1 (lam • z))⁻¹ i k) ϑ i p *
          StrictWeightCarleman.phaseField (fun i k z => (S.g1 (lam • z))⁻¹ i k) ϑ j p) /
        StrictWeightCarleman.phaseNorm (fun i k z => (S.g1 (lam • z))⁻¹ i k) ϑ p +
        ∑ i, ∑ j, metricHessianMatrix (dilatedMetric S.g1 lam) ϑ p i j * v i * v j) :
    ∃ r C τ0 : ℝ, 0 < r ∧ 0 < C ∧ 1 ≤ τ0 ∧ Metric.closedBall p r ⊆ Ω ∧ ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ,
      ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ Metric.closedBall p r →
      τ * (∫ x, ∑ i, OAI.AnisotropicCalderon.pd i (fun y => Real.exp (τ * ϑ y) * w y) x ^ 2) +
        τ ^ 3 * (∫ x, (Real.exp (τ * ϑ x) * w x) ^ 2) ≤
        C * ∫ x, Real.exp (2 * (τ * ϑ x)) *
          coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) w) x ^ 2 := by
  obtain ⟨ρ, hρ, hbΩ, Θ, hΘ, hEq⟩ := exists_smooth_phase_eqOn_ball hΩ hϑ p hp
  have hpb : p ∈ Metric.ball p ρ := Metric.mem_ball_self hρ
  have hnear : Θ =ᶠ[nhds p] ϑ :=
    Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hpb) hEq
  have hpd : ∀ i, OAI.AnisotropicCalderon.pd i Θ p = OAI.AnisotropicCalderon.pd i ϑ p := by
    intro i
    unfold OAI.AnisotropicCalderon.pd
    rw [hnear.fderiv_eq]
  have hW : ∀ i, StrictWeightCarleman.phaseField (fun i k z => (S.g1 (lam • z))⁻¹ i k) Θ i p =
      StrictWeightCarleman.phaseField (fun i k z => (S.g1 (lam • z))⁻¹ i k) ϑ i p := by
    intro i
    simp only [StrictWeightCarleman.phaseField, hpd]
  have hN : StrictWeightCarleman.phaseNorm (fun i k z => (S.g1 (lam • z))⁻¹ i k) Θ p =
      StrictWeightCarleman.phaseNorm (fun i k z => (S.g1 (lam • z))⁻¹ i k) ϑ p := by
    simp only [StrictWeightCarleman.phaseNorm, hpd]
  have hH : ∀ i j, metricHessianMatrix (dilatedMetric S.g1 lam) Θ p i j =
      metricHessianMatrix (dilatedMetric S.g1 lam) ϑ p i j :=
    fun i j => metricHessianMatrix_congr_of_eventuallyEq _ hnear i j
  obtain ⟨r0, C, τ0, hr0, hC, hτ0, hest⟩ :=
    local_strict_weight_carleman_native_first_of_metricHessian S lam hΘ p
      (by simpa only [hpd] using hdϑ)
      (by
        intro v hunit horth
        have horth' := horth
        simp only [hW] at horth'
        simpa only [hH, hW, hN] using hsrc v hunit horth')
  set r : ℝ := min r0 (ρ / 2) with hrdef
  have hr : 0 < r := lt_min hr0 (half_pos hρ)
  have hrball : Metric.closedBall p r ⊆ Metric.ball p ρ :=
    (Metric.closedBall_subset_closedBall (min_le_right _ _)).trans
      (Metric.closedBall_subset_ball (half_lt_self hρ))
  refine ⟨r, C, τ0, hr, hC, hτ0, hrball.trans hbΩ, fun τ hτ w hw hwc hKw => ?_⟩
  have h := hest τ hτ w hw hwc
    (hKw.trans (Metric.closedBall_subset_closedBall (min_le_left _ _)))
  have hoff : ∀ y, y ∉ Metric.ball p ρ → y ∉ tsupport w :=
    fun y hy hyw => hy (hrball (hKw hyw))
  have hfun : (fun y => Real.exp (τ * Θ y) * w y) =
      (fun y => Real.exp (τ * ϑ y) * w y) := by
    funext y
    by_cases hy : y ∈ Metric.ball p ρ
    · rw [hEq hy]
    · simp [image_eq_zero_of_notMem_tsupport (hoff y hy)]
  have ha : ∀ i k, ContDiff ℝ ∞ (fun z => dilatedFirstPrincipal S lam z i k) := fun i k =>
    (contDiff_principalCoefficient_entry S.g1 S.g1_admissible i k).comp
      (contDiff_id.const_smul lam)
  have hvan : ∀ x ∉ tsupport w,
      coordinateFluxDivergence (metricDivergenceFlux (fun y => S.g1 (lam • y)) w) x = 0 := by
    intro x hx
    rw [coordinateFluxDivergence_eq_divCoeffGrad]
    have h0 := OAI.AnisotropicCalderon.Sop_vanish
      (a := fun i k z => dilatedFirstPrincipal S lam z i k) (X := fun _ _ => 0)
      (q := fun _ => 0) (θ := fun _ => 0) ha (fun _ => contDiff_const)
      contDiff_const contDiff_const hw hx
    change OAI.AnisotropicCalderon.Lop
      (fun i k z => dilatedFirstPrincipal S lam z i k) w x = 0
    simpa [OAI.AnisotropicCalderon.Sop] using h0
  have hres : ∀ x, Real.exp (2 * (τ * Θ x)) * (coordinateFluxDivergence (metricDivergenceFlux (fun y => S.g1 (lam • y)) w) x) ^ 2 =
      Real.exp (2 * (τ * ϑ x)) * (coordinateFluxDivergence (metricDivergenceFlux (fun y => S.g1 (lam • y)) w) x) ^ 2 := by
    intro x
    by_cases hx : x ∈ Metric.ball p ρ
    · rw [hEq hx]
    · simp [hvan x (hoff x hx)]
  have hmass : ∀ x, (Real.exp (τ * Θ x) * w x) ^ 2 =
      (Real.exp (τ * ϑ x) * w x) ^ 2 := fun x => by rw [congrFun hfun x]
  simp only [hfun, hmass, hres] at h
  exact h

/-- The literal second operator estimate for an unchanged locally smooth metric-strict phase. -/
theorem local_strict_weight_carleman_native_second_of_metricHessian_of_local_phase
    (S : KnownSideSourceData) (L lam : ℝ) {ϑ : R3 → ℝ} {Ω : Set R3} (hΩ : IsOpen Ω)
    (hϑ : ContDiffOn ℝ ∞ ϑ Ω) (p : R3) (hp : p ∈ Ω)
    (hdϑ : (fun k => OAI.AnisotropicCalderon.pd k ϑ p) ≠ 0)
    (hsrc : ∀ v : Fin 3 → ℝ, ∑ i, ∑ j, dilatedMetric S.g2 lam p i j * v i * v j = 1 →
      ∑ i, ∑ j, dilatedMetric S.g2 lam p i j * StrictWeightCarleman.phaseField
        (fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k) ϑ i p * v j = 0 →
      0 < (∑ i, ∑ j, metricHessianMatrix (dilatedMetric S.g2 lam) ϑ p i j *
          StrictWeightCarleman.phaseField (fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k) ϑ i p *
          StrictWeightCarleman.phaseField (fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k) ϑ j p) /
        StrictWeightCarleman.phaseNorm (fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k) ϑ p +
        ∑ i, ∑ j, metricHessianMatrix (dilatedMetric S.g2 lam) ϑ p i j * v i * v j) :
    ∃ r C τ0 : ℝ, 0 < r ∧ 0 < C ∧ 1 ≤ τ0 ∧ Metric.closedBall p r ⊆ Ω ∧ ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ,
      ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ Metric.closedBall p r →
      τ * (∫ x, ∑ i, OAI.AnisotropicCalderon.pd i (fun y => Real.exp (τ * ϑ y) * w y) x ^ 2) +
        τ ^ 3 * (∫ x, (Real.exp (τ * ϑ x) * w x) ^ 2) ≤
        C * ∫ x, Real.exp (2 * (τ * ϑ x)) * normalizedSecondLaplacian S.g1 S.g2 L lam w x ^ 2 := by
  obtain ⟨ρ, hρ, hbΩ, Θ, hΘ, hEq⟩ := exists_smooth_phase_eqOn_ball hΩ hϑ p hp
  have hpb : p ∈ Metric.ball p ρ := Metric.mem_ball_self hρ
  have hnear : Θ =ᶠ[nhds p] ϑ :=
    Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hpb) hEq
  have hpd : ∀ i, OAI.AnisotropicCalderon.pd i Θ p = OAI.AnisotropicCalderon.pd i ϑ p := by
    intro i
    unfold OAI.AnisotropicCalderon.pd
    rw [hnear.fderiv_eq]
  have hW : ∀ i, StrictWeightCarleman.phaseField (fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k) Θ i p =
      StrictWeightCarleman.phaseField (fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k) ϑ i p := by
    intro i
    simp only [StrictWeightCarleman.phaseField, hpd]
  have hN : StrictWeightCarleman.phaseNorm (fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k) Θ p =
      StrictWeightCarleman.phaseNorm (fun i k z => (dilatedMetric S.g2 lam z)⁻¹ i k) ϑ p := by
    simp only [StrictWeightCarleman.phaseNorm, hpd]
  have hH : ∀ i j, metricHessianMatrix (dilatedMetric S.g2 lam) Θ p i j =
      metricHessianMatrix (dilatedMetric S.g2 lam) ϑ p i j :=
    fun i j => metricHessianMatrix_congr_of_eventuallyEq _ hnear i j
  obtain ⟨r0, C, τ0, hr0, hC, hτ0, hest⟩ :=
    local_strict_weight_carleman_native_second_of_metricHessian S L lam hΘ p
      (by simpa only [hpd] using hdϑ)
      (by
        intro v hunit horth
        have horth' := horth
        simp only [hW] at horth'
        simpa only [hH, hW, hN] using hsrc v hunit horth')
  set r : ℝ := min r0 (ρ / 2) with hrdef
  have hr : 0 < r := lt_min hr0 (half_pos hρ)
  have hrball : Metric.closedBall p r ⊆ Metric.ball p ρ :=
    (Metric.closedBall_subset_closedBall (min_le_right _ _)).trans
      (Metric.closedBall_subset_ball (half_lt_self hρ))
  refine ⟨r, C, τ0, hr, hC, hτ0, hrball.trans hbΩ, fun τ hτ w hw hwc hKw => ?_⟩
  have h := hest τ hτ w hw hwc
    (hKw.trans (Metric.closedBall_subset_closedBall (min_le_left _ _)))
  have hoff : ∀ y, y ∉ Metric.ball p ρ → y ∉ tsupport w :=
    fun y hy hyw => hy (hrball (hKw hyw))
  have hfun : (fun y => Real.exp (τ * Θ y) * w y) =
      (fun y => Real.exp (τ * ϑ y) * w y) := by
    funext y
    by_cases hy : y ∈ Metric.ball p ρ
    · rw [hEq hy]
    · simp [image_eq_zero_of_notMem_tsupport (hoff y hy)]
  have ha : ∀ i k, ContDiff ℝ ∞
      (fun z => principalCoefficient (dilatedMetric S.g2 lam) z i k) :=
    contDiff_dilatedSecondPrincipal S lam
  have hvan : ∀ x ∉ tsupport w, normalizedSecondLaplacian S.g1 S.g2 L lam w x = 0 := by
    intro x hx
    rw [Geometry.normalizedSecondLaplacian_eq_mul_fluxDiv, coordinateFluxDivergence_eq_divCoeffGrad]
    have h0 := OAI.AnisotropicCalderon.Sop_vanish
      (a := fun i k z => principalCoefficient (dilatedMetric S.g2 lam) z i k)
      (X := fun _ _ => 0) (q := fun _ => 0) (θ := fun _ => 0) ha
      (fun _ => contDiff_const) contDiff_const contDiff_const hw hx
    have hL : OAI.AnisotropicCalderon.Lop
        (fun i k z => principalCoefficient (dilatedMetric S.g2 lam) z i k) w x = 0 := by
      simpa [OAI.AnisotropicCalderon.Sop] using h0
    change _ * OAI.AnisotropicCalderon.Lop
      (fun i k z => principalCoefficient (dilatedMetric S.g2 lam) z i k) w x = 0
    rw [hL, mul_zero]
  have hres : ∀ x, Real.exp (2 * (τ * Θ x)) * (normalizedSecondLaplacian S.g1 S.g2 L lam w x) ^ 2 =
      Real.exp (2 * (τ * ϑ x)) * (normalizedSecondLaplacian S.g1 S.g2 L lam w x) ^ 2 := by
    intro x
    by_cases hx : x ∈ Metric.ball p ρ
    · rw [hEq hx]
    · simp [hvan x (hoff x hx)]
  have hmass : ∀ x, (Real.exp (τ * Θ x) * w x) ^ 2 =
      (Real.exp (τ * ϑ x) * w x) ^ 2 := fun x => by rw [congrFun hfun x]
  simp only [hfun, hmass, hres] at h
  exact h


end C4LocalNativePhase

end OAI.AnisotropicCalderon.MixedKernelConstructionTask

/-!
## C4 cutoff commutator and compact-flux energy identity (Plan B §5 COMM, §6 identity)

Expansion: REPORT.md §1, items P1-P6, E0-E2, written before this code. Ported from Root's
unverified draft `Root-cutoff-commutator-draft-v001` (P1-P4) and extended (E1, E2). All
functions are globally smooth; zero extension of locally smooth solutions is NOT claimed here.
-/
namespace OAI.AnisotropicCalderon.CutoffCommutator
open MeasureTheory
open scoped ContDiff

/-- P1: second product rule for native partials. -/
theorem pd_pd_mul {f g : R3 → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (i j : Fin 3) (x : R3) :
    pd i (pd j (fun y => f y * g y)) x =
      pd i (pd j f) x * g x + pd j f x * pd i g x +
        pd i f x * pd j g x + f x * pd i (pd j g) x := by
  have hfirst : pd j (fun y => f y * g y) =
      fun y => pd j f y * g y + f y * pd j g y :=
    funext fun y => pd_mul hf hg y
  rw [hfirst, pd_add ((contDiff_pd hf).mul hg) (hf.mul (contDiff_pd hg)),
    pd_mul (contDiff_pd hf) hg, pd_mul hf (contDiff_pd hg)]
  ring

/-- P2: expansion of the literal divergence operator. -/
theorem Lop_expand (a : Fin 3 → Fin 3 → R3 → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) {u : R3 → ℝ}
    (hu : ContDiff ℝ ∞ u) (x : R3) :
    Lop a u x = ∑ i, ∑ j,
      (pd i (a i j) x * pd j u x + a i j x * pd i (pd j u) x) := by
  unfold Lop
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pd_sum (fun j => (ha i j).mul (contDiff_pd hu))]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact pd_mul (ha i j) (contDiff_pd hu) x

/-- P3: the symmetric-coefficient cutoff commutator. -/
theorem Lop_mul_symm (a : Fin 3 → Fin 3 → R3 → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    (hs : ∀ i j x, a i j x = a j i x)
    {chi u : R3 → ℝ} (hc : ContDiff ℝ ∞ chi) (hu : ContDiff ℝ ∞ u) (x : R3) :
    Lop a (fun y => chi y * u y) x =
      chi x * Lop a u x + u x * Lop a chi x +
        2 * ∑ i, ∑ j, a i j x * pd i chi x * pd j u x := by
  rw [Lop_expand a ha (hc.mul hu), Lop_expand a ha hu, Lop_expand a ha hc]
  simp only [pd_mul hc hu, pd_pd_mul hc hu, Fin.sum_univ_three]
  have h10 : a 1 0 x = a 0 1 x := hs 1 0 x
  have h20 : a 2 0 x = a 0 2 x := hs 2 0 x
  have h21 : a 2 1 x = a 1 2 x := hs 2 1 x
  simp only [h10, h20, h21]
  ring

/-- P4 (COMM): a scalar `b` OUTSIDE the divergence; no derivative of `b` appears. -/
theorem beta_Lop_cutoff_comm (a : Fin 3 → Fin 3 → R3 → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    (hs : ∀ i j x, a i j x = a j i x)
    {chi u : R3 → ℝ} (hc : ContDiff ℝ ∞ chi) (hu : ContDiff ℝ ∞ u)
    (b : R3 → ℝ) (x : R3) :
    b x * Lop a (fun y => chi y * u y) x - chi x * (b x * Lop a u x) =
      b x * (u x * Lop a chi x +
        2 * ∑ i, ∑ j, a i j x * pd i chi x * pd j u x) := by
  rw [Lop_mul_symm a ha hs hc hu]
  ring

/-- E1: integrated energy identity by the direct compact flux `eta² u (a∇u)`. The PDE is
needed only where `eta ≠ 0`; no global H¹ or weak-solution premise. -/
theorem energy_integral_eq_zero {a : Fin 3 → Fin 3 → R3 → ℝ}
    (ha : ∀ i k, ContDiff ℝ ∞ (a i k)) {eta u : R3 → ℝ} (heta : ContDiff ℝ ∞ eta)
    (hetac : HasCompactSupport eta) (hu : ContDiff ℝ ∞ u)
    (hL : ∀ x, eta x ≠ 0 → Lop a u x = 0) :
    ∫ x, ∑ i, pd i (fun y => eta y ^ 2 * u y) x * ∑ k, a i k x * pd k u x = 0 := by
  have hG : ∀ i, ContDiff ℝ ∞ (fun z => ∑ k, a i k z * pd k u z) := fun i =>
    ContDiff.sum fun k _ => (ha i k).mul (contDiff_pd hu)
  have hE : ContDiff ℝ ∞ (fun y => eta y ^ 2 * u y) := (heta.pow 2).mul hu
  have hF : ∀ i, ContDiff ℝ ∞ (fun z => eta z ^ 2 * u z * ∑ k, a i k z * pd k u z) :=
    fun i => hE.mul (hG i)
  have hFc : ∀ i, HasCompactSupport (fun z => eta z ^ 2 * u z * ∑ k, a i k z * pd k u z) := by
    intro i
    refine hetac.mono ?_
    intro z hz
    simp only [Function.mem_support] at hz ⊢
    intro h0
    apply hz
    simp [h0]
  have hpt : ∀ x, ∑ i, pd i (fun y => eta y ^ 2 * u y) x * ∑ k, a i k x * pd k u x =
      ∑ i, pd i (fun z => eta z ^ 2 * u z * ∑ k, a i k z * pd k u z) x := by
    intro x
    have h1 : ∑ i, pd i (fun z => eta z ^ 2 * u z * ∑ k, a i k z * pd k u z) x =
        ∑ i, (pd i (fun y => eta y ^ 2 * u y) x * ∑ k, a i k x * pd k u x +
          eta x ^ 2 * u x * pd i (fun z => ∑ k, a i k z * pd k u z) x) :=
      Finset.sum_congr rfl fun i _ => pd_mul hE (hG i) x
    have h2 : Lop a u x = ∑ i, pd i (fun z => ∑ k, a i k z * pd k u z) x := rfl
    rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum, ← h2]
    by_cases h0 : eta x = 0
    · simp [h0]
    · rw [hL x h0, mul_zero, add_zero]
  simp only [hpt]
  rw [integral_finsetSum _ fun i _ => integrable_of_contDiff_hasCompactSupport
    (contDiff_pd (hF i)) (hasCompactSupport_pd (hFc i))]
  exact Finset.sum_eq_zero fun i _ => integral_pd_eq_zero (hF i) (hFc i)

/-- E2: the expanded identity of Plan B §6,
`∫ eta² ∇u·a∇u + 2 ∫ eta u ∇eta·a∇u = 0`, before Young's inequality. -/
theorem energy_identity_expanded {a : Fin 3 → Fin 3 → R3 → ℝ}
    (ha : ∀ i k, ContDiff ℝ ∞ (a i k)) {eta u : R3 → ℝ} (heta : ContDiff ℝ ∞ eta)
    (hetac : HasCompactSupport eta) (hu : ContDiff ℝ ∞ u)
    (hL : ∀ x, eta x ≠ 0 → Lop a u x = 0) :
    (∫ x, eta x ^ 2 * ∑ i, ∑ k, pd i u x * a i k x * pd k u x) +
      2 * ∫ x, eta x * u x * ∑ i, ∑ k, pd i eta x * a i k x * pd k u x = 0 := by
  have h1 := energy_integral_eq_zero ha heta hetac hu hL
  have hpd : ∀ i x, pd i (fun y => eta y ^ 2 * u y) x =
      2 * eta x * pd i eta x * u x + eta x ^ 2 * pd i u x := by
    intro i x
    have hsq : (fun y => eta y ^ 2) = fun y => eta y * eta y := funext fun y => sq (eta y)
    rw [pd_mul (heta.pow 2) hu, hsq, pd_mul heta heta]
    ring
  have hf1 : ContDiff ℝ ∞ (fun x => eta x ^ 2 * ∑ i, ∑ k, pd i u x * a i k x * pd k u x) :=
    (heta.pow 2).mul (ContDiff.sum fun i _ => ContDiff.sum fun k _ =>
      ((contDiff_pd hu).mul (ha i k)).mul (contDiff_pd hu))
  have hf2 : ContDiff ℝ ∞
      (fun x => eta x * u x * ∑ i, ∑ k, pd i eta x * a i k x * pd k u x) :=
    (heta.mul hu).mul (ContDiff.sum fun i _ => ContDiff.sum fun k _ =>
      ((contDiff_pd heta).mul (ha i k)).mul (contDiff_pd hu))
  have hc1 : HasCompactSupport
      (fun x => eta x ^ 2 * ∑ i, ∑ k, pd i u x * a i k x * pd k u x) := by
    refine hetac.mono ?_
    intro z hz
    simp only [Function.mem_support] at hz ⊢
    intro h0
    apply hz
    simp [h0]
  have hc2 : HasCompactSupport
      (fun x => eta x * u x * ∑ i, ∑ k, pd i eta x * a i k x * pd k u x) := by
    refine hetac.mono ?_
    intro z hz
    simp only [Function.mem_support] at hz ⊢
    intro h0
    apply hz
    simp [h0]
  have hpt : ∀ x, ∑ i, pd i (fun y => eta y ^ 2 * u y) x * ∑ k, a i k x * pd k u x =
      eta x ^ 2 * (∑ i, ∑ k, pd i u x * a i k x * pd k u x) +
        2 * (eta x * u x * ∑ i, ∑ k, pd i eta x * a i k x * pd k u x) := by
    intro x
    simp only [hpd, Fin.sum_univ_three]
    ring
  simp only [hpt] at h1
  rw [integral_add (integrable_of_contDiff_hasCompactSupport hf1 hc1)
    ((integrable_of_contDiff_hasCompactSupport hf2 hc2).const_mul 2),
    integral_const_mul] at h1
  exact h1

/-- Y: scalar Young inequality in the division-free form used by INT. -/
theorem young_pair {lamE Λ s α β : ℝ} (hl : 0 < lamE) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hs : s ^ 2 ≤ Λ ^ 2 * α * β) :
    -(2 * lamE * s) ≤ lamE ^ 2 / 2 * α + 2 * Λ ^ 2 * β := by
  have hT : 0 ≤ lamE ^ 2 / 2 * α + 2 * Λ ^ 2 * β := by positivity
  have hT2 : 4 * (lamE * s) ^ 2 ≤ (lamE ^ 2 / 2 * α + 2 * Λ ^ 2 * β) ^ 2 := by
    nlinarith [sq_nonneg (lamE ^ 2 / 2 * α - 2 * Λ ^ 2 * β),
      mul_le_mul_of_nonneg_left hs (sq_nonneg lamE)]
  by_contra h
  push_neg at h
  nlinarith [h, hT, hT2]

/-- A smooth function vanishing wherever the compactly supported `eta` vanishes is
integrable. -/
theorem integrable_of_eta_factor {eta f : R3 → ℝ} (hetac : HasCompactSupport eta)
    (hf : ContDiff ℝ ∞ f) (h0 : ∀ x, eta x = 0 → f x = 0) : Integrable f :=
  integrable_of_contDiff_hasCompactSupport hf
    (hetac.mono fun z hz => fun he => hz (h0 z he))

/-- R1 (INT): direct Caccioppoli inequality for a smooth solution of `Lop a u = 0` on the
zero-free set of the compact cutoff `eta`, from E2 and Young; ellipticity bounds are needed
only where `eta ≠ 0`. No global H¹ or weak-solution premise. -/
theorem caccioppoli_of_ellipticity {a : Fin 3 → Fin 3 → R3 → ℝ}
    (ha : ∀ i k, ContDiff ℝ ∞ (a i k)) {eta u : R3 → ℝ} (heta : ContDiff ℝ ∞ eta)
    (hetac : HasCompactSupport eta) (hu : ContDiff ℝ ∞ u)
    (hL : ∀ x, eta x ≠ 0 → Lop a u x = 0) {lamE Λ : ℝ} (hl : 0 < lamE)
    (hlow : ∀ x, eta x ≠ 0 → ∀ ξ : Fin 3 → ℝ,
      lamE * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ k, ξ i * a i k x * ξ k)
    (hup : ∀ x, eta x ≠ 0 → ∀ ζ ξ : Fin 3 → ℝ,
      (∑ i, ∑ k, ζ i * a i k x * ξ k) ^ 2 ≤ Λ ^ 2 * (∑ i, ζ i ^ 2) * ∑ k, ξ k ^ 2) :
    ∫ x, eta x ^ 2 * ∑ i, pd i u x ^ 2 ≤
      (2 * Λ / lamE) ^ 2 * ∫ x, u x ^ 2 * ∑ i, pd i eta x ^ 2 := by
  have hE2 := energy_identity_expanded ha heta hetac hu hL
  have hgu : ContDiff ℝ ∞ (fun x => ∑ i, pd i u x ^ 2) :=
    ContDiff.sum fun i _ => (contDiff_pd hu).pow 2
  have hge : ContDiff ℝ ∞ (fun x => ∑ i, pd i eta x ^ 2) :=
    ContDiff.sum fun i _ => (contDiff_pd heta).pow 2
  have IQ : Integrable (fun x => eta x ^ 2 * ∑ i, ∑ k, pd i u x * a i k x * pd k u x) :=
    integrable_of_eta_factor hetac ((heta.pow 2).mul (ContDiff.sum fun i _ => ContDiff.sum
      fun k _ => ((contDiff_pd hu).mul (ha i k)).mul (contDiff_pd hu)))
      (fun x h => by simp [h])
  have IR : Integrable (fun x => eta x * u x * ∑ i, ∑ k, pd i eta x * a i k x * pd k u x) :=
    integrable_of_eta_factor hetac ((heta.mul hu).mul (ContDiff.sum fun i _ => ContDiff.sum
      fun k _ => ((contDiff_pd heta).mul (ha i k)).mul (contDiff_pd hu)))
      (fun x h => by simp [h])
  have Iα : Integrable (fun x => eta x ^ 2 * ∑ i, pd i u x ^ 2) :=
    integrable_of_eta_factor hetac ((heta.pow 2).mul hgu) (fun x h => by simp [h])
  have Iβ : Integrable (fun x => u x ^ 2 * ∑ i, pd i eta x ^ 2) := by
    refine integrable_of_contDiff_hasCompactSupport ((hu.pow 2).mul hge) (hetac.mono' ?_)
    intro z hz
    by_contra hn
    apply hz
    have hf : fderiv ℝ eta z = 0 := by
      by_contra hne
      exact hn (support_fderiv_subset (𝕜 := ℝ) hne)
    simp [pd, hf]
  have hA : ∀ x, lamE * (eta x ^ 2 * ∑ i, pd i u x ^ 2) ≤
      eta x ^ 2 * ∑ i, ∑ k, pd i u x * a i k x * pd k u x := by
    intro x
    by_cases h0 : eta x = 0
    · simp [h0]
    · have h := hlow x h0 (fun i => pd i u x)
      calc lamE * (eta x ^ 2 * ∑ i, pd i u x ^ 2) =
          eta x ^ 2 * (lamE * ∑ i, pd i u x ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h (sq_nonneg _)
  have hB : ∀ x, -(2 * lamE * (eta x * u x * ∑ i, ∑ k, pd i eta x * a i k x * pd k u x)) ≤
      lamE ^ 2 / 2 * (eta x ^ 2 * ∑ i, pd i u x ^ 2) +
        2 * Λ ^ 2 * (u x ^ 2 * ∑ i, pd i eta x ^ 2) := by
    intro x
    have hα : 0 ≤ eta x ^ 2 * ∑ i, pd i u x ^ 2 :=
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)
    have hβ : 0 ≤ u x ^ 2 * ∑ i, pd i eta x ^ 2 :=
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)
    by_cases h0 : eta x = 0
    · have hR : eta x * u x * ∑ i, ∑ k, pd i eta x * a i k x * pd k u x = 0 := by
        rw [h0]; ring
      have hα0 : eta x ^ 2 * ∑ i, pd i u x ^ 2 = 0 := by rw [h0]; ring
      rw [hR, hα0]
      have : 0 ≤ 2 * Λ ^ 2 * (u x ^ 2 * ∑ i, pd i eta x ^ 2) := by positivity
      linarith
    · refine young_pair hl hα hβ ?_
      have hP := hup x h0 (fun i => pd i eta x) (fun k => pd k u x)
      calc (eta x * u x * ∑ i, ∑ k, pd i eta x * a i k x * pd k u x) ^ 2 =
          eta x ^ 2 * u x ^ 2 * (∑ i, ∑ k, pd i eta x * a i k x * pd k u x) ^ 2 := by ring
        _ ≤ eta x ^ 2 * u x ^ 2 *
            (Λ ^ 2 * (∑ i, pd i eta x ^ 2) * ∑ k, pd k u x ^ 2) :=
          mul_le_mul_of_nonneg_left hP (by positivity)
        _ = Λ ^ 2 * (eta x ^ 2 * ∑ i, pd i u x ^ 2) * (u x ^ 2 * ∑ i, pd i eta x ^ 2) := by
          ring
  have h1 : lamE * ∫ x, eta x ^ 2 * ∑ i, pd i u x ^ 2 ≤
      ∫ x, eta x ^ 2 * ∑ i, ∑ k, pd i u x * a i k x * pd k u x := by
    rw [← integral_const_mul]
    exact integral_mono (Iα.const_mul lamE) IQ hA
  have h2 : ∫ x, -(2 * lamE * (eta x * u x * ∑ i, ∑ k, pd i eta x * a i k x * pd k u x)) ≤
      ∫ x, (lamE ^ 2 / 2 * (eta x ^ 2 * ∑ i, pd i u x ^ 2) +
        2 * Λ ^ 2 * (u x ^ 2 * ∑ i, pd i eta x ^ 2)) :=
    integral_mono ((IR.const_mul (2 * lamE)).neg)
      ((Iα.const_mul (lamE ^ 2 / 2)).add (Iβ.const_mul (2 * Λ ^ 2))) hB
  rw [integral_neg, integral_const_mul, integral_add (Iα.const_mul _) (Iβ.const_mul _),
    integral_const_mul, integral_const_mul] at h2
  have h1' := mul_le_mul_of_nonneg_left h1 hl.le
  have h3 : lamE * (∫ x, eta x ^ 2 * ∑ i, ∑ k, pd i u x * a i k x * pd k u x) +
      2 * lamE * ∫ x, eta x * u x * ∑ i, ∑ k, pd i eta x * a i k x * pd k u x = 0 := by
    linear_combination lamE * hE2
  have hl2 : 0 < lamE ^ 2 := by positivity
  have e1 : (2 * Λ / lamE) ^ 2 = 4 * Λ ^ 2 / lamE ^ 2 := by rw [div_pow]; ring
  rw [e1, div_mul_eq_mul_div, le_div_iff₀ hl2]
  nlinarith [h1', h2, h3]

/-- EL: compact ellipticity bounds, lower by T6a with `ℓ = 0`, upper by Cauchy–Schwarz. -/
theorem ellipticity_on_compact {a : Fin 3 → Fin 3 → R3 → ℝ} (hac : ∀ i k, Continuous (a i k))
    {K : Set R3} (hK : IsCompact K)
    (hpos : ∀ x ∈ K, ∀ ξ : Fin 3 → ℝ, ξ ≠ 0 → 0 < ∑ i, ∑ k, ξ i * a i k x * ξ k) :
    ∃ lamE Λ : ℝ, 0 < lamE ∧
      (∀ x ∈ K, ∀ ξ : Fin 3 → ℝ, lamE * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ k, ξ i * a i k x * ξ k) ∧
      (∀ x ∈ K, ∀ ζ ξ : Fin 3 → ℝ,
        (∑ i, ∑ k, ζ i * a i k x * ξ k) ^ 2 ≤ Λ ^ 2 * (∑ i, ζ i ^ 2) * ∑ k, ξ k ^ 2) := by
  have hQc : Continuous (fun p : R3 × (Fin 3 → ℝ) =>
      ∑ i, ∑ k, p.2 i * a i k p.1 * p.2 k) := by
    have := hac
    fun_prop
  obtain ⟨D, α, -, hα, hcoer⟩ := StrictWeightCarleman.uniform_rank_one_coercivity hK
    (fun x ξ => ∑ i, ∑ k, ξ i * a i k x * ξ k) (fun _ _ => 0) hQc continuous_const
    (fun x c ξ => by simp only [Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]; ring)
    (fun x c ξ => by ring) (fun x hx ξ hξ _ => hpos x hx ξ hξ)
  have hnc : Continuous (fun x => ∑ i, ∑ k, a i k x ^ 2) := by
    have := hac
    fun_prop
  obtain ⟨N, hN⟩ := hK.exists_bound_of_continuousOn hnc.continuousOn
  refine ⟨α, max N 1, hα, fun x hx ξ => ?_, fun x hx ζ ξ => ?_⟩
  · have h := hcoer x hx ξ
    simpa using h
  · have hrow : (∑ i, ∑ k, ζ i * a i k x * ξ k) ^ 2 ≤
        (∑ i, ζ i ^ 2) * ((∑ i, ∑ k, a i k x ^ 2) * ∑ k, ξ k ^ 2) := by
      have e : ∑ i, ∑ k, ζ i * a i k x * ξ k = ∑ i, ζ i * ∑ k, a i k x * ξ k :=
        Finset.sum_congr rfl fun i _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      rw [e]
      refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun i _ => sq_nonneg _)
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hNx : ∑ i, ∑ k, a i k x ^ 2 ≤ max N 1 ^ 2 := by
      have h1 := hN x hx
      rw [Real.norm_eq_abs] at h1
      have h2 := le_abs_self (∑ i, ∑ k, a i k x ^ 2)
      have hM1 : (1 : ℝ) ≤ max N 1 := le_max_right _ _
      have hM : max N 1 ≤ max N 1 ^ 2 := by
        rw [sq]
        exact le_mul_of_one_le_left (by linarith) hM1
      exact h2.trans (h1.trans ((le_max_left N 1).trans hM))
    have hζ : 0 ≤ ∑ i, ζ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hξ : 0 ≤ ∑ k, ξ k ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    calc _ ≤ (∑ i, ζ i ^ 2) * ((∑ i, ∑ k, a i k x ^ 2) * ∑ k, ξ k ^ 2) := hrow
      _ ≤ (∑ i, ζ i ^ 2) * (max N 1 ^ 2 * ∑ k, ξ k ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hNx hξ) hζ
      _ = _ := by ring

/-- R2a: zero extension. A cutoff with `tsupport chi ⊆ D` times a function smooth only on
the open `D` is globally smooth; values of `w` off `D` are irrelevant. -/
theorem contDiff_mul_of_tsupport_subset {D : Set R3} (hD : IsOpen D) {chi w : R3 → ℝ}
    (hc : ContDiff ℝ ∞ chi) (hsub : tsupport chi ⊆ D) (hw : ContDiffOn ℝ ∞ w D) :
    ContDiff ℝ ∞ (fun y => chi y * w y) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ D
  · exact (hc.contDiffOn.mul hw).contDiffAt (hD.mem_nhds hx)
  · have hx' : x ∉ tsupport chi := fun h => hx (hsub h)
    have hmem : (tsupport chi)ᶜ ∈ nhds x := (isClosed_tsupport chi).isOpen_compl.mem_nhds hx'
    have heq : (fun y => chi y * w y) =ᶠ[nhds x] fun _ => (0 : ℝ) :=
      Filter.mem_of_superset hmem fun y hy => by
        have h0 : chi y = 0 := by
          by_contra h
          exact hy (subset_tsupport chi h)
        show chi y * w y = 0
        rw [h0, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-- L1: native partials depend only on the germ. -/
theorem pd_congr_of_eventuallyEq {f g : R3 → ℝ} {x : R3} (h : f =ᶠ[nhds x] g) (i : Fin 3) :
    pd i f x = pd i g x := by
  unfold pd
  rw [h.fderiv_eq]

/-- L2: the literal divergence operator depends only on the germ. -/
theorem Lop_congr_of_eventuallyEq (a : Fin 3 → Fin 3 → R3 → ℝ) {f g : R3 → ℝ} {x : R3}
    (h : f =ᶠ[nhds x] g) : Lop a f x = Lop a g x := by
  unfold Lop
  refine Finset.sum_congr rfl fun i _ => pd_congr_of_eventuallyEq ?_ i
  have hk : ∀ k, ∀ᶠ y in nhds x, pd k f y = pd k g y := fun k =>
    h.eventuallyEq_nhds.mono fun y hy => pd_congr_of_eventuallyEq hy k
  filter_upwards [Filter.eventually_all.2 hk] with y hy
  simp only [hy]

/-- R2a: the zero extension keeps the compact support of the cutoff. -/
theorem hasCompactSupport_mul_left_of {chi w : R3 → ℝ} (hcc : HasCompactSupport chi) :
    HasCompactSupport (fun y => chi y * w y) :=
  hcc.mono fun y hy h0 => hy (by simp [h0])

/-- Positive definiteness in the explicit double-sum form used by EL. -/
theorem quadSum_pos_of_posDef {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M.PosDef)
    {ξ : Fin 3 → ℝ} (hξ : ξ ≠ 0) : 0 < ∑ i, ∑ k, ξ i * M i k * ξ k := by
  have h := hM.dotProduct_mulVec_pos hξ
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Fin.sum_univ_three] at h
  simp only [Fin.sum_univ_three]
  linarith

/-- Caccioppoli with constants from compact ellipticity on `tsupport eta`, chosen BEFORE `u`. -/
theorem exists_caccioppoli_constant {a : Fin 3 → Fin 3 → R3 → ℝ}
    (ha : ∀ i k, ContDiff ℝ ∞ (a i k)) {eta : R3 → ℝ} (heta : ContDiff ℝ ∞ eta)
    (hetac : HasCompactSupport eta)
    (hpos : ∀ x ∈ tsupport eta, ∀ ξ : Fin 3 → ℝ, ξ ≠ 0 →
      0 < ∑ i, ∑ k, ξ i * a i k x * ξ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : R3 → ℝ, ContDiff ℝ ∞ u → (∀ x, eta x ≠ 0 → Lop a u x = 0) →
      ∫ x, eta x ^ 2 * ∑ i, pd i u x ^ 2 ≤ C * ∫ x, u x ^ 2 * ∑ i, pd i eta x ^ 2 := by
  obtain ⟨lamE, Λ, hl, hlow, hup⟩ :=
    ellipticity_on_compact (fun i k => (ha i k).continuous) hetac hpos
  refine ⟨(2 * Λ / lamE) ^ 2, sq_nonneg _, fun u hu hL => ?_⟩
  exact caccioppoli_of_ellipticity ha heta hetac hu hL hl
    (fun x hx => hlow x (subset_tsupport eta hx))
    (fun x hx => hup x (subset_tsupport eta hx))

/-- Z1: off `tsupport chi` the cutoff has the zero germ, for arbitrary `w`. -/
theorem mul_eventuallyEq_zero_of_not_mem_tsupport {chi : R3 → ℝ} (w : R3 → ℝ) {x : R3}
    (hx : x ∉ tsupport chi) : (fun y => chi y * w y) =ᶠ[nhds x] fun _ => (0 : ℝ) :=
  Filter.mem_of_superset ((isClosed_tsupport chi).isOpen_compl.mem_nhds hx) fun y hy => by
    have h0 : chi y = 0 := by
      by_contra h
      exact hy (subset_tsupport chi h)
    show chi y * w y = 0
    rw [h0, zero_mul]

/-- Z1: the literal divergence operator kills constants. -/
theorem Lop_const_zero (a : Fin 3 → Fin 3 → R3 → ℝ) (x : R3) :
    Lop a (fun _ => (0 : ℝ)) x = 0 := by
  simp [Lop, pd]

/-- Z1: off `tsupport chi`, `Lop a (chi*w)`, `Lop a chi` and every `pd i chi` vanish. -/
theorem Lop_mul_eq_zero_of_not_mem_tsupport (a : Fin 3 → Fin 3 → R3 → ℝ) {chi : R3 → ℝ}
    (w : R3 → ℝ) {x : R3} (hx : x ∉ tsupport chi) :
    Lop a (fun y => chi y * w y) x = 0 := by
  rw [Lop_congr_of_eventuallyEq a (mul_eventuallyEq_zero_of_not_mem_tsupport w hx)]
  exact Lop_const_zero a x

theorem chi_eventuallyEq_zero_of_not_mem_tsupport {chi : R3 → ℝ} {x : R3}
    (hx : x ∉ tsupport chi) : chi =ᶠ[nhds x] fun _ => (0 : ℝ) := by
  have h := mul_eventuallyEq_zero_of_not_mem_tsupport (chi := chi) (fun _ => (1 : ℝ)) hx
  simpa using h

theorem Lop_eq_zero_of_not_mem_tsupport (a : Fin 3 → Fin 3 → R3 → ℝ) {chi : R3 → ℝ}
    {x : R3} (hx : x ∉ tsupport chi) : Lop a chi x = 0 := by
  rw [Lop_congr_of_eventuallyEq a (chi_eventuallyEq_zero_of_not_mem_tsupport hx)]
  exact Lop_const_zero a x

theorem pd_eq_zero_of_not_mem_tsupport {chi : R3 → ℝ} {x : R3} (hx : x ∉ tsupport chi)
    (i : Fin 3) : pd i chi x = 0 := by
  rw [pd_congr_of_eventuallyEq (chi_eventuallyEq_zero_of_not_mem_tsupport hx) i]
  simp [pd]

/-- Z3: where the cutoff is locally constant its partials vanish. -/
theorem pd_eq_zero_of_eventuallyEq_const {chi : R3 → ℝ} {x : R3} {c : ℝ}
    (h : chi =ᶠ[nhds x] fun _ => c) (i : Fin 3) : pd i chi x = 0 := by
  rw [pd_congr_of_eventuallyEq h i]
  simp [pd]

/-- Z3: where the cutoff is locally constant, `Lop a chi` vanishes. -/
theorem Lop_eq_zero_of_eventuallyEq_const (a : Fin 3 → Fin 3 → R3 → ℝ) {chi : R3 → ℝ}
    {x : R3} {c : ℝ} (h : chi =ᶠ[nhds x] fun _ => c) : Lop a chi x = 0 := by
  rw [Lop_congr_of_eventuallyEq a h]
  simp [Lop, pd]

/-- P0: first native chain rule for the strict phase `psi = theta - kappa*theta^2`. -/
theorem pd_strictPhase {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (κ : ℝ) (i : Fin 3) (x : R3) :
    pd i (fun y => θ y - κ * θ y ^ 2) x = (1 - 2 * κ * θ x) * pd i θ x := by
  have h : (fun y => θ y - κ * θ y ^ 2) = fun y => θ y + (-κ) * (θ y * θ y) := by
    funext y
    ring
  have hsq : ContDiff ℝ ∞ (fun y => θ y * θ y) := hθ.mul hθ
  have hc : ContDiff ℝ ∞ (fun y => (-κ) * (θ y * θ y)) := contDiff_const.mul hsq
  rw [h, pd_add hθ hc, pd_const_mul (-κ) hsq, pd_mul hθ hθ]
  ring

/-- P0: second native chain rule for the strict phase; at `theta x = 0` this is
`Hess theta - 2 kappa dtheta ⊗ dtheta`. -/
theorem pd_pd_strictPhase {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (κ : ℝ) (i j : Fin 3)
    (x : R3) :
    pd j (pd i (fun y => θ y - κ * θ y ^ 2)) x =
      (1 - 2 * κ * θ x) * pd j (pd i θ) x - 2 * κ * pd j θ x * pd i θ x := by
  have h : pd i (fun y => θ y - κ * θ y ^ 2) =
      fun y => (1 + (-2 * κ) * θ y) * pd i θ y := by
    funext y
    rw [pd_strictPhase hθ κ i y]
    ring
  have hl : ContDiff ℝ ∞ (fun y => (-2 * κ) * θ y) := contDiff_const.mul hθ
  have hf : ContDiff ℝ ∞ (fun y => 1 + (-2 * κ) * θ y) := contDiff_const.add hl
  rw [h, pd_mul hf (contDiff_pd hθ), pd_add contDiff_const hl, pd_const_mul (-2 * κ) hθ,
    pd_const]
  ring

/-- L1: a smooth compactly supported plateau, `= 1` near the compact `K`, supported in open
`D`. It depends only on `(K, D)`. -/
theorem exists_plateau_cutoff {D K : Set R3} (hD : IsOpen D) (hK : IsCompact K)
    (hKD : K ⊆ D) :
    ∃ zeta : R3 → ℝ, ContDiff ℝ ∞ zeta ∧ HasCompactSupport zeta ∧ tsupport zeta ⊆ D ∧
      ∀ x ∈ K, zeta =ᶠ[nhds x] fun _ => (1 : ℝ) := by
  obtain ⟨U, hUo, hKU, hUD, hUc⟩ := exists_open_between_and_isCompact_closure hK hD hKD
  obtain ⟨V, hVo, hKV, hVU, -⟩ := exists_open_between_and_isCompact_closure hK hUo hKU
  obtain ⟨f, hf, -, hsupp, h1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hUo isClosed_closure hVU
  refine ⟨f, hf, ?_, ?_, ?_⟩
  · show IsCompact (closure (Function.support f))
    rw [hsupp]
    exact hUc
  · show closure (Function.support f) ⊆ D
    rw [hsupp]
    exact hUD
  · intro x hx
    exact Filter.mem_of_superset (hVo.mem_nhds (hKV hx)) fun y hy =>
      (h1 y).1 (subset_closure hy)

/-- L2: local Caccioppoli with an explicit plateau `zeta` (chosen before `w`); `w` is smooth
only on `D` and solves the PDE only on `tsupport eta`. -/
theorem exists_local_caccioppoli_constant_with_plateau
    {D : Set R3} (hD : IsOpen D)
    {a : Fin 3 → Fin 3 → R3 → ℝ} (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    {eta zeta : R3 → ℝ} (heta : ContDiff ℝ ∞ eta) (hetac : HasCompactSupport eta)
    (hzeta : ContDiff ℝ ∞ zeta)
    (hzD : tsupport zeta ⊆ D)
    (hz1 : ∀ x ∈ tsupport eta, zeta =ᶠ[nhds x] fun _ => (1 : ℝ))
    (hpos : ∀ x ∈ tsupport eta, ∀ ξ : Fin 3 → ℝ, ξ ≠ 0 →
      0 < ∑ i, ∑ k, ξ i * a i k x * ξ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : R3 → ℝ, ContDiffOn ℝ ∞ w D →
      (∀ x ∈ tsupport eta, Lop a w x = 0) →
      ∫ x, eta x ^ 2 * ∑ i, pd i w x ^ 2 ≤
        C * ∫ x, w x ^ 2 * ∑ i, pd i eta x ^ 2 := by
  obtain ⟨C, hC, hcac⟩ := exists_caccioppoli_constant ha heta hetac hpos
  refine ⟨C, hC, ?_⟩
  intro w hw hL
  have hu : ContDiff ℝ ∞ (fun y => zeta y * w y) :=
    contDiff_mul_of_tsupport_subset hD hzeta hzD hw
  have heq (x : R3) (hx : x ∈ tsupport eta) : (fun y => zeta y * w y) =ᶠ[nhds x] w := by
    filter_upwards [hz1 x hx] with y hy
    rw [hy, one_mul]
  have hpde : ∀ x, eta x ≠ 0 → Lop a (fun y => zeta y * w y) x = 0 := by
    intro x hx
    have hK : x ∈ tsupport eta := subset_tsupport eta hx
    rw [Lop_congr_of_eventuallyEq a (heq x hK)]
    exact hL x hK
  have hleft : (fun x => eta x ^ 2 * ∑ i, pd i (fun y => zeta y * w y) x ^ 2) =
      (fun x => eta x ^ 2 * ∑ i, pd i w x ^ 2) := by
    funext x
    by_cases hx : x ∈ tsupport eta
    · have hp : ∀ i, pd i (fun y => zeta y * w y) x = pd i w x := fun i =>
        pd_congr_of_eventuallyEq (heq x hx) i
      simp only [hp]
    · have h0 : eta x = 0 := by
        by_contra hn
        exact hx (subset_tsupport eta hn)
      simp [h0]
  have hright : (fun x => (zeta x * w x) ^ 2 * ∑ i, pd i eta x ^ 2) =
      (fun x => w x ^ 2 * ∑ i, pd i eta x ^ 2) := by
    funext x
    by_cases hx : x ∈ tsupport eta
    · rw [(heq x hx).eq_of_nhds]
    · simp [pd_eq_zero_of_not_mem_tsupport hx]
  have h := hcac _ hu hpde
  beta_reduce at h
  rw [hleft, hright] at h
  exact h

/-- L2+L1: local Caccioppoli; the constant depends only on `a`, `eta` (and `D`), and is
chosen BEFORE the arbitrary local solution `w`. -/
theorem exists_local_caccioppoli_constant
    {D : Set R3} (hD : IsOpen D)
    {a : Fin 3 → Fin 3 → R3 → ℝ} (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    {eta : R3 → ℝ} (heta : ContDiff ℝ ∞ eta) (hetac : HasCompactSupport eta)
    (hKD : tsupport eta ⊆ D)
    (hpos : ∀ x ∈ tsupport eta, ∀ ξ : Fin 3 → ℝ, ξ ≠ 0 →
      0 < ∑ i, ∑ k, ξ i * a i k x * ξ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : R3 → ℝ, ContDiffOn ℝ ∞ w D →
      (∀ x ∈ tsupport eta, Lop a w x = 0) →
      ∫ x, eta x ^ 2 * ∑ i, pd i w x ^ 2 ≤
        C * ∫ x, w x ^ 2 * ∑ i, pd i eta x ^ 2 := by
  obtain ⟨zeta, hz, -, hzD, hz1⟩ := exists_plateau_cutoff hD hetac hKD
  exact exists_local_caccioppoli_constant_with_plateau hD ha heta hetac hz hzD hz1 hpos

end OAI.AnisotropicCalderon.CutoffCommutator

