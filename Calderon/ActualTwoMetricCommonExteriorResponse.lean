import Calderon.RadiusTwoMetricSourceFunctionalMinimizerTailDiagnostic
import Calderon.MetricNativeAffineReplacementCorrectionDiagnostic
import Calderon.NativeNestedSourceRestrictionTailDiagnostic

/-! EXPANSION.json precedes this exact original two-metric native source-response construction.
The source trace-regularity step is replaced by genuine native H1 density. Kernel realization
and pointwise smooth representatives remain separate; no kernel/source-equality premise. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory TopologicalSpace
open scoped ENNReal InnerProductSpace ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge EnergyBridge.ExteriorSource EnergyBridge.NativeNestedDomain
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

def exteriorAnnulusOpens : Opens R3 :=
  ⟨{x : R3 | (1 : ℝ) < ‖x‖ ∧ ‖x‖ < 2},
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)⟩

lemma exteriorAnnulusOpens_le_radiusTwoOpens : exteriorAnnulusOpens ≤ radiusTwoOpens := by
  intro x hx
  have hNorm : ‖x‖ < 2 := hx.2
  change x ∈ Metric.ball (0 : R3) 2
  simpa only [Metric.mem_ball,dist_zero_right] using hNorm

lemma exteriorSupportedSource_zero_on_ball (F : SmoothData)
    (hSupport : Function.support F.1 ⊆ (exteriorAnnulusOpens : Set R3)) :
    ∀ x ∈ (ballOpens : Set R3), F.1 x = 0 := by
  intro x hx
  have hNorm : ‖x‖ < 1 := by
    change x ∈ Metric.ball (0 : R3) 1 at hx
    simpa only [Metric.mem_ball,dist_zero_right] using hx
  by_contra hF
  have hAnn : x ∈ (exteriorAnnulusOpens : Set R3) := hSupport hF
  exact (not_lt_of_ge hNorm.le) hAnn.1

lemma radiusTwoSourceSolution_restriction_weak_harmonic
    (g : MatrixField) (hg : IsAdmissibleMetric g) (F : SmoothData)
    (hSupport : Function.support F.1 ⊆ (exteriorAnnulusOpens : Set R3)) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0
      (TauCeti.W1p.restrictL ballOpens_le_radiusTwoOpens
        (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F) : RadiusTwoH1)) (v : BallH1) = 0 := by
  have hZero : ∀ᵐ x ∂(volume : Measure R3).restrict radiusTwoOpens,
      x ∈ (ballOpens : Set R3) → F.1 x = 0 :=
    Filter.Eventually.of_forall (exteriorSupportedSource_zero_on_ball F hSupport)
  exact source_restriction_weak_harmonic ballOpens radiusTwoOpens ballOpens_le_radiusTwoOpens
    (principalCoefficient g) (memLp_radiusTwoMetricEnergyIntegrand g hg)
    (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F)) F.1 hZero
    (radiusTwoSourceSolution_smooth_equation g hg F) v

def radiusTwoMetricInteriorReplacement
    (g₁ g₂ : MatrixField) (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (F : SmoothData) : RadiusTwoH1Zero :=
  nativeZeroBoundaryReplacement ballOpens radiusTwoOpens ballOpens_le_radiusTwoOpens
    (radiusTwoSourceSolution g₁ hg₁ (smoothRadiusTwoForcing F))
    (metricNativeAffineReplacementCorrection g₁ g₂ hg₁ hg₂
      (TauCeti.W1p.restrictL ballOpens_le_radiusTwoOpens
        (radiusTwoSourceSolution g₁ hg₁ (smoothRadiusTwoForcing F) : RadiusTwoH1)))

lemma radiusTwoMetricInteriorReplacement_eq_constructor
    (g₁ g₂ : MatrixField) (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (F : SmoothData) :
    radiusTwoMetricInteriorReplacement g₁ g₂ hg₁ hg₂ F =
    nativeZeroBoundaryReplacement ballOpens radiusTwoOpens ballOpens_le_radiusTwoOpens
      (radiusTwoSourceSolution g₁ hg₁ (smoothRadiusTwoForcing F))
      (metricNativeAffineReplacementCorrection g₁ g₂ hg₁ hg₂
        (TauCeti.W1p.restrictL ballOpens_le_radiusTwoOpens
          (radiusTwoSourceSolution g₁ hg₁ (smoothRadiusTwoForcing F) : RadiusTwoH1))) := rfl

attribute [local irreducible] metricNativeAffineHarmonicExtension metricNativeAffineReplacementCorrection
  radiusTwoSourceSolution radiusTwoMetricInteriorReplacement nativeZeroBoundaryReplacement radiusTwoMetricSourceFunctional

lemma radiusTwoMetricInteriorReplacement_restrict
    (g₁ g₂ : MatrixField) (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (F : SmoothData) (hSupport : Function.support F.1 ⊆ (exteriorAnnulusOpens : Set R3)) :
    TauCeti.W1p.restrictL ballOpens_le_radiusTwoOpens
      (radiusTwoMetricInteriorReplacement g₁ g₂ hg₁ hg₂ F : RadiusTwoH1) =
    metricNativeAffineHarmonicExtension g₂ hg₂
      (TauCeti.W1p.restrictL ballOpens_le_radiusTwoOpens
        (radiusTwoSourceSolution g₁ hg₁ (smoothRadiusTwoForcing F) : RadiusTwoH1)) := by
  let W : RadiusTwoH1Zero := radiusTwoSourceSolution g₁ hg₁ (smoothRadiusTwoForcing F)
  let d : BallH1 := TauCeti.W1p.restrictL ballOpens_le_radiusTwoOpens (W : RadiusTwoH1)
  let z : BallH1Zero := metricNativeAffineReplacementCorrection g₁ g₂ hg₁ hg₂ d
  have hFix : metricNativeAffineHarmonicExtension g₁ hg₁ d = d :=
    metricNativeAffineHarmonicExtension_eq_self_of_weak g₁ hg₁ d
      (radiusTwoSourceSolution_restriction_weak_harmonic g₁ hg₁ F hSupport)
  have hShape := congrArg (fun R : RadiusTwoH1Zero =>
    TauCeti.W1p.restrictL ballOpens_le_radiusTwoOpens (R : RadiusTwoH1))
      (radiusTwoMetricInteriorReplacement_eq_constructor g₁ g₂ hg₁ hg₂ F)
  have hRestr := nativeZeroBoundaryReplacement_restrict ballOpens radiusTwoOpens
    ballOpens_le_radiusTwoOpens W z
  have hCorr := metricNativeAffineReplacementCorrection_coe g₁ g₂ hg₁ hg₂ d
  have hAdd := congrArg (fun v : BallH1 => d+v) hCorr
  have hAlgebra : d + (metricNativeAffineHarmonicExtension g₂ hg₂ d -
      metricNativeAffineHarmonicExtension g₁ hg₁ d) = metricNativeAffineHarmonicExtension g₂ hg₂ d := by
    rw [hFix]
    abel
  exact hShape.trans (hRestr.trans (hAdd.trans hAlgebra))

lemma radiusTwoMetricInteriorReplacement_energy_eq
    (g₁ g₂ : MatrixField) (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (hΛ : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g₁ f = minimalEnergy g₂ f)
    (F : SmoothData) (hSupport : Function.support F.1 ⊆ (exteriorAnnulusOpens : Set R3)) :
    TauCeti.PDE.energyFormH1 (principalCoefficient g₂) 0 0
      (radiusTwoMetricInteriorReplacement g₁ g₂ hg₁ hg₂ F : RadiusTwoH1)
      (radiusTwoMetricInteriorReplacement g₁ g₂ hg₁ hg₂ F : RadiusTwoH1) =
    TauCeti.PDE.energyFormH1 (principalCoefficient g₁) 0 0
      (radiusTwoSourceSolution g₁ hg₁ (smoothRadiusTwoForcing F) : RadiusTwoH1)
      (radiusTwoSourceSolution g₁ hg₁ (smoothRadiusTwoForcing F) : RadiusTwoH1) := by
  let W : RadiusTwoH1Zero := radiusTwoSourceSolution g₁ hg₁ (smoothRadiusTwoForcing F)
  let d : BallH1 := TauCeti.W1p.restrictL ballOpens_le_radiusTwoOpens (W : RadiusTwoH1)
  let z : BallH1Zero := metricNativeAffineReplacementCorrection g₁ g₂ hg₁ hg₂ d
  let R : RadiusTwoH1Zero := nativeZeroBoundaryReplacement ballOpens radiusTwoOpens
    ballOpens_le_radiusTwoOpens W z
  have hShape : radiusTwoMetricInteriorReplacement g₁ g₂ hg₁ hg₂ F = R :=
    radiusTwoMetricInteriorReplacement_eq_constructor g₁ g₂ hg₁ hg₂ F
  have hRestr : TauCeti.W1p.restrictL ballOpens_le_radiusTwoOpens (R : RadiusTwoH1) =
      metricNativeAffineHarmonicExtension g₂ hg₂ d :=
    (congrArg (fun T : RadiusTwoH1Zero =>
      TauCeti.W1p.restrictL ballOpens_le_radiusTwoOpens (T : RadiusTwoH1)) hShape).symm.trans
      (radiusTwoMetricInteriorReplacement_restrict g₁ g₂ hg₁ hg₂ F hSupport)
  have hFix : metricNativeAffineHarmonicExtension g₁ hg₁ d = d :=
    metricNativeAffineHarmonicExtension_eq_self_of_weak g₁ hg₁ d
      (radiusTwoSourceSolution_restriction_weak_harmonic g₁ hg₁ F hSupport)
  have hLocal := metricReplacement_energy_difference_eq_inner radiusTwoOpens ballOpens_le_radiusTwoOpens
    g₁ g₂ hg₁ hg₂ (memLp_radiusTwoMetricEnergyIntegrand g₁ hg₁)
    (memLp_radiusTwoMetricEnergyIntegrand g₂ hg₂) W z
  have hSecond := congrArg (fun v : BallH1 => TauCeti.PDE.energyFormH1
    (principalCoefficient g₂) 0 0 v v) hRestr
  have hFirst := congrArg (fun v : BallH1 => TauCeti.PDE.energyFormH1
    (principalCoefficient g₁) 0 0 v v) hFix.symm
  have hInner := congrArg₂ (fun s t : ℝ => s-t) hSecond hFirst
  have hDense := metricNativeAffineHarmonicExtension_self_energy_eq_of_minimalEnergy_eq g₁ g₂ hg₁ hg₂ hΛ d
  have hZero := hLocal.trans (hInner.trans (sub_eq_zero.mpr hDense))
  have hEquality := sub_eq_zero.mp hZero
  have hOuter := congrArg (fun v : RadiusTwoH1Zero => TauCeti.PDE.energyFormH1
    (principalCoefficient g₂) 0 0 (v : RadiusTwoH1) (v : RadiusTwoH1)) hShape
  exact hOuter.trans hEquality

lemma radiusTwoMetricInteriorReplacement_functional_eq
    (g₁ g₂ : MatrixField) (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (hΛ : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g₁ f = minimalEnergy g₂ f)
    (F : SmoothData) (hSupport : Function.support F.1 ⊆ (exteriorAnnulusOpens : Set R3)) :
    radiusTwoMetricSourceFunctional g₂ hg₂ F (radiusTwoMetricInteriorReplacement g₁ g₂ hg₁ hg₂ F) =
    radiusTwoMetricSourceFunctional g₁ hg₁ F (radiusTwoSourceSolution g₁ hg₁ (smoothRadiusTwoForcing F)) := by
  let W : RadiusTwoH1Zero := radiusTwoSourceSolution g₁ hg₁ (smoothRadiusTwoForcing F)
  let d : BallH1 := TauCeti.W1p.restrictL ballOpens_le_radiusTwoOpens (W : RadiusTwoH1)
  let z : BallH1Zero := metricNativeAffineReplacementCorrection g₁ g₂ hg₁ hg₂ d
  have hZero : ∀ᵐ x ∂(volume : Measure R3).restrict radiusTwoOpens,
      x ∈ (ballOpens : Set R3) → F.1 x = 0 :=
    Filter.Eventually.of_forall (exteriorSupportedSource_zero_on_ball F hSupport)
  have hSource := nativeZeroBoundaryReplacement_source_pairing_eq ballOpens radiusTwoOpens
    ballOpens_le_radiusTwoOpens W z F.1 hZero
  have hShape := congrArg (fun v : RadiusTwoH1Zero =>
    ∫ x in radiusTwoOpens, F.1 x * TauCeti.W1p.value (v : RadiusTwoH1) x ∂(volume : Measure R3))
      (radiusTwoMetricInteriorReplacement_eq_constructor g₁ g₂ hg₁ hg₂ F)
  have hPair := hShape.trans hSource
  have hEnergy := radiusTwoMetricInteriorReplacement_energy_eq g₁ g₂ hg₁ hg₂ hΛ F hSupport
  exact (radiusTwoMetricSourceFunctional_apply g₂ hg₂ F _).trans
    ((congrArg₂ (fun s t : ℝ => (1/2 : ℝ)*s-t) hEnergy hPair).trans
      (radiusTwoMetricSourceFunctional_apply g₁ hg₁ F W).symm)

lemma radiusTwoMetricInteriorReplacement_eq_second_solution
    (g₁ g₂ : MatrixField) (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (hΛ : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g₁ f = minimalEnergy g₂ f)
    (F : SmoothData) (hSupport : Function.support F.1 ⊆ (exteriorAnnulusOpens : Set R3)) :
    radiusTwoMetricInteriorReplacement g₁ g₂ hg₁ hg₂ F =
      radiusTwoSourceSolution g₂ hg₂ (smoothRadiusTwoForcing F) := by
  let W₁ : RadiusTwoH1Zero := radiusTwoSourceSolution g₁ hg₁ (smoothRadiusTwoForcing F)
  let W₂ : RadiusTwoH1Zero := radiusTwoSourceSolution g₂ hg₂ (smoothRadiusTwoForcing F)
  have hΛrev : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g₂ f = minimalEnergy g₁ f :=
    fun f hf => (hΛ f hf).symm
  have hForward := radiusTwoMetricInteriorReplacement_functional_eq g₁ g₂ hg₁ hg₂ hΛ F hSupport
  have hReverse := radiusTwoMetricInteriorReplacement_functional_eq g₂ g₁ hg₂ hg₁ hΛrev F hSupport
  have h21 : radiusTwoMetricSourceFunctional g₂ hg₂ F W₂ ≤ radiusTwoMetricSourceFunctional g₁ hg₁ F W₁ :=
    (radiusTwoMetricSourceFunctional_min g₂ hg₂ F _).trans (le_of_eq hForward)
  have h12 : radiusTwoMetricSourceFunctional g₁ hg₁ F W₁ ≤ radiusTwoMetricSourceFunctional g₂ hg₂ F W₂ :=
    (radiusTwoMetricSourceFunctional_min g₁ hg₁ F _).trans (le_of_eq hReverse)
  exact eq_radiusTwoSourceSolution_of_functional_eq g₂ hg₂ F _
    (hForward.trans (le_antisymm h12 h21))

lemma radiusTwoSourceSolution_common_exterior_value_ae
    (g₁ g₂ : MatrixField) (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (hΛ : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g₁ f = minimalEnergy g₂ f)
    (F : SmoothData) (hCompact : HasCompactSupport F.1)
    (hSupport : Function.support F.1 ⊆ (exteriorAnnulusOpens : Set R3)) :
    ∀ᵐ x ∂(volume : Measure R3).restrict exteriorAnnulusOpens,
      TauCeti.W1p.value (radiusTwoSourceSolution g₁ hg₁ (smoothRadiusTwoForcing F) : RadiusTwoH1) x =
      TauCeti.W1p.value (radiusTwoSourceSolution g₂ hg₂ (smoothRadiusTwoForcing F) : RadiusTwoH1) x := by
  let W : RadiusTwoH1Zero := radiusTwoSourceSolution g₁ hg₁ (smoothRadiusTwoForcing F)
  let d : BallH1 := TauCeti.W1p.restrictL ballOpens_le_radiusTwoOpens (W : RadiusTwoH1)
  let z : BallH1Zero := metricNativeAffineReplacementCorrection g₁ g₂ hg₁ hg₂ d
  have hOut := nativeZeroBoundaryReplacement_value_eq_outside ballOpens radiusTwoOpens
    ballOpens_le_radiusTwoOpens W z
  have hShape := congrArg (fun T : RadiusTwoH1Zero => ∀ᵐ x ∂(volume : Measure R3).restrict radiusTwoOpens,
    x ∉ (ballOpens : Set R3) → TauCeti.W1p.value (T : RadiusTwoH1) x =
      TauCeti.W1p.value (W : RadiusTwoH1) x)
    (radiusTwoMetricInteriorReplacement_eq_constructor g₁ g₂ hg₁ hg₂ F)
  have hActualOut := Eq.mp hShape.symm hOut
  have hSecond := congrArg (fun T : RadiusTwoH1Zero => ∀ᵐ x ∂(volume : Measure R3).restrict radiusTwoOpens,
    x ∉ (ballOpens : Set R3) → TauCeti.W1p.value (T : RadiusTwoH1) x =
      TauCeti.W1p.value (W : RadiusTwoH1) x)
    (radiusTwoMetricInteriorReplacement_eq_second_solution g₁ g₂ hg₁ hg₂ hΛ F hSupport)
  have hWhole := Eq.mp hSecond hActualOut
  have hAnn : ∀ᵐ x ∂(volume : Measure R3).restrict exteriorAnnulusOpens,
      x ∉ (ballOpens : Set R3) → TauCeti.W1p.value
        (radiusTwoSourceSolution g₂ hg₂ (smoothRadiusTwoForcing F) : RadiusTwoH1) x =
      TauCeti.W1p.value (W : RadiusTwoH1) x := hWhole.filter_mono
    (ae_mono (Measure.restrict_mono_set (volume : Measure R3)
      (SetLike.coe_subset_coe.mpr exteriorAnnulusOpens_le_radiusTwoOpens)))
  filter_upwards [hAnn,ae_restrict_mem exteriorAnnulusOpens.isOpen.measurableSet] with x hx hxMem
  have hxOut : x ∉ (ballOpens : Set R3) := by
    intro hxBall
    have hSmall : ‖x‖ < 1 := by
      change x ∈ Metric.ball (0 : R3) 1 at hxBall
      simpa only [Metric.mem_ball,dist_zero_right] using hxBall
    exact (not_lt_of_ge hSmall.le) hxMem.1
  exact (hx hxOut).symm

theorem radiusTwoSourceSolution_common_exterior_restriction
    (g₁ g₂ : MatrixField) (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (hΛ : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g₁ f = minimalEnergy g₂ f)
    (F : SmoothData) (hCompact : HasCompactSupport F.1)
    (hSupport : Function.support F.1 ⊆ (exteriorAnnulusOpens : Set R3)) :
    TauCeti.W1p.restrictL exteriorAnnulusOpens_le_radiusTwoOpens
      (radiusTwoSourceSolution g₁ hg₁ (smoothRadiusTwoForcing F) : RadiusTwoH1) =
    TauCeti.W1p.restrictL exteriorAnnulusOpens_le_radiusTwoOpens
      (radiusTwoSourceSolution g₂ hg₂ (smoothRadiusTwoForcing F) : RadiusTwoH1) := by
  apply TauCeti.W1p.ext_value
  apply Lp.ext
  have h₁ := TauCeti.W1p.value_restrictL_ae exteriorAnnulusOpens_le_radiusTwoOpens
    (radiusTwoSourceSolution g₁ hg₁ (smoothRadiusTwoForcing F) : RadiusTwoH1)
  have h₂ := TauCeti.W1p.value_restrictL_ae exteriorAnnulusOpens_le_radiusTwoOpens
    (radiusTwoSourceSolution g₂ hg₂ (smoothRadiusTwoForcing F) : RadiusTwoH1)
  have hEqual := radiusTwoSourceSolution_common_exterior_value_ae g₁ g₂ hg₁ hg₂ hΛ F hCompact hSupport
  filter_upwards [h₁,h₂,hEqual] with x hx₁ hx₂ hxEqual
  exact hx₁.trans (hxEqual.trans hx₂.symm)

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exteriorAnnulusOpens
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exteriorAnnulusOpens_le_radiusTwoOpens
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exteriorSupportedSource_zero_on_ball
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourceSolution_restriction_weak_harmonic
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoMetricInteriorReplacement
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoMetricInteriorReplacement_eq_constructor
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoMetricInteriorReplacement_restrict
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoMetricInteriorReplacement_energy_eq
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoMetricInteriorReplacement_functional_eq
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoMetricInteriorReplacement_eq_second_solution
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourceSolution_common_exterior_value_ae
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourceSolution_common_exterior_restriction
