import Calderon.NativePrincipalSmoothFluxDictionary
import Calderon.HalfGaugeCompactCollar
import Calderon.HalfGaugedWeakPoleIdentity
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator MetricVolume DirichletFamily DirichletFamily.DriftBootstrap NativePolynomialBulkMoments

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referencePhysicalHalfGaugeResidualZero (p : ℝ × (R3 × ℝ)) : BallSobolev 0 :=
  actualReferenceHalfGaugedResidualLpFamily g hg L y0 Φ B ε C ρ H a w hData
    coefficientSpatialBump coefficientSpatialBump.contDiff coefficientSpatialBump.hasCompactSupport sphereSurfaceMass⁻¹ 1 p

variable (hcalc : FixedSobolevCalculus)
    (θ ζ : R3 → ℝ) (hθ : ContDiff ℝ ∞ θ) (hζ : ContDiff ℝ ∞ ζ) (hCompact : HasCompactSupport θ)
    (b : ℝ) (hb : 0 < b) (hZero : ∀ z ∈ ball (0 : R3) b, ζ z = 0)

def referencePhysicalHalfGaugeCollarForcing (p : ℝ × (R3 × ℝ)) : BallSobolev 0 :=
  referencePhysicalHalfGaugeResidualZero g hg L y0 Φ B ε C ρ H a w hData p -
    ordinaryPrincipalL hcalc 0
      (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 p)
      (referencePhysicalHalfGaugeCollarSobolev 2 g hg L y0 Φ B ε C ρ H a w hData
        θ ζ hθ hζ hCompact b hb hZero sphereSurfaceMass⁻¹ p)

def referencePhysicalHalfGaugeCollarCorrection (p : ℝ × (R3 × ℝ)) : StrongDirichletSpace 0 :=
  (strongDirichletOperator hcalc 0
    (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 p)).inverse
      (referencePhysicalHalfGaugeCollarForcing g hg L y0 Φ B ε C ρ H a w hData hcalc
        θ ζ hθ hζ hCompact b hb hZero p)

include hg hData in
theorem contDiff_referencePhysicalHalfGaugeResidualZero :
    ContDiff ℝ ∞ (referencePhysicalHalfGaugeResidualZero g hg L y0 Φ B ε C ρ H a w hData) := by
  exact contDiff_actualReferenceHalfGaugedResidualLpFamily g hg L y0 Φ B ε C ρ H a w hData
    coefficientSpatialBump coefficientSpatialBump.contDiff coefficientSpatialBump.hasCompactSupport sphereSurfaceMass⁻¹ 1
include hg hData hcalc in
theorem contDiff_referencePhysicalHalfGaugeCollarForcing :
    ContDiff ℝ ∞ (referencePhysicalHalfGaugeCollarForcing g hg L y0 Φ B ε C ρ H a w hData hcalc
      θ ζ hθ hζ hCompact b hb hZero) := by
  exact (contDiff_referencePhysicalHalfGaugeResidualZero g hg L y0 Φ B ε C ρ H a w hData).sub
    ((contDiff_referencePhysicalGauge_fullPrincipal g hg L y0 Φ B ε C ρ H a w hData hcalc 0).clm_apply
      (contDiff_referencePhysicalHalfGaugeCollarSobolev g hg L y0 Φ B ε C ρ H a w hData hcalc 2
        θ ζ hθ hζ hCompact b hb hZero sphereSurfaceMass⁻¹))
include hg hData hcalc in
theorem contDiff_referencePhysicalHalfGaugeCollarCorrection (hreg : FixedDirichletRegularity) :
    ContDiff ℝ ∞ (referencePhysicalHalfGaugeCollarCorrection g hg L y0 Φ B ε C ρ H a w hData hcalc
      θ ζ hθ hζ hCompact b hb hZero) := by
  have hOp : ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) => strongDirichletOperator hcalc 0 (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 p)) := by
    have hEq : (fun p : ℝ × (R3 × ℝ) => strongDirichletOperator hcalc 0 (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 p)) =
        (fun p => (ordinaryPrincipalL hcalc 0 (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 p)).comp (strongDirichletSubmodule 0).toSubmodule.subtypeL) :=
      funext (fun p => (ordinaryPrincipalL_restriction hcalc 0 (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 p)).symm)
    rw [hEq]
    exact (contDiff_referencePhysicalGauge_fullPrincipal g hg L y0 Φ B ε C ρ H a w hData hcalc 0).clm_comp contDiff_const
  have hInv : ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) => (strongDirichletOperator hcalc 0 (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 p)).inverse) :=
    contDiffOn_univ.mp (contDiffOn_banachInverseFamily _ Set.univ hOp.contDiffOn
      (fun p _ => referencePhysicalGaugePrincipal_isInvertible g hg L y0 Φ B ε C ρ H a w hData hcalc hreg 0 p))
  exact hInv.clm_apply (contDiff_referencePhysicalHalfGaugeCollarForcing g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero)
include hg hData hcalc in
theorem referencePhysicalHalfGaugeCollarCorrection_equation (hreg : FixedDirichletRegularity)
    (p : ℝ × (R3 × ℝ)) :
    ordinaryPrincipalL hcalc 0
      (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 p)
      (referencePhysicalHalfGaugeCollarCorrection g hg L y0 Φ B ε C ρ H a w hData hcalc
        θ ζ hθ hζ hCompact b hb hZero p : BallSobolev 2) =
      referencePhysicalHalfGaugeCollarForcing g hg L y0 Φ B ε C ρ H a w hData hcalc
        θ ζ hθ hζ hCompact b hb hZero p := by
  change ((ordinaryPrincipalL hcalc 0 (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 p)).comp
    (strongDirichletSubmodule 0).toSubmodule.subtypeL)
      ((strongDirichletOperator hcalc 0 (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 p)).inverse (referencePhysicalHalfGaugeCollarForcing g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero p)) = _
  rw [ordinaryPrincipalL_restriction]
  exact (referencePhysicalGaugePrincipal_isInvertible g hg L y0 Φ B ε C ρ H a w hData hcalc hreg 0 p).self_apply_inverse _
include hg hData hcalc in
theorem exists_compact_uniform_referencePhysicalHalfGaugeCollarForcing_bound
    (K : Set (ℝ × (R3 × ℝ))) (hK : IsCompact K) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ p ∈ K,
      ‖referencePhysicalHalfGaugeCollarForcing g hg L y0 Φ B ε C ρ H a w hData hcalc
        θ ζ hθ hζ hCompact b hb hZero p‖ ≤ C0 := by
  obtain ⟨C0,hC0⟩ := hK.exists_bound_of_continuousOn
    (contDiff_referencePhysicalHalfGaugeCollarForcing g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero).continuous.continuousOn
  exact ⟨max C0 1,le_max_right _ _,fun p hp => (hC0 p hp).trans (le_max_left _ _)⟩
include hg hData hcalc in
theorem exists_compact_uniform_referencePhysicalHalfGaugeCollarCorrection_bound
    (hreg : FixedDirichletRegularity) (K : Set (ℝ × (R3 × ℝ))) (hK : IsCompact K) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ p ∈ K,
      ‖referencePhysicalHalfGaugeCollarCorrection g hg L y0 Φ B ε C ρ H a w hData hcalc
        θ ζ hθ hζ hCompact b hb hZero p‖ ≤ C0 := by
  obtain ⟨C0,hC0⟩ := hK.exists_bound_of_continuousOn
    (contDiff_referencePhysicalHalfGaugeCollarCorrection g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero hreg).continuous.continuousOn
  exact ⟨max C0 1,le_max_right _ _,fun p hp => (hC0 p hp).trans (le_max_left _ _)⟩
include hg hData in
theorem referencePhysicalHalfGaugeResidualZero_ae_profile (p : ℝ × (R3 × ℝ)) :
    TauCeti.Wkp.value 0 (referencePhysicalHalfGaugeResidualZero g hg L y0 Φ B ε C ρ H a w hData p)
      =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun z => halfGaugeResidualRatio (referencePhysicalHalfGauge g L Φ) (p,z) *
          normalCoefficientResidualProfile a sphereSurfaceMass⁻¹ (p,z) +
        (inverseNormPotential sphereSurfaceMass⁻¹ z / referencePhysicalHalfGauge g L Φ (p,0)) *
          scalarCoefficientPotential a (referencePhysicalHalfGauge g L Φ) (p,z)) := by
  have hOne : ∀ z ∈ ball (0 : R3) 1, coefficientSpatialBump z = 1 := by
    intro z hz
    have hn : ‖z‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hz
    exact coefficientSpatialBump_eq_one z hn.le
  have hAE := halfGaugedNormalResidualLpFamily_ae_profile
    a hData.1.2.2.2.2.2.2.2.2.1 (referencePhysicalHalfGauge g L Φ)
    (contDiff_referencePhysicalHalfGauge g hg L y0 Φ B ε C ρ H a w hData)
    (fun x => (referencePhysicalHalfGauge_pos g L Φ x).ne')
    coefficientSpatialBump coefficientSpatialBump.contDiff coefficientSpatialBump.hasCompactSupport
    sphereSurfaceMass⁻¹ 1 hOne p
  rw [TauCeti.Wkp.value_zero]
  exact hAE
include hg hData hcalc in
theorem ordinaryPrincipalL_referencePhysicalHalfGaugeCollarSobolev_value_ae
    (p : ℝ × (R3 × ℝ)) :
    TauCeti.Wkp.value 0 (ordinaryPrincipalL hcalc 0
      (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 p)
      (referencePhysicalHalfGaugeCollarSobolev 2 g hg L y0 Φ B ε C ρ H a w hData
        θ ζ hθ hζ hCompact b hb hZero sphereSurfaceMass⁻¹ p))
      =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun z => -coordinateFluxDivergence
        (fun x => matrixOperatorMap (referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H (p,x))
          (gradient (fun y => referencePhysicalHalfGaugeCollarField g L Φ θ ζ sphereSurfaceMass⁻¹ (p,y)) x)) z) := by
  let f : SmoothData := ⟨fun z => referencePhysicalHalfGaugeCollarField g L Φ θ ζ sphereSurfaceMass⁻¹ (p,z),
    (contDiff_referencePhysicalHalfGaugeCollarField g hg L y0 Φ B ε C ρ H a w hData θ ζ hθ hζ hCompact b hb hZero sphereSurfaceMass⁻¹).comp
      (contDiff_const.prodMk contDiff_id)⟩
  have hAE := ordinaryPrincipalL_smoothBallSobolev_value_ae_coordinateFlux hcalc 0 (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 p) f
  rw [coefficientMatrixField_referencePhysicalGaugeCoefficientJets] at hAE
  exact hAE
include hg hData hcalc in
theorem referencePhysicalHalfGaugeCollarForcing_value_ae (p : ℝ × (R3 × ℝ)) :
    TauCeti.Wkp.value 0
      (referencePhysicalHalfGaugeCollarForcing g hg L y0 Φ B ε C ρ H a w hData hcalc
        θ ζ hθ hζ hCompact b hb hZero p)
      =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun z => (halfGaugeResidualRatio (referencePhysicalHalfGauge g L Φ) (p,z) *
          normalCoefficientResidualProfile a sphereSurfaceMass⁻¹ (p,z) +
        (inverseNormPotential sphereSurfaceMass⁻¹ z / referencePhysicalHalfGauge g L Φ (p,0)) *
          scalarCoefficientPotential a (referencePhysicalHalfGauge g L Φ) (p,z)) -
        (-coordinateFluxDivergence
          (fun x => matrixOperatorMap (referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H (p,x))
            (gradient (fun y => referencePhysicalHalfGaugeCollarField g L Φ θ ζ sphereSurfaceMass⁻¹ (p,y)) x)) z)) := by
  let P0 : BallSobolev 0 := ordinaryPrincipalL hcalc 0 (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 p) (referencePhysicalHalfGaugeCollarSobolev 2 g hg L y0 Φ B ε C ρ H a w hData θ ζ hθ hζ hCompact b hb hZero sphereSurfaceMass⁻¹ p)
  filter_upwards [Lp.coeFn_sub (referencePhysicalHalfGaugeResidualZero g hg L y0 Φ B ε C ρ H a w hData p) P0,
    referencePhysicalHalfGaugeResidualZero_ae_profile g hg L y0 Φ B ε C ρ H a w hData p,
    ordinaryPrincipalL_referencePhysicalHalfGaugeCollarSobolev_value_ae g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero p] with z hSub hFq hP
  change (referencePhysicalHalfGaugeResidualZero g hg L y0 Φ B ε C ρ H a w hData p - P0) z = _
  simp only [Pi.sub_apply] at hSub
  rw [TauCeti.Wkp.value_zero] at hFq hP
  rw [hSub,hFq,hP]
end OAI.AnisotropicCalderon.ConnectionError
