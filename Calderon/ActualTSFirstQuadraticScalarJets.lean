import Calderon.ActualTFirstNegativeGraph
import Calderon.ActualHigherSMixedWordScalarUniformCaps

/-! Actual frame-weighted original207 quadratic-word scalar first jets.
Only the scalar coefficient data are treated here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped BigOperators ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstQuadraticScalarJets
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualTFirstPhysicalDictionary ActualTZeroNegativeGraph ActualFiniteHarmonicCore
  ActualFiniteCoreLoweringRealization ActualHigherSPhysicalPairing AmbientReferenceRaising
  SmoothMetricFrame MovingFrameConnection ReferenceDensityBounds ConformalDepth
  FixedParameterProfilePullback FixedParameterProfileBudgets
  ActualTSPrincipalCoefficients ActualTSPrincipalGreen ActualHigherSCoordinateWeightBounds
  ActualHigherSLeadingBracketGain ActualTSPrincipalPhysicalGreen ActualTSPrincipalAngularCaps
  ActualScalarPrincipalAdjoint ActualHigherSScalarCommutatorForm ActualScalarPrincipalSelfFormBound
  ActualHigherSScalarCommutatorNativeForm ActualMixedAngularPairedGains
  ActualPiJacobiRadialGainedRows ActualJacobiAngularGainedRows
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier
  ActualHigherSMixedWordScalarJets ActualHigherSQuadraticZeroWords ReferenceWeightedApproximation

/-- Exact original first-T frame component times one unchanged quadratic S word coefficient. -/
def firstQuadraticWordWeight (g : MatrixField) (L : ℝ) (g2 : MatrixField)
    (q dr Ar : ℝ) (p : ℕ) (i l : Fin 3) (z : ZeroWord) (x : R3) : ℝ :=
  referenceMetricGramFrame g L (q,x) i l*actualWordCoefficient g L g2 dr Ar p q x z

attribute [local irreducible] actualWordCoefficient referenceMetricGramFrame actualReferenceBeta

/-- One constant controls genuine actual first jets of every ordered word before all profiles. -/
theorem exists_actual_first_quadratic_word_scalar_first_caps
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (y0 : R3) (rho : ℝ) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ Cscalar : ℝ, 0 < Cscalar ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 →
      ∀ x ∈ closedBall y0 rho,
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      ∀ i l : Fin 3, ∀ z : ZeroWord,
      ScalarPointJet (firstQuadraticWordWeight g L g2 q dr Ar p i l z) x
        (Cscalar*eta) (Cscalar*eta*actualReferenceBeta g L q dr Ar p x) := by
  let frameCap := exists_metricFrame_uniform_first_caps g hg L y0 rho
  let Mf : ℝ := Classical.choose frameCap
  have hMf : 1 ≤ Mf := (Classical.choose_spec frameCap).1
  have hFrame := (Classical.choose_spec frameCap).2
  let wordCap := exists_actual_mixed_word_scalar_first_caps g hg L hL y0 rho g2 hg2
  let Cw : ℝ := Classical.choose wordCap
  have hCw : 0 < Cw := (Classical.choose_spec wordCap).1
  have hWords := (Classical.choose_spec wordCap).2
  let Cscalar : ℝ := 2*Mf*Cw+1
  have hMf0 : 0 ≤ Mf := zero_le_one.trans hMf
  have hMC : 0 ≤ Mf*Cw := mul_nonneg hMf0 hCw.le
  have hCscalar : 0 < Cscalar := by dsimp only [Cscalar]; positivity
  have hMC0 : Mf*Cw ≤ Cscalar := by dsimp only [Cscalar]; nlinarith only [hMC]
  have hMC2 : 2*Mf*Cw ≤ Cscalar := by dsimp only [Cscalar]; linarith
  refine ⟨Cscalar,hCscalar,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hx hb hs i l z
  let r := referenceRadius dr Ar p L x
  let beta := actualReferenceBeta g L q dr Ar p x
  have hr : 0 ≤ r := (referenceRadius_pos dr Ar p L x hdr hAr).le
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hrEta : r ≤ eta := by
    calc
      r = r*1 := (mul_one r).symm
      _ ≤ r*beta^2 := mul_le_mul_of_nonneg_left (by nlinarith only [hb] : (1:ℝ)≤beta^2) hr
      _ ≤ eta := hs
  have hF : ScalarPointJet (fun y => referenceMetricGramFrame g L (q,y) i l) x Mf Mf :=
    ⟨((hFrame q hq x hx i l).1.contDiffAt).differentiableAt (by simp),
      (hFrame q hq x hx i l).2.1,(hFrame q hq x hx i l).2.2⟩
  have hW := (hWords q hq dr hdr hdr1 Ar hAr p hp x hx hb (hs.trans heta1)).1 z
  have hProd := hF.mul hW
  have hValue : Mf*(Cw*r) ≤ Cscalar*eta := by
    calc
      _ = (Mf*Cw)*r := by ring
      _ ≤ (Mf*Cw)*eta := mul_le_mul_of_nonneg_left hrEta hMC
      _ ≤ _ := mul_le_mul_of_nonneg_right hMC0 heta
  have hDeriv : Mf*(Cw*r*beta)+(Cw*r)*Mf ≤ Cscalar*eta*beta := by
    have hScale : (Mf*Cw)*r ≤ (Mf*Cw)*eta := mul_le_mul_of_nonneg_left hrEta hMC
    have hBetaScale : (Mf*Cw)*eta ≤ (Mf*Cw)*eta*beta := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (mul_nonneg hMC heta)
    calc
      _ = (Mf*Cw)*r*beta+(Mf*Cw)*r := by ring
      _ ≤ (Mf*Cw)*eta*beta+(Mf*Cw)*eta*beta :=
        add_le_add (mul_le_mul_of_nonneg_right hScale hb0) (hScale.trans hBetaScale)
      _ = (2*Mf*Cw)*eta*beta := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMC2 heta) hb0
  unfold firstQuadraticWordWeight
  exact hProd.mono hValue hDeriv

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstQuadraticScalarJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstQuadraticScalarJets.exists_actual_first_quadratic_word_scalar_first_caps
