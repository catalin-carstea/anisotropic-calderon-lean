import Calderon.ActualTSFirstQuadraticScalarJets
import Calderon.ActualReferenceAngularCoefficientJets

/-! D01-owned successor of the preserved Transfer source-only scalar draft.
Before-code: ../scalar-UPFRONT.md and ../UPFRONT.md.
The cap proof is inherited from the Root-authored uncompiled draft. The
d01_scalar Codex agent authored the global smoothness lemma and namespace
repair; exact runtime model/version/effort are unexposed.
This scalar component does not itself prove the full original D01 estimate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped BigOperators ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroFirstScalarJets
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
  ActualReferenceAngularCoefficientJets ActualRetainedGeneratorMultiplierGains
  ActualReferenceZeroECommutators

/-- Original S-first scalar times one of the thirty original T-zero coefficients. -/
def zeroFirstWordWeight (g : MatrixField) (L : ℝ) (g2 : MatrixField)
    (q dr Ar : ℝ) (p : ℕ) (k j i : Fin 3) (V : Generator) (x : R3) : ℝ :=
  ((referenceRadius dr Ar p L x)^2*
    firstCoordinateWeight g g2 L k j (ActualHigherSFormation.higherSParam L dr Ar p q x))*
      referenceAngularZeroCoefficient g L q dr Ar p x i V

/-- Global smoothness of the actual coefficient is separate from its pointwise first jets. -/
theorem contDiff_zeroFirstWordWeight
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)
    (k j i : Fin 3) (V : Generator) :
    ContDiff ℝ ∞ (zeroFirstWordWeight g L g2 q dr Ar p k j i V) := by
  have hS : ContDiff ℝ ∞ (fun y =>
      firstCoordinateWeight g g2 L k j (ActualHigherSFormation.higherSParam L dr Ar p q y)) := by
    rw [physical_firstCoordinateWeight_eq_base]
    exact (contDiff_coordinateWeightBase g g2 hg hg2 L k j).comp
      (contDiff_const.prodMk contDiff_id)
  exact (((contDiff_referenceRadius_actual dr Ar p L hdr hAr).pow 2).mul hS).mul
    (contDiff_reference_angular_coefficient g hg L q dr Ar p hdr hAr i V)

/-- A positive constant controls every original D01 scalar first jet before all profiles. -/
theorem exists_actual_zero_first_word_scalar_first_caps
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (y0 : R3) (rho : ℝ) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ Cw : ℝ, 0 < Cw ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 →
      ∀ x ∈ closedBall y0 rho,
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      ∀ k j i : Fin 3, ∀ V : Generator,
      ScalarPointJet (zeroFirstWordWeight g L g2 q dr Ar p k j i V) x (Cw*eta) (Cw*eta) := by
  obtain ⟨Cc,hCc,hCoefficient⟩ := exists_reference_angular_coefficient_first_caps
    g hg L hL (closedBall y0 rho) (isCompact_closedBall _ _)
  let scalarWitness := exists_physical_firstCoordinateWeight_uniform_first_caps g g2 hg hg2 L y0 rho
  let Ms : ℝ := Classical.choose scalarWitness
  have hMs : 1 ≤ Ms := (Classical.choose_spec scalarWitness).1
  have hScalar := (Classical.choose_spec scalarWitness).2
  obtain ⟨J,hJ,hRadius⟩ := exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds
    g hg L hL (closedBall y0 rho) (isCompact_closedBall _ _) 1
  let Cw : ℝ := 1+(2*J+2)*Ms*Cc
  have hMs0 : 0 ≤ Ms := zero_le_one.trans hMs
  have hSC : 0 ≤ Ms*Cc := mul_nonneg hMs0 hCc.le
  have hCw : 0 < Cw := by dsimp only [Cw]; positivity
  have hC0 : Ms*Cc ≤ Cw := by
    dsimp only [Cw]
    nlinarith only [hSC,hJ,mul_nonneg hJ.le hSC]
  have hC1 : (2*J+2)*Ms*Cc ≤ Cw := by dsimp only [Cw]; linarith
  refine ⟨Cw,hCw,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hx hb hs k j i V
  let r : ℝ := referenceRadius dr Ar p L x
  let beta : ℝ := actualReferenceBeta g L q dr Ar p x
  have hr : 0 < r := referenceRadius_pos dr Ar p L x hdr hAr
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hb2 : (1 : ℝ) ≤ beta^2 := by nlinarith only [hb]
  have hb12 : beta ≤ beta^2 := by nlinarith only [hb]
  have hr1 : r ≤ 1 :=
    ((by simpa only [mul_one] using mul_le_mul_of_nonneg_left hb2 hr.le : r ≤ r*beta^2).trans hs).trans heta1
  have hSmall : r^2*beta^2 ≤ eta := by
    calc
      _ = r*(r*beta^2) := by ring
      _ ≤ r*eta := mul_le_mul_of_nonneg_left hs hr.le
      _ ≤ 1*eta := mul_le_mul_of_nonneg_right hr1 heta
      _ = eta := one_mul _
  have hR : ScalarPointJet (referenceRadius dr Ar p L) x r (J*r*beta) := by
    refine ⟨(contDiff_referenceRadius_actual dr Ar p L hdr hAr).contDiffAt.differentiableAt (by simp),?_,?_⟩
    · exact (abs_of_pos hr).le
    · simpa only [norm_iteratedFDeriv_one,pow_one,r,beta,actualReferenceBeta] using
        (hRadius q hq dr hdr hdr1 Ar hAr p hp x hx).1
  have hS0 := hScalar q hq x hx dr Ar p k j
  have hS : ScalarPointJet
      (fun y => firstCoordinateWeight g g2 L k j (ActualHigherSFormation.higherSParam L dr Ar p q y)) x Ms Ms :=
    ⟨hS0.1.contDiffAt.differentiableAt (by simp),hS0.2.1,hS0.2.2⟩
  have hCc0 := hCoefficient q hq dr hdr hdr1 Ar hAr p hp x hx hb i V
  have hC : ScalarPointJet (fun y => referenceAngularZeroCoefficient g L q dr Ar p y i V)
      x (Cc*beta) (Cc*beta^2) :=
    ⟨(contDiff_reference_angular_coefficient g hg L q dr Ar p hdr hAr i V).contDiffAt.differentiableAt (by simp),
      hCc0.1,hCc0.2⟩
  have hProd := ((hR.mul hR).mul hS).mul hC
  have hBetaScale : (Ms*Cc)*r^2*beta ≤ (Ms*Cc)*r^2*beta^2 :=
    mul_le_mul_of_nonneg_left hb12 (mul_nonneg hSC (sq_nonneg r))
  have hValue : ((r*r)*Ms)*(Cc*beta) ≤ Cw*eta := by
    calc
      _ = (Ms*Cc)*r^2*beta := by ring
      _ ≤ (Ms*Cc)*r^2*beta^2 := hBetaScale
      _ = (Ms*Cc)*(r^2*beta^2) := by ring
      _ ≤ Cw*(r^2*beta^2) := mul_le_mul_of_nonneg_right hC0 (mul_nonneg (sq_nonneg r) (sq_nonneg beta))
      _ ≤ Cw*eta := mul_le_mul_of_nonneg_left hSmall hCw.le
  have hDerivative :
      ((r*r)*Ms)*(Cc*beta^2)+(Cc*beta)*((r*r)*Ms+Ms*(r*(J*r*beta)+r*(J*r*beta))) ≤ Cw*eta := by
    calc
      _ = ((2*J+1)*Ms*Cc)*(r^2*beta^2)+(Ms*Cc)*r^2*beta := by ring
      _ ≤ ((2*J+2)*Ms*Cc)*(r^2*beta^2) := by nlinarith only [hBetaScale]
      _ ≤ Cw*(r^2*beta^2) := mul_le_mul_of_nonneg_right hC1 (mul_nonneg (sq_nonneg r) (sq_nonneg beta))
      _ ≤ Cw*eta := mul_le_mul_of_nonneg_left hSmall hCw.le
  unfold zeroFirstWordWeight
  simpa only [pow_two] using hProd.mono hValue hDerivative

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroFirstScalarJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroFirstScalarJets.contDiff_zeroFirstWordWeight
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroFirstScalarJets.exists_actual_zero_first_word_scalar_first_caps
