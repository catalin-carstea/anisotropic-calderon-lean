import Calderon.ActualNativeMovingAdjointMixedJWeightedL2
import Calderon.ActualFiniteCoreSobolevRepresentation
import Calderon.FiniteCoreH1BesselNorm
import Calderon.ActualFiniteHarmonicModelHorizontalProfileIntegral

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore
  ActualFiniteHarmonicModel ReferenceDensityBounds ReferenceWeightedApproximation ConformalDepth
attribute [local irreducible] referenceNativeMovingAdjointParametricJ
  sphereSobolevInclusionL sphereSobolevZeroEquiv harmonicSphereSubspace

variable (g : MatrixField) (L : ℝ) (y0 : R3) (ρ : ℝ)
  (hg : IsAdmissibleMetric g) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

/-- The genuine mixed correction is small relative to profile energy after a cofinal beta choice. -/
theorem exists_referenceNativeMixedJ_uniform_profile_energy_bound
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (hL : 0 < L) :
    ∃ CJ : ℝ, 0 < CJ ∧ ∀ hreg : FixedDirichletRegularity,
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ δ A : ℝ, ∀ p : ℕ,
      ∀ hδ : 0 < δ, ∀ hA : 0 < A, 1 ≤ p →
      ∀ betaMin : ℝ, 1 ≤ betaMin →
      ∀ F : smoothCompactFiniteSphereCore hO hD,
      (∀ y ∈ tsupport F.val,
        ‖y-y0‖ ≤ ρ ∧ ‖fderiv ℝ (referenceRadius δ A p L) y‖ ≤ 1 ∧
          betaMin ≤ actualReferenceBeta g L q δ A p y) →
      let R := referenceRadius δ A p L
      let u := finiteCoreSobolevLift hO hD (3/2 : ℝ) F
      let j := fun y : R3 => (sphereSobolevZeroEquiv hO hD).symm
        (referenceNativeMovingAdjointParametricJ hF hO hD g g2 L ((q,y),fderiv ℝ R y)
          (sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num) (u y)))
      betaMin^2 * (∫ y : R3, referenceDensityFamily g L (q,y)*‖j y‖^2) ≤
        CJ * (∫ y : R3, referenceDensityFamily g L (q,y)*
          finiteCoreReferenceProfileEnergy hO hD g hg L q
            (actualReferenceBeta g L q δ A p y) F y) := by
  obtain ⟨CJ,hCJ,hBound⟩ :=
    exists_referenceNativeMovingAdjointParametricJ_uniform_bound
      hF hO hD g g2 hg hg2 L (closedBall y0 ρ) (isCompact_closedBall _ _)
  refine ⟨CJ^2,by positivity,?_⟩
  intro hreg q hq δ A p hδ hA hp betaMin hMin F hRoom R u j
  have hR : ContDiff ℝ ∞ R :=
    ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δ A p L hδ hA
  have hRep := finiteCoreSobolevLift_representation hO hD (3/2 : ℝ) (by norm_num) F
  have hRoomU (y : R3) (hy : y ∈ tsupport u) :
      ‖y-y0‖ ≤ ρ ∧ ‖fderiv ℝ R y‖ ≤ 1 := by
    have h := hRoom y (hRep.2.2.1 hy)
    exact ⟨h.1,h.2.1⟩
  let beta : R3 → ℝ := actualReferenceBeta g L q δ A p
  let U : R3 → SphereSobolev 1 := fun y =>
    sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num) (u y)
  have hPreparation := referenceNativeMovingAdjointParametricJ_lift_smooth_compact
    hF hO hD g g2 hg hg2 L q R hR u hRep.1 hRep.2.1
  have hU : ContDiff ℝ ∞ U := hPreparation.1
  have hjSmooth : ContDiff ℝ ∞ j := hPreparation.2.2.2.1
  have hjCompact : HasCompactSupport j := hPreparation.2.2.2.2.2.1
  have hRho : Continuous (fun y : R3 => referenceDensityFamily g L (q,y)) :=
    WeightedBaseSpectral.continuous_referenceBaseDensity g hg L q
  have hjInt := integrable_weighted_norm_sq_of_continuous_compact
    (fun y : R3 => referenceDensityFamily g L (q,y)) hRho j
    hjSmooth.continuous hjCompact
  have hUInt := integrable_weighted_norm_sq_of_continuous_compact
    (fun y : R3 => referenceDensityFamily g L (q,y)) hRho U
    hU.continuous hPreparation.2.2.1
  have hJPoint (y : R3) : ‖j y‖ ≤ CJ*‖U y‖ := by
    by_cases hy : y ∈ tsupport u
    · have hBall : y ∈ closedBall y0 ρ := by
        simpa only [mem_closedBall,dist_eq_norm] using (hRoomU y hy).1
      have hOp := hBound q hq y hBall (fderiv ℝ R y) (hRoomU y hy).2
      calc
        ‖j y‖ = ‖referenceNativeMovingAdjointParametricJ hF hO hD g g2 L
            ((q,y),fderiv ℝ R y) (U y)‖ :=
          norm_sphereSobolevZeroEquiv_symm_apply hO hD _
        _ ≤ ‖referenceNativeMovingAdjointParametricJ hF hO hD g g2 L
            ((q,y),fderiv ℝ R y)‖*‖U y‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ CJ*‖U y‖ := mul_le_mul_of_nonneg_right hOp (norm_nonneg _)
    · have hu0 : u y = 0 := image_eq_zero_of_notMem_tsupport hy
      simpa only [j,U,hu0,map_zero,norm_zero,mul_zero] using (le_rfl : (0 : ℝ) ≤ 0)
  have hjBound : (∫ y : R3, referenceDensityFamily g L (q,y)*‖j y‖^2) ≤
      CJ^2*(∫ y : R3, referenceDensityFamily g L (q,y)*‖U y‖^2) := by
    rw [← integral_const_mul]
    apply integral_mono hjInt (hUInt.const_mul (CJ^2))
    intro y
    have hSquare : ‖j y‖^2 ≤ CJ^2*‖U y‖^2 := by
      have h := (sq_le_sq₀ (norm_nonneg (j y))
        (mul_nonneg hCJ.le (norm_nonneg (U y)))).2 (hJPoint y)
      simpa only [mul_pow] using h
    have h := mul_le_mul_of_nonneg_left hSquare
      (referenceDensityFamily_pos g hg L (q,y)).le
    exact h.trans_eq (mul_left_comm _ _ _)
  have hBeta (y : R3) : 0 < beta y :=
    actualReferenceBeta_pos g hg L q δ A p hL hδ hA hp y
  have hBetaCont : Continuous beta :=
    continuous_actualReferenceBeta g hg L q δ A p hL hδ hA
  have hEnergyInt := integrable_finiteCoreReferenceProfileEnergy
    hO hD g hg L q beta hBetaCont hBeta F
  have hPoint (y : R3) : betaMin^2*‖U y‖^2 ≤
      finiteCoreReferenceProfileEnergy hO hD g hg L q (beta y) F y := by
    by_cases hy : y ∈ tsupport u
    · have hMinY := (hRoom y (hRep.2.2.1 hy)).2.2
      have hSq : betaMin^2 ≤ (beta y)^2 :=
        (sq_le_sq₀ (by linarith : 0 ≤ betaMin) (hBeta y).le).2 hMinY
      calc
        _ ≤ (beta y)^2*‖U y‖^2 := mul_le_mul_of_nonneg_right hSq (sq_nonneg _)
        _ ≤ _ := beta_sq_mul_norm_finiteCoreSobolevLift_one_le_referenceProfileEnergy
          hO hD g hg L q (beta y) (hBeta y).le F y
    · have hu0 : u y = 0 := image_eq_zero_of_notMem_tsupport hy
      have hU0 : U y = 0 := by simp only [U,hu0,map_zero]
      rw [hU0,norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),mul_zero]
      exact finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q (beta y) (hBeta y).le F y
  have hWeighted (y : R3) : betaMin^2*(referenceDensityFamily g L (q,y)*‖U y‖^2) ≤
      referenceDensityFamily g L (q,y)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (beta y) F y := by
    have h := mul_le_mul_of_nonneg_left (hPoint y)
      (referenceDensityFamily_pos g hg L (q,y)).le
    exact (mul_left_comm _ _ _).trans_le h
  have hIntegral : betaMin^2 * (∫ y : R3, referenceDensityFamily g L (q,y)*‖U y‖^2) ≤
      ∫ y : R3, referenceDensityFamily g L (q,y)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (beta y) F y := by
    rw [← integral_const_mul]
    exact integral_mono (hUInt.const_mul (betaMin^2)) hEnergyInt hWeighted
  calc
    _ ≤ betaMin^2*(CJ^2*(∫ y : R3, referenceDensityFamily g L (q,y)*‖U y‖^2)) :=
      mul_le_mul_of_nonneg_left hjBound (sq_nonneg betaMin)
    _ = CJ^2*(betaMin^2*(∫ y : R3, referenceDensityFamily g L (q,y)*‖U y‖^2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hIntegral (sq_nonneg CJ)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceNativeMixedJ_uniform_profile_energy_bound
