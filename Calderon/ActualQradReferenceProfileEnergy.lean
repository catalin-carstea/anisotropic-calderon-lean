import Calderon.FiniteCoreH1BesselNorm
import Calderon.ActualFiniteHarmonicModelHorizontalProfileIntegral
import Calderon.ActualHighRadialCommutatorGainCore
import Mathlib.MeasureTheory.Function.L1Space.Integrable
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic SpectralCoreRegularity SpectralWeightedGraph ActualFiniteHarmonicModel
  SectionFiveErrorForms DirichletFamily DirichletFamily.DriftBootstrap ReferenceDensityBounds ConformalDepth
  ReferenceWeightedApproximation

lemma beta_mul_norm_finiteCoreSobolevLift_threeHalf_sq_le_referenceProfileEnergy
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q beta : ℝ) (hb : 0 ≤ beta)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    beta*‖finiteCoreSobolevLift hO hD (3/2 : ℝ) F x‖^2 ≤
      finiteCoreReferenceProfileEnergy hO hD g hg L q beta F x := by
  rw [norm_finiteCoreSobolevLift hO hD (3/2 : ℝ) F x]
  have hHorizontal : 0 ≤ ∑ a : Fin 3,
      ‖(coreReferenceHorizontal hO hD g hg L q a F).val x‖^2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hOne : 0 ≤ beta^2*‖(coreWeightOperator hO hD (besselWeight 1) F).val x‖^2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hHalf : 0 ≤ beta⁻¹*(∑ a : Fin 3,
      ‖(coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
        (coreReferenceHorizontal hO hD g hg L q a F)).val x‖^2) :=
    mul_nonneg (inv_nonneg.mpr hb) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  unfold finiteCoreReferenceProfileEnergy sourceNormSquareIntegrand
  linarith

theorem integrable_referenceProfile_signed_radius_six_gain
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q δ A : ℝ) (p : ℕ)
    (hL : 0 < L) (hδ : 0 < δ) (hA : 0 < A) (hp : 1 ≤ p)
    (K : Set R3) (C theta : ℝ) (hC : 0 ≤ C) (hTheta : 0 ≤ theta) (hTheta1 : theta ≤ 1)
    (hBeta : ∀ y ∈ K, 1 ≤ actualReferenceBeta g L q δ A p y)
    (hSmall : ∀ y ∈ K,
      referenceRadius δ A p L y*(actualReferenceBeta g L q δ A p y)^2 ≤ theta)
    (F : smoothCompactFiniteSphereCore hO hD) (W : R3 → ℝ)
    (hW : AEStronglyMeasurable W (volume : Measure R3))
    (hZero : ∀ y, y ∉ K → W y = 0)
    (hBound : ∀ y ∈ K, |W y| ≤ C*(referenceRadius δ A p L y)^6*
      ‖finiteCoreSobolevLift hO hD (3/2 : ℝ) F y‖^2) :
    Integrable (fun y : R3 => referenceDensityFamily g L (q,y)*W y) ∧
    |∫ y : R3, referenceDensityFamily g L (q,y)*W y| ≤
      C*theta*(∫ y : R3, referenceDensityFamily g L (q,y)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q δ A p y) F y) := by
  let beta := actualReferenceBeta g L q δ A p
  let rho := fun y : R3 => referenceDensityFamily g L (q,y)
  let E := fun y : R3 => finiteCoreReferenceProfileEnergy hO hD g hg L q (beta y) F y
  have hbPos (y : R3) : 0 < beta y := actualReferenceBeta_pos g hg L q δ A p hL hδ hA hp y
  have hbCont : Continuous beta := continuous_actualReferenceBeta g hg L q δ A p hL hδ hA
  have hRho : Continuous rho := WeightedBaseSpectral.continuous_referenceBaseDensity g hg L q
  have hRhoNonneg (y : R3) : 0 ≤ rho y := (referenceDensityFamily_pos g hg L (q,y)).le
  have hENonneg (y : R3) : 0 ≤ E y :=
    finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q (beta y) (hbPos y).le F y
  have hEnergyInt : Integrable (fun y : R3 => rho y*E y) :=
    integrable_finiteCoreReferenceProfileEnergy hO hD g hg L q beta hbCont hbPos F
  have hPoint (y : R3) : ‖rho y*W y‖ ≤ C*theta*(rho y*E y) := by
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hRhoNonneg y)]
    by_cases hy : y ∈ K
    · have hPow := radial_pow_six_le_theta_mul_beta (referenceRadius δ A p L y) (beta y) theta
        (referenceRadius_pos δ A p L y hδ hA).le (hBeta y hy) (hSmall y hy) hTheta1
      have hHigh := beta_mul_norm_finiteCoreSobolevLift_threeHalf_sq_le_referenceProfileEnergy
        hO hD g hg L q (beta y) (hbPos y).le F y
      have hLocal : |W y| ≤ C*theta*E y := by
        calc
          _ ≤ C*(referenceRadius δ A p L y)^6*
              ‖finiteCoreSobolevLift hO hD (3/2 : ℝ) F y‖^2 := hBound y hy
          _ ≤ C*(theta*beta y)*‖finiteCoreSobolevLift hO hD (3/2 : ℝ) F y‖^2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPow hC) (sq_nonneg _)
          _ = C*theta*(beta y*‖finiteCoreSobolevLift hO hD (3/2 : ℝ) F y‖^2) := by ring
          _ ≤ C*theta*E y := mul_le_mul_of_nonneg_left hHigh (mul_nonneg hC hTheta)
      exact (mul_le_mul_of_nonneg_left hLocal (hRhoNonneg y)).trans_eq (by ring)
    · rw [hZero y hy,abs_zero,mul_zero]
      exact mul_nonneg (mul_nonneg hC hTheta) (mul_nonneg (hRhoNonneg y) (hENonneg y))
  have hMajor : Integrable (fun y : R3 => C*theta*(rho y*E y)) := hEnergyInt.const_mul (C*theta)
  have hInt : Integrable (fun y : R3 => rho y*W y) :=
    hMajor.mono' (hRho.aestronglyMeasurable.mul hW) (Filter.Eventually.of_forall hPoint)
  refine ⟨hInt,?_⟩
  have hNormIntegral := norm_integral_le_integral_norm (μ := (volume : Measure R3)) (fun y : R3 => rho y*W y)
  have hMono := integral_mono hInt.norm hMajor hPoint
  have hFinal : ‖∫ y : R3, rho y*W y‖ ≤ C*theta*(∫ y : R3, rho y*E y) :=
    hNormIntegral.trans (hMono.trans_eq (integral_const_mul _ _))
  simpa only [Real.norm_eq_abs] using hFinal
end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
