import Calderon.BoundedAngularShift
import Calderon.NativeValueRadialTrace

/-! First radial correction on the completed sphere: the input-side spectral
coefficient, the degree-zero action and the positive lowering shift. -/
set_option autoImplicit false
noncomputable section
open MvPolynomial Set MeasureTheory
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic SphereHilbertDecomposition SpectralWeightedGraph
  BoundedSpectralMultiplier BoundedAngularShift AngularShiftGraph
  HarmonicDerivativeOperator SmoothSphereRotationProjection

def radialDriftWeight (k : ℕ) : ℝ := ((k : ℝ)+1)/(2*(k : ℝ)+1)

theorem abs_radialDriftWeight_le_one (k : ℕ) : |radialDriftWeight k| ≤ 1 := by
  have hd : 0 < 2*(k : ℝ)+1 := by positivity
  have hn : 0 ≤ (k : ℝ)+1 := by positivity
  rw [radialDriftWeight,abs_of_nonneg (div_nonneg hn hd.le)]
  apply (div_le_one (a := (k : ℝ)+1) (b := 2*(k : ℝ)+1) hd).mpr
  linarith [show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k]

def radialDriftMultiplier (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    SphereL2 →L[ℝ] SphereL2 :=
  boundedSpectralMultiplier hO hD radialDriftWeight 1 (by norm_num) abs_radialDriftWeight_le_one

theorem boundedSpectralMultiplier_single
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (w : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ k, |w k| ≤ C)
    (k : ℕ) (a : harmonicSphereSubspace k) :
    boundedSpectralMultiplier hO hD w C hC hw (a : SphereL2) = w k • (a : SphereL2) :=
  spectralGraph_output_unique hO hD w (a : SphereL2) _ _
    (boundedSpectralMultiplier_mem hO hD w C hC hw (a : SphereL2))
    (spectralGraph_single hO hD w k a)

theorem inverseDegreeMultiplier_single
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (k : ℕ) (a : harmonicSphereSubspace k) :
    inverseDegreeMultiplier hO hD (a : SphereL2) = inverseDegreeWeight k • (a : SphereL2) :=
  boundedSpectralMultiplier_single hO hD inverseDegreeWeight 1 (by norm_num)
    abs_inverseDegreeWeight_le_one k a

theorem radialDriftMultiplier_single
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (k : ℕ) (a : harmonicSphereSubspace k) :
    radialDriftMultiplier hO hD (a : SphereL2) = radialDriftWeight k • (a : SphereL2) :=
  boundedSpectralMultiplier_single hO hD radialDriftWeight 1 (by norm_num)
    abs_radialDriftWeight_le_one k a

theorem normalizedDerivative_single
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (i : Fin 3) (m : ℕ) (a : harmonicSphereSubspace (m+1)) :
    normalizedDerivative hF hO hD i (a : SphereL2) =
      inverseDegreeWeight (m+1) • (harmonicDerivative hF m i a : SphereL2) := by
  have hInput := normalizedDerivativeOutput_graph hF hO hD i (a : SphereL2)
  change (inverseDegreeMultiplier hO hD (a : SphereL2),
    normalizedDerivative hF hO hD i (a : SphereL2)) ∈ sphereDerivativeGraph hF hO hD i at hInput
  rw [inverseDegreeMultiplier_single hO hD (m+1) a] at hInput
  have hTarget := (sphereDerivativeGraph hF hO hD i).smul_mem (inverseDegreeWeight (m+1))
    (sphereDerivativeGraph_single hF hO hD i m a)
  exact sphereDerivativeGraph_output_unique hF hO hD i
    (inverseDegreeWeight (m+1) • (a : SphereL2)) _ _ hInput hTarget

theorem normalizedDerivative_constant
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (i : Fin 3) (a : harmonicSphereSubspace 0) :
    normalizedDerivative hF hO hD i (a : SphereL2) = 0 := by
  have hInput := normalizedDerivativeOutput_graph hF hO hD i (a : SphereL2)
  change (inverseDegreeMultiplier hO hD (a : SphereL2),
    normalizedDerivative hF hO hD i (a : SphereL2)) ∈ sphereDerivativeGraph hF hO hD i at hInput
  rw [inverseDegreeMultiplier_single hO hD 0 a] at hInput
  simp only [inverseDegreeWeight,Nat.cast_zero,add_zero,inv_one,one_smul] at hInput
  exact sphereDerivativeGraph_output_unique hF hO hD i (a : SphereL2) _ _ hInput
    (sphereDerivativeGraph_constant hF hO hD i a)

theorem normalizedDerivative_polynomial
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (i : Fin 3) (m : ℕ) (p : harmonicHomogeneous (m+1)) :
    normalizedDerivative hF hO hD i (polynomialSphereL2 p) =
      inverseDegreeWeight (m+1) • polynomialSphereL2 (MvPolynomial.pderiv i p) := by
  have h := normalizedDerivative_single hF hO hD i m (harmonicPolynomialSphereMap (m+1) p)
  rw [harmonicDerivative_apply_image] at h
  exact h

def radialDriftTraceL
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (d : R3) : SphereL2 →L[ℝ] SphereL2 :=
  -∑ i : Fin 3, (d i) • ((normalizedDerivative hF hO hD i).comp (radialDriftMultiplier hO hD))

theorem norm_radialDriftTraceL_le
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (d : R3) : ‖radialDriftTraceL hF hO hD d‖ ≤ 2 * ∑ i : Fin 3, |d i| := by
  have hW : ‖radialDriftMultiplier hO hD‖ ≤ 1 :=
    norm_boundedSpectralMultiplier_le hO hD radialDriftWeight 1 (by norm_num)
      abs_radialDriftWeight_le_one
  unfold radialDriftTraceL
  rw [norm_neg]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ i : Fin 3, |d i| * (2*1) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul,Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (norm_normalizedDerivative_le hF hO hD i) hW
          (norm_nonneg _) (by norm_num))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem radialDriftTraceL_constant
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (d : R3) (a : harmonicSphereSubspace 0) :
    radialDriftTraceL hF hO hD d (a : SphereL2) = 0 := by
  simp only [radialDriftTraceL,ContinuousLinearMap.neg_apply,sum_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    radialDriftMultiplier_single hO hD 0 a,map_smul,normalizedDerivative_constant hF hO hD,
    smul_zero,Finset.sum_const_zero,neg_zero]

theorem radialDriftTraceL_polynomial
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (d : R3) (m : ℕ) (p : harmonicHomogeneous (m+1)) :
    radialDriftTraceL hF hO hD d (polynomialSphereL2 p) =
      (-(2*((m+1 : ℕ) : ℝ)+1)⁻¹) •
        polynomialSphereL2 (GreenRadialTrace.driftDerivative (polynomialCoordinateMap d) p) := by
  let a : harmonicSphereSubspace (m+1) := harmonicPolynomialSphereMap (m+1) p
  have hW : radialDriftMultiplier hO hD (polynomialSphereL2 p) =
      radialDriftWeight (m+1) • polynomialSphereL2 p :=
    radialDriftMultiplier_single hO hD (m+1) a
  have hWeight : radialDriftWeight (m+1) * inverseDegreeWeight (m+1) =
      (2*((m+1 : ℕ) : ℝ)+1)⁻¹ := by
    unfold radialDriftWeight inverseDegreeWeight
    have h1 : (1+((m+1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have h2 : (2*((m+1 : ℕ) : ℝ)+1) ≠ 0 := by positivity
    field_simp [h1,h2]
    <;> ring
  have hAction (i : Fin 3) :
      (normalizedDerivative hF hO hD i).comp (radialDriftMultiplier hO hD)
        (polynomialSphereL2 p) =
      (2*((m+1 : ℕ) : ℝ)+1)⁻¹ • polynomialSphereL2 (MvPolynomial.pderiv i p) := by
    rw [ContinuousLinearMap.comp_apply,hW,map_smul,normalizedDerivative_polynomial,
      smul_smul,hWeight]
  simp only [radialDriftTraceL,ContinuousLinearMap.neg_apply,sum_apply,
    ContinuousLinearMap.smul_apply,hAction]
  rw [GreenRadialTrace.driftDerivative,map_sum]
  simp only [polynomialCoordinateMap_apply,← smul_eq_C_mul,map_smul]
  rw [Finset.smul_sum,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_smul,smul_smul,← neg_smul]
  congr 1
  ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
