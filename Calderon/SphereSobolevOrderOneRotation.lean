import Calderon.SmoothSphereRotationBounds
import Calderon.SphereSobolevInclusion
import Calderon.NativeFullSharpHalfTrace
import Mathlib.Analysis.Normed.Lp.lpHolder

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace Classical
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SmoothSphereRotation SmoothSphereRotationProjection SmoothSphereRotationBounds
  SmoothAngularCasimir SpectralCoreRegularity SpectralWeightedGraph NativeFullSharpHalfTrace
  DirichletFamily EnergyBridge

lemma norm_inverseDegree_harmonicSphereRotation_le (k : ℕ) (i j : Fin 3)
    (a : harmonicSphereSubspace k) :
    ‖(1+(k:ℝ))⁻¹ • harmonicSphereRotation k i j a‖ ≤ Real.sqrt 2*‖a‖ := by
  have hk : 0 < 1+(k:ℝ) := by positivity
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hk)]
  calc
    _ ≤ (1+(k:ℝ))⁻¹*(Real.sqrt 2*(1+(k:ℝ))*‖a‖) :=
      mul_le_mul_of_nonneg_left (norm_harmonicSphereRotation_le k i j a) (inv_nonneg.mpr hk.le)
    _ = _ := by field_simp [hk.ne'] <;> ring

def sphereSobolevRotationL (s : ℝ) (i j : Fin 3) :
    SphereSobolev s →L[ℝ] SphereSobolev (s-1) :=
  lp.mapCLM 2 (fun k : ℕ => (1+(k:ℝ))⁻¹ • harmonicSphereRotation k i j)
    (Real.sqrt_nonneg 2) (by
      intro k
      apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg 2)
      intro a
      exact norm_inverseDegree_harmonicSphereRotation_le k i j a)

lemma norm_sphereSobolevRotationL_le (s : ℝ) (i j : Fin 3) :
    ‖sphereSobolevRotationL s i j‖ ≤ Real.sqrt 2 := by
  unfold sphereSobolevRotationL
  exact lp.norm_mapCLM_le _ _ _ _

lemma besselWeight_rotation_decode (s : ℝ) (k : ℕ) :
    besselWeight (-(s-1)) k * (1+(k:ℝ))⁻¹ = besselWeight (-s) k := by
  unfold besselWeight
  rw [← Real.rpow_neg_one,← Real.rpow_add (by positivity : 0 < 1+(k:ℝ))]
  congr 1
  ring

lemma sphereSobolevCoefficientL_rotation
    (s : ℝ) (i j : Fin 3) (k : ℕ) (u : SphereSobolev s) :
    sphereSobolevCoefficientL (s-1) k (sphereSobolevRotationL s i j u) =
      harmonicSphereRotation k i j (sphereSobolevCoefficientL s k u) := by
  change besselWeight (-(s-1)) k • ((1+(k:ℝ))⁻¹ • harmonicSphereRotation k i j (u k)) =
    harmonicSphereRotation k i j (besselWeight (-s) k • u k)
  rw [map_smul,smul_smul,besselWeight_rotation_decode]

lemma sphereSobolevRotationL_nativeHalfTrace_smooth
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (f : SmoothData) (i j : Fin 3) :
    sphereSobolevRotationL (1/2 : ℝ) i j (nativeHalfTraceL hF hO hD τ0 (smoothSobolev f)) =
      sphereSobolevInclusionL 0 (-1/2 : ℝ) (by norm_num)
        (sphereSobolevZeroEquiv hO hD
          (smoothSphereLift (sphereRotationDerivative i j f.1)
            (contDiff_sphereRotationDerivative i j f.1 f.2))) := by
  apply sphereSobolev_ext (-1/2 : ℝ)
  intro k
  have hs : (1/2 : ℝ)-1 = -1/2 := by norm_num
  have hrot : sphereSobolevCoefficientL (-1/2 : ℝ) k
      (sphereSobolevRotationL (1/2 : ℝ) i j
        (nativeHalfTraceL hF hO hD τ0 (smoothSobolev f))) =
      harmonicSphereRotation k i j
        (sphereSobolevCoefficientL (1/2 : ℝ) k
          (nativeHalfTraceL hF hO hD τ0 (smoothSobolev f))) := by
    simpa only [sphereSobolevCoefficientL,hs] using
      sphereSobolevCoefficientL_rotation (1/2 : ℝ) i j k
        (nativeHalfTraceL hF hO hD τ0 (smoothSobolev f))
  rw [hrot,sphereSobolevCoefficientL_nativeHalfTraceL,
    sphereSobolevCoefficientL_inclusion,sphereSobolevCoefficientL_zeroEquiv,
    sphereHarmonicCoordinate_sphereRotationDerivative hO hD k i j f.1 f.2,τ0.valueTrace_smooth]
  rfl

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.norm_inverseDegree_harmonicSphereRotation_le
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevRotationL
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.norm_sphereSobolevRotationL_le
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.besselWeight_rotation_decode
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevCoefficientL_rotation
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevRotationL_nativeHalfTrace_smooth
