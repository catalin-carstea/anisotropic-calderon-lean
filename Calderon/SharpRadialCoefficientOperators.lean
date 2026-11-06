import Calderon.SharpRadialHarmonicCoefficientCore
import Calderon.BoundedRadialDriftTrace

set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SpectralWeightedGraph DirichletFamily.DriftBootstrap

/-! Upfront expansion: EXPANSION-sharp-midpoint-coefficients-joint-v001.md, steps 6–7.
The degree multiplier is (1+k)-1 on decoded coefficients, not the raw lp identity. -/
lemma sphereCoefficient_one_add_smul_sub
    {V : Type*} [AddCommGroup V] [Module ℝ V] (c : ℝ) (v : V) :
    (1+c) • v - v = c • v := by
  rw [add_smul,one_smul]
  abel

def sphereSobolevDegreeL : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  (sphereSobolevBesselEquiv 1 1).toContinuousLinearEquiv.toContinuousLinearMap -
    sphereSobolevInclusionL 1 0 (by norm_num)

lemma sphereSobolevDegreeL_single (k : ℕ) (u : harmonicSphereSubspace k) :
    sphereSobolevDegreeL (sphereSobolevSingleL 1 k u) =
      (k : ℝ) • sphereSobolevSingleL 0 k u := by
  rw [sphereSobolevDegreeL,ContinuousLinearMap.sub_apply,sphereSobolevInclusionL_single]
  change besselWeight 1 k • lp.single (E := fun j : ℕ => ↥(harmonicSphereSubspace j)) 2 k u - besselWeight 0 k • lp.single (E := fun j : ℕ => ↥(harmonicSphereSubspace j)) 2 k u =
    (k : ℝ) • (besselWeight 0 k • lp.single (E := fun j : ℕ => ↥(harmonicSphereSubspace j)) 2 k u)
  simp only [besselWeight,Real.rpow_one,Real.rpow_zero,one_smul]
  exact sphereCoefficient_one_add_smul_sub (k : ℝ)
    (lp.single (E := fun j : ℕ => ↥(harmonicSphereSubspace j)) 2 k u)

def sphereSobolevFirstRadialDriftL (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (d : R3) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((radialDriftTraceL hF hO hD d).comp
      ((sphereSobolevZeroEquiv hO hD).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (sphereSobolevInclusionL 1 0 (by norm_num))))

lemma sphereSobolevFirstRadialDriftL_single (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (d : R3)
    (k : ℕ) (u : harmonicSphereSubspace k) :
    sphereSobolevFirstRadialDriftL hF hO hD d (sphereSobolevSingleL 1 k u) =
      sphereSobolevZeroEquiv hO hD (radialDriftTraceL hF hO hD d (u : SphereL2)) := by
  have hz : (sphereSobolevZeroEquiv hO hD).symm (sphereSobolevSingleL 0 k u) =
      (u : SphereL2) := by
    apply (sphereSobolevZeroEquiv hO hD).injective
    rw [LinearIsometryEquiv.apply_symm_apply,sphereSobolevZeroEquiv_harmonic_subtype]
  change sphereSobolevZeroEquiv hO hD (radialDriftTraceL hF hO hD d
    ((sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevSingleL 1 k u)))) = _
  rw [sphereSobolevInclusionL_single,hz]

end OAI.AnisotropicCalderon.SphereHarmonic
