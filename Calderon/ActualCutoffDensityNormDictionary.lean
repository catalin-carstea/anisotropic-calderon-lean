import Calderon.ActualOriginalDensitySourceNormShift
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open SphereHarmonic WeightedBaseSpectral
attribute [local irreducible] nativeDensitySphereL2L referenceBaseLift

theorem nativeDensitySphereL2L_apply_eq_original_zero_equiv
    (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics) (u:SphereSobolev (3/2:ℝ)):
    nativeDensitySphereL2L hO hD u=(sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) u) := by
  unfold nativeDensitySphereL2L
  rfl

theorem referenceBaseLift_original_cutoff_density_enorm_le_of_norm_le
    (g:MatrixField) (hg:IsAdmissibleMetric g) (L lambda D:ℝ)
    (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (chi:R3→ℝ) (hchi:ContDiff ℝ ∞ chi) (hchic:HasCompactSupport chi)
    (Psi:R3→SphereSobolev (3/2:ℝ)) (hPsi:ContDiff ℝ ∞ Psi)
    (hNorm:‖referenceBaseLift g hg L lambda (fun y=>chi y • nativeDensitySphereL2L hO hD (Psi y))
      (hchi.continuous.smul ((nativeDensitySphereL2L hO hD).continuous.comp hPsi.continuous)) hchic.smul_right‖ ≤ D):
    let V:R3→SphereL2 := fun y=>chi y • (sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) (Psi y))
    ∀ hV:Continuous V,∀ hVc:HasCompactSupport V,
      ‖referenceBaseLift g hg L lambda V hV hVc‖ₑ ≤ ENNReal.ofReal D := by
  intro V hV hVc
  unfold nativeDensitySphereL2L at hNorm
  change ‖referenceBaseLift g hg L lambda V hV hVc‖ ≤ D at hNorm
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hNorm

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
