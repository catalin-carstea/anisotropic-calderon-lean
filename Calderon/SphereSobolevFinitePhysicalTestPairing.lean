import Calderon.SharpRadialHarmonicCoefficientCore

set_option autoImplicit false
noncomputable section
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SpectralWeightedGraph SpectralCoreRegularity

/-! Full upfront: EXPANSION-v001.json. Probability-L2 finite test pairing with
an unrestricted full output; all Single1/physical coefficient0 conventions retained. -/

lemma inner_zeroEquiv_symm_finite_harmonic_test
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (U : SphereSobolev 0) (t : Finset ℕ) (v : ∀ m, harmonicSphereSubspace m) :
    ⟪(sphereSobolevZeroEquiv hO hD).symm U,
      (∑ m ∈ t, (v m : SphereL2))⟫_ℝ =
    ∑ m ∈ t, ⟪sphereSobolevCoefficientL 0 m U,v m⟫_ℝ := by
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro m _
  have hDecode : sphereHarmonicCoordinate hO hD m
      ((sphereSobolevZeroEquiv hO hD).symm U) = sphereSobolevCoefficientL 0 m U := by
    have h := sphereSobolevCoefficientL_zeroEquiv hO hD m
      ((sphereSobolevZeroEquiv hO hD).symm U)
    rw [LinearIsometryEquiv.apply_symm_apply] at h
    exact h.symm
  exact (inner_sphereHarmonicCoordinate_right hO hD m
    ((sphereSobolevZeroEquiv hO hD).symm U) (v m)).trans
      (congrArg (fun x : harmonicSphereSubspace m => ⟪x,v m⟫_ℝ) hDecode)

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.inner_zeroEquiv_symm_finite_harmonic_test
end OAI.AnisotropicCalderon.SphereHarmonic
