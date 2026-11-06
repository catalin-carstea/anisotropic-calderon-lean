import Calderon.ActualNativeCutoffHalfLift
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic ActualFiniteHarmonicCore ConnectionError ConformalDepth
attribute [local irreducible] referencePhysicalDensityOperator sphereSobolevInclusionL

theorem nativeNormalizedCutoffPhysicalOperator_eq_original_normalizedSource
    (hcalc:FixedSobolevCalculus) (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics)
    (hD:DenseSphereHarmonics) (tau0:UnitBallValueTrace) (S:KnownSideSourceData) (L:ℝ)
    (cover:NativeNormalCover S L) (chi:R3→ℝ) (lambda delta Rstar:ℝ) (p:ℕ)
    (Psi:R3→SphereSobolev (3/2:ℝ)) (i:Fin cover.count) (y:R3):
    nativeNormalizedCutoffPhysicalOperator hcalc hF hO hD tau0 S L cover chi lambda delta Rstar p Psi i y=
      referencePhysicalDensityOperator S.g1 L (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B
        (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho (cover.packet i).H (cover.packet i).a
        (cover.packet i).w (cover.packet i).native_data S.g1_admissible hcalc hF hO hD tau0 S.g2 lambda
        (referenceRadius delta Rstar p L) (normalizedThreeHalfSourceField chi Psi) y := by
  rfl

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
