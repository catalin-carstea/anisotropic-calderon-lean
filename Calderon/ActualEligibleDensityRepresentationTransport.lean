import Calderon.ActualEligibleDensityKernelIndependence
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic ConnectionError ConformalDepth

theorem exists_uniform_native_density_representation_transport
    (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics) (tau0:UnitBallValueTrace) (S:KnownSideSourceData):
    ∃ lambda0:ℝ,0 < lambda0 ∧ ∀ (L:ℝ) (cover:NativeNormalCover S L)
      (lambda delta Rstar bound separation:ℝ) (p:ℕ)
      (K1 K2:ConstructedMixedKernel S L lambda delta Rstar bound separation p cover)
      (Psi:R3→SphereSobolev (3/2:ℝ)),
      0 < lambda → lambda ≤ lambda0 → lambda ≤ cover.dilationCeiling → 0 < delta → 0 < Rstar →
      (∀ y∈cylinder,referenceRadius delta Rstar p L y < cover.radiusCeiling) →
      RepresentsNativeMixedKernelDensity hO hD tau0 S L lambda delta Rstar bound separation p cover K1 Psi →
      RepresentsNativeMixedKernelDensity hO hD tau0 S L lambda delta Rstar bound separation p cover K2 Psi := by
  obtain ⟨lambda0,hlambda0,H⟩ := exists_uniform_constructedMixedKernel_sphere_germ_uniqueness S
  refine ⟨lambda0,hlambda0,?_⟩
  intro L cover lambda delta Rstar bound separation p K1 K2 Psi hlam hlam0 hlamRoom hd hRs hRadius hRep
  intro i y hy u hu
  have hFlux:=nativeMixedKernelWronskianFlux_eq_of_product_germs S L (cover.packet i) lambda
    K1.kernel K2.kernel u.1 y (referenceRadius delta Rstar p L y) y
    (H L cover lambda delta Rstar bound separation p K1 K2 hlam hlam0 hlamRoom hd hRs hRadius i y hy)
  exact (hRep i y hy u hu).trans hFlux

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
