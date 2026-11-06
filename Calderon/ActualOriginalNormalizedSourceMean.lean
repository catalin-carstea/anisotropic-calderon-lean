import Calderon.ActualOriginalDensitySourceNormShift
import Calderon.ActualAnyEligiblePsiMeanZero
import Calderon.ActualEligibleDensityRepresentationTransport
set_option autoImplicit false
noncomputable section
open Set Metric MvPolynomial
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic ConnectionError ConformalDepth ActualFiniteHarmonicCore
attribute [local irreducible] sphereSobolevInclusionL harmonicSphereSubspace sphereSobolevConstantOne

theorem nativeDensitySphereL2L_constantOne
    (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics):
    nativeDensitySphereL2L hO hD (sphereSobolevConstantOne (3/2:ℝ))=polynomialSphereL2 (C 1) := by
  change (sphereSobolevZeroEquiv hO hD).symm
    (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) (sphereSobolevConstantOne (3/2:ℝ)))=_
  rw [sphereSobolevInclusionL_constantOne,sphereSobolevZeroEquiv_symm_constantOne]

theorem sphereMean_original_normalized_source_of_eligible_density
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity) (hF:SphereFischerInner)
    (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics) (tau0:UnitBallValueTrace)
    (hKernel:UnitBallValueTraceKernel tau0)
    (S:KnownSideSourceData) (L lambda delta Rstar bound separation:ℝ) (p:ℕ)
    (cover:NativeNormalCover S L)
    (K:ConstructedMixedKernel S L lambda delta Rstar bound separation p cover)
    (hd:0 < delta) (hRs:0 < Rstar) (hlam:0 < lambda) (hlamRoom:lambda ≤ cover.dilationCeiling)
    (hRadius:∀ y∈cylinder,referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (Psi:R3→SphereSobolev (3/2:ℝ)) (hPsi:ContDiff ℝ ∞ Psi) (hPsic:HasCompactSupport Psi)
    (hRep:RepresentsNativeMixedKernelDensity hO hD tau0 S L lambda delta Rstar bound separation p cover K Psi)
    (chi:R3→ℝ) (hSupp:tsupport chi⊆interior cylinder):
    ∀ y:R3,sphereMean (nativeDensitySphereL2L hO hD (normalizedThreeHalfSourceField chi Psi y))=0 := by
  have hMean:= (sphereMean_any_eligible_native_density_and_cutoff_sub_one
    hcalc hreg hF hO hD tau0 hKernel S L lambda delta Rstar bound separation p cover K
    hd hRs hlam hlamRoom hRadius Psi hPsi hPsic hRep chi hSupp).2
  intro y
  rw [nativeDensitySphereL2L_normalized_source,nativeDensitySphereL2L_constantOne]
  exact hMean y

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
