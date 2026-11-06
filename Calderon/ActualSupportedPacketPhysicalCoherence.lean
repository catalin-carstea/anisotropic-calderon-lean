import Calderon.ActualPacketPhysicalOperatorCoherence
import Calderon.ActualPhysicalDensityOperatorLocality
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ConformalDepth ActualScalarPrincipalAdjoint
attribute [local irreducible] referencePhysicalDensityOperator sphereSobolevInclusionL harmonicSphereSubspace
  nativePacketPhysicalDensityOperator

theorem tsupport_nativePacketPhysicalDensityOperator_subset
    (hcalc:FixedSobolevCalculus) (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (S:KnownSideSourceData) (L lambda delta Rstar:ℝ) (p:ℕ) (cover:NativeNormalCover S L)
    (u:R3→SphereSobolev (3/2:ℝ)) (i:Fin cover.count):
    tsupport (fun y => nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p u i y)⊆tsupport u := by
  unfold nativePacketPhysicalDensityOperator
  exact tsupport_referencePhysicalDensityOperator_subset S.g1 L (cover.packet i).y0 (cover.packet i).Phi
    (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
    (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
    S.g1_admissible hcalc hF hO hD tau0 S.g2 lambda (referenceRadius delta Rstar p L) u

theorem nativePacketPhysicalDensityOperator_eq_of_supported_source
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (hKernel:UnitBallValueTraceKernel tau0)
    (S:KnownSideSourceData) (L lambda delta Rstar:ℝ) (p:ℕ) (cover:NativeNormalCover S L)
    (hd:0 < delta) (hRs:0 < Rstar) (hLam:lambda∈Icc (0:ℝ) cover.dilationCeiling)
    (i j:Fin cover.count) (K:Set R3) (hK:K⊆(cover.packet i).centers)
    (u:R3→SphereSobolev (3/2:ℝ)) (hu:ContDiff ℝ ∞ u) (hSupp:tsupport u⊆K)
    (y:R3) (hy:y∈(cover.packet j).centers) (hrceil:referenceRadius delta Rstar p L y < cover.radiusCeiling):
    nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p u i y=
      nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p u j y := by
  by_cases hk:y∈K
  · exact nativePacketPhysicalDensityOperator_eq_on_overlap hcalc hreg hF hO hD tau0 hKernel S L lambda delta Rstar p
      cover hd hRs hLam i j y ⟨hK hk,hy⟩ hrceil u hu
  · have hz (k:Fin cover.count):nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p u k y=0 := by
      exact image_eq_zero_of_notMem_tsupport (fun hm => hk (hSupp
        (tsupport_nativePacketPhysicalDensityOperator_subset hcalc hF hO hD tau0 S L lambda delta Rstar p cover u k hm)))
    rw [hz i,hz j]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
