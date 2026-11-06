import Calderon.ActualPhysicalOperatorFiniteSum
import Calderon.ActualSupportedPacketPhysicalCoherence
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ConformalDepth ActualScalarPrincipalAdjoint
attribute [local irreducible] sphereSobolevInclusionL referencePhysicalDensityOperator harmonicSphereSubspace
  nativePacketPhysicalDensityOperator

theorem nativePacketPhysicalDensityOperator_sum_of_supported_graphs
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (hKernel:UnitBallValueTraceKernel tau0)
    (S:KnownSideSourceData) (L lambda delta Rstar:ℝ) (p:ℕ) (cover:NativeNormalCover S L)
    (hd:0 < delta) (hRs:0 < Rstar) (hLam:lambda∈Icc (0:ℝ) cover.dilationCeiling)
    (K:Fin cover.count→Set R3) (hK:∀ i,K i⊆(cover.packet i).centers)
    (b:Fin cover.count→R3→SphereSobolev (3/2:ℝ)) (hb:∀ i,ContDiff ℝ ∞ (b i))
    (hbs:∀ i,tsupport (b i)⊆K i) (B:Fin cover.count→R3→SphereL2)
    (hB:∀ i y,sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (B i y))=
      nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p (b i) i y)
    (j:Fin cover.count) (y:R3) (hy:y∈(cover.packet j).centers)
    (hrceil:referenceRadius delta Rstar p L y < cover.radiusCeiling):
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (∑ i,B i y))=
      nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p
        (fun z => ∑ i,b i z) j y := by
  rw [map_sum,map_sum]
  calc
    (∑ i,sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (B i y)))=
        ∑ i,nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p (b i) j y := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hB i y]
      exact nativePacketPhysicalDensityOperator_eq_of_supported_source hcalc hreg hF hO hD tau0 hKernel S L lambda delta Rstar p
        cover hd hRs hLam i j (K i) (hK i) (b i) (hb i) (hbs i) y hy hrceil
    _ = _ := (nativePacketPhysicalDensityOperator_sum hcalc hreg hF hO hD tau0 S L lambda delta Rstar p cover hd hRs hLam j y
      hy hrceil cover.count b hb).symm

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
