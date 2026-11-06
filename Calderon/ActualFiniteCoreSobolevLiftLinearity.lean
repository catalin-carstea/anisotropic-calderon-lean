import Calderon.ActualOriginalFiniteSourceL2Graph
import Calderon.ActualPhysicalOperatorFiniteSum
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open SphereHarmonic ActualFiniteHarmonicCore EnergyBridge DirichletFamily
  DirichletFamily.DriftBootstrap ConformalDepth
attribute [local irreducible] sphereSobolevInclusionL finiteCoreSobolevLift

theorem finiteCoreSobolevLift_add
    (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics) (s:ℝ) (hs:0 ≤ s)
    (A B:smoothCompactFiniteSphereCore hO hD):
    finiteCoreSobolevLift hO hD s (A+B)=
      (fun y=>finiteCoreSobolevLift hO hD s A y+finiteCoreSobolevLift hO hD s B y) := by
  funext y
  apply sphereSobolevInclusionL_injective s 0 hs
  rw [(finiteCoreSobolevLift_representation hO hD s hs (A+B)).2.2.2.1 y,map_add,
    (finiteCoreSobolevLift_representation hO hD s hs A).2.2.2.1 y,
    (finiteCoreSobolevLift_representation hO hD s hs B).2.2.2.1 y]
  exact map_add (sphereSobolevZeroEquiv hO hD) ((A:R3→SphereL2) y) ((B:R3→SphereL2) y)

theorem finiteCoreSobolevLift_smul
    (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics) (s:ℝ) (hs:0 ≤ s)
    (a:ℝ) (A:smoothCompactFiniteSphereCore hO hD):
    finiteCoreSobolevLift hO hD s (a • A)=
      (fun y=>a • finiteCoreSobolevLift hO hD s A y) := by
  funext y
  apply sphereSobolevInclusionL_injective s 0 hs
  rw [(finiteCoreSobolevLift_representation hO hD s hs (a • A)).2.2.2.1 y,map_smul,
    (finiteCoreSobolevLift_representation hO hD s hs A).2.2.2.1 y]
  exact map_smul (sphereSobolevZeroEquiv hO hD) a ((A:R3→SphereL2) y)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
