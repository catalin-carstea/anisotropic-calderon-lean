import Calderon.ActualModelCommutatorWords
import Calderon.BoundedAngularShift
import Calderon.SmoothSphereRotationProjection
import Calderon.PrincipalDirectional
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Algebra.Module.LinearMap.End
import Calderon.ActualFiniteHarmonicCoreWeights
import Calderon.ActualFiniteHarmonicCoreNormalizedRaising

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  BoundedAngularShift AngularShiftGraph HarmonicDerivativeOperator PrincipalCommutator
  SmoothSphereRotationProjection

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

private abbrev coreRaisingFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] coreRaisingFunction

def coreRaising (hF : SphereFischerInner) (i : Fin 3) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  coreNormalizedRaising hO hD hF i * coreWeightOperator hO hD (besselWeight 1)

lemma coreRaising_graph (hF : SphereFischerInner) (i : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    (F x,coreRaising hO hD hF i F x) ∈ sphereRaisingGraph hF hO hD i := by
  have hw := coreWeightOperator_graph hO hD (besselWeight 1) F x
  have hr := normalizedRaising_graph hF hO hD i (F x)
    (coreWeightOperator hO hD (besselWeight 1) F x) hw
  simpa only [coreRaising, Module.End.mul_apply, coreNormalizedRaising,
    LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_mk] using hr


end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
