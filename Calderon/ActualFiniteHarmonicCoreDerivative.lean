import Calderon.ActualModelCommutatorWords
import Calderon.BoundedAngularShift
import Calderon.SmoothSphereRotationProjection
import Calderon.PrincipalDirectional
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Algebra.Module.LinearMap.End
import Calderon.ActualFiniteHarmonicCoreWeights
import Calderon.ActualFiniteHarmonicCoreNormalizedDerivative

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  BoundedAngularShift AngularShiftGraph HarmonicDerivativeOperator PrincipalCommutator
  SmoothSphereRotationProjection

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

private abbrev coreDerivativeFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] coreDerivativeFunction

def coreDerivative (hF : SphereFischerInner) (i : Fin 3) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  coreNormalizedDerivative hO hD hF i * coreWeightOperator hO hD (besselWeight 1)

lemma coreDerivative_graph (hF : SphereFischerInner) (i : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    (F x,coreDerivative hO hD hF i F x) ∈ sphereDerivativeGraph hF hO hD i := by
  have hw := coreWeightOperator_graph hO hD (besselWeight 1) F x
  have hd := normalizedDerivative_graph hF hO hD i (F x)
    (coreWeightOperator hO hD (besselWeight 1) F x) hw
  simpa only [coreDerivative, Module.End.mul_apply, coreNormalizedDerivative,
    LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_mk] using hd


end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
