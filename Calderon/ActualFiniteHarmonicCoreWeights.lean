import Calderon.ActualModelCommutatorWords
import Calderon.BoundedAngularShift
import Calderon.SmoothSphereRotationProjection
import Calderon.PrincipalDirectional
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Algebra.Module.LinearMap.End
import Calderon.ActualFiniteHarmonicCoreBlockOperator

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  BoundedAngularShift AngularShiftGraph HarmonicDerivativeOperator PrincipalCommutator
  SmoothSphereRotationProjection

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

private abbrev coreWeightsFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] coreWeightsFunction

def coreWeightOperator (w : ℕ → ℝ) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  coreBlockOperator hO hD (fun k => w k • ContinuousLinearMap.id ℝ (harmonicSphereSubspace k))

lemma coreWeightOperator_graph (w : ℕ → ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    (F x,coreWeightOperator hO hD w F x) ∈ spectralGraph hO hD w := by
  intro k
  change sphereHarmonicCoordinate hO hD k
      (coreBlockOperator hO hD (fun l => w l • ContinuousLinearMap.id ℝ (harmonicSphereSubspace l)) F x) =
    w k • sphereHarmonicCoordinate hO hD k (F x)
  rw [coreBlockOperator_coordinate]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]

def coreDegree : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  coreWeightOperator hO hD (fun k => (k:ℝ))


end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
