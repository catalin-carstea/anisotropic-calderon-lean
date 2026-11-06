import Calderon.ActualModelCommutatorWords
import Calderon.BoundedAngularShift
import Calderon.SmoothSphereRotationProjection
import Calderon.PrincipalDirectional
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Algebra.Module.LinearMap.End
import Calderon.ActualFiniteHarmonicCoreBase
import Calderon.ActualFiniteHarmonicCoreScalar

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  BoundedAngularShift AngularShiftGraph HarmonicDerivativeOperator PrincipalCommutator
  SmoothSphereRotationProjection

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

private abbrev coreLeibnizFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] coreLeibnizFunction

lemma coefficientDerivative_coreScalar (v : R3) (c : R3 → ℝ) (hc : ContDiff ℝ ∞ c) :
    ActualModelCommutatorWords.coefficientDerivative
      (coreDirectionalDerivative hO hD v) (coreScalar hO hD c hc) =
    coreScalar hO hD (directionalFDeriv v c) (contDiff_directionalFDeriv v c hc) := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  simp only [ActualModelCommutatorWords.coefficientDerivative, ActualModelCommutatorWords.commutator,
    Module.End.mul_apply, LinearMap.sub_apply, coreDirectionalDerivative, coreScalar,
    LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_mk, Submodule.coe_sub, Pi.sub_apply]
  rw [directionalFDeriv_smul v c (F : R3 → SphereL2) hc F.property.1 x]
  abel

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
