import Calderon.ActualModelCommutatorWords
import Calderon.BoundedAngularShift
import Calderon.SmoothSphereRotationProjection
import Calderon.PrincipalDirectional
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Algebra.Module.LinearMap.End
import Calderon.ActualFiniteHarmonicCoreSpace

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  BoundedAngularShift AngularShiftGraph HarmonicDerivativeOperator PrincipalCommutator
  SmoothSphereRotationProjection

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

private abbrev coreScalarFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] coreScalarFunction

lemma scalarMul_core_mem (c : R3 → ℝ) (hc : ContDiff ℝ ∞ c)
    (F : smoothCompactFiniteSphereCore hO hD) :
    (fun x => c x • F x) ∈ smoothCompactFiniteSphereCore hO hD := by
  obtain ⟨n, hn⟩ := F.property.2.2
  refine ⟨hc.smul F.property.1, ?_, ⟨n, ?_⟩⟩
  · have hsupport : HasCompactSupport (c • (F : R3 → SphereL2)) :=
      F.property.2.1.smul_left
    have hfield : (c • (F : R3 → SphereL2)) = (fun x : R3 => c x • F x) := by
      funext x
      rfl
    exact hfield ▸ hsupport
  · intro x k hk
    rw [map_smul, hn x k hk, smul_zero]

def coreScalar (c : R3 → ℝ) (hc : ContDiff ℝ ∞ c) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) where
  toFun F := ⟨fun x => c x • F x,scalarMul_core_mem hO hD c hc F⟩
  map_add' := by
    intro F G
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_mk, Submodule.coe_add, Pi.add_apply, smul_add]
  map_smul' := by
    intro c0 F
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_mk, Submodule.coe_smul, Pi.smul_apply]
    exact smul_comm (c x) c0 (F x)


end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
