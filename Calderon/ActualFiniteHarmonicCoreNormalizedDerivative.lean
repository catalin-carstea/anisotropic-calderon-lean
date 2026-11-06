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

private abbrev coreNormalizedDerivativeFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] coreNormalizedDerivativeFunction

lemma normalizedDerivative_core_mem (hF : SphereFischerInner) (i : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) :
    (fun x => normalizedDerivative hF hO hD i (F x)) ∈
      smoothCompactFiniteSphereCore hO hD := by
  obtain ⟨n, hn⟩ := F.property.2.2
  refine ⟨(normalizedDerivative hF hO hD i).contDiff.comp F.property.1,
    F.property.2.1.comp_left (map_zero (normalizedDerivative hF hO hD i)),
    ⟨n, ?_⟩⟩
  intro x k hk
  change sphereHarmonicCoordinate hO hD k (normalizedDerivativeOutput hF hO hD i (F x)) = 0
  rw [normalizedDerivativeOutput_graph hF hO hD i (F x) k,
    inverseDegreeMultiplier_coordinate, hn x (k+1) (by omega), smul_zero, map_zero]

def coreNormalizedDerivative (hF : SphereFischerInner) (i : Fin 3) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) where
  toFun F := ⟨fun x => normalizedDerivative hF hO hD i (F x),normalizedDerivative_core_mem hO hD hF i F⟩
  map_add' := by
    intro F G
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_mk, Submodule.coe_add, Pi.add_apply, map_add]
  map_smul' := by
    intro c F
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_mk, Submodule.coe_smul, Pi.smul_apply, map_smul, RingHom.id_apply]


end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
