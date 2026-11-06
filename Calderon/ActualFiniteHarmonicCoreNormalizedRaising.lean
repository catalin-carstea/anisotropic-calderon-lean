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

private abbrev coreNormalizedRaisingFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] coreNormalizedRaisingFunction

lemma normalizedRaising_core_mem (hF : SphereFischerInner) (i : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) :
    (fun x => normalizedRaising hF hO hD i (F x)) ∈
      smoothCompactFiniteSphereCore hO hD := by
  obtain ⟨n, hn⟩ := F.property.2.2
  refine ⟨(normalizedRaising hF hO hD i).contDiff.comp F.property.1,
    F.property.2.1.comp_left (map_zero (normalizedRaising hF hO hD i)),
    ⟨n+1, ?_⟩⟩
  intro x k hk
  cases k with
  | zero => omega
  | succ m =>
    change sphereHarmonicCoordinate hO hD (m+1) (normalizedRaisingOutput hF hO hD i (F x)) = 0
    rw [(normalizedRaisingOutput_graph hF hO hD i (F x)).2 m,
      inverseDegreeMultiplier_coordinate, hn x m (by omega), smul_zero, map_zero]

def coreNormalizedRaising (hF : SphereFischerInner) (i : Fin 3) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) where
  toFun F := ⟨fun x => normalizedRaising hF hO hD i (F x),normalizedRaising_core_mem hO hD hF i F⟩
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
