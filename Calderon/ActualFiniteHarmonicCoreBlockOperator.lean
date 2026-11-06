import Calderon.ActualModelCommutatorWords
import Calderon.BoundedAngularShift
import Calderon.SmoothSphereRotationProjection
import Calderon.PrincipalDirectional
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Algebra.Module.LinearMap.End
import Calderon.ActualFiniteHarmonicCoreBlockField

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  BoundedAngularShift AngularShiftGraph HarmonicDerivativeOperator PrincipalCommutator
  SmoothSphereRotationProjection

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

private abbrev coreBlockOperatorFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] coreBlockOperatorFunction

def coreBlockOperator
    (K : ∀ k, harmonicSphereSubspace k →L[ℝ] harmonicSphereSubspace k) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) where
  toFun F := ⟨coreBlockField hO hD K F,coreBlockField_mem hO hD K F⟩
  map_add' := by
    intro F G
    apply Subtype.ext
    funext x
    apply (sphereHarmonicDecomposition hO hD).injective
    apply lp.ext
    funext k
    change sphereHarmonicCoordinate hO hD k (coreBlockField hO hD K (F+G) x) =
      sphereHarmonicCoordinate hO hD k
        (coreBlockField hO hD K F x + coreBlockField hO hD K G x)
    simp only [coreBlockField_coordinate, map_add, Submodule.coe_add, Pi.add_apply]
  map_smul' := by
    intro c F
    apply Subtype.ext
    funext x
    apply (sphereHarmonicDecomposition hO hD).injective
    apply lp.ext
    funext k
    change sphereHarmonicCoordinate hO hD k (coreBlockField hO hD K (c • F) x) =
      sphereHarmonicCoordinate hO hD k (c • coreBlockField hO hD K F x)
    simp only [coreBlockField_coordinate, map_smul, Submodule.coe_smul,
      Pi.smul_apply, RingHom.id_apply]

lemma coreBlockOperator_coordinate
    (K : ∀ k, harmonicSphereSubspace k →L[ℝ] harmonicSphereSubspace k)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (k : ℕ) :
    sphereHarmonicCoordinate hO hD k (coreBlockOperator hO hD K F x) =
      K k (sphereHarmonicCoordinate hO hD k (F x)) := by
  exact coreBlockField_coordinate hO hD K F x k


end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
