import Calderon.ActualModelCommutatorWords
import Calderon.BoundedAngularShift
import Calderon.SmoothSphereRotationProjection
import Calderon.PrincipalDirectional
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Algebra.Module.LinearMap.End
import Calderon.ActualFiniteHarmonicCoreCutoff

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  BoundedAngularShift AngularShiftGraph HarmonicDerivativeOperator PrincipalCommutator
  SmoothSphereRotationProjection

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

private abbrev coreBlockFieldFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] coreBlockFieldFunction

def coreBlockField
    (K : ∀ k, harmonicSphereSubspace k →L[ℝ] harmonicSphereSubspace k)
    (F : smoothCompactFiniteSphereCore hO hD) : R3 → SphereL2 :=
  fun x => finiteHarmonicBlockCutoff hO hD F.property.2.2.choose K (F x)

lemma coreBlockField_coordinate
    (K : ∀ k, harmonicSphereSubspace k →L[ℝ] harmonicSphereSubspace k)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (k : ℕ) :
    sphereHarmonicCoordinate hO hD k (coreBlockField hO hD K F x) =
      K k (sphereHarmonicCoordinate hO hD k (F x)) := by
  unfold coreBlockField
  exact finiteHarmonicBlockCutoff_coordinate_of_band hO hD F.property.2.2.choose K
    (F : R3 → SphereL2) F.property.2.2.choose_spec x k

lemma coreBlockField_mem
    (K : ∀ k, harmonicSphereSubspace k →L[ℝ] harmonicSphereSubspace k)
    (F : smoothCompactFiniteSphereCore hO hD) :
    coreBlockField hO hD K F ∈ smoothCompactFiniteSphereCore hO hD := by
  let n := F.property.2.2.choose
  have hfield : coreBlockField hO hD K F =
      ((finiteHarmonicBlockCutoff hO hD n K : SphereL2 → SphereL2) ∘
        (F : R3 → SphereL2)) := by
    funext x
    rfl
  have hsmooth : ContDiff ℝ ∞
      ((finiteHarmonicBlockCutoff hO hD n K : SphereL2 → SphereL2) ∘
        (F : R3 → SphereL2)) :=
    (finiteHarmonicBlockCutoff hO hD n K).contDiff.comp F.property.1
  have hsupport : HasCompactSupport
      ((finiteHarmonicBlockCutoff hO hD n K : SphereL2 → SphereL2) ∘
        (F : R3 → SphereL2)) :=
    F.property.2.1.comp_left (map_zero (finiteHarmonicBlockCutoff hO hD n K))
  refine ⟨hfield.symm ▸ hsmooth, hfield.symm ▸ hsupport, ⟨n, ?_⟩⟩
  intro x k hk
  rw [coreBlockField_coordinate, F.property.2.2.choose_spec x k hk, map_zero]


end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
