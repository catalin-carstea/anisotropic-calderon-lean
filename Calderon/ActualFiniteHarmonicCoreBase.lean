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

private abbrev coreBaseFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] coreBaseFunction

lemma directionalDerivative_core_mem (v : R3)
    (F : smoothCompactFiniteSphereCore hO hD) :
    directionalFDeriv v (F : R3 → SphereL2) ∈
      smoothCompactFiniteSphereCore hO hD := by
  obtain ⟨n, hn⟩ := F.property.2.2
  refine ⟨contDiff_directionalFDeriv v (F : R3 → SphereL2) F.property.1,
    F.property.2.1.fderiv_apply ℝ v, ⟨n, ?_⟩⟩
  intro x k hk
  have hz : (fun y => sphereHarmonicCoordinate hO hD k (F y)) = (fun _ : R3 => 0) :=
    funext (fun y => hn y k hk)
  have hd : fderiv ℝ (fun y => sphereHarmonicCoordinate hO hD k (F y)) x v = 0 := by
    rw [hz]
    simp
  rw [fderiv_sphereHarmonicCoordinate hO hD k (F : R3 → SphereL2) x
    (F.property.1.differentiable (by simp) x)] at hd
  exact hd

def coreDirectionalDerivative (v : R3) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) where
  toFun F := ⟨directionalFDeriv v (F : R3 → SphereL2),directionalDerivative_core_mem hO hD v F⟩
  map_add' := by
    intro F G
    apply Subtype.ext
    funext x
    change directionalFDeriv v (fun y => F y + G y) x =
      directionalFDeriv v (F : R3 → SphereL2) x + directionalFDeriv v (G : R3 → SphereL2) x
    exact directionalFDeriv_add v _ _ F.property.1 G.property.1 x
  map_smul' := by
    intro c F
    apply Subtype.ext
    funext x
    change directionalFDeriv v (fun y => c • F y) x =
      c • directionalFDeriv v (F : R3 → SphereL2) x
    rw [directionalFDeriv_smul v (fun _ : R3 => c) (F : R3 → SphereL2)
      contDiff_const F.property.1 x]
    simp [directionalFDeriv]

lemma coreDirectionalDerivative_commute (v w : R3) :
    Commute (coreDirectionalDerivative hO hD v) (coreDirectionalDerivative hO hD w) := by
  change coreDirectionalDerivative hO hD v * coreDirectionalDerivative hO hD w =
    coreDirectionalDerivative hO hD w * coreDirectionalDerivative hO hD v
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  change directionalFDeriv v (directionalFDeriv w (F : R3 → SphereL2)) x =
    directionalFDeriv w (directionalFDeriv v (F : R3 → SphereL2)) x
  exact directionalFDeriv_commute v w _ F.property.1 x


end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
