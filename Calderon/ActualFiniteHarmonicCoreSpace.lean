import Calderon.ActualModelCommutatorWords
import Calderon.BoundedAngularShift
import Calderon.SmoothSphereRotationProjection
import Calderon.PrincipalDirectional
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Algebra.Module.LinearMap.End

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  BoundedAngularShift AngularShiftGraph HarmonicDerivativeOperator PrincipalCommutator
  SmoothSphereRotationProjection

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

def finiteHarmonicBand (n : ℕ) (F : R3 → SphereL2) : Prop :=
  ∀ x k, n ≤ k → sphereHarmonicCoordinate hO hD k (F x) = 0

def smoothCompactFiniteSphereCore : Submodule ℝ (R3 → SphereL2) where
  carrier := {F | ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
    ∃ n, finiteHarmonicBand hO hD n F}
  zero_mem' := by
    refine ⟨contDiff_const, HasCompactSupport.zero, ⟨0, ?_⟩⟩
    intro x k hk
    simp
  add_mem' := by
    intro F G hF hG
    refine ⟨hF.1.add hG.1, hF.2.1.add hG.2.1, ?_⟩
    obtain ⟨n, hn⟩ := hF.2.2
    obtain ⟨m, hm⟩ := hG.2.2
    refine ⟨max n m, ?_⟩
    intro x k hk
    change sphereHarmonicCoordinate hO hD k (F x + G x) = 0
    rw [map_add, hn x k ((le_max_left n m).trans hk),
      hm x k ((le_max_right n m).trans hk), add_zero]
  smul_mem' := by
    intro c F hF
    obtain ⟨n, hn⟩ := hF.2.2
    refine ⟨contDiff_const.smul hF.1, ?_, ⟨n, ?_⟩⟩
    · have hsupport : HasCompactSupport ((fun _ : R3 => c) • F) :=
        hF.2.1.smul_left
      have hfield : ((fun _ : R3 => c) • F : R3 → SphereL2) = c • F := by
        funext x
        rfl
      exact hfield ▸ hsupport
    · intro x k hk
      change sphereHarmonicCoordinate hO hD k (c • F x) = 0
      rw [map_smul, hn x k hk, smul_zero]


end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
