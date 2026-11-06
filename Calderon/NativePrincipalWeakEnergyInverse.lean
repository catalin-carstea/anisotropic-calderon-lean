import Calderon.NativeOrthogonalZeroEnergyInvertibility
import Calderon.SmoothPositiveCoefficientNativeCoercivity
import Calderon.UniformSmallDriftCoercivity
import Calderon.CoerciveFunctionalInverseEquality
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

local instance : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 3 → Fin 3 → ℝ))

theorem nativeZeroPrincipalCoefficientEnergy_isInvertible
    (A : MatrixField) (hA : Continuous A) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) A lam Lam) :
    (nativeZeroCoefficientEnergyL A 0 0
      (memLp_continuousCoefficientEnergyIntegrand A hA)).IsInvertible := by
  let E := nativeZeroCoefficientEnergyL A 0 0
    (memLp_continuousCoefficientEnergyIntegrand A hA)
  have hZero : ∀ z ∈ (ballOpens : Set R3), ‖(0 : R3 → R3) z‖ ≤ lam/4 := by
    intro z hz
    simpa only [Pi.zero_apply,norm_zero] using
      (div_pos hUE.pos (by norm_num : (0 : ℝ) < 4)).le
  have hCoercive : IsCoercive E := by
    refine ⟨3*lam/40,by positivity [hUE.pos],?_⟩
    intro u
    rw [nativeZeroCoefficientEnergyL_apply,TauCeti.PDE.energyFormH1L0_apply]
    exact unitBall_smallDrift_coercivity hUE hA.aestronglyMeasurable
      aestronglyMeasurable_const hZero u
  exact (isInvertible_and_inverse_eq_functionalInverse E hCoercive).1

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
