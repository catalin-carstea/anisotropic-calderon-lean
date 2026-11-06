import Calderon.NativeCoefficientRotationProductRule
import Calderon.NativeSmoothBallSobolev

/-! Actual compact rotation derivative. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge SphereHarmonic SmoothSphereRotation

def coefficientRotationJets (k : ℕ) (Q : SmoothCoefficientJets 3) (i j : Fin 3) :
    SmoothCoefficientJets k :=
  compactCoefficient k
    (fun x => unitBallSmoothCutoff x * sphereRotationDerivative i j (coefficientValue 3 Q) x)
    (unitBallSmoothCutoff.contDiff.mul
      (contDiff_sphereRotationDerivative i j _ (contDiff_coefficientValue 3 Q)))
    (unitBallSmoothCutoff.hasCompactSupport.mul_right)

lemma coefficientValue_coefficientRotationJets (k : ℕ) (Q : SmoothCoefficientJets 3)
    (i j : Fin 3) :
    coefficientValue k (coefficientRotationJets k Q i j) =
      fun x => unitBallSmoothCutoff x * sphereRotationDerivative i j (coefficientValue 3 Q) x :=
  coefficientValue_compactCoefficient k _ _ _

lemma coefficientRotationJets_sphere_value (k : ℕ) (Q : SmoothCoefficientJets 3)
    (i j : Fin 3) (x : UnitSphere) :
    coefficientValue k (coefficientRotationJets k Q i j) x.val =
      sphereRotationDerivative i j (coefficientValue 3 Q) x.val := by
  have hValue := congrFun (coefficientValue_coefficientRotationJets k Q i j) x.val
  have hCut : unitBallSmoothCutoff x.val = 1 := by
    apply unitBallSmoothCutoff.one_of_mem_closedBall
    change dist x.val (0 : R3) ≤ (2 : ℝ)
    have hNorm : ‖x.val‖ = (1 : ℝ) := by
      simpa only [Metric.mem_sphere,dist_zero_right] using x.property
    simpa only [dist_zero_right,hNorm] using (by norm_num : (1 : ℝ) ≤ 2)
  exact hValue.trans ((congrArg
    (fun c : ℝ => c * sphereRotationDerivative i j (coefficientValue 3 Q) x.val) hCut).trans
      (one_mul _))

end OAI.AnisotropicCalderon.DirichletFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.coefficientRotationJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.coefficientValue_coefficientRotationJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.coefficientRotationJets_sphere_value
