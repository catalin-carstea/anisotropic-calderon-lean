import Calderon.ActualHigherSFirstPhysicalCommutatorGraph
import Calderon.FiniteCoreSobolevDerivativeEnergy
import Calderon.ActualFiniteHarmonicCoreScalar
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic PrincipalCommutator ReferenceDensityBounds
  DirichletFamily.DriftBootstrap.ActualHigherSFirstPhysicalCommutatorGraph
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
local notation "Core" => smoothCompactFiniteSphereCore hO hD

/-- Exact ordered second-coordinate action as an endomorphism of the genuine finite core. -/
def coreCoordinateSecondAction (a : Fin 3 → Fin 3 → R3 → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) : Module.End ℝ Core :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (coreScalar hO hD (a i j) (ha i j))*
      (coreDirectionalDerivative hO hD (coordinateDirection i))*
      (coreDirectionalDerivative hO hD (coordinateDirection j))

lemma coreCoordinateSecondAction_apply (a : Fin 3 → Fin 3 → R3 → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (F : Core) (x : R3) :
    (coreCoordinateSecondAction hO hD a ha F).val x = coordinateSecondAction a F.val x := by
  simp only [coreCoordinateSecondAction,LinearMap.sum_apply,Module.End.mul_apply,
    Submodule.coe_sum,Finset.sum_apply,coreScalar,coreDirectionalDerivative,
    LinearMap.coe_mk,AddHom.coe_mk]
  rfl

/-- The actual scalar action does not enlarge the input's closed support. -/
lemma coreCoordinateSecondAction_tsupport (a : Fin 3 → Fin 3 → R3 → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (F : Core) :
    tsupport (coreCoordinateSecondAction hO hD a ha F).val ⊆ tsupport F.val := by
  apply closure_minimal ?_ (isClosed_tsupport F.val)
  intro x hx
  by_contra hx'
  apply hx
  rw [coreCoordinateSecondAction_apply]
  exact coordinateSecondAction_eq_zero_off a F.val (tsupport F.val) (isClosed_tsupport F.val)
    (fun y hy => image_eq_zero_of_notMem_tsupport hy) x hx'

/-- Two ordered base derivatives commute with the exact finite Sobolev lift. -/
lemma directional_second_finiteCoreSobolevLift (s : ℝ) (F : Core) (X Y x : R3) :
    directionalFDeriv X (directionalFDeriv Y (finiteCoreSobolevLift hO hD s F)) x =
      finiteCoreSobolevLift hO hD s
        (coreDirectionalDerivative hO hD X (coreDirectionalDerivative hO hD Y F)) x := by
  have hY : directionalFDeriv Y (finiteCoreSobolevLift hO hD s F) =
      finiteCoreSobolevLift hO hD s (coreDirectionalDerivative hO hD Y F) :=
    funext (fun y => directionalFDeriv_finiteCoreSobolevLift hO hD s F Y y)
  rw [hY]
  exact directionalFDeriv_finiteCoreSobolevLift hO hD s
    (coreDirectionalDerivative hO hD Y F) X x

/-- Literal global finite-input graph in every original Sobolev representation. -/
theorem finiteCoreSobolevLift_coreCoordinateSecondAction
    (s : ℝ) (a : Fin 3 → Fin 3 → R3 → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (F : Core) :
    finiteCoreSobolevLift hO hD s (coreCoordinateSecondAction hO hD a ha F) =
      coordinateSecondAction a (finiteCoreSobolevLift hO hD s F) := by
  funext x
  apply sphereSobolev_ext s
  intro k
  rw [sphereSobolevCoefficientL_finiteCoreSobolevLift,coreCoordinateSecondAction_apply]
  simp only [coordinateSecondAction,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [directional_second_finiteCoreSobolevLift,sphereSobolevCoefficientL_finiteCoreSobolevLift]
  rfl
end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
