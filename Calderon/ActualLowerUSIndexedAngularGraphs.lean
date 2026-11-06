import Calderon.ActualLowerUSOrdinaryAngularMaps
import Calderon.ActualLowerUSLowerWordAdjoints

/-! GPT-6.1 Sol author support. Before-code ordinary-angular-before-v001.
Indexed finite input graphs; the true finite adjoint dictionary is imported
from its separate owner. No assertion that E/e/S preserves finite harmonics. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
open SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFiniteHarmonicModel.ActualLowerUSLowerWordAdjoints
  ActualAngularHighDraft ActualAngularPiDraft
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

/-- Indexed exact finite input graph of identity/minus-rotation/degree/lowering. -/
theorem lowerSAngularHigh_finiteCoreSobolevLift
    (i : LowerCoreAngularGeneratorIndex) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    lowerSAngularHigh hF hO hD i (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x) =
      finiteCoreSobolevLift hO hD (1/2 : ℝ) (lowerCoreAngularGenerator hO hD hF i F) x := by
  rcases i with z | ((ij | z) | a)
  · exact sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) (1/2 : ℝ) (by norm_num) F x
  · change -(sphereSobolevRotationL (3/2 : ℝ) ij.1 ij.2
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)) =
      finiteCoreSobolevLift hO hD (1/2 : ℝ) ((-coreRotation hO hD ij.1 ij.2) F) x
    rw [rotationHigh_finiteCoreSobolevLift hO hD]
    apply halfToSphereL2_injective hO hD
    rw [map_neg,halfToSphereL2_finiteCoreSobolevLift,halfToSphereL2_finiteCoreSobolevLift]
    rfl
  · exact degreeHigh_finiteCoreSobolevLift hO hD F x
  · exact loweringHigh_finiteCoreSobolevLift hO hD hF a F x

/-- Indexed exact finite input graph of the TRUE angular adjoint. -/
theorem lowerSAngularSharpHigh_finiteCoreSobolevLift
    (i : LowerCoreAngularGeneratorIndex) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    lowerSAngularSharpHigh hF hO hD i (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x) =
      finiteCoreSobolevLift hO hD (1/2 : ℝ) (lowerCoreAngularGeneratorAdjoint hO hD hF i F) x := by
  rcases i with z | ((ij | z) | a)
  · exact sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) (1/2 : ℝ) (by norm_num) F x
  · exact rotationHigh_finiteCoreSobolevLift hO hD ij.1 ij.2 F x
  · exact degreeHigh_finiteCoreSobolevLift hO hD F x
  · exact raisingHigh_finiteCoreSobolevLift hO hD hF a F x

/-- Inclusion of the genuine finite G output agrees with its high map. -/
theorem lowerSAngularHigh_finiteCoreHi_inclusion
    (i : LowerCoreAngularGeneratorIndex) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    IH (finiteCoreSobolevLift hO hD (3/2 : ℝ) (lowerCoreAngularGenerator hO hD hF i F) x) =
      lowerSAngularHigh hF hO hD i (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x) :=
  (sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
    (lowerCoreAngularGenerator hO hD hF i F) x).trans
      (lowerSAngularHigh_finiteCoreSobolevLift hF hO hD i F x).symm

/-- Inclusion of the genuine finite Gstar output agrees with its true high map. -/
theorem lowerSAngularSharpHigh_finiteCoreHi_inclusion
    (i : LowerCoreAngularGeneratorIndex) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    IH (finiteCoreSobolevLift hO hD (3/2 : ℝ) (lowerCoreAngularGeneratorAdjoint hO hD hF i F) x) =
      lowerSAngularSharpHigh hF hO hD i (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x) :=
  (sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
    (lowerCoreAngularGeneratorAdjoint hO hD hF i F) x).trans
      (lowerSAngularSharpHigh_finiteCoreSobolevLift hF hO hD i F x).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
