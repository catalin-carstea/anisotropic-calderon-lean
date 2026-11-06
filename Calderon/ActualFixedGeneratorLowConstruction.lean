import Calderon.ActualFullEPhysicalEndpoints
import Calderon.ActualGeneratorEPairedGainedEndpoints
import Calderon.ActualCanonicalAngularGainedBracket

/-! Small constant-family paired low construction, original4503 only.
The two maps are opaque parameters; the actual fixed producer discharges pairing.
No final extra premise, mathematical change or checker limit increase is introduced. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFixedGeneratorLowConstruction
open SphereHarmonic ActualFullEGainedEndpoints ActualGeneratorEPairedGainedEndpoints
  ActualAngularHighDraft ActualAngularPiDraft
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "I33" => sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
attribute [local irreducible] sphereSobolevInclusionL

theorem exists_constant_paired_low (Ch Dh : Hi →L[ℝ] Half)
    (hAdj : ∀ u v : Hi, PP (IH v) (JL (Ch u)) = PP (IH u) (JL (Dh v))) :
    ∃ C : Half →L[ℝ] Neg,
      C.comp IH = (JL).comp Ch ∧
      (I33).comp C = (v016TransposeL Dh).comp JL ∧
      ‖C‖ ≤ (‖Ch‖+‖Dh‖)/2 := by
  have hc := v016_compatible_of_adjunction Ch Dh hAdj
  let B : Half →L[ℝ] Neg := sphereSobolevBalancedDualEndpointL (v016TransposeL Dh) Ch hc
  have hUp : B.comp IH = (JL).comp Ch :=
    sphereSobolevBalancedDualEndpointL_upper_inclusion (v016TransposeL Dh) Ch hc
  have hLo : (I33).comp B = (v016TransposeL Dh).comp JL :=
    sphereSobolevBalancedDualEndpointL_lower_inclusion (v016TransposeL Dh) Ch hc
  have hN0 : ‖B‖ ≤ (‖v016TransposeL Dh‖+‖Ch‖)/2 :=
    norm_sphereSobolevBalancedDualEndpointL_le (v016TransposeL Dh) Ch hc
  have hN1 := norm_v016TransposeL_apply_le Dh
  exact ⟨B, hUp, hLo, hN0.trans (by linarith)⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFixedGeneratorLowConstruction
