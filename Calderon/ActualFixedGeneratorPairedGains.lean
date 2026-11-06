import Calderon.ActualFixedGeneratorHighGraphs
import Calderon.ActualFixedGeneratorLowConstruction
import Calderon.ActualFixedGeneratorFinitePairedFamily

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFixedGeneratorPairedGains
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualCanonicalAngularGainedBracket ActualFiniteHarmonicModel
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  HarmonicDerivativeOperator RotationCasimir SmoothSphereRotationProjection
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "I33" => sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "RH" => sphereSobolevRotationL (3/2 : ℝ)
local notation "RL" => sphereSobolevRotationL (1/2 : ℝ)
local notation "DH" => sphereSobolevShiftedDegreeL (3/2 : ℝ)
local notation "DL" => sphereSobolevShiftedDegreeL (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

attribute [local irreducible] sphereSobolevRotationL sphereSobolevShiftedDegreeL
  sphereSobolevInclusionL sphereSobolevSingleL generatorHigh generatorLow
  generatorSharpHigh generatorSharpLow rotationLieHigh fixedGeneratorGainHigh

theorem exists_fixed_generator_paired_gains :
    ∃ Cl : Generator → Generator → Half →L[ℝ] Neg,
      (∀ V W U, JL (fixedGeneratorGainHigh V W U) =
        generatorSharpLow V (generatorHigh W U) -
          generatorLow W (generatorSharpHigh V U)) ∧
      (∀ V W U Z, PP (IH Z) (JL (fixedGeneratorGainHigh V W U)) =
        PP (IH U) (JL (fixedGeneratorGainHigh W V Z))) ∧
      (∀ V W,
        (Cl V W).comp IH = (JL).comp (fixedGeneratorGainHigh V W) ∧
        (I33).comp (Cl V W) = (v016TransposeL (fixedGeneratorGainHigh W V)).comp JL ∧
        ‖Cl V W‖ ≤ (‖fixedGeneratorGainHigh V W‖ + ‖fixedGeneratorGainHigh W V‖)/2) ∧
      (∃ M : ℝ, 1 ≤ M ∧ ∀ V W : Generator,
        ‖fixedGeneratorGainHigh V W‖ ≤ M ∧ ‖Cl V W‖ ≤ M) := by
  have hAdj : ∀ V W : Generator, ∀ U Z : Hi,
      PP (IH Z) (JL (fixedGeneratorGainHigh V W U)) =
        PP (IH U) (JL (fixedGeneratorGainHigh W V Z)) :=
    fun V W U Z => fixedGeneratorGainHigh_paired V W U Z
  have hFamily : ∃ Cl : Generator → Generator → Half →L[ℝ] Neg,
      (∀ V W,
        (Cl V W).comp IH = (JL).comp (fixedGeneratorGainHigh V W) ∧
        (I33).comp (Cl V W) = (v016TransposeL (fixedGeneratorGainHigh W V)).comp JL ∧
        ‖Cl V W‖ ≤ (‖fixedGeneratorGainHigh V W‖+‖fixedGeneratorGainHigh W V‖)/2) ∧
      ∃ M : ℝ, 1 ≤ M ∧ ∀ V W : Generator,
        ‖fixedGeneratorGainHigh V W‖ ≤ M ∧ ‖Cl V W‖ ≤ M :=
    ActualFixedGeneratorFinitePairedFamily.exists_finite_paired_family fixedGeneratorGainHigh hAdj
  let Cl : Generator → Generator → Half →L[ℝ] Neg := Classical.choose hFamily
  have hCl := Classical.choose_spec hFamily
  exact ⟨Cl,fixedGeneratorGainHigh_graph,fixedGeneratorGainHigh_paired,hCl.1,hCl.2⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFixedGeneratorPairedGains
