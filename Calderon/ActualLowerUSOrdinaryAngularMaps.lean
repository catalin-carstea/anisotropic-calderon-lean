import Calderon.ActualLowerUSFirstCoefficientGraph
import Calderon.ActualLowerUSAdjointZeroPolynomial

/-! GPT-6.1 Sol author support. Before-code ordinary-angular-before-v001.
Canonical ordinary maps and their TRUE angular partners, no analytic callback. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
open SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

abbrev OrdinarySAngularIndex := (Fin 3 × Fin 3) ⊕ (Unit ⊕ Fin 3)

def ordinarySToFirstIndex : OrdinarySAngularIndex → FirstAngularIndex
  | Sum.inl ij => Sum.inl (Sum.inl ij)
  | Sum.inr (Sum.inl z) => Sum.inl (Sum.inr z)
  | Sum.inr (Sum.inr a) => Sum.inr a

variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

def firstAngularSharpHigh : FirstAngularIndex → Hi →L[ℝ] Half
  | Sum.inl V => generatorHigh V
  | Sum.inr a => raisingHigh hF hO hD a

def firstAngularSharpLow : FirstAngularIndex → Half →L[ℝ] Neg
  | Sum.inl V => generatorLow V
  | Sum.inr a => raisingLow hF hO hD a

def lowerSAngularHigh : LowerCoreAngularGeneratorIndex → Hi →L[ℝ] Half
  | Sum.inl _ => IH
  | Sum.inr v => firstAngularHigh hF hO hD v
def lowerSAngularLow : LowerCoreAngularGeneratorIndex → Half →L[ℝ] Neg
  | Sum.inl _ => JL
  | Sum.inr v => firstAngularLow hF hO hD v
def lowerSAngularSharpHigh : LowerCoreAngularGeneratorIndex → Hi →L[ℝ] Half
  | Sum.inl _ => IH
  | Sum.inr v => firstAngularSharpHigh hF hO hD v
def lowerSAngularSharpLow : LowerCoreAngularGeneratorIndex → Half →L[ℝ] Neg
  | Sum.inl _ => JL
  | Sum.inr v => firstAngularSharpLow hF hO hD v

def ordinarySAngularHigh (v : OrdinarySAngularIndex) : Hi →L[ℝ] Half :=
  firstAngularSharpHigh hF hO hD (ordinarySToFirstIndex v)
def ordinarySAngularLow (v : OrdinarySAngularIndex) : Half →L[ℝ] Neg :=
  firstAngularSharpLow hF hO hD (ordinarySToFirstIndex v)
def ordinarySAngularSharpHigh (v : OrdinarySAngularIndex) : Hi →L[ℝ] Half :=
  firstAngularHigh hF hO hD (ordinarySToFirstIndex v)
def ordinarySAngularSharpLow (v : OrdinarySAngularIndex) : Half →L[ℝ] Neg :=
  firstAngularLow hF hO hD (ordinarySToFirstIndex v)

theorem firstAngularHigh_low_compatibility (v : FirstAngularIndex) (u : Hi) :
    JL (firstAngularHigh hF hO hD v u) = firstAngularLow hF hO hD v (IH u) := by
  cases v with
  | inl V =>
    cases V with
    | inl ij =>
      have h : JL (sphereSobolevRotationL (3/2 : ℝ) ij.1 ij.2 u) =
          sphereSobolevRotationL (1/2 : ℝ) ij.1 ij.2 (IH u) := by
        simpa only [ContinuousLinearMap.comp_apply] using
          congrArg (fun A : Hi →L[ℝ] Neg => A u) (sphereSobolevRotationL_threehalf_half_compatibility ij.1 ij.2)
      change JL (-(sphereSobolevRotationL (3/2 : ℝ) ij.1 ij.2 u)) =
        -(sphereSobolevRotationL (1/2 : ℝ) ij.1 ij.2 (IH u))
      exact (map_neg JL _).trans (congrArg (fun z : Neg => -z) h)
    | inr z => exact congrArg (fun A : Hi →L[ℝ] Neg => A u) sphereSobolevShiftedDegree_high_half_compatibility
  | inr a => exact v017_inclusion_loweringHigh hF hO hD a u

theorem firstAngularSharpHigh_low_compatibility (v : FirstAngularIndex) (u : Hi) :
    JL (firstAngularSharpHigh hF hO hD v u) = firstAngularSharpLow hF hO hD v (IH u) := by
  cases v with
  | inl V =>
    cases V with
    | inl ij =>
      simpa only [firstAngularSharpHigh,firstAngularSharpLow,generatorHigh,generatorLow,
        ContinuousLinearMap.comp_apply] using
        congrArg (fun A : Hi →L[ℝ] Neg => A u) (sphereSobolevRotationL_threehalf_half_compatibility ij.1 ij.2)
    | inr z => exact congrArg (fun A : Hi →L[ℝ] Neg => A u) sphereSobolevShiftedDegree_high_half_compatibility
  | inr a => exact v017_inclusion_raisingHigh hF hO hD a u

theorem firstAngularLow_pairing (v : FirstAngularIndex) (u z : Half) :
    PP u (firstAngularLow hF hO hD v z) = PP z (firstAngularSharpLow hF hO hD v u) := by
  cases v with
  | inl V =>
    cases V with
    | inl ij =>
      have hh := sphereSobolevDualPairing_half_rotation_skew ij.1 ij.2 z u
      have h : PP u (sphereSobolevRotationL (1/2 : ℝ) ij.1 ij.2 z) =
          -PP z (sphereSobolevRotationL (1/2 : ℝ) ij.1 ij.2 u) :=
        (real_inner_comm u (sphereSobolevRotationL (1/2 : ℝ) ij.1 ij.2 z)).symm.trans hh
      change ⟪u,-sphereSobolevRotationL (1/2 : ℝ) ij.1 ij.2 z⟫_ℝ =
        ⟪z,sphereSobolevRotationL (1/2 : ℝ) ij.1 ij.2 u⟫_ℝ
      rw [inner_neg_right]
      change ⟪u,sphereSobolevRotationL (1/2 : ℝ) ij.1 ij.2 z⟫_ℝ =
        -⟪z,sphereSobolevRotationL (1/2 : ℝ) ij.1 ij.2 u⟫_ℝ at h
      linarith only [h]
    | inr z0 =>
      have hh := sphereSobolevDualPairing_lower_distributionalTranspose
        (sphereSobolevShiftedDegreeL (1/2 : ℝ)) z u
      rw [sphereLowerDistributionalTranspose_shiftedDegree_half] at hh
      exact hh
  | inr a => exact v017_pairing_loweringLow_raisingLow hF hO hD a u z

theorem firstAngularSharpLow_pairing (v : FirstAngularIndex) (u z : Half) :
    PP u (firstAngularSharpLow hF hO hD v z) = PP z (firstAngularLow hF hO hD v u) :=
  (firstAngularLow_pairing hF hO hD v z u).symm

theorem lowerSAngularHigh_low_compatibility (v : LowerCoreAngularGeneratorIndex) (u : Hi) :
    JL (lowerSAngularHigh hF hO hD v u) = lowerSAngularLow hF hO hD v (IH u) := by
  cases v with
  | inl z => rfl
  | inr v => exact firstAngularHigh_low_compatibility hF hO hD v u

theorem lowerSAngularSharpHigh_low_compatibility (v : LowerCoreAngularGeneratorIndex) (u : Hi) :
    JL (lowerSAngularSharpHigh hF hO hD v u) = lowerSAngularSharpLow hF hO hD v (IH u) := by
  cases v with
  | inl z => rfl
  | inr v => exact firstAngularSharpHigh_low_compatibility hF hO hD v u

theorem lowerSAngularLow_pairing (v : LowerCoreAngularGeneratorIndex) (u z : Half) :
    PP u (lowerSAngularLow hF hO hD v z) = PP z (lowerSAngularSharpLow hF hO hD v u) := by
  cases v with
  | inl v => exact v016_pairing_inclusion_symm u z
  | inr v => exact firstAngularLow_pairing hF hO hD v u z

theorem lowerSAngularSharpLow_pairing (v : LowerCoreAngularGeneratorIndex) (u z : Half) :
    PP u (lowerSAngularSharpLow hF hO hD v z) = PP z (lowerSAngularLow hF hO hD v u) :=
  (lowerSAngularLow_pairing hF hO hD v z u).symm

theorem ordinarySAngularHigh_low_compatibility (v : OrdinarySAngularIndex) (u : Hi) :
    JL (ordinarySAngularHigh hF hO hD v u) = ordinarySAngularLow hF hO hD v (IH u) :=
  firstAngularSharpHigh_low_compatibility hF hO hD (ordinarySToFirstIndex v) u
theorem ordinarySAngularSharpHigh_low_compatibility (v : OrdinarySAngularIndex) (u : Hi) :
    JL (ordinarySAngularSharpHigh hF hO hD v u) = ordinarySAngularSharpLow hF hO hD v (IH u) :=
  firstAngularHigh_low_compatibility hF hO hD (ordinarySToFirstIndex v) u
theorem ordinarySAngularLow_pairing (v : OrdinarySAngularIndex) (u z : Half) :
    PP u (ordinarySAngularLow hF hO hD v z) = PP z (ordinarySAngularSharpLow hF hO hD v u) :=
  firstAngularSharpLow_pairing hF hO hD (ordinarySToFirstIndex v) u z
theorem ordinarySAngularSharpLow_pairing (v : OrdinarySAngularIndex) (u z : Half) :
    PP u (ordinarySAngularSharpLow hF hO hD v z) = PP z (ordinarySAngularLow hF hO hD v u) :=
  firstAngularLow_pairing hF hO hD (ordinarySToFirstIndex v) u z

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
