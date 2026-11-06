import Calderon.ActualLowerUSOrdinaryAngularMaps
import Calderon.ActualCanonicalGeneratorAngularGainedRows

/-! GPT-6.1 Sol. Before-code ordinary-angular-before-v001. Actual completed
rotation Lie and degree/rotation graphs, via the canonical dense single basis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
open SphereHarmonic SmoothSphereRotationProjection ActualFiniteHarmonicModel
  ActualCanonicalAngularGainedBracket ActualCanonicalGeneratorAngularGainedRows
  ActualAngularHighDraft ActualAngularPiDraft

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "RH" => sphereSobolevRotationL (3/2 : ℝ)
local notation "RL" => sphereSobolevRotationL (1/2 : ℝ)
local notation "BH" => sphereSobolevShiftedDegreeL (3/2 : ℝ)
local notation "BL" => sphereSobolevShiftedDegreeL (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

def rotationLieHigh (i j a b : Fin 3) : Hi →L[ℝ] Half :=
  (if j=a then (1:ℝ) else 0) • RH i b - (if j=b then (1:ℝ) else 0) • RH i a -
    (if i=a then (1:ℝ) else 0) • RH j b + (if i=b then (1:ℝ) else 0) • RH j a
def rotationLieLow (i j a b : Fin 3) : Half →L[ℝ] Neg :=
  (if j=a then (1:ℝ) else 0) • RL i b - (if j=b then (1:ℝ) else 0) • RL i a -
    (if i=a then (1:ℝ) else 0) • RL j b + (if i=b then (1:ℝ) else 0) • RL j a

private lemma rotationHigh_single (i j : Fin 3) (k : ℕ) (v : harmonicSphereSubspace k) :
    RH i j (sphereSobolevSingleL (3/2 : ℝ) k v) =
      sphereSobolevSingleL (1/2 : ℝ) k (harmonicSphereRotation k i j v) := by
  simpa only [sphereSobolevSingleL,show (3/2 : ℝ)-1 = (1/2 : ℝ) by norm_num] using
    sphereSobolevRotationL_single (3/2 : ℝ) i j k v
private lemma rotationLow_single (i j : Fin 3) (k : ℕ) (v : harmonicSphereSubspace k) :
    RL i j (sphereSobolevSingleL (1/2 : ℝ) k v) =
      sphereSobolevSingleL (-(1/2 : ℝ)) k (harmonicSphereRotation k i j v) := by
  simpa only [sphereSobolevSingleL,show (1/2 : ℝ)-1 = (-(1/2) : ℝ) by norm_num] using
    sphereSobolevRotationL_single (1/2 : ℝ) i j k v
private lemma degreeHigh_single (k : ℕ) (v : harmonicSphereSubspace k) :
    BH (sphereSobolevSingleL (3/2 : ℝ) k v) =
      (k:ℝ) • sphereSobolevSingleL (1/2 : ℝ) k v := by
  simpa only [sphereSobolevSingleL,show (3/2 : ℝ)-1 = (1/2 : ℝ) by norm_num] using
    sphereSobolevShiftedDegreeL_single (3/2 : ℝ) k v
private lemma degreeLow_single (k : ℕ) (v : harmonicSphereSubspace k) :
    BL (sphereSobolevSingleL (1/2 : ℝ) k v) =
      (k:ℝ) • sphereSobolevSingleL (-(1/2 : ℝ)) k v := by
  simpa only [sphereSobolevSingleL,show (1/2 : ℝ)-1 = (-(1/2) : ℝ) by norm_num] using
    sphereSobolevShiftedDegreeL_single (1/2 : ℝ) k v

/-- Completed-space rotation Lie graph. The dense-single theorem is the
checked extension step; no unproved finite-to-completed implication is used. -/
theorem rotationLieHigh_graph (i j a b : Fin 3) :
    (JL).comp (rotationLieHigh i j a b) = (RL i j).comp (RH a b) - (RL a b).comp (RH i j) := by
  apply sphereSobolev_clm_eq_of_single (3/2 : ℝ)
  intro k v
  have hLie := harmonicSphereRotation_lie_commutator k i j a b v
  have hs := congrArg (sphereSobolevSingleL (-(1/2 : ℝ)) k) hLie.symm
  simp only [rotationLieHigh,ContinuousLinearMap.comp_apply,add_apply,sub_apply,smul_apply,
    map_add,map_sub,map_smul,rotationHigh_single,rotationLow_single,sphereSobolevInclusionL_single]
  simpa only [map_add,map_sub,apply_ite,map_zero,ite_smul,one_smul,zero_smul] using hs

theorem rotationLieHigh_low_compatibility (i j a b : Fin 3) :
    (rotationLieLow i j a b).comp IH = (JL).comp (rotationLieHigh i j a b) := by
  apply ContinuousLinearMap.ext
  intro u
  have hR (s t : Fin 3) : RL s t (IH u) = JL (RH s t u) := by
    have hh := congrArg (fun A : Hi →L[ℝ] Neg => A u)
      (sphereSobolevRotationL_threehalf_half_compatibility s t)
    simpa only [ContinuousLinearMap.comp_apply] using hh.symm
  simp only [rotationLieLow,rotationLieHigh,ContinuousLinearMap.comp_apply,add_apply,sub_apply,
    smul_apply,map_add,map_sub,map_smul,hR]

theorem degree_rotation_commutator_zero (i j : Fin 3) :
    (BL).comp (RH i j) - (RL i j).comp BH = 0 := by
  apply sphereSobolev_clm_eq_of_single (3/2 : ℝ)
  intro k v
  simp only [ContinuousLinearMap.comp_apply,sub_apply,ContinuousLinearMap.zero_apply,
    rotationHigh_single,rotationLow_single,degreeHigh_single,degreeLow_single,map_smul,sub_self]

theorem rotation_degree_commutator_zero (i j : Fin 3) :
    (RL i j).comp BH - (BL).comp (RH i j) = 0 := by
  have h := degree_rotation_commutator_zero i j
  exact sub_eq_zero.mpr (sub_eq_zero.mp h).symm

theorem degree_degree_commutator_zero : (BL).comp BH - (BL).comp BH = 0 := sub_self _

/-- The Lie row is skew under the original Half dual pairing. -/
theorem rotationLieLow_pairing (i j a b : Fin 3) (u z : Half) :
    sphereSobolevDualPairing (1/2 : ℝ) u (rotationLieLow i j a b z) =
      -sphereSobolevDualPairing (1/2 : ℝ) z (rotationLieLow i j a b u) := by
  have hR (s t : Fin 3) : sphereSobolevDualPairing (1/2 : ℝ) u (RL s t z) =
      -sphereSobolevDualPairing (1/2 : ℝ) z (RL s t u) :=
    (real_inner_comm u (RL s t z)).symm.trans
      (sphereSobolevDualPairing_half_rotation_skew s t z u)
  change (∀ s t : Fin 3, ⟪u,RL s t z⟫_ℝ = -⟪z,RL s t u⟫_ℝ) at hR
  change ⟪u,rotationLieLow i j a b z⟫_ℝ = -⟪z,rotationLieLow i j a b u⟫_ℝ
  simp only [rotationLieLow,add_apply,sub_apply,smul_apply,inner_add_right,inner_sub_right,
    real_inner_smul_right]
  simp_rw [hR]
  ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
