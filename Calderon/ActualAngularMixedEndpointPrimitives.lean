import Calderon.ActualPiMixedWeakEndpointCore
import Calderon.ActualAngularFirstOrderMaps
import Calderon.ActualMovingBoundaryTransposeIdentification
import Calderon.NativeRadialJetTranspose
import Calderon.SphereSobolevTangentialEndpointCompatibility
import Calderon.SphereSobolevHalfDualRotationPairing
import Calderon.SphereSobolevCoordinateInclusion
import Calderon.NativeOrderOneCoefficientMultiplier

/-! DRAFT NOT CHECKED (claude-actual-Pi-low-instantiation-2026-10-29-v017, Claude Opus 5.5, author
only, nothing compiled or run). Before-source mathematics: output/MATHEMATICS.md. Root supplied the
routing and the exact API names. v015 (`ActualAngularPiMixedCapsDraft`) and v016
(`ActualAngularPiMixedLowDraft`) are imported unchanged.

Contents:
* §1 Lemma H: the half-level adjunction `P(x, aL_i y) = P(y, AL_i x)` for ALL `x y : Half`.
* §2 Lemma I: the inclusion graphs `J ∘ aH_i = aL_i ∘ IH` and `J ∘ AH_i = AL_i ∘ IH`.
* §3 the cross adjunctions (aA1), (aA2).
* §4 the native Pi primitives (high/half, half/negative, direct adjoint pairing).
* §5 the ACTUAL theorem. It obtains the v015 witnesses once and returns the v015 facts together
  with two actual low families `C_l, D_l` on the SAME witnesses: graphs, weak transpose graphs,
  midpoint norms, `ContDiffOn ∞` on the closed `S`, and one cap per `N`.
NOT claimed: D_Q, absorption, coercivity, Main. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter Metric
open scoped ContDiff ENNReal Topology InnerProductSpace

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft

open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotation MetricOperator
  NormalCoordinatesFrame NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier NativeNegativeHalfSmoothMultiplier ActualAngularHighDraft

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "NegH" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "I33" => sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)

local instance v017PiHighComplete : CompleteSpace (SphereSobolev (3/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance v017PiHalfComplete : CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance v017PiNegativeComplete : CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

local notation "Mh" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ)
  (EuclideanSpace.single j (1 : ℝ))
local notation "Ml" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
  (EuclideanSpace.single j (1 : ℝ))
local notation "Mn" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ))
  (EuclideanSpace.single j (1 : ℝ))
local notation "natH" => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "natL" => nativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "natN" => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "low" => smoothMultiplierLowerJets

/-! ### §1 Lemma H: half-level adjunction (MATHEMATICS.md §2) -/

/-- `P(x, aL_i y) = P(y, AL_i x)` for all `x y : Half`. The rotation terms use (M) and the half
rotation skew. The degree term uses (M) and `(Bl)ᵗ = Bl`. There is no extra factor or sign. -/
theorem v017_pairing_loweringLow_raisingLow (i : Fin 3) (x y : Half) :
    PP x (loweringLow hF hO hD i y) = PP y (raisingLow hF hO hD i x) := by
  have hTerm (j : Fin 3) :
      ⟪x, (Mn j) (sphereSobolevRotationL (1/2 : ℝ) j i y)⟫_ℝ =
        -⟪y, sphereSobolevRotationL (1/2 : ℝ) j i ((Ml j) x)⟫_ℝ := by
    have hM := sphereSobolevDualPairing_linearCoordinate_half_duality hF hO hD
      (EuclideanSpace.single j 1) (sphereSobolevRotationL (1/2 : ℝ) j i y) x
    have hSwap : ⟪(Ml j) x, sphereSobolevRotationL (1/2 : ℝ) j i y⟫_ℝ =
        ⟪sphereSobolevRotationL (1/2 : ℝ) j i y, (Ml j) x⟫_ℝ := real_inner_comm _ _
    exact hM.trans (hSwap.trans (sphereSobolevDualPairing_half_rotation_skew j i y ((Ml j) x)))
  have hDeg :
      ⟪x, (Mn i) (sphereSobolevShiftedDegreeL (1/2 : ℝ) y)⟫_ℝ =
        ⟪y, sphereSobolevShiftedDegreeL (1/2 : ℝ) ((Ml i) x)⟫_ℝ := by
    have hM := sphereSobolevDualPairing_linearCoordinate_half_duality hF hO hD
      (EuclideanSpace.single i 1) (sphereSobolevShiftedDegreeL (1/2 : ℝ) y) x
    have hT := sphereSobolevDualPairing_lower_distributionalTranspose
      (sphereSobolevShiftedDegreeL (1/2 : ℝ)) y ((Ml i) x)
    rw [sphereLowerDistributionalTranspose_shiftedDegree_half] at hT
    exact hM.trans hT
  change ⟪x, loweringLow hF hO hD i y⟫_ℝ = ⟪y, raisingLow hF hO hD i x⟫_ℝ
  simp only [loweringLow, raisingLow, ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, inner_add_right,
    inner_neg_right, inner_sum]
  rw [← Finset.sum_neg_distrib]
  exact congrArg₂ (fun a b : ℝ => a + b) (Finset.sum_congr rfl (fun j _ => hTerm j)) hDeg

/-! ### §2 Lemma I: inclusion graphs (MATHEMATICS.md §3) -/

/-- (I-a) `J (aH_i x) = aL_i (IH x)`. -/
theorem v017_inclusion_loweringHigh (i : Fin 3) (x : Hi) :
    JL (loweringHigh hF hO hD i x) = loweringLow hF hO hD i (IH x) := by
  have hRot (j : Fin 3) : JL (sphereSobolevRotationL (3/2 : ℝ) j i x) =
      sphereSobolevRotationL (1/2 : ℝ) j i (IH x) :=
    congrArg (fun A : Hi →L[ℝ] NegH => A x)
      (sphereSobolevRotationL_threehalf_half_compatibility j i)
  have hDeg : JL (sphereSobolevShiftedDegreeL (3/2 : ℝ) x) =
      sphereSobolevShiftedDegreeL (1/2 : ℝ) (IH x) :=
    congrArg (fun A : Hi →L[ℝ] NegH => A x) sphereSobolevShiftedDegree_high_half_compatibility
  have hM (j : Fin 3) (v : Half) : JL ((Ml j) v) = (Mn j) (JL v) :=
    sphereSobolevInclusionL_linearCoordinateMul hF hO hD (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) _ v
  simp only [loweringHigh, loweringLow, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, map_add, map_sum, hM, hRot,
    hDeg]

/-- (I-A) `J (AH_i x) = AL_i (IH x)`. -/
theorem v017_inclusion_raisingHigh (i : Fin 3) (x : Hi) :
    JL (raisingHigh hF hO hD i x) = raisingLow hF hO hD i (IH x) := by
  have hRot (j : Fin 3) (v : Hi) : JL (sphereSobolevRotationL (3/2 : ℝ) j i v) =
      sphereSobolevRotationL (1/2 : ℝ) j i (IH v) :=
    congrArg (fun A : Hi →L[ℝ] NegH => A v)
      (sphereSobolevRotationL_threehalf_half_compatibility j i)
  have hDeg (v : Hi) : JL (sphereSobolevShiftedDegreeL (3/2 : ℝ) v) =
      sphereSobolevShiftedDegreeL (1/2 : ℝ) (IH v) :=
    congrArg (fun A : Hi →L[ℝ] NegH => A v) sphereSobolevShiftedDegree_high_half_compatibility
  have hM (j : Fin 3) : IH ((Mh j) x) = (Ml j) (IH x) :=
    sphereSobolevInclusionL_linearCoordinateMul hF hO hD (3/2 : ℝ) (1/2 : ℝ) (by norm_num) _ x
  simp only [raisingHigh, raisingLow, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    map_add, map_neg, map_sum, hRot, hDeg, hM]

/-! ### §3 Cross adjunctions (aA1), (aA2) (MATHEMATICS.md §4) -/

theorem v017_aA1 (i : Fin 3) (x : Hi) (y : Half) :
    PP (IH x) (loweringLow hF hO hD i y) = PP y (JL (raisingHigh hF hO hD i x)) := by
  rw [v017_inclusion_raisingHigh hF hO hD i x]
  exact v017_pairing_loweringLow_raisingLow hF hO hD i (IH x) y

theorem v017_aA2 (i : Fin 3) (x : Hi) (y : Half) :
    PP (loweringHigh hF hO hD i x) (JL y) = PP (IH x) (raisingLow hF hO hD i y) := by
  rw [v016_pairing_inclusion_symm, v017_inclusion_loweringHigh hF hO hD i x]
  exact v017_pairing_loweringLow_raisingLow hF hO hD i y (IH x)

/-! ### §4 Native Pi primitives (MATHEMATICS.md §1, §5) -/

/-- (Πc) `IH ∘ natH Q = natL (low Q) ∘ IH`, from the exact coefficient-value identity. -/
theorem v017_native_high_half (Q : SmoothCoefficientJets 3) (z : Hi) :
    IH (natH Q z) = natL (low Q) (IH z) :=
  congrArg (fun A : Hi →L[ℝ] Half => A z)
    (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 Q (low Q)
      (coefficientValue_smoothMultiplierLowerJets Q).symm)

/-- (ΠN) `J ∘ natL F = natN F ∘ J`. -/
theorem v017_native_half_negative (F : SmoothCoefficientJets 2) (y : Half) :
    JL (natL F y) = natN F (JL y) :=
  congrArg (fun A : Half →L[ℝ] NegH => A y)
    (nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0 F)

/-- (Πs) `P(natL F x, y) = P(x, natN F y)`. `natN F` is by definition the real Hilbert adjoint
of `natL F`. -/
theorem v017_native_pairing (F : SmoothCoefficientJets 2) (x : Half) (y : NegH) :
    PP (natL F x) y = PP x (natN F y) := by
  exact (ContinuousLinearMap.adjoint_inner_right (natL F) x y).symm


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft
