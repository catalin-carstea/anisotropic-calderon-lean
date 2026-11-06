import Calderon.ActualLowerUSDPresentations
import Calderon.ActualLowerUSFirstCoefficientJets

/-! The full scalar/angular D on finite tests, against arbitrary Half outputs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
open SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ActualLowerUSGainedDQ ActualLowerUSZeroAngularSum
  ActualFiniteHarmonicModel.ActualLowerUSLowerWordAdjoints
  PrincipalCommutator ReferenceDensityBounds

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

private theorem pairing_inclusion_fintype_sum {ι : Type*} [Fintype ι]
    (z : Half) (c : ι → ℝ) (v : ι → Half) :
    PP z (JL (∑ i : ι, c i • v i)) = ∑ i : ι, c i * PP z (JL (v i)) := by
  simp only [map_sum,map_smul,sphereSobolevDualPairing,inner_sum,real_inner_smul_right]

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (hF : SphereFischerInner) (g g2 : MatrixField) (hg : IsAdmissibleMetric g)
  (hg2 : IsAdmissibleMetric g2) (L q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)
local notation "FC" => smoothCompactFiniteSphereCore hO hD
local notation "LF" => finiteCoreSobolevLift hO hD
local notation "DL" => lowerAdjointFirstLow g L hF hO hD g2 q dr Ar p
local notation "DD" => nativeULowerAdjointFirstCoefficient hO hD hF g g2 hg hg2
  L q dr Ar p hdr hAr
local notation "BN" => (fun i : Fin 3 => nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr)
local notation "dd" => (fun i : Fin 3 => coreDirectionalDerivative hO hD (coordinateDirection i))
local notation "cD" => nativeDFirstCoefficient g g2 L q dr Ar p
local notation "GS" => lowerCoreAngularGeneratorAdjoint hO hD hF

include hg hg2 hdr hAr

private theorem nativeDCoefficient_smooth (i : Fin 3) (v : LowerCoreAngularGeneratorIndex) :
    ContDiff ℝ ∞ (cD i v) := by
  cases v with
  | inl z => exact (contDiff_nativeFirstScalarCoefficient g g2 hg hg2 L q dr Ar p hdr hAr i).neg
  | inr v => exact contDiff_firstAngularCoefficient g g2 hg hg2 L q dr Ar p hdr hAr i v

/-- The complete native Dlow is globally smooth, including its scalar row. -/
theorem contDiff_lowerAdjointFirstLow (i : Fin 3) : ContDiff ℝ ∞ (DL i) := by
  unfold lowerAdjointFirstLow
  exact (((contDiff_nativeFirstScalarCoefficient g g2 hg hg2 L q dr Ar p hdr hAr i).neg).smul
    contDiff_const).add (ContDiff.sum (fun v _ =>
      (contDiff_firstAngularCoefficient g g2 hg hg2 L q dr Ar p hdr hAr i v).smul contDiff_const))

/-- Genuine original Dlow transpose on the finite test; z need not be finite. -/
theorem nativeDlow_finite_pairing (i : Fin 3) (F : FC) (x : R3) (z : Half) :
    PP (LF (1/2 : ℝ) F x) (DL i x z) =
      PP (LF (1/2 : ℝ) ((-BN i) F) x) (JL z) := by
  have hDL : DL i x z = ∑ v : LowerCoreAngularGeneratorIndex,
      cD i v x • lowerSAngularLow hF hO hD v z := by
    simp only [lowerAdjointFirstLow,LowerCoreAngularGeneratorIndex,
      Fintype.sum_sum_type,Fintype.sum_unique,nativeDFirstCoefficient,lowerSAngularLow,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply]
  have hSharp (v : LowerCoreAngularGeneratorIndex) :
      lowerSAngularSharpLow hF hO hD v (LF (1/2 : ℝ) F x) =
        JL (LF (1/2 : ℝ) (GS v F) x) := by
    have hLift : IH (LF (3/2 : ℝ) F x) = LF (1/2 : ℝ) F x :=
      sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) (1/2 : ℝ)
        (by norm_num) F x
    have hHigh : lowerSAngularSharpHigh hF hO hD v (LF (3/2 : ℝ) F x) =
        LF (1/2 : ℝ) (GS v F) x :=
      lowerSAngularSharpHigh_finiteCoreSobolevLift hF hO hD v F x
    calc
      _ = lowerSAngularSharpLow hF hO hD v (IH (LF (3/2 : ℝ) F x)) :=
        congrArg (lowerSAngularSharpLow hF hO hD v) hLift.symm
      _ = JL (lowerSAngularSharpHigh hF hO hD v (LF (3/2 : ℝ) F x)) :=
        (lowerSAngularSharpHigh_low_compatibility hF hO hD v (LF (3/2 : ℝ) F x)).symm
      _ = _ := congrArg JL hHigh
  have hNative : LF (1/2 : ℝ) ((-BN i) F) x =
      ∑ v : LowerCoreAngularGeneratorIndex, cD i v x • LF (1/2 : ℝ) (GS v F) x := by
    rw [nativeDstar_eq_first_presentation hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr i]
    exact finiteCoreSobolevLift_presentation hO hD (1/2 : ℝ) GS (cD i)
      (nativeDCoefficient_smooth g g2 hg hg2 L q dr Ar p hdr hAr i) F x
  calc
    _ = ∑ v : LowerCoreAngularGeneratorIndex, cD i v x *
        PP (LF (1/2 : ℝ) F x) (lowerSAngularLow hF hO hD v z) := by
      rw [hDL]
      simp only [sphereSobolevDualPairing,inner_sum,real_inner_smul_right]
    _ = ∑ v : LowerCoreAngularGeneratorIndex, cD i v x *
        PP z (JL (LF (1/2 : ℝ) (GS v F) x)) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [lowerSAngularLow_pairing,hSharp]
    _ = PP z (JL (LF (1/2 : ℝ) ((-BN i) F) x)) :=
      (pairing_inclusion_fintype_sum z (fun v => cD i v x)
        (fun v => LF (1/2 : ℝ) (GS v F) x)).symm.trans
          (congrArg (fun u : Half => PP z (JL u)) hNative).symm
    _ = _ := v016_pairing_inclusion_symm z (LF (1/2 : ℝ) ((-BN i) F) x)

/-- Exact ordered coefficient derivative graph. It differentiates a global
finite graph with original scalar coefficients, never a closed-room equality. -/
theorem lowerAdjointFirstLow_coefficientDerivative_finite_graph
    (i j : Fin 3) (F : FC) (x : R3) :
    directionalFDeriv (coordinateDirection i) (DL j) x (LF (1/2 : ℝ) F x) =
      LF (-(1/2 : ℝ)) ((ActualModelCommutatorWords.coefficientDerivative (dd i) (DD j)) F) x := by
  have hFun : (fun y => DL j y (LF (1/2 : ℝ) F y)) =
      fun y => LF (-(1/2 : ℝ)) (DD j F) y :=
    funext (lowerAdjointFirstLow_finiteCore_graph hO hD hF g g2 hg hg2
      L q dr Ar p hdr hAr j F)
  have hDiff := congrArg (fun f : R3 → Neg => directionalFDeriv (coordinateDirection i) f x) hFun
  rw [directionalFDeriv_clm_apply (coordinateDirection i) (DL j)
    (finiteCoreSobolevLift hO hD (1/2 : ℝ) F)
    (contDiff_lowerAdjointFirstLow hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr j)
    (contDiff_finiteCoreSobolevLift hO hD (1/2 : ℝ) F)] at hDiff
  simp_rw [directionalFDeriv_finiteCoreSobolevLift] at hDiff
  rw [lowerAdjointFirstLow_finiteCore_graph hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr] at hDiff
  have hLift : LF (-(1/2 : ℝ))
      ((ActualModelCommutatorWords.coefficientDerivative (dd i) (DD j)) F) x =
      LF (-(1/2 : ℝ)) ((dd i) (DD j F)) x -
        LF (-(1/2 : ℝ)) (DD j ((dd i) F)) x := by
    simp only [ActualModelCommutatorWords.coefficientDerivative,ActualModelCommutatorWords.commutator,
      LinearMap.sub_apply,Module.End.mul_apply,finiteCoreSobolevLift,map_sub,
      Submodule.coe_sub,Pi.sub_apply]
  rw [hLift]
  exact eq_sub_of_add_eq hDiff

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
