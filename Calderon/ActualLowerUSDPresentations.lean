import Calderon.ActualLowerUSZeroAngularSum
import Calderon.ActualLowerUSAdjointPresentation
import Calderon.ActualLowerUSFirstAdjointNorm
import Calderon.ActualLowerUSFirstCoefficientJets
import Calderon.ActualLowerUSIndexedAngularGraphs
import Calderon.ActualLowerUSAdjointCore

/-! Original mathematical author: GPT-6.1 Sol, lower_bound_route.
Mechanical module extraction: Root, recorded in ../D-PRESENTATIONS-EXTRACTION-v001.json.
Before-code: ../d-presentation-module-boundary-upfront-v001.md.
Exact full D/Dstar presentations only; no physical Q output or analytic cap. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSGainedDQ
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualFullEGainedEndpoints ActualAngularHighDraft ActualAngularPiDraft
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints ActualLowerUSSecondRow
  ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation NormalizedPrincipalMetric
  ActualFiniteHarmonicModel.ActualLowerUSAdjointPresentation ActualLowerUSZeroAngularSum
  ActualFiniteHarmonicModel.ActualLowerUSLowerWordAdjoints

/-- Original full D scalar and angular coefficients on the lower-only index. -/
def nativeDFirstCoefficient (g g2 : MatrixField) (L q dr Ar : ℝ) (p : ℕ)
    (j : Fin 3) : LowerCoreAngularGeneratorIndex → R3 → ℝ
  | Sum.inl _ => fun x => -nativeFirstScalarCoefficient g g2 L q dr Ar p j x
  | Sum.inr v => fun x => firstAngularCoefficient g L g2 q dr Ar p j x v

theorem contDiff_nativeDFirstCoefficient
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)
    (j : Fin 3) (i : LowerCoreAngularGeneratorIndex) :
    ContDiff ℝ ∞ (nativeDFirstCoefficient g g2 L q dr Ar p j i) := by
  cases i with
  | inl z => exact (contDiff_nativeFirstScalarCoefficient g g2 hg hg2 L q dr Ar p hdr hAr j).neg
  | inr v => exact contDiff_firstAngularCoefficient g g2 hg hg2 L q dr Ar p hdr hAr j v

section NativePresentation
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (hF : SphereFischerInner) (g g2 : MatrixField) (hg : IsAdmissibleMetric g)
  (hg2 : IsAdmissibleMetric g2) (L q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)
local notation "D" j:max => nativeULowerAdjointFirstCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr j
local notation "Bnative" j:max => nativeB hO hD hF g g2 hg L q dr Ar p j hg2 hdr hAr
local notation "GG" => lowerCoreAngularGenerator hO hD hF
local notation "GS" => lowerCoreAngularGeneratorAdjoint hO hD hF
local notation "cD" j:max => nativeDFirstCoefficient g g2 L q dr Ar p j
local notation "hcD" j:max => contDiff_nativeDFirstCoefficient g g2 hg hg2 L q dr Ar p hdr hAr j

/-- Full native D equals this globally smooth scalar presentation. The checked
physical D dictionary and exact indexed finite lifts identify its actual fields. -/
theorem nativeD_eq_first_presentation (j : Fin 3) :
    D j = coreScalarCombination hO hD GG (cD j) (hcD j) := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  have hPhys := lowerAdjointFirstHigh_finiteCore_physical
    hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr j F x
  have hLift := finiteCoreSobolevLift_presentation hO hD (1/2 : ℝ) GG (cD j) (hcD j) F x
  have hSum : lowerAdjointFirstHigh g L hF hO hD g2 q dr Ar p j x
      (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x) =
      ∑ i : LowerCoreAngularGeneratorIndex, (cD j) i x •
        finiteCoreSobolevLift hO hD (1/2 : ℝ) (GG i F) x := by
    simp_rw [← lowerSAngularHigh_finiteCoreSobolevLift hF hO hD]
    simp only [LowerCoreAngularGeneratorIndex,Fintype.sum_sum_type,Fintype.sum_unique,
      nativeDFirstCoefficient,lowerSAngularHigh,lowerAdjointFirstHigh,
      add_apply,smul_apply,sum_apply]
  calc
    _ = sphereSobolevHalfToSphereL2L hO hD
        (lowerAdjointFirstHigh g L hF hO hD g2 q dr Ar p j x
          (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)) := hPhys.symm
    _ = sphereSobolevHalfToSphereL2L hO hD
        (∑ i : LowerCoreAngularGeneratorIndex, (cD j) i x •
          finiteCoreSobolevLift hO hD (1/2 : ℝ) (GG i F) x) := congrArg _ hSum
    _ = sphereSobolevHalfToSphereL2L hO hD
        (finiteCoreSobolevLift hO hD (1/2 : ℝ)
          (coreScalarCombination hO hD GG (cD j) (hcD j) F) x) := congrArg _ hLift.symm
    _ = _ := halfToSphereL2_finiteCoreSobolevLift hO hD _ x

/-- Identify the already fixed genuine sphere adjoint before pairing a full
nonfinite physical Q output. No endpoint is inferred by an adjunction shortcut. -/
theorem nativeDstar_eq_first_presentation (j : Fin 3) :
    -Bnative j = coreScalarCombination hO hD GS (cD j) (hcD j) := by
  apply pointwise_adjoint_unique hO hD (D j)
  · intro F G x
    simpa only [LinearMap.neg_apply,Submodule.coe_neg,Pi.neg_apply] using
      nativeULowerAdjointFirstCoefficient_inner
        hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr j F G x
  · intro F G x
    rw [nativeD_eq_first_presentation hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr j]
    exact coreScalarCombination_inner_adjoint hO hD GG GS
      (fun i U V x => (hasCoreAngularFirstOrderBounds_lowerCoreAngularGenerator hO hD hF i x).2.1 U V)
      (cD j) (hcD j) F G x
end NativePresentation

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSGainedDQ
