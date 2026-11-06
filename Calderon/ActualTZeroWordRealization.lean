import Calderon.ActualTSZeroWordPairing
import Calderon.ActualTZeroGenuineReverse

/-!
Before-code: ../T-S-L00-weighted-assembly-before-source-nov03-night-v001/.
Exact ORIGINAL T-zero finite word realization. All lifts are on original finite
input. Raw adjoint corrections and original coefficients/norms are retained.
This does not yet identify the full coefficient-weighted physical L00 pairing.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTZeroWordRealization
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAllAngularAtomGainedRoom ActualTZeroGenuineReverse ActualReferenceZeroECommutators
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ActualTZeroNegativeGraph ActualFixedAtomFiniteLifts AmbientReferenceRaising
  ConformalDepth ReferenceDensityBounds SmoothMetricFrame MovingFrameConnection

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "DL" => sphereSobolevShiftedDegreeL (3/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def highNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def highSpace : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
attribute [local instance] highNormed highSpace

variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3))
  (ε C ρ : ℝ) (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
local notation "ARoom" d:max => AllAngularAtomRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data d


local notation "Tq" => ActualHigherSFormation.higherSParam L
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "cc" => referenceAngularZeroCoefficient g L
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "VA" => ActualHigherSQuadraticZeroQuartic.actualAtomHi
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "VB" => ActualHigherSQuadraticZeroQuartic.actualReverseAtomHi
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "AH" => angularAtomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RH" => angularAtomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RHalf" => genuineReferenceZeroReverseHalf hF hO hD g L
local notation "fi" q:max dr:max Ar:max p:max x:max i:max =>
  referenceFrameDerivative g L q i (fun y => Real.log (referenceRadius dr Ar p L y)) x

/-- Literal thirty forward T-zero words using existing finite generator high lifts. -/
def referenceZeroForwardWordHalf (q dr Ar : ℝ) (p : ℕ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : Half :=
  ∑ i : Fin 3, ∑ V : Generator, cc q dr Ar p x i V •
    raisingHigh hF hO hD i (VA dr Ar p q F x (Sum.inr (Sum.inl V)))
local notation "FHalf" => referenceZeroForwardWordHalf
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data

attribute [local irreducible] raisingHigh raisingLow generatorHigh generatorLow
  generatorSharpHigh generatorSharpLow sphereSobolevInclusionL sphereSobolevShiftedDegreeL
  referenceHighHorizontalAngularL referenceAngularHigh referenceZeroNegative
  angularAtomHigh angularAtomLow angularAtomReverseHigh
  ActualHigherSFormation.higherSInput ActualHigherSQuadraticZeroQuartic.actualAtomHi
  ActualHigherSQuadraticZeroQuartic.actualReverseAtomHi referenceZeroForwardWordHalf

/-- Only the generator branch of the already existing original finite-input lifts. -/
private lemma generator_input_inclusion (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (V : Generator) :
    IH (VA dr Ar p q F x (Sum.inr (Sum.inl V)))=generatorHigh V (UF F x) := by
  cases V with
  | inl ij =>
    simpa only [ActualHigherSQuadraticZeroQuartic.actualAtomHi,generatorHigh,
      ActualHigherSFormation.higherSInput] using rotationFiniteHi_inclusion hO hD F ij.1 ij.2 x
  | inr z =>
    simpa only [ActualHigherSQuadraticZeroQuartic.actualAtomHi,generatorHigh,
      ActualHigherSFormation.higherSInput] using
      DegreeGraphLifting.inclusion_finiteCoreSobolevLift_coreDegree hO hD F x

private lemma reference_zero_negative_apply_words (q dr Ar : ℝ) (p : ℕ) (x : R3) (U : Hi) :
    referenceZeroNegative hO hD hF g L q dr Ar p x U =
      ∑ i : Fin 3, ∑ V : Generator, cc q dr Ar p x i V •
        raisingLow hF hO hD i (generatorHigh V U) := by
  have hFactor (i : Fin 3) :
      (referenceHighHorizontalAngularL g L q x i+fi q dr Ar p x i • DL) U =
        ∑ V : Generator, cc q dr Ar p x i V • generatorHigh V U := by
    have h := congrArg (fun A : Hi →L[ℝ] Half => A U)
      (referenceAngularHigh_eq g L q dr Ar p x i)
    exact h.symm.trans (by
      simp only [referenceAngularHigh,_root_.sum_apply,_root_.smul_apply])
  calc
    _ = ∑ i : Fin 3, raisingLow hF hO hD i
        ((referenceHighHorizontalAngularL g L q x i+fi q dr Ar p x i • DL) U) := by
      simp only [referenceZeroNegative,_root_.sum_apply,ContinuousLinearMap.comp_apply]
    _ = _ := by
      simp_rw [hFactor]
      simp only [map_sum,map_smul]

/-- Exact original negative graph for the thirty-word forward field. -/
theorem forward_word_negative_graph {d : ℝ} (P : ARoom d)
    (q dr Ar : ℝ) (p : ℕ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (ht : (Tq dr Ar p q) x ∈ ParamRoom d) :
    JL (FHalf q dr Ar p F x)=referenceZeroNegative hO hD hF g L q dr Ar p x (UF F x) := by
  let t := (Tq dr Ar p q) x
  have hRow (i : Fin 3) (V : Generator) :
      JL (raisingHigh hF hO hD i (VA dr Ar p q F x (Sum.inr (Sum.inl V)))) =
        raisingLow hF hO hD i (generatorHigh V (UF F x)) := by
    have h := P.atomGraph (Sum.inr (Sum.inr i)) t ht
      (VA dr Ar p q F x (Sum.inr (Sum.inl V)))
    have hA : JL (raisingHigh hF hO hD i (VA dr Ar p q F x (Sum.inr (Sum.inl V)))) =
        raisingLow hF hO hD i (IH (VA dr Ar p q F x (Sum.inr (Sum.inl V)))) := by
      simpa only [angularAtomHigh,angularAtomLow] using h
    exact hA.trans (congrArg (raisingLow hF hO hD i)
      (generator_input_inclusion hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
        Room hreg data dr Ar p q F x V))
  calc
    _ = ∑ i : Fin 3, ∑ V : Generator, cc q dr Ar p x i V •
        raisingLow hF hO hD i (generatorHigh V (UF F x)) := by
      simp only [referenceZeroForwardWordHalf,map_sum,map_smul]
      simp_rw [hRow]
    _ = _ := (reference_zero_negative_apply_words hF hO hD g L q dr Ar p x (UF F x)).symm

/-- The original actual finite T-zero Half field, by genuine inclusion injectivity. -/
theorem native_zero_half_eq_forward_words {d : ℝ} (P : ARoom d)
    (q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (ht : (Tq dr Ar p q) x ∈ ParamRoom d) :
    finiteCoreSobolevLift hO hD (1/2 : ℝ)
      (nativeReferenceZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F) x =
        FHalf q dr Ar p F x := by
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  have hN : JL (finiteCoreSobolevLift hO hD (1/2 : ℝ)
      (nativeReferenceZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F) x) =
      referenceZeroNegative hO hD hF g L q dr Ar p x (UF F x) := by
    simpa only [ActualHigherSFormation.higherSInput] using
      native_zero_negative_graph hO hD hF g hg L q dr Ar p hdr hAr F x
  exact hN.trans (forward_word_negative_graph
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data P q dr Ar p F x ht).symm

/-- The original genuine reverse field is exactly the reverse actual atom-word sum. -/
theorem genuine_reverse_half_eq_actual_word_sum
    (q dr Ar : ℝ) (p : ℕ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    RHalf q dr Ar p F x =
      ∑ i : Fin 3, ∑ V : Generator, cc q dr Ar p x i V •
        RH ((Tq dr Ar p q) x) (Sum.inr (Sum.inl V))
          (VB dr Ar p q F x (Sum.inr (Sum.inr i))) := by
  simp only [genuineReferenceZeroReverseHalf,angularAtomReverseHigh,
    ActualHigherSQuadraticZeroQuartic.actualReverseAtomHi]

/-- Forward actual atom-word sum, with no operator or coefficient convention change. -/
theorem forward_half_eq_actual_word_sum
    (q dr Ar : ℝ) (p : ℕ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    FHalf q dr Ar p F x =
      ∑ i : Fin 3, ∑ V : Generator, cc q dr Ar p x i V •
        AH ((Tq dr Ar p q) x) (Sum.inr (Sum.inr i))
          (VA dr Ar p q F x (Sum.inr (Sum.inl V))) := by
  simp only [referenceZeroForwardWordHalf,angularAtomHigh]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTZeroWordRealization
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTZeroWordRealization.native_zero_half_eq_forward_words
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTZeroWordRealization.genuine_reverse_half_eq_actual_word_sum
