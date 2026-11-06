import Calderon.ActualHigherSMixedCubicPhysicalExpansion
import Calderon.ActualHigherSAllAtomProfileFirstCaps
import Calderon.ActualHigherSMixedWordScalarUniformCaps
import Calderon.ActualHigherSMixedWordScalarSmooth
import Calderon.ActualHigherSCubicProductDerivative
import Calderon.ActualHigherSMixedCubicAbsorption
import Calderon.ActualHigherSCubicIntegration
import Calderon.ActualLowerSSelfFormation

/-! Complete original-data mixed P/Z2 weak expansion and uniform estimate.
All derived room/profile/cap hypotheses below are internal interface facts; the
public uniform producers retain only the original hypotheses. Uncompiled author
integration: own native qualifications and conditional imports are recorded in
CORRESPONDENCE.json; no independent review or canonical acceptance claimed. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSActualCubicBound
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ConformalDepth
  ActualHigherSQuadraticZeroWords ActualFixedAtomFiniteLifts ActualRetainedGeneratorMultiplierGains
  ActualHigherSQuadraticZeroQuartic PrincipalCommutator ReferenceWeightedApproximation
  ActualHigherSActualCubicPairing ActualScalarPrincipalSelfFormBound SectionFiveErrorForms
  ActualNormalizedSecondMetricDrift SmoothMetricFrame
open ReferenceDensityBounds FixedParameterProfilePullback
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "PL" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

/- Expose only the original canonical CLM structures locally. Each right-hand
side is Mathlib's existing standard construction, not a different norm. -/
@[instance_reducible] private def negDualNormed : NormedAddCommGroup (Neg →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := Neg) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
attribute [local instance] negDualNormed
@[instance_reducible] private def negDualSpace : NormedSpace ℝ (Neg →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (E := Neg) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
attribute [local instance] negDualSpace
@[instance_reducible] private def coefficientLowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := Half) (F := Neg) (σ₁₂ := RingHom.id ℝ)
attribute [local instance] coefficientLowNormed
@[instance_reducible] private def coefficientLowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) :=
  ContinuousLinearMap.toNormedSpace (E := Half) (F := Neg) (σ₁₂ := RingHom.id ℝ)
attribute [local instance] coefficientLowSpace
@[instance_reducible] private def highDualNormed : NormedAddCommGroup (Hi →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := Hi) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
attribute [local instance] highDualNormed
@[instance_reducible] private def highDualSpace : NormedSpace ℝ (Hi →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (E := Hi) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
attribute [local instance] highDualSpace
@[instance_reducible] private def highFormNormed : NormedAddCommGroup (Hi →L[ℝ] Hi →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := Hi) (F := Hi →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
attribute [local instance] highFormNormed
@[instance_reducible] private def highFormSpace : NormedSpace ℝ (Hi →L[ℝ] Hi →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (E := Hi) (F := Hi →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
attribute [local instance] highFormSpace
@[instance_reducible] private def pairingFormNormed : NormedAddCommGroup (Half →L[ℝ] Neg →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := Half) (F := Neg →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
attribute [local instance] pairingFormNormed
@[instance_reducible] private def pairingFormSpace : NormedSpace ℝ (Half →L[ℝ] Neg →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace (E := Half) (F := Neg →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
attribute [local instance] pairingFormSpace

private lemma high_forms_isBoundedSMul : IsBoundedSMul ℝ (Hi →L[ℝ] Hi →L[ℝ] ℝ) := by
  have h := NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := Hi →L[ℝ] Hi →L[ℝ] ℝ)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq, normedAddCommGroup_ofSeparation_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] at h
  exact h
attribute [local instance] high_forms_isBoundedSMul

private lemma native_pairing_zero_right (v : Half) : PP v (0 : Neg) = 0 := by
  change PL v (0 : Neg) = 0
  exact map_zero (PL v)

private lemma native_pairing_zero_zero : PP (0 : Half) (0 : Neg) = 0 :=
  native_pairing_zero_right (0 : Half)

private lemma integrable_sub_lambda (f g : R3 → ℝ) (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun x => f x-g x) := by
  have he : (f-g) = fun x => f x-g x := by funext x; rfl
  rw [← he]
  exact hf.sub hg

private lemma integrable_weighted_difference (mu A B : R3 → ℝ)
    (hA : Integrable (fun x => mu x*A x)) (hB : Integrable (fun x => mu x*B x)) :
    Integrable (fun x => mu x*(A x-B x)) := by
  have he : ((fun x => mu x*A x)-(fun x => mu x*B x)) =
      fun x => mu x*(A x-B x) := by
    funext x
    exact (mul_sub _ _ _).symm
  rw [← he]
  exact hA.sub hB

private lemma integral_three_difference (f g h : R3 → ℝ)
    (hf : Integrable f) (hg : Integrable g) (hh : Integrable h) :
    (∫ x, f x-g x-h x) = (∫ x, f x)-(∫ x, g x)-(∫ x, h x) := by
  calc
    (∫ x, f x-g x-h x) = (∫ x, f x-g x)-(∫ x, h x) :=
      integral_sub (f := fun x => f x-g x) (g := h) (integrable_sub_lambda f g hf hg) hh
    _ = (∫ x, f x)-(∫ x, g x)-(∫ x, h x) :=
      congrArg (fun r : ℝ => r-(∫ x, h x)) (integral_sub hf hg)

private lemma row_integration_transport (mu A B S D C W : R3 → ℝ)
    (hA : Integrable (fun x => mu x*A x)) (hB : Integrable (fun x => mu x*B x))
    (hD : Integrable D) (hC : Integrable C)
    (hSkew : (fun x => mu x*(A x-B x)) = S)
    (hWeak : W = fun x => S x-D x-C x)
    (hIBP : 2*(∫ x, mu x*A x) = (∫ x, mu x*(A x-B x))-(∫ x, D x)-(∫ x, C x)) :
    Integrable (fun x => mu x*A x) ∧ Integrable (fun x => mu x*B x) ∧
    Integrable S ∧ Integrable D ∧ Integrable C ∧ Integrable W ∧
      2*(∫ x, mu x*A x) = ∫ x, W x := by
  have hS : Integrable S := by
    rw [← hSkew]
    exact integrable_weighted_difference mu A B hA hB
  have hW : Integrable W := by
    rw [hWeak]
    exact integrable_sub_lambda _ _ (integrable_sub_lambda _ _ hS hD) hC
  refine ⟨hA,hB,hS,hD,hC,hW,?_⟩
  rw [hSkew] at hIBP
  rw [hWeak, integral_three_difference _ _ _ hS hD hC]
  exact hIBP

private lemma raw_row_integration_transport (mu A B D0 C0 D C : R3 → ℝ)
    (hDensity : D0 = D) (hCoefficient : C0 = C)
    (hRaw : Integrable (fun x => mu x*A x) ∧ Integrable (fun x => mu x*B x) ∧
      Integrable D0 ∧ Integrable C0 ∧
      2*(∫ x, mu x*A x) = (∫ x, mu x*(A x-B x))-(∫ x, D0 x)-(∫ x, C0 x)) :
    Integrable (fun x => mu x*A x) ∧ Integrable (fun x => mu x*B x) ∧
      Integrable D ∧ Integrable C ∧
      2*(∫ x, mu x*A x) = (∫ x, mu x*(A x-B x))-(∫ x, D x)-(∫ x, C x) := by
  rw [hDensity, hCoefficient] at hRaw
  exact hRaw

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BL" => orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "GG" => fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  Room hreg data.Gcoord data.GN data.δ0 data.germs
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "VF" => ActualHigherSFormation.higherSLift hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "VR" => ActualReverseEHigherLift.reverseEHigherLift g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "FD" => ActualHigherSFormation.higherSDoubleHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "RD" => ActualCommonFirstWordQuadraticAdjoint.revDoubleHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

local notation "AH" => atomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "AL" => atomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RH" => atomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RL" => atomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ARoom" d:max => ActualAllAngularAtomGainedRoom.AllAngularAtomRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data d
local notation "WC" => actualWordCoefficient g L

local notation "Z2" => actualZ2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "T2" => actualT2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "PF" => ActualPPLowerRemainder.actualPPFirstOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PR" => ActualPPLowerRemainder.actualPPReverseFirstOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  atomHigh atomLow atomReverseHigh atomReverseLow sphereSobolevInclusionL

def actualMixedCubicForm (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (k i : Fin 3) (z : ZeroWord) (x : R3) : Hi →L[ℝ] Hi →L[ℝ] ℝ :=
  mixedWordScalar g L g2 dr Ar p q k i z x •
    cubicAtomForm g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 ((Tq dr Ar p q) x)
      (eAtom i) (wordAtoms z).1 (wordAtoms z).2
local notation "QMix" => actualMixedCubicForm
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

def actualMixedCubicCoefficientDerivative (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (k i : Fin 3) (z : ZeroWord) : ℝ :=
  let A : ZeroAtom → R3 → Hi →L[ℝ] Half := fun aa y => AH ((Tq dr Ar p q) y) aa
  let Bv : ZeroAtom → R3 → Hi →L[ℝ] Half := fun aa y => RH ((Tq dr Ar p q) y) aa
  let Lw : ZeroAtom → R3 → Half →L[ℝ] Neg := fun aa y => AL ((Tq dr Ar p q) y) aa
  let Rw : ZeroAtom → R3 → Half →L[ℝ] Neg := fun aa y => RL ((Tq dr Ar p q) y) aa
  let aa := eAtom i
  let bb := (wordAtoms z).1
  let cc := (wordAtoms z).2
  let U := UF F x
  let X := coordinateDirection k
  let s := mixedWordScalar g L g2 dr Ar p q k i z
  directionalFDeriv X s x *
      (PP (A aa x U) (Lw bb x (A cc x U)) + PP (Bv aa x U) (Rw cc x (Bv bb x U))) +
    s x *
      (PP (directionalFDeriv X (A aa) x U) (Lw bb x (A cc x U)) +
        PP (A aa x U) (directionalFDeriv X (Lw bb) x (A cc x U)) +
        PP (A aa x U) (Lw bb x (directionalFDeriv X (A cc) x U)) +
        (PP (directionalFDeriv X (Bv aa) x U) (Rw cc x (Bv bb x U)) +
        PP (Bv aa x U) (directionalFDeriv X (Rw cc) x (Bv bb x U)) +
        PP (Bv aa x U) (Rw cc x (directionalFDeriv X (Bv bb) x U))))
local notation "CoeffDeriv" => actualMixedCubicCoefficientDerivative
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Positive forward cubic contribution, including its full scalar and density. -/
def actualMixedCubicForwardRow (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (k i : Fin 3) (z : ZeroWord) : ℝ :=
  referenceDensityFamily g L (q,x)*(mixedWordScalar g L g2 dr Ar p q k i z x *
    PP (AH ((Tq dr Ar p q) x) (eAtom i) (directionalFDeriv (coordinateDirection k) (UF F) x))
      (AL ((Tq dr Ar p q) x) (wordAtoms z).1 (AH ((Tq dr Ar p q) x) (wordAtoms z).2 (UF F x))))

/-- Positive reverse cubic contribution, from subtracting the genuine negative reverse first field. -/
def actualMixedCubicReverseRow (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (k i : Fin 3) (z : ZeroWord) : ℝ :=
  referenceDensityFamily g L (q,x)*(mixedWordScalar g L g2 dr Ar p q k i z x *
    PP (RH ((Tq dr Ar p q) x) (eAtom i) (directionalFDeriv (coordinateDirection k) (UF F) x))
      (RL ((Tq dr Ar p q) x) (wordAtoms z).2 (RH ((Tq dr Ar p q) x) (wordAtoms z).1 (UF F x))))
local notation "ForwardRow" => actualMixedCubicForwardRow
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ReverseRow" => actualMixedCubicReverseRow
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

def actualMixedCubicSkewRow {d : ℝ} (P : ARoom d) (g2 : MatrixField)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD)
    (x : R3) (k i : Fin 3) (z : ZeroWord) : ℝ :=
  referenceDensityFamily g L (q,x)*mixedWordScalar g L g2 dr Ar p q k i z x *
    cubicSkewRow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P
      ((Tq dr Ar p q) x)
      (directionalFDeriv (coordinateDirection k) (ActualHigherSScalarCommutatorNativeForm.halfInput hO hD F) x)
      (UF F x) (eAtom i) (wordAtoms z).1 (wordAtoms z).2

def actualMixedCubicDensityRow (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (k i : Fin 3) (z : ZeroWord) : ℝ :=
  directionalFDeriv (coordinateDirection k) (fun y => referenceDensityFamily g L (q,y)) x *
    mixedWordScalar g L g2 dr Ar p q k i z x *
      cubicAtomForm g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 ((Tq dr Ar p q) x)
        (eAtom i) (wordAtoms z).1 (wordAtoms z).2 (UF F x) (UF F x)

def actualMixedCubicCoefficientRow (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (k i : Fin 3) (z : ZeroWord) : ℝ :=
  referenceDensityFamily g L (q,x)*CoeffDeriv g2 dr Ar p q F x k i z

local notation "Skew" => actualMixedCubicSkewRow
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "Density" => actualMixedCubicDensityRow
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Coefficient" => actualMixedCubicCoefficientRow
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

def actualMixedCubicWeakRow {d : ℝ} (P : ARoom d) (g2 : MatrixField)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD)
    (x : R3) (k i : Fin 3) (z : ZeroWord) : ℝ :=
  Skew P g2 dr Ar p q F x k i z - Density g2 dr Ar p q F x k i z -
    Coefficient g2 dr Ar p q F x k i z
local notation "WeakRow" => actualMixedCubicWeakRow
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

def actualMixedCubicWeakRemainder {d : ℝ} (P : ARoom d) (g2 : MatrixField)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  ∑ k : Fin 3, ∑ i : Fin 3, ∑ z : ZeroWord, WeakRow P g2 dr Ar p q F x k i z

private lemma actual_mixed_scalar_eq_explicit (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (k i : Fin 3) (z : ZeroWord) :
    mixedWordScalar g L g2 dr Ar p q k i z = fun x =>
      (referenceRadius dr Ar p L x)^2 *
        ActualHigherSLeadingBracketGain.firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) x) *
          WC g2 dr Ar p q x z := by
  funext x
  rfl

private lemma actual_mixed_form_eq_paired (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (k i : Fin 3) (z : ZeroWord) :
    QMix g2 dr Ar p q k i z = fun y => mixedWordScalar g L g2 dr Ar p q k i z y •
      ActualHigherSCubicProductDerivative.pairedCubicForm PL
        (AH ((Tq dr Ar p q) y) (eAtom i))
        (AH ((Tq dr Ar p q) y) (wordAtoms z).2)
        (RH ((Tq dr Ar p q) y) (eAtom i))
        (RH ((Tq dr Ar p q) y) (wordAtoms z).1)
        (AL ((Tq dr Ar p q) y) (wordAtoms z).1)
        (RL ((Tq dr Ar p q) y) (wordAtoms z).2) := by
  funext y
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro U
  rfl

lemma contDiffAt_actualMixedCubicForm (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (x : R3) (Cprof : ℝ)
    (hAP : ActualHigherSAllAtomProfileCaps.ActualAtomProfileFirstCapsAt
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Cprof dr Ar p q x)
    (k i : Fin 3) (z : ZeroWord) : ContDiffAt ℝ ∞ (QMix g2 dr Ar p q k i z) x := by
  have hS := ActualHigherSMixedWordScalarJets.contDiff_actualMixedWordScalar_pure
    g hg L g2 hg2 dr Ar p hdr hAr q k i z
  have hScalar : ContDiff ℝ ∞ (mixedWordScalar g L g2 dr Ar p q k i z) := by
    rw [actual_mixed_scalar_eq_explicit]
    exact hS
  have hForwardSmooth := ActualHigherSCubicProductDerivative.contDiffAt_cubicForm PL
    (fun y => AH ((Tq dr Ar p q) y) (eAtom i))
    (fun y => AH ((Tq dr Ar p q) y) (wordAtoms z).2)
    (fun y => AL ((Tq dr Ar p q) y) (wordAtoms z).1) x
    (hAP.highSmooth _) (hAP.highSmooth _) (hAP.lowSmooth _)
  have hR := ActualHigherSCubicProductDerivative.contDiffAt_cubicForm PL
    (fun y => RH ((Tq dr Ar p q) y) (eAtom i))
    (fun y => RH ((Tq dr Ar p q) y) (wordAtoms z).1)
    (fun y => RL ((Tq dr Ar p q) y) (wordAtoms z).2) x
    (hAP.reverseHighSmooth _) (hAP.reverseHighSmooth _) (hAP.reverseLowSmooth _)
  have hProduct := hScalar.contDiffAt.smul (hForwardSmooth.add hR)
  rw [Pi.smul_def'] at hProduct
  rw [actual_mixed_form_eq_paired]
  simpa only [ActualHigherSCubicProductDerivative.pairedCubicForm] using hProduct

lemma actualMixedCubicCoefficientDerivative_eq (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (Cprof : ℝ)
    (hAP : ActualHigherSAllAtomProfileCaps.ActualAtomProfileFirstCapsAt
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Cprof dr Ar p q x)
    (k i : Fin 3) (z : ZeroWord) :
    directionalFDeriv (coordinateDirection k) (QMix g2 dr Ar p q k i z) x (UF F x) (UF F x) =
      CoeffDeriv g2 dr Ar p q F x k i z := by
  have hS := (ActualHigherSMixedWordScalarJets.contDiff_actualMixedWordScalar_pure
    g hg L g2 hg2 dr Ar p hdr hAr q k i z).differentiable (by simp) x
  have h := ActualHigherSCubicProductDerivative.directional_weightedPairedCubicForm_apply PL
    (fun y => AH ((Tq dr Ar p q) y) (eAtom i))
    (fun y => AH ((Tq dr Ar p q) y) (wordAtoms z).2)
    (fun y => RH ((Tq dr Ar p q) y) (eAtom i))
    (fun y => RH ((Tq dr Ar p q) y) (wordAtoms z).1)
    (fun y => AL ((Tq dr Ar p q) y) (wordAtoms z).1)
    (fun y => RL ((Tq dr Ar p q) y) (wordAtoms z).2) x (coordinateDirection k)
    ((hAP.highSmooth _).differentiableAt (by simp)) ((hAP.highSmooth _).differentiableAt (by simp))
    ((hAP.reverseHighSmooth _).differentiableAt (by simp)) ((hAP.reverseHighSmooth _).differentiableAt (by simp))
    ((hAP.lowSmooth _).differentiableAt (by simp)) ((hAP.reverseLowSmooth _).differentiableAt (by simp))
    (mixedWordScalar g L g2 dr Ar p q k i z) hS (UF F x)
  rw [actual_mixed_form_eq_paired]
  simpa only [actualMixedCubicCoefficientDerivative,
    ActualHigherSCubicProductDerivative.pairedCubicForm, ActualHigherSCubicProductDerivative.cubicForm,
    ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply] using h
structure ActualMixedCubicWeakFacts {d : ℝ} (P : ARoom d) (g2 : MatrixField)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD) : Prop where
  physicalFirst_integrable : Integrable (fun x => referenceDensityFamily g L (q,x)*
    ⟪PF g2 dr Ar p q F x, KL (Z2 g2 dr Ar p q F x)⟫_ℝ)
  physicalReverse_integrable : Integrable (fun x => referenceDensityFamily g L (q,x)*
    ⟪PR g2 dr Ar p q F x, KL (T2 g2 dr Ar p q F x)⟫_ℝ)
  forwardRow_integrable : ∀ k i z, Integrable (fun x => ForwardRow g2 dr Ar p q F x k i z)
  reverseRow_integrable : ∀ k i z, Integrable (fun x => ReverseRow g2 dr Ar p q F x k i z)
  weightedRow_integrable : ∀ k i z, Integrable (fun x => referenceDensityFamily g L (q,x)*
    QMix g2 dr Ar p q k i z x (directionalFDeriv (coordinateDirection k) (UF F) x) (UF F x))
  transposedRow_integrable : ∀ k i z, Integrable (fun x => referenceDensityFamily g L (q,x)*
    QMix g2 dr Ar p q k i z x (UF F x) (directionalFDeriv (coordinateDirection k) (UF F) x))
  skewRow_integrable : ∀ k i z, Integrable (fun x => Skew P g2 dr Ar p q F x k i z)
  densityRow_integrable : ∀ k i z, Integrable (fun x => Density g2 dr Ar p q F x k i z)
  coefficientRow_integrable : ∀ k i z, Integrable (fun x => Coefficient g2 dr Ar p q F x k i z)
  weakRow_integrable : ∀ k i z, Integrable (fun x => WeakRow P g2 dr Ar p q F x k i z)
  weakRemainder_integrable : Integrable (actualMixedCubicWeakRemainder
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P g2 dr Ar p q F)
  coefficientDerivative_eq : ∀ x k i z,
    directionalFDeriv (coordinateDirection k) (QMix g2 dr Ar p q k i z) x (UF F x) (UF F x) =
      CoeffDeriv g2 dr Ar p q F x k i z
  row_integral_identity : ∀ k i z,
    2*(∫ x, referenceDensityFamily g L (q,x)*QMix g2 dr Ar p q k i z x
      (directionalFDeriv (coordinateDirection k) (UF F) x) (UF F x)) =
      ∫ x, WeakRow P g2 dr Ar p q F x k i z
  integral_identity :
    2*((∫ x, referenceDensityFamily g L (q,x)*
        ⟪PF g2 dr Ar p q F x, KL (Z2 g2 dr Ar p q F x)⟫_ℝ) -
      (∫ x, referenceDensityFamily g L (q,x)*
        ⟪PR g2 dr Ar p q F x, KL (T2 g2 dr Ar p q F x)⟫_ℝ)) =
      ∫ x, actualMixedCubicWeakRemainder
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P g2 dr Ar p q F x

local notation "WeakFacts" => ActualMixedCubicWeakFacts
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

private lemma higherSInput_smooth_and_zero (F : smoothCompactFiniteSphereCore hO hD)
    (K : Set R3) (hsupp : tsupport F.val ⊆ K) :
    ContDiff ℝ ∞ (UF F) ∧ ∀ x ∉ K, UF F x = 0 := by
  refine ⟨contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F, ?_⟩
  intro x hx
  apply ActualHigherSFormation.finiteCoreSobolevLift_eq_zero_of_eval hO hD (3/2 : ℝ) F x
  exact image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp h))

private lemma coefficientDerivative_global {d : ℝ} (P : ARoom d)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (K : Set R3)
    (hsupp : tsupport F.val ⊆ K) (Cp : ℝ)
    (hAP : ∀ x ∈ K, ActualHigherSAllAtomProfileCaps.ActualAtomProfileFirstCapsAt
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Cp dr Ar p q x)
    (x : R3) (k i : Fin 3) (z : ZeroWord) :
    directionalFDeriv (coordinateDirection k) (QMix g2 dr Ar p q k i z) x (UF F x) (UF F x) =
      CoeffDeriv g2 dr Ar p q F x k i z := by
  by_cases hx : x ∈ K
  · exact actualMixedCubicCoefficientDerivative_eq
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 hg2 dr Ar p hdr hAr q F x Cp (hAP x hx) k i z
  · have h0 := (higherSInput_smooth_and_zero hO hD F K hsupp).2 x hx
    simp only [actualMixedCubicCoefficientDerivative, h0, map_zero,
      zero_apply, native_pairing_zero_zero, mul_zero, zero_add, add_zero]

private lemma actual_mixed_form_apply (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (x : R3) (k i : Fin 3) (z : ZeroWord) (v U : Hi) :
    QMix g2 dr Ar p q k i z x v U = mixedWordScalar g L g2 dr Ar p q k i z x *
      cubicAtomForm g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        ((Tq dr Ar p q) x) (eAtom i) (wordAtoms z).1 (wordAtoms z).2 v U := rfl

private lemma cubic_skew_zero_second {d : ℝ} (P : ARoom d) (t : Tpar)
    (du : Half) (aa bb cc : ZeroAtom) :
    cubicSkewRow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      P t du (0 : Hi) aa bb cc = 0 := by
  simp only [cubicSkewRow, map_zero, native_pairing_zero_right, zero_add, sub_zero]

private lemma actual_mixed_skew_point_eq {d : ℝ} (P : ARoom d) (g2 : MatrixField)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD)
    (x : R3) (ht : (Tq dr Ar p q) x ∈ ParamRoom d) (k i : Fin 3) (z : ZeroWord) :
    referenceDensityFamily g L (q,x)*
      (QMix g2 dr Ar p q k i z x (directionalFDeriv (coordinateDirection k) (UF F) x) (UF F x)-
        QMix g2 dr Ar p q k i z x (UF F x) (directionalFDeriv (coordinateDirection k) (UF F) x)) =
      Skew P g2 dr Ar p q F x k i z := by
  have h := actual_cubic_directional_skew
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    P dr Ar p q F x ht k (eAtom i) (wordAtoms z).1 (wordAtoms z).2
  simp only [actualMixedCubicSkewRow, actual_mixed_form_apply]
  rw [← mul_sub, h]
  exact (mul_assoc _ _ _).symm

private lemma actual_mixed_skew_function_eq {d : ℝ} (P : ARoom d) (g2 : MatrixField)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD)
    (K : Set R3) (hsupp : tsupport F.val ⊆ K)
    (hTP : ∀ x ∈ K, (Tq dr Ar p q) x ∈ ParamRoom d) (k i : Fin 3) (z : ZeroWord) :
    (fun x => referenceDensityFamily g L (q,x)*
      (QMix g2 dr Ar p q k i z x (directionalFDeriv (coordinateDirection k) (UF F) x) (UF F x)-
        QMix g2 dr Ar p q k i z x (UF F x) (directionalFDeriv (coordinateDirection k) (UF F) x))) =
      fun x => Skew P g2 dr Ar p q F x k i z := by
  funext x
  by_cases hx : x ∈ K
  · exact actual_mixed_skew_point_eq
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      P g2 dr Ar p q F x (hTP x hx) k i z
  · have h0 := (higherSInput_smooth_and_zero hO hD F K hsupp).2 x hx
    have hSkew0 : Skew P g2 dr Ar p q F x k i z = 0 := by
      unfold actualMixedCubicSkewRow
      rw [h0, cubic_skew_zero_second, mul_zero]
    rw [hSkew0]
    simp only [h0, map_zero, zero_apply, sub_self, mul_zero]

private lemma actual_mixed_density_point_eq (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (k i : Fin 3) (z : ZeroWord) :
    directionalFDeriv (coordinateDirection k) (fun y => referenceDensityFamily g L (q,y)) x *
      QMix g2 dr Ar p q k i z x (UF F x) (UF F x) = Density g2 dr Ar p q F x k i z := by
  rw [actual_mixed_form_apply]
  unfold actualMixedCubicDensityRow
  exact (mul_assoc _ _ _).symm

private lemma actual_mixed_coefficient_zero_of_input_zero (g2 : MatrixField)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD)
    (x : R3) (k i : Fin 3) (z : ZeroWord) (h0 : UF F x = 0) :
    CoeffDeriv g2 dr Ar p q F x k i z = 0 := by
  simp only [actualMixedCubicCoefficientDerivative, h0, map_zero,
    native_pairing_zero_zero, mul_zero, zero_add, add_zero]

private lemma actual_mixed_weak_row_zero_of_input_zero {d : ℝ} (P : ARoom d)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD)
    (x : R3) (k i : Fin 3) (z : ZeroWord) (h0 : UF F x = 0) :
    WeakRow P g2 dr Ar p q F x k i z = 0 := by
  have hS0 : Skew P g2 dr Ar p q F x k i z = 0 := by
    unfold actualMixedCubicSkewRow
    rw [h0, cubic_skew_zero_second, mul_zero]
  have hD0 : Density g2 dr Ar p q F x k i z = 0 := by
    unfold actualMixedCubicDensityRow
    rw [h0, map_zero, mul_zero]
  have hC0 : Coefficient g2 dr Ar p q F x k i z = 0 := by
    unfold actualMixedCubicCoefficientRow
    rw [actual_mixed_coefficient_zero_of_input_zero
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F x k i z h0, mul_zero]
  simp only [actualMixedCubicWeakRow, hS0, hD0, hC0, sub_self, sub_zero]

private lemma actual_mixed_weak_remainder_zero_of_input_zero {d : ℝ} (P : ARoom d)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD)
    (x : R3) (h0 : UF F x = 0) :
    actualMixedCubicWeakRemainder
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P g2 dr Ar p q F x = 0 := by
  unfold actualMixedCubicWeakRemainder
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro z _
  exact actual_mixed_weak_row_zero_of_input_zero
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    P g2 dr Ar p q F x k i z h0

private lemma actual_mixed_raw_row_integration (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (K : Set R3) (hK : IsCompact K)
    (hsupp : tsupport F.val ⊆ K) (Cp : ℝ)
    (hAP : ∀ x ∈ K, ActualHigherSAllAtomProfileCaps.ActualAtomProfileFirstCapsAt
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Cp dr Ar p q x)
    (k i : Fin 3) (z : ZeroWord) :
    Integrable (fun x => referenceDensityFamily g L (q,x)*QMix g2 dr Ar p q k i z x
      (directionalFDeriv (coordinateDirection k) (UF F) x) (UF F x)) ∧
    Integrable (fun x => referenceDensityFamily g L (q,x)*QMix g2 dr Ar p q k i z x
      (UF F x) (directionalFDeriv (coordinateDirection k) (UF F) x)) ∧
    Integrable (fun x => directionalFDeriv (coordinateDirection k)
      (fun y => referenceDensityFamily g L (q,y)) x*QMix g2 dr Ar p q k i z x (UF F x) (UF F x)) ∧
    Integrable (fun x => referenceDensityFamily g L (q,x)*
      directionalFDeriv (coordinateDirection k) (QMix g2 dr Ar p q k i z) x (UF F x) (UF F x)) ∧
    2*(∫ x, referenceDensityFamily g L (q,x)*QMix g2 dr Ar p q k i z x
      (directionalFDeriv (coordinateDirection k) (UF F) x) (UF F x)) =
      (∫ x, referenceDensityFamily g L (q,x)*
        (QMix g2 dr Ar p q k i z x (directionalFDeriv (coordinateDirection k) (UF F) x) (UF F x)-
          QMix g2 dr Ar p q k i z x (UF F x) (directionalFDeriv (coordinateDirection k) (UF F) x))) -
      (∫ x, directionalFDeriv (coordinateDirection k) (fun y => referenceDensityFamily g L (q,y)) x *
        QMix g2 dr Ar p q k i z x (UF F x) (UF F x)) -
      (∫ x, referenceDensityFamily g L (q,x)*
        directionalFDeriv (coordinateDirection k) (QMix g2 dr Ar p q k i z) x (UF F x) (UF F x)) := by
  have hU := higherSInput_smooth_and_zero hO hD F K hsupp
  have hmu : ContDiff ℝ ∞ (fun x : R3 => referenceDensityFamily g L (q,x)) :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hQ : ∀ x ∈ K, ContDiffAt ℝ ∞ (QMix g2 dr Ar p q k i z) x := fun x hx =>
    contDiffAt_actualMixedCubicForm
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 hg2 dr Ar p hdr hAr q x Cp (hAP x hx) k i z
  exact ActualHigherSCubicIntegration.weighted_diagonal_pairing_eq_skew_sub_derivatives
    (QMix g2 dr Ar p q k i z) (fun x => referenceDensityFamily g L (q,x)) (UF F)
    K hK hmu hU.1 hU.2 hQ (coordinateDirection k)

private lemma actual_mixed_density_function_eq (g2 : MatrixField)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD)
    (k i : Fin 3) (z : ZeroWord) :
    (fun x => directionalFDeriv (coordinateDirection k)
      (fun y => referenceDensityFamily g L (q,y)) x *
      QMix g2 dr Ar p q k i z x (UF F x) (UF F x)) =
      fun x => Density g2 dr Ar p q F x k i z :=
  funext (fun x => actual_mixed_density_point_eq
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F x k i z)

private lemma actual_mixed_coefficient_function_eq {d : ℝ} (P : ARoom d)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (K : Set R3)
    (hsupp : tsupport F.val ⊆ K) (Cp : ℝ)
    (hAP : ∀ x ∈ K, ActualHigherSAllAtomProfileCaps.ActualAtomProfileFirstCapsAt
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Cp dr Ar p q x)
    (k i : Fin 3) (z : ZeroWord) :
    (fun x => referenceDensityFamily g L (q,x)*
      directionalFDeriv (coordinateDirection k) (QMix g2 dr Ar p q k i z) x (UF F x) (UF F x)) =
      fun x => Coefficient g2 dr Ar p q F x k i z := by
  funext x
  rw [coefficientDerivative_global
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    P g2 hg2 dr Ar p hdr hAr q F K hsupp Cp hAP x k i z]
  rfl

private lemma actual_mixed_transported_row_integration {d : ℝ} (P : ARoom d)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (K : Set R3) (hK : IsCompact K)
    (hsupp : tsupport F.val ⊆ K) (Cp : ℝ)
    (hAP : ∀ x ∈ K, ActualHigherSAllAtomProfileCaps.ActualAtomProfileFirstCapsAt
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Cp dr Ar p q x)
    (k i : Fin 3) (z : ZeroWord) :
    Integrable (fun x => referenceDensityFamily g L (q,x)*QMix g2 dr Ar p q k i z x
      (directionalFDeriv (coordinateDirection k) (UF F) x) (UF F x)) ∧
    Integrable (fun x => referenceDensityFamily g L (q,x)*QMix g2 dr Ar p q k i z x
      (UF F x) (directionalFDeriv (coordinateDirection k) (UF F) x)) ∧
    Integrable (fun x => Density g2 dr Ar p q F x k i z) ∧
    Integrable (fun x => Coefficient g2 dr Ar p q F x k i z) ∧
    2*(∫ x, referenceDensityFamily g L (q,x)*QMix g2 dr Ar p q k i z x
      (directionalFDeriv (coordinateDirection k) (UF F) x) (UF F x)) =
      (∫ x, referenceDensityFamily g L (q,x)*
        (QMix g2 dr Ar p q k i z x (directionalFDeriv (coordinateDirection k) (UF F) x) (UF F x)-
          QMix g2 dr Ar p q k i z x (UF F x) (directionalFDeriv (coordinateDirection k) (UF F) x))) -
      (∫ x, Density g2 dr Ar p q F x k i z) -
      (∫ x, Coefficient g2 dr Ar p q F x k i z) := by
  exact raw_row_integration_transport
    (fun x => referenceDensityFamily g L (q,x))
    (fun x => QMix g2 dr Ar p q k i z x (directionalFDeriv (coordinateDirection k) (UF F) x) (UF F x))
    (fun x => QMix g2 dr Ar p q k i z x (UF F x) (directionalFDeriv (coordinateDirection k) (UF F) x))
    (fun x => directionalFDeriv (coordinateDirection k)
      (fun y => referenceDensityFamily g L (q,y)) x *
      QMix g2 dr Ar p q k i z x (UF F x) (UF F x))
    (fun x => referenceDensityFamily g L (q,x)*
      directionalFDeriv (coordinateDirection k) (QMix g2 dr Ar p q k i z) x (UF F x) (UF F x))
    (fun x => Density g2 dr Ar p q F x k i z)
    (fun x => Coefficient g2 dr Ar p q F x k i z)
    (actual_mixed_density_function_eq
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F k i z)
    (actual_mixed_coefficient_function_eq
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      P g2 hg2 dr Ar p hdr hAr q F K hsupp Cp hAP k i z)
    (actual_mixed_raw_row_integration
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 hg2 dr Ar p hdr hAr q F K hK hsupp Cp hAP k i z)

private lemma actual_mixed_row_integration {d : ℝ} (P : ARoom d)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (K : Set R3) (hK : IsCompact K)
    (hsupp : tsupport F.val ⊆ K) (Cp : ℝ)
    (hAP : ∀ x ∈ K, ActualHigherSAllAtomProfileCaps.ActualAtomProfileFirstCapsAt
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Cp dr Ar p q x)
    (hTP : ∀ x ∈ K, (Tq dr Ar p q) x ∈ ParamRoom d)
    (k i : Fin 3) (z : ZeroWord) :
    Integrable (fun x => referenceDensityFamily g L (q,x)*QMix g2 dr Ar p q k i z x
      (directionalFDeriv (coordinateDirection k) (UF F) x) (UF F x)) ∧
    Integrable (fun x => referenceDensityFamily g L (q,x)*QMix g2 dr Ar p q k i z x
      (UF F x) (directionalFDeriv (coordinateDirection k) (UF F) x)) ∧
    Integrable (fun x => Skew P g2 dr Ar p q F x k i z) ∧
    Integrable (fun x => Density g2 dr Ar p q F x k i z) ∧
    Integrable (fun x => Coefficient g2 dr Ar p q F x k i z) ∧
    Integrable (fun x => WeakRow P g2 dr Ar p q F x k i z) ∧
    2*(∫ x, referenceDensityFamily g L (q,x)*QMix g2 dr Ar p q k i z x
      (directionalFDeriv (coordinateDirection k) (UF F) x) (UF F x)) =
      ∫ x, WeakRow P g2 dr Ar p q F x k i z := by
  obtain ⟨hA,hB,hDensityInt,hCoefficientInt,hIBP⟩ := actual_mixed_transported_row_integration
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    P g2 hg2 dr Ar p hdr hAr q F K hK hsupp Cp hAP k i z
  have hSkew := actual_mixed_skew_function_eq
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    P g2 dr Ar p q F K hsupp hTP k i z
  have hWeak : (fun x => WeakRow P g2 dr Ar p q F x k i z) =
      fun x => Skew P g2 dr Ar p q F x k i z - Density g2 dr Ar p q F x k i z -
        Coefficient g2 dr Ar p q F x k i z := by funext x; rfl
  exact row_integration_transport
    (fun x => referenceDensityFamily g L (q,x))
    (fun x => QMix g2 dr Ar p q k i z x (directionalFDeriv (coordinateDirection k) (UF F) x) (UF F x))
    (fun x => QMix g2 dr Ar p q k i z x (UF F x) (directionalFDeriv (coordinateDirection k) (UF F) x))
    (fun x => Skew P g2 dr Ar p q F x k i z)
    (fun x => Density g2 dr Ar p q F x k i z)
    (fun x => Coefficient g2 dr Ar p q F x k i z)
    (fun x => WeakRow P g2 dr Ar p q F x k i z)
    hA hB hDensityInt hCoefficientInt hSkew hWeak hIBP

private lemma actual_mixed_physical_integrable {d : ℝ} (P : ARoom d) (dF : ℝ)
    (Cm : ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs dF)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (K : Set R3) (hK : IsCompact K)
    (hsupp : tsupport F.val ⊆ K) (Cp : ℝ)
    (hAP : ∀ x ∈ K, ActualHigherSAllAtomProfileCaps.ActualAtomProfileFirstCapsAt
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Cp dr Ar p q x)
    (hTP : ∀ x ∈ K, (Tq dr Ar p q) x ∈ ParamRoom d)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom dF) :
    (∀ k i z, Integrable (fun x => ForwardRow g2 dr Ar p q F x k i z)) ∧
    (∀ k i z, Integrable (fun x => ReverseRow g2 dr Ar p q F x k i z)) ∧
    Integrable (fun x => referenceDensityFamily g L (q,x)*
      ⟪PF g2 dr Ar p q F x, KL (Z2 g2 dr Ar p q F x)⟫_ℝ) ∧
    Integrable (fun x => referenceDensityFamily g L (q,x)*
      ⟪PR g2 dr Ar p q F x, KL (T2 g2 dr Ar p q F x)⟫_ℝ) := by
  let QF : Fin 3 → Fin 3 → ZeroWord → R3 → Hi →L[ℝ] Hi →L[ℝ] ℝ := fun k i z x =>
    mixedWordScalar g L g2 dr Ar p q k i z x •
      (PL).bilinearComp (AH ((Tq dr Ar p q) x) (eAtom i))
        ((AL ((Tq dr Ar p q) x) (wordAtoms z).1).comp (AH ((Tq dr Ar p q) x) (wordAtoms z).2))
  let QR : Fin 3 → Fin 3 → ZeroWord → R3 → Hi →L[ℝ] Hi →L[ℝ] ℝ := fun k i z x =>
    mixedWordScalar g L g2 dr Ar p q k i z x •
      (PL).bilinearComp (RH ((Tq dr Ar p q) x) (eAtom i))
        ((RL ((Tq dr Ar p q) x) (wordAtoms z).2).comp (RH ((Tq dr Ar p q) x) (wordAtoms z).1))
  have hU := higherSInput_smooth_and_zero hO hD F K hsupp
  have hmu : ContDiff ℝ ∞ (fun x : R3 => referenceDensityFamily g L (q,x)) :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hQF (k i : Fin 3) (z : ZeroWord) (x : R3) (hx : x ∈ K) : ContDiffAt ℝ ∞ (QF k i z) x := by
    have hS := ActualHigherSMixedWordScalarJets.contDiff_actualMixedWordScalar_pure
      g hg L g2 hg2 dr Ar p hdr hAr q k i z
    exact hS.contDiffAt.smul (ActualHigherSCubicProductDerivative.contDiffAt_cubicForm PL
      _ _ _ x ((hAP x hx).highSmooth _) ((hAP x hx).highSmooth _) ((hAP x hx).lowSmooth _))
  have hQR (k i : Fin 3) (z : ZeroWord) (x : R3) (hx : x ∈ K) : ContDiffAt ℝ ∞ (QR k i z) x := by
    have hS := ActualHigherSMixedWordScalarJets.contDiff_actualMixedWordScalar_pure
      g hg L g2 hg2 dr Ar p hdr hAr q k i z
    exact hS.contDiffAt.smul (ActualHigherSCubicProductDerivative.contDiffAt_cubicForm PL
      _ _ _ x ((hAP x hx).reverseHighSmooth _) ((hAP x hx).reverseHighSmooth _)
      ((hAP x hx).reverseLowSmooth _))
  have hIF (k i : Fin 3) (z : ZeroWord) : Integrable (fun x => referenceDensityFamily g L (q,x)*
      QF k i z x (directionalFDeriv (coordinateDirection k) (UF F) x) (UF F x)) :=
    (ActualHigherSCubicIntegration.weighted_diagonal_pairing_eq_skew_sub_derivatives
      (QF k i z) (fun x => referenceDensityFamily g L (q,x)) (UF F) K hK hmu hU.1 hU.2
      (hQF k i z) (coordinateDirection k)).1
  have hIR (k i : Fin 3) (z : ZeroWord) : Integrable (fun x => referenceDensityFamily g L (q,x)*
      QR k i z x (directionalFDeriv (coordinateDirection k) (UF F) x) (UF F x)) :=
    (ActualHigherSCubicIntegration.weighted_diagonal_pairing_eq_skew_sub_derivatives
      (QR k i z) (fun x => referenceDensityFamily g L (q,x)) (UF F) K hK hmu hU.1 hU.2
      (hQR k i z) (coordinateDirection k)).1
  have hPhysical := ActualHigherSMixedCubicPhysicalExpansion.actual_mixed_cubic_two_pairings
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    P dF Cm g2 dr Ar p hdr hAr q F hTF (fun x hx => hTP x (hsupp hx))
  have hFRows (k i : Fin 3) (z : ZeroWord) : Integrable (fun x => ForwardRow g2 dr Ar p q F x k i z) := by
    simpa only [actualMixedCubicForwardRow,QF,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.comp_apply,smul_eq_mul,
      ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply] using hIF k i z
  have hRRows (k i : Fin 3) (z : ZeroWord) : Integrable (fun x => ReverseRow g2 dr Ar p q F x k i z) := by
    simpa only [actualMixedCubicReverseRow,QR,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.comp_apply,smul_eq_mul,
      ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply] using hIR k i z
  refine ⟨hFRows,hRRows,?_,?_⟩
  · have hsum := integrable_finsetSum Finset.univ (fun k _ =>
      integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun z _ => hIF k i z)))
    convert hsum using 1
    funext x
    rw [(hPhysical x).1]
    simp only [Finset.mul_sum,QF,ContinuousLinearMap.smul_apply,ContinuousLinearMap.bilinearComp_apply,
      ContinuousLinearMap.comp_apply,smul_eq_mul,ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply]

  · have hsum := (integrable_finsetSum Finset.univ (fun k _ =>
      integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun z _ => hIR k i z)))).neg
    convert hsum using 1
    funext x
    rw [(hPhysical x).2]
    simp only [mul_neg,Finset.mul_sum,QR,ContinuousLinearMap.smul_apply,ContinuousLinearMap.bilinearComp_apply,
      ContinuousLinearMap.comp_apply,smul_eq_mul,ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply]
    congr 1

private lemma integral_triple_sum {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (f : ι → κ → ν → R3 → ℝ) (hf : ∀ i j k, Integrable (f i j k)) :
    (∫ x, ∑ i : ι, ∑ j : κ, ∑ k : ν, f i j k x) =
      ∑ i : ι, ∑ j : κ, ∑ k : ν, ∫ x, f i j k x := by
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
    (fun j _ => integrable_finsetSum Finset.univ (fun k _ => hf i j k)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => integrable_finsetSum Finset.univ (fun k _ => hf i j k))]
  apply Finset.sum_congr rfl
  intro j _
  exact integral_finsetSum Finset.univ (fun k _ => hf i j k)

private lemma actual_mixed_weak_facts {d : ℝ} (P : ARoom d) (dF : ℝ)
    (Cm : ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs dF)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (K : Set R3) (hK : IsCompact K)
    (hsupp : tsupport F.val ⊆ K) (Cp : ℝ)
    (hAP : ∀ x ∈ K, ActualHigherSAllAtomProfileCaps.ActualAtomProfileFirstCapsAt
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Cp dr Ar p q x)
    (hTP : ∀ x ∈ K, (Tq dr Ar p q) x ∈ ParamRoom d)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom dF) :
    WeakFacts P g2 dr Ar p q F := by
  have hRows := actual_mixed_row_integration
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    P g2 hg2 dr Ar p hdr hAr q F K hK hsupp Cp hAP hTP
  obtain ⟨hFRows,hRRows,hIF,hIR⟩ := actual_mixed_physical_integrable
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    P dF Cm g2 hg2 dr Ar p hdr hAr q F K hK hsupp Cp hAP hTP hTF
  have hWeak (k i : Fin 3) (z : ZeroWord) := (hRows k i z).2.2.2.2.2.1
  have hWsum : Integrable (actualMixedCubicWeakRemainder
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P g2 dr Ar p q F) :=
    integrable_finsetSum Finset.univ (fun k _ => integrable_finsetSum Finset.univ
      (fun i _ => integrable_finsetSum Finset.univ (fun z _ => hWeak k i z)))
  refine ⟨hIF,hIR,hFRows,hRRows,(fun k i z => (hRows k i z).1),
    (fun k i z => (hRows k i z).2.1),(fun k i z => (hRows k i z).2.2.1),
    (fun k i z => (hRows k i z).2.2.2.1),(fun k i z => (hRows k i z).2.2.2.2.1),
    hWeak,hWsum,?_,(fun k i z => (hRows k i z).2.2.2.2.2.2),?_⟩
  · exact coefficientDerivative_global
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      P g2 hg2 dr Ar p hdr hAr q F K hsupp Cp hAP
  · have hPhysical := ActualHigherSMixedCubicPhysicalExpansion.actual_mixed_cubic_finite_sum
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      P dF Cm g2 dr Ar p hdr hAr q F hTF (fun x hx => hTP x (hsupp hx))
    have hDistribute : (fun x =>
        referenceDensityFamily g L (q,x)*⟪PF g2 dr Ar p q F x, KL (Z2 g2 dr Ar p q F x)⟫_ℝ-
          referenceDensityFamily g L (q,x)*⟪PR g2 dr Ar p q F x, KL (T2 g2 dr Ar p q F x)⟫_ℝ) =
        (fun x => referenceDensityFamily g L (q,x)*
          (⟪PF g2 dr Ar p q F x, KL (Z2 g2 dr Ar p q F x)⟫_ℝ-
            ⟪PR g2 dr Ar p q F x, KL (T2 g2 dr Ar p q F x)⟫_ℝ)) := by
      funext x
      exact (mul_sub _ _ _).symm
    have hFunctions : (fun x => referenceDensityFamily g L (q,x)*
        (⟪PF g2 dr Ar p q F x, KL (Z2 g2 dr Ar p q F x)⟫_ℝ-
          ⟪PR g2 dr Ar p q F x, KL (T2 g2 dr Ar p q F x)⟫_ℝ)) =
        fun x => ∑ k : Fin 3, ∑ i : Fin 3, ∑ z : ZeroWord,
          referenceDensityFamily g L (q,x)*QMix g2 dr Ar p q k i z x
            (directionalFDeriv (coordinateDirection k) (UF F) x) (UF F x) := by
      funext x
      change referenceDensityFamily g L (q,x)*
        actualMixedCubicDensity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
          g2 dr Ar p q F x = _
      rw [hPhysical x]
      simp only [Finset.mul_sum,actualMixedCubicForm,ContinuousLinearMap.smul_apply,smul_eq_mul]
    rw [← integral_sub hIF hIR,hDistribute,hFunctions,
      integral_triple_sum _ (fun k i z => (hRows k i z).1)]
    change 2*(∑ k : Fin 3, ∑ i : Fin 3, ∑ z : ZeroWord, _) =
      ∫ x, ∑ k : Fin 3, ∑ i : Fin 3, ∑ z : ZeroWord, WeakRow P g2 dr Ar p q F x k i z
    rw [integral_triple_sum _ hWeak]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro z _
    exact (hRows k i z).2.2.2.2.2.2
private lemma abs_sub_le_abs_add_abs (a b : ℝ) : |a-b| ≤ |a|+|b| := by
  simpa only [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)

private lemma pair_low_high_bound (Low : Half →L[ℝ] Neg) (High : Hi →L[ℝ] Half)
    (du : Half) (U : Hi) (M : ℝ) (hM : 0 ≤ M)
    (hL : ‖Low‖ ≤ M) (hH : ‖High‖ ≤ M) :
    |PP du (Low (High U))| ≤ ‖PL‖*M^2*‖du‖*‖U‖ := by
  have hp := (PL du).le_opNorm (Low (High U))
  have hdu := (PL).le_opNorm du
  have hl := Low.le_opNorm (High U)
  have hh := High.le_opNorm U
  calc
    _ = ‖PL du (Low (High U))‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖PL du‖*‖Low (High U)‖ := hp
    _ ≤ (‖PL‖*‖du‖)*(M*(M*‖U‖)) := by
      have hHigh : ‖High U‖ ≤ M*‖U‖ :=
        hh.trans (mul_le_mul_of_nonneg_right hH (norm_nonneg U))
      have hLow : ‖Low (High U)‖ ≤ M*(M*‖U‖) :=
        hl.trans (mul_le_mul hL hHigh (norm_nonneg (High U)) hM)
      exact mul_le_mul hdu hLow (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

private lemma abs_bilinear_diagonal_le (Q : Hi →L[ℝ] Hi →L[ℝ] ℝ) (U : Hi) :
    |Q U U| ≤ ‖Q‖*‖U‖^2 := by
  calc
    _ = ‖Q U U‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖Q U‖*‖U‖ := (Q U).le_opNorm U
    _ ≤ (‖Q‖*‖U‖)*‖U‖ :=
      mul_le_mul_of_nonneg_right (Q.le_opNorm U) (norm_nonneg U)
    _ = _ := by ring

private lemma cubicSkewRow_bound {d : ℝ} (P : ARoom d) (t : Tpar)
    (du : Half) (U : Hi) (aa bb cc : ZeroAtom) (M : ℝ) (hM : 0 ≤ M)
    (hA : ∀ a, ‖AH t a‖ ≤ M) (hB : ∀ a, ‖RH t a‖ ≤ M)
    (hL : ∀ a, ‖AL t a‖ ≤ M) (hR : ∀ a, ‖RL t a‖ ≤ M)
    (hG : ∀ a b, ‖P.gainHigh a b t‖ ≤ M)
    (hCl : ∀ a b, ‖P.gainLow a b t‖ ≤ M) :
    |cubicSkewRow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      P t du U aa bb cc| ≤ 4*‖PL‖*M^2*‖du‖*‖U‖ := by
  have h1 := pair_low_high_bound (P.gainLow aa bb t) (AH t cc) du U M hM (hCl _ _) (hA _)
  have h2 := pair_low_high_bound (AL t bb) (P.gainHigh aa cc t) du U M hM (hL _) (hG _ _)
  have h3 := pair_low_high_bound (P.gainLow cc aa t) (RH t bb) du U M hM (hCl _ _) (hB _)
  have h4 := pair_low_high_bound (RL t cc) (P.gainHigh bb aa t) du U M hM (hR _) (hG _ _)
  let p1 := PP du (P.gainLow aa bb t (AH t cc U))
  let p2 := PP du (AL t bb (P.gainHigh aa cc t U))
  let p3 := PP du (P.gainLow cc aa t (RH t bb U))
  let p4 := PP du (RL t cc (P.gainHigh bb aa t U))
  let D := ‖PL‖*M^2*‖du‖*‖U‖
  change |p1+p2-p3-p4| ≤ 4*‖PL‖*M^2*‖du‖*‖U‖
  calc
    _ ≤ |p1+p2-p3|+|p4| := abs_sub_le_abs_add_abs _ _
    _ ≤ (|p1+p2|+|p3|)+|p4| := add_le_add (abs_sub_le_abs_add_abs _ _) le_rfl
    _ ≤ ((|p1|+|p2|)+|p3|)+|p4| :=
      add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
    _ ≤ ((D+D)+D)+D := add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = _ := by dsimp [D]; ring

private lemma actual_mixed_form_bounds (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (x : R3) (M Cs r beta : ℝ) (hM : 0 ≤ M) (hCs : 0 ≤ Cs) (hr : 0 ≤ r) (hb : 1 ≤ beta)
    (hAP : ActualHigherSAllAtomProfileCaps.ActualAtomProfileFirstCapsAt
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 M dr Ar p q x)
    (k i : Fin 3) (z : ZeroWord)
    (hS : ActualHigherSMixedWordScalarJets.ScalarPointJet
      (mixedWordScalar g L g2 dr Ar p q k i z) x (Cs*r^3) (Cs*r^3*beta)) :
    ‖cubicAtomForm g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      ((Tq dr Ar p q) x) (eAtom i) (wordAtoms z).1 (wordAtoms z).2‖ ≤ 2*‖PL‖*M^3 ∧
    ‖fderiv ℝ (QMix g2 dr Ar p q k i z) x‖ ≤ 8*Cs*‖PL‖*M^3*r^3*beta := by
  let A := fun y => AH ((Tq dr Ar p q) y) (eAtom i)
  let C1 := fun y => AH ((Tq dr Ar p q) y) (wordAtoms z).2
  let Bv := fun y => RH ((Tq dr Ar p q) y) (eAtom i)
  let C2 := fun y => RH ((Tq dr Ar p q) y) (wordAtoms z).1
  let Lw := fun y => AL ((Tq dr Ar p q) y) (wordAtoms z).1
  let Rw := fun y => RL ((Tq dr Ar p q) y) (wordAtoms z).2
  have hValue := ActualHigherSCubicProductDerivative.norm_pairedCubicForm_le
    PL A C1 Bv C2 Lw Rw x M hM
    (hAP.highBound _) (hAP.highBound _) (hAP.reverseHighBound _) (hAP.reverseHighBound _)
    (hAP.lowBound _) (hAP.reverseLowBound _)
  have hDerivative := ActualHigherSCubicProductDerivative.norm_fderiv_weightedPairedCubicForm_le
    PL A C1 Bv C2 Lw Rw x
    ((hAP.highSmooth _).differentiableAt (by simp)) ((hAP.highSmooth _).differentiableAt (by simp))
    ((hAP.reverseHighSmooth _).differentiableAt (by simp))
    ((hAP.reverseHighSmooth _).differentiableAt (by simp))
    ((hAP.lowSmooth _).differentiableAt (by simp)) ((hAP.reverseLowSmooth _).differentiableAt (by simp))
    (mixedWordScalar g L g2 dr Ar p q k i z) hS.differentiable M M hM hM
    (hAP.highBound _) (hAP.highBound _) (hAP.reverseHighBound _) (hAP.reverseHighBound _)
    (hAP.lowBound _) (hAP.reverseLowBound _)
    (hAP.highDerivativeBound _) (hAP.highDerivativeBound _)
    (hAP.reverseHighDerivativeBound _) (hAP.reverseHighDerivativeBound _)
    (hAP.lowDerivativeBound _) (hAP.reverseLowDerivativeBound _)
  have hT : Cs*r^3 ≤ Cs*r^3*beta := le_mul_of_one_le_right (by positivity) hb
  constructor
  · simpa only [cubicAtomForm,ActualHigherSCubicProductDerivative.pairedCubicForm,
      ActualHigherSCubicProductDerivative.cubicForm,A,C1,Bv,C2,Lw,Rw] using hValue
  · change ‖fderiv ℝ (fun y => mixedWordScalar g L g2 dr Ar p q k i z y •
        ActualHigherSCubicProductDerivative.pairedCubicForm PL (A y) (C1 y) (Bv y) (C2 y) (Lw y) (Rw y)) x‖ ≤ _
    calc
      _ ≤ ‖fderiv ℝ (mixedWordScalar g L g2 dr Ar p q k i z) x‖*(2*‖PL‖*M^3)+
          |mixedWordScalar g L g2 dr Ar p q k i z x| *(6*‖PL‖*M^2*M) := hDerivative
      _ ≤ (Cs*r^3*beta)*(2*‖PL‖*M^3)+(Cs*r^3*beta)*(6*‖PL‖*M^2*M) :=
        add_le_add (mul_le_mul_of_nonneg_right hS.derivative (by positivity))
          (mul_le_mul_of_nonneg_right (hS.value.trans hT) (by positivity))
      _ = _ := by ring
-- Exact companion target; same section binder order as the minimal producer.
theorem exists_uniform_same_packet_actual_mixed_cubic_weak_bound
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ d : ℝ, 0 < d ∧ ∃ P : ARoom d, ∃ Cmix etaMix : ℝ,
      0 < Cmix ∧ 0 < etaMix ∧ etaMix ≤ data.eta0 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaMix →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      WeakFacts P g2 dr Ar p q F ∧
      |∫ x, actualMixedCubicWeakRemainder
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P g2 dr Ar p q F x| ≤
        Cmix*eta*(∫ x, referenceDensityFamily g L (q,x)*finiteCoreReferenceProfileEnergy
          hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x)
 := by
  obtain ⟨dA,hdA,_hdAD,_hdA0,_hdAρ,_hRoom,⟨P⟩⟩ :=
    ActualAllAngularAtomGainedRoom.exists_same_packet_allAngularAtom_room
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hKernel
  obtain ⟨Cp,etaP,hCp,hetaP,hetaP0,hetaP1,hProfiles⟩ :=
    ActualHigherSAllAtomProfileCaps.exists_actual_allAtom_profile_first_caps
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hdA P hL
  obtain ⟨Mg,hMg,_hAtoms,hGains⟩ := P.finiteCaps 0
  obtain ⟨Cs,hCs,hScalars⟩ := ActualHigherSMixedWordScalarJets.exists_actual_mixed_word_scalar_first_caps
    g hg L hL y0 ρ g2 hg2
  obtain ⟨Md,hMd,hdmu⟩ := ActualHigherSScalarCommutatorNativeForm.exists_density_coordinate_relative_bound
    g hg L (closedBall y0 ρ) (isCompact_closedBall _ _)
  obtain ⟨Cr,hCr,hcoord⟩ := ActualHigherSScalarCommutatorNativeForm.exists_halfInput_coordinate_reference_bound
    hO hD g hg L (closedBall y0 ρ) (isCompact_closedBall _ _)
  obtain ⟨dF,Cm⟩ := ActualCommonFirstWordQuadraticAdjoint.exists_common_first_word_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel
    data.δ0 data.δ0_pos data.germs
  let d := min dA dF
  have hd : 0 < d := lt_min hdA Cm.rev.pos
  obtain ⟨epsG,hepsG,_hepsG1,hGuard⟩ := exists_uniform_strict_higherSParam_guard
    g hg L hL y0 ρ d hd (closedBall y0 ρ) (isCompact_closedBall _ _)
  obtain ⟨_CLead,_hCLead,hLeading⟩ := ActualFullEGainedAssembly.exists_actual_leading_signed_second_reference_form
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hL hreg data g2 hg2
  let M := 1+Cp+Mg
  let N := ‖PL‖
  let Cdir := 1+∑ k : Fin 3, ‖coordinateDirection k‖
  let Csk := 4*Cs*N*M^2
  let Cden := 2*Md*Cs*N*M^3
  let Ccoef := 8*Cs*N*M^3*Cdir
  let CRow := Csk*(Cr+1)+Cden+Ccoef
  let Cmix := 1+1863*CRow
  let etaMix := min etaP (min 1 epsG)
  have hCp0 : 0 ≤ Cp := zero_le_one.trans hCp
  have hMg0 : 0 ≤ Mg := zero_le_one.trans hMg
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hCpM : Cp ≤ M := by dsimp [M]; linarith
  have hMgM : Mg ≤ M := by dsimp [M]; linarith
  have hMd0 : 0 ≤ Md := zero_le_one.trans hMd
  have hN0 : 0 ≤ N := norm_nonneg _
  have hdir0 : 0 ≤ Cdir := by dsimp [Cdir]; positivity
  have hCsk : 0 ≤ Csk := by dsimp [Csk]; positivity
  have hCden : 0 ≤ Cden := by dsimp [Cden]; positivity
  have hCcoef : 0 ≤ Ccoef := by dsimp [Ccoef]; positivity
  have hCRow : 0 ≤ CRow := by dsimp [CRow]; positivity
  have hCmix : 0 < Cmix := by dsimp [Cmix]; positivity
  refine ⟨dA,hdA,P,Cmix,etaMix,hCmix,lt_min hetaP (lt_min zero_lt_one hepsG),
    (min_le_left _ _).trans hetaP0,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaMix K hK hKball F hsupp hb hs
  have hetaProf : eta ≤ etaP := hetaMix.trans (min_le_left _ _)
  have heta0 : eta ≤ data.eta0 := hetaProf.trans hetaP0
  have heta1 : eta ≤ 1 := hetaMix.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hetaG : eta ≤ epsG := hetaMix.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hT (x : R3) (hx : x ∈ K) : (Tq dr Ar p q) x ∈ ParamRoom d := by
    have hguard := hGuard q hq dr hdr hdr1 Ar hAr p hp eta heta hetaG x
      (ball_subset_closedBall (hKball hx)) (hKball hx) (hb x hx) (hs x hx)
    exact (higherSParam_eventually_mem y0 ρ d L dr Ar q p hdr hAr x hguard).self_of_nhds
  have hTP (x : R3) (hx : x ∈ K) : (Tq dr Ar p q) x ∈ ParamRoom dA :=
    ⟨commonRoom_mono y0 ρ (min_le_left dA dF) (hT x hx).1,(hT x hx).2⟩
  have hTF (x : R3) (hx : x ∈ tsupport F.val) : (Tq dr Ar p q) x ∈ ParamRoom dF :=
    ⟨commonRoom_mono y0 ρ (min_le_right dA dF) (hT x (hsupp hx)).1,(hT x (hsupp hx)).2⟩
  have hAP0 := hProfiles q hq dr hdr hdr1 Ar hAr p hp eta heta hetaProf K hKball hb hs
  have hAP (x : R3) (hx : x ∈ K) :
      ActualHigherSAllAtomProfileCaps.ActualAtomProfileFirstCapsAt
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 M dr Ar p q x := by
    let Hx := hAP0 x hx
    exact ⟨Hx.highSmooth,Hx.lowSmooth,Hx.reverseHighSmooth,Hx.reverseLowSmooth,
      fun aa => (Hx.highBound aa).trans hCpM,fun aa => (Hx.lowBound aa).trans hCpM,
      fun aa => (Hx.reverseHighBound aa).trans hCpM,fun aa => (Hx.reverseLowBound aa).trans hCpM,
      fun aa => (Hx.highDerivativeBound aa).trans hCpM,fun aa => (Hx.lowDerivativeBound aa).trans hCpM,
      fun aa => (Hx.reverseHighDerivativeBound aa).trans hCpM,
      fun aa => (Hx.reverseLowDerivativeBound aa).trans hCpM⟩
  have hFacts := actual_mixed_weak_facts
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    P dF Cm g2 hg2 dr Ar p hdr hAr q F K hK hsupp M hAP hTP hTF
  refine ⟨hFacts,?_⟩
  have hPoint (x : R3) (hx : x ∈ K) (k i : Fin 3) (z : ZeroWord) :
      |WeakRow P g2 dr Ar p q F x k i z| ≤ CRow*eta*(referenceDensityFamily g L (q,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x) := by
    let r := referenceRadius dr Ar p L x
    let beta := actualReferenceBeta g L q dr Ar p x
    let U := UF F x
    let du := directionalFDeriv (coordinateDirection k)
      (ActualHigherSScalarCommutatorNativeForm.halfInput hO hD F) x
    let mu := referenceDensityFamily g L (q,x)
    let E := finiteCoreReferenceProfileEnergy hO hD g hg L q beta F x
    let t := (Tq dr Ar p q) x
    have hr : 0 ≤ r := (referenceRadius_pos dr Ar p L x hdr hAr).le
    have hbX : 1 ≤ beta := hb x hx
    have hb0 : 0 ≤ beta := zero_le_one.trans hbX
    have hmu0 : 0 ≤ mu := (referenceDensityFamily_pos g hg L (q,x)).le
    have hS : ActualHigherSMixedWordScalarJets.ScalarPointJet
        (mixedWordScalar g L g2 dr Ar p q k i z) x (Cs*r^3) (Cs*r^3*beta) :=
      (hScalars q hq dr hdr hdr1 Ar hAr p hp x (ball_subset_closedBall (hKball hx))
        hbX ((hs x hx).trans heta1)).2 k i z
    have hG (aa bb : ZeroAtom) : ‖P.gainHigh aa bb t‖ ≤ M := by
      have h0 : ‖P.gainHigh aa bb t‖ ≤ Mg := by
        simpa only [norm_iteratedFDerivWithin_zero] using (hGains aa bb 0 le_rfl t (hTP x hx)).1
      exact h0.trans hMgM
    have hCl (aa bb : ZeroAtom) : ‖P.gainLow aa bb t‖ ≤ M := by
      have h0 : ‖P.gainLow aa bb t‖ ≤ Mg := by
        simpa only [norm_iteratedFDerivWithin_zero] using (hGains aa bb 0 le_rfl t (hTP x hx)).2
      exact h0.trans hMgM
    have hSkew := cubicSkewRow_bound
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P t du U
      (eAtom i) (wordAtoms z).1 (wordAtoms z).2 M hM0
      (hAP x hx).highBound (hAP x hx).reverseHighBound
      (hAP x hx).lowBound (hAP x hx).reverseLowBound hG hCl
    have hForms := actual_mixed_form_bounds
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 dr Ar p q x M Cs r beta hM0 hCs.le hr hbX (hAP x hx) k i z hS
    have hSkewWeighted : |Skew P g2 dr Ar p q F x k i z| ≤ mu*(Csk*r^3*‖du‖*‖U‖) := by
      rw [actualMixedCubicSkewRow,abs_mul,abs_mul,abs_of_nonneg hmu0]
      calc
        _ ≤ mu*(Cs*r^3)*(4*‖PL‖*M^2*‖du‖*‖U‖) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hS.value hmu0) hSkew (abs_nonneg _)
            (by positivity)
        _ = _ := by dsimp [Csk,N]; ring
    have hDiagonal : |cubicAtomForm g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        t (eAtom i) (wordAtoms z).1 (wordAtoms z).2 U U| ≤ 2*‖PL‖*M^3*‖U‖^2 :=
      (abs_bilinear_diagonal_le _ U).trans (mul_le_mul_of_nonneg_right hForms.1 (sq_nonneg _))
    have hDensity : |Density g2 dr Ar p q F x k i z| ≤ mu*(Cden*r^3*‖U‖^2) := by
      rw [actualMixedCubicDensityRow,abs_mul,abs_mul]
      calc
        _ ≤ (Md*mu)*(Cs*r^3)*(2*‖PL‖*M^3*‖U‖^2) :=
          mul_le_mul (mul_le_mul (hdmu q hq x (ball_subset_closedBall (hKball hx)) k)
            hS.value (abs_nonneg _) (mul_nonneg hMd0 hmu0)) hDiagonal
              (abs_nonneg _) (by positivity)
        _ = _ := by dsimp [Cden,N]; ring
    have hDir : ‖coordinateDirection k‖ ≤ Cdir :=
      (Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ k)).trans
        (by dsimp [Cdir]; linarith)
    have hDNorm : ‖directionalFDeriv (coordinateDirection k) (QMix g2 dr Ar p q k i z) x‖ ≤
        (8*Cs*‖PL‖*M^3*r^3*beta)*Cdir :=
      ((fderiv ℝ (QMix g2 dr Ar p q k i z) x).le_opNorm _).trans
        (mul_le_mul hForms.2 hDir (norm_nonneg _) (by positivity))
    have hCoefficient : |Coefficient g2 dr Ar p q F x k i z| ≤ mu*(Ccoef*r^3*beta*‖U‖^2) := by
      rw [actualMixedCubicCoefficientRow,abs_mul,abs_of_nonneg hmu0,
        ← hFacts.coefficientDerivative_eq x k i z]
      calc
        _ ≤ mu*(‖directionalFDeriv (coordinateDirection k) (QMix g2 dr Ar p q k i z) x‖*‖U‖^2) :=
          mul_le_mul_of_nonneg_left (abs_bilinear_diagonal_le _ U) hmu0
        _ ≤ mu*(((8*Cs*‖PL‖*M^3*r^3*beta)*Cdir)*‖U‖^2) := by gcongr
        _ = _ := by dsimp [Ccoef,N]; ring
    have hHigh := ActualLowerSSelfFormation.beta_mul_norm_higherSInput_sq_le_referenceProfileEnergy
      g L hg hO hD q beta hb0 F x
    have hCoordAll := hcoord q hq x (ball_subset_closedBall (hKball hx)) beta hbX F
    have hCoord : beta⁻¹*‖du‖^2 ≤ Cr*E := by
      have hOne : ‖du‖^2 ≤ ∑ j : Fin 3,
          ‖directionalFDeriv (coordinateDirection j)
            (ActualHigherSScalarCommutatorNativeForm.halfInput hO hD F) x‖^2 :=
        by
          dsimp only [du]
          exact Finset.single_le_sum (fun (j : Fin 3) _ =>
            sq_nonneg (‖directionalFDeriv (coordinateDirection j)
              (ActualHigherSScalarCommutatorNativeForm.halfInput hO hD F) x‖)) (Finset.mem_univ k)
      have hFirst := mul_le_mul_of_nonneg_left hOne (inv_nonneg.mpr hb0)
      have hRest : beta⁻¹*(∑ j : Fin 3,
          ‖directionalFDeriv (coordinateDirection j)
            (ActualHigherSScalarCommutatorNativeForm.halfInput hO hD F) x‖^2) ≤
          coordinateEnergyDensity coordinateDirection beta
            (ActualHigherSScalarCommutatorNativeForm.halfInput hO hD F) x := by
        unfold coordinateEnergyDensity
        exact le_add_of_nonneg_right (by positivity)
      exact hFirst.trans (hRest.trans hCoordAll)
    have hAbsorb := ActualHigherSMixedCubicAbsorption.mixed_cubic_three_term_absorption
      r beta eta E ‖U‖ ‖du‖ Cr Csk Cden Ccoef mu hr hbX heta heta1 (hs x hx)
      (norm_nonneg _) (norm_nonneg _) hCr.le hCsk hCden hCcoef hmu0 hHigh hCoord
    calc
      _ ≤ |Skew P g2 dr Ar p q F x k i z|+|Density g2 dr Ar p q F x k i z|+
          |Coefficient g2 dr Ar p q F x k i z| :=
        (abs_sub_le_abs_add_abs _ _).trans (add_le_add (abs_sub_le_abs_add_abs _ _) le_rfl)
      _ ≤ mu*(Csk*r^3*‖du‖*‖U‖)+mu*(Cden*r^3*‖U‖^2)+mu*(Ccoef*r^3*beta*‖U‖^2) :=
        add_le_add (add_le_add hSkewWeighted hDensity) hCoefficient
      _ = mu*(Csk*r^3*‖du‖*‖U‖+Cden*r^3*‖U‖^2+Ccoef*r^3*beta*‖U‖^2) := by ring
      _ ≤ CRow*eta*(mu*E) := hAbsorb
  have hWeighted (x : R3) :
      |actualMixedCubicWeakRemainder
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P g2 dr Ar p q F x| ≤
        (Cmix*eta)*(referenceDensityFamily g L (q,x)*finiteCoreReferenceProfileEnergy
          hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x) := by
    by_cases hx : x ∈ K
    · have hsum := (Finset.abs_sum_le_sum_abs _ Finset.univ).trans
        (Finset.sum_le_sum (fun k _ => (Finset.abs_sum_le_sum_abs _ Finset.univ).trans
          (Finset.sum_le_sum (fun i _ => (Finset.abs_sum_le_sum_abs _ Finset.univ).trans
            (Finset.sum_le_sum (fun z _ => hPoint x hx k i z))))))
      have hE0 := finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q
        (actualReferenceBeta g L q dr Ar p x) (zero_le_one.trans (hb x hx)) F x
      have hmu0 := (referenceDensityFamily_pos g hg L (q,x)).le
      calc
        _ ≤ (1863 : ℝ)*(CRow*eta*(referenceDensityFamily g L (q,x)*finiteCoreReferenceProfileEnergy
            hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x)) := by
          convert hsum using 1 <;> simp only [actualMixedCubicWeakRemainder,Finset.sum_const,Finset.card_univ,
            Fintype.card_fin,card_zeroWord,nsmul_eq_mul,Nat.cast_ofNat] <;> ring
        _ ≤ (Cmix*eta)*(referenceDensityFamily g L (q,x)*finiteCoreReferenceProfileEnergy
            hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x) := by
          dsimp [Cmix]
          nlinarith only [mul_nonneg heta (mul_nonneg hmu0 hE0)]
    · have h0 := (higherSInput_smooth_and_zero hO hD F K hsupp).2 x hx
      have hE0 := finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q
        (actualReferenceBeta g L q dr Ar p x)
        (actualReferenceBeta_pos g hg L q dr Ar p hL hdr hAr hp x).le F x
      have hmu0 := (referenceDensityFamily_pos g hg L (q,x)).le
      have hR0 := actual_mixed_weak_remainder_zero_of_input_zero
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        P g2 dr Ar p q F x h0
      rw [hR0, abs_zero]
      exact mul_nonneg (mul_nonneg hCmix.le heta) (mul_nonneg hmu0 hE0)
  have hEnergyInt := (hLeading q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 K hK hKball F hsupp hb hs).2.1
  calc
    _ ≤ ∫ x, |actualMixedCubicWeakRemainder
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P g2 dr Ar p q F x| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (actualMixedCubicWeakRemainder
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P g2 dr Ar p q F)
    _ ≤ ∫ x, (Cmix*eta)*(referenceDensityFamily g L (q,x)*finiteCoreReferenceProfileEnergy
        hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x) :=
      integral_mono hFacts.weakRemainder_integrable.abs (hEnergyInt.const_mul _) hWeighted
    _ = _ := by rw [integral_const_mul]
theorem exists_uniform_same_packet_actual_mixed_cubic_bound
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ Cmix etaMix : ℝ, 0 < Cmix ∧ 0 < etaMix ∧ etaMix ≤ data.eta0 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaMix →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      Integrable (fun x => referenceDensityFamily g L (q,x)*
        ⟪PF g2 dr Ar p q F x, KL (Z2 g2 dr Ar p q F x)⟫_ℝ) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x)*
        ⟪PR g2 dr Ar p q F x, KL (T2 g2 dr Ar p q F x)⟫_ℝ) ∧
      |2*((∫ x, referenceDensityFamily g L (q,x)*
          ⟪PF g2 dr Ar p q F x, KL (Z2 g2 dr Ar p q F x)⟫_ℝ) -
        (∫ x, referenceDensityFamily g L (q,x)*
          ⟪PR g2 dr Ar p q F x, KL (T2 g2 dr Ar p q F x)⟫_ℝ))| ≤
        Cmix*eta*(∫ x, referenceDensityFamily g L (q,x)*finiteCoreReferenceProfileEnergy
          hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x)
 := by
  obtain ⟨d,hd,P,Cmix,etaMix,hCmix,hetaMix,hetaMix0,hAll⟩ :=
    exists_uniform_same_packet_actual_mixed_cubic_weak_bound
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hL hKernel g2 hg2
  refine ⟨Cmix,etaMix,hCmix,hetaMix,hetaMix0,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaMix' K hK hKball F hsupp hb hs
  obtain ⟨hFacts,hBound⟩ := hAll q hq dr hdr hdr1 Ar hAr p hp eta heta hetaMix' K hK hKball F hsupp hb hs
  exact ⟨hFacts.physicalFirst_integrable,hFacts.physicalReverse_integrable,
    hFacts.integral_identity.symm ▸ hBound⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSActualCubicBound
