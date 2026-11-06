import Calderon.ActualLowerUSFinitePretestSupport
import Calderon.ActualLowerUSOrdinaryAngularBrackets
import Calderon.ActualLowerUSFirstAngularGainTranspose
import Calderon.ActualLowerUSZeroSWordBudget
import Calderon.ActualLowerUSWeakQuadraticLeibniz
import Calderon.ActualLowerUSFiniteQuadraticCommutator
import Calderon.ActualLowerUSIndexedAngularGraphs
import Calderon.ActualLowerUSZeroSDecomposition

/-!
Literal all-five-group primitive G/Q gained words, with true adjoint words.
Actual primitive generator/Q weak graphs and original-profile caps.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSGeneratorZeroCommutator
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualFullEGainedEndpoints ActualAngularHighDraft ActualAngularPiDraft
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ActualPiJacobiRadialGainedRows ActualMixedAngularPairedGains ActualLowerUSSecondRow
  ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation NormalizedPrincipalMetric
  ActualLowerUSZeroSWordBudget FixedParameterProfilePullback
  MovingFrameConnection SmoothMetricFrame ActualNormalizedSecondMetricDrift
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

@[instance_reducible] private def gqHighMapNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
attribute [local instance] gqHighMapNormed
@[instance_reducible] private def gqHighMapSpace : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
attribute [local instance] gqHighMapSpace
@[instance_reducible] private def gqLowMapNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] gqLowMapNormed
@[instance_reducible] private def gqLowMapSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] gqLowMapSpace
@[instance_reducible] private def gqZeroMapNormed : NormedAddCommGroup (Hi →L[ℝ] Neg) := inferInstance
attribute [local instance] gqZeroMapNormed
@[instance_reducible] private def gqZeroMapSpace : NormedSpace ℝ (Hi →L[ℝ] Neg) := inferInstance
attribute [local instance] gqZeroMapSpace

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

local notation "MRoom" => MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0
  g L y0 Φ B ε C ρ H a w hData hg hreg data.δ0 data.germs
local notation "GRoom" δ:max => GeneratorEndpointRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs δ
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q




local notation "eH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "GL" => firstAngularGain
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "GH" => ActualLowerUSFirstAngularGainPair.firstAngularGainHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "GS" => ActualLowerUSFirstAngularGainPair.firstAngularGainSharpHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "GSL" => ActualLowerUSFirstAngularGainPair.firstAngularGainSharpLow
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "AGH" => lowerSAngularHigh hF hO hD
local notation "AGL" => lowerSAngularLow hF hO hD
local notation "AGSH" => lowerSAngularSharpHigh hF hO hD
local notation "AGSL" => lowerSAngularSharpLow hF hO hD
local notation "OH" => ordinarySAngularHigh hF hO hD
local notation "OL" => ordinarySAngularLow hF hO hD
local notation "OSH" => ordinarySAngularSharpHigh hF hO hD
local notation "OSL" => ordinarySAngularSharpLow hF hO hD
local notation "BH" => lowerSAngularBracketHigh hF hO hD
local notation "BL" => lowerSAngularBracketLow hF hO hD
local notation "BSH" => lowerSAngularBracketSharpHigh hF hO hD
local notation "BSL" => lowerSAngularBracketSharpLow hF hO hD

/-- The identity generator has zero genuine E gain; all remaining indices use
exactly the retained first-angular room and paired reverse endpoint. -/
def lowerGeneratorEGainHigh (mixed : MRoom) (j : Fin 3) (t : Tpar) :
    LowerCoreAngularGeneratorIndex → Hi →L[ℝ] Half
  | Sum.inl _ => 0
  | Sum.inr v => GH mixed j t v

def lowerGeneratorEGainLow (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (j : Fin 3) (t : Tpar) : LowerCoreAngularGeneratorIndex → Half →L[ℝ] Neg
  | Sum.inl _ => 0
  | Sum.inr v => GL mixed δ gen j t v

def lowerGeneratorEGainSharpHigh (j : Fin 3) (t : Tpar) :
    LowerCoreAngularGeneratorIndex → Hi →L[ℝ] Half
  | Sum.inl _ => 0
  | Sum.inr v => GS j t v

def lowerGeneratorEGainSharpLow (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (j : Fin 3) (t : Tpar) : LowerCoreAngularGeneratorIndex → Half →L[ℝ] Neg
  | Sum.inl _ => 0
  | Sum.inr v => GSL mixed δ gen j t v

local notation "CH" => lowerGeneratorEGainHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "CL" => lowerGeneratorEGainLow
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "CSH" => lowerGeneratorEGainSharpHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "CSL" => lowerGeneratorEGainSharpLow
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

/-- G against one actual E, at either signed orientation. -/
def generatorESingleWord (adjoint : Bool) (mixed : MRoom) (j : Fin 3)
    (t : Tpar) (i : LowerCoreAngularGeneratorIndex) : Hi →L[ℝ] Neg :=
  ContinuousLinearMap.comp JL (if adjoint then CSH j t i else CH mixed j t i)

/-- G against H E, retaining both order-two words and the actual adjoint. -/
def generatorOrdinaryEWord (adjoint : Bool) (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (h : OrdinarySAngularIndex) (j : Fin 3) (t : Tpar)
    (i : LowerCoreAngularGeneratorIndex) : Hi →L[ℝ] Neg :=
  if adjoint then
    (eL j t).comp (BSH i h) + (CSL mixed δ gen j t i).comp (OSH h)
  else
    (BL i h).comp (EH j t) + (OL h).comp (CH mixed j t i)

/-- G against E H, with the distinct original composition order. -/
def generatorEOrdinaryWord (adjoint : Bool) (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (j : Fin 3) (h : OrdinarySAngularIndex) (t : Tpar)
    (i : LowerCoreAngularGeneratorIndex) : Hi →L[ℝ] Neg :=
  if adjoint then
    (OSL h).comp (CSH j t i) + (BSL i h).comp (eH j t)
  else
    (CL mixed δ gen j t i).comp (OH h) + (EL j t).comp (BH i h)

/-- G against the full ordered E/E word; no negative-space E extension occurs. -/
def generatorDoubleEWord (adjoint : Bool) (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (a b : Fin 3) (t : Tpar) (i : LowerCoreAngularGeneratorIndex) : Hi →L[ℝ] Neg :=
  if adjoint then
    (eL b t).comp (CSH a t i) + (CSL mixed δ gen b t i).comp (eH a t)
  else
    (CL mixed δ gen a t i).comp (EH b t) + (EL a t).comp (CH mixed b t i)

/-- Ordinary G/derivative-E word. The reverse derivative is the derivative of
the actual ordered reverse E family, not a differentiated gained assumption. -/
def generatorDerivativeEWord (adjoint : Bool) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (j : Fin 3) (X : R3) (x : R3) (i : LowerCoreAngularGeneratorIndex) : Hi →L[ℝ] Neg :=
  if adjoint then
    (fderiv ℝ (fun y => eL j ((Tq dr Ar p q) y)) x X).comp (AGSH i) -
      (AGSL i).comp (fderiv ℝ (fun y => eH j ((Tq dr Ar p q) y)) x X)
  else
    (AGL i).comp (fderiv ℝ (fun y => EH j ((Tq dr Ar p q) y)) x X) -
      (fderiv ℝ (fun y => EL j ((Tq dr Ar p q) y)) x X).comp (AGH i)


/-- Finite tags retain every original scalar coefficient and ordered word. -/
abbrev ZeroQPair := Fin 3 × Fin 3
abbrev ZeroQTriple := Fin 3 × Fin 3 × Fin 3
abbrev ZeroQQuad := Fin 3 × Fin 3 × Fin 3 × Fin 3
abbrev ZeroQLinearIndex := ZeroQPair ⊕ (ZeroQPair ⊕ (ZeroQTriple ⊕ Fin 3))
abbrev ZeroQQuadraticIndex := (ZeroQQuad ⊕ ZeroQQuad) ⊕
  ((ZeroQPair ⊕ ZeroQPair) ⊕ ((ZeroQPair ⊕ ZeroQPair) ⊕ ZeroQPair))
abbrev ZeroQTermIndex := ZeroQLinearIndex ⊕ ZeroQQuadraticIndex

/-- Exact real coefficients of the eleven scalar rows within the five groups. -/
def zeroQTermScalar (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ) (x : R3) :
    ZeroQTermIndex → ℝ :=
  let r := referenceRadius dr Ar p L x
  let Q := fun a b : Fin 3 => referenceDensityPrincipalFrameCoefficient g g2 L q x a b
  let f := fun a : Fin 3 => referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x a
  let Gamma := fun a c d : Fin 3 => referenceFrameConnectionCoefficient g L q x
    (referenceMetricGramFrame g L (q,x) a) c d
  fun
  | Sum.inl (Sum.inl ab) => r^2*Q ab.1 ab.2
  | Sum.inl (Sum.inr (Sum.inl ab)) => r^2*Q ab.1 ab.2*f ab.1
  | Sum.inl (Sum.inr (Sum.inr (Sum.inl abk))) => -r^2*Q abk.1 abk.2.1*Gamma abk.1 abk.2.2 abk.2.1
  | Sum.inl (Sum.inr (Sum.inr (Sum.inr a))) => r^2*normalizedSecondDriftFrameJoint g g2 L a (q,x)
  | Sum.inr (Sum.inl (Sum.inl abcd)) => r^2*Q abcd.1 abcd.2.1*(1/2 : ℝ)*Gamma abcd.1 abcd.2.2.1 abcd.2.2.2
  | Sum.inr (Sum.inl (Sum.inr abcd)) => r^2*Q abcd.1 abcd.2.1*(1/2 : ℝ)*Gamma abcd.2.1 abcd.2.2.1 abcd.2.2.2
  | Sum.inr (Sum.inr (Sum.inl (Sum.inl ab))) => r^2*Q ab.1 ab.2*f ab.1
  | Sum.inr (Sum.inr (Sum.inl (Sum.inr ab))) => r^2*Q ab.1 ab.2*f ab.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inl ab)))) => r*Q ab.1 ab.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inr ab)))) => r*Q ab.1 ab.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr ab))) => r^3*Q ab.1 ab.2

/-- Only the ordinary differentiated-E row has a non-unit directional weight. -/
def zeroQTermDirectionWeight (q : ℝ) (x : R3) : ZeroQTermIndex → ℝ
  | Sum.inl (Sum.inl ab) => ‖referenceMetricGramFrame g L (q,x) ab.1‖
  | _ => 1

/-- Every term is a two-word H^(3/2)-to-H^(-1/2) operator, at either true
signed orientation. No scalar coefficients are hidden inside its gain data. -/
def zeroQTermWord (adjoint : Bool) (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (q dr Ar : ℝ) (p : ℕ) (x : R3) (i : LowerCoreAngularGeneratorIndex) :
    ZeroQTermIndex → Hi →L[ℝ] Neg :=
  let t := (Tq dr Ar p q) x
  let E := generatorESingleWord
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data adjoint mixed
  let HE := generatorOrdinaryEWord
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data adjoint mixed δ gen
  let EHword := generatorEOrdinaryWord
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data adjoint mixed δ gen
  fun
  | Sum.inl (Sum.inl ab) => generatorDerivativeEWord
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      adjoint dr Ar p q ab.2 (referenceMetricGramFrame g L (q,x) ab.1) x i
  | Sum.inl (Sum.inr (Sum.inl ab)) => E ab.2 t i
  | Sum.inl (Sum.inr (Sum.inr (Sum.inl abk))) => E abk.2.2 t i
  | Sum.inl (Sum.inr (Sum.inr (Sum.inr a))) => E a t i
  | Sum.inr (Sum.inl (Sum.inl abcd)) => HE (Sum.inl (abcd.2.2.1,abcd.2.2.2)) abcd.2.1 t i
  | Sum.inr (Sum.inl (Sum.inr abcd)) => EHword abcd.1 (Sum.inl (abcd.2.2.1,abcd.2.2.2)) t i
  | Sum.inr (Sum.inr (Sum.inl (Sum.inl ab))) => HE (Sum.inr (Sum.inl ())) ab.2 t i
  | Sum.inr (Sum.inr (Sum.inl (Sum.inr ab))) => EHword ab.1 (Sum.inr (Sum.inl ())) t i
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inl ab)))) => HE (Sum.inr (Sum.inr ab.1)) ab.2 t i
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inr ab)))) => EHword ab.1 (Sum.inr (Sum.inr ab.2)) t i
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr ab))) => generatorDoubleEWord
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      adjoint mixed δ gen ab.1 ab.2 t i

/-- Literal all-five-group primitive weak coefficient. -/
def lowerGeneratorZeroCoefficient (adjoint : Bool) (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ) (x : R3)
    (i : LowerCoreAngularGeneratorIndex) : Hi →L[ℝ] Neg :=
  ∑ z : ZeroQTermIndex, zeroQTermScalar g L g2 q dr Ar p x z •
    zeroQTermWord g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data adjoint mixed δ gen q dr Ar p x i z

/-- Exposed coefficient mass for the actual finite word presentation. -/
def zeroQTermMass (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ) (x : R3) : ℝ :=
  ∑ z : ZeroQTermIndex,
    |zeroQTermScalar g L g2 q dr Ar p x z| * zeroQTermDirectionWeight g L q x z


/-- The finite presentation has exactly the exposed original five-group mass;
there is no hidden derivative or omitted scalar coefficient. -/
theorem zeroQTermMass_eq_lowerSZeroWordMass (g2 : MatrixField) (q dr Ar : ℝ)
    (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (x : R3) :
    zeroQTermMass g L g2 q dr Ar p x = lowerSZeroWordMass g g2 L q dr Ar p x := by
  have hr := referenceRadius_pos dr Ar p L x hdr hAr
  simp only [zeroQTermMass,ZeroQTermIndex,ZeroQLinearIndex,ZeroQQuadraticIndex,
    ZeroQPair,ZeroQTriple,ZeroQQuad,Fintype.sum_sum_type,Fintype.sum_prod_type,
    zeroQTermScalar,zeroQTermDirectionWeight]
  simp only [abs_mul,abs_neg,abs_pow,abs_of_pos hr]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<1/2),mul_one]
  unfold lowerSZeroWordMass lowerSConnectionWordMass
  dsimp only
  simp only [two_mul,mul_add,add_mul,Finset.sum_add_distrib,
    Finset.mul_sum,Finset.sum_mul,mul_assoc]
  abel

/-- A pointwise primitive word cap gives the norm of the entire actual sum.
This is only finite norm bookkeeping; the final producer discharges its word
cap from original data and does not expose this premise. -/
private lemma norm_lowerGeneratorZeroCoefficient_le
    (adjoint : Bool) (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)
    (x : R3) (i : LowerCoreAngularGeneratorIndex) (M : ℝ) (hM : 0 ≤ M)
    (hWord : ∀ z : ZeroQTermIndex,
      ‖zeroQTermWord g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        Room hreg data adjoint mixed δ gen q dr Ar p x i z‖ ≤
      M*zeroQTermDirectionWeight g L q x z) :
    ‖lowerGeneratorZeroCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data adjoint mixed δ gen g2 q dr Ar p x i‖ ≤
      M*lowerSZeroWordMass g g2 L q dr Ar p x := by
  rw [← zeroQTermMass_eq_lowerSZeroWordMass g L g2 q dr Ar p hdr hAr x]
  calc
    _ ≤ ∑ z : ZeroQTermIndex, |zeroQTermScalar g L g2 q dr Ar p x z| *
        (M*zeroQTermDirectionWeight g L q x z) := by
      unfold lowerGeneratorZeroCoefficient
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro z _
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hWord z) (abs_nonneg _)
    _ = M*zeroQTermMass g L g2 q dr Ar p x := by
      unfold zeroQTermMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring


/-- Fixed canonical angular family budget. It depends on no profile or metric
point and is derived from the norms of this finite list of actual maps. -/
def generatorZeroCanonicalNormBudget : ℝ :=
  1 + (∑ i : LowerCoreAngularGeneratorIndex,
    (‖AGH i‖+‖AGL i‖+‖AGSH i‖+‖AGSL i‖)) +
    (∑ h : OrdinarySAngularIndex, (‖OH h‖+‖OL h‖+‖OSH h‖+‖OSL h‖)) +
    (∑ i : LowerCoreAngularGeneratorIndex, ∑ h : OrdinarySAngularIndex,
      (‖BH i h‖+‖BL i h‖+‖BSH i h‖+‖BSL i h‖))

private lemma generatorZeroCanonicalNormBudget_pos :
    0 < generatorZeroCanonicalNormBudget hF hO hD := by
  unfold generatorZeroCanonicalNormBudget
  positivity

private lemma four_nonnegative_families_caps {ι : Type*} [Fintype ι]
    (f0 f1 f2 f3 : ι → ℝ)
    (h0 : ∀ i, 0 ≤ f0 i) (h1 : ∀ i, 0 ≤ f1 i)
    (h2 : ∀ i, 0 ≤ f2 i) (h3 : ∀ i, 0 ≤ f3 i) (i : ι) :
    let S := ∑ j : ι, (f0 j+f1 j+f2 j+f3 j)
    f0 i ≤ S ∧ f1 i ≤ S ∧ f2 i ≤ S ∧ f3 i ≤ S := by
  have hi := Finset.single_le_sum
    (fun j _ => add_nonneg (add_nonneg (add_nonneg (h0 j) (h1 j)) (h2 j)) (h3 j))
    (Finset.mem_univ i)
  dsimp only
  exact ⟨by linarith [h1 i,h2 i,h3 i],by linarith [h0 i,h2 i,h3 i],
    by linarith [h0 i,h1 i,h3 i],by linarith [h0 i,h1 i,h2 i]⟩

private lemma generatorZeroCanonicalNormBudget_caps :
    let N := generatorZeroCanonicalNormBudget hF hO hD
    (∀ i : LowerCoreAngularGeneratorIndex,
      ‖AGH i‖ ≤ N ∧ ‖AGL i‖ ≤ N ∧ ‖AGSH i‖ ≤ N ∧ ‖AGSL i‖ ≤ N) ∧
    (∀ h : OrdinarySAngularIndex,
      ‖OH h‖ ≤ N ∧ ‖OL h‖ ≤ N ∧ ‖OSH h‖ ≤ N ∧ ‖OSL h‖ ≤ N) ∧
    (∀ i : LowerCoreAngularGeneratorIndex, ∀ h : OrdinarySAngularIndex,
      ‖BH i h‖ ≤ N ∧ ‖BL i h‖ ≤ N ∧ ‖BSH i h‖ ≤ N ∧ ‖BSL i h‖ ≤ N) := by
  let A := ∑ i : LowerCoreAngularGeneratorIndex, (‖AGH i‖+‖AGL i‖+‖AGSH i‖+‖AGSL i‖)
  let O := ∑ h : OrdinarySAngularIndex, (‖OH h‖+‖OL h‖+‖OSH h‖+‖OSL h‖)
  let Bk := ∑ i : LowerCoreAngularGeneratorIndex, ∑ h : OrdinarySAngularIndex,
    (‖BH i h‖+‖BL i h‖+‖BSH i h‖+‖BSL i h‖)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ =>
    add_nonneg (add_nonneg (add_nonneg (norm_nonneg (AGH i))
      (norm_nonneg (AGL i))) (norm_nonneg (AGSH i))) (norm_nonneg (AGSL i)))
  have hO0 : 0 ≤ O := Finset.sum_nonneg (fun h _ =>
    add_nonneg (add_nonneg (add_nonneg (norm_nonneg (OH h))
      (norm_nonneg (OL h))) (norm_nonneg (OSH h))) (norm_nonneg (OSL h)))
  have hBk : 0 ≤ Bk := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun h _ =>
    add_nonneg (add_nonneg (add_nonneg (norm_nonneg (BH i h))
      (norm_nonneg (BL i h))) (norm_nonneg (BSH i h))) (norm_nonneg (BSL i h))))
  have hN : generatorZeroCanonicalNormBudget hF hO hD = 1+A+O+Bk := rfl
  have hAN : A ≤ generatorZeroCanonicalNormBudget hF hO hD := by
    exact hN.symm ▸ (show A ≤ 1+A+O+Bk by linarith)
  have hON : O ≤ generatorZeroCanonicalNormBudget hF hO hD := by
    exact hN.symm ▸ (show O ≤ 1+A+O+Bk by linarith)
  have hBN : Bk ≤ generatorZeroCanonicalNormBudget hF hO hD := by
    exact hN.symm ▸ (show Bk ≤ 1+A+O+Bk by linarith)
  constructor
  · intro i
    have hi := four_nonnegative_families_caps
      (fun j => ‖AGH j‖) (fun j => ‖AGL j‖) (fun j => ‖AGSH j‖) (fun j => ‖AGSL j‖)
      (fun j => norm_nonneg (AGH j)) (fun j => norm_nonneg (AGL j))
      (fun j => norm_nonneg (AGSH j)) (fun j => norm_nonneg (AGSL j)) i
    exact ⟨hi.1.trans hAN,hi.2.1.trans hAN,hi.2.2.1.trans hAN,hi.2.2.2.trans hAN⟩
  constructor
  · intro h
    have hi := four_nonnegative_families_caps
      (fun j => ‖OH j‖) (fun j => ‖OL j‖) (fun j => ‖OSH j‖) (fun j => ‖OSL j‖)
      (fun j => norm_nonneg (OH j)) (fun j => norm_nonneg (OL j))
      (fun j => norm_nonneg (OSH j)) (fun j => norm_nonneg (OSL j)) h
    exact ⟨hi.1.trans hON,hi.2.1.trans hON,hi.2.2.1.trans hON,hi.2.2.2.trans hON⟩
  · intro i h
    have hi := four_nonnegative_families_caps
      (fun j => ‖BH i j‖) (fun j => ‖BL i j‖) (fun j => ‖BSH i j‖) (fun j => ‖BSL i j‖)
      (fun j => norm_nonneg (BH i j)) (fun j => norm_nonneg (BL i j))
      (fun j => norm_nonneg (BSH i j)) (fun j => norm_nonneg (BSL i j)) h
    have hOuter : (∑ j : OrdinarySAngularIndex,
        (‖BH i j‖+‖BL i j‖+‖BSH i j‖+‖BSL i j‖)) ≤ Bk :=
      Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun k _ =>
        add_nonneg (add_nonneg (add_nonneg (norm_nonneg (BH j k))
          (norm_nonneg (BL j k))) (norm_nonneg (BSH j k))) (norm_nonneg (BSL j k))))
        (Finset.mem_univ i)
    have hiN := hOuter.trans hBN
    exact ⟨hi.1.trans hiN,hi.2.1.trans hiN,hi.2.2.1.trans hiN,hi.2.2.2.trans hiN⟩

private lemma norm_comp_budget (A : Half →L[ℝ] Neg) (B : Hi →L[ℝ] Half)
    (a b : ℝ) (ha : 0 ≤ a) (hA : ‖A‖ ≤ a) (hB : ‖B‖ ≤ b) :
    ‖A.comp B‖ ≤ a*b :=
  (ContinuousLinearMap.opNorm_comp_le A B).trans (mul_le_mul hA hB (norm_nonneg B) ha)

/-- Pointwise actual word estimate. The gain and E caps are internal inputs of
this private bookkeeping lemma; the public original-profile producer derives
all of them from the selected physical room. -/
private lemma norm_zeroQTermWord_le
    (adjoint : Bool) (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (q dr Ar : ℝ) (p : ℕ) (x : R3) (M : ℝ) (hM : 0 ≤ M)
    (hGain : ∀ j : Fin 3, ∀ v : FirstAngularIndex,
      ‖GL mixed δ gen j ((Tq dr Ar p q) x) v‖ ≤ M ∧
      ‖GH mixed j ((Tq dr Ar p q) x) v‖ ≤ M ∧
      ‖GS j ((Tq dr Ar p q) x) v‖ ≤ M ∧
      ‖GSL mixed δ gen j ((Tq dr Ar p q) x) v‖ ≤ M)
    (hE : ∀ j : Fin 3,
      ‖EH j ((Tq dr Ar p q) x)‖ ≤ data.M ∧
      ‖EL j ((Tq dr Ar p q) x)‖ ≤ data.M ∧
      ‖eH j ((Tq dr Ar p q) x)‖ ≤ data.M ∧
      ‖eL j ((Tq dr Ar p q) x)‖ ≤ data.M ∧
      ‖fderiv ℝ (fun y => EH j ((Tq dr Ar p q) y)) x‖ ≤ data.M*data.KT ∧
      ‖fderiv ℝ (fun y => EL j ((Tq dr Ar p q) y)) x‖ ≤ data.M*data.KT ∧
      ‖fderiv ℝ (fun y => eH j ((Tq dr Ar p q) y)) x‖ ≤ data.M*data.KT ∧
      ‖fderiv ℝ (fun y => eL j ((Tq dr Ar p q) y)) x‖ ≤ data.M*data.KT) :
    let N := generatorZeroCanonicalNormBudget hF hO hD
    let Cw := 1+2*N*data.M*data.KT+2*N*(data.M+M)+2*M*data.M+M
    ∀ i : LowerCoreAngularGeneratorIndex, ∀ z : ZeroQTermIndex,
      ‖zeroQTermWord g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        Room hreg data adjoint mixed δ gen q dr Ar p x i z‖ ≤
      Cw*zeroQTermDirectionWeight g L q x z := by
  let N := generatorZeroCanonicalNormBudget hF hO hD
  let Cw := 1+2*N*data.M*data.KT+2*N*(data.M+M)+2*M*data.M+M
  have hN : 0 ≤ N := (generatorZeroCanonicalNormBudget_pos hF hO hD).le
  have hME : 0 ≤ data.M := data.M_nonneg
  have hKT : 0 ≤ data.KT := data.KT_pos.le
  have hNcap := generatorZeroCanonicalNormBudget_caps hF hO hD
  have hCw0 : 0 ≤ Cw := by dsimp only [Cw]; positivity
  have hd0 : 0 ≤ 2*N*data.M*data.KT := by positivity
  have ho0 : 0 ≤ 2*N*(data.M+M) := by positivity
  have he0 : 0 ≤ 2*M*data.M := by positivity
  have hMC : M ≤ Cw := by dsimp only [Cw]; linarith only [hd0,ho0,he0]
  have hNC : N*data.M+N*M ≤ Cw := by
    dsimp only [Cw]
    nlinarith [mul_nonneg hN hME,mul_nonneg hN hM,
      mul_nonneg (mul_nonneg hN hME) hKT,mul_nonneg hM hME]
  have hEC : 2*M*data.M ≤ Cw := by dsimp only [Cw]; linarith only [hd0,ho0,hM]
  have hDC : 2*N*data.M*data.KT ≤ Cw := by dsimp only [Cw]; linarith only [ho0,he0,hM]
  have hG (j : Fin 3) (i : LowerCoreAngularGeneratorIndex) :
      ‖CL mixed δ gen j ((Tq dr Ar p q) x) i‖ ≤ M ∧
      ‖CH mixed j ((Tq dr Ar p q) x) i‖ ≤ M ∧
      ‖CSH j ((Tq dr Ar p q) x) i‖ ≤ M ∧
      ‖CSL mixed δ gen j ((Tq dr Ar p q) x) i‖ ≤ M := by
    cases i with
    | inl v => simp only [lowerGeneratorEGainLow,lowerGeneratorEGainHigh,
        lowerGeneratorEGainSharpHigh,lowerGeneratorEGainSharpLow,norm_zero]; exact ⟨hM,hM,hM,hM⟩
    | inr v => exact hGain j v
  have hJL : ‖JL‖ ≤ 1 := norm_sphereSobolevInclusionL_le (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  have hSingle (j : Fin 3) (i : LowerCoreAngularGeneratorIndex) :
      ‖generatorESingleWord g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        Room hreg data adjoint mixed j ((Tq dr Ar p q) x) i‖ ≤ Cw := by
    unfold generatorESingleWord
    have hc : ‖(if adjoint then CSH j ((Tq dr Ar p q) x) i else CH mixed j ((Tq dr Ar p q) x) i)‖ ≤ M := by
      cases adjoint
      · exact (hG j i).2.1
      · exact (hG j i).2.2.1
    exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hJL hc (norm_nonneg _) (by norm_num))).trans (by simpa only [one_mul] using hMC)
  have hHE (h : OrdinarySAngularIndex) (j : Fin 3) (i : LowerCoreAngularGeneratorIndex) :
      ‖generatorOrdinaryEWord g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        Room hreg data adjoint mixed δ gen h j ((Tq dr Ar p q) x) i‖ ≤ Cw := by
    cases adjoint
    · change ‖(BL i h).comp (EH j _) + (OL h).comp (CH mixed j _ i)‖ ≤ Cw
      exact ((norm_add_le _ _).trans (add_le_add
        (norm_comp_budget _ _ N data.M hN (hNcap.2.2 i h).2.1 (hE j).1)
        (norm_comp_budget _ _ N M hN (hNcap.2.1 h).2.1 (hG j i).2.1))).trans hNC
    · change ‖(eL j _).comp (BSH i h) + (CSL mixed δ gen j _ i).comp (OSH h)‖ ≤ Cw
      have h1 := norm_comp_budget _ _ data.M N hME (hE j).2.2.2.1 (hNcap.2.2 i h).2.2.1
      have h2 := norm_comp_budget _ _ M N hM (hG j i).2.2.2 (hNcap.2.1 h).2.2.1
      nlinarith only [(norm_add_le _ _).trans (add_le_add h1 h2),hNC]
  have hEH (j : Fin 3) (h : OrdinarySAngularIndex) (i : LowerCoreAngularGeneratorIndex) :
      ‖generatorEOrdinaryWord g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        Room hreg data adjoint mixed δ gen j h ((Tq dr Ar p q) x) i‖ ≤ Cw := by
    cases adjoint
    · change ‖(CL mixed δ gen j _ i).comp (OH h) + (EL j _).comp (BH i h)‖ ≤ Cw
      have h1 := norm_comp_budget _ _ M N hM (hG j i).1 (hNcap.2.1 h).1
      have h2 := norm_comp_budget _ _ data.M N hME (hE j).2.1 (hNcap.2.2 i h).1
      nlinarith only [(norm_add_le _ _).trans (add_le_add h1 h2),hNC]
    · change ‖(OSL h).comp (CSH j _ i) + (BSL i h).comp (eH j _)‖ ≤ Cw
      exact ((norm_add_le _ _).trans (add_le_add
        (norm_comp_budget _ _ N M hN (hNcap.2.1 h).2.2.2 (hG j i).2.2.1)
        (norm_comp_budget _ _ N data.M hN (hNcap.2.2 i h).2.2.2 (hE j).2.2.1))).trans
        (by nlinarith only [hNC])
  have hEE (ia ib : Fin 3) (i : LowerCoreAngularGeneratorIndex) :
      ‖generatorDoubleEWord g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        Room hreg data adjoint mixed δ gen ia ib ((Tq dr Ar p q) x) i‖ ≤ Cw := by
    cases adjoint
    · change ‖(CL mixed δ gen ia _ i).comp (EH ib _) + (EL ia _).comp (CH mixed ib _ i)‖ ≤ Cw
      have h1 := norm_comp_budget _ _ M data.M hM (hG ia i).1 (hE ib).1
      have h2 := norm_comp_budget _ _ data.M M hME (hE ia).2.1 (hG ib i).2.1
      nlinarith only [(norm_add_le _ _).trans (add_le_add h1 h2),hEC]
    · change ‖(eL ib _).comp (CSH ia _ i) + (CSL mixed δ gen ib _ i).comp (eH ia _)‖ ≤ Cw
      have h1 := norm_comp_budget _ _ data.M M hME (hE ib).2.2.2.1 (hG ia i).2.2.1
      have h2 := norm_comp_budget _ _ M data.M hM (hG ib i).2.2.2 (hE ia).2.2.1
      nlinarith only [(norm_add_le _ _).trans (add_le_add h1 h2),hEC]
  have hDE (j : Fin 3) (X : R3) (i : LowerCoreAngularGeneratorIndex) :
      ‖generatorDerivativeEWord g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        adjoint dr Ar p q j X x i‖ ≤ Cw*‖X‖ := by
    have hdEH : ‖fderiv ℝ (fun y => EH j ((Tq dr Ar p q) y)) x X‖ ≤ data.M*data.KT*‖X‖ :=
      ((fderiv ℝ (fun y => EH j ((Tq dr Ar p q) y)) x).le_opNorm X).trans
        (mul_le_mul_of_nonneg_right (hE j).2.2.2.2.1 (norm_nonneg X))
    have hdEL : ‖fderiv ℝ (fun y => EL j ((Tq dr Ar p q) y)) x X‖ ≤ data.M*data.KT*‖X‖ :=
      ((fderiv ℝ (fun y => EL j ((Tq dr Ar p q) y)) x).le_opNorm X).trans
        (mul_le_mul_of_nonneg_right (hE j).2.2.2.2.2.1 (norm_nonneg X))
    have hdeH : ‖fderiv ℝ (fun y => eH j ((Tq dr Ar p q) y)) x X‖ ≤ data.M*data.KT*‖X‖ :=
      ((fderiv ℝ (fun y => eH j ((Tq dr Ar p q) y)) x).le_opNorm X).trans
        (mul_le_mul_of_nonneg_right (hE j).2.2.2.2.2.2.1 (norm_nonneg X))
    have hdeL : ‖fderiv ℝ (fun y => eL j ((Tq dr Ar p q) y)) x X‖ ≤ data.M*data.KT*‖X‖ :=
      ((fderiv ℝ (fun y => eL j ((Tq dr Ar p q) y)) x).le_opNorm X).trans
        (mul_le_mul_of_nonneg_right (hE j).2.2.2.2.2.2.2 (norm_nonneg X))
    have hLast := mul_le_mul_of_nonneg_right hDC (norm_nonneg X)
    cases adjoint
    · change ‖ContinuousLinearMap.comp (AGL i)
          (fderiv ℝ (fun y => EH j ((Tq dr Ar p q) y)) x X) -
        ContinuousLinearMap.comp
          (fderiv ℝ (fun y => EL j ((Tq dr Ar p q) y)) x X) (AGH i)‖ ≤ Cw*‖X‖
      have h1 := norm_comp_budget _ _ N (data.M*data.KT*‖X‖) hN (hNcap.1 i).2.1 hdEH
      have h2 := norm_comp_budget _ _ (data.M*data.KT*‖X‖) N (by positivity) hdEL (hNcap.1 i).1
      nlinarith only [(norm_sub_le _ _).trans (add_le_add h1 h2),hLast]
    · change ‖ContinuousLinearMap.comp
          (fderiv ℝ (fun y => eL j ((Tq dr Ar p q) y)) x X) (AGSH i) -
        ContinuousLinearMap.comp (AGSL i)
          (fderiv ℝ (fun y => eH j ((Tq dr Ar p q) y)) x X)‖ ≤ Cw*‖X‖
      have h1 := norm_comp_budget _ _ (data.M*data.KT*‖X‖) N (by positivity) hdeL (hNcap.1 i).2.2.1
      have h2 := norm_comp_budget _ _ N (data.M*data.KT*‖X‖) hN (hNcap.1 i).2.2.2 hdeH
      nlinarith only [(norm_sub_le _ _).trans (add_le_add h1 h2),hLast]
  change ∀ i : LowerCoreAngularGeneratorIndex, ∀ z : ZeroQTermIndex,
    ‖zeroQTermWord g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data adjoint mixed δ gen q dr Ar p x i z‖ ≤
      Cw*zeroQTermDirectionWeight g L q x z
  intro i z
  rcases z with (ab | (ab | (abk | a))) | ((abcd | abcd) | ((ab | ab) | ((ab | ab) | ab)))
  · exact hDE ab.2 _ i
  · simpa only [zeroQTermWord,zeroQTermDirectionWeight,mul_one] using hSingle ab.2 i
  · simpa only [zeroQTermWord,zeroQTermDirectionWeight,mul_one] using hSingle abk.2.2 i
  · simpa only [zeroQTermWord,zeroQTermDirectionWeight,mul_one] using hSingle a i
  · simpa only [zeroQTermWord,zeroQTermDirectionWeight,mul_one] using hHE (Sum.inl (abcd.2.2.1,abcd.2.2.2)) abcd.2.1 i
  · simpa only [zeroQTermWord,zeroQTermDirectionWeight,mul_one] using hEH abcd.1 (Sum.inl (abcd.2.2.1,abcd.2.2.2)) i
  · simpa only [zeroQTermWord,zeroQTermDirectionWeight,mul_one] using hHE (Sum.inr (Sum.inl ())) ab.2 i
  · simpa only [zeroQTermWord,zeroQTermDirectionWeight,mul_one] using hEH ab.1 (Sum.inr (Sum.inl ())) i
  · simpa only [zeroQTermWord,zeroQTermDirectionWeight,mul_one] using hHE (Sum.inr (Sum.inr ab.1)) ab.2 i
  · simpa only [zeroQTermWord,zeroQTermDirectionWeight,mul_one] using hEH ab.1 (Sum.inr (Sum.inr ab.2)) i
  · simpa only [zeroQTermWord,zeroQTermDirectionWeight,mul_one] using hEE ab.1 ab.2 i


/-- Actual all-five-group bounded words, including the true reverse adjoint,
with every cap internally derived before profiles. The native finite graph is
proved separately; no callback is a premise of this producer. -/
theorem exists_retained_lowerGeneratorZeroCoefficient_uniform_profile_bound
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ mixed : MRoom, ∃ δ : ℝ, 0 < δ ∧ ∃ gen : GRoom δ,
      ∃ C_G : ℝ, 0 < C_G ∧ ∃ etaG : ℝ, 0 < etaG ∧
      etaG ≤ data.eta0 ∧ etaG ≤ 1 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaG →
      ∀ x ∈ closedBall y0 ρ, x ∈ ball y0 ρ →
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      CoordinateBootstrapJets.coordinateH8 (referenceNormalizedPrincipalDifference g g2 L q) x ≤
        eta*referenceRadius dr Ar p L x →
      (Tq dr Ar p q) x ∈ ParamRoom δ ∧
      (Tq dr Ar p q) x ∈ ParamRoom mixed.δ ∧
      (Tq dr Ar p q) x ∈ ParamRoom data.δ ∧
      ∀ i : LowerCoreAngularGeneratorIndex, ∀ adjoint : Bool,
        ‖lowerGeneratorZeroCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          Room hreg data adjoint mixed δ gen g2 q dr Ar p x i‖ ≤
          C_G*referenceRadius dr Ar p L x := by
  obtain ⟨mixed,δ,hδ,gen,M,hM,etaG,hEtaG,hEtaG0,hEtaG1,hGain⟩ :=
    ActualLowerUSFirstAngularGainPair.exists_retained_firstAngular_gain_pair_uniform_profile_caps
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 hL hKernel
  obtain ⟨CQ,hCQ,hQ⟩ := exists_lowerSZeroWordMass_uniform_profile_bound
    g g2 hg hg2 L hL y0 ρ
  let N := generatorZeroCanonicalNormBudget hF hO hD
  let Cw := 1+2*N*data.M*data.KT+2*N*(data.M+M)+2*M*data.M+M
  have hN : 0 ≤ N := (generatorZeroCanonicalNormBudget_pos hF hO hD).le
  have hME : 0 ≤ data.M := data.M_nonneg
  have hKT : 0 ≤ data.KT := data.KT_pos.le
  have hCw : 0 < Cw := by dsimp only [Cw]; positivity
  refine ⟨mixed,δ,hδ,gen,Cw*CQ,mul_pos hCw hCQ,etaG,hEtaG,hEtaG0,hEtaG1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaG x hx hxBall hb hs hH8
  have hc := hGain q hq dr hdr hdr1 Ar hAr p hp eta heta hetaG x hx hxBall hb hs hH8
  have hpE (j : Fin 3) := data.physical_caps q hq dr hdr hdr1 Ar hAr p hp
    eta heta (hetaG.trans hEtaG0) x hx hxBall hb hs j j
  have hGainPoint (j : Fin 3) (v : FirstAngularIndex) :
      ‖GL mixed δ gen j ((Tq dr Ar p q) x) v‖ ≤ M ∧
      ‖GH mixed j ((Tq dr Ar p q) x) v‖ ≤ M ∧
      ‖GS j ((Tq dr Ar p q) x) v‖ ≤ M ∧
      ‖GSL mixed δ gen j ((Tq dr Ar p q) x) v‖ ≤ M := by
    have h := hc.2.2.2 j v
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩
  have hEPoint (j : Fin 3) :
      ‖EH j ((Tq dr Ar p q) x)‖ ≤ data.M ∧
      ‖EL j ((Tq dr Ar p q) x)‖ ≤ data.M ∧
      ‖eH j ((Tq dr Ar p q) x)‖ ≤ data.M ∧
      ‖eL j ((Tq dr Ar p q) x)‖ ≤ data.M ∧
      ‖fderiv ℝ (fun y => EH j ((Tq dr Ar p q) y)) x‖ ≤ data.M*data.KT ∧
      ‖fderiv ℝ (fun y => EL j ((Tq dr Ar p q) y)) x‖ ≤ data.M*data.KT ∧
      ‖fderiv ℝ (fun y => eH j ((Tq dr Ar p q) y)) x‖ ≤ data.M*data.KT ∧
      ‖fderiv ℝ (fun y => eL j ((Tq dr Ar p q) y)) x‖ ≤ data.M*data.KT :=
    ⟨(hpE j).2.2.1.2.1,(hpE j).2.2.2.1.2.1,
      (hpE j).2.2.2.2.1.2.1,(hpE j).2.2.2.2.2.2.1,
      (hpE j).2.2.1.2.2,(hpE j).2.2.2.1.2.2,
      (hpE j).2.2.2.2.1.2.2,(hpE j).2.2.2.2.2.2.2⟩
  have hMass := hQ q hq dr hdr hdr1 Ar hAr p hp eta heta (hetaG.trans hEtaG1) x hx hb hs
  refine ⟨hc.1,hc.2.1,hc.2.2.1,?_⟩
  intro i adjoint
  have hWords := norm_zeroQTermWord_le
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    adjoint mixed δ gen q dr Ar p x M hM.le hGainPoint hEPoint i
  have hNorm := norm_lowerGeneratorZeroCoefficient_le
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    adjoint mixed δ gen g2 q dr Ar p hdr hAr x i Cw hCw.le hWords
  calc
    _ ≤ Cw*lowerSZeroWordMass g g2 L q dr Ar p x := hNorm
    _ ≤ Cw*(CQ*referenceRadius dr Ar p L x) := mul_le_mul_of_nonneg_left hMass hCw.le
    _ = (Cw*CQ)*referenceRadius dr Ar p L x := by ring


open Filter

/-- Actual ordinary E high/low and reverse adjunction diagrams on the retained
physical region. These use the same W.piGerm, not an abstract response family. -/
private lemma actualOrdinaryE_pivots (j : Fin 3) (t : Tpar)
    (ht : t ∈ ParamRoom data.δ) :
    (∀ u : Hi, JL (EH j t u) = EL j t (IH u)) ∧
    (∀ u : Hi, JL (eH j t u) = eL j t (IH u)) ∧
    (∀ u v : Half, PP u (EL j t v) = PP v (eL j t u)) := by
  have ht0 : t ∈ ParamRoom data.δ0 :=
    ⟨commonRoom_mono y0 ρ data.δ_le0 ht.1,ht.2⟩
  have hSeg := segment_of_mem_commonRoom hcalc hF hO hD τ0
    g L y0 Φ B ε C ρ H a w hData data.parameter_subset t.1 ht.1
  have hp := (data.germs.piGerm j t ht0).self_of_nhds
  let Q := piJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    data.δ0 data.germs j t
  exact ⟨fun u => canonicalHigh_low_compatibility
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg j t hSeg Q hp.1 hp.2.1 u,
    fun u => explicit_ordered_reverse_high_low_compatibility
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 j t hSeg Q hp.2.1 hp.2.2 u,
    fun u v => canonicalLow_explicit_ordered_reverse_pairing
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 j t hSeg Q hp.2.1 hp.2.2 u v⟩

private lemma fderiv_fixed_clm_at {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (f : R3 → E) (x X : R3) (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun y => A (f y)) x X = A (fderiv ℝ f x X) := by
  simpa only [ContinuousLinearMap.comp_apply,Function.comp_def] using
    congrArg (fun D : R3 →L[ℝ] F => D X) (A.hasFDerivAt.comp x hf.hasFDerivAt).fderiv

private lemma fderiv_fixed_clm_eventuallyEq {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : E →L[ℝ] G) (B : F →L[ℝ] G) (f : R3 → E) (k : R3 → F)
    (x X : R3) (hf : DifferentiableAt ℝ f x) (hk : DifferentiableAt ℝ k x)
    (heq : (fun y => A (f y)) =ᶠ[𝓝 x] (fun y => B (k y))) :
    A (fderiv ℝ f x X) = B (fderiv ℝ k x X) := by
  have hd := congrArg (fun D : R3 →L[ℝ] G => D X) (heq.fderiv_eq (𝕜 := ℝ))
  exact (fderiv_fixed_clm_at A f x X hf).symm.trans
    (hd.trans (fderiv_fixed_clm_at B k x X hk))

/-- Differentiating the actual neighborhood diagrams retains both reverse
adjunction and high/low compatibility. It introduces no gain derivative cap. -/
private lemma actualOrdinaryE_derivative_pivots
    (q dr Ar : ℝ) (p : ℕ) (x X : R3) (j : Fin 3)
    (hmem : ∀ᶠ y in 𝓝 x, (Tq dr Ar p q) y ∈ ParamRoom data.δ)
    (hEH : DifferentiableAt ℝ (fun y => EH j ((Tq dr Ar p q) y)) x)
    (hEL : DifferentiableAt ℝ (fun y => EL j ((Tq dr Ar p q) y)) x)
    (heH : DifferentiableAt ℝ (fun y => eH j ((Tq dr Ar p q) y)) x)
    (heL : DifferentiableAt ℝ (fun y => eL j ((Tq dr Ar p q) y)) x) :
    (∀ u : Hi,
      JL ((fderiv ℝ (fun y => EH j ((Tq dr Ar p q) y)) x X) u) =
      (fderiv ℝ (fun y => EL j ((Tq dr Ar p q) y)) x X) (IH u)) ∧
    (∀ u : Hi,
      JL ((fderiv ℝ (fun y => eH j ((Tq dr Ar p q) y)) x X) u) =
      (fderiv ℝ (fun y => eL j ((Tq dr Ar p q) y)) x X) (IH u)) ∧
    (∀ u v : Half,
      PP u ((fderiv ℝ (fun y => EL j ((Tq dr Ar p q) y)) x X) v) =
      PP v ((fderiv ℝ (fun y => eL j ((Tq dr Ar p q) y)) x X) u)) := by
  constructor
  · intro u
    let EvalH : (Hi →L[ℝ] Half) →L[ℝ] Neg :=
      ContinuousLinearMap.comp JL (ContinuousLinearMap.apply ℝ Half u)
    let EvalL : (Half →L[ℝ] Neg) →L[ℝ] Neg := ContinuousLinearMap.apply ℝ Neg (IH u)
    have heq : (fun y => EvalH (EH j ((Tq dr Ar p q) y))) =ᶠ[𝓝 x]
        (fun y => EvalL (EL j ((Tq dr Ar p q) y))) :=
      hmem.mono (fun y hy => (actualOrdinaryE_pivots
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data j _ hy).1 u)
    exact fderiv_fixed_clm_eventuallyEq EvalH EvalL
      (fun y => EH j ((Tq dr Ar p q) y)) (fun y => EL j ((Tq dr Ar p q) y))
      x X hEH hEL heq
  constructor
  · intro u
    let EvalH : (Hi →L[ℝ] Half) →L[ℝ] Neg :=
      ContinuousLinearMap.comp JL (ContinuousLinearMap.apply ℝ Half u)
    let EvalL : (Half →L[ℝ] Neg) →L[ℝ] Neg := ContinuousLinearMap.apply ℝ Neg (IH u)
    have heq : (fun y => EvalH (eH j ((Tq dr Ar p q) y))) =ᶠ[𝓝 x]
        (fun y => EvalL (eL j ((Tq dr Ar p q) y))) :=
      hmem.mono (fun y hy => (actualOrdinaryE_pivots
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data j _ hy).2.1 u)
    exact fderiv_fixed_clm_eventuallyEq EvalH EvalL
      (fun y => eH j ((Tq dr Ar p q) y)) (fun y => eL j ((Tq dr Ar p q) y))
      x X heH heL heq
  · intro u v
    let EvalH : (Half →L[ℝ] Neg) →L[ℝ] ℝ :=
      (innerSL ℝ u).comp (ContinuousLinearMap.apply ℝ Neg v)
    let EvalL : (Half →L[ℝ] Neg) →L[ℝ] ℝ :=
      (innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ Neg u)
    have heq : (fun y => EvalH (EL j ((Tq dr Ar p q) y))) =ᶠ[𝓝 x]
        (fun y => EvalL (eL j ((Tq dr Ar p q) y))) :=
      hmem.mono (fun y hy => (actualOrdinaryE_pivots
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data j _ hy).2.2 u v)
    exact fderiv_fixed_clm_eventuallyEq EvalH EvalL
      (fun y => EL j ((Tq dr Ar p q) y)) (fun y => eL j ((Tq dr Ar p q) y))
      x X hEL heL heq


private lemma pp_add_right (a : Half) (b c : Neg) : PP a (b+c) = PP a b+PP a c :=
  inner_add_right a b c
private lemma pp_sub_right (a : Half) (b c : Neg) : PP a (b-c) = PP a b-PP a c :=
  inner_sub_right a b c
private lemma pp_zero_right (a : Half) : PP a (0 : Neg) = 0 := inner_zero_right a
private lemma pp_zero_left (b : Neg) : PP (0 : Half) b = 0 := inner_zero_left b

private lemma lower_transpose_pairing_of_upper
    (A : Half →L[ℝ] Neg) (AH : Hi →L[ℝ] Half)
    (hc : ∀ u : Hi, A (IH u) = JL (AH u)) (u : Hi) (z : Half) :
    PP (IH u) (sphereLowerDistributionalTranspose A z) = PP (AH u) (JL z) := by
  calc
    _ = PP z (A (IH u)) :=
      (sphereSobolevDualPairing_lower_distributionalTranspose A (IH u) z).symm
    _ = PP z (JL (AH u)) := congrArg (PP z) (hc u)
    _ = _ := v016_pairing_inclusion_symm _ _

/-- Ordinary first-order weak graph with genuine finite higher lifts. The
second family can be a differentiated actual E; no gained derivative is used. -/
private lemma weak_firstorder_word_graph
    (G Gstar : Hi →L[ℝ] Half) (Gl Gstarl : Half →L[ℝ] Neg)
    (E : Hi →L[ℝ] Half) (El : Half →L[ℝ] Neg)
    (hG : ∀ a b : Half, PP a (Gl b) = PP b (Gstarl a))
    (hGs : ∀ a : Hi, Gstarl (IH a) = JL (Gstar a))
    (hE : ∀ a : Hi, JL (E a) = El (IH a))
    (u v uGstar vG : Hi) (hu : IH uGstar = Gstar u) (hv : IH vG = G v) :
    PP (IH uGstar) (JL (E v))-PP (IH u) (JL (E vG)) =
      PP (IH u) (Gl (E v)-El (G v)) := by
  have hLeft : PP (IH uGstar) (JL (E v)) = PP (IH u) (Gl (E v)) := by
    calc
      _ = PP (Gstar u) (JL (E v)) := congrArg (fun z => PP z (JL (E v))) hu
      _ = PP (E v) (JL (Gstar u)) := v016_pairing_inclusion_symm _ _
      _ = PP (E v) (Gstarl (IH u)) := congrArg (PP (E v)) (hGs u).symm
      _ = _ := (hG (IH u) (E v)).symm
  have hRight : PP (IH u) (JL (E vG)) = PP (IH u) (El (G v)) := by
    rw [hE,hv]
  exact (congrArg₂ (fun a b : ℝ => a-b) hLeft hRight).trans
    (pp_sub_right (IH u) (Gl (E v)) (El (G v))).symm

/-- A two-factor product is transposed using its actual lower adjunction and
high reverse graph. The nonfinite intermediate vector remains in Half. -/
private lemma weak_product_actual_adjoint
    (A : Half →L[ℝ] Neg) (Astar : Hi →L[ℝ] Half)
    (Bhigh : Hi →L[ℝ] Half) (Bstar : Half →L[ℝ] Neg)
    (hA : ∀ u : Hi, ∀ z : Half, PP (IH u) (A z) = PP (Astar u) (JL z))
    (hB : ∀ v : Hi, ∀ z : Half, PP (IH v) (Bstar z) = PP z (JL (Bhigh v)))
    (u v : Hi) :
    PP (IH u) (A (Bhigh v)) = PP (IH v) (Bstar (Astar u)) := by
  calc
    _ = PP (Astar u) (JL (Bhigh v)) := hA u (Bhigh v)
    _ = _ := (hB v (Astar u)).symm


private lemma lowerGeneratorEGain_high_graph (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (j : Fin 3) (t : Tpar) (htG : t ∈ ParamRoom δ) (htM : t ∈ ParamRoom mixed.δ)
    (htD : t ∈ ParamRoom data.δ) (i : LowerCoreAngularGeneratorIndex) (u : Hi) :
    JL (CH mixed j t i u) = AGL i (EH j t u)-EL j t (AGH i u) := by
  cases i with
  | inl z =>
    have h := (actualOrdinaryE_pivots
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data j t htD).1 u
    simpa only [lowerGeneratorEGainHigh,lowerSAngularLow,lowerSAngularHigh,
      ContinuousLinearMap.zero_apply,map_zero,h,sub_self] using (rfl : (0 : Neg)=0)
  | inr v =>
    exact ActualLowerUSFirstAngularGainPair.firstAngularGainHigh_graph
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      mixed δ gen j t htG htM v u

private lemma lowerGeneratorEGain_sharp_high_graph (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (j : Fin 3) (t : Tpar) (htG : t ∈ ParamRoom δ) (htM : t ∈ ParamRoom mixed.δ)
    (htD : t ∈ ParamRoom data.δ) (i : LowerCoreAngularGeneratorIndex) (u : Hi) :
    JL (CSH j t i u) = eL j t (AGSH i u)-AGSL i (eH j t u) := by
  cases i with
  | inl z =>
    have h := (actualOrdinaryE_pivots
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data j t htD).2.1 u
    simpa only [lowerGeneratorEGainSharpHigh,lowerSAngularSharpLow,lowerSAngularSharpHigh,
      ContinuousLinearMap.zero_apply,map_zero,h,sub_self] using (rfl : (0 : Neg)=0)
  | inr v =>
    exact ActualLowerUSFirstAngularGainPair.firstAngularGainSharpHigh_graph
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      mixed δ gen j t htG htM v u

private lemma lowerGeneratorEGain_high_low_compatibility
    (mixed : MRoom) (δ : ℝ) (gen : GRoom δ) (j : Fin 3) (t : Tpar)
    (htG : t ∈ ParamRoom δ) (htM : t ∈ ParamRoom mixed.δ)
    (i : LowerCoreAngularGeneratorIndex) (u : Hi) :
    CL mixed δ gen j t i (IH u) = JL (CH mixed j t i u) := by
  cases i with
  | inl z => simp only [lowerGeneratorEGainLow,lowerGeneratorEGainHigh,ContinuousLinearMap.zero_apply,map_zero]
  | inr v =>
    exact (firstAngularGain_graph
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      mixed δ gen j t htG htM v u).trans
      (ActualLowerUSFirstAngularGainPair.firstAngularGainHigh_graph
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        mixed δ gen j t htG htM v u).symm

private lemma lowerGeneratorEGain_low_pairing
    (mixed : MRoom) (δ : ℝ) (gen : GRoom δ) (j : Fin 3) (t : Tpar)
    (htG : t ∈ ParamRoom δ) (htM : t ∈ ParamRoom mixed.δ)
    (i : LowerCoreAngularGeneratorIndex) (u : Hi) (z : Half) :
    PP (IH u) (CL mixed δ gen j t i z) = PP (CSH j t i u) (JL z) := by
  cases i with
  | inl a => simp only [lowerGeneratorEGainLow,lowerGeneratorEGainSharpHigh,
      ContinuousLinearMap.zero_apply,pp_zero_right,pp_zero_left]
  | inr v =>
    exact ActualLowerUSFirstAngularGainPair.firstAngularGain_low_pairing
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      mixed δ gen j t htG htM v u z

private lemma lowerGeneratorEGain_sharp_low_pairing
    (mixed : MRoom) (δ : ℝ) (gen : GRoom δ) (j : Fin 3) (t : Tpar)
    (htG : t ∈ ParamRoom δ) (htM : t ∈ ParamRoom mixed.δ)
    (i : LowerCoreAngularGeneratorIndex) (u : Hi) (z : Half) :
    PP (IH u) (CSL mixed δ gen j t i z) = PP (CH mixed j t i u) (JL z) := by
  cases i with
  | inl a => simp only [lowerGeneratorEGainSharpLow,lowerGeneratorEGainHigh,
      ContinuousLinearMap.zero_apply,pp_zero_right,pp_zero_left]
  | inr v =>
    exact lower_transpose_pairing_of_upper (GL mixed δ gen j t v) (GH mixed j t v)
      (fun u0 => lowerGeneratorEGain_high_low_compatibility
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        mixed δ gen j t htG htM (Sum.inr v) u0) u z


/-- Original primitive Q words before commutation. The first derivative is the
literal physical pullback derivative; all composition orders are retained. -/
def zeroQOriginalTermWord (q dr Ar : ℝ) (p : ℕ) (x : R3) :
    ZeroQTermIndex → Hi →L[ℝ] Neg :=
  let t := (Tq dr Ar p q) x
  let E := fun j : Fin 3 => ContinuousLinearMap.comp JL (EH j t)
  fun
  | Sum.inl (Sum.inl ab) => ContinuousLinearMap.comp JL
      (fderiv ℝ (fun y => EH ab.2 ((Tq dr Ar p q) y)) x
        (referenceMetricGramFrame g L (q,x) ab.1))
  | Sum.inl (Sum.inr (Sum.inl ab)) => E ab.2
  | Sum.inl (Sum.inr (Sum.inr (Sum.inl abk))) => E abk.2.2
  | Sum.inl (Sum.inr (Sum.inr (Sum.inr a))) => E a
  | Sum.inr (Sum.inl (Sum.inl abcd)) =>
      (OL (Sum.inl (abcd.2.2.1,abcd.2.2.2))).comp (EH abcd.2.1 t)
  | Sum.inr (Sum.inl (Sum.inr abcd)) =>
      (EL abcd.1 t).comp (OH (Sum.inl (abcd.2.2.1,abcd.2.2.2)))
  | Sum.inr (Sum.inr (Sum.inl (Sum.inl ab))) =>
      (OL (Sum.inr (Sum.inl ()))).comp (EH ab.2 t)
  | Sum.inr (Sum.inr (Sum.inl (Sum.inr ab))) =>
      (EL ab.1 t).comp (OH (Sum.inr (Sum.inl ())))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inl ab)))) =>
      (OL (Sum.inr (Sum.inr ab.1))).comp (EH ab.2 t)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inr ab)))) =>
      (EL ab.1 t).comp (OH (Sum.inr (Sum.inr ab.2)))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr ab))) => (EL ab.1 t).comp (EH ab.2 t)

private lemma high_test_pairing_of_low
    (A Astar : Half →L[ℝ] Neg) (AstarHigh : Hi →L[ℝ] Half)
    (hp : ∀ u v : Half, PP u (A v) = PP v (Astar u))
    (hc : ∀ u : Hi, JL (AstarHigh u) = Astar (IH u)) (u : Hi) (z : Half) :
    PP (IH u) (A z) = PP (AstarHigh u) (JL z) := by
  calc
    _ = PP z (Astar (IH u)) := hp (IH u) z
    _ = PP z (JL (AstarHigh u)) := congrArg (PP z) (hc u).symm
    _ = _ := v016_pairing_inclusion_symm _ _

private lemma high_test_reverse_pairing_of_low
    (A Astar : Half →L[ℝ] Neg) (Ahigh : Hi →L[ℝ] Half)
    (hp : ∀ u v : Half, PP u (A v) = PP v (Astar u))
    (hc : ∀ u : Hi, JL (Ahigh u) = A (IH u)) (u : Hi) (z : Half) :
    PP (IH u) (Astar z) = PP z (JL (Ahigh u)) := by
  exact (hp z (IH u)).symm.trans (congrArg (PP z) (hc u).symm)


private lemma scalar_word_graph_transport
    (A A0 C C0 : Hi →L[ℝ] Neg) (hA : A = A0) (hC : C = C0)
    (a b : Half) (v vG : Hi)
    (h : PP a (A0 v)-PP b (A0 vG) = PP b (C0 v)) :
    PP a (A v)-PP b (A vG) = PP b (C v) :=
  (congrArg (fun T : Hi →L[ℝ] Neg => PP a (T v)-PP b (T vG)) hA).trans
    (h.trans (congrArg (fun T : Hi →L[ℝ] Neg => PP b (T v)) hC).symm)

private lemma scalar_word_adjoint_transport
    (C C0 S S0 : Hi →L[ℝ] Neg) (hC : C = C0) (hS : S = S0)
    (a b : Half) (u v : Hi) (h : PP a (C0 v) = PP b (S0 u)) :
    PP a (C v) = PP b (S u) :=
  (congrArg (fun T : Hi →L[ℝ] Neg => PP a (T v)) hC).trans
    (h.trans (congrArg (fun T : Hi →L[ℝ] Neg => PP b (T u)) hS).symm)

/-- Exact primitive weak graph on actual higher finite lifts. Ordinary angular
brackets and actual G/E gains supply every cancellation; physical E outputs
are only ever arguments of bounded Half/negative maps. -/
private lemma zeroQTermWord_forward_graph
    (mixed : MRoom) (δ : ℝ) (gen : GRoom δ) (q dr Ar : ℝ) (p : ℕ) (x : R3)
    (htG : (Tq dr Ar p q) x ∈ ParamRoom δ)
    (htM : (Tq dr Ar p q) x ∈ ParamRoom mixed.δ)
    (hmem : ∀ᶠ y in 𝓝 x, (Tq dr Ar p q) y ∈ ParamRoom data.δ)
    (hDiff : ∀ j : Fin 3,
      DifferentiableAt ℝ (fun y => EH j ((Tq dr Ar p q) y)) x ∧
      DifferentiableAt ℝ (fun y => EL j ((Tq dr Ar p q) y)) x ∧
      DifferentiableAt ℝ (fun y => eH j ((Tq dr Ar p q) y)) x ∧
      DifferentiableAt ℝ (fun y => eL j ((Tq dr Ar p q) y)) x)
    (i : LowerCoreAngularGeneratorIndex) (u v uGstar vG : Hi)
    (hu : IH uGstar = AGSH i u) (hv : IH vG = AGH i v) (z : ZeroQTermIndex) :
    PP (IH uGstar) (zeroQOriginalTermWord g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      q dr Ar p x z v) -
    PP (IH u) (zeroQOriginalTermWord g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      q dr Ar p x z vG) =
    PP (IH u) (zeroQTermWord g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data false mixed δ gen q dr Ar p x i z v) := by
  let t := (Tq dr Ar p q) x
  have htD : t ∈ ParamRoom data.δ := hmem.self_of_nhds
  have hE (j : Fin 3) := actualOrdinaryE_pivots
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data j t htD
  have hG := lowerSAngularLow_pairing hF hO hD i
  have hGs : ∀ a : Hi, AGSL i (IH a) = JL (AGSH i a) :=
    fun a => (lowerSAngularSharpHigh_low_compatibility hF hO hD i a).symm
  have hSingle (j : Fin 3) :
      PP (IH uGstar) (JL (EH j t v))-PP (IH u) (JL (EH j t vG)) =
      PP (IH u) (JL (CH mixed j t i v)) := by
    exact (weak_firstorder_word_graph (AGH i) (AGSH i) (AGL i) (AGSL i)
      (EH j t) (EL j t) hG hGs (hE j).1 u v uGstar vG hu hv).trans
      (congrArg (PP (IH u)) (lowerGeneratorEGain_high_graph
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      mixed δ gen j t htG htM htD i v).symm)
  have hDE (j : Fin 3) (X : R3) :
      PP (IH uGstar) (JL ((fderiv ℝ (fun y => EH j ((Tq dr Ar p q) y)) x X) v))-
      PP (IH u) (JL ((fderiv ℝ (fun y => EH j ((Tq dr Ar p q) y)) x X) vG)) =
      PP (IH u) ((AGL i) ((fderiv ℝ (fun y => EH j ((Tq dr Ar p q) y)) x X) v)-
        (fderiv ℝ (fun y => EL j ((Tq dr Ar p q) y)) x X) ((AGH i) v)) := by
    have hd := actualOrdinaryE_derivative_pivots
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      q dr Ar p x X j hmem (hDiff j).1 (hDiff j).2.1 (hDiff j).2.2.1 (hDiff j).2.2.2
    exact weak_firstorder_word_graph (AGH i) (AGSH i) (AGL i) (AGSL i)
      (fderiv ℝ (fun y => EH j ((Tq dr Ar p q) y)) x X)
      (fderiv ℝ (fun y => EL j ((Tq dr Ar p q) y)) x X)
      hG hGs hd.1 u v uGstar vG hu hv
  have hHE (h : OrdinarySAngularIndex) (j : Fin 3) :
      PP (IH uGstar) (OL h (EH j t v))-PP (IH u) (OL h (EH j t vG)) =
      PP (IH u) (BL i h (EH j t v)+OL h (CH mixed j t i v)) := by
    exact ActualLowerUSWeakAngularWords.weak_quadratic_word_leibniz
      (AGH i) (AGSH i) (AGL i) (AGSL i)
      (OH h) (EH j t) (OSH h) (OL h) (EL j t) (OSL h)
      (BH i h) (BSH i h) (CH mixed j t i) (BL i h)
      hG (ordinarySAngularLow_pairing hF hO hD h)
      (fun a => (ordinarySAngularSharpHigh_low_compatibility hF hO hD h a).symm)
      (hE j).1 (lowerSAngularBracketLow_pairing hF hO hD i h)
      (lowerSAngularBracketSharpHigh_graph hF hO hD i h)
      (lowerGeneratorEGain_high_graph
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        mixed δ gen j t htG htM htD i)
      u v uGstar vG hu hv
  have hEH (j : Fin 3) (h : OrdinarySAngularIndex) :
      PP (IH uGstar) (EL j t (OH h v))-PP (IH u) (EL j t (OH h vG)) =
      PP (IH u) (CL mixed δ gen j t i (OH h v)+EL j t (BH i h v)) := by
    exact ActualLowerUSWeakAngularWords.weak_quadratic_word_leibniz
      (AGH i) (AGSH i) (AGL i) (AGSL i)
      (EH j t) (OH h) (eH j t) (EL j t) (OL h) (eL j t)
      (CH mixed j t i) (CSH j t i) (BH i h) (CL mixed δ gen j t i)
      hG (hE j).2.2 (fun a => ((hE j).2.1 a).symm)
      (ordinarySAngularHigh_low_compatibility hF hO hD h)
      (lowerGeneratorEGain_low_pairing
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        mixed δ gen j t htG htM i)
      (lowerGeneratorEGain_sharp_high_graph
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        mixed δ gen j t htG htM htD i)
      (lowerSAngularBracketHigh_graph hF hO hD i h)
      u v uGstar vG hu hv
  have hEE (ia ib : Fin 3) :
      PP (IH uGstar) (EL ia t (EH ib t v))-PP (IH u) (EL ia t (EH ib t vG)) =
      PP (IH u) (CL mixed δ gen ia t i (EH ib t v)+EL ia t (CH mixed ib t i v)) := by
    exact ActualLowerUSWeakAngularWords.weak_quadratic_word_leibniz
      (AGH i) (AGSH i) (AGL i) (AGSL i)
      (EH ia t) (EH ib t) (eH ia t) (EL ia t) (EL ib t) (eL ia t)
      (CH mixed ia t i) (CSH ia t i) (CH mixed ib t i) (CL mixed δ gen ia t i)
      hG (hE ia).2.2 (fun c => ((hE ia).2.1 c).symm) (hE ib).1
      (lowerGeneratorEGain_low_pairing
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        mixed δ gen ia t htG htM i)
      (lowerGeneratorEGain_sharp_high_graph
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        mixed δ gen ia t htG htM htD i)
      (lowerGeneratorEGain_high_graph
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        mixed δ gen ib t htG htM htD i)
      u v uGstar vG hu hv
  let O := zeroQOriginalTermWord
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q dr Ar p x
  let R := zeroQTermWord
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    false mixed δ gen q dr Ar p x i
  rcases z with (ab | (ab | (abk | ja))) | ((abcd | abcd) | ((ab | ab) | ((ab | ab) | ab)))
  · have hA : O (Sum.inl (Sum.inl ab)) = ContinuousLinearMap.comp (JL) ((fderiv ℝ (fun y => EH ab.2 ((Tq dr Ar p q) y)) x (referenceMetricGramFrame g L (q,x) ab.1))) := rfl
    have hC : R (Sum.inl (Sum.inl ab)) = ContinuousLinearMap.comp (AGL i) ((fderiv ℝ (fun y => EH ab.2 ((Tq dr Ar p q) y)) x (referenceMetricGramFrame g L (q,x) ab.1))) - ContinuousLinearMap.comp ((fderiv ℝ (fun y => EL ab.2 ((Tq dr Ar p q) y)) x (referenceMetricGramFrame g L (q,x) ab.1))) (AGH i) := by
      simp only [R,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have h0 : PP (IH uGstar) ((ContinuousLinearMap.comp (JL) ((fderiv ℝ (fun y => EH ab.2 ((Tq dr Ar p q) y)) x (referenceMetricGramFrame g L (q,x) ab.1)))) v) - PP (IH u) ((ContinuousLinearMap.comp (JL) ((fderiv ℝ (fun y => EH ab.2 ((Tq dr Ar p q) y)) x (referenceMetricGramFrame g L (q,x) ab.1)))) vG) =
        PP (IH u) ((ContinuousLinearMap.comp (AGL i) ((fderiv ℝ (fun y => EH ab.2 ((Tq dr Ar p q) y)) x (referenceMetricGramFrame g L (q,x) ab.1))) - ContinuousLinearMap.comp ((fderiv ℝ (fun y => EL ab.2 ((Tq dr Ar p q) y)) x (referenceMetricGramFrame g L (q,x) ab.1))) (AGH i)) v) := by
      simpa only [t,ContinuousLinearMap.comp_apply,add_apply,sub_apply] using (hDE ab.2 (referenceMetricGramFrame g L (q,x) ab.1))
    exact scalar_word_graph_transport _ _ _ _ hA hC (IH uGstar) (IH u) v vG h0
  · have hA : O (Sum.inl (Sum.inr (Sum.inl ab))) = ContinuousLinearMap.comp (JL) (EH ab.2 t) := rfl
    have hC : R (Sum.inl (Sum.inr (Sum.inl ab))) = ContinuousLinearMap.comp (JL) (CH mixed ab.2 t i) := by
      simp only [R,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have h0 : PP (IH uGstar) ((ContinuousLinearMap.comp (JL) (EH ab.2 t)) v) - PP (IH u) ((ContinuousLinearMap.comp (JL) (EH ab.2 t)) vG) =
        PP (IH u) ((ContinuousLinearMap.comp (JL) (CH mixed ab.2 t i)) v) := by
      simpa only [t,ContinuousLinearMap.comp_apply,add_apply,sub_apply] using (hSingle ab.2)
    exact scalar_word_graph_transport _ _ _ _ hA hC (IH uGstar) (IH u) v vG h0
  · have hA : O (Sum.inl (Sum.inr (Sum.inr (Sum.inl abk)))) = ContinuousLinearMap.comp (JL) (EH abk.2.2 t) := rfl
    have hC : R (Sum.inl (Sum.inr (Sum.inr (Sum.inl abk)))) = ContinuousLinearMap.comp (JL) (CH mixed abk.2.2 t i) := by
      simp only [R,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have h0 : PP (IH uGstar) ((ContinuousLinearMap.comp (JL) (EH abk.2.2 t)) v) - PP (IH u) ((ContinuousLinearMap.comp (JL) (EH abk.2.2 t)) vG) =
        PP (IH u) ((ContinuousLinearMap.comp (JL) (CH mixed abk.2.2 t i)) v) := by
      simpa only [t,ContinuousLinearMap.comp_apply,add_apply,sub_apply] using (hSingle abk.2.2)
    exact scalar_word_graph_transport _ _ _ _ hA hC (IH uGstar) (IH u) v vG h0
  · have hA : O (Sum.inl (Sum.inr (Sum.inr (Sum.inr ja)))) = ContinuousLinearMap.comp (JL) (EH ja t) := rfl
    have hC : R (Sum.inl (Sum.inr (Sum.inr (Sum.inr ja)))) = ContinuousLinearMap.comp (JL) (CH mixed ja t i) := by
      simp only [R,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have h0 : PP (IH uGstar) ((ContinuousLinearMap.comp (JL) (EH ja t)) v) - PP (IH u) ((ContinuousLinearMap.comp (JL) (EH ja t)) vG) =
        PP (IH u) ((ContinuousLinearMap.comp (JL) (CH mixed ja t i)) v) := by
      simpa only [t,ContinuousLinearMap.comp_apply,add_apply,sub_apply] using (hSingle ja)
    exact scalar_word_graph_transport _ _ _ _ hA hC (IH uGstar) (IH u) v vG h0
  · have hA : O (Sum.inr (Sum.inl (Sum.inl abcd))) = ContinuousLinearMap.comp (OL (Sum.inl (abcd.2.2.1,abcd.2.2.2))) (EH abcd.2.1 t) := rfl
    have hC : R (Sum.inr (Sum.inl (Sum.inl abcd))) = ContinuousLinearMap.comp (BL i (Sum.inl (abcd.2.2.1,abcd.2.2.2))) (EH abcd.2.1 t) + ContinuousLinearMap.comp (OL (Sum.inl (abcd.2.2.1,abcd.2.2.2))) (CH mixed abcd.2.1 t i) := by
      simp only [R,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have h0 : PP (IH uGstar) ((ContinuousLinearMap.comp (OL (Sum.inl (abcd.2.2.1,abcd.2.2.2))) (EH abcd.2.1 t)) v) - PP (IH u) ((ContinuousLinearMap.comp (OL (Sum.inl (abcd.2.2.1,abcd.2.2.2))) (EH abcd.2.1 t)) vG) =
        PP (IH u) ((ContinuousLinearMap.comp (BL i (Sum.inl (abcd.2.2.1,abcd.2.2.2))) (EH abcd.2.1 t) + ContinuousLinearMap.comp (OL (Sum.inl (abcd.2.2.1,abcd.2.2.2))) (CH mixed abcd.2.1 t i)) v) := by
      simpa only [t,ContinuousLinearMap.comp_apply,add_apply,sub_apply] using (hHE (Sum.inl (abcd.2.2.1,abcd.2.2.2)) abcd.2.1)
    exact scalar_word_graph_transport _ _ _ _ hA hC (IH uGstar) (IH u) v vG h0
  · have hA : O (Sum.inr (Sum.inl (Sum.inr abcd))) = ContinuousLinearMap.comp (EL abcd.1 t) (OH (Sum.inl (abcd.2.2.1,abcd.2.2.2))) := rfl
    have hC : R (Sum.inr (Sum.inl (Sum.inr abcd))) = ContinuousLinearMap.comp (CL mixed δ gen abcd.1 t i) (OH (Sum.inl (abcd.2.2.1,abcd.2.2.2))) + ContinuousLinearMap.comp (EL abcd.1 t) (BH i (Sum.inl (abcd.2.2.1,abcd.2.2.2))) := by
      simp only [R,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have h0 : PP (IH uGstar) ((ContinuousLinearMap.comp (EL abcd.1 t) (OH (Sum.inl (abcd.2.2.1,abcd.2.2.2)))) v) - PP (IH u) ((ContinuousLinearMap.comp (EL abcd.1 t) (OH (Sum.inl (abcd.2.2.1,abcd.2.2.2)))) vG) =
        PP (IH u) ((ContinuousLinearMap.comp (CL mixed δ gen abcd.1 t i) (OH (Sum.inl (abcd.2.2.1,abcd.2.2.2))) + ContinuousLinearMap.comp (EL abcd.1 t) (BH i (Sum.inl (abcd.2.2.1,abcd.2.2.2)))) v) := by
      simpa only [t,ContinuousLinearMap.comp_apply,add_apply,sub_apply] using (hEH abcd.1 (Sum.inl (abcd.2.2.1,abcd.2.2.2)))
    exact scalar_word_graph_transport _ _ _ _ hA hC (IH uGstar) (IH u) v vG h0
  · have hA : O (Sum.inr (Sum.inr (Sum.inl (Sum.inl ab)))) = ContinuousLinearMap.comp (OL (Sum.inr (Sum.inl ()))) (EH ab.2 t) := rfl
    have hC : R (Sum.inr (Sum.inr (Sum.inl (Sum.inl ab)))) = ContinuousLinearMap.comp (BL i (Sum.inr (Sum.inl ()))) (EH ab.2 t) + ContinuousLinearMap.comp (OL (Sum.inr (Sum.inl ()))) (CH mixed ab.2 t i) := by
      simp only [R,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have h0 : PP (IH uGstar) ((ContinuousLinearMap.comp (OL (Sum.inr (Sum.inl ()))) (EH ab.2 t)) v) - PP (IH u) ((ContinuousLinearMap.comp (OL (Sum.inr (Sum.inl ()))) (EH ab.2 t)) vG) =
        PP (IH u) ((ContinuousLinearMap.comp (BL i (Sum.inr (Sum.inl ()))) (EH ab.2 t) + ContinuousLinearMap.comp (OL (Sum.inr (Sum.inl ()))) (CH mixed ab.2 t i)) v) := by
      simpa only [t,ContinuousLinearMap.comp_apply,add_apply,sub_apply] using (hHE (Sum.inr (Sum.inl ())) ab.2)
    exact scalar_word_graph_transport _ _ _ _ hA hC (IH uGstar) (IH u) v vG h0
  · have hA : O (Sum.inr (Sum.inr (Sum.inl (Sum.inr ab)))) = ContinuousLinearMap.comp (EL ab.1 t) (OH (Sum.inr (Sum.inl ()))) := rfl
    have hC : R (Sum.inr (Sum.inr (Sum.inl (Sum.inr ab)))) = ContinuousLinearMap.comp (CL mixed δ gen ab.1 t i) (OH (Sum.inr (Sum.inl ()))) + ContinuousLinearMap.comp (EL ab.1 t) (BH i (Sum.inr (Sum.inl ()))) := by
      simp only [R,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have h0 : PP (IH uGstar) ((ContinuousLinearMap.comp (EL ab.1 t) (OH (Sum.inr (Sum.inl ())))) v) - PP (IH u) ((ContinuousLinearMap.comp (EL ab.1 t) (OH (Sum.inr (Sum.inl ())))) vG) =
        PP (IH u) ((ContinuousLinearMap.comp (CL mixed δ gen ab.1 t i) (OH (Sum.inr (Sum.inl ()))) + ContinuousLinearMap.comp (EL ab.1 t) (BH i (Sum.inr (Sum.inl ())))) v) := by
      simpa only [t,ContinuousLinearMap.comp_apply,add_apply,sub_apply] using (hEH ab.1 (Sum.inr (Sum.inl ())))
    exact scalar_word_graph_transport _ _ _ _ hA hC (IH uGstar) (IH u) v vG h0
  · have hA : O (Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inl ab))))) = ContinuousLinearMap.comp (OL (Sum.inr (Sum.inr ab.1))) (EH ab.2 t) := rfl
    have hC : R (Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inl ab))))) = ContinuousLinearMap.comp (BL i (Sum.inr (Sum.inr ab.1))) (EH ab.2 t) + ContinuousLinearMap.comp (OL (Sum.inr (Sum.inr ab.1))) (CH mixed ab.2 t i) := by
      simp only [R,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have h0 : PP (IH uGstar) ((ContinuousLinearMap.comp (OL (Sum.inr (Sum.inr ab.1))) (EH ab.2 t)) v) - PP (IH u) ((ContinuousLinearMap.comp (OL (Sum.inr (Sum.inr ab.1))) (EH ab.2 t)) vG) =
        PP (IH u) ((ContinuousLinearMap.comp (BL i (Sum.inr (Sum.inr ab.1))) (EH ab.2 t) + ContinuousLinearMap.comp (OL (Sum.inr (Sum.inr ab.1))) (CH mixed ab.2 t i)) v) := by
      simpa only [t,ContinuousLinearMap.comp_apply,add_apply,sub_apply] using (hHE (Sum.inr (Sum.inr ab.1)) ab.2)
    exact scalar_word_graph_transport _ _ _ _ hA hC (IH uGstar) (IH u) v vG h0
  · have hA : O (Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inr ab))))) = ContinuousLinearMap.comp (EL ab.1 t) (OH (Sum.inr (Sum.inr ab.2))) := rfl
    have hC : R (Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inr ab))))) = ContinuousLinearMap.comp (CL mixed δ gen ab.1 t i) (OH (Sum.inr (Sum.inr ab.2))) + ContinuousLinearMap.comp (EL ab.1 t) (BH i (Sum.inr (Sum.inr ab.2))) := by
      simp only [R,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have h0 : PP (IH uGstar) ((ContinuousLinearMap.comp (EL ab.1 t) (OH (Sum.inr (Sum.inr ab.2)))) v) - PP (IH u) ((ContinuousLinearMap.comp (EL ab.1 t) (OH (Sum.inr (Sum.inr ab.2)))) vG) =
        PP (IH u) ((ContinuousLinearMap.comp (CL mixed δ gen ab.1 t i) (OH (Sum.inr (Sum.inr ab.2))) + ContinuousLinearMap.comp (EL ab.1 t) (BH i (Sum.inr (Sum.inr ab.2)))) v) := by
      simpa only [t,ContinuousLinearMap.comp_apply,add_apply,sub_apply] using (hEH ab.1 (Sum.inr (Sum.inr ab.2)))
    exact scalar_word_graph_transport _ _ _ _ hA hC (IH uGstar) (IH u) v vG h0
  · have hA : O (Sum.inr (Sum.inr (Sum.inr (Sum.inr ab)))) = ContinuousLinearMap.comp (EL ab.1 t) (EH ab.2 t) := rfl
    have hC : R (Sum.inr (Sum.inr (Sum.inr (Sum.inr ab)))) = ContinuousLinearMap.comp (CL mixed δ gen ab.1 t i) (EH ab.2 t) + ContinuousLinearMap.comp (EL ab.1 t) (CH mixed ab.2 t i) := by
      simp only [R,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have h0 : PP (IH uGstar) ((ContinuousLinearMap.comp (EL ab.1 t) (EH ab.2 t)) v) - PP (IH u) ((ContinuousLinearMap.comp (EL ab.1 t) (EH ab.2 t)) vG) =
        PP (IH u) ((ContinuousLinearMap.comp (CL mixed δ gen ab.1 t i) (EH ab.2 t) + ContinuousLinearMap.comp (EL ab.1 t) (CH mixed ab.2 t i)) v) := by
      simpa only [t,ContinuousLinearMap.comp_apply,add_apply,sub_apply] using (hEE ab.1 ab.2)
    exact scalar_word_graph_transport _ _ _ _ hA hC (IH uGstar) (IH u) v vG h0


/-- True adjunction of every commutator word. Both sides keep physical E/e
intermediates in Half, including the differentiated ordinary E row. -/
private lemma zeroQTermWord_actual_adjoint
    (mixed : MRoom) (δ : ℝ) (gen : GRoom δ) (q dr Ar : ℝ) (p : ℕ) (x : R3)
    (htG : (Tq dr Ar p q) x ∈ ParamRoom δ)
    (htM : (Tq dr Ar p q) x ∈ ParamRoom mixed.δ)
    (hmem : ∀ᶠ y in 𝓝 x, (Tq dr Ar p q) y ∈ ParamRoom data.δ)
    (hDiff : ∀ j : Fin 3,
      DifferentiableAt ℝ (fun y => EH j ((Tq dr Ar p q) y)) x ∧
      DifferentiableAt ℝ (fun y => EL j ((Tq dr Ar p q) y)) x ∧
      DifferentiableAt ℝ (fun y => eH j ((Tq dr Ar p q) y)) x ∧
      DifferentiableAt ℝ (fun y => eL j ((Tq dr Ar p q) y)) x)
    (i : LowerCoreAngularGeneratorIndex) (u v : Hi) (z : ZeroQTermIndex) :
    PP (IH u) (zeroQTermWord g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data false mixed δ gen q dr Ar p x i z v) =
    PP (IH v) (zeroQTermWord g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data true mixed δ gen q dr Ar p x i z u) := by
  let t := (Tq dr Ar p q) x
  have htD : t ∈ ParamRoom data.δ := hmem.self_of_nhds
  have hE (j : Fin 3) := actualOrdinaryE_pivots
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data j t htD
  have hEF (j : Fin 3) := high_test_pairing_of_low (EL j t) (eL j t) (eH j t)
    (hE j).2.2 (hE j).2.1
  have hER (j : Fin 3) := high_test_reverse_pairing_of_low (EL j t) (eL j t) (EH j t)
    (hE j).2.2 (hE j).1
  have hGF := high_test_pairing_of_low (AGL i) (AGSL i) (AGSH i)
    (lowerSAngularLow_pairing hF hO hD i) (lowerSAngularSharpHigh_low_compatibility hF hO hD i)
  have hGR := high_test_reverse_pairing_of_low (AGL i) (AGSL i) (AGH i)
    (lowerSAngularLow_pairing hF hO hD i) (lowerSAngularHigh_low_compatibility hF hO hD i)
  have hOF (h : OrdinarySAngularIndex) := high_test_pairing_of_low (OL h) (OSL h) (OSH h)
    (ordinarySAngularLow_pairing hF hO hD h) (ordinarySAngularSharpHigh_low_compatibility hF hO hD h)
  have hOR (h : OrdinarySAngularIndex) := high_test_reverse_pairing_of_low (OL h) (OSL h) (OH h)
    (ordinarySAngularLow_pairing hF hO hD h) (ordinarySAngularHigh_low_compatibility hF hO hD h)
  have hCF (j : Fin 3) := lowerGeneratorEGain_low_pairing
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    mixed δ gen j t htG htM i
  have hCR (j : Fin 3) (aa : Hi) (bb : Half) :
      PP (IH aa) (CSL mixed δ gen j t i bb) = PP bb (JL (CH mixed j t i aa)) :=
    (lowerGeneratorEGain_sharp_low_pairing
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      mixed δ gen j t htG htM i aa bb).trans (v016_pairing_inclusion_symm _ _)
  have hBR (h : OrdinarySAngularIndex) (a : Hi) (b : Half) :
      PP (IH a) (BSL i h b) = PP b (JL (BH i h a)) :=
    (lowerSAngularBracketSharpLow_pairing hF hO hD i h a b).trans
      (v016_pairing_inclusion_symm _ _)
  have hSingle (j : Fin 3) :
      PP (IH u) (JL (CH mixed j t i v)) = PP (IH v) (JL (CSH j t i u)) := by
    calc
      _ = PP (IH u) (CL mixed δ gen j t i (IH v)) := congrArg (PP (IH u))
        (lowerGeneratorEGain_high_low_compatibility
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
          mixed δ gen j t htG htM i v).symm
      _ = PP (CSH j t i u) (JL (IH v)) := hCF j u (IH v)
      _ = _ := v016_pairing_inclusion_symm _ _
  have hHE (h : OrdinarySAngularIndex) (j : Fin 3) :
      PP (IH u) (BL i h (EH j t v)+OL h (CH mixed j t i v)) =
      PP (IH v) (eL j t (BSH i h u)+CSL mixed δ gen j t i (OSH h u)) := by
    have h1 := weak_product_actual_adjoint (BL i h) (BSH i h) (EH j t) (eL j t)
      (lowerSAngularBracketLow_pairing hF hO hD i h) (hER j) u v
    have h2 := weak_product_actual_adjoint (OL h) (OSH h) (CH mixed j t i) (CSL mixed δ gen j t i)
      (hOF h) (hCR j) u v
    exact (pp_add_right (IH u) _ _).trans
      ((congrArg₂ (fun a b : ℝ => a+b) h1 h2).trans (pp_add_right (IH v) _ _).symm)
  have hEH (j : Fin 3) (h : OrdinarySAngularIndex) :
      PP (IH u) (CL mixed δ gen j t i (OH h v)+EL j t (BH i h v)) =
      PP (IH v) (OSL h (CSH j t i u)+BSL i h (eH j t u)) := by
    have h1 := weak_product_actual_adjoint (CL mixed δ gen j t i) (CSH j t i) (OH h) (OSL h)
      (hCF j) (hOR h) u v
    have h2 := weak_product_actual_adjoint (EL j t) (eH j t) (BH i h) (BSL i h)
      (hEF j) (hBR h) u v
    exact (pp_add_right (IH u) _ _).trans
      ((congrArg₂ (fun a b : ℝ => a+b) h1 h2).trans (pp_add_right (IH v) _ _).symm)
  have hEE (a b : Fin 3) :
      PP (IH u) (CL mixed δ gen a t i (EH b t v)+EL a t (CH mixed b t i v)) =
      PP (IH v) (eL b t (CSH a t i u)+CSL mixed δ gen b t i (eH a t u)) := by
    have h1 := weak_product_actual_adjoint (CL mixed δ gen a t i) (CSH a t i) (EH b t) (eL b t)
      (hCF a) (hER b) u v
    have h2 := weak_product_actual_adjoint (EL a t) (eH a t) (CH mixed b t i) (CSL mixed δ gen b t i)
      (hEF a) (hCR b) u v
    exact (pp_add_right (IH u) _ _).trans
      ((congrArg₂ (fun a b : ℝ => a+b) h1 h2).trans (pp_add_right (IH v) _ _).symm)
  have hDE (j : Fin 3) (X : R3) :
      PP (IH u) ((AGL i) ((fderiv ℝ (fun y => EH j ((Tq dr Ar p q) y)) x X) v)-
        (fderiv ℝ (fun y => EL j ((Tq dr Ar p q) y)) x X) ((AGH i) v)) =
      PP (IH v) ((fderiv ℝ (fun y => eL j ((Tq dr Ar p q) y)) x X) (AGSH i u)-
        AGSL i ((fderiv ℝ (fun y => eH j ((Tq dr Ar p q) y)) x X) u)) := by
    have hd := actualOrdinaryE_derivative_pivots
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      q dr Ar p x X j hmem (hDiff j).1 (hDiff j).2.1 (hDiff j).2.2.1 (hDiff j).2.2.2
    have hDF := high_test_pairing_of_low
      (fderiv ℝ (fun y => EL j ((Tq dr Ar p q) y)) x X)
      (fderiv ℝ (fun y => eL j ((Tq dr Ar p q) y)) x X)
      (fderiv ℝ (fun y => eH j ((Tq dr Ar p q) y)) x X) hd.2.2 hd.2.1
    have hDR := high_test_reverse_pairing_of_low
      (fderiv ℝ (fun y => EL j ((Tq dr Ar p q) y)) x X)
      (fderiv ℝ (fun y => eL j ((Tq dr Ar p q) y)) x X)
      (fderiv ℝ (fun y => EH j ((Tq dr Ar p q) y)) x X) hd.2.2 hd.1
    have h1 := weak_product_actual_adjoint (AGL i) (AGSH i)
      (fderiv ℝ (fun y => EH j ((Tq dr Ar p q) y)) x X)
      (fderiv ℝ (fun y => eL j ((Tq dr Ar p q) y)) x X) hGF hDR u v
    have h2 := weak_product_actual_adjoint
      (fderiv ℝ (fun y => EL j ((Tq dr Ar p q) y)) x X)
      (fderiv ℝ (fun y => eH j ((Tq dr Ar p q) y)) x X)
      (AGH i) (AGSL i) hDF hGR u v
    exact (pp_sub_right (IH u) _ _).trans
      ((congrArg₂ (fun a b : ℝ => a-b) h1 h2).trans (pp_sub_right (IH v) _ _).symm)
  let R := zeroQTermWord
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    false mixed δ gen q dr Ar p x i
  let S := zeroQTermWord
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    true mixed δ gen q dr Ar p x i
  rcases z with (ab | (ab | (abk | ja))) | ((abcd | abcd) | ((ab | ab) | ((ab | ab) | ab)))
  · have hC : R (Sum.inl (Sum.inl ab)) = ContinuousLinearMap.comp (AGL i) ((fderiv ℝ (fun y => EH ab.2 ((Tq dr Ar p q) y)) x (referenceMetricGramFrame g L (q,x) ab.1))) - ContinuousLinearMap.comp ((fderiv ℝ (fun y => EL ab.2 ((Tq dr Ar p q) y)) x (referenceMetricGramFrame g L (q,x) ab.1))) (AGH i) := by
      simp only [R,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have hS : S (Sum.inl (Sum.inl ab)) = ContinuousLinearMap.comp ((fderiv ℝ (fun y => eL ab.2 ((Tq dr Ar p q) y)) x (referenceMetricGramFrame g L (q,x) ab.1))) (AGSH i) - ContinuousLinearMap.comp (AGSL i) ((fderiv ℝ (fun y => eH ab.2 ((Tq dr Ar p q) y)) x (referenceMetricGramFrame g L (q,x) ab.1))) := by
      simp only [S,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have h0 : PP (IH u) ((ContinuousLinearMap.comp (AGL i) ((fderiv ℝ (fun y => EH ab.2 ((Tq dr Ar p q) y)) x (referenceMetricGramFrame g L (q,x) ab.1))) - ContinuousLinearMap.comp ((fderiv ℝ (fun y => EL ab.2 ((Tq dr Ar p q) y)) x (referenceMetricGramFrame g L (q,x) ab.1))) (AGH i)) v) = PP (IH v) ((ContinuousLinearMap.comp ((fderiv ℝ (fun y => eL ab.2 ((Tq dr Ar p q) y)) x (referenceMetricGramFrame g L (q,x) ab.1))) (AGSH i) - ContinuousLinearMap.comp (AGSL i) ((fderiv ℝ (fun y => eH ab.2 ((Tq dr Ar p q) y)) x (referenceMetricGramFrame g L (q,x) ab.1)))) u) := by
      simpa only [t,ContinuousLinearMap.comp_apply,add_apply,sub_apply] using (hDE ab.2 (referenceMetricGramFrame g L (q,x) ab.1))
    exact scalar_word_adjoint_transport _ _ _ _ hC hS (IH u) (IH v) u v h0
  · have hC : R (Sum.inl (Sum.inr (Sum.inl ab))) = ContinuousLinearMap.comp (JL) (CH mixed ab.2 t i) := by
      simp only [R,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have hS : S (Sum.inl (Sum.inr (Sum.inl ab))) = ContinuousLinearMap.comp (JL) (CSH ab.2 t i) := by
      simp only [S,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have h0 : PP (IH u) ((ContinuousLinearMap.comp (JL) (CH mixed ab.2 t i)) v) = PP (IH v) ((ContinuousLinearMap.comp (JL) (CSH ab.2 t i)) u) := by
      simpa only [t,ContinuousLinearMap.comp_apply,add_apply,sub_apply] using (hSingle ab.2)
    exact scalar_word_adjoint_transport _ _ _ _ hC hS (IH u) (IH v) u v h0
  · have hC : R (Sum.inl (Sum.inr (Sum.inr (Sum.inl abk)))) = ContinuousLinearMap.comp (JL) (CH mixed abk.2.2 t i) := by
      simp only [R,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have hS : S (Sum.inl (Sum.inr (Sum.inr (Sum.inl abk)))) = ContinuousLinearMap.comp (JL) (CSH abk.2.2 t i) := by
      simp only [S,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have h0 : PP (IH u) ((ContinuousLinearMap.comp (JL) (CH mixed abk.2.2 t i)) v) = PP (IH v) ((ContinuousLinearMap.comp (JL) (CSH abk.2.2 t i)) u) := by
      simpa only [t,ContinuousLinearMap.comp_apply,add_apply,sub_apply] using (hSingle abk.2.2)
    exact scalar_word_adjoint_transport _ _ _ _ hC hS (IH u) (IH v) u v h0
  · have hC : R (Sum.inl (Sum.inr (Sum.inr (Sum.inr ja)))) = ContinuousLinearMap.comp (JL) (CH mixed ja t i) := by
      simp only [R,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have hS : S (Sum.inl (Sum.inr (Sum.inr (Sum.inr ja)))) = ContinuousLinearMap.comp (JL) (CSH ja t i) := by
      simp only [S,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have h0 : PP (IH u) ((ContinuousLinearMap.comp (JL) (CH mixed ja t i)) v) = PP (IH v) ((ContinuousLinearMap.comp (JL) (CSH ja t i)) u) := by
      simpa only [t,ContinuousLinearMap.comp_apply,add_apply,sub_apply] using (hSingle ja)
    exact scalar_word_adjoint_transport _ _ _ _ hC hS (IH u) (IH v) u v h0
  · have hC : R (Sum.inr (Sum.inl (Sum.inl abcd))) = ContinuousLinearMap.comp (BL i (Sum.inl (abcd.2.2.1,abcd.2.2.2))) (EH abcd.2.1 t) + ContinuousLinearMap.comp (OL (Sum.inl (abcd.2.2.1,abcd.2.2.2))) (CH mixed abcd.2.1 t i) := by
      simp only [R,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have hS : S (Sum.inr (Sum.inl (Sum.inl abcd))) = ContinuousLinearMap.comp (eL abcd.2.1 t) (BSH i (Sum.inl (abcd.2.2.1,abcd.2.2.2))) + ContinuousLinearMap.comp (CSL mixed δ gen abcd.2.1 t i) (OSH (Sum.inl (abcd.2.2.1,abcd.2.2.2))) := by
      simp only [S,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have h0 : PP (IH u) ((ContinuousLinearMap.comp (BL i (Sum.inl (abcd.2.2.1,abcd.2.2.2))) (EH abcd.2.1 t) + ContinuousLinearMap.comp (OL (Sum.inl (abcd.2.2.1,abcd.2.2.2))) (CH mixed abcd.2.1 t i)) v) = PP (IH v) ((ContinuousLinearMap.comp (eL abcd.2.1 t) (BSH i (Sum.inl (abcd.2.2.1,abcd.2.2.2))) + ContinuousLinearMap.comp (CSL mixed δ gen abcd.2.1 t i) (OSH (Sum.inl (abcd.2.2.1,abcd.2.2.2)))) u) := by
      simpa only [t,ContinuousLinearMap.comp_apply,add_apply,sub_apply] using (hHE (Sum.inl (abcd.2.2.1,abcd.2.2.2)) abcd.2.1)
    exact scalar_word_adjoint_transport _ _ _ _ hC hS (IH u) (IH v) u v h0
  · have hC : R (Sum.inr (Sum.inl (Sum.inr abcd))) = ContinuousLinearMap.comp (CL mixed δ gen abcd.1 t i) (OH (Sum.inl (abcd.2.2.1,abcd.2.2.2))) + ContinuousLinearMap.comp (EL abcd.1 t) (BH i (Sum.inl (abcd.2.2.1,abcd.2.2.2))) := by
      simp only [R,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have hS : S (Sum.inr (Sum.inl (Sum.inr abcd))) = ContinuousLinearMap.comp (OSL (Sum.inl (abcd.2.2.1,abcd.2.2.2))) (CSH abcd.1 t i) + ContinuousLinearMap.comp (BSL i (Sum.inl (abcd.2.2.1,abcd.2.2.2))) (eH abcd.1 t) := by
      simp only [S,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have h0 : PP (IH u) ((ContinuousLinearMap.comp (CL mixed δ gen abcd.1 t i) (OH (Sum.inl (abcd.2.2.1,abcd.2.2.2))) + ContinuousLinearMap.comp (EL abcd.1 t) (BH i (Sum.inl (abcd.2.2.1,abcd.2.2.2)))) v) = PP (IH v) ((ContinuousLinearMap.comp (OSL (Sum.inl (abcd.2.2.1,abcd.2.2.2))) (CSH abcd.1 t i) + ContinuousLinearMap.comp (BSL i (Sum.inl (abcd.2.2.1,abcd.2.2.2))) (eH abcd.1 t)) u) := by
      simpa only [t,ContinuousLinearMap.comp_apply,add_apply,sub_apply] using (hEH abcd.1 (Sum.inl (abcd.2.2.1,abcd.2.2.2)))
    exact scalar_word_adjoint_transport _ _ _ _ hC hS (IH u) (IH v) u v h0
  · have hC : R (Sum.inr (Sum.inr (Sum.inl (Sum.inl ab)))) = ContinuousLinearMap.comp (BL i (Sum.inr (Sum.inl ()))) (EH ab.2 t) + ContinuousLinearMap.comp (OL (Sum.inr (Sum.inl ()))) (CH mixed ab.2 t i) := by
      simp only [R,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have hS : S (Sum.inr (Sum.inr (Sum.inl (Sum.inl ab)))) = ContinuousLinearMap.comp (eL ab.2 t) (BSH i (Sum.inr (Sum.inl ()))) + ContinuousLinearMap.comp (CSL mixed δ gen ab.2 t i) (OSH (Sum.inr (Sum.inl ()))) := by
      simp only [S,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have h0 : PP (IH u) ((ContinuousLinearMap.comp (BL i (Sum.inr (Sum.inl ()))) (EH ab.2 t) + ContinuousLinearMap.comp (OL (Sum.inr (Sum.inl ()))) (CH mixed ab.2 t i)) v) = PP (IH v) ((ContinuousLinearMap.comp (eL ab.2 t) (BSH i (Sum.inr (Sum.inl ()))) + ContinuousLinearMap.comp (CSL mixed δ gen ab.2 t i) (OSH (Sum.inr (Sum.inl ())))) u) := by
      simpa only [t,ContinuousLinearMap.comp_apply,add_apply,sub_apply] using (hHE (Sum.inr (Sum.inl ())) ab.2)
    exact scalar_word_adjoint_transport _ _ _ _ hC hS (IH u) (IH v) u v h0
  · have hC : R (Sum.inr (Sum.inr (Sum.inl (Sum.inr ab)))) = ContinuousLinearMap.comp (CL mixed δ gen ab.1 t i) (OH (Sum.inr (Sum.inl ()))) + ContinuousLinearMap.comp (EL ab.1 t) (BH i (Sum.inr (Sum.inl ()))) := by
      simp only [R,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have hS : S (Sum.inr (Sum.inr (Sum.inl (Sum.inr ab)))) = ContinuousLinearMap.comp (OSL (Sum.inr (Sum.inl ()))) (CSH ab.1 t i) + ContinuousLinearMap.comp (BSL i (Sum.inr (Sum.inl ()))) (eH ab.1 t) := by
      simp only [S,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have h0 : PP (IH u) ((ContinuousLinearMap.comp (CL mixed δ gen ab.1 t i) (OH (Sum.inr (Sum.inl ()))) + ContinuousLinearMap.comp (EL ab.1 t) (BH i (Sum.inr (Sum.inl ())))) v) = PP (IH v) ((ContinuousLinearMap.comp (OSL (Sum.inr (Sum.inl ()))) (CSH ab.1 t i) + ContinuousLinearMap.comp (BSL i (Sum.inr (Sum.inl ()))) (eH ab.1 t)) u) := by
      simpa only [t,ContinuousLinearMap.comp_apply,add_apply,sub_apply] using (hEH ab.1 (Sum.inr (Sum.inl ())))
    exact scalar_word_adjoint_transport _ _ _ _ hC hS (IH u) (IH v) u v h0
  · have hC : R (Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inl ab))))) = ContinuousLinearMap.comp (BL i (Sum.inr (Sum.inr ab.1))) (EH ab.2 t) + ContinuousLinearMap.comp (OL (Sum.inr (Sum.inr ab.1))) (CH mixed ab.2 t i) := by
      simp only [R,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have hS : S (Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inl ab))))) = ContinuousLinearMap.comp (eL ab.2 t) (BSH i (Sum.inr (Sum.inr ab.1))) + ContinuousLinearMap.comp (CSL mixed δ gen ab.2 t i) (OSH (Sum.inr (Sum.inr ab.1))) := by
      simp only [S,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have h0 : PP (IH u) ((ContinuousLinearMap.comp (BL i (Sum.inr (Sum.inr ab.1))) (EH ab.2 t) + ContinuousLinearMap.comp (OL (Sum.inr (Sum.inr ab.1))) (CH mixed ab.2 t i)) v) = PP (IH v) ((ContinuousLinearMap.comp (eL ab.2 t) (BSH i (Sum.inr (Sum.inr ab.1))) + ContinuousLinearMap.comp (CSL mixed δ gen ab.2 t i) (OSH (Sum.inr (Sum.inr ab.1)))) u) := by
      simpa only [t,ContinuousLinearMap.comp_apply,add_apply,sub_apply] using (hHE (Sum.inr (Sum.inr ab.1)) ab.2)
    exact scalar_word_adjoint_transport _ _ _ _ hC hS (IH u) (IH v) u v h0
  · have hC : R (Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inr ab))))) = ContinuousLinearMap.comp (CL mixed δ gen ab.1 t i) (OH (Sum.inr (Sum.inr ab.2))) + ContinuousLinearMap.comp (EL ab.1 t) (BH i (Sum.inr (Sum.inr ab.2))) := by
      simp only [R,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have hS : S (Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inr ab))))) = ContinuousLinearMap.comp (OSL (Sum.inr (Sum.inr ab.2))) (CSH ab.1 t i) + ContinuousLinearMap.comp (BSL i (Sum.inr (Sum.inr ab.2))) (eH ab.1 t) := by
      simp only [S,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have h0 : PP (IH u) ((ContinuousLinearMap.comp (CL mixed δ gen ab.1 t i) (OH (Sum.inr (Sum.inr ab.2))) + ContinuousLinearMap.comp (EL ab.1 t) (BH i (Sum.inr (Sum.inr ab.2)))) v) = PP (IH v) ((ContinuousLinearMap.comp (OSL (Sum.inr (Sum.inr ab.2))) (CSH ab.1 t i) + ContinuousLinearMap.comp (BSL i (Sum.inr (Sum.inr ab.2))) (eH ab.1 t)) u) := by
      simpa only [t,ContinuousLinearMap.comp_apply,add_apply,sub_apply] using (hEH ab.1 (Sum.inr (Sum.inr ab.2)))
    exact scalar_word_adjoint_transport _ _ _ _ hC hS (IH u) (IH v) u v h0
  · have hC : R (Sum.inr (Sum.inr (Sum.inr (Sum.inr ab)))) = ContinuousLinearMap.comp (CL mixed δ gen ab.1 t i) (EH ab.2 t) + ContinuousLinearMap.comp (EL ab.1 t) (CH mixed ab.2 t i) := by
      simp only [R,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have hS : S (Sum.inr (Sum.inr (Sum.inr (Sum.inr ab)))) = ContinuousLinearMap.comp (eL ab.2 t) (CSH ab.1 t i) + ContinuousLinearMap.comp (CSL mixed δ gen ab.2 t i) (eH ab.1 t) := by
      simp only [S,t,zeroQTermWord,generatorDerivativeEWord,generatorESingleWord,
      generatorOrdinaryEWord,generatorEOrdinaryWord,generatorDoubleEWord,
      Bool.false_eq_true,ite_false,ite_true]
    have h0 : PP (IH u) ((ContinuousLinearMap.comp (CL mixed δ gen ab.1 t i) (EH ab.2 t) + ContinuousLinearMap.comp (EL ab.1 t) (CH mixed ab.2 t i)) v) = PP (IH v) ((ContinuousLinearMap.comp (eL ab.2 t) (CSH ab.1 t i) + ContinuousLinearMap.comp (CSL mixed δ gen ab.2 t i) (eH ab.1 t)) u) := by
      simpa only [t,ContinuousLinearMap.comp_apply,add_apply,sub_apply] using (hEE ab.1 ab.2)
    exact scalar_word_adjoint_transport _ _ _ _ hC hS (IH u) (IH v) u v h0


private structure QDictionaryRow (V : Type*) where
  r : ℝ
  Q : Fin 3 → Fin 3 → ℝ
  b : Fin 3 → ℝ
  f : Fin 3 → ℝ
  gamma : Fin 3 → Fin 3 → Fin 3 → ℝ
  e : Fin 3 → V
  de : Fin 3 → Fin 3 → V
  rotE : Fin 3 → Fin 3 → Fin 3 → V
  erot : Fin 3 → Fin 3 → Fin 3 → V
  ne : Fin 3 → V
  en : Fin 3 → V
  ae : Fin 3 → Fin 3 → V
  ea : Fin 3 → Fin 3 → V
  ee : Fin 3 → Fin 3 → V

private def qDictionaryScalar {V : Type*} (d : QDictionaryRow V) : ZeroQTermIndex → ℝ
  | Sum.inl (Sum.inl ab) => d.r^2*d.Q ab.1 ab.2
  | Sum.inl (Sum.inr (Sum.inl ab)) => d.r^2*d.Q ab.1 ab.2*d.f ab.1
  | Sum.inl (Sum.inr (Sum.inr (Sum.inl abk))) => -d.r^2*d.Q abk.1 abk.2.1*d.gamma abk.1 abk.2.2 abk.2.1
  | Sum.inl (Sum.inr (Sum.inr (Sum.inr a))) => d.r^2*d.b a
  | Sum.inr (Sum.inl (Sum.inl abcd)) => d.r^2*d.Q abcd.1 abcd.2.1*(1/2 : ℝ)*d.gamma abcd.1 abcd.2.2.1 abcd.2.2.2
  | Sum.inr (Sum.inl (Sum.inr abcd)) => d.r^2*d.Q abcd.1 abcd.2.1*(1/2 : ℝ)*d.gamma abcd.2.1 abcd.2.2.1 abcd.2.2.2
  | Sum.inr (Sum.inr (Sum.inl (Sum.inl ab))) => d.r^2*d.Q ab.1 ab.2*d.f ab.1
  | Sum.inr (Sum.inr (Sum.inl (Sum.inr ab))) => d.r^2*d.Q ab.1 ab.2*d.f ab.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inl ab)))) => d.r*d.Q ab.1 ab.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inr ab)))) => d.r*d.Q ab.1 ab.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr ab))) => d.r^3*d.Q ab.1 ab.2

private def qDictionaryVector {V : Type*} (d : QDictionaryRow V) : ZeroQTermIndex → V
  | Sum.inl (Sum.inl ab) => d.de ab.1 ab.2
  | Sum.inl (Sum.inr (Sum.inl ab)) => d.e ab.2
  | Sum.inl (Sum.inr (Sum.inr (Sum.inl abk))) => d.e abk.2.2
  | Sum.inl (Sum.inr (Sum.inr (Sum.inr a))) => d.e a
  | Sum.inr (Sum.inl (Sum.inl abcd)) => d.rotE abcd.2.1 abcd.2.2.1 abcd.2.2.2
  | Sum.inr (Sum.inl (Sum.inr abcd)) => d.erot abcd.1 abcd.2.2.1 abcd.2.2.2
  | Sum.inr (Sum.inr (Sum.inl (Sum.inl ab))) => d.ne ab.2
  | Sum.inr (Sum.inr (Sum.inl (Sum.inr ab))) => d.en ab.1
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inl ab)))) => d.ae ab.1 ab.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inr ab)))) => d.ea ab.1 ab.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr ab))) => d.ee ab.1 ab.2

private def qGroupedVector {V : Type*} [AddCommGroup V] [Module ℝ V]
    (d : QDictionaryRow V) : V :=
  (d.r^2 • (∑ i : Fin 3, ∑ j : Fin 3, d.Q i j •
    (d.de i j+d.f i • d.e j-∑ k : Fin 3, d.gamma i k j • d.e k))+
    d.r^2 • (∑ i : Fin 3, d.b i • d.e i))+
  d.r^2 • (∑ i : Fin 3, ∑ j : Fin 3, d.Q i j •
    ((1/2 : ℝ) • (∑ c : Fin 3, ∑ k : Fin 3, d.gamma i c k • d.rotE j c k)+
      (1/2 : ℝ) • (∑ c : Fin 3, ∑ k : Fin 3, d.gamma j c k • d.erot i c k)))+
  d.r^2 • (∑ i : Fin 3, ∑ j : Fin 3, d.Q i j •
    (d.f i • d.ne j+d.f j • d.en i))+
  d.r • (∑ i : Fin 3, ∑ j : Fin 3, d.Q i j • (d.ae i j+d.ea i j))+
  d.r^3 • (∑ i : Fin 3, ∑ j : Fin 3, d.Q i j • d.ee i j)

private theorem qGroupedVector_eq_dictionary {V : Type*} [AddCommGroup V] [Module ℝ V]
    (d : QDictionaryRow V) :
    qGroupedVector d = ∑ z : ZeroQTermIndex, qDictionaryScalar d z • qDictionaryVector d z := by
  simp only [qGroupedVector,qDictionaryScalar,qDictionaryVector,
    ZeroQTermIndex,ZeroQLinearIndex,ZeroQQuadraticIndex,ZeroQPair,ZeroQTriple,ZeroQQuad,
    Fintype.sum_sum_type,Fintype.sum_prod_type,
    smul_add,smul_sub,Finset.smul_sum,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    smul_smul,mul_assoc,neg_mul,neg_smul,Finset.sum_neg_distrib]
  module

private def actualQDictionaryRow (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ)
    (x : R3) (u : Hi) : QDictionaryRow Neg where
  r := referenceRadius dr Ar p L x
  Q := referenceDensityPrincipalFrameCoefficient g g2 L q x
  b := fun i => normalizedSecondDriftFrameJoint g g2 L i (q,x)
  f := referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x
  gamma := fun i c k => referenceFrameConnectionCoefficient g L q x
    (referenceMetricGramFrame g L (q,x) i) c k
  e := fun j => JL (EH j ((Tq dr Ar p q) x) u)
  de := fun i j => JL ((fderiv ℝ (fun y => EH j ((Tq dr Ar p q) y)) x
    (referenceMetricGramFrame g L (q,x) i)) u)
  rotE := fun j c k => OL (Sum.inl (c,k)) (EH j ((Tq dr Ar p q) x) u)
  erot := fun i c k => EL i ((Tq dr Ar p q) x) (OH (Sum.inl (c,k)) u)
  ne := fun j => OL (Sum.inr (Sum.inl ())) (EH j ((Tq dr Ar p q) x) u)
  en := fun i => EL i ((Tq dr Ar p q) x) (OH (Sum.inr (Sum.inl ())) u)
  ae := fun i j => OL (Sum.inr (Sum.inr i)) (EH j ((Tq dr Ar p q) x) u)
  ea := fun i j => EL i ((Tq dr Ar p q) x) (OH (Sum.inr (Sum.inr j)) u)
  ee := fun i j => EL i ((Tq dr Ar p q) x) (EH j ((Tq dr Ar p q) x) u)

private theorem actualFiveGroups_eq_qGroupedVector
    (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ) (x : R3) (u : Hi) :
    (ActualLowerUSZeroSDecomposition.lowerSZeroLinearGroup
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x+
    ActualLowerUSZeroSDecomposition.lowerSZeroConnectionGroup
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x+
    ActualLowerUSZeroSDecomposition.lowerSZeroDegreeGroup
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x+
    ActualLowerUSZeroSDecomposition.lowerSZeroAngularGroup
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x+
    ActualLowerUSZeroSDecomposition.lowerSZeroDoubleGroup
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x) u =
    qGroupedVector (actualQDictionaryRow
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q dr Ar p x u) := by
  have hOL (i : Fin 3) : referenceLowerHorizontalAngularL g L q x i =
      (1/2 : ℝ) • ∑ c : Fin 3, ∑ k : Fin 3,
        referenceFrameConnectionCoefficient g L q x
          (referenceMetricGramFrame g L (q,x) i) c k • OL (Sum.inl (c,k)) := rfl
  have hOH (i : Fin 3) : referenceHighHorizontalAngularL g L q x i =
      (1/2 : ℝ) • ∑ c : Fin 3, ∑ k : Fin 3,
        referenceFrameConnectionCoefficient g L q x
          (referenceMetricGramFrame g L (q,x) i) c k • OH (Sum.inl (c,k)) := rfl
  have hNL : sphereSobolevShiftedDegreeL (1/2 : ℝ) = OL (Sum.inr (Sum.inl ())) := rfl
  have hNH : sphereSobolevShiftedDegreeL (3/2 : ℝ) = OH (Sum.inr (Sum.inl ())) := rfl
  have hAL (i : Fin 3) : sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i =
      OL (Sum.inr (Sum.inr i)) := rfl
  have hAH (i : Fin 3) : sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i =
      OH (Sum.inr (Sum.inr i)) := rfl
  simp only [ActualLowerUSZeroSDecomposition.lowerSZeroLinearGroup,
    ActualLowerUSZeroSDecomposition.lowerSZeroConnectionGroup,
    ActualLowerUSZeroSDecomposition.lowerSZeroDegreeGroup,
    ActualLowerUSZeroSDecomposition.lowerSZeroAngularGroup,
    ActualLowerUSZeroSDecomposition.lowerSZeroDoubleGroup,
    hOL,hOH,hNL,hNH,hAL,hAH,qGroupedVector,actualQDictionaryRow,
    add_apply,sub_apply,smul_apply,sum_apply,ContinuousLinearMap.comp_apply,
    map_smul,map_sum]

private theorem actualDictionary_eq_qDictionary
    (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ) (x : R3) (u : Hi) :
    (∑ z : ZeroQTermIndex, zeroQTermScalar g L g2 q dr Ar p x z •
      zeroQOriginalTermWord g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        q dr Ar p x z) u =
    ∑ z : ZeroQTermIndex,
      qDictionaryScalar (actualQDictionaryRow
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q dr Ar p x u) z •
      qDictionaryVector (actualQDictionaryRow
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q dr Ar p x u) z := by
  simp only [sum_apply,smul_apply]
  apply Finset.sum_congr rfl
  intro z _
  rcases z with (ab | (ab | (abk | a))) | ((abcd | abcd) | ((ab | ab) | ((ab | ab) | ab))) <;> rfl

private theorem canonicalZeroCoefficient_eq_zeroQOriginalTerms
    (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ) (x : R3) :
    ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x =
      ∑ z : ZeroQTermIndex, zeroQTermScalar g L g2 q dr Ar p x z •
        zeroQOriginalTermWord g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          q dr Ar p x z := by
  apply ContinuousLinearMap.ext
  intro u
  have h := congrArg (fun A : Hi →L[ℝ] Neg => A u)
    (ActualLowerUSZeroSDecomposition.canonicalZeroCoefficient_eq_lower_groups
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x)
  exact h.trans ((actualFiveGroups_eq_qGroupedVector
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q dr Ar p x u).trans
      ((qGroupedVector_eq_dictionary _).trans (actualDictionary_eq_qDictionary
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q dr Ar p x u).symm))
private lemma pp_sum_smul {ι : Type*} [Fintype ι]
    (a : Half) (c : ι → ℝ) (f : ι → Neg) :
    PP a (∑ i : ι, c i • f i) = ∑ i : ι, c i * PP a (f i) := by
  simp only [sphereSobolevDualPairing,inner_sum,real_inner_smul_right]

private lemma weighted_word_forward_graph {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (A R : ι → Hi →L[ℝ] Neg) (a b : Half) (v vG : Hi)
    (h : ∀ i, PP a (A i v)-PP b (A i vG) = PP b (R i v)) :
    PP a ((∑ i : ι, c i • A i) v)-PP b ((∑ i : ι, c i • A i) vG) =
      PP b ((∑ i : ι, c i • R i) v) := by
  simp only [sum_apply,smul_apply,pp_sum_smul,← Finset.sum_sub_distrib,← mul_sub]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun z : ℝ => c i*z) (h i)

private lemma weighted_word_adjoint_graph {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (R S : ι → Hi →L[ℝ] Neg) (a b : Half) (u v : Hi)
    (h : ∀ i, PP a (R i v) = PP b (S i u)) :
    PP a ((∑ i : ι, c i • R i) v) = PP b ((∑ i : ι, c i • S i) u) := by
  simp only [sum_apply,smul_apply,pp_sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun z : ℝ => c i*z) (h i)

private lemma actual_coefficient_forward_sum
    (mixed : MRoom) (δ : ℝ) (gen : GRoom δ) (g2 : MatrixField)
    (q dr Ar : ℝ) (p : ℕ) (x : R3) (i : LowerCoreAngularGeneratorIndex)
    (a0 b0 : Half) (v vG : Hi)
    (hWord : ∀ z : ZeroQTermIndex,
      PP a0 (zeroQOriginalTermWord
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q dr Ar p x z v) -
      PP b0 (zeroQOriginalTermWord
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q dr Ar p x z vG) =
      PP b0 (zeroQTermWord
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        false mixed δ gen q dr Ar p x i z v)) :
    PP a0 (ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x v) -
    PP b0 (ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x vG) =
    PP b0 (lowerGeneratorZeroCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      false mixed δ gen g2 q dr Ar p x i v) := by
  let c := zeroQTermScalar g L g2 q dr Ar p x
  let A := zeroQOriginalTermWord
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q dr Ar p x
  let R := zeroQTermWord
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    false mixed δ gen q dr Ar p x i
  have hA : ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x =
      ∑ z : ZeroQTermIndex, c z • A z :=
    canonicalZeroCoefficient_eq_zeroQOriginalTerms
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q dr Ar p x
  have hR : lowerGeneratorZeroCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      false mixed δ gen g2 q dr Ar p x i = ∑ z : ZeroQTermIndex, c z • R z := rfl
  exact scalar_word_graph_transport _ _ _ _ hA hR a0 b0 v vG
    (weighted_word_forward_graph c A R a0 b0 v vG hWord)

private lemma actual_coefficient_adjoint_sum
    (mixed : MRoom) (δ : ℝ) (gen : GRoom δ) (g2 : MatrixField)
    (q dr Ar : ℝ) (p : ℕ) (x : R3) (i : LowerCoreAngularGeneratorIndex)
    (a0 b0 : Half) (u v : Hi)
    (hWord : ∀ z : ZeroQTermIndex,
      PP a0 (zeroQTermWord
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        false mixed δ gen q dr Ar p x i z v) =
      PP b0 (zeroQTermWord
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        true mixed δ gen q dr Ar p x i z u)) :
    PP a0 (lowerGeneratorZeroCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      false mixed δ gen g2 q dr Ar p x i v) =
    PP b0 (lowerGeneratorZeroCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      true mixed δ gen g2 q dr Ar p x i u) := by
  let c := zeroQTermScalar g L g2 q dr Ar p x
  let R := zeroQTermWord
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    false mixed δ gen q dr Ar p x i
  let S := zeroQTermWord
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    true mixed δ gen q dr Ar p x i
  have hR : lowerGeneratorZeroCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      false mixed δ gen g2 q dr Ar p x i = ∑ z : ZeroQTermIndex, c z • R z := rfl
  have hS : lowerGeneratorZeroCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      true mixed δ gen g2 q dr Ar p x i = ∑ z : ZeroQTermIndex, c z • S z := rfl
  exact scalar_word_adjoint_transport _ _ _ _ hR hS a0 b0 u v
    (weighted_word_adjoint_graph c R S a0 b0 u v hWord)


/-- Finite linearity of the complete weak word graph. This is pointwise and
makes no smoothness assertion about a chosen coefficient-mass witness. -/
private lemma lowerGeneratorZeroCoefficient_forward_graph
    (mixed : MRoom) (δ : ℝ) (gen : GRoom δ) (g2 : MatrixField)
    (q dr Ar : ℝ) (p : ℕ) (x : R3)
    (htG : (Tq dr Ar p q) x ∈ ParamRoom δ)
    (htM : (Tq dr Ar p q) x ∈ ParamRoom mixed.δ)
    (hmem : ∀ᶠ y in 𝓝 x, (Tq dr Ar p q) y ∈ ParamRoom data.δ)
    (hDiff : ∀ j : Fin 3,
      DifferentiableAt ℝ (fun y => EH j ((Tq dr Ar p q) y)) x ∧
      DifferentiableAt ℝ (fun y => EL j ((Tq dr Ar p q) y)) x ∧
      DifferentiableAt ℝ (fun y => eH j ((Tq dr Ar p q) y)) x ∧
      DifferentiableAt ℝ (fun y => eL j ((Tq dr Ar p q) y)) x)
    (i : LowerCoreAngularGeneratorIndex) (u v uGstar vG : Hi)
    (hu : IH uGstar = AGSH i u) (hv : IH vG = AGH i v) :
    PP (IH uGstar) (ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x v) -
    PP (IH u) (ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x vG) =
    PP (IH u) (lowerGeneratorZeroCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      false mixed δ gen g2 q dr Ar p x i v) := by
  exact actual_coefficient_forward_sum
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    mixed δ gen g2 q dr Ar p x i (IH uGstar) (IH u) v vG
    (fun z => zeroQTermWord_forward_graph
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      mixed δ gen q dr Ar p x htG htM hmem hDiff i u v uGstar vG hu hv z)

private lemma lowerGeneratorZeroCoefficient_actual_adjoint
    (mixed : MRoom) (δ : ℝ) (gen : GRoom δ) (g2 : MatrixField)
    (q dr Ar : ℝ) (p : ℕ) (x : R3)
    (htG : (Tq dr Ar p q) x ∈ ParamRoom δ)
    (htM : (Tq dr Ar p q) x ∈ ParamRoom mixed.δ)
    (hmem : ∀ᶠ y in 𝓝 x, (Tq dr Ar p q) y ∈ ParamRoom data.δ)
    (hDiff : ∀ j : Fin 3,
      DifferentiableAt ℝ (fun y => EH j ((Tq dr Ar p q) y)) x ∧
      DifferentiableAt ℝ (fun y => EL j ((Tq dr Ar p q) y)) x ∧
      DifferentiableAt ℝ (fun y => eH j ((Tq dr Ar p q) y)) x ∧
      DifferentiableAt ℝ (fun y => eL j ((Tq dr Ar p q) y)) x)
    (i : LowerCoreAngularGeneratorIndex) (u v : Hi) :
    PP (IH u) (lowerGeneratorZeroCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      false mixed δ gen g2 q dr Ar p x i v) =
    PP (IH v) (lowerGeneratorZeroCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      true mixed δ gen g2 q dr Ar p x i u) := by
  exact actual_coefficient_adjoint_sum
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    mixed δ gen g2 q dr Ar p x i (IH u) (IH v) u v
    (fun z => zeroQTermWord_actual_adjoint
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      mixed δ gen q dr Ar p x htG htM hmem hDiff i u v z)


open ActualHigherSZeroPhysicalGraph ActualHigherSPhysicalPairing
  ActualLowerUSFiniteQuadraticCommutator ActualFiniteHarmonicModel.ActualLowerUSLowerWordAdjoints

local notation "CRoom" δ:max => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs δ
local notation "CZ" g2:max dr:max Ar:max p:max q:max =>
  ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q
local notation "Comp" g2:max dr:max Ar:max p:max hdr:max hAr:max q:max =>
  ActualLowerUSFiniteQuadraticCommutator.lowerGeneratorZeroCommutatorDensity
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs g2 dr Ar p hdr hAr q

private theorem actual_nativeZeroOut_pairing_of_negative_graph
    (hreg0 : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0)
    (δF : ℝ)
    (Cm : ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg0 δ0 W δF)
    (hJac : ∀ z ∈ commonRoom y0 ρ δF,
      ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (hq : q ∈ Icc (0 : ℝ) 1)
    (U V : smoothCompactFiniteSphereCore hO hD)
    (hTV : ∀ y ∈ tsupport V.val,
      ActualHigherSFormation.higherSParam L dr Ar p q y ∈
        Set.prod (commonRoom y0 ρ δF) (closedBall (0 : R3 →L[ℝ] ℝ) 1))
    (x : R3) :
    ⟪U.val x,nativeZeroOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg0 δ0 W g2 dr Ar p hdr hAr q V x⟫_ℝ =
    PP (IH (finiteCoreSobolevLift hO hD (3/2 : ℝ) U x))
      (ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) V x)) := by
  have hGraph := nativeZeroHalf_negative_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg0 δ0 W δF Cm hJac g2 hg2 dr Ar p hdr hAr q hq V hTV
  have hPair := physical_pairing_of_graph hO hD U
    (nativeZeroHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg0 δ0 W g2 dr Ar p hdr hAr q V)
    (fun y => ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q y
      (ActualHigherSFormation.higherSInput hO hD V y)) hGraph x
  have hInput : ActualHigherSFormation.higherSInput hO hD V x =
      finiteCoreSobolevLift hO hD (3/2 : ℝ) V x := rfl
  have hPairInput := congrArg
    (fun z : Hi => PP (IH (finiteCoreSobolevLift hO hD (3/2 : ℝ) U x))
      (ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x z)) hInput
  change ⟪U.val x,sphereSobolevHalfToSphereL2L hO hD
    (nativeZeroHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg0 δ0 W g2 dr Ar p hdr hAr q V x)⟫_ℝ = _
  exact hPair.symm.trans hPairInput


private theorem actual_nativeGeneratorZeroCommutator_of_scalar_graph
    (hreg0 : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0)
    (δF : ℝ)
    (Cm : ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg0 δ0 W δF)
    (hJac : ∀ z ∈ commonRoom y0 ρ δF,
      ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (hq : q ∈ Icc (0 : ℝ) 1)
    (i : LowerCoreAngularGeneratorIndex)
    (U V : smoothCompactFiniteSphereCore hO hD)
    (hTV : ∀ y ∈ tsupport V.val,
      ActualHigherSFormation.higherSParam L dr Ar p q y ∈
        Set.prod (commonRoom y0 ρ δF) (closedBall (0 : R3 →L[ℝ] ℝ) 1))
    (x : R3) (graphValue : ℝ)
    (hScalar :
      PP (IH (finiteCoreSobolevLift hO hD (3/2 : ℝ)
          (lowerCoreAngularGeneratorAdjoint hO hD hF i U) x))
        (ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x
          (finiteCoreSobolevLift hO hD (3/2 : ℝ) V x)) -
      PP (IH (finiteCoreSobolevLift hO hD (3/2 : ℝ) U x))
        (ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x
          (finiteCoreSobolevLift hO hD (3/2 : ℝ)
            (lowerCoreAngularGenerator hO hD hF i V) x)) = graphValue) :
    lowerGeneratorZeroCommutatorDensity
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg0 δ0 W g2 dr Ar p hdr hAr q i U V x = graphValue := by
  have hTGV : ∀ y ∈ tsupport (lowerCoreAngularGenerator hO hD hF i V).val,
      ActualHigherSFormation.higherSParam L dr Ar p q y ∈
        Set.prod (commonRoom y0 ρ δF) (closedBall (0 : R3 →L[ℝ] ℝ) 1) :=
    fun y hy => hTV y ((finiteCoreSupportPreserving_lowerCoreAngularGenerator hO hD hF i V) hy)
  have hP1 := actual_nativeZeroOut_pairing_of_negative_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg0 δ0 W δF Cm hJac g2 hg2 dr Ar p hdr hAr q hq
    (lowerCoreAngularGeneratorAdjoint hO hD hF i U) V hTV x
  have hP2 := actual_nativeZeroOut_pairing_of_negative_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg0 δ0 W δF Cm hJac g2 hg2 dr Ar p hdr hAr q hq
    U (lowerCoreAngularGenerator hO hD hF i V) hTGV x
  unfold lowerGeneratorZeroCommutatorDensity
  exact (congrArg₂ (fun a b : ℝ => a-b) hP1 hP2).trans hScalar


private lemma lowerGenerator_support (i : LowerCoreAngularGeneratorIndex) :
    FiniteCoreSupportPreserving hO hD (lowerCoreAngularGenerator hO hD hF i) :=
  finiteCoreSupportPreserving_of_pointwise_adjoint hO hD _
    (lowerCoreAngularGeneratorAdjoint hO hD hF i)
    (fun U V x => (hasCoreAngularFirstOrderBounds_lowerCoreAngularGenerator hO hD hF i x).2.1 U V)

/-- Exact identification with the original native physical scalar commutator.
The only transformed inputs are genuine finite angular G(V) and Gstar(U). -/
private theorem lowerGeneratorZeroCommutatorDensity_eq_forward_pairing
    (mixed : MRoom) (δG : ℝ) (gen : GRoom δG)
    (δF : ℝ) (Cm : CRoom δF)
    (hJac : ∀ z ∈ commonRoom y0 ρ δF,
      ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (V : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ y ∈ tsupport V.val, (Tq dr Ar p q) y ∈ ParamRoom δF)
    (x : R3) (htG : (Tq dr Ar p q) x ∈ ParamRoom δG)
    (htM : (Tq dr Ar p q) x ∈ ParamRoom mixed.δ)
    (hmem : ∀ᶠ y in 𝓝 x, (Tq dr Ar p q) y ∈ ParamRoom data.δ)
    (hDiff : ∀ j : Fin 3,
      DifferentiableAt ℝ (fun y => EH j ((Tq dr Ar p q) y)) x ∧
      DifferentiableAt ℝ (fun y => EL j ((Tq dr Ar p q) y)) x ∧
      DifferentiableAt ℝ (fun y => eH j ((Tq dr Ar p q) y)) x ∧
      DifferentiableAt ℝ (fun y => eL j ((Tq dr Ar p q) y)) x)
    (i : LowerCoreAngularGeneratorIndex) (U : smoothCompactFiniteSphereCore hO hD) :
    (Comp g2 dr Ar p hdr hAr q) i U V x =
      PP (IH (finiteCoreSobolevLift hO hD (3/2 : ℝ) U x))
        (lowerGeneratorZeroCoefficient
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
          false mixed δG gen g2 q dr Ar p x i
          (finiteCoreSobolevLift hO hD (3/2 : ℝ) V x)) := by
  have hScalar := lowerGeneratorZeroCoefficient_forward_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    mixed δG gen g2 q dr Ar p x htG htM hmem hDiff i
    (finiteCoreSobolevLift hO hD (3/2 : ℝ) U x)
    (finiteCoreSobolevLift hO hD (3/2 : ℝ) V x)
    (finiteCoreSobolevLift hO hD (3/2 : ℝ)
      (lowerCoreAngularGeneratorAdjoint hO hD hF i U) x)
    (finiteCoreSobolevLift hO hD (3/2 : ℝ)
      (lowerCoreAngularGenerator hO hD hF i V) x)
    (lowerSAngularSharpHigh_finiteCoreHi_inclusion hF hO hD i U x)
    (lowerSAngularHigh_finiteCoreHi_inclusion hF hO hD i V x)
  have hNative := actual_nativeGeneratorZeroCommutator_of_scalar_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs δF Cm hJac g2 hg2 dr Ar p hdr hAr q hq i U V hTF x _ hScalar
  exact hNative


private abbrev finiteWeightValue (s : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : SphereL2 :=
  (coreWeightOperator hO hD (SpectralWeightedGraph.besselWeight s) F).val x
local notation "WH" F:max x:max => ‖finiteWeightValue hO hD (1/2 : ℝ) F x‖
local notation "WHi" F:max x:max => ‖finiteWeightValue hO hD (3/2 : ℝ) F x‖

/-- Complete actual primitive generator/Q producer, in both weak Sobolev
orientations, derived from original profile and H8 hypotheses. The original
physical Qout and its genuine finite angular pretests are retained exactly. -/
theorem exists_lowerGeneratorZeroCommutator_uniform_profile_bound
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ δ : ℝ, ∃ Cm : CRoom δ,
      (∀ z ∈ commonRoom y0 ρ δ,
        ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z) ∧
      ∃ C_G : ℝ, 0 < C_G ∧ ∃ etaG : ℝ, 0 < etaG ∧
      etaG ≤ data.eta0 ∧ etaG ≤ 1 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaG →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x *
        (actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      (∀ x ∈ K, CoordinateBootstrapJets.coordinateH8
        (referenceNormalizedPrincipalDifference g g2 L q) x ≤
          eta*referenceRadius dr Ar p L x) →
      (∀ x ∈ K, (Tq dr Ar p q) x ∈ ParamRoom δ) ∧
      ∀ i : LowerCoreAngularGeneratorIndex,
      ∀ U V : smoothCompactFiniteSphereCore hO hD,
      tsupport U.val ⊆ K → tsupport V.val ⊆ K → ∀ x ∈ K,
        |(Comp g2 dr Ar p hdr hAr q) i U V x| ≤
          C_G*referenceRadius dr Ar p L x*(WH U x)*(WHi V x) ∧
        |(Comp g2 dr Ar p hdr hAr q) i U V x| ≤
          C_G*referenceRadius dr Ar p L x*(WHi U x)*(WH V x) := by
  obtain ⟨mixed,δG,hδG,gen,CG,hCG,etaN,hEtaN,hEtaN0,hEtaN1,hNorm⟩ :=
    exists_retained_lowerGeneratorZeroCoefficient_uniform_profile_bound
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 hL hKernel
  obtain ⟨δF,Cm,hJac⟩ := ActualCommonQuadraticFormationConsumer.exists_retained_common_formation_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg hKernel data.δ0 data.δ0_pos data.germs
  obtain ⟨etaF,hEtaF,hEtaF1,hGuardF⟩ := exists_uniform_strict_higherSParam_guard
    g hg L hL y0 ρ δF Cm.rev.pos (closedBall y0 ρ) (isCompact_closedBall _ _)
  obtain ⟨etaD,hEtaD,hEtaD1,hGuardD⟩ := exists_uniform_strict_higherSParam_guard
    g hg L hL y0 ρ data.δ data.δ_pos (closedBall y0 ρ) (isCompact_closedBall _ _)
  let etaG := min etaN (min etaF etaD)
  have hEtaG : 0 < etaG := lt_min hEtaN (lt_min hEtaF hEtaD)
  have hGN : etaG ≤ etaN := min_le_left _ _
  have hGF : etaG ≤ etaF := (min_le_right _ _).trans (min_le_left _ _)
  have hGD : etaG ≤ etaD := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δF,Cm,hJac,CG,hCG,etaG,hEtaG,hGN.trans hEtaN0,hGN.trans hEtaN1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaG K _hK hBall hb hs hH8
  have hClosed (x : R3) (hx : x ∈ K) : x ∈ closedBall y0 ρ := ball_subset_closedBall (hBall hx)
  have hTFK (x : R3) (hx : x ∈ K) : (Tq dr Ar p q) x ∈ ParamRoom δF := by
    have hgF := hGuardF q hq dr hdr hdr1 Ar hAr p hp eta heta (hetaG.trans hGF)
      x (hClosed x hx) (hBall hx) (hb x hx) (hs x hx)
    exact (higherSParam_eventually_mem y0 ρ δF L dr Ar q p hdr hAr x hgF).self_of_nhds
  refine ⟨hTFK,?_⟩
  intro i U V _hSU hSV x hx
  have hc := hNorm q hq dr hdr hdr1 Ar hAr p hp eta heta (hetaG.trans hGN)
    x (hClosed x hx) (hBall hx) (hb x hx) (hs x hx) (hH8 x hx)
  have hDguard := hGuardD q hq dr hdr hdr1 Ar hAr p hp eta heta (hetaG.trans hGD)
    x (hClosed x hx) (hBall hx) (hb x hx) (hs x hx)
  have hmem := higherSParam_eventually_mem y0 ρ data.δ L dr Ar q p hdr hAr x hDguard
  have hpE (j : Fin 3) := data.physical_caps q hq dr hdr hdr1 Ar hAr p hp eta heta
    (hetaG.trans (hGN.trans hEtaN0)) x (hClosed x hx) (hBall hx) (hb x hx) (hs x hx) j j
  have hDiff (j : Fin 3) :
      DifferentiableAt ℝ (fun y => EH j ((Tq dr Ar p q) y)) x ∧
      DifferentiableAt ℝ (fun y => EL j ((Tq dr Ar p q) y)) x ∧
      DifferentiableAt ℝ (fun y => eH j ((Tq dr Ar p q) y)) x ∧
      DifferentiableAt ℝ (fun y => eL j ((Tq dr Ar p q) y)) x :=
    ⟨(hpE j).2.2.1.1.differentiableAt (by simp),
      (hpE j).2.2.2.1.1.differentiableAt (by simp),
      (hpE j).2.2.2.2.1.1.differentiableAt (by simp),
      (hpE j).2.2.2.2.2.1.differentiableAt (by simp)⟩
  let u := finiteCoreSobolevLift hO hD (3/2 : ℝ) U x
  let v := finiteCoreSobolevLift hO hD (3/2 : ℝ) V x
  let RF := lowerGeneratorZeroCoefficient
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    false mixed δG gen g2 q dr Ar p x i
  let RS := lowerGeneratorZeroCoefficient
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    true mixed δG gen g2 q dr Ar p x i
  have hGraphRaw := lowerGeneratorZeroCommutatorDensity_eq_forward_pairing
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      mixed δG gen δF Cm hJac g2 hg2 dr Ar p hdr hAr q hq V
      (fun y hy => hTFK y (hSV hy)) x hc.1 hc.2.1 hmem hDiff i U
  have hGraph : (Comp g2 dr Ar p hdr hAr q) i U V x = PP (IH u) (RF v) := by
    simpa only [u,v,RF] using hGraphRaw
  have hStarRaw := lowerGeneratorZeroCoefficient_actual_adjoint
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      mixed δG gen g2 q dr Ar p x hc.1 hc.2.1 hmem hDiff i u v
  have hStar : PP (IH u) (RF v) = PP (IH v) (RS u) := by
    simpa only [RF,RS] using hStarRaw
  have hRFn : ‖RF v‖ ≤ (CG*referenceRadius dr Ar p L x)*‖v‖ :=
    (RF.le_opNorm v).trans (mul_le_mul_of_nonneg_right (hc.2.2.2 i false) (norm_nonneg v))
  have hRSn : ‖RS u‖ ≤ (CG*referenceRadius dr Ar p L x)*‖u‖ :=
    (RS.le_opNorm u).trans (mul_le_mul_of_nonneg_right (hc.2.2.2 i true) (norm_nonneg u))
  have hUH : ‖u‖ = WHi U x := norm_finiteCoreSobolevLift hO hD (3/2 : ℝ) U x
  have hVH : ‖v‖ = WHi V x := norm_finiteCoreSobolevLift hO hD (3/2 : ℝ) V x
  have hUL : ‖IH u‖ = WH U x := by
    change ‖IH (finiteCoreSobolevLift hO hD (3/2 : ℝ) U x)‖ = _
    rw [sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) (1/2 : ℝ) (by norm_num)]
    exact norm_finiteCoreSobolevLift hO hD (1/2 : ℝ) U x
  have hVL : ‖IH v‖ = WH V x := by
    change ‖IH (finiteCoreSobolevLift hO hD (3/2 : ℝ) V x)‖ = _
    rw [sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) (1/2 : ℝ) (by norm_num)]
    exact norm_finiteCoreSobolevLift hO hD (1/2 : ℝ) V x
  constructor
  · calc
      _ = |PP (IH u) (RF v)| := congrArg abs hGraph
      _ ≤ ‖IH u‖*‖RF v‖ := abs_sphereSobolevDualPairing_le (1/2 : ℝ) _ _
      _ ≤ ‖IH u‖*((CG*referenceRadius dr Ar p L x)*‖v‖) :=
        mul_le_mul_of_nonneg_left hRFn (norm_nonneg _)
      _ = CG*referenceRadius dr Ar p L x*(WH U x)*(WHi V x) := by rw [hUL,hVH]; ring
  · calc
      _ = |PP (IH v) (RS u)| := congrArg abs (hGraph.trans hStar)
      _ ≤ ‖IH v‖*‖RS u‖ := abs_sphereSobolevDualPairing_le (1/2 : ℝ) _ _
      _ ≤ ‖IH v‖*((CG*referenceRadius dr Ar p L x)*‖u‖) :=
        mul_le_mul_of_nonneg_left hRSn (norm_nonneg _)
      _ = CG*referenceRadius dr Ar p L x*(WHi U x)*(WH V x) := by rw [hVL,hUH]; ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSGeneratorZeroCommutator
