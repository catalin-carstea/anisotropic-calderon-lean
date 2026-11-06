import Calderon.ActualPPIntegralRemainder
import Calderon.ActualHigherSQuadraticZeroQuarticBounds
import Calderon.ActualHigherSDirectLower
import Calderon.ActualHigherSActualCubicBound
import Calderon.ActualLowerSSelfPhysicalDecomposition
import Calderon.ActualLowerSSelfFormation
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerSSelfRemainder
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
 ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
 ReferenceDensityBounds ReferenceWeightedApproximation ConformalDepth FixedParameterProfilePullback
 PrincipalCommutator SectionFiveErrorForms
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
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
local notation "SF" => ActualHigherSFormation.nativeHigherSOut hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "TF" => ActualHigherSAdjointFormation.higherSAdjointOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PF" => ActualPPLowerRemainder.actualPPFirstOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PR" => ActualPPLowerRemainder.actualPPReverseFirstOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Z2" => ActualHigherSQuadraticZeroQuartic.actualZ2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "T2" => ActualHigherSQuadraticZeroQuartic.actualT2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "Z1" => ActualHigherSLinearZero.linearZeroHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "T1" => ActualHigherSLinearZero.linearAdjointZeroHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "U" => ActualHigherSFormation.higherSInput hO hD
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
variable (g2 : MatrixField)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "HU" => ActualHigherSScalarCommutatorNativeForm.halfInput hO hD
local notation "Lead" => actualLeadingSignedSecondNeg
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
local notation "BR" => ActualPPLowerRemainder.actualPPBalancedRow
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "DF" => ActualHigherSDirectLower.directFirstLinear
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "DQ" => ActualHigherSDirectLower.directQuadraticLinear
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
local notation "DS" => ActualHigherSDirectLower.directLinearSquares
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "DR" => ActualHigherSDirectLower.actualDirectLower
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "ARoom" d:max => ActualAllAngularAtomGainedRoom.AllAngularAtomRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data d
local notation "WC" => ActualHigherSQuadraticZeroWords.actualWordCoefficient g L g2
local notation "QR" => ActualHigherSQuadraticZeroQuartic.quarticWordRow
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "Word" => ActualHigherSQuadraticZeroWords.ZeroWord

def originalSignedNormDensity (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)
    (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  ‖SF dr Ar p hdr hAr q hreg data.δ0 data.germs g2 F x‖^2-
    ‖TF hreg data.δ0 data.germs g2 dr Ar p hdr hAr q F x‖^2

def originalLeadingDensity (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  referenceDensityFamily g L (q,x)*PP (HU F x) (Lead dr Ar p q F x)

def originalEnergyDensity (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  referenceDensityFamily g L (q,x)*finiteCoreReferenceProfileEnergy hO hD g hg L q
    (actualReferenceBeta g L q dr Ar p x) F x

def originalLowerSSelfRemainder (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)
    (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD) : ℝ :=
  (∫ x,referenceDensityFamily g L (q,x)*
    originalSignedNormDensity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p hdr hAr q F x)-
  (∫ x,originalLeadingDensity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F x)

/-- Exactly six original physical norm categories, with every direct term literal. -/
def physicalSixCategoryDensity (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  (‖PF g2 dr Ar p q F x‖^2-‖PR g2 dr Ar p q F x‖^2)+
  2*(⟪PF g2 dr Ar p q F x,KL (Z2 g2 dr Ar p q F x)⟫_ℝ-
    ⟪PR g2 dr Ar p q F x,KL (T2 g2 dr Ar p q F x)⟫_ℝ)+
  (‖KL (Z2 g2 dr Ar p q F x)‖^2-‖KL (T2 g2 dr Ar p q F x)‖^2)+
  2*(⟪PF g2 dr Ar p q F x,KL (Z1 g2 dr Ar p q x (U F x))⟫_ℝ-
    ⟪PR g2 dr Ar p q F x,KL (T1 g2 dr Ar p q x (U F x))⟫_ℝ)+
  2*(⟪KL (Z2 g2 dr Ar p q F x),KL (Z1 g2 dr Ar p q x (U F x))⟫_ℝ-
    ⟪KL (T2 g2 dr Ar p q F x),KL (T1 g2 dr Ar p q x (U F x))⟫_ℝ)+
  (‖KL (Z1 g2 dr Ar p q x (U F x))‖^2-‖KL (T1 g2 dr Ar p q x (U F x))‖^2)

/-- Literal grouped207² sum of the selected four-pairing quartic rows.
No individual row integrability is asserted by this definition. -/
def physicalQuarticWordSum {d : ℝ} (P : ARoom d) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  ∑ z : Word,∑ v : Word,(WC dr Ar p q x z*WC dr Ar p q x v)*QR P ((Tq dr Ar p q) x) (U F x) z v

local notation "ND" => originalSignedNormDensity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
local notation "LD" => originalLeadingDensity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
local notation "ED" => originalEnergyDensity g L hg hO hD
local notation "REM" => originalLowerSSelfRemainder g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
local notation "SIX" => physicalSixCategoryDensity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
local notation "QSUM" => physicalQuarticWordSum g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2

def PrimaryLowerSSelfConclusions (Crem eta : ℝ) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD) : Prop :=
  let mu := fun x : R3 => referenceDensityFamily g L (q,x)
  let pp := fun x : R3 => ∑ l : Fin 3,∑ k : Fin 3,BR dr Ar p q F x l k
  let first := fun x : R3 => mu x*(‖PF g2 dr Ar p q F x‖^2-‖PR g2 dr Ar p q F x‖^2)
  let mixF := fun x : R3 => mu x*⟪PF g2 dr Ar p q F x,KL (Z2 g2 dr Ar p q F x)⟫_ℝ
  let mixR := fun x : R3 => mu x*⟪PR g2 dr Ar p q F x,KL (T2 g2 dr Ar p q F x)⟫_ℝ
  let quartic := fun x : R3 => mu x*(‖KL (Z2 g2 dr Ar p q F x)‖^2-‖KL (T2 g2 dr Ar p q F x)‖^2)
  Integrable (fun x => mu x*‖SF dr Ar p hdr hAr q hreg data.δ0 data.germs g2 F x‖^2) ∧
  Integrable (fun x => mu x*‖TF hreg data.δ0 data.germs g2 dr Ar p hdr hAr q F x‖^2) ∧
  Integrable (fun x => mu x*‖PF g2 dr Ar p q F x‖^2) ∧
  Integrable (fun x => mu x*‖PR g2 dr Ar p q F x‖^2) ∧
  Integrable (fun x => mu x*‖KL (Z2 g2 dr Ar p q F x)‖^2) ∧
  Integrable (fun x => mu x*‖KL (T2 g2 dr Ar p q F x)‖^2) ∧
  Integrable (fun x => mu x*‖KL (Z1 g2 dr Ar p q x (U F x))‖^2) ∧
  Integrable (fun x => mu x*‖KL (T1 g2 dr Ar p q x (U F x))‖^2) ∧
  Integrable (fun x => mu x*ND dr Ar p hdr hAr q F x) ∧ Integrable (LD dr Ar p q F) ∧
  Integrable (ED dr Ar p q F) ∧ Integrable (fun x => mu x*ND dr Ar p hdr hAr q F x-LD dr Ar p q F x) ∧
  Integrable first ∧ Integrable mixF ∧ Integrable mixR ∧ Integrable quartic ∧
  Integrable (fun x => mu x*DF dr Ar p q F x) ∧ Integrable (fun x => mu x*DQ dr Ar p q F x) ∧
  Integrable (fun x => mu x*DS dr Ar p q F x) ∧ Integrable (fun x => mu x*DR dr Ar p q F x) ∧
  Integrable pp ∧ (∀ l k : Fin 3,Integrable (fun x => BR dr Ar p q F x l k)) ∧
  (∀ x : R3,ND dr Ar p hdr hAr q F x=SIX dr Ar p q F x) ∧
  ((∫ x,first x)=(∫ x,LD dr Ar p q F x)+(∫ x,pp x)) ∧
  (REM dr Ar p hdr hAr q F=∫ x,mu x*ND dr Ar p hdr hAr q F x-LD dr Ar p q F x) ∧
  (∃ dQ : ℝ,0 < dQ ∧ ∃ P : ARoom dQ,
    Integrable (fun x => mu x*QSUM P dr Ar p q F x) ∧
    (∀ x : R3,quartic x=mu x*QSUM P dr Ar p q F x) ∧
    REM dr Ar p hdr hAr q F=(∫ x,pp x)+2*((∫ x,mixF x)-(∫ x,mixR x))+
      (∫ x,mu x*QSUM P dr Ar p q F x)+(∫ x,mu x*DR dr Ar p q F x)) ∧
  |REM dr Ar p hdr hAr q F| ≤ Crem*eta*(∫ x,ED dr Ar p q F x)

def PrimaryLowerSSelfContract : Prop :=
  ∃ Crem etaRem : ℝ,0 < Crem ∧ 0 < etaRem ∧ etaRem ≤ data.eta0 ∧
  ∀ q ∈ Icc (0 : ℝ) 1,
  ∀ dr : ℝ,∀ hdr : 0 < dr,dr ≤ 1 → ∀ Ar : ℝ,∀ hAr : 0 < Ar,
  ∀ p : ℕ,1 ≤ p → ∀ eta : ℝ,0 ≤ eta → eta ≤ etaRem →
  ∀ K : Set R3,IsCompact K → K ⊆ ball y0 ρ →
  ∀ F : smoothCompactFiniteSphereCore hO hD,tsupport F.val ⊆ K →
  (∀ x ∈ K,1 ≤ actualReferenceBeta g L q dr Ar p x) →
  (∀ x ∈ K,referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
  PrimaryLowerSSelfConclusions g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
    Crem eta dr Ar p hdr hAr q F


private lemma weighted_norm_sq_integrable {V : Type*} [NormedAddCommGroup V]
    (mu : R3 → ℝ) (f : R3 → V) (hmu : Continuous mu) (hf : Continuous f)
    (hc : HasCompactSupport f) : Integrable (fun x => mu x*‖f x‖^2) := by
  apply (hmu.mul (hf.norm.pow 2)).integrable_of_hasCompactSupport
  apply hc.mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro hz
  exact hx (by
    change mu x*‖f x‖^2=0
    simp [hz])

private lemma weighted_sub_integrable (mu f g : R3 → ℝ)
    (hf : Integrable (fun x => mu x*f x)) (hg : Integrable (fun x => mu x*g x)) :
    Integrable (fun x => mu x*(f x-g x)) :=
  (hf.sub hg).congr (Filter.Eventually.of_forall (fun x => by
    change mu x*f x-mu x*g x=mu x*(f x-g x)
    ring))

private lemma weighted_sub_integral (mu f g : R3 → ℝ)
    (hf : Integrable (fun x => mu x*f x)) (hg : Integrable (fun x => mu x*g x)) :
    (∫ x,mu x*(f x-g x))=(∫ x,mu x*f x)-(∫ x,mu x*g x) := by
  have hfun : (fun x => mu x*(f x-g x))=(fun x => mu x*f x-mu x*g x) := by
    funext x
    ring
  rw [hfun,integral_sub hf hg]

private lemma six_integral (a b c d e f : R3 → ℝ)
    (ha : Integrable a) (hb : Integrable b) (hc : Integrable c)
    (hd : Integrable d) (he : Integrable e) (hf : Integrable f) :
    (∫ x,a x+b x+c x+d x+e x+f x)=
      (∫ x,a x)+(∫ x,b x)+(∫ x,c x)+(∫ x,d x)+(∫ x,e x)+(∫ x,f x) := by
  have h2 : (∫ x,a x+b x)=(∫ x,a x)+(∫ x,b x) := by
    simpa only [Pi.add_apply] using integral_add ha hb
  have h3 : (∫ x,a x+b x+c x)=(∫ x,a x+b x)+(∫ x,c x) := by
    simpa only [Pi.add_apply] using integral_add (ha.add hb) hc
  have h4 : (∫ x,a x+b x+c x+d x)=(∫ x,a x+b x+c x)+(∫ x,d x) := by
    simpa only [Pi.add_apply] using integral_add ((ha.add hb).add hc) hd
  have h5 : (∫ x,a x+b x+c x+d x+e x)=(∫ x,a x+b x+c x+d x)+(∫ x,e x) := by
    simpa only [Pi.add_apply] using integral_add (((ha.add hb).add hc).add hd) he
  have h6 : (∫ x,a x+b x+c x+d x+e x+f x)=(∫ x,a x+b x+c x+d x+e x)+(∫ x,f x) := by
    simpa only [Pi.add_apply] using integral_add ((((ha.add hb).add hc).add hd).add he) hf
  rw [h6,h5,h4,h3,h2]

private lemma abs_four_add_le (a b c d : ℝ) : |a+b+c+d| ≤ |a|+|b|+|c|+|d| :=
  (abs_add_le (a+b+c) d).trans
    (add_le_add ((abs_add_le (a+b) c).trans
      (add_le_add (abs_add_le a b) (le_refl |c|))) (le_refl |d|))

attribute [local irreducible] sphereSobolevHalfToSphereL2L sphereSobolevInclusionL
  ActualHigherSFormation.higherSInput ActualHigherSScalarCommutatorNativeForm.halfInput
  ActualHigherSFormation.nativeHigherSOut ActualHigherSAdjointFormation.higherSAdjointOut
  ActualPPLowerRemainder.actualPPFirstOut ActualPPLowerRemainder.actualPPReverseFirstOut
  ActualHigherSQuadraticZeroQuartic.actualZ2Half ActualHigherSQuadraticZeroQuartic.actualT2Half
  ActualHigherSLinearZero.linearZeroHigh ActualHigherSLinearZero.linearAdjointZeroHigh

/-- Primary original remainder estimate. The full Mixed weak companion is a
separately pending assigned component, and is not asserted by this theorem. -/
theorem exists_original_lower_s_self_primary_remainder (hL : 0 < L)
    (hKernel : UnitBallValueTraceKernel τ0) (hg2 : IsAdmissibleMetric g2) :
    PrimaryLowerSSelfContract g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 := by
  obtain ⟨CPP,etaPP,hCPP,hetaPP,hetaPP0,hPP⟩ :=
    ActualPPLowerRemainder.exists_actual_pp_lower_remainder
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hL hKernel hg2
  obtain ⟨CM,etaM,hCM,hetaM,hetaM0,hMixed⟩ :=
    ActualHigherSActualCubicBound.exists_uniform_same_packet_actual_mixed_cubic_bound
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hL hKernel g2 hg2
  obtain ⟨CQ,etaQ,hCQ,hetaQ,hetaQ0,hQuartic⟩ :=
    ActualHigherSQuadraticZeroQuarticBounds.exists_uniform_same_packet_actual207_quartic_bound
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hL hKernel g2 hg2
  obtain ⟨CD,etaD,hCD,hetaD,hetaD0,hDirect⟩ :=
    ActualHigherSDirectLower.exists_actual_direct_lower
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hL hKernel hg2
  obtain ⟨etaSplit,hetaSplit,hetaSplit0,hSplit⟩ :=
    ActualLowerSSelfPhysicalDecomposition.exists_same_packet_physical_first_zero_split
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hL hKernel g2 hg2
  obtain ⟨etaFormation,hetaFormation,hetaFormation0,hFormation⟩ :=
    ActualLowerSSelfFormation.exists_uniform_same_packet_higherS_formation
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hL hKernel g2 hg2
  obtain ⟨dQ,hdQ,_hdQD,PQ,dI,hdI,hdIQ,_hdI0,_hdIrho,hQuarticIdentity⟩ :=
    ActualHigherSQuadraticZeroQuartic.exists_same_packet_actual207_word_identity
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hKernel g2
  obtain ⟨epsQ,hepsQ,_hepsQ1,hGuardQ⟩ := exists_uniform_strict_higherSParam_guard
    g hg L hL y0 ρ dI hdI (closedBall y0 ρ) (isCompact_closedBall _ _)
  let etaNorm := min etaSplit etaFormation
  let etaBounds := min etaPP (min etaM (min etaQ etaD))
  let etaRem := min data.eta0 (min etaNorm (min etaBounds epsQ))
  let Crem := 1+CPP+CM+CQ+CD
  have hCrem : 0 < Crem := by dsimp only [Crem]; positivity
  have hetaNorm : 0 < etaNorm := lt_min hetaSplit hetaFormation
  have hetaBounds : 0 < etaBounds := lt_min hetaPP (lt_min hetaM (lt_min hetaQ hetaD))
  refine ⟨Crem,etaRem,hCrem,lt_min data.eta0_pos (lt_min hetaNorm (lt_min hetaBounds hepsQ)),min_le_left _ _,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaRem K hK hKball F hsupp hb hs
  have heNorm : eta ≤ etaNorm := hetaRem.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heBounds : eta ≤ etaBounds := hetaRem.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have heGuard : eta ≤ epsQ := hetaRem.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hePP : eta ≤ etaPP := heBounds.trans (min_le_left _ _)
  have heM : eta ≤ etaM := heBounds.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heQ : eta ≤ etaQ := heBounds.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have heD : eta ≤ etaD := heBounds.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have heSplit : eta ≤ etaSplit := heNorm.trans (min_le_left _ _)
  have heFormation : eta ≤ etaFormation := heNorm.trans (min_le_right _ _)
  let mu := fun x : R3 => referenceDensityFamily g L (q,x)
  let pp := fun x : R3 => ∑ l : Fin 3,∑ k : Fin 3,BR dr Ar p q F x l k
  let first := fun x : R3 => mu x*(‖PF g2 dr Ar p q F x‖^2-‖PR g2 dr Ar p q F x‖^2)
  let mixF := fun x : R3 => mu x*⟪PF g2 dr Ar p q F x,KL (Z2 g2 dr Ar p q F x)⟫_ℝ
  let mixR := fun x : R3 => mu x*⟪PR g2 dr Ar p q F x,KL (T2 g2 dr Ar p q F x)⟫_ℝ
  let mixed := fun x : R3 => 2*(mixF x-mixR x)
  let quartic := fun x : R3 => mu x*(‖KL (Z2 g2 dr Ar p q F x)‖^2-‖KL (T2 g2 dr Ar p q F x)‖^2)
  let directF := fun x : R3 => mu x*DF dr Ar p q F x
  let directQ := fun x : R3 => mu x*DQ dr Ar p q F x
  let directS := fun x : R3 => mu x*DS dr Ar p q F x
  let direct := fun x : R3 => mu x*DR dr Ar p q F x
  let native := fun x : R3 => mu x*ND dr Ar p hdr hAr q F x
  let lead := LD dr Ar p q F
  let energy := ED dr Ar p q F
  obtain ⟨hIP,hIR,hIL,hIPP,hIE,hIBR,hPPWeak,hPPBound⟩ :=
    hPP q hq dr hdr hdr1 Ar hAr p hp eta heta hePP K hK hKball F hsupp hb hs
  obtain ⟨hIMF,hIMR,hMBound⟩ :=
    hMixed q hq dr hdr hdr1 Ar hAr p hp eta heta heM K hK hKball F hsupp hb hs
  obtain ⟨hIZ,hIT,_hQPoint,hQBound⟩ :=
    hQuartic q hq dr hdr hdr1 Ar hAr p hp eta heta heQ K hK hKball F hsupp hb hs
  obtain ⟨hReg,hIDF,hIDQ,hIDS,hID,_hIAbs,_hIED,_hDPoint,_hDAbs,hDBound⟩ :=
    hDirect q hq dr hdr hdr1 Ar hAr p hp eta heta heD K hK hKball F hsupp hb hs
  obtain ⟨_hout,_hTFsmooth,_hTFcompact,hNSF,hNTF⟩ :=
    hFormation q hq dr hdr hdr1 Ar hAr p hp eta heta heFormation K hK hKball F hsupp hb hs
  have hFields := hSplit q hq dr hdr hdr1 Ar hAr p hp eta heta heSplit K hK hKball F hsupp hb hs
  have hmu : Continuous mu := (contDiff_referenceDensityFamily g hg L).continuous.comp
    (continuous_const.prodMk continuous_id)
  have hIZ1 : Integrable (fun x => mu x*‖KL (Z1 g2 dr Ar p q x (U F x))‖^2) := by
    have h := weighted_norm_sq_integrable mu
      (ActualHigherSDirectLower.actualZ1Out
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F) hmu
      hReg.2.2.2.2.1.1.continuous hReg.2.2.2.2.1.2
    simpa only [ActualHigherSDirectLower.actualZ1Out] using h
  have hIT1 : Integrable (fun x => mu x*‖KL (T1 g2 dr Ar p q x (U F x))‖^2) := by
    have h := weighted_norm_sq_integrable mu
      (ActualHigherSDirectLower.actualT1Out
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F) hmu
      hReg.2.2.2.2.2.1.continuous hReg.2.2.2.2.2.2
    simpa only [ActualHigherSDirectLower.actualT1Out] using h
  have hNative : Integrable native := weighted_sub_integrable mu _ _ hNSF hNTF
  have hRemainder : Integrable (fun x => native x-lead x) := hNative.sub hIL
  have hFirst : Integrable first := weighted_sub_integrable mu _ _ hIP hIR
  have hQuartic : Integrable quartic := weighted_sub_integrable mu _ _ hIZ hIT
  have hMixedInt : Integrable mixed := (hIMF.sub hIMR).const_mul 2
  have hPhysical (x : R3) : ND dr Ar p hdr hAr q F x=SIX dr Ar p q F x := by
    unfold originalSignedNormDensity
    rw [(hFields x).1,(hFields x).2]
    exact ActualLowerSSelfPhysicalDecomposition.signed_three_block_expansion _ _ _ _ _ _
  have hNativeFun : native=(fun x => first x+mixed x+quartic x+directF x+directQ x+directS x) := by
    funext x
    dsimp only [native]
    rw [hPhysical x]
    dsimp only [physicalSixCategoryDensity,first,mixed,mixF,mixR,quartic,directF,directQ,directS,
      ActualHigherSDirectLower.directFirstLinear,ActualHigherSDirectLower.directQuadraticLinear,
      ActualHigherSDirectLower.directLinearSquares,ActualHigherSDirectLower.actualZ1Out,
      ActualHigherSDirectLower.actualT1Out]
    ring
  have hSixIntegral : (∫ x,native x)=(∫ x,first x)+(∫ x,mixed x)+(∫ x,quartic x)+
      (∫ x,directF x)+(∫ x,directQ x)+(∫ x,directS x) := by
    rw [hNativeFun]
    exact six_integral first mixed quartic directF directQ directS hFirst hMixedInt hQuartic hIDF hIDQ hIDS
  have hDirectFun : direct=(fun x => directF x+directQ x+directS x) := by
    funext x
    dsimp only [direct,directF,directQ,directS,ActualHigherSDirectLower.actualDirectLower]
    ring
  have hDirectIntegral : (∫ x,direct x)=(∫ x,directF x)+(∫ x,directQ x)+(∫ x,directS x) := by
    rw [hDirectFun]
    have hFQ : (∫ x,directF x+directQ x)=(∫ x,directF x)+(∫ x,directQ x) := by
      simpa only [Pi.add_apply] using integral_add hIDF hIDQ
    have hFQS : (∫ x,directF x+directQ x+directS x)=
        (∫ x,directF x+directQ x)+(∫ x,directS x) := by
      simpa only [Pi.add_apply] using integral_add (hIDF.add hIDQ) hIDS
    exact hFQS.trans (congrArg (fun t : ℝ => t+(∫ x,directS x)) hFQ)
  have hMixedIntegral : (∫ x,mixed x)=2*((∫ x,mixF x)-(∫ x,mixR x)) := by
    rw [integral_const_mul,integral_sub hIMF hIMR]
  have hQuarticIntegral : (∫ x,quartic x)=
      (∫ x,mu x*‖KL (Z2 g2 dr Ar p q F x)‖^2)-(∫ x,mu x*‖KL (T2 g2 dr Ar p q F x)‖^2) :=
    weighted_sub_integral mu _ _ hIZ hIT
  have hRemIntegral : REM dr Ar p hdr hAr q F=∫ x,native x-lead x := by
    unfold originalLowerSSelfRemainder
    exact (integral_sub hNative hIL).symm
  have hRemFour : REM dr Ar p hdr hAr q F=(∫ x,pp x)+(∫ x,mixed x)+(∫ x,quartic x)+(∫ x,direct x) := by
    have hPPWeakLocal : (∫ x,first x)=(∫ x,lead x)+(∫ x,pp x) := hPPWeak
    unfold originalLowerSSelfRemainder
    change (∫ x,native x)-(∫ x,lead x)=_
    rw [hSixIntegral,hPPWeakLocal,hDirectIntegral]
    ring
  have hTI : ∀ x ∈ tsupport F.val,(Tq dr Ar p q) x ∈ ParamRoom dI := by
    intro x hx
    have hxK := hsupp hx
    have hguard := hGuardQ q hq dr hdr hdr1 Ar hAr p hp eta heta heGuard x
      (ball_subset_closedBall (hKball hxK)) (hKball hxK) (hb x hxK) (hs x hxK)
    exact (higherSParam_eventually_mem y0 ρ dI L dr Ar q p hdr hAr x hguard).self_of_nhds
  have hQPoint (x : R3) : quartic x=mu x*QSUM PQ dr Ar p q F x :=
    congrArg (fun t : ℝ => mu x*t) (hQuarticIdentity dr Ar p hdr hAr q F hTI x)
  have hQFun : quartic=(fun x => mu x*QSUM PQ dr Ar p q F x) := funext hQPoint
  have hQGroup : Integrable (fun x => mu x*QSUM PQ dr Ar p q F x) := hQFun ▸ hQuartic
  have hExpanded : REM dr Ar p hdr hAr q F=(∫ x,pp x)+
      2*((∫ x,mixF x)-(∫ x,mixR x))+(∫ x,mu x*QSUM PQ dr Ar p q F x)+(∫ x,direct x) := by
    rw [← hQFun,← hMixedIntegral]
    exact hRemFour
  have hEI0 : 0 ≤ ∫ x,energy x := integral_nonneg (fun x => by
    have hbeta := actualReferenceBeta_pos g hg L q dr Ar p hL hdr hAr hp x
    exact mul_nonneg (referenceDensityFamily_pos g hg L (q,x)).le
      (finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q _ hbeta.le F x))
  have hCremBound : CPP+CM+CQ+CD ≤ Crem := by dsimp only [Crem]; linarith
  have hRemBound : |REM dr Ar p hdr hAr q F| ≤ Crem*eta*(∫ x,energy x) := by
    have hm : |∫ x,mixed x| ≤ CM*eta*(∫ x,energy x) := by rw [hMixedIntegral]; exact hMBound
    have hqbound : |∫ x,quartic x| ≤ CQ*eta*(∫ x,energy x) := by rw [hQuarticIntegral]; exact hQBound
    rw [hRemFour]
    calc
      _ ≤ |∫ x,pp x|+|∫ x,mixed x|+|∫ x,quartic x|+|∫ x,direct x| := abs_four_add_le _ _ _ _
      _ ≤ CPP*eta*(∫ x,energy x)+CM*eta*(∫ x,energy x)+CQ*eta*(∫ x,energy x)+CD*eta*(∫ x,energy x) :=
        add_le_add (add_le_add (add_le_add hPPBound hm) hqbound) hDBound
      _ = (CPP+CM+CQ+CD)*eta*(∫ x,energy x) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCremBound heta) hEI0
  exact ⟨hNSF,hNTF,hIP,hIR,hIZ,hIT,hIZ1,hIT1,hNative,hIL,hIE,hRemainder,
    hFirst,hIMF,hIMR,hQuartic,hIDF,hIDQ,hIDS,hID,hIPP,hIBR,hPhysical,hPPWeak,hRemIntegral,
    ⟨dQ,hdQ,PQ,hQGroup,hQPoint,hExpanded⟩,hRemBound⟩
local notation "MixedFacts" => ActualHigherSActualCubicBound.ActualMixedCubicWeakFacts
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "MixedWeak" => ActualHigherSActualCubicBound.actualMixedCubicWeakRemainder
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

/-- Complete row facts use the fixed mixed and quartic rooms exported before
all profile inputs, and retain the original physical six categories. -/
def CompleteLowerSSelfConclusions {dMix dQ : ℝ} (Pmix : ARoom dMix) (PQ : ARoom dQ)
    (Crem eta : ℝ) (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)
    (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD) : Prop :=
  PrimaryLowerSSelfConclusions g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
    Crem eta dr Ar p hdr hAr q F ∧
  MixedFacts Pmix g2 dr Ar p q F ∧
  Integrable (fun x => referenceDensityFamily g L (q,x)*QSUM PQ dr Ar p q F x) ∧
  (∀ x : R3,referenceDensityFamily g L (q,x)*
    (‖KL (Z2 g2 dr Ar p q F x)‖^2-‖KL (T2 g2 dr Ar p q F x)‖^2)=
    referenceDensityFamily g L (q,x)*QSUM PQ dr Ar p q F x) ∧
  REM dr Ar p hdr hAr q F=
    (∫ x,∑ l : Fin 3,∑ k : Fin 3,BR dr Ar p q F x l k)+
    (∫ x,MixedWeak Pmix g2 dr Ar p q F x)+
    (∫ x,referenceDensityFamily g L (q,x)*QSUM PQ dr Ar p q F x)+
    (∫ x,referenceDensityFamily g L (q,x)*DR dr Ar p q F x)

/-- Positive constants and fixed mixed/quartic rooms precede every profile/input. -/
def CompleteLowerSSelfContract : Prop :=
  ∃ Crem etaRem dMix dQ : ℝ,0 < dMix ∧ 0 < dQ ∧
  ∃ Pmix : ARoom dMix,∃ PQ : ARoom dQ,
  0 < Crem ∧ 0 < etaRem ∧ etaRem ≤ data.eta0 ∧
  ∀ q ∈ Icc (0 : ℝ) 1,
  ∀ dr : ℝ,∀ hdr : 0 < dr,dr ≤ 1 → ∀ Ar : ℝ,∀ hAr : 0 < Ar,
  ∀ p : ℕ,1 ≤ p → ∀ eta : ℝ,0 ≤ eta → eta ≤ etaRem →
  ∀ K : Set R3,IsCompact K → K ⊆ ball y0 ρ →
  ∀ F : smoothCompactFiniteSphereCore hO hD,tsupport F.val ⊆ K →
  (∀ x ∈ K,1 ≤ actualReferenceBeta g L q dr Ar p x) →
  (∀ x ∈ K,referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
  CompleteLowerSSelfConclusions g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
    Pmix PQ Crem eta dr Ar p hdr hAr q F

/-- Complete original-data producer with uniformly exported mixed/quartic rooms. -/
theorem exists_original_lower_s_self_remainder (hL : 0 < L)
    (hKernel : UnitBallValueTraceKernel τ0) (hg2 : IsAdmissibleMetric g2) :
    CompleteLowerSSelfContract g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
 := by
  obtain ⟨Crem,etaPrimary,hCrem,hetaPrimary,hetaPrimary0,hPrimary⟩ :=
    exists_original_lower_s_self_primary_remainder
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hL hKernel hg2
  obtain ⟨dMix,hdMix,Pmix,CMix,etaMix,hCMix,hetaMix,hetaMix0,hMixedWeak⟩ :=
    ActualHigherSActualCubicBound.exists_uniform_same_packet_actual_mixed_cubic_weak_bound
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hL hKernel g2 hg2
  obtain ⟨dQ,hdQ,_hdQD,PQ,dI,hdI,hdIQ,_hdI0,_hdIrho,hQuarticIdentity⟩ :=
    ActualHigherSQuadraticZeroQuartic.exists_same_packet_actual207_word_identity
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hKernel g2
  obtain ⟨epsQ,hepsQ,_hepsQ1,hGuardQ⟩ := exists_uniform_strict_higherSParam_guard
    g hg L hL y0 ρ dI hdI (closedBall y0 ρ) (isCompact_closedBall _ _)
  refine ⟨Crem,min etaPrimary (min etaMix epsQ),dMix,dQ,hdMix,hdQ,Pmix,PQ,hCrem,
    lt_min hetaPrimary (lt_min hetaMix hepsQ),(min_le_left _ _).trans hetaPrimary0,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaRem K hK hKball F hsupp hb hs
  have hePrimary : eta ≤ etaPrimary := hetaRem.trans (min_le_left _ _)
  have heMixed : eta ≤ etaMix := hetaRem.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heGuard : eta ≤ epsQ := hetaRem.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hP : PrimaryLowerSSelfConclusions
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
      Crem eta dr Ar p hdr hAr q F :=
    hPrimary q hq dr hdr hdr1 Ar hAr p hp eta heta hePrimary K hK hKball F hsupp hb hs
  have hW : MixedFacts Pmix g2 dr Ar p q F :=
    (hMixedWeak q hq dr hdr hdr1 Ar hAr p hp eta heta heMixed K hK hKball F hsupp hb hs).1
  refine ⟨hP,hW,?_⟩
  rcases hP with ⟨_h01,_h02,_h03,_h04,_h05,_h06,_h07,_h08,_h09,_h10,_h11,_h12,
    _h13,_h14,_h15,_h16,_h17,_h18,_h19,_h20,_h21,_h22,_h23,_h24,_h25,hQuartic,_h27⟩
  obtain ⟨dQOld,hdQOld,PQOld,hQOldInt,hQOldPoint,hExpanded⟩ := hQuartic
  have hTI : ∀ x ∈ tsupport F.val,(Tq dr Ar p q) x ∈ ParamRoom dI := by
    intro x hx
    have hxK := hsupp hx
    have hguard := hGuardQ q hq dr hdr hdr1 Ar hAr p hp eta heta heGuard x
      (ball_subset_closedBall (hKball hxK)) (hKball hxK) (hb x hxK) (hs x hxK)
    exact (higherSParam_eventually_mem y0 ρ dI L dr Ar q p hdr hAr x hguard).self_of_nhds
  have hQPoint (x : R3) : referenceDensityFamily g L (q,x)*
      (‖KL (Z2 g2 dr Ar p q F x)‖^2-‖KL (T2 g2 dr Ar p q F x)‖^2)=
      referenceDensityFamily g L (q,x)*QSUM PQ dr Ar p q F x :=
    congrArg (fun t : ℝ => referenceDensityFamily g L (q,x)*t)
      (hQuarticIdentity dr Ar p hdr hAr q F hTI x)
  have hQOldNew : (fun x => referenceDensityFamily g L (q,x)*QSUM PQOld dr Ar p q F x)=
      (fun x => referenceDensityFamily g L (q,x)*QSUM PQ dr Ar p q F x) := by
    funext x
    exact (hQOldPoint x).symm.trans (hQPoint x)
  have hQInt : Integrable (fun x => referenceDensityFamily g L (q,x)*QSUM PQ dr Ar p q F x) :=
    hQOldNew ▸ hQOldInt
  have hQIntegral : (∫ x,referenceDensityFamily g L (q,x)*QSUM PQOld dr Ar p q F x)=
      (∫ x,referenceDensityFamily g L (q,x)*QSUM PQ dr Ar p q F x) :=
    congrArg (fun f : R3 → ℝ => ∫ x,f x) hQOldNew
  rw [hQIntegral] at hExpanded
  refine ⟨hQInt,hQPoint,?_⟩
  have hMixedEquality :
      2*((∫ x,referenceDensityFamily g L (q,x)*
        ⟪PF g2 dr Ar p q F x,KL (Z2 g2 dr Ar p q F x)⟫_ℝ)-
      (∫ x,referenceDensityFamily g L (q,x)*
        ⟪PR g2 dr Ar p q F x,KL (T2 g2 dr Ar p q F x)⟫_ℝ))=
      (∫ x,MixedWeak Pmix g2 dr Ar p q F x) := hW.integral_identity
  have hReplace := congrArg
    (fun t : ℝ => (∫ x,∑ l : Fin 3,∑ k : Fin 3,BR dr Ar p q F x l k)+t+
      (∫ x,referenceDensityFamily g L (q,x)*QSUM PQ dr Ar p q F x)+
      (∫ x,referenceDensityFamily g L (q,x)*DR dr Ar p q F x)) hMixedEquality
  exact hExpanded.trans hReplace

/-- The original whole signed physical integral is its leading integral plus
its exact original lower S-self remainder, with the same retained packet. -/
lemma integral_originalSignedNormDensity_eq_leading_add_remainder
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) :
    (∫ x,referenceDensityFamily g L (q,x)*
      originalSignedNormDensity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        Room hreg data g2 dr Ar p hdr hAr q F x) =
    (∫ x,originalLeadingDensity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 dr Ar p q F x) +
    originalLowerSSelfRemainder g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 dr Ar p hdr hAr q F := by
  unfold originalLowerSSelfRemainder
  ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerSSelfRemainder
