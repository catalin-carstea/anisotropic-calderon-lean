import Calderon.ActualTSZeroFirstLiteralWords
import Calderon.ActualTSZeroFirstScalarJets
import Calderon.ActualTSZeroFirstEnergyTools
import Calderon.ActualTSFirstQuadraticTriple
import Calderon.ActualTZeroCorrectionUniform

/-! The original D01 odd-triple errors and the entire raw correction are bounded
in the unchanged inclusion energy. No high derivative norm is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroFirstPointwise
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAllAngularAtomGainedRoom ActualTZeroGenuineReverse ActualTZeroCorrectionUniform
  ActualRetainedGeneratorMultiplierGains ActualReferenceZeroECommutators
  AmbientReferenceRaising ActualGeneratorEPairedGainedEndpoints
  ActualSFirstPhysicalDictionary ActualHigherSFormation ActualHigherSCoordinateWeightBounds
  ActualHigherSLeadingBracketGain
  ActualTSZeroFirstLiteralWords ActualTSZeroFirstScalarJets ActualTSZeroFirstEnergyTools
  ActualTSFirstQuadraticTriple ActualHigherSScalarCommutatorForm ActualHigherSZeroScalarCommutatorForm
  PrincipalCommutator ReferenceWeightedApproximation ReferenceDensityBounds ConformalDepth

private lemma scaled_pair_difference (a r b e omega : ℝ)
    (h : a+r=a+b-e) : omega*(a+r)-omega*(a+b) = -omega*e := by
  rw [h]
  ring

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PL" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def negDualNormed : NormedAddCommGroup (Neg →L[ℝ] ℝ) := inferInstance
@[instance_reducible] private def negDualSpace : NormedSpace ℝ (Neg →L[ℝ] ℝ) := inferInstance
attribute [local instance] negDualNormed negDualSpace
@[instance_reducible] private def highHalfNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def highHalfSpace : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def lowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
@[instance_reducible] private def lowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] highHalfNormed highHalfSpace lowNormed lowSpace
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
local notation "Tq" => higherSParam L
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "UF" => higherSInput hO hD
local notation "AH" => angularAtomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "AL" => angularAtomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RH" => angularAtomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RL" => angularAtomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Corr" => referenceZeroAdjointCorrection
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
local notation "WD" => zeroFirstWordDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "CD" => zeroFirstCorrectionDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data

/-- The exact symmetric part of one original D01 triple, without the outer four. -/
def zeroFirstSymmetricWordDensity (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ)
    (F : smoothCompactFiniteSphereCore hO hD) (k j i : Fin 3) (V : Generator) (x : R3) : ℝ :=
  let t := (Tq dr Ar p q) x
  let u := UF F x
  let v := fderiv ℝ (UF F) x (coordinateDirection k)
  zeroFirstWordWeight g L g2 q dr Ar p k j i V x *
    (PL (AH t (Sum.inl j) v)
      (AL t (Sum.inr (Sum.inr i)) (AH t (Sum.inr (Sum.inl V)) u))+
     PL (AH t (Sum.inl j) u)
      (AL t (Sum.inr (Sum.inr i)) (AH t (Sum.inr (Sum.inl V)) v)))
local notation "SD" => zeroFirstSymmetricWordDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  raisingHigh raisingLow loweringHigh loweringLow generatorHigh generatorLow
  generatorSharpHigh generatorSharpLow sphereSobolevInclusionL referenceZeroAdjointCorrection

private lemma radius_sq_beta_le (r beta eta : ℝ) (hr : 0 < r)
    (hb : 1 ≤ beta) (hs : r*beta^2 ≤ eta) (he : eta ≤ 1) : r^2*beta ≤ eta := by
  have hb2 : (1 : ℝ) ≤ beta^2 := by nlinarith only [hb]
  have hr1 : r ≤ 1 :=
    ((by simpa only [mul_one] using mul_le_mul_of_nonneg_left hb2 hr.le : r ≤ r*beta^2).trans hs).trans he
  have hrb : r ≤ beta := hr1.trans hb
  calc
    _ = r*beta*r := by ring
    _ ≤ r*beta*beta := mul_le_mul_of_nonneg_left hrb (mul_nonneg hr.le (zero_le_one.trans hb))
    _ = r*beta^2 := by ring
    _ ≤ eta := hs

/-- Both constants are produced from the original room and scalar factories,
before every later profile and finite input. This is an internal support layer. -/
theorem exists_original_zero_first_pointwise_row_bounds
    (hL : 0 < L) {d : ℝ} (P : ARoom d) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ Cword CcorrRow : ℝ, 0 < Cword ∧ 0 < CcorrRow ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 →
      ∀ x ∈ closedBall y0 ρ, (Tq dr Ar p q) x ∈ ParamRoom d →
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      ∀ F : smoothCompactFiniteSphereCore hO hD,
      (∀ k j i : Fin 3, ∀ V : Generator,
        |WD g2 q dr Ar p F k j i V x-SD g2 q dr Ar p F k j i V x| ≤
          Cword*eta*inclusionEnergyDensity IH (actualReferenceBeta g L q dr Ar p x) (UF F) x) ∧
      (∀ k j : Fin 3, |CD P g2 q dr Ar p F k j x| ≤
        CcorrRow*eta*inclusionEnergyDensity IH (actualReferenceBeta g L q dr Ar p x) (UF F) x) := by
  obtain ⟨Cw,hCw,hScalar⟩ := exists_actual_zero_first_word_scalar_first_caps g hg L hL y0 ρ g2 hg2
  obtain ⟨Cg,hCg,hTriple⟩ := exists_actual_uniform_three_word_symmetrization
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data P
  obtain ⟨CT,hCT,hCorr⟩ := exists_original_correction_uniform_beta_bound
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL P
      (closedBall y0 ρ) (isCompact_closedBall _ _)
  obtain ⟨M,hM,hAtoms,_hGains⟩ := P.finiteCaps 0
  let scalarWitness := exists_physical_firstCoordinateWeight_uniform_first_caps g g2 hg hg2 L y0 ρ
  let Ms := Classical.choose scalarWitness
  have hMs : 1 ≤ Ms := (Classical.choose_spec scalarWitness).1
  have hS := (Classical.choose_spec scalarWitness).2
  let Cword : ℝ := Cw*Cg
  let CcorrRow : ℝ := Ms*‖PL‖*CT*M+1
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hMs0 : 0 ≤ Ms := zero_le_one.trans hMs
  have hCC0 : 0 ≤ Ms*‖PL‖*CT*M := by positivity
  refine ⟨Cword,CcorrRow,mul_pos hCw hCg,by dsimp only [CcorrRow]; positivity,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hx ht hb hs F
  let beta := actualReferenceBeta g L q dr Ar p x
  let t := (Tq dr Ar p q) x
  let u := UF F
  let e := inclusionEnergyDensity IH beta u x
  have hbeta : 0 ≤ beta := zero_le_one.trans hb
  have he : 0 ≤ e := inclusionEnergyDensity_nonneg IH beta u x hbeta
  have hMixed (k : Fin 3) :
      ‖u x‖*‖IH (fderiv ℝ u x (coordinateDirection k))‖ ≤ e := by
    have h := inclusion_energy_mixed_le IH beta u x (zero_lt_one.trans_le hb) k
    calc
      _ = ‖IH (fderiv ℝ u x (coordinateDirection k))‖*‖u x‖ := mul_comm _ _
      _ ≤ e := h
  constructor
  · intro k j i V
    let a : AngularAtom := Sum.inl j
    let b : AngularAtom := Sum.inr (Sum.inr i)
    let c : AngularAtom := Sum.inr (Sum.inl V)
    let v := fderiv ℝ u x (coordinateDirection k)
    let omega := zeroFirstWordWeight g L g2 q dr Ar p k j i V x
    let G := PL (AH t c v) (JL (P.gainHigh b a t (u x)))+
      PL (RH t b (u x)) (JL (P.gainHigh a c t v))
    have hId := (hTriple t ht (u x) v a b c).1
    have hGain : |G| ≤ Cg*‖u x‖*‖IH v‖ := (hTriple t ht (u x) v a b c).2
    have hOmega : |omega| ≤ Cw*eta :=
      (hScalar q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hx hb hs k j i V).value
    have hDiff : WD g2 q dr Ar p F k j i V x-SD g2 q dr Ar p F k j i V x = -omega*G := by
      change omega*(PL (AH t a v) (AL t b (AH t c (u x)))+
        PL (RH t a v) (RL t c (RH t b (u x))))-
        omega*(PL (AH t a v) (AL t b (AH t c (u x)))+
          PL (AH t a (u x)) (AL t b (AH t c v))) = -omega*G
      exact scaled_pair_difference _ _ _ G omega hId
    rw [hDiff,abs_mul,abs_neg]
    calc
      _ ≤ (Cw*eta)*(Cg*‖u x‖*‖IH v‖) :=
        mul_le_mul hOmega hGain (abs_nonneg _) (mul_nonneg hCw.le heta)
      _ = (Cword*eta)*(‖u x‖*‖IH v‖) := by dsimp only [Cword]; ring
      _ ≤ Cword*eta*e := mul_le_mul_of_nonneg_left (hMixed k) (by dsimp only [Cword]; positivity)
  · intro k j
    let v := fderiv ℝ u x (coordinateDirection k)
    let s := firstCoordinateWeight g g2 L k j t
    let r := referenceRadius dr Ar p L x
    have hr : 0 < r := referenceRadius_pos dr Ar p L x hdr hAr
    have hrb : r^2*beta ≤ eta := radius_sq_beta_le r beta eta hr hb hs heta1
    have hS0 : |s| ≤ Ms := (hS q hq x hx dr Ar p k j).2.1
    have hC : ‖Corr P q dr Ar p x‖ ≤ CT*beta :=
      hCorr q hq dr hdr hdr1 Ar hAr p hp x hx ht hb
    have hRL : ‖RL t (Sum.inl j)‖ ≤ M := by
      simpa only [norm_iteratedFDerivWithin_zero] using (hAtoms (Sum.inl j) 0 le_rfl t ht).2.2.2
    have hGraph : JL (RH t (Sum.inl j) v)=RL t (Sum.inl j) (IH v) :=
      P.reverseAtomGraph (Sum.inl j) t ht v
    have hPair := abs_bilinear_actions_le PL (Corr P q dr Ar p x) (RL t (Sum.inl j))
      (u x) (IH v) (CT*beta) M (mul_nonneg hCT.le hbeta) hM0 hC hRL
    have hScale : |r^2*s| ≤ r^2*Ms := by
      rw [abs_mul,abs_of_nonneg (sq_nonneg r)]
      exact mul_le_mul_of_nonneg_left hS0 (sq_nonneg r)
    change |(r^2*s)*PL (Corr P q dr Ar p x (u x)) (JL (RH t (Sum.inl j) v))| ≤ CcorrRow*eta*e
    rw [hGraph,abs_mul]
    calc
      _ ≤ (r^2*Ms)*(‖PL‖*(CT*beta)*M*‖u x‖*‖IH v‖) :=
        mul_le_mul hScale hPair (abs_nonneg _) (mul_nonneg (sq_nonneg r) hMs0)
      _ = (Ms*‖PL‖*CT*M)*(r^2*beta)*(‖u x‖*‖IH v‖) := by ring
      _ ≤ (Ms*‖PL‖*CT*M)*eta*e :=
        mul_le_mul (mul_le_mul_of_nonneg_left hrb hCC0) (hMixed k)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg hCC0 heta)
      _ ≤ CcorrRow*eta*e := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by dsimp only [CcorrRow]; linarith : Ms*‖PL‖*CT*M ≤ CcorrRow) heta) he

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroFirstPointwise
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroFirstPointwise.exists_original_zero_first_pointwise_row_bounds
