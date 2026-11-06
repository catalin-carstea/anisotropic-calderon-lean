import Calderon.ActualTSFirstQuadraticPhysicalWords
import Calderon.ActualTSFirstQuadraticActualGreen
import Calderon.ActualTSFirstQuadraticGains
import Calderon.ActualHigherSQuadraticZeroQuarticRegularity

/-! Exact global original quadratic D10 symmetric-minus-both-gains split. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstQuadraticPhysicalSplit
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualAllAngularAtomGainedRoom
  ActualFiniteHarmonicCore ConformalDepth ReferenceDensityBounds ReferenceWeightedApproximation


local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "PL" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def highDualNormed :
    NormedAddCommGroup (Hi →L[ℝ] ℝ) := inferInstance
@[instance_reducible] private def highDualSpace :
    NormedSpace ℝ (Hi →L[ℝ] ℝ) := inferInstance
attribute [local instance] highDualNormed highDualSpace
attribute [local instance] ActualTSActualTripleRoomCaps.tripleCoefficientNormedGroup
  ActualTSActualTripleRoomCaps.tripleCoefficientNormedSpace

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



open MeasureTheory PrincipalCommutator ActualTSFirstQuadraticPhysicalWords
  ActualTSFirstQuadraticActualGreen ActualTSFirstQuadraticGains ActualTSFirstQuadraticTriple
  ActualTSFirstQuadraticScalarJets ActualHigherSQuadraticZeroWords
  ActualHigherSQuadraticZeroQuartic ActualHigherSQuadraticZeroQuarticBounds
  ActualHigherSZeroScalarNativeForm ActualTFirstPhysicalDictionary
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "Tq" => ActualHigherSFormation.higherSParam L
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "AH" => angularAtomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "AL" => angularAtomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RH" => angularAtomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RL" => angularAtomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "SD" => actualWeightedSymmetricDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "WG" => weightedOriginalTripleGain
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
local notation "QD" => ActualTSFirstLinearZeroPointwise.firstQuadraticZeroCrossDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
local notation "WD" => originalQuadraticFirstWordDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "CRoom" d:max => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs d
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "Z2" => actualZ2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "T2" => actualT2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

/-- The exact factor4 total of all original weighted symmetric first rows. -/
def originalQuadraticSymmetricTotal (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  4*∑ l : Fin 3, ∑ i : Fin 3, ∑ z : ZeroWord,
    SD g2 q dr Ar p F i l z (raisingAtom i) (wordAtoms z).1 (wordAtoms z).2 x
local notation "ST" => originalQuadraticSymmetricTotal
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

/-- The exact factor4 weighted total of BOTH genuine gains, to be subtracted. -/
def originalQuadraticGainTotal {d : ℝ} (P : ARoom d) (g2 : MatrixField)
    (q dr Ar : ℝ) (p : ℕ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  4*∑ l : Fin 3, ∑ i : Fin 3, ∑ z : ZeroWord,
    referenceDensityFamily g L (q,x)*WG P g2 q dr Ar p (UF F) i l z x
local notation "GT" => originalQuadraticGainTotal
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data

private lemma weighted_row_sum_identity (mu : ℝ)
    (f s r : Fin 3 → Fin 3 → ZeroWord → ℝ)
    (h : ∀ l i z, mu*f l i z=s l i z-r l i z) :
    mu*(4*∑ l : Fin 3, ∑ i : Fin 3, ∑ z : ZeroWord, f l i z)=
      4*(∑ l : Fin 3, ∑ i : Fin 3, ∑ z : ZeroWord, s l i z)-
        4*(∑ l : Fin 3, ∑ i : Fin 3, ∑ z : ZeroWord, r l i z) := by
  have hs : (∑ l : Fin 3, ∑ i : Fin 3, ∑ z : ZeroWord, mu*f l i z)=
      (∑ l : Fin 3, ∑ i : Fin 3, ∑ z : ZeroWord, s l i z)-
        (∑ l : Fin 3, ∑ i : Fin 3, ∑ z : ZeroWord, r l i z) := by
    simp only [h,Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum] at hs
  nlinarith only [hs]

attribute [local irreducible] angularAtomHigh angularAtomLow angularAtomReverseHigh
  angularAtomReverseLow ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
  ActualHigherSFormation.higherSInput
  actualWeightedSymmetricDensity weightedOriginalTripleGain
  originalQuadraticSymmetricTotal originalQuadraticGainTotal
  ActualTSFirstLinearZeroPointwise.firstQuadraticZeroCrossDensity
  originalQuadraticFirstWordDensity

private lemma weighted_scalar_row (mu w a b c g : ℝ) (h : a+b=a+c-g) :
    mu*(w*(a+b))=mu*(w*a+w*c)-mu*(w*g) := by
  have hm := congrArg (fun z : ℝ => mu*(w*z)) h
  nlinarith only [hm]

set_option diagnostics true in
private theorem actual_weighted_row_split_at
    {dA : ℝ} (P : ARoom dA) (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (hxA : (Tq dr Ar p q) x ∈ ParamRoom dA) (i l : Fin 3) (z : ZeroWord) :
    referenceDensityFamily g L (q,x)*
      (firstQuadraticWordWeight g L g2 q dr Ar p i l z x*
        (PL (raisingHigh hF hO hD i (directionalFDeriv (coordinateDirection l) (UF F) x))
          (AL ((Tq dr Ar p q) x) (wordAtoms z).1
            (AH ((Tq dr Ar p q) x) (wordAtoms z).2 (UF F x)))+
         PL (loweringHigh hF hO hD i (directionalFDeriv (coordinateDirection l) (UF F) x))
          (RL ((Tq dr Ar p q) x) (wordAtoms z).2
            (RH ((Tq dr Ar p q) x) (wordAtoms z).1 (UF F x)))))=
      SD g2 q dr Ar p F i l z (raisingAtom i) (wordAtoms z).1 (wordAtoms z).2 x-
        referenceDensityFamily g L (q,x)*WG P g2 q dr Ar p (UF F) i l z x := by
  let pairWitness := exists_actual_uniform_three_word_symmetrization
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data P
  have hPair := (Classical.choose_spec pairWitness).2
  have hSym := (hPair ((Tq dr Ar p q) x) hxA (UF F x)
    (directionalFDeriv (coordinateDirection l) (UF F) x)
    (raisingAtom i) (wordAtoms z).1 (wordAtoms z).2).1
  have hRaise : AH ((Tq dr Ar p q) x) (raisingAtom i)=raisingHigh hF hO hD i := by
    simp only [angularAtomHigh,raisingAtom]
  have hLower : RH ((Tq dr Ar p q) x) (raisingAtom i)=loweringHigh hF hO hD i := by
    simp only [angularAtomReverseHigh,raisingAtom]
  have hForward := congrArg
    (fun A : Hi →L[ℝ] Half =>
      PL (A (directionalFDeriv (coordinateDirection l) (UF F) x))
        (AL ((Tq dr Ar p q) x) (wordAtoms z).1
          (AH ((Tq dr Ar p q) x) (wordAtoms z).2 (UF F x)))) hRaise
  have hReverse := congrArg
    (fun A : Hi →L[ℝ] Half =>
      PL (A (directionalFDeriv (coordinateDirection l) (UF F) x))
        (RL ((Tq dr Ar p q) x) (wordAtoms z).2
          (RH ((Tq dr Ar p q) x) (wordAtoms z).1 (UF F x)))) hLower
  have hLeft := congrArg (fun t : ℝ => referenceDensityFamily g L (q,x)*
    (firstQuadraticWordWeight g L g2 q dr Ar p i l z x*t))
      (congrArg₂ (fun a b : ℝ => a+b) hForward hReverse)
  have hSD :
      SD g2 q dr Ar p F i l z (raisingAtom i) (wordAtoms z).1 (wordAtoms z).2 x=
      referenceDensityFamily g L (q,x)*
        (firstQuadraticWordWeight g L g2 q dr Ar p i l z x*
          PL (AH ((Tq dr Ar p q) x) (raisingAtom i) (directionalFDeriv (coordinateDirection l) (UF F) x))
            (AL ((Tq dr Ar p q) x) (wordAtoms z).1
              (AH ((Tq dr Ar p q) x) (wordAtoms z).2 (UF F x)))+
         firstQuadraticWordWeight g L g2 q dr Ar p i l z x*
          PL (AH ((Tq dr Ar p q) x) (raisingAtom i) (UF F x))
            (AL ((Tq dr Ar p q) x) (wordAtoms z).1
              (AH ((Tq dr Ar p q) x) (wordAtoms z).2
                (directionalFDeriv (coordinateDirection l) (UF F) x)))) := by
    unfold actualWeightedSymmetricDensity
    rfl
  have hGainDef :
      WG P g2 q dr Ar p (UF F) i l z x=
      firstQuadraticWordWeight g L g2 q dr Ar p i l z x*
        (PL (AH ((Tq dr Ar p q) x) (wordAtoms z).2
            (directionalFDeriv (coordinateDirection l) (UF F) x))
          (JL (P.gainHigh (wordAtoms z).1 (raisingAtom i) ((Tq dr Ar p q) x) (UF F x)))+
         PL (RH ((Tq dr Ar p q) x) (wordAtoms z).1 (UF F x))
          (JL (P.gainHigh (raisingAtom i) (wordAtoms z).2 ((Tq dr Ar p q) x)
            (directionalFDeriv (coordinateDirection l) (UF F) x)))) := by
    unfold weightedOriginalTripleGain
    rfl
  have hAlg := weighted_scalar_row (referenceDensityFamily g L (q,x))
    (firstQuadraticWordWeight g L g2 q dr Ar p i l z x) _ _ _ _ hSym
  have hBoundary := congrArg₂
    (fun s r : ℝ => s-referenceDensityFamily g L (q,x)*r) hSD hGainDef
  exact hLeft.symm.trans (hAlg.trans hBoundary.symm)

/-- Original weighted density equals the symmetric total minus BOTH gain totals
at each admissible point, preserving the literal factor4 and all word orders. -/
theorem original_quadratic_weighted_split_at
    {dA : ℝ} (P : ARoom dA) (dF : ℝ) (Cm : CRoom dF)
    (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ y ∈ tsupport F.val, (Tq dr Ar p q) y ∈ ParamRoom dF)
    (x : R3) (hxA : (Tq dr Ar p q) x ∈ ParamRoom dA) :
    referenceDensityFamily g L (q,x)*QD g2 dr Ar p q F x=
      ST g2 q dr Ar p F x-GT P g2 q dr Ar p F x := by
  have hW := original_first_quadratic_cross_eq_words_at
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
    P dF Cm g2 dr Ar p hdr hAr q F hT x hxA
  rw [hW]
  unfold originalQuadraticFirstWordDensity originalQuadraticSymmetricTotal originalQuadraticGainTotal
  apply weighted_row_sum_identity
  intro l i z
  exact actual_weighted_row_split_at hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    Room hreg data P g2 q dr Ar p F x hxA i l z

/-- The same literal split holds globally, including outside the input support. -/
theorem original_quadratic_weighted_split
    {dA : ℝ} (P : ARoom dA) (dF : ℝ) (Cm : CRoom dF)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (q dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (F : smoothCompactFiniteSphereCore hO hD)
    (hA : ∀ y ∈ tsupport F.val, (Tq dr Ar p q) y ∈ ParamRoom dA)
    (hT : ∀ y ∈ tsupport F.val, (Tq dr Ar p q) y ∈ ParamRoom dF) :
    ∀ x, referenceDensityFamily g L (q,x)*QD g2 dr Ar p q F x=
      ST g2 q dr Ar p F x-GT P g2 q dr Ar p F x := by
  have hReg := actualZ2T2_contDiff_support
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    dF Cm g2 hg2 dr Ar p hdr hAr q F hT
  intro x
  by_cases hx : x ∈ tsupport F.val
  · exact original_quadratic_weighted_split_at hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      Room hreg data P dF Cm g2 q dr Ar p hdr hAr F hT x (hA x hx)
  · have hU : UF F x=0 := highInput_eq_zero_off hO hD F x hx
    have hZ : Z2 g2 dr Ar p q F x=0 := by
      by_contra hn
      exact hx (hReg.2.2.1 (subset_closure hn))
    have hR : T2 g2 dr Ar p q F x=0 := by
      by_contra hn
      exact hx (hReg.2.2.2 (subset_closure hn))
    have hS0 (i l : Fin 3) (z : ZeroWord) :
        SD g2 q dr Ar p F i l z (raisingAtom i) (wordAtoms z).1 (wordAtoms z).2 x=0 := by
      simp only [actualWeightedSymmetricDensity,ActualTSSymmetricFirstGreen.symmetricFirstDensity,
        hU,map_zero,zero_apply,mul_zero,add_zero]
    have hG0 (i l : Fin 3) (z : ZeroWord) :
        WG P g2 q dr Ar p (UF F) i l z x=0 := by
      simp only [weightedOriginalTripleGain,hU,map_zero,zero_apply,mul_zero,add_zero]
    simp only [ActualTSFirstLinearZeroPointwise.firstQuadraticZeroCrossDensity,hZ,hR,
      map_zero,inner_zero_right,mul_zero,sub_self,originalQuadraticSymmetricTotal,
      originalQuadraticGainTotal,hS0,hG0,Finset.sum_const_zero]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstQuadraticPhysicalSplit
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstQuadraticPhysicalSplit.original_quadratic_weighted_split_at
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstQuadraticPhysicalSplit.original_quadratic_weighted_split
