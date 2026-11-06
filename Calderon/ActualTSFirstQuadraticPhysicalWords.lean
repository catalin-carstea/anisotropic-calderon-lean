import Calderon.ActualTSFirstLinearZeroIntegral
import Calderon.ActualTSFirstQuadraticTriple
import Calderon.ActualTSFirstQuadraticScalarJets

/-! Exact original quadratic D10 physical-to-word dictionary.
Before-code: ../T-S-first-quadratic-physical-words-before-source-nov04-day-v001/.
No energy estimate or finite angular S output is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstQuadraticPhysicalWords
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualAllAngularAtomGainedRoom
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ConformalDepth
  ActualHigherSQuadraticZeroWords ActualHigherSQuadraticZeroQuartic
  ActualTSFirstQuadraticScalarJets ActualTFirstPhysicalDictionary PrincipalCommutator
  ReferenceDensityBounds ReferenceWeightedApproximation SmoothMetricFrame MovingFrameConnection

private lemma pairing_two_first_sums {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : E →L[ℝ] F →L[ℝ] ℝ) (a : Fin 3 → Fin 3 → ℝ)
    (u : Fin 3 → Fin 3 → E) (c : ZeroWord → ℝ) (v : ZeroWord → F) :
    P (∑ l : Fin 3, ∑ i : Fin 3, a l i • u l i) (∑ z : ZeroWord, c z • v z) =
      ∑ l : Fin 3, ∑ i : Fin 3, ∑ z : ZeroWord, (a l i*c z)*P (u l i) (v z) := by
  simp only [map_sum,map_smul,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro z _
  ring

private lemma pairing_four_first_sums {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : E →L[ℝ] F →L[ℝ] ℝ) (a : Fin 3 → Fin 3 → ℝ)
    (u v : Fin 3 → Fin 3 → E) (c : ZeroWord → ℝ) (z r : ZeroWord → F) :
    4*P (∑ l : Fin 3, ∑ i : Fin 3, a l i • u l i) (∑ k : ZeroWord, c k • z k)-
      4*P (-(∑ l : Fin 3, ∑ i : Fin 3, a l i • v l i)) (∑ k : ZeroWord, c k • r k) =
      4*∑ l : Fin 3, ∑ i : Fin 3, ∑ k : ZeroWord,
        (a l i*c k)*(P (u l i) (z k)+P (v l i) (r k)) := by
  simp only [map_neg,ContinuousLinearMap.neg_apply,mul_neg,sub_neg_eq_add]
  rw [pairing_two_first_sums P a u c z,pairing_two_first_sums P a v c r]
  simp only [mul_add,Finset.sum_add_distrib]

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PL" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
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


local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Tq" => ActualHigherSFormation.higherSParam L
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "AH" => angularAtomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "AL" => angularAtomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RH" => angularAtomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RL" => angularAtomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "MAH" => atomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "MAL" => atomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "MRH" => atomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "MRL" => atomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "VA" => actualAtomHi g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "VB" => actualReverseAtomHi g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "Z2" => actualZ2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "T2" => actualT2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "WC" => actualWordCoefficient g L
local notation "TF" => referenceFirstHalf hO hD hF g L
local notation "TD" => referenceAdjointFirstHalf hO hD hF g L
local notation "QD" => ActualTSFirstLinearZeroPointwise.firstQuadraticZeroCrossDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
local notation "CRoom" d:max => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs d

attribute [local irreducible] angularAtomHigh angularAtomLow angularAtomReverseHigh angularAtomReverseLow
  atomHigh atomLow atomReverseHigh atomReverseLow actualAtomHi actualReverseAtomHi
  actualZ2Half actualT2Half ActualHigherSFormation.higherSInput
  ActualHigherSScalarCommutatorNativeForm.halfDualPairingL

/-- Original physical quadratic halves have the exact original ordered negative graphs.
Only already-proved original finite INPUT lift inclusions are used. -/
theorem original_quadratic_zero_negative_graphs
    {dA : ℝ} (P : ARoom dA) (dF : ℝ) (Cm : CRoom dF)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ y ∈ tsupport F.val, (Tq dr Ar p q) y ∈ ParamRoom dF)
    (x : R3) (hxA : (Tq dr Ar p q) x ∈ ParamRoom dA) :
    JL (Z2 g2 dr Ar p q F x) =
      ∑ z : ZeroWord, WC g2 dr Ar p q x z •
        AL ((Tq dr Ar p q) x) (wordAtoms z).1
          (AH ((Tq dr Ar p q) x) (wordAtoms z).2 (UF F x)) ∧
    JL (T2 g2 dr Ar p q F x) =
      ∑ z : ZeroWord, WC g2 dr Ar p q x z •
        RL ((Tq dr Ar p q) x) (wordAtoms z).2
          (RH ((Tq dr Ar p q) x) (wordAtoms z).1 (UF F x)) := by
  have hLift := actualAtomHi_inclusions g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    Room hreg data dF Cm dr Ar p hdr hAr q F hT x
  constructor
  · rw [actualZ2Half_eq_sum g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 dr Ar p q F x]
    simp only [map_sum,map_smul]
    apply Finset.sum_congr rfl
    intro z _
    apply congrArg (fun v : Neg => WC g2 dr Ar p q x z • v)
    calc
      _ = MAL ((Tq dr Ar p q) x) (wordAtoms z).1
          (IH (VA dr Ar p q F x (wordAtoms z).2)) :=
        ActualHigherSZeroAtomTransport.atom_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          Room hreg data P ((Tq dr Ar p q) x) hxA (wordAtoms z).1 _
      _ = MAL ((Tq dr Ar p q) x) (wordAtoms z).1
          (MAH ((Tq dr Ar p q) x) (wordAtoms z).2 (UF F x)) :=
        congrArg (MAL ((Tq dr Ar p q) x) (wordAtoms z).1) (hLift.1 (wordAtoms z).2)
      _ = _ := by
        have hLo : MAL ((Tq dr Ar p q) x) (wordAtoms z).1 =
            AL ((Tq dr Ar p q) x) (wordAtoms z).1 :=
          ActualHigherSZeroAtomDictionary.atomLow_eq_angularAtomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
            ((Tq dr Ar p q) x) (wordAtoms z).1
        have hHi : MAH ((Tq dr Ar p q) x) (wordAtoms z).2 =
            AH ((Tq dr Ar p q) x) (wordAtoms z).2 :=
          ActualHigherSZeroAtomDictionary.atomHigh_eq_angularAtomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
            ((Tq dr Ar p q) x) (wordAtoms z).2
        exact congrArg₂ (fun (D : Half →L[ℝ] Neg) (A : Hi →L[ℝ] Half) => D (A (UF F x))) hLo hHi
  · rw [actualT2Half_eq_sum g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 dr Ar p q F x]
    simp only [map_sum,map_smul]
    apply Finset.sum_congr rfl
    intro z _
    apply congrArg (fun v : Neg => WC g2 dr Ar p q x z • v)
    calc
      _ = MRL ((Tq dr Ar p q) x) (wordAtoms z).2
          (IH (VB dr Ar p q F x (wordAtoms z).1)) :=
        ActualHigherSZeroAtomTransport.reverse_atom_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          Room hreg data P ((Tq dr Ar p q) x) hxA (wordAtoms z).2 _
      _ = MRL ((Tq dr Ar p q) x) (wordAtoms z).2
          (MRH ((Tq dr Ar p q) x) (wordAtoms z).1 (UF F x)) :=
        congrArg (MRL ((Tq dr Ar p q) x) (wordAtoms z).2) (hLift.2 (wordAtoms z).1)
      _ = _ := by
        have hLo : MRL ((Tq dr Ar p q) x) (wordAtoms z).2 =
            RL ((Tq dr Ar p q) x) (wordAtoms z).2 :=
          ActualHigherSZeroAtomDictionary.atomReverseLow_eq_angularAtomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
            ((Tq dr Ar p q) x) (wordAtoms z).2
        have hHi : MRH ((Tq dr Ar p q) x) (wordAtoms z).1 =
            RH ((Tq dr Ar p q) x) (wordAtoms z).1 :=
          ActualHigherSZeroAtomDictionary.atomReverseHigh_eq_angularAtomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
            ((Tq dr Ar p q) x) (wordAtoms z).1
        exact congrArg₂ (fun (D : Half →L[ℝ] Neg) (A : Hi →L[ℝ] Half) => D (A (UF F x))) hLo hHi

/-- The exact odd triple sum from the original physical quadratic D10 row.
The raw adjoint FIRST minus sign makes the reverse triple a PLUS here. -/
def originalQuadraticFirstWordDensity (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  4*∑ l : Fin 3, ∑ i : Fin 3, ∑ z : ZeroWord,
    firstQuadraticWordWeight g L g2 q dr Ar p i l z x*
      (PL (raisingHigh hF hO hD i (directionalFDeriv (coordinateDirection l) (UF F) x))
        (AL ((Tq dr Ar p q) x) (wordAtoms z).1
          (AH ((Tq dr Ar p q) x) (wordAtoms z).2 (UF F x)))+
       PL (loweringHigh hF hO hD i (directionalFDeriv (coordinateDirection l) (UF F) x))
        (RL ((Tq dr Ar p q) x) (wordAtoms z).2
          (RH ((Tq dr Ar p q) x) (wordAtoms z).1 (UF F x))))
local notation "WD" => originalQuadraticFirstWordDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

/-- Literal physical D10 quadratic density equals its original word sum at every
admissible point, with factor4, original coefficients and reverse order intact. -/
theorem original_first_quadratic_cross_eq_words_at
    {dA : ℝ} (P : ARoom dA) (dF : ℝ) (Cm : CRoom dF)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ y ∈ tsupport F.val, (Tq dr Ar p q) y ∈ ParamRoom dF)
    (x : R3) (hxA : (Tq dr Ar p q) x ∈ ParamRoom dA) :
    QD g2 dr Ar p q F x = WD g2 dr Ar p q F x := by
  have hGraph := original_quadratic_zero_negative_graphs hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    Room hreg data P dF Cm g2 dr Ar p hdr hAr q F hT x hxA
  have hFwd : ⟪KL (TF q (UF F) x),KL (Z2 g2 dr Ar p q F x)⟫_ℝ =
      PL (TF q (UF F) x)
        (∑ z : ZeroWord, WC g2 dr Ar p q x z •
          AL ((Tq dr Ar p q) x) (wordAtoms z).1
            (AH ((Tq dr Ar p q) x) (wordAtoms z).2 (UF F x))) :=
    (ActualHigherSZeroAtomTransport.half_pairing_inner hO hD
      (TF q (UF F) x) (Z2 g2 dr Ar p q F x)).symm.trans
        (congrArg (PL (TF q (UF F) x)) hGraph.1)
  have hRev : ⟪KL (TD q (UF F) x),KL (T2 g2 dr Ar p q F x)⟫_ℝ =
      PL (TD q (UF F) x)
        (∑ z : ZeroWord, WC g2 dr Ar p q x z •
          RL ((Tq dr Ar p q) x) (wordAtoms z).2
            (RH ((Tq dr Ar p q) x) (wordAtoms z).1 (UF F x))) :=
    (ActualHigherSZeroAtomTransport.half_pairing_inner hO hD
      (TD q (UF F) x) (T2 g2 dr Ar p q F x)).symm.trans
        (congrArg (PL (TD q (UF F) x)) hGraph.2)
  unfold ActualTSFirstLinearZeroPointwise.firstQuadraticZeroCrossDensity
  rw [hFwd,hRev]
  dsimp only [referenceFirstHalf,referenceAdjointFirstHalf,
    originalQuadraticFirstWordDensity,firstQuadraticWordWeight,directionalFDeriv]
  exact pairing_four_first_sums PL
    (fun l i => referenceMetricGramFrame g L (q,x) i l)
    (fun l i => raisingHigh hF hO hD i (fderiv ℝ (UF F) x (coordinateDirection l)))
    (fun l i => loweringHigh hF hO hD i (fderiv ℝ (UF F) x (coordinateDirection l)))
    (fun z => WC g2 dr Ar p q x z)
    (fun z => AL ((Tq dr Ar p q) x) (wordAtoms z).1
      (AH ((Tq dr Ar p q) x) (wordAtoms z).2 (UF F x)))
    (fun z => RL ((Tq dr Ar p q) x) (wordAtoms z).2
      (RH ((Tq dr Ar p q) x) (wordAtoms z).1 (UF F x)))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstQuadraticPhysicalWords
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstQuadraticPhysicalWords.original_quadratic_zero_negative_graphs
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSFirstQuadraticPhysicalWords.original_first_quadratic_cross_eq_words_at
