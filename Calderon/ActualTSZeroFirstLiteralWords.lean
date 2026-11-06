import Calderon.ActualTSLowerZeroZeroBinding
import Calderon.ActualTZeroGenuineReverse
import Calderon.ActualReferenceZeroECommutators

/-! Exact original D01 physical-to-word dictionary. Third-owned successor.
Before-code: ../UPFRONT.md, exact statement: ../TARGET-SPEC.txt.
All 270 triple occurrences and all nine full raw correction pairings remain.
No analytic norm estimate or assumed high derivative norm is introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroFirstLiteralWords
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAllAngularAtomGainedRoom ActualTZeroGenuineReverse ActualReferenceZeroECommutators
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ActualTZeroNegativeGraph ActualTZeroWordRealization ActualTSZeroLiteralPointwise
  ActualSFirstPhysicalDictionary ActualHigherSFormation AmbientReferenceRaising
  ActualHigherSLeadingBracketGain ActualHigherSAdjointLeadingCoordinate
  ActualHigherSPhysicalPairing PrincipalCommutator
  ConformalDepth ReferenceDensityBounds SmoothMetricFrame MovingFrameConnection

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "DL" => sphereSobolevShiftedDegreeL (3/2 : ℝ)
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
local notation "Tq" => higherSParam L
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "UF" => higherSInput hO hD
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "cc" => referenceAngularZeroCoefficient g L
local notation "AH" => angularAtomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "AL" => angularAtomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RH" => angularAtomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RL" => angularAtomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Corr" => referenceZeroAdjointCorrection
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
local notation "S1" => referenceSFirstHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Sd1" => referenceSAdjointFirstHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "D01" => ActualTSLowerZeroZeroBinding.originalZeroFirstCrossDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

/-- A literal member of the 3*3*3*10 original word/coordinate list, without factor four. -/
def zeroFirstWordDensity (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ)
    (F : smoothCompactFiniteSphereCore hO hD) (k j i : Fin 3) (V : Generator) (x : R3) : ℝ :=
  let t := (Tq dr Ar p q) x
  let u := UF F x
  let v := fderiv ℝ (UF F) x (coordinateDirection k)
  ((referenceRadius dr Ar p L x)^2*firstCoordinateWeight g g2 L k j t*cc q dr Ar p x i V)*
    (PL (AH t (Sum.inl j) v)
      (AL t (Sum.inr (Sum.inr i)) (AH t (Sum.inr (Sum.inl V)) u))+
     PL (RH t (Sum.inl j) v)
      (RL t (Sum.inr (Sum.inl V)) (RH t (Sum.inr (Sum.inr i)) u)))

/-- One of nine pairings of the ENTIRE original 30-gain plus three minus-fi correction. -/
def zeroFirstCorrectionDensity {d : ℝ} (P : ARoom d) (g2 : MatrixField)
    (q dr Ar : ℝ) (p : ℕ) (F : smoothCompactFiniteSphereCore hO hD)
    (k j : Fin 3) (x : R3) : ℝ :=
  ((referenceRadius dr Ar p L x)^2*
    firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) x))*
    PL (Corr P q dr Ar p x (UF F x))
      (JL (RH ((Tq dr Ar p q) x) (Sum.inl j)
        (fderiv ℝ (UF F) x (coordinateDirection k))))

local notation "WD" => zeroFirstWordDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "CD" => zeroFirstCorrectionDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data

attribute [local irreducible] nativeReferenceZeroCoefficient nativeReferenceAdjointZeroCoefficient
  sphereSobolevInclusionL sphereSobolevHalfToSphereL2L referenceZeroAdjointCorrection
attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  raisingHigh raisingLow loweringHigh loweringLow generatorHigh generatorLow
  generatorSharpHigh generatorSharpLow

private lemma decode_native_half (G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    KL (finiteCoreSobolevLift hO hD (1/2 : ℝ) G x)=G.val x := by
  have h := halfToSphereL2_finiteCoreLift hO hD G x
  rw [sphereSobolevInclusionL_finiteCoreSobolevLift] at h
  exact h

private lemma native_half_pair (G : smoothCompactFiniteSphereCore hO hD) (x : R3) (z : Half) :
    ⟪G.val x,KL z⟫_ℝ=PL z (JL (finiteCoreSobolevLift hO hD (1/2 : ℝ) G x)) := by
  calc
    _ = ⟪KL (finiteCoreSobolevLift hO hD (1/2 : ℝ) G x),KL z⟫_ℝ :=
      congrArg (fun v => ⟪v,KL z⟫_ℝ) (decode_native_half hO hD G x).symm
    _ = _ := by
      rw [ActualHigherSZeroAtomTransport.half_pairing_inner hO hD]
      exact real_inner_comm _ _

private lemma mixed_weighted_pairing {E F ι κ : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Fintype ι] [Fintype κ]
    (P : E →L[ℝ] F →L[ℝ] ℝ) (c : ι → ℝ) (d : κ → ℝ) (A : ι → E) (X : κ → F) :
    P (∑ i, c i • A i) (∑ k, d k • X k) =
      ∑ i, ∑ k, (c i*d k)*P (A i) (X k) := by
  have hLeft (y : F) : P (∑ i, c i • A i) y=∑ i, c i*P (A i) y := by
    change P.flip y (∑ i, c i • A i)=_
    simp only [map_sum,map_smul,smul_eq_mul,ContinuousLinearMap.flip_apply]
  rw [hLeft]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_sum,map_smul,smul_eq_mul,Finset.mul_sum,mul_assoc]

private lemma weighted_pairing_sums {E F ι κ : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Fintype ι] [Fintype κ]
    (P : E →L[ℝ] F →L[ℝ] ℝ) (J : E →L[ℝ] F) (r : ℝ)
    (c : ι → ℝ) (d : κ → ℝ) (A B : ι → E) (X Y : κ → F) (z : E)
    (hSym : ∀ y : E, P y (J z)=P z (J y)) :
    P (r • ∑ i, c i • A i) (∑ k, d k • X k)-
      P (-(r • ∑ i, c i • B i)) ((∑ k, d k • Y k)+J z) =
      r*(∑ i, ∑ k, (c i*d k)*(P (A i) (X k)+P (B i) (Y k)))+
      r*(∑ i, c i*P z (J (B i))) := by
  have hf := mixed_weighted_pairing P c d A X
  have hr := mixed_weighted_pairing P c d B Y
  have hc : P (∑ i, c i • B i) (J z)=∑ i, c i*P z (J (B i)) := by
    change P.flip (J z) (∑ i, c i • B i)=_
    simp only [map_sum,map_smul,smul_eq_mul,ContinuousLinearMap.flip_apply,hSym]
  simp only [map_smul,map_neg,map_add,_root_.smul_apply,_root_.neg_apply,
    smul_eq_mul,neg_mul,sub_neg_eq_add]
  rw [hf,hr,hc]
  simp only [mul_add,Finset.mul_sum,Finset.sum_add_distrib,mul_assoc]
  ring

private lemma forward_negative_words (q dr Ar : ℝ) (p : ℕ) (x : R3) (U : Hi) :
    referenceZeroNegative hO hD hF g L q dr Ar p x U =
      ∑ i : Fin 3, ∑ V : Generator, cc q dr Ar p x i V •
        raisingLow hF hO hD i (generatorHigh V U) := by
  have hFactor (i : Fin 3) :
      (referenceHighHorizontalAngularL g L q x i+
        referenceFrameDerivative g L q i (fun y => Real.log (referenceRadius dr Ar p L y)) x • DL) U =
        ∑ V : Generator, cc q dr Ar p x i V • generatorHigh V U := by
    have h := congrArg (fun A : Hi →L[ℝ] Half => A U)
      (referenceAngularHigh_eq g L q dr Ar p x i)
    exact h.symm.trans (by
      simp only [referenceAngularHigh,_root_.sum_apply,_root_.smul_apply])
  simp only [referenceZeroNegative,_root_.sum_apply,ContinuousLinearMap.comp_apply]
  simp_rw [hFactor]
  simp only [map_sum,map_smul]

private lemma half_pairing_symmetric
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (z y : Half) : PL z (JL y)=PL y (JL z) := by
  rw [ActualHigherSZeroAtomTransport.half_pairing_inner hO hD,
    ActualHigherSZeroAtomTransport.half_pairing_inner hO hD]
  exact real_inner_comm _ _

private lemma native_zero_first_negative_graphs
    {d : ℝ} (P : ARoom d) (q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (ht : (Tq dr Ar p q) x ∈ ParamRoom d) :
    (JL (finiteCoreSobolevLift hO hD (1/2 : ℝ)
      (nativeReferenceZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F) x)=
      ∑ i : Fin 3, ∑ V : Generator, cc q dr Ar p x i V •
        raisingLow hF hO hD i (generatorHigh V (UF F x))) ∧
    (JL (finiteCoreSobolevLift hO hD (1/2 : ℝ)
      (nativeReferenceAdjointZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F) x)=
      (∑ i : Fin 3, ∑ V : Generator, cc q dr Ar p x i V •
        generatorSharpLow V (loweringHigh hF hO hD i (UF F x)))+
      JL (Corr P q dr Ar p x (UF F x))) := by
  constructor
  · have h := native_zero_negative_graph hO hD hF g hg L q dr Ar p hdr hAr F x
    exact h.trans (forward_negative_words hF hO hD g L q dr Ar p x (UF F x))
  · have h := native_adjoint_zero_negative_graph hO hD hF g hg L q dr Ar p hdr hAr F x
    have he := h.trans (raw_adjoint_zero_eq_genuine_reverse_add_correction
      hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
      P q dr Ar p x ht (UF F x))
    simpa only [genuineReferenceZeroReverseNegative,_root_.sum_apply,_root_.smul_apply,
      ContinuousLinearMap.comp_apply] using he

private lemma correction_pairing_symmetric
    {d : ℝ} (P : ARoom d) (q dr Ar : ℝ) (p : ℕ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (z : Half) :
    PL z (JL (Corr P q dr Ar p x (UF F x)))=
      PL (Corr P q dr Ar p x (UF F x)) (JL z) :=
  half_pairing_symmetric hO hD z (Corr P q dr Ar p x (UF F x))

private lemma zero_first_word_sum_algebra
    {d : ℝ} (P : ARoom d) (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    PL (S1 g2 dr Ar p q (UF F) x)
      (∑ i : Fin 3, ∑ V : Generator, cc q dr Ar p x i V •
        raisingLow hF hO hD i (generatorHigh V (UF F x)))-
    PL (Sd1 g2 dr Ar p q (UF F) x)
      ((∑ i : Fin 3, ∑ V : Generator, cc q dr Ar p x i V •
        generatorSharpLow V (loweringHigh hF hO hD i (UF F x)))+
        JL (Corr P q dr Ar p x (UF F x))) =
      (∑ k : Fin 3, ∑ j : Fin 3, ∑ i : Fin 3, ∑ V : Generator,
        WD g2 q dr Ar p F k j i V x)+
      (∑ k : Fin 3, ∑ j : Fin 3, CD P g2 q dr Ar p F k j x) := by
  let r2 : ℝ := (referenceRadius dr Ar p L x)^2
  let sc : Fin 3 × Fin 3 → ℝ := fun kj =>
    firstCoordinateWeight g g2 L kj.1 kj.2 ((Tq dr Ar p q) x)
  let dc : Fin 3 × Generator → ℝ := fun iV => cc q dr Ar p x iV.1 iV.2
  let A : Fin 3 × Fin 3 → Half := fun kj =>
    AH ((Tq dr Ar p q) x) (Sum.inl kj.2)
      (fderiv ℝ (UF F) x (coordinateDirection kj.1))
  let Bv : Fin 3 × Fin 3 → Half := fun kj =>
    RH ((Tq dr Ar p q) x) (Sum.inl kj.2)
      (fderiv ℝ (UF F) x (coordinateDirection kj.1))
  let X : Fin 3 × Generator → Neg := fun iV =>
    raisingLow hF hO hD iV.1 (generatorHigh iV.2 (UF F x))
  let Y : Fin 3 × Generator → Neg := fun iV =>
    generatorSharpLow iV.2 (loweringHigh hF hO hD iV.1 (UF F x))
  let z : Half := Corr P q dr Ar p x (UF F x)
  have hSym (y : Half) : PL y (JL z)=PL z (JL y) := half_pairing_symmetric hO hD y z
  have hAlgebra := weighted_pairing_sums PL JL r2 sc dc A Bv X Y z hSym
  have hS : S1 g2 dr Ar p q (UF F) x=r2 • ∑ kj, sc kj • A kj := by
    simp only [Fintype.sum_prod_type]
    rfl
  have hSd : Sd1 g2 dr Ar p q (UF F) x=-(r2 • ∑ kj, sc kj • Bv kj) := by
    simp only [Fintype.sum_prod_type]
    rfl
  have hWord (k j i : Fin 3) (V : Generator) :
      WD g2 q dr Ar p F k j i V x=(r2*sc (k,j)*dc (i,V))*
        (PL (A (k,j)) (X (i,V))+PL (Bv (k,j)) (Y (i,V))) := rfl
  have hCorrection (k j : Fin 3) :
      CD P g2 q dr Ar p F k j x=(r2*sc (k,j))*PL z (JL (Bv (k,j))) := rfl
  have hWords : r2*(∑ kj, ∑ iV, (sc kj*dc iV)*
      (PL (A kj) (X iV)+PL (Bv kj) (Y iV)))=
      ∑ k : Fin 3, ∑ j : Fin 3, ∑ i : Fin 3, ∑ V : Generator, WD g2 q dr Ar p F k j i V x := by
    simp only [Fintype.sum_prod_type,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro V _
    rw [hWord]
    ring
  have hCorrections : r2*(∑ kj, sc kj*PL z (JL (Bv kj)))=
      ∑ k : Fin 3, ∑ j : Fin 3, CD P g2 q dr Ar p F k j x := by
    simp only [Fintype.sum_prod_type,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    exact (mul_assoc r2 (sc (k,j)) (PL z (JL (Bv (k,j))))).symm.trans (hCorrection k j).symm
  have hShape := congrArg₂
    (fun a b : Half => PL a (∑ iV, dc iV • X iV)-PL b ((∑ iV, dc iV • Y iV)+JL z)) hS hSd
  have hResult := hShape.trans
    (hAlgebra.trans (congrArg₂ (fun a b : ℝ => a+b) hWords hCorrections))
  simpa only [Fintype.sum_prod_type,dc,X,Y,z] using hResult
/-- Physical native fields match every original zero/first word and the full raw correction.
The only room hypothesis is used for the genuine existing adjoint graph. -/
theorem original_zero_first_eq_all_words_add_full_correction
    {d : ℝ} (P : ARoom d) (g2 : MatrixField) (q dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (F : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (ht : (Tq dr Ar p q) x ∈ ParamRoom d) :
    D01 g2 dr Ar p hdr hAr q F x =
      4*(∑ k : Fin 3, ∑ j : Fin 3, ∑ i : Fin 3, ∑ V : Generator,
        WD g2 q dr Ar p F k j i V x)+
      4*(∑ k : Fin 3, ∑ j : Fin 3, CD P g2 q dr Ar p F k j x) := by
  have hNative := native_zero_first_negative_graphs
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
    P q dr Ar p hdr hAr F x ht
  have hForward := native_half_pair hO hD
    (nativeReferenceZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F) x
    (S1 g2 dr Ar p q (UF F) x)
  have hAdjoint := native_half_pair hO hD
    (nativeReferenceAdjointZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr F) x
    (Sd1 g2 dr Ar p q (UF F) x)
  have hForwardTransport := hForward.trans
    (congrArg (PL (S1 g2 dr Ar p q (UF F) x)) hNative.1)
  have hAdjointTransport := hAdjoint.trans
    (congrArg (PL (Sd1 g2 dr Ar p q (UF F) x)) hNative.2)
  have hPhysical : D01 g2 dr Ar p hdr hAr q F x =
      4*(PL (S1 g2 dr Ar p q (UF F) x)
        (∑ i : Fin 3, ∑ V : Generator, cc q dr Ar p x i V •
          raisingLow hF hO hD i (generatorHigh V (UF F x)))-
        PL (Sd1 g2 dr Ar p q (UF F) x)
          ((∑ i : Fin 3, ∑ V : Generator, cc q dr Ar p x i V •
            generatorSharpLow V (loweringHigh hF hO hD i (UF F x)))+
            JL (Corr P q dr Ar p x (UF F x)))) :=
    congrArg (fun r : ℝ => 4*r)
      (congrArg₂ (fun a b : ℝ => a-b) hForwardTransport hAdjointTransport)
  have hAlgebra := zero_first_word_sum_algebra
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
    P g2 q dr Ar p F x
  have hFinish := congrArg (fun r : ℝ => 4*r) hAlgebra
  exact hPhysical.trans (hFinish.trans (mul_add _ _ _))

/-- The original D01 vanishes off the original input support, with no room premise. -/
theorem original_zero_first_eq_zero_off_tsupport
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (hx : x ∉ tsupport F.val) :
    D01 g2 dr Ar p hdr hAr q F x=0 := by
  have hv (k : Fin 3) : fderiv ℝ (UF F) x (coordinateDirection k)=0 := by
    change directionalFDeriv (coordinateDirection k)
      (finiteCoreSobolevLift hO hD (3/2 : ℝ) F) x=0
    rw [directionalFDeriv_finiteCoreSobolevLift]
    apply sphereSobolev_ext (3/2 : ℝ)
    intro n
    rw [sphereSobolevCoefficientL_finiteCoreSobolevLift]
    have hz : (coreDirectionalDerivative hO hD (coordinateDirection k) F).val x=0 :=
      image_eq_zero_of_notMem_tsupport (fun hy => hx
        (tsupport_coreDirectionalDerivative_subset hO hD (coordinateDirection k) F hy))
    rw [hz,map_zero,map_zero]
  unfold ActualTSLowerZeroZeroBinding.originalZeroFirstCrossDensity
    referenceSFirstHalf referenceSAdjointFirstHalf
  simp only [hv,map_zero,smul_zero,Finset.sum_const_zero,neg_zero,inner_zero_right,
    sub_self,mul_zero]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroFirstLiteralWords
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroFirstLiteralWords.original_zero_first_eq_all_words_add_full_correction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroFirstLiteralWords.original_zero_first_eq_zero_off_tsupport
