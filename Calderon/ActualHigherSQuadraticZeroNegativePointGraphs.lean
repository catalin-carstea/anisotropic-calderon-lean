import Calderon.ActualHigherSQuadraticZeroQuartic
import Calderon.FixedParameterProfilePullback

/-! Complete actual207 pointwise Half→negative realization and support closure.
This owner supplies the point identities imported by the uniform profile consumer.
It adds no analytic premise, output truncation or final estimate callback. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSQuadraticZeroNegativeGraphs
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ConformalDepth
  ActualHigherSQuadraticZeroWords ActualFixedAtomFiniteLifts ActualRetainedGeneratorMultiplierGains
  ActualHigherSQuadraticZeroQuartic ReferenceWeightedApproximation FixedParameterProfilePullback
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "PL" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

private lemma map_eq_of_values_zero {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (J : E →L[ℝ] G) (A : F →L[ℝ] G) {x : E} {y : F}
    (hx : x = 0) (hy : y = 0) : J x = A y := by
  exact (congrArg J hx).trans
    ((map_zero J).trans ((map_zero A).symm.trans (congrArg A hy).symm))

/-- Complete finite weighted-word graph, before every physical data context. -/
private lemma weighted_word_graph {E H N ι κ : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (I : E →L[ℝ] H) (J : H →L[ℝ] N)
    (A : κ → E →L[ℝ] H) (B : κ → H →L[ℝ] N)
    (V : κ → E) (U : E) (c : ι → ℝ) (left right : ι → κ) (Z : H) (W : N)
    (hA : ∀ b v, J (A b v) = B b (I v))
    (hV : ∀ b, I (V b) = A b U)
    (hZ : Z = ∑ z : ι, c z • A (left z) (V (right z)))
    (hW : W = ∑ z : ι, c z • B (left z) (A (right z) U)) : J Z = W := by
  calc
    J Z = J (∑ z : ι, c z • A (left z) (V (right z))) := congrArg J hZ
    _ = ∑ z : ι, c z • B (left z) (A (right z) U) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro z _
      rw [map_smul]
      exact congrArg (fun n : N => c z • n)
        ((hA (left z) (V (right z))).trans (congrArg (B (left z)) (hV (right z))))
    _ = W := hW.symm

/-- Complete support closure, using only proved on-support graphs and off-support zeros. -/
lemma negative_graph_pair_of_support {E H N X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (J : E →L[ℝ] N) (F R : X → E) (A B : X → H →L[ℝ] N)
    (U : X → H) (S : Set X)
    (hOn : ∀ x ∈ S, J (F x) = A x (U x) ∧ J (R x) = B x (U x))
    (hOff : ∀ x ∉ S, F x = 0 ∧ R x = 0)
    (hInput : ∀ x ∉ S, U x = 0) :
    ∀ x, J (F x) = A x (U x) ∧ J (R x) = B x (U x) := by
  intro x
  by_cases hx : x ∈ S
  · exact hOn x hx
  · exact ⟨map_eq_of_values_zero J (A x) (hOff x hx).1 (hInput x hx),
      map_eq_of_values_zero J (B x) (hOff x hx).2 (hInput x hx)⟩

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

local notation "VA" => actualAtomHi g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "VB" => actualReverseAtomHi g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "Z2" => actualZ2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "T2" => actualT2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  sphereSobolevInclusionL atomHigh atomLow atomReverseHigh atomReverseLow
  actualAtomHi actualReverseAtomHi actualZ2Half actualT2Half
  quadraticZeroHalf quadraticZeroReverseHalf wordHalf wordReverseHalf
  quadraticZeroNegative quadraticZeroReverseNegative wordNegative wordReverseNegative

/-- Whole negative-family value as the original abstract ordered word sum. -/
lemma quadraticZeroNegative_apply_eq_sum (g2 : MatrixField) (dr Ar : ℝ)
    (p : ℕ) (q : ℝ) (x : R3) (U : Hi) :
    quadraticZeroNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x U =
      ∑ z : ZeroWord, WC g2 dr Ar p q x z •
        AL ((Tq dr Ar p q) x) (wordAtoms z).1
          (AH ((Tq dr Ar p q) x) (wordAtoms z).2 U) := by
  simp only [quadraticZeroNegative, wordNegative, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]

/-- Genuine reverse negative value with the original reversed atom order. -/
lemma quadraticZeroReverseNegative_apply_eq_sum (g2 : MatrixField) (dr Ar : ℝ)
    (p : ℕ) (q : ℝ) (x : R3) (U : Hi) :
    quadraticZeroReverseNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x U =
      ∑ z : ZeroWord, WC g2 dr Ar p q x z •
        RL ((Tq dr Ar p q) x) (wordAtoms z).2
          (RH ((Tq dr Ar p q) x) (wordAtoms z).1 U) := by
  simp only [quadraticZeroReverseNegative, wordReverseNegative, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]

lemma actualZ2Half_negative_graph {d : ℝ} (P : ARoom d) (dF : ℝ)
    (Cm : ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs dF)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom dF)
    (x : R3) (ht : (Tq dr Ar p q) x ∈ ParamRoom d) :
    JL (Z2 g2 dr Ar p q F x) =
      quadraticZeroNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        g2 dr Ar p q x (UF F x) := by
  have hLifts := actualAtomHi_inclusions g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    dF Cm dr Ar p hdr hAr q F hT x
  exact weighted_word_graph IH JL
    (AH ((Tq dr Ar p q) x)) (AL ((Tq dr Ar p q) x))
    (VA dr Ar p q F x) (UF F x) (WC g2 dr Ar p q x)
    (fun z : ZeroWord => (wordAtoms z).1) (fun z : ZeroWord => (wordAtoms z).2)
    (Z2 g2 dr Ar p q F x)
    (quadraticZeroNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x (UF F x))
    (fun aa v => ActualHigherSZeroAtomTransport.atom_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P ((Tq dr Ar p q) x) ht aa v)
    hLifts.1
    (actualZ2Half_eq_sum g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F x)
    (quadraticZeroNegative_apply_eq_sum g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x (UF F x))

lemma actualT2Half_negative_graph {d : ℝ} (P : ARoom d) (dF : ℝ)
    (Cm : ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs dF)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom dF)
    (x : R3) (ht : (Tq dr Ar p q) x ∈ ParamRoom d) :
    JL (T2 g2 dr Ar p q F x) =
      quadraticZeroReverseNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        g2 dr Ar p q x (UF F x) := by
  have hLifts := actualAtomHi_inclusions g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    dF Cm dr Ar p hdr hAr q F hT x
  exact weighted_word_graph IH JL
    (RH ((Tq dr Ar p q) x)) (RL ((Tq dr Ar p q) x))
    (VB dr Ar p q F x) (UF F x) (WC g2 dr Ar p q x)
    (fun z : ZeroWord => (wordAtoms z).2) (fun z : ZeroWord => (wordAtoms z).1)
    (T2 g2 dr Ar p q F x)
    (quadraticZeroReverseNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x (UF F x))
    (fun aa v => ActualHigherSZeroAtomTransport.reverse_atom_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P ((Tq dr Ar p q) x) ht aa v)
    hLifts.2
    (actualT2Half_eq_sum g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F x)
    (quadraticZeroReverseNegative_apply_eq_sum g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x (UF F x))

lemma actualZ2T2_eq_zero_off_input_support (dF : ℝ)
    (Cm : ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs dF)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom dF)
    (x : R3) (hx : x ∉ tsupport F.val) :
    Z2 g2 dr Ar p q F x = 0 ∧ T2 g2 dr Ar p q F x = 0 := by
  obtain ⟨hV0, hv0⟩ := actualAtomHi_eq_zero_off_support g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    dF Cm dr Ar p hdr hAr q F hT x hx
  exact ⟨actualZ2Half_eq_zero_of_lifts_eq_zero g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F x hV0,
    actualT2Half_eq_zero_of_lifts_eq_zero g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F x hv0⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSQuadraticZeroNegativeGraphs
