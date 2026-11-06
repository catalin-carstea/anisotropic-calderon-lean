import Calderon.ActualHigherSCubicPairing
import Calderon.ActualHigherSCubicLowPivot
import Calderon.ActualAllAngularAtomGainedRoom
import Calderon.ActualHigherSQuadraticZeroQuartic
import Calderon.ActualPPLowerRemainder
import Calderon.ActualHigherSZeroAtomTransport

/-! Author component of continuing actual mixed P/Z2 consumer. The final uniform
bound is an archived target, not asserted in this component. Full-Half gained
pivot and actual four-gain cubic cancellation are proved below. Own4510/4511
imports retain their native/source qualifications; new own sources and focused
LowPivot ec0024ae are conditional, not provider grants. No compiler by author. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSActualCubicPairing
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ConformalDepth
  ActualHigherSQuadraticZeroWords ActualFixedAtomFiniteLifts ActualRetainedGeneratorMultiplierGains
  ActualHigherSQuadraticZeroQuartic PrincipalCommutator ReferenceWeightedApproximation
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "PL" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
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

/-- Entire first-coordinate times word coefficient: no factor is differentiated in isolation. -/
def mixedWordScalar (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (k i : Fin 3) (z : ZeroWord) (x : R3) : ℝ :=
  (referenceRadius dr Ar p L x)^2*ActualHigherSLeadingBracketGain.firstCoordinateWeight g g2 L k i ((Tq dr Ar p q) x)*
    WC g2 dr Ar p q x z

def actualMixedCubicDensity (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  ⟪PF g2 dr Ar p q F x, KL (Z2 g2 dr Ar p q F x)⟫_ℝ -
    ⟪PR g2 dr Ar p q F x, KL (T2 g2 dr Ar p q F x)⟫_ℝ

/-- The SAME-W paired upper graphs determine the gained pivot on ALL Half inputs. -/
lemma allAtom_full_half_gained_pivot {d : ℝ} (P : ARoom d) (t : Tpar)
    (ht : t ∈ ParamRoom d) (aa bb : ZeroAtom) (x y : Half) :
    PP x (P.gainLow aa bb t y) = PP y (P.gainLow bb aa t x) := by
  have hUpper (aa bb : ZeroAtom) (u : Hi) : P.gainLow aa bb t (IH u) = JL (P.gainHigh aa bb t u) := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun C : Hi →L[ℝ] Neg => C u) (P.upper aa bb t ht)
  have hPaired (aa bb : ZeroAtom) (u v : Hi) :
      PL (IH v) (JL (P.gainHigh aa bb t u)) = PL (IH u) (JL (P.gainHigh bb aa t v)) := by
    simpa only [ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply] using P.paired aa bb t ht u v
  simpa only [ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply] using
    ActualHigherSCubicLowPivot.paired_low_pivot_of_dense_inclusion
      IH JL PL (fun aa bb => P.gainHigh aa bb t) (fun aa bb => P.gainLow aa bb t)
      (denseRange_sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num))
      hUpper hPaired aa bb x y

/-- The actual positive cubic form; its second reverse term keeps the original minus-first sign. -/
def cubicAtomForm (t : Tpar) (aa bb cc : ZeroAtom) : Hi →L[ℝ] Hi →L[ℝ] ℝ :=
  (PL).bilinearComp (AH t aa) ((AL t bb).comp (AH t cc)) +
    (PL).bilinearComp (RH t aa) ((RL t cc).comp (RH t bb))

lemma cubicAtomForm_apply (t : Tpar) (aa bb cc : ZeroAtom) (v U2 : Hi) :
    cubicAtomForm g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t aa bb cc v U2 =
      PP (AH t aa v) (AL t bb (AH t cc U2)) + PP (RH t aa v) (RL t cc (RH t bb U2)) := rfl

/-- The first input is literally Half; no high angular norm of the derivative remains. -/
def cubicSkewRow {d : ℝ} (P : ARoom d) (t : Tpar) (du : Half) (U : Hi)
    (aa bb cc : ZeroAtom) : ℝ :=
  PP du (P.gainLow aa bb t (AH t cc U)) + PP du (AL t bb (P.gainHigh aa cc t U)) -
    PP du (P.gainLow cc aa t (RH t bb U)) - PP du (RL t cc (P.gainHigh bb aa t U))

lemma cubicAtomForm_sub_transpose_eq {d : ℝ} (P : ARoom d) (t : Tpar)
    (ht : t ∈ ParamRoom d) (aa bb cc : ZeroAtom) (v U : Hi) :
    cubicAtomForm g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t aa bb cc v U -
      cubicAtomForm g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t aa bb cc U v =
      cubicSkewRow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P t (IH v) U aa bb cc := by
  have hA (aa : ZeroAtom) (u : Hi) : JL (AH t aa u) = AL t aa (IH u) := by
    exact ActualHigherSZeroAtomTransport.atom_graph
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P t ht aa u
  have hB (aa : ZeroAtom) (u : Hi) : JL (RH t aa u) = RL t aa (IH u) := by
    exact ActualHigherSZeroAtomTransport.reverse_atom_graph
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P t ht aa u
  have hP (aa : ZeroAtom) (x y : Half) : PL x (AL t aa y) = PL y (RL t aa x) := by
    exact ActualHigherSZeroAtomTransport.atom_pivot
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P t ht aa x y
  have hPair (x y : Half) : PL x (JL y) = ⟪KL x, KL y⟫_ℝ := by
    exact ActualHigherSZeroAtomTransport.half_pairing_inner hO hD x y
  have hG (aa bb : ZeroAtom) (u : Hi) :
      JL (P.gainHigh aa bb t u) = RL t aa (AH t bb u) - AL t bb (RH t aa u) := by
    exact ActualHigherSZeroAtomTransport.gain_graph
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P t ht aa bb u
  have hCl (aa bb : ZeroAtom) (u : Hi) : P.gainLow aa bb t (IH u) = JL (P.gainHigh aa bb t u) := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun C : Hi →L[ℝ] Neg => C u) (P.upper aa bb t ht)
  have hClP (aa bb : ZeroAtom) (x y : Half) : PL x (P.gainLow aa bb t y) = PL y (P.gainLow bb aa t x) := by
    simpa only [ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply] using
      allAtom_full_half_gained_pivot
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P t ht aa bb x y
  have h := ActualHigherSCubicPairing.cubic_pairing_sub_transpose_eq_four_pairings
    IH JL KL PL (AH t) (RH t) (AL t) (RL t)
    (fun aa bb => P.gainHigh aa bb t) (fun aa bb => P.gainLow aa bb t)
    hA hB hP hPair hG hCl hClP aa bb cc v U
  simpa only [cubicAtomForm_apply, cubicSkewRow,
    ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply] using h

/-- For the ACTUAL finite input, the differentiated first input remains the exact Half derivative. -/
lemma actual_cubic_directional_skew {d : ℝ} (P : ARoom d)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD)
    (x : R3) (ht : (Tq dr Ar p q) x ∈ ParamRoom d) (k : Fin 3) (aa bb cc : ZeroAtom) :
    cubicAtomForm g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 ((Tq dr Ar p q) x) aa bb cc
      (directionalFDeriv (OAI.AnisotropicCalderon.ReferenceDensityBounds.coordinateDirection k) (UF F) x) (UF F x) -
    cubicAtomForm g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 ((Tq dr Ar p q) x) aa bb cc
      (UF F x) (directionalFDeriv (OAI.AnisotropicCalderon.ReferenceDensityBounds.coordinateDirection k) (UF F) x) =
    cubicSkewRow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P ((Tq dr Ar p q) x)
      (directionalFDeriv (OAI.AnisotropicCalderon.ReferenceDensityBounds.coordinateDirection k) (ActualHigherSScalarCommutatorNativeForm.halfInput hO hD F) x)
      (UF F x) aa bb cc := by
  have h := cubicAtomForm_sub_transpose_eq
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P ((Tq dr Ar p q) x) ht
    aa bb cc (directionalFDeriv (OAI.AnisotropicCalderon.ReferenceDensityBounds.coordinateDirection k) (UF F) x) (UF F x)
  rw [ActualHigherSScalarCommutatorNativeForm.directional_halfInput hO hD F (OAI.AnisotropicCalderon.ReferenceDensityBounds.coordinateDirection k) x]
  exact h

/-- Original hypotheses produce the all-Half pivot; it is not a final callback. -/
theorem exists_same_packet_allAtom_full_half_pivot (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ d : ℝ, 0 < d ∧ d ≤ data.δ ∧ d ≤ data.δ0 ∧ d ≤ ρ ∧
      ∃ P : ARoom d, ∀ t ∈ ParamRoom d, ∀ aa bb : ZeroAtom, ∀ x y : Half,
        PP x (P.gainLow aa bb t y) = PP y (P.gainLow bb aa t x) := by
  obtain ⟨d, hd, hdD, hd0, hdρ, _hRoom, ⟨P⟩⟩ :=
    ActualAllAngularAtomGainedRoom.exists_same_packet_allAngularAtom_room
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hKernel
  exact ⟨d, hd, hdD, hd0, hdρ, P, fun t ht aa bb x y =>
    allAtom_full_half_gained_pivot
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P t ht aa bb x y⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSActualCubicPairing
