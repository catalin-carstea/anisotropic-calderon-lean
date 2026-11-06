import Calderon.ActualHigherSDoubleQuarticIdentity
import Calderon.ActualHigherSQuadraticZeroWords
import Calderon.ActualAllAngularAtomGainedRoom
import Calderon.ActualFixedAtomFiniteLifts
import Calderon.ActualSobolevDegreeGraphLifting
import Calderon.ActualHigherSAdjointFormation
import Calderon.ActualHigherSAdjointLeadingCoordinate
import Calderon.ActualHigherSQuadraticZeroQuarticValues
import Calderon.ActualHigherSZeroAtomDictionary
import Calderon.ActualHigherSFiniteWordPolarization
import Calderon.ActualHigherSZeroAtomTransport

/-! Author actual207-word specialization. Conditional own Words003/AllRoom002/
FixedLift001 imports are NOT qualified provider grants. Exact before-code contract
is archived in upfront-v001. No analytic bound or canonical acceptance is claimed here. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSQuadraticZeroQuartic
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ConformalDepth
  ActualHigherSQuadraticZeroWords ActualFixedAtomFiniteLifts ActualRetainedGeneratorMultiplierGains
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

local notation "VA" => actualAtomHi g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "VB" => actualReverseAtomHi g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "Z2" => actualZ2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "T2" => actualT2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "QR" => quarticWordRow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

lemma actual207_word_identity_at {d : ℝ} (P : ARoom d) (t : Tpar) (ht : t ∈ ParamRoom d)
    (U : Hi) (V v : ZeroAtom → Hi)
    (hV : ∀ a, IH (V a) = AH t a U) (hv : ∀ a, IH (v a) = RH t a U)
    (c : ZeroWord → ℝ) :
    ‖KL (∑ z : ZeroWord, c z • AH t (wordAtoms z).1 (V (wordAtoms z).2))‖^2 -
      ‖KL (∑ z : ZeroWord, c z • RH t (wordAtoms z).2 (v (wordAtoms z).1))‖^2 =
      ∑ z : ZeroWord, ∑ w : ZeroWord, (c z*c w)*QR P t U z w := by
  have hA (b : ZeroAtom) (u : Hi) : JL (AH t b u) = AL t b (IH u) :=
    ActualHigherSZeroAtomTransport.atom_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P t ht b u
  have hB (b : ZeroAtom) (u : Hi) : JL (RH t b u) = RL t b (IH u) :=
    ActualHigherSZeroAtomTransport.reverse_atom_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P t ht b u
  have hP (b : ZeroAtom) (x y : Half) : PL x (AL t b y) = PL y (RL t b x) :=
    ActualHigherSZeroAtomTransport.atom_pivot g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P t ht b x y
  have hPair (x y : Half) : PL x (JL y) = ⟪KL x, KL y⟫_ℝ :=
    ActualHigherSZeroAtomTransport.half_pairing_inner hO hD x y
  obtain ⟨hAdjA, hAdjB⟩ := ActualHigherSDoubleQuarticIdentity.high_pairings_of_low_pivot
    IH JL KL PL (AH t) (RH t) (AL t) (RL t) hA hB hP hPair
  have hG (b e : ZeroAtom) (u : Hi) :
      JL (P.gainHigh b e t u) = RL t b (AH t e u) - AL t e (RH t b u) :=
    ActualHigherSZeroAtomTransport.gain_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P t ht b e u
  have hCl (b e : ZeroAtom) (u : Hi) : P.gainLow b e t (IH u) = JL (P.gainHigh b e t u) := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun C : Hi →L[ℝ] Neg => C u) (P.upper b e t ht)
  apply ActualHigherSFiniteWordPolarization.norm_weighted_word_sum_sq_sub KL c
  intro z w
  have h := ActualHigherSDoubleQuarticIdentity.double_word_pairing_sub_reverse_eq_four_pairings
    IH JL KL PL (AH t) (RH t) (AL t) (RL t)
    (fun b e => P.gainHigh b e t) (fun b e => P.gainLow b e t)
    (sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num))
    hA hB hG hCl hAdjA hAdjB hPair U V v hV hv
    (wordAtoms z).1 (wordAtoms z).2 (wordAtoms w).1 (wordAtoms w).2
  simpa only [quarticWordRow, ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply] using h

/-- Actual same-packet207-word identity. Every lift is constructed internally;
this support-room form is consumed by the uniform guard theorem. -/
theorem exists_same_packet_actual207_word_identity (hKernel : UnitBallValueTraceKernel τ0)
    (g2 : MatrixField) :
    ∃ dA : ℝ, 0 < dA ∧ dA ≤ data.δ ∧
      ∃ P : ARoom dA, ∃ d : ℝ, 0 < d ∧ d ≤ dA ∧ d ≤ data.δ0 ∧ d ≤ ρ ∧
      ∀ (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ),
      ∀ F : smoothCompactFiniteSphereCore hO hD,
      (∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom d) → ∀ x : R3,
      ‖KL (Z2 g2 dr Ar p q F x)‖^2 - ‖KL (T2 g2 dr Ar p q F x)‖^2 =
        ∑ z : ZeroWord, ∑ v : ZeroWord,
          (WC g2 dr Ar p q x z * WC g2 dr Ar p q x v) *
            QR P ((Tq dr Ar p q) x) (UF F x) z v := by
  obtain ⟨dA, hdA, hdAD, hdA0, hdAρ, _hRoomA, ⟨P⟩⟩ :=
    ActualAllAngularAtomGainedRoom.exists_same_packet_allAngularAtom_room
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hKernel
  obtain ⟨dF, Cm⟩ := ActualCommonFirstWordQuadraticAdjoint.exists_common_first_word_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel
    data.δ0 data.δ0_pos data.germs
  let d := min dA dF
  have hdA' : d ≤ dA := min_le_left _ _
  have hdF : d ≤ dF := min_le_right _ _
  refine ⟨dA, hdA, hdAD, P, d, lt_min hdA Cm.rev.pos, hdA', hdA'.trans hdA0,
    hdA'.trans hdAρ, ?_⟩
  intro dr Ar p hdr hAr q F hT x
  have hTF : ∀ y ∈ tsupport F.val, (Tq dr Ar p q) y ∈ ParamRoom dF :=
    fun y hy => ⟨commonRoom_mono y0 ρ hdF (hT y hy).1, (hT y hy).2⟩
  have hLifts := actualAtomHi_inclusions
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    dF Cm dr Ar p hdr hAr q F hTF x
  by_cases hx : x ∈ tsupport F.val
  · have htA : (Tq dr Ar p q) x ∈ ParamRoom dA :=
      ⟨commonRoom_mono y0 ρ hdA' (hT x hx).1, (hT x hx).2⟩
    rw [actualZ2Half_eq_sum g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F x,
      actualT2Half_eq_sum g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F x]
    exact actual207_word_identity_at g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      P ((Tq dr Ar p q) x) htA (UF F x)
      (VA dr Ar p q F x) (VB dr Ar p q F x) hLifts.1 hLifts.2
      (WC g2 dr Ar p q x)
  · obtain ⟨hV0, hv0⟩ := actualAtomHi_eq_zero_off_support g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      dF Cm dr Ar p hdr hAr q F hTF x hx
    have hZ0 : Z2 g2 dr Ar p q F x = 0 :=
      actualZ2Half_eq_zero_of_lifts_eq_zero g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F x hV0
    have hT0 : T2 g2 dr Ar p q F x = 0 :=
      actualT2Half_eq_zero_of_lifts_eq_zero g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F x hv0
    have hU0 : UF F x = 0 := ActualHigherSFormation.higherSInput_eq_zero
      hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 dr Ar p hdr hAr q F x hx
    have hRow0 (z v : ZeroWord) : QR P ((Tq dr Ar p q) x) (UF F x) z v = 0 := by
      rw [hU0]
      exact quarticWordRow_zero g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data P ((Tq dr Ar p q) x) z v
    have hSum0 : (∑ z : ZeroWord, ∑ v : ZeroWord,
        (WC g2 dr Ar p q x z * WC g2 dr Ar p q x v) *
          QR P ((Tq dr Ar p q) x) (UF F x) z v) = 0 := by
      apply Finset.sum_eq_zero
      intro z _
      apply Finset.sum_eq_zero
      intro v _
      rw [hRow0 z v, mul_zero]
    exact ActualHigherSZeroAtomTransport.sub_values_eq_sum_of_both_eq_zero
      (fun Z : Half => ‖KL Z‖^2) hZ0 hT0 hSum0

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSQuadraticZeroQuartic
