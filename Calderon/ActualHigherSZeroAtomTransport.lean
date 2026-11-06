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

/-! Actual 207-word specialization. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroAtomTransport
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

local notation "RAH" => ActualAllAngularAtomGainedRoom.angularAtomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RAL" => ActualAllAngularAtomGainedRoom.angularAtomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RRH" => ActualAllAngularAtomGainedRoom.angularAtomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RRL" => ActualAllAngularAtomGainedRoom.angularAtomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Scalar equality boundary: apply one original observable to two zero values. -/
lemma sub_values_eq_sum_of_both_eq_zero {V : Type*} [Zero V]
    (f : V → ℝ) {x y : V} {s : ℝ}
    (hx : x = 0) (hy : y = 0) (hs : s = 0) : f x - f y = s := by
  have hxy : x = y := hx.trans hy.symm
  exact (sub_eq_zero.mpr (congrArg f hxy)).trans hs.symm

/-- The existing native pairing CLM has its original scalar value. -/
lemma half_pairing_apply (x : Half) (n : Neg) : PL x n = PP x n := by
  simp only [ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply]

/-- Original actual forward graph transported by two typed CLM congruences. -/
lemma atom_graph {d : ℝ} (P : ARoom d) (t : Tpar) (ht : t ∈ ParamRoom d)
    (b : ZeroAtom) (u : Hi) : JL (AH t b u) = AL t b (IH u) := by
  calc
    JL (AH t b u) = JL (RAH t b u) :=
      congrArg (fun K : Hi →L[ℝ] Half => JL (K u))
        (ActualHigherSZeroAtomDictionary.atomHigh_eq_angularAtomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b)
    _ = RAL t b (IH u) := P.atomGraph b t ht u
    _ = AL t b (IH u) :=
      congrArg (fun K : Half →L[ℝ] Neg => K (IH u))
        (ActualHigherSZeroAtomDictionary.atomLow_eq_angularAtomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b).symm

/-- Original genuine reverse graph, without rewriting inside a word identity. -/
lemma reverse_atom_graph {d : ℝ} (P : ARoom d) (t : Tpar) (ht : t ∈ ParamRoom d)
    (b : ZeroAtom) (u : Hi) : JL (RH t b u) = RL t b (IH u) := by
  calc
    JL (RH t b u) = JL (RRH t b u) :=
      congrArg (fun K : Hi →L[ℝ] Half => JL (K u))
        (ActualHigherSZeroAtomDictionary.atomReverseHigh_eq_angularAtomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b)
    _ = RRL t b (IH u) := P.reverseAtomGraph b t ht u
    _ = RL t b (IH u) :=
      congrArg (fun K : Half →L[ℝ] Neg => K (IH u))
        (ActualHigherSZeroAtomDictionary.atomReverseLow_eq_angularAtomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b).symm

/-- Full original Half pivot transported by scalar congruences and pairing values. -/
lemma atom_pivot {d : ℝ} (P : ARoom d) (t : Tpar) (ht : t ∈ ParamRoom d)
    (b : ZeroAtom) (x y : Half) : PL x (AL t b y) = PL y (RL t b x) := by
  calc
    PL x (AL t b y) = PP x (AL t b y) := half_pairing_apply x (AL t b y)
    _ = PP x (RAL t b y) :=
      congrArg (fun K : Half →L[ℝ] Neg => PP x (K y))
        (ActualHigherSZeroAtomDictionary.atomLow_eq_angularAtomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b)
    _ = PP y (RRL t b x) := P.atomPivot b t ht x y
    _ = PP y (RL t b x) :=
      congrArg (fun K : Half →L[ℝ] Neg => PP y (K x))
        (ActualHigherSZeroAtomDictionary.atomReverseLow_eq_angularAtomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b).symm
    _ = PL y (RL t b x) := (half_pairing_apply y (RL t b x)).symm

/-- Original signed high gain graph under the proved dictionary equalities. -/
lemma gain_graph {d : ℝ} (P : ARoom d) (t : Tpar) (ht : t ∈ ParamRoom d)
    (b e : ZeroAtom) (u : Hi) :
    JL (P.gainHigh b e t u) = RL t b (AH t e u) - AL t e (RH t b u) := by
  have hFirst : RRL t b (RAH t e u) = RL t b (AH t e u) :=
    congrArg₂ (fun (K : Half →L[ℝ] Neg) (D : Hi →L[ℝ] Half) => K (D u))
      (ActualHigherSZeroAtomDictionary.atomReverseLow_eq_angularAtomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b).symm
      (ActualHigherSZeroAtomDictionary.atomHigh_eq_angularAtomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t e).symm
  have hSecond : RAL t e (RRH t b u) = AL t e (RH t b u) :=
    congrArg₂ (fun (K : Half →L[ℝ] Neg) (D : Hi →L[ℝ] Half) => K (D u))
      (ActualHigherSZeroAtomDictionary.atomLow_eq_angularAtomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t e).symm
      (ActualHigherSZeroAtomDictionary.atomReverseHigh_eq_angularAtomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b).symm
  exact (P.gainGraph b e t ht u).trans (congrArg₂ (fun x y : Neg => x - y) hFirst hSecond)

/-- Original native pairing-to-physical-inner-product contract, isolated. -/
lemma half_pairing_inner (x y : Half) : PL x (JL y) = ⟪KL x, KL y⟫_ℝ := by
  exact (half_pairing_apply x (JL y)).trans
    (ActualHigherSPhysicalPairing.halfPairing_eq_inner_sphereL2 hO hD x y)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroAtomTransport
