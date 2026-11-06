import Calderon.ActualAllAngularAtomGainedRoom
import Calderon.ActualHigherSDoubleQuarticIdentity
import Calderon.ActualHigherSZeroAtomTransport
import Calderon.ActualHigherSPairingNormDiagnostic
import Calderon.ActualHigherSCommonProfileRoomData
import Calderon.ActualHigherSZeroAtomDictionary

/-!
Original ordered word pairing bound for arbitrary four angular atoms.
The actual finite-input lifts are supplied by the physical consumer.
This is not a whole T/S energy bound.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroWordPairing
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualAllAngularAtomGainedRoom
  ActualFiniteHarmonicCore ConformalDepth ReferenceDensityBounds ReferenceWeightedApproximation

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PL" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def highNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def highSpace : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def lowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
@[instance_reducible] private def lowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] highNormed highSpace lowNormed lowSpace

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
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "AH" => angularAtomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "AL" => angularAtomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RH" => angularAtomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RL" => angularAtomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] angularAtomHigh angularAtomLow angularAtomReverseHigh
  angularAtomReverseLow sphereSobolevInclusionL

/-- Original low graphs and pivots close every analytic premise of the generic
four-pairing estimate. Only original input lift equalities remain at this support layer. -/
theorem exists_uniform_ordered_word_pair_bound {d : ℝ} (P : ARoom d) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ t ∈ ParamRoom d, ∀ U : Hi,
      ∀ V v : AngularAtom → Hi,
      (∀ b, IH (V b)=AH t b U) → (∀ b, IH (v b)=RH t b U) →
      ∀ i j k l : AngularAtom,
      |⟪KL (AH t i (V j)),KL (AH t k (V l))⟫_ℝ -
        ⟪KL (RH t j (v i)),KL (RH t l (v k))⟫_ℝ| ≤
        4*ActualHigherSPairingNormDiagnostic.standardPairingNorm PL*M^3*‖U‖^2 := by
  let caps := P.finiteCaps 0
  let M := Classical.choose caps
  have hM : 1 ≤ M := (Classical.choose_spec caps).1
  have hAtoms := (Classical.choose_spec caps).2.1
  have hGains := (Classical.choose_spec caps).2.2
  refine ⟨M,hM,?_⟩
  intro t ht U V v hV hv i j k l
  have hA (b : AngularAtom) (z : Hi) : JL (AH t b z)=AL t b (IH z) :=
    P.atomGraph b t ht z
  have hB (b : AngularAtom) (z : Hi) : JL (RH t b z)=RL t b (IH z) :=
    P.reverseAtomGraph b t ht z
  have hPivot (b : AngularAtom) (z y : Half) : PL z (AL t b y)=PL y (RL t b z) := by
    simpa only [ActualHigherSScalarCommutatorNativeForm.halfDualPairingL_apply] using
      P.atomPivot b t ht z y
  have hPair (z y : Half) : PL z (JL y)=⟪KL z,KL y⟫_ℝ :=
    ActualHigherSZeroAtomTransport.half_pairing_inner hO hD z y
  obtain ⟨hAdjA,hAdjB⟩ := ActualHigherSDoubleQuarticIdentity.high_pairings_of_low_pivot
    IH JL KL PL (AH t) (RH t) (AL t) (RL t) hA hB hPivot hPair
  have hG (b e : AngularAtom) (z : Hi) :
      JL (P.gainHigh b e t z)=RL t b (AH t e z)-AL t e (RH t b z) :=
    P.gainGraph b e t ht z
  have hCl (b e : AngularAtom) (z : Hi) :
      P.gainLow b e t (IH z)=JL (P.gainHigh b e t z) := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun K : Hi →L[ℝ] Neg => K z) (P.upper b e t ht)
  have hId := ActualHigherSDoubleQuarticIdentity.double_word_pairing_sub_reverse_eq_four_pairings
    IH JL KL PL (AH t) (RH t) (AL t) (RL t)
    (fun b e => P.gainHigh b e t) (fun b e => P.gainLow b e t)
    (sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num))
    hA hB hG hCl hAdjA hAdjB hPair U V v hV hv i j k l
  have hAH (b : AngularAtom) : ‖AH t b‖ ≤ M := by
    simpa only [norm_iteratedFDerivWithin_zero] using (hAtoms b 0 le_rfl t ht).1
  have hRH (b : AngularAtom) : ‖RH t b‖ ≤ M := by
    simpa only [norm_iteratedFDerivWithin_zero] using (hAtoms b 0 le_rfl t ht).2.2.1
  have hAL (b : AngularAtom) : ‖AL t b‖ ≤ M := by
    simpa only [norm_iteratedFDerivWithin_zero] using (hAtoms b 0 le_rfl t ht).2.1
  have hGH (b e : AngularAtom) : ‖P.gainHigh b e t‖ ≤ M := by
    simpa only [norm_iteratedFDerivWithin_zero] using (hGains b e 0 le_rfl t ht).1
  have hGL (b e : AngularAtom) : ‖P.gainLow b e t‖ ≤ M := by
    simpa only [norm_iteratedFDerivWithin_zero] using (hGains b e 0 le_rfl t ht).2
  rw [hId]
  exact ActualHigherSPairingNormDiagnostic.abs_four_native_pairings_le
    (AH t) (RH t) (fun b e => P.gainHigh b e t) (AL t) (fun b e => P.gainLow b e t)
    M (zero_le_one.trans hM) hAH hRH hGH hAL hGL U i j k l


local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "Tq" => ActualHigherSFormation.higherSParam L
local notation "VA" => ActualHigherSQuadraticZeroQuartic.actualAtomHi
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "VB" => ActualHigherSQuadraticZeroQuartic.actualReverseAtomHi
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

attribute [local irreducible] ActualHigherSFormation.higherSInput
  ActualHigherSQuadraticZeroQuartic.actualAtomHi ActualHigherSQuadraticZeroQuartic.actualReverseAtomHi

/-- The exact original physical paired difference, named only to keep the
large uniform statement behind a scalar elaboration boundary. -/
def actualOrderedWordPairingDefect (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (i j k l : AngularAtom) : ℝ :=
  ⟪KL (AH ((Tq dr Ar p q) x) i (VA dr Ar p q F x j)),
    KL (AH ((Tq dr Ar p q) x) k (VA dr Ar p q F x l))⟫_ℝ -
  ⟪KL (RH ((Tq dr Ar p q) x) j (VB dr Ar p q F x i)),
    KL (RH ((Tq dr Ar p q) x) l (VB dr Ar p q F x k))⟫_ℝ

local notation "DPair" => actualOrderedWordPairingDefect
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
attribute [local irreducible] actualOrderedWordPairingDefect

/-- Actual original finite input: the common room, all lifts and quantitative
premises are produced internally before every later profile/support/atom choice. -/
theorem exists_original_finite_input_word_pair_bound
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ M etaWord : ℝ, 1 ≤ M ∧ 0 < etaWord ∧ etaWord ≤ data.eta0 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaWord →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      ∀ x ∈ tsupport F.val, ∀ i j k l : AngularAtom,
      |DPair dr Ar p q F x i j k l| ≤
        4*ActualHigherSPairingNormDiagnostic.standardPairingNorm PL*M^3*‖UF F x‖^2 := by
  obtain ⟨dA,hdA,_hdAD,_hdA0,_hdArho,_hInv,⟨P⟩⟩ :=
    ActualAllAngularAtomGainedRoom.exists_same_packet_allAngularAtom_room
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hKernel
  obtain ⟨M,hM,hBound⟩ := exists_uniform_ordered_word_pair_bound
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data P
  let G := Classical.choice (ActualHigherSQuarticFactorization.exists_common_profile_room_data
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    hL hKernel dA hdA)
  let etaWord := min data.eta0 G.epsG
  refine ⟨M,etaWord,hM,lt_min data.eta0_pos G.epsG_pos,min_le_left _ _,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaWord K hK hKball F hsupp hb hs x hx i j k l
  have rooms := G.members q hq dr hdr hdr1 Ar hAr p hp eta heta
    (hetaWord.trans (min_le_right _ _)) K hK hKball F hsupp hb hs
  have hLifts := ActualHigherSQuadraticZeroQuartic.actualAtomHi_inclusions
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    G.commonRadius G.common dr Ar p hdr hAr q F rooms.2 x
  let t := (Tq dr Ar p q) x
  have hV (b : AngularAtom) : IH (VA dr Ar p q F x b)=AH t b (UF F x) :=
    (hLifts.1 b).trans (congrArg (fun A : Hi →L[ℝ] Half => A (UF F x))
      (ActualHigherSZeroAtomDictionary.atomHigh_eq_angularAtomHigh
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b))
  have hv (b : AngularAtom) : IH (VB dr Ar p q F x b)=RH t b (UF F x) :=
    (hLifts.2 b).trans (congrArg (fun A : Hi →L[ℝ] Half => A (UF F x))
      (ActualHigherSZeroAtomDictionary.atomReverseHigh_eq_angularAtomReverseHigh
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b))
  unfold actualOrderedWordPairingDefect
  exact hBound t (rooms.1 x hx) (UF F x) (VA dr Ar p q F x) (VB dr Ar p q F x)
    hV hv i j k l

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroWordPairing
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroWordPairing.exists_uniform_ordered_word_pair_bound

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSZeroWordPairing.exists_original_finite_input_word_pair_bound
