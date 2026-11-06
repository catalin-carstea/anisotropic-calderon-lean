import Calderon.ActualLowerSSelfRemainder
import Calderon.ActualModelSSignedAbsorption
import Calderon.ActualLeadingFullOutputCore
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualSSelfErrorInterface
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualFullEGainedEndpoints ActualAngularHighDraft ActualAngularPiDraft
  ActualHigherSLeadingBracketGain ConformalDepth ReferenceWeightedApproximation ReferenceDensityBounds
  FixedParameterProfilePullback NormalizedPrincipalMetric ActualHigherSScalarCommutatorNativeForm
  ActualModelSMixedComparison
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
  (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
local notation "FC" => smoothCompactFiniteSphereCore hO hD
local notation "LD" => ActualLowerSSelfRemainder.originalLeadingDensity
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
local notation "RS" => ActualLowerSSelfRemainder.originalLowerSSelfRemainder
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
local notation "ED" => ActualLowerSSelfRemainder.originalEnergyDensity g L hg hO hD
local notation "LOut" => actualLeadingSignedSecondOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
local notation "PCon" => ActualLowerSSelfRemainder.PrimaryLowerSSelfConclusions
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
local notation "CCon" => ActualLowerSSelfRemainder.CompleteLowerSSelfConclusions
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
local notation "ARoom" d:max => ActualAllAngularAtomGainedRoom.AllAngularAtomRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data d
local notation "Dec" => ActualModelSErrorDecomposition
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2
local notation "Rem" => actualModelSUnestimatedDensity
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2
local notation "Lo" => nativeULowerSCrossDensity
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "SO" dr:max Ar:max p:max hdr:max hAr:max q:max => ActualHigherSFormation.nativeHigherSOut
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 dr Ar p hdr hAr q hreg data.δ0 data.germs g2
local notation "SD" dr:max Ar:max p:max hdr:max hAr:max q:max => ActualHigherSAdjointFormation.higherSAdjointOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs g2 dr Ar p hdr hAr q
local notation "TT" dr:max Ar:max p:max hdr:max hAr:max q:max => nativeT hO hD hF g hg L q dr Ar p hdr hAr
local notation "TD" dr:max Ar:max p:max hdr:max hAr:max q:max => nativeTdag hO hD hF g hg L q dr Ar p hdr hAr
local notation "ZZ" dr:max Ar:max p:max hdr:max hAr:max q:max => nativeZ hO hD hF g hg L q dr Ar p hdr hAr

-- L1: expose the existing actual leading graph/physical pairing bridge.
lemma original_leading_density_eq_physical_of_profile_room
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (F : FC)
    (hTF : ∀ x ∈ tsupport F.val,(Tq dr Ar p q) x ∈ ParamRoom data.δ) :
    ∀ x : R3,LD dr Ar p q F x=
      referenceDensityFamily g L (q,x)*⟪F.val x,LOut dr Ar p q F x⟫_ℝ := by
  have hgraph := actualLeadingSignedSecondHalf_negative_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F hTF
  intro x
  have hp := ActualHigherSPhysicalPairing.physical_pairing_of_graph hO hD F
    (actualLeadingSignedSecondHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 dr Ar p q F)
    (actualLeadingSignedSecondNeg g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 dr Ar p q F) hgraph x
  have hweighted := congrArg (fun t : ℝ => referenceDensityFamily g L (q,x)*t) hp
  simpa only [ActualLowerSSelfRemainder.originalLeadingDensity,halfInput,
    ActualHigherSFormation.higherSInput,actualLeadingSignedSecondOut] using hweighted

-- L2: exact density regrouping, deriving every L1 field from produced records.
lemma integral_model_S_remaining_eq_original_s_self
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (CS CE eta : ℝ) (F : FC)
    (hP : PCon CS eta dr Ar p hdr hAr q F)
    (hDec : Dec dr Ar p hdr hAr q CE eta F)
    (hTF : ∀ x ∈ tsupport F.val,(Tq dr Ar p q) x ∈ ParamRoom data.δ) :
    (∫ x,referenceDensityFamily g L (q,x)*Rem dr Ar p hdr hAr q F x)=
      RS dr Ar p hdr hAr q F+
      4*(∫ x,referenceDensityFamily g L (q,x)*
        (⟪((TT dr Ar p hdr hAr q) F).val x,(SO dr Ar p hdr hAr q) F x⟫_ℝ-
         ⟪(((TD dr Ar p hdr hAr q) F)+((ZZ dr Ar p hdr hAr q) F)).val x,
           (SD dr Ar p hdr hAr q) F x⟫_ℝ))+
      2*(∫ x,referenceDensityFamily g L (q,x)*Lo dr Ar p hdr hAr q F x) := by
  have hLead := original_leading_density_eq_physical_of_profile_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
    dr Ar p q F hTF
  rcases hP with ⟨_h01,_h02,_h03,_h04,_h05,_h06,_h07,_h08,_h09,_h10,_h11,h12,
    _h13,_h14,_h15,_h16,_h17,_h18,_h19,_h20,_h21,_h22,_h23,_h24,h25,_h26,_h27⟩
  rcases hDec with ⟨hMixed,hLo,_hRem,_hKnown,_hEnergy,_hEq,_hKnownBound⟩
  rcases hMixed with ⟨_hFullF,_hFullD,_hMF,_hMD,_hSF,_hSD,hCT,_hCU,_hMixedEq⟩
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let rss : R3 → ℝ := fun x => mu x*
    ActualLowerSSelfRemainder.originalSignedNormDensity
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
      dr Ar p hdr hAr q F x-LD dr Ar p q F x
  let ctw : R3 → ℝ := fun x => mu x*
    (⟪((TT dr Ar p hdr hAr q) F).val x,(SO dr Ar p hdr hAr q) F x⟫_ℝ-
     ⟪(((TD dr Ar p hdr hAr q) F)+((ZZ dr Ar p hdr hAr q) F)).val x,
       (SD dr Ar p hdr hAr q) F x⟫_ℝ)
  let low : R3 → ℝ := fun x => mu x*Lo dr Ar p hdr hAr q F x
  have hRssInt : Integrable rss := h12
  have hCTInt : Integrable ctw := hCT
  have hLoInt : Integrable low := hLo
  have hRssEq : RS dr Ar p hdr hAr q F=∫ x,rss x := h25
  have hFun : (fun x => mu x*Rem dr Ar p hdr hAr q F x)=
      (fun x => rss x+4*ctw x+2*low x) := by
    funext x
    dsimp only [rss,ctw,low,ActualLowerSSelfRemainder.originalSignedNormDensity,
      actualModelSUnestimatedDensity]
    rw [hLead x]
    ring
  have hAdd1 : (∫ x,rss x+4*ctw x)=(∫ x,rss x)+(∫ x,4*ctw x) := by
    simpa only [Pi.add_apply] using integral_add hRssInt (hCTInt.const_mul 4)
  have hAdd2 : (∫ x,rss x+4*ctw x+2*low x)=
      (∫ x,rss x+4*ctw x)+(∫ x,2*low x) := by
    simpa only [Pi.add_apply] using
      integral_add (hRssInt.add (hCTInt.const_mul 4)) (hLoInt.const_mul 2)
  change (∫ x,mu x*Rem dr Ar p hdr hAr q F x)=
    RS dr Ar p hdr hAr q F+4*(∫ x,ctw x)+2*(∫ x,low x)
  calc
    _ = ∫ x,rss x+4*ctw x+2*low x :=
      congrArg (fun f : R3 → ℝ => ∫ x,f x) hFun
    _ = (∫ x,rss x)+(∫ x,4*ctw x)+(∫ x,2*low x) := by rw [hAdd2,hAdd1]
    _ = _ := by rw [← hRssEq,integral_const_mul,integral_const_mul]

-- L3: closed common-witness producer, not a new analytic callback.
theorem exists_uniform_model_S_s_self_error_interface
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ CS CE etaI dMix dQ : ℝ,0 < dMix ∧ 0 < dQ ∧
    ∃ Pmix : ARoom dMix,∃ PQ : ARoom dQ,
    0 < CS ∧ 0 < CE ∧ 0 < etaI ∧ etaI ≤ data.eta0 ∧ etaI ≤ 1 ∧
    ∀ q ∈ Icc (0 : ℝ) 1,
    ∀ dr : ℝ,∀ hdr : 0 < dr,dr ≤ 1 → ∀ Ar : ℝ,∀ hAr : 0 < Ar,
    ∀ p : ℕ,1 ≤ p → ∀ eta : ℝ,0 ≤ eta → eta ≤ etaI →
    ∀ K : Set R3,IsCompact K → K ⊆ ball y0 ρ →
    ∀ F : FC,tsupport F.val ⊆ K →
    (∀ x ∈ K,1 ≤ actualReferenceBeta g L q dr Ar p x) →
    (∀ x ∈ K,referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
    (∀ x ∈ K,CoordinateBootstrapJets.coordinateH8
      (referenceNormalizedPrincipalDifference g g2 L q) x ≤ eta*referenceRadius dr Ar p L x) →
    CCon Pmix PQ CS eta dr Ar p hdr hAr q F ∧
    Dec dr Ar p hdr hAr q CE eta F ∧
    (∀ x : R3,LD dr Ar p q F x=
      referenceDensityFamily g L (q,x)*⟪F.val x,LOut dr Ar p q F x⟫_ℝ) ∧
    (∫ x,referenceDensityFamily g L (q,x)*Rem dr Ar p hdr hAr q F x)=
      RS dr Ar p hdr hAr q F+
      4*(∫ x,referenceDensityFamily g L (q,x)*
        (⟪((TT dr Ar p hdr hAr q) F).val x,(SO dr Ar p hdr hAr q) F x⟫_ℝ-
         ⟪(((TD dr Ar p hdr hAr q) F)+((ZZ dr Ar p hdr hAr q) F)).val x,
           (SD dr Ar p hdr hAr q) F x⟫_ℝ))+
      2*(∫ x,referenceDensityFamily g L (q,x)*Lo dr Ar p hdr hAr q F x) := by
  obtain ⟨CS,etaSS,dMix,dQ,hdMix,hdQ,Pmix,PQ,hCS,hetaSS,hetaSS0,hSS⟩ :=
    ActualLowerSSelfRemainder.exists_original_lower_s_self_remainder
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hL hKernel hg2
  obtain ⟨CE,hCE,etaDec,hetaDec,hetaDec0,hetaDec1,hDec⟩ :=
    exists_actual_model_S_error_decomposition
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 hL hKernel
  obtain ⟨epsGraph,hepsGraph,_hepsGraph1,hGuard⟩ := exists_uniform_strict_higherSParam_guard
    g hg L hL y0 ρ data.δ data.δ_pos (closedBall y0 ρ) (isCompact_closedBall _ _)
  refine ⟨CS,CE,min etaSS (min etaDec epsGraph),dMix,dQ,hdMix,hdQ,Pmix,PQ,
    hCS,hCE,lt_min hetaSS (lt_min hetaDec hepsGraph),
    (min_le_left _ _).trans hetaSS0,
    ((min_le_right _ _).trans (min_le_left _ _)).trans hetaDec1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaI K hK hKball F hsupp hb hs hH8
  have heSS : eta ≤ etaSS := hetaI.trans (min_le_left _ _)
  have heDec : eta ≤ etaDec := hetaI.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heGraph : eta ≤ epsGraph := hetaI.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hC : CCon Pmix PQ CS eta dr Ar p hdr hAr q F :=
    hSS q hq dr hdr hdr1 Ar hAr p hp eta heta heSS K hK hKball F hsupp hb hs
  have hDecomp : Dec dr Ar p hdr hAr q CE eta F :=
    hDec q hq dr hdr hdr1 Ar hAr p hp eta heta heDec K hK hKball F hsupp hb hs hH8
  have hTF : ∀ x ∈ tsupport F.val,(Tq dr Ar p q) x ∈ ParamRoom data.δ := by
    intro x hx
    have hxK := hsupp hx
    have hguard := hGuard q hq dr hdr hdr1 Ar hAr p hp eta heta heGraph x
      (ball_subset_closedBall (hKball hxK)) (hKball hxK) (hb x hxK) (hs x hxK)
    exact (higherSParam_eventually_mem y0 ρ data.δ L dr Ar q p hdr hAr x hguard).self_of_nhds
  refine ⟨hC,hDecomp,?_,?_⟩
  · exact original_leading_density_eq_physical_of_profile_room
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F hTF
  · exact integral_model_S_remaining_eq_original_s_self
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2
      dr Ar p hdr hAr q CS CE eta F hC.1 hDecomp hTF

-- L4: algebra only; the two named analytic bounds are hypotheses.
lemma model_S_remaining_bound_of_named_TZS_and_ULS_bounds
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (CS CE CTZS CULS eta : ℝ) (F : FC)
    (hP : PCon CS eta dr Ar p hdr hAr q F)
    (hDec : Dec dr Ar p hdr hAr q CE eta F)
    (hTF : ∀ x ∈ tsupport F.val,(Tq dr Ar p q) x ∈ ParamRoom data.δ)
    (hTZS : |4*(∫ x,referenceDensityFamily g L (q,x)*
      (⟪((TT dr Ar p hdr hAr q) F).val x,(SO dr Ar p hdr hAr q) F x⟫_ℝ-
       ⟪(((TD dr Ar p hdr hAr q) F)+((ZZ dr Ar p hdr hAr q) F)).val x,
         (SD dr Ar p hdr hAr q) F x⟫_ℝ))| ≤
      CTZS*eta*(∫ x,ED dr Ar p q F x))
    (hULS : |2*(∫ x,referenceDensityFamily g L (q,x)*Lo dr Ar p hdr hAr q F x)| ≤
      CULS*eta*(∫ x,ED dr Ar p q F x)) :
    |∫ x,referenceDensityFamily g L (q,x)*Rem dr Ar p hdr hAr q F x| ≤
      (CS+CTZS+CULS)*eta*(∫ x,ED dr Ar p q F x) := by
  have hIdentity := integral_model_S_remaining_eq_original_s_self
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2
    dr Ar p hdr hAr q CS CE eta F hP hDec hTF
  rcases hP with ⟨_h01,_h02,_h03,_h04,_h05,_h06,_h07,_h08,_h09,_h10,_h11,_h12,
    _h13,_h14,_h15,_h16,_h17,_h18,_h19,_h20,_h21,_h22,_h23,_h24,_h25,_h26,hSBound⟩
  rw [hIdentity]
  calc
    _ ≤ |RS dr Ar p hdr hAr q F|+
        |4*(∫ x,referenceDensityFamily g L (q,x)*
          (⟪((TT dr Ar p hdr hAr q) F).val x,(SO dr Ar p hdr hAr q) F x⟫_ℝ-
           ⟪(((TD dr Ar p hdr hAr q) F)+((ZZ dr Ar p hdr hAr q) F)).val x,
             (SD dr Ar p hdr hAr q) F x⟫_ℝ))|+
        |2*(∫ x,referenceDensityFamily g L (q,x)*Lo dr Ar p hdr hAr q F x)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ CS*eta*(∫ x,ED dr Ar p q F x)+
        CTZS*eta*(∫ x,ED dr Ar p q F x)+CULS*eta*(∫ x,ED dr Ar p q F x) :=
      add_le_add (add_le_add hSBound hTZS) hULS
    _ = _ := by ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualSSelfErrorInterface
