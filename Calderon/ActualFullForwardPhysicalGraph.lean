import Calderon.ActualFinitePhysicalAdjointOutput
import Calderon.ActualNativeMixedJPhysicalGraph
import Calderon.ActualHigherSNegativeFullDictionaryRows
import Calderon.ActualPhysicalProductsPostmapGraph
import Calderon.ActualLowerSSelfFormation
import Calderon.ActualPhysicalLowResidualIntegralCap
import Calderon.ActualNativeMovingAdjointMixedJPointGraph
import Calderon.ActualPerturbedModelSupport
import Calderon.PhysicalDensityProductsForwardLiteralPostmapSection
import Calderon.ActualPhysicalDensityOperatorLocality

/-! AUTHOR source preparation only, approved full-forward v002 mathematics.
The generic algebra and concrete proof body are verbatim approved beforecode.
Original full input/output, given packet witnesses, norms and quantifiers retained.
Future coherent executable parent: NULL. No compiler/native/review credit here.
Source-object NULLs, completion/inclusion bindings, literature/model qualifiers,
historical SectionFive scope and pending human ratification remain unchanged.
-/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.MainPhysicalGraphBridge
open Set Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore
  ActualFiniteHarmonicModel ActualFullEGainedEndpoints ActualFullEGainedAssembly
  ReferenceDensityBounds ReferenceWeightedApproximation ConformalDepth


-- COMPLETE proposed pure lemma proof, not a materialized/checkable owner yet.
-- Instantiate pointwise; each graph premise is derived from the retained ACTUAL
-- component owners in the unchanged final producer, never a new final callback.
private theorem assemble_full_physical_graph_at
    {E N : Type*} [NormedAddCommGroup E] [NormedAddCommGroup N]
    [NormedSpace ℝ E] [NormedSpace ℝ N]
    (K0 : E →L[ℝ] N) (mr drift so low products : E)
    (physical jf first second angular pair double : N)
    (hPhysical : physical = K0 (mr + drift) + jf + first + second + angular + pair + double)
    (hLow : K0 low = K0 drift + jf + first)
    (hSO : K0 so = second + angular + double)
    (hProducts : K0 products = pair) :
    K0 (mr + so + low + products) = physical := by
  calc
    K0 (mr + so + low + products) = K0 mr + K0 so + K0 low + K0 products := by
      simp only [map_add]
    _ = K0 (mr + drift) + jf + first + second + angular + pair + double := by
      rw [hLow, hSO, hProducts, map_add]
      abel
    _ = physical := hPhysical.symm

-- Reuses the proof of the existing private half-postmap lemma in
-- ActualFinitePhysicalAdjointOutput. No new public assumption or map is introduced.
private lemma physicalL2Inclusion_literal_half_postmap
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (v : SphereSobolev (1/2 : ℝ)) :
  physicalL2Inclusion hO hD ((sphereSobolevZeroEquiv hO hD).symm
    (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) v)) =
  sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) v := by
  have hCancel := congrArg (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num))
    ((sphereSobolevZeroEquiv hO hD).apply_symm_apply
      (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) v))
  have hTrans := congrArg
    (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T v)
    (sphereSobolevInclusionL_trans (1/2 : ℝ) 0 (-(1/2 : ℝ)) (by norm_num) (by norm_num))
  exact hCancel.trans hTrans

/-- Pointwise cut of the existing actual physical calculation.
The sole SO graph proof is the already-derived original component fact;
this adds no hypothesis to the selected public producer. -/
private theorem physical_graph_at_of_original_higherS_graph
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (hreg : FixedDirichletRegularity)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (F : smoothCompactFiniteSphereCore hO hD) (y : R3)
    (hyRoom : ‖y-y0‖ ≤ ρ)
    (hr : referenceRadius dr Ar p L y ≠ 0)
    (hInv : ∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ
        (q,((y,referenceRadius dr Ar p L y),ξ.val))).IsInvertible)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1,
      (q,(y,θ*referenceRadius dr Ar p L y)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (so : SphereL2)
    (hso : sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD so) =
      ActualHigherSFormation.nativeHigherSNegative
        hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 g2 q
        (referenceRadius dr Ar p L) (ActualHigherSFormation.higherSInput hO hD F) y) :
    let R : R3 → ℝ := referenceRadius dr Ar p L
    let u : R3 → SphereSobolev (3/2 : ℝ) := finiteCoreSobolevLift hO hD (3/2 : ℝ) F
    let K0 := physicalL2Inclusion hO hD
    let MR : R3 → SphereL2 :=
      (nativeModelRaising hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr F).val
    let LOW : R3 → SphereL2 :=
      nativeMixedFirstCorrectionLowOut hF hO hD g hg g2 L q dr Ar p hdr hAr F
    let Pout : R3 → SphereL2 := fun x => (sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
        (referencePhysicalDensityProductsHalfOperator
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R x
          (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)))
    K0 (MR y + so + LOW y + Pout y) = referencePhysicalDensityOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R u y := by
  classical
  intro R u K0 MR LOW Pout
  let Drift : R3 → SphereL2 :=
    (nativeModelRaisingDrift hO hD hF g g2 hg hg2 L q F).val
  have hR : ContDiff ℝ ∞ R :=
    ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual dr Ar p L hdr hAr
  have hpEnd : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := by
    simpa only [one_mul] using hSegment 1 ⟨zero_le_one,le_rfl⟩
  have hDict := referencePhysicalDensityOperator_finiteCore_eq_nativeModel_add_full_residual
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
    hg g2 hg2 hreg q hq dr Ar p hdr hAr F y hyRoom hInv hpEnd
  -- Preserve every dictionary let. These names are exactly its 36-let telescope.
  extract_lets (merge := false) (useContext := false) (descend := false)
    dR du dK dIin dIout dAhi dAlo dD dFh dFl dEh dEl dF dE dMF dME
    dQ dSigma db dGamma df drad dCovD dUF dUE dUA dUFE dUEE dUSigma dUD
    dUFirst dUSecond dUAngular dUProducts dUDouble dJF at hDict
  have hPhysical : referencePhysicalDensityOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R u y =
      K0 (MR y + Drift y) + dJF + dUFirst + dUSecond + dUAngular + dUProducts + dUDouble :=
    hDict
  have hKPointEvaluation (v : SphereL2) : K0 v =
      sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD v) := by
    rfl
  have hJ : K0 (nativeMixedJOut hF hO hD g g2 L q dr Ar p F y) =
      K0 (Drift y) + dJF := by
    have hJRaw := nativeMixedJOut_negative_graph_of_mem_closedBall
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hg2 hreg
      q hq dr Ar p F y hyRoom
    extract_lets (merge := true) (useContext := true) (descend := false) at hJRaw
    exact hJRaw
  have hUF : K0 (nativeUFirstOut hF hO hD g hg g2 L q dr Ar p hdr hAr F y) = dUFirst := by
    have hUFRaw := nativeUFirstOut_negative_graph
      hF hO hD g hg g2 L q dr Ar p hdr hAr F y
    extract_lets (merge := true) (useContext := true) (descend := false) at hUFRaw
    exact hUFRaw
  have hLow : K0 (LOW y) = K0 (Drift y) + dJF + dUFirst := by
    change K0 (nativeMixedJOut hF hO hD g g2 L q dr Ar p F y +
      nativeUFirstOut hF hO hD g hg g2 L q dr Ar p hdr hAr F y) = _
    have hLowMap := K0.map_add
      (nativeMixedJOut hF hO hD g g2 L q dr Ar p F y)
      (nativeUFirstOut hF hO hD g hg g2 L q dr Ar p hdr hAr F y)
    have hLowSum := congrArg₂
      (fun z t : SphereSobolev (-(1/2 : ℝ)) => z + t) hJ hUF
    exact hLowMap.trans hLowSum
  have hSOValues :
      ActualHigherSFormation.nativeHigherSNegative
        hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 g2 q R u y =
          dUSecond + dUAngular + dUDouble := by
    have hSORaw := nativeHigherSNegative_eq_full_dictionary_rows
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q dR du y
    extract_lets (merge := true) (useContext := true) (descend := false) at hSORaw
    exact hSORaw
  have hSOEvaluation := hKPointEvaluation (so)
  have hSOInferred := hSOEvaluation.trans hso
  have hSO : K0 (so) = dUSecond + dUAngular + dUDouble :=
    hSOInferred.trans hSOValues
  have hProducts : K0 (Pout y) = dUProducts := by
    have hProductsRaw := physicalProductsPostmap_negative_graph_of_radial_room
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg g2 q hq dR hR du
      y hyRoom hr hInv hSegment
    extract_lets (merge := true) (useContext := true) (descend := false) at hProductsRaw
    have hMapAlias : dK = K0 := by rfl
    have hRadiusAlias : dR = R := by rfl
    have hInputAlias : du = u := by rfl
    rw [hMapAlias, hRadiusAlias, hInputAlias] at hProductsRaw
    simpa only [Pout, u] using hProductsRaw
  exact assemble_full_physical_graph_at K0 (MR y) (Drift y) (so) (LOW y) (Pout y)
    _ dJF dUFirst dUSecond dUAngular dUProducts dUDouble hPhysical hLow hSO hProducts

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
  (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)

theorem exists_uniform_same_packet_full_physical_graph (hL : 0 < L)
    (hKernel : UnitBallValueTraceKernel τ0) :
  ∃ etaGraph : ℝ, 0 < etaGraph ∧ etaGraph ≤ data.eta0 ∧
  ∀ q ∈ Icc (0 : ℝ) 1, ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
  ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 2 ≤ p →
  ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaGraph →
  ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
  ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
  (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
  (∀ x ∈ K, referenceRadius dr Ar p L x * (actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
  let R : R3 → ℝ := referenceRadius dr Ar p L
  let Pout : R3 → SphereL2 := fun x => (sphereSobolevZeroEquiv hO hD).symm
    (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
      (referencePhysicalDensityProductsHalfOperator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R x
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) F x)))
  let V : R3 → SphereL2 := fun x =>
    (nativeModelRaising hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr F).val x +
    ActualHigherSFormation.nativeHigherSOut hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      dr Ar p hdr hAr q hreg data.δ0 data.germs g2 F x +
    nativeMixedFirstCorrectionLowOut hF hO hD g hg g2 L q dr Ar p hdr hAr F x + Pout x
  ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧ MemLp V 2 (volume : Measure R3) ∧
  tsupport V ⊆ tsupport F.val ∧
  ∀ x : R3, physicalL2Inclusion hO hD (V x) =
    referencePhysicalDensityOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      g2 q R (finiteCoreSobolevLift hO hD (3/2 : ℝ) F) x := by
  classical
  obtain ⟨etaFormation, hetaFormation, hetaFormation0, hFormation⟩ :=
    ActualLowerSSelfFormation.exists_uniform_same_packet_higherS_formation
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data hL hKernel g2 hg2
  let etaGraph : ℝ := min etaFormation (data.δ / 2)
  have hetaGraph : 0 < etaGraph := lt_min hetaFormation (div_pos data.δ_pos (by norm_num))
  have hetaGraph0 : etaGraph ≤ data.eta0 :=
    (min_le_left _ _).trans hetaFormation0
  refine ⟨etaGraph, hetaGraph, hetaGraph0, ?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaG K hK hKball F hFs hb hs
  intro R Pout V
  have hp1 : 1 ≤ p := by omega
  have hetaForm : eta ≤ etaFormation := hetaG.trans (min_le_left _ _)
  have hetaDelta : eta ≤ data.δ / 2 := hetaG.trans (min_le_right _ _)
  have hR : ContDiff ℝ ∞ R :=
    ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual dr Ar p L hdr hAr
  have hKgeom : K ⊆ closedBall y0 ρ :=
    fun x hx => ball_subset_closedBall (hKball hx)
  have hRadius (x : R3) (hx : x ∈ K) : 0 < R x ∧ R x < data.δ := by
    have hr : 0 < R x := referenceRadius_pos dr Ar p L x hdr hAr
    have hb2 : 1 ≤ (actualReferenceBeta g L q dr Ar p x)^2 := by
      nlinarith only [hb x hx]
    have hrBeta : R x ≤ R x * (actualReferenceBeta g L q dr Ar p x)^2 := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hb2 hr.le
    have hrEta : R x ≤ eta := hrBeta.trans (hs x hx)
    exact ⟨hr, (hrEta.trans hetaDelta).trans_lt (by linarith only [data.δ_pos])⟩
  have hRoom : ∀ x ∈ K, R x ≠ 0 ∧
      (∀ θ ∈ Icc (0 : ℝ) 1, (q,(x,θ*R x)) ∈
        referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) ∧
      (∀ ξ : UnitSphere,
        (referenceFramedNormalizedJacobian g L Φ (q,((x,R x),ξ.val))).IsInvertible) := by
    intro x hx
    have hr := hRadius x hx
    have hTube : (q,(x,R x)) ∈
        Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-data.δ) data.δ) :=
      ⟨hq,hKgeom hx,⟨(neg_nonpos.mpr data.δ_pos.le).trans hr.1.le,hr.2.le⟩⟩
    have hJac := referenceFramedNormalizedJacobian_isInvertible_on_actual_coefficient_tube
      g L y0 Φ B ε C ρ H a w hData data.δ data.δ_pos data.δ_le
      (q,(x,R x)) hTube
    refine ⟨ne_of_gt hr.1, ?_, hJac⟩
    intro θ hθ
    have hθ0 : 0 ≤ θ*R x := mul_nonneg hθ.1 hr.1.le
    have hθR : θ*R x ≤ R x := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hθ.2 hr.1.le
    exact data.parameter_subset
      ⟨hq,hKgeom hx,⟨(neg_nonpos.mpr data.δ_pos.le).trans hθ0,hθR.trans hr.2.le⟩⟩
  let u : R3 → SphereSobolev (3/2 : ℝ) := finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  let K0 := physicalL2Inclusion hO hD
  let MR : R3 → SphereL2 :=
    (nativeModelRaising hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr F).val
  let SO : R3 → SphereL2 :=
    ActualHigherSFormation.nativeHigherSOut hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      dr Ar p hdr hAr q hreg data.δ0 data.germs g2 F
  let LOW : R3 → SphereL2 :=
    nativeMixedFirstCorrectionLowOut hF hO hD g hg g2 L q dr Ar p hdr hAr F
  let Drift : R3 → SphereL2 :=
    (nativeModelRaisingDrift hO hD hF g g2 hg hg2 L q F).val
  have hRep := finiteCoreSobolevLift_representation hO hD (3/2 : ℝ) (by norm_num) F
  have huSupp : tsupport u ⊆ tsupport F.val := hRep.2.2.1
  have huZero (x : R3) (hx : x ∉ K) : u x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (hFs (huSupp h)))
  have hSOAll := hFormation q hq dr hdr hdr1 Ar hAr p hp1 eta heta hetaForm
    K hK hKball F hFs hb hs
  have hSOGraph := hSOAll.1.2.2.2.2.1
  have hSORegular := hSOAll.1.2.2.2.2.2.1
  have hPAll := referencePhysicalDensityProductsForward_literal_postmap_section_properties
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg
    g2 hg2 q hq R hR K hKgeom hRoom F hFs
  have hPSmooth := hPAll.1
  have hPSupp := hPAll.2.2.2.1
  have hLowRegular := nativeMixedFirstCorrectionLowOut_smooth_compact
    hF hO hD g hg g2 hg2 L q dr Ar p hdr hAr F
  have hMRSmooth : ContDiff ℝ ∞ MR :=
    (nativeModelRaising hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr F).property.1
  have hTLocal := finiteCoreSupportPreserving_nativeT hO hD hF g hg L q dr Ar p hdr hAr
  have hULocal := finiteCoreSupportPreserving_nativeU hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
  have hMRLocal := finiteCoreSupportPreserving_add hO hD _ _
    (finiteCoreSupportPreserving_add hO hD _ _ hTLocal hTLocal) hULocal F
  have hMRSupp : tsupport MR ⊆ tsupport F.val := by
    simpa only [MR,nativeModelRaising,two_mul] using hMRLocal
  have hJSupp : tsupport (nativeMixedJOut hF hO hD g g2 L q dr Ar p F) ⊆ tsupport F.val := by
    apply closure_minimal ?_ (isClosed_tsupport F.val)
    intro x hx
    by_contra hNot
    have hz : u x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hNot (huSupp h))
    dsimp only [u] at hz
    apply hx
    simp only [nativeMixedJOut,hz,map_zero]
  have hUFSupp := (tsupport_nativeUFirstOut_subset hF hO hD g hg g2 L q dr Ar p hdr hAr F).2.1
  have hLowSupp : tsupport LOW ⊆ tsupport F.val :=
    (tsupport_add _ _).trans (union_subset hJSupp hUFSupp)
  have hVSmooth : ContDiff ℝ ∞ V :=
    ((hMRSmooth.add hSORegular.1).add hLowRegular.1).add hPSmooth
  have hVZero (x : R3) (hx : x ∉ tsupport F.val) : V x = 0 := by
    have hMR0 : MR x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hMRSupp h))
    have hSO0 : SO x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hSORegular.2.1 h))
    have hLow0 : LOW x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hLowSupp h))
    have hP0 : Pout x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hPSupp h))
    change MR x + SO x + LOW x + Pout x = 0
    simp only [hMR0,hSO0,hLow0,hP0,add_zero]
  have hVSupp : tsupport V ⊆ tsupport F.val := by
    apply closure_minimal ?_ (isClosed_tsupport F.val)
    intro x hx
    by_contra hn
    exact hx (hVZero x hn)
  have hVCompact : HasCompactSupport V :=
    F.property.2.1.of_isClosed_subset (isClosed_tsupport V) hVSupp
  refine ⟨hVSmooth,hVCompact,hVSmooth.continuous.memLp_of_hasCompactSupport hVCompact,hVSupp,?_⟩
  intro y
  by_cases hy : y ∈ tsupport F.val
  · have hyK : y ∈ K := hFs hy
    have hyRoom : ‖y-y0‖ ≤ ρ := by
      simpa only [mem_closedBall,dist_eq_norm] using hKgeom hyK
    have hAt := hRoom y hyK
    change K0 (MR y + SO y + LOW y + Pout y) = _
    have hGraphRaw := physical_graph_at_of_original_higherS_graph
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg g2 hg2
      q hq dr Ar p hdr hAr F y hyRoom hAt.1 hAt.2.2 hAt.2.1 (SO y) (hSOGraph y)
    extract_lets (merge := true) (useContext := true) (descend := false) at hGraphRaw
    exact hGraphRaw
  · have hPhysicalSupp := tsupport_referencePhysicalDensityOperator_subset
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R u
    have hPhysicalZero : referencePhysicalDensityOperator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R u y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hy (huSupp (hPhysicalSupp h)))
    exact (congrArg K0 (hVZero y hy)).trans (K0.map_zero.trans hPhysicalZero.symm)
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.MainPhysicalGraphBridge
