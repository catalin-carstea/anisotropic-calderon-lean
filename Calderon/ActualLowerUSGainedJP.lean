import Calderon.ActualLowerUSJPCoefficient

/-! Author-support GPT-6.1 Sol. Before-code ../gained-jp-upfront-v001.md.
Complete actual fixed-metric J/P producer: original coordinate weights, actual
paired gains, genuine fixed Js, original lower-only J mass. No analytic cap
callback is a theorem premise. Source-only pending Root checks; no compiler. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSGainedJP
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualFullEGainedEndpoints ActualAngularHighDraft ActualAngularPiDraft
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints ActualMixedAngularPairedGains
  ActualLowerUSSecondRow ActualLowerUSFirstAngularGainPair ActualHigherSPhysicalPairing
  ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation NormalizedPrincipalMetric
  ActualLowerUSJPWords ActualLowerUSJPCoefficient ActualLowerUSFirstOutput ActualLowerUSJPPresentation
  ActualHigherSLeadingBracketGain ActualHigherSCoordinateWeightBounds
  ActualFiniteHarmonicModel.ActualLowerUSLowerWordAdjoints
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
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


local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "Pout" g2:max dr:max Ar:max p:max q:max =>
  nativeFirstOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q
local notation "Comp" g2:max hg2:max dr:max Ar:max p:max hdr:max hAr:max q:max =>
  nativeJPCommutatorDensity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    g2 hg2 dr Ar p hdr hAr q
local notation "PW" => quadraticPWordCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "Word" => lowerQuadraticWord hO hD hF
local notation "WordStar" => lowerQuadraticWordAdjoint hO hD hF
private abbrev finiteWeightValue (s : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : SphereL2 :=
  (coreWeightOperator hO hD (SpectralWeightedGraph.besselWeight s) F).val x
local notation "WH" F:max x:max => ‖finiteWeightValue hO hD (1/2 : ℝ) F x‖
local notation "WHi" F:max x:max => ‖finiteWeightValue hO hD (3/2 : ℝ) F x‖

private lemma scalar_mass_bound {ι : Type*} [Fintype ι] (c f : ι → ℝ) (A B : ℝ)
    (hB : 0 ≤ B) (hc : (∑ i,|c i|) ≤ A) (hf : ∀ i, |f i| ≤ B) :
    |∑ i,c i*f i| ≤ A*B := by
  calc
    _ ≤ ∑ i,|c i*f i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i,|c i| * |f i| := by simp only [abs_mul]
    _ ≤ ∑ i,|c i| * B := Finset.sum_le_sum
      (fun i _ => mul_le_mul_of_nonneg_left (hf i) (abs_nonneg _))
    _ = (∑ i,|c i|)*B := (Finset.sum_mul _ _ _).symm
    _ ≤ A*B := mul_le_mul_of_nonneg_right hc hB

/-- Strong actual r² cap in both original finite Sobolev orientations. -/
theorem exists_nativeJP_uniform_profile_bound_strong
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ C_JP : ℝ, 0 < C_JP ∧ ∃ etaJP : ℝ, 0 < etaJP ∧ etaJP ≤ data.eta0 ∧ etaJP ≤ 1 ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
      ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 1 ≤ p →
      ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaJP →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      (∀ x ∈ K, CoordinateBootstrapJets.coordinateH8
        (referenceNormalizedPrincipalDifference g g2 L q) x ≤ eta*referenceRadius dr Ar p L x) →
      ∀ U V : smoothCompactFiniteSphereCore hO hD,
      tsupport U.val ⊆ K → tsupport V.val ⊆ K → ∀ j : Fin 3, ∀ x ∈ K,
        |(Comp g2 hg2 dr Ar p hdr hAr q) j U V x| ≤
          C_JP*eta*(referenceRadius dr Ar p L x)^2*(WH U x)*(WHi V x) ∧
        |(Comp g2 hg2 dr Ar p hdr hAr q) j U V x| ≤
          C_JP*eta*(referenceRadius dr Ar p L x)^2*(WHi U x)*(WH V x) := by
  obtain ⟨mixed,δ,hδ,gen,M,hM,etaG,hEtaG,hEtaG0,hEtaG1,hGain⟩ :=
    exists_retained_firstAngular_gain_pair_uniform_profile_caps
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 hL hKernel
  obtain ⟨MW,hMW,hWeights⟩ := exists_coordinateWeightBase_uniform_first_caps g g2 hg hg2 L y0 ρ
  obtain ⟨CJ,hCJ,hJMass⟩ := exists_nativeULowerAdjointZero_lower_uniform_mass
    hO hD hF g g2 hg hg2 L hL y0 ρ
  let C0 : ℝ := 6*MW*jpOrdinaryGeneratorBudget hF hO hD*M
  have hC0 : 0 < C0 := by
    dsimp only [C0]
    exact mul_pos
      (mul_pos (mul_pos (by norm_num) (zero_lt_one.trans_le hMW))
        (jpOrdinaryGeneratorBudget_pos hF hO hD)) hM
  let C_JP : ℝ := 1+CJ*C0
  have hCJP : 0 < C_JP := by dsimp only [C_JP]; positivity
  refine ⟨C_JP,hCJP,etaG,hEtaG,hEtaG0,hEtaG1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaG K _hK hBall hb hs hH8 U V _hSU _hSV j x hx
  have hxClosed : x ∈ closedBall y0 ρ := ball_subset_closedBall (hBall hx)
  have heta1 : eta ≤ 1 := hetaG.trans hEtaG1
  have hGainHere := hGain q hq dr hdr hdr1 Ar hAr p hp eta heta hetaG x hxClosed (hBall hx)
    (hb x hx) (hs x hx) (hH8 x hx)
  have hGainPoint (k : Fin 3) (v : FirstAngularIndex) := hGainHere.2.2.2 k v
  have hWeight (k : Fin 3) : |firstCoordinateWeight g g2 L j k ((Tq dr Ar p q) x)| ≤ MW := by
    rw [firstCoordinateWeight_eq_base]
    exact (hWeights q hq x hxClosed j k).1
  let r := referenceRadius dr Ar p L x
  have hWordNorm (adjoint : Bool) (ij : LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex) :
      ‖PW adjoint mixed δ gen g2 dr Ar p q j x ij‖ ≤ C0*r^2 := by
    exact norm_quadraticPWord_le g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data adjoint mixed δ gen g2 dr Ar p q j x M MW hM.le (zero_le_one.trans hMW)
      (fun k v => let hc := hGainPoint k v; ⟨hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1⟩) hWeight ij
  let u := finiteCoreSobolevLift hO hD (3/2 : ℝ) U x
  let v := finiteCoreSobolevLift hO hD (3/2 : ℝ) V x
  let uh := finiteCoreSobolevLift hO hD (1/2 : ℝ) U x
  let vh := finiteCoreSobolevLift hO hD (1/2 : ℝ) V x
  have hu : IH u = uh := sphereSobolevInclusionL_finiteCoreSobolevLift hO hD _ _ (by norm_num) U x
  have hv : IH v = vh := sphereSobolevInclusionL_finiteCoreSobolevLift hO hD _ _ (by norm_num) V x
  have huN : ‖u‖ = WHi U x := norm_finiteCoreSobolevLift hO hD (3/2 : ℝ) U x
  have hvN : ‖v‖ = WHi V x := norm_finiteCoreSobolevLift hO hD (3/2 : ℝ) V x
  have huhN : ‖uh‖ = WH U x := norm_finiteCoreSobolevLift hO hD (1/2 : ℝ) U x
  have hvhN : ‖vh‖ = WH V x := norm_finiteCoreSobolevLift hO hD (1/2 : ℝ) V x
  let wordForm (ij : LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex) : ℝ :=
    ⟪(WordStar ij U).val x,(Pout g2 dr Ar p q) j V x⟫_ℝ -
      ⟪U.val x,(Pout g2 dr Ar p q) j (Word ij V) x⟫_ℝ
  have hGraph (ij : LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex) :
      wordForm ij = PP uh (PW false mixed δ gen g2 dr Ar p q j x ij v) :=
    quadraticPWord_physical_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data mixed δ gen g2 dr Ar p q j x hGainHere.1 hGainHere.2.1 hGainHere.2.2.1 ij U V
  have hStarGraph (ij : LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex) :
      wordForm ij = PP vh (PW true mixed δ gen g2 dr Ar p q j x ij u) := by
    rw [hGraph,← hu,← hv]
    exact quadraticPWord_pairing g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data mixed δ gen g2 dr Ar p q j x hGainHere.1 hGainHere.2.1 ij u v
  have hFwd (ij : LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex) :
      |wordForm ij| ≤ C0*r^2*(WH U x)*(WHi V x) := by
    rw [hGraph]
    calc
      _ ≤ ‖uh‖*‖PW false mixed δ gen g2 dr Ar p q j x ij v‖ := abs_sphereSobolevDualPairing_le _ _ _
      _ ≤ ‖uh‖*((C0*r^2)*‖v‖) := mul_le_mul_of_nonneg_left
        (((PW false mixed δ gen g2 dr Ar p q j x ij).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (hWordNorm false ij) (norm_nonneg v))) (norm_nonneg uh)
      _ = _ := by rw [huhN,hvN]; ring
  have hRev (ij : LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex) :
      |wordForm ij| ≤ C0*r^2*(WHi U x)*(WH V x) := by
    rw [hStarGraph]
    calc
      _ ≤ ‖vh‖*‖PW true mixed δ gen g2 dr Ar p q j x ij u‖ := abs_sphereSobolevDualPairing_le _ _ _
      _ ≤ ‖vh‖*((C0*r^2)*‖u‖) := mul_le_mul_of_nonneg_left
        (((PW true mixed δ gen g2 dr Ar p q j x ij).le_opNorm u).trans
          (mul_le_mul_of_nonneg_right (hWordNorm true ij) (norm_nonneg u))) (norm_nonneg vh)
      _ = _ := by rw [hvhN,huN]; ring
  obtain ⟨c,hc,hJ,hMass⟩ := hJMass q hq dr hdr hdr1 Ar hAr p hp eta heta heta1
    x hxClosed (hb x hx) (hH8 x hx) (hs x hx)
  have hExpand := nativeJP_eq_lower_word_sum g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    g2 hg2 dr Ar p hdr hAr q c hc hJ j U V x
  simp only [hExpand]
  change |∑ ij,c ij x*wordForm ij| ≤ _ ∧ |∑ ij,c ij x*wordForm ij| ≤ _
  have hCoef : CJ*C0 ≤ C_JP := by dsimp only [C_JP]; linarith
  constructor
  · calc
      _ ≤ (CJ*eta)*(C0*r^2*(WH U x)*(WHi V x)) :=
        scalar_mass_bound _ _ _ _ (by positivity) hMass hFwd
      _ = (CJ*C0)*eta*r^2*(WH U x)*(WHi V x) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCoef heta) (sq_nonneg r)) (norm_nonneg _)) (norm_nonneg _)
  · calc
      _ ≤ (CJ*eta)*(C0*r^2*(WHi U x)*(WH V x)) :=
        scalar_mass_bound _ _ _ _ (by positivity) hMass hRev
      _ = (CJ*C0)*eta*r^2*(WHi U x)*(WH V x) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCoef heta) (sq_nonneg r)) (norm_nonneg _)) (norm_nonneg _)

/-- Requested original-profile C eta cap, with all constants before profiles. -/
theorem exists_nativeJP_uniform_profile_bound
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ C_JP : ℝ, 0 < C_JP ∧ ∃ etaJP : ℝ, 0 < etaJP ∧ etaJP ≤ data.eta0 ∧ etaJP ≤ 1 ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
      ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 1 ≤ p →
      ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaJP →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      (∀ x ∈ K, CoordinateBootstrapJets.coordinateH8
        (referenceNormalizedPrincipalDifference g g2 L q) x ≤ eta*referenceRadius dr Ar p L x) →
      ∀ U V : smoothCompactFiniteSphereCore hO hD,
      tsupport U.val ⊆ K → tsupport V.val ⊆ K → ∀ j : Fin 3, ∀ x ∈ K,
        |(Comp g2 hg2 dr Ar p hdr hAr q) j U V x| ≤ C_JP*eta*(WH U x)*(WHi V x) ∧
        |(Comp g2 hg2 dr Ar p hdr hAr q) j U V x| ≤ C_JP*eta*(WHi U x)*(WH V x) := by
  obtain ⟨CJP,hCJP,etaJP,hEtaJP,hEtaJP0,hEtaJP1,hBound⟩ :=
    exists_nativeJP_uniform_profile_bound_strong
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 hL hKernel
  refine ⟨CJP,hCJP,etaJP,hEtaJP,hEtaJP0,hEtaJP1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaJP K hK hBall hb hs hH8 U V hSU hSV j x hx
  have h := hBound q hq dr hdr hdr1 Ar hAr p hp eta heta hetaJP K hK hBall hb hs hH8 U V hSU hSV j x hx
  let r := referenceRadius dr Ar p L x
  let beta := actualReferenceBeta g L q dr Ar p x
  have hr : 0 < r := referenceRadius_pos dr Ar p L x hdr hAr
  have hr1 : r ≤ 1 := by
    have hb2 : 1 ≤ beta^2 := one_le_pow₀ (hb x hx)
    exact ((le_mul_of_one_le_right hr.le hb2).trans (hs x hx)).trans (hetaJP.trans hEtaJP1)
  have hr2 : r^2 ≤ 1 := by
    simpa only [pow_two,one_mul] using mul_self_le_mul_self hr.le hr1
  constructor
  · exact h.1.trans (by
      have hr' := mul_le_mul_of_nonneg_left hr2 (mul_nonneg hCJP.le heta)
      simpa only [mul_one] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hr' (norm_nonneg _)) (norm_nonneg _))
  · exact h.2.trans (by
      have hr' := mul_le_mul_of_nonneg_left hr2 (mul_nonneg hCJP.le heta)
      simpa only [mul_one] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hr' (norm_nonneg _)) (norm_nonneg _))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSGainedJP
