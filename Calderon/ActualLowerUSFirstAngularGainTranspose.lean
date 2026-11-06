import Calderon.ActualLowerUSFirstAngularGainPair
import Calderon.ActualLowerUSSecondRow

/-!
Actual lower transpose of the same gain, true-adjoint high compatibility,
and a construction with the original parameter order and no cap hypotheses.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSFirstAngularGainPair
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualFullEGainedEndpoints ActualAngularHighDraft ActualAngularPiDraft
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ActualPiJacobiRadialGainedRows ActualMixedAngularPairedGains ActualLowerUSSecondRow
  ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation NormalizedPrincipalMetric
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

private lemma norm_lowerDistributionalTranspose_le (A : Half →L[ℝ] Neg) :
    ‖sphereLowerDistributionalTranspose A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro z
  change ‖sphereHalfDualCarrierEquiv
    ((ContinuousLinearMap.adjoint A) (sphereHalfDualCarrierEquiv z))‖ ≤ ‖A‖*‖z‖
  rw [LinearIsometryEquiv.norm_map]
  have hAdj : ‖ContinuousLinearMap.adjoint A‖ = ‖A‖ :=
    (ContinuousLinearMap.adjoint : (Half →L[ℝ] Neg) ≃ₗᵢ[ℝ] (Neg →L[ℝ] Half)).norm_map A
  simpa only [hAdj,LinearIsometryEquiv.norm_map] using
    (ContinuousLinearMap.adjoint A).le_opNorm (sphereHalfDualCarrierEquiv z)

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

local notation "MRoom" => MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0
  g L y0 Φ B ε C ρ H a w hData hg hreg data.δ0 data.germs
local notation "GRoom" δ:max => GeneratorEndpointRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs δ
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q



local notation "GL" => firstAngularGain
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "GH" => firstAngularGainHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "GS" => firstAngularGainSharpHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

/-- Actual angular dual transpose of the retained gain, with no extra endpoint premise. -/
def firstAngularGainSharpLow (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (j : Fin 3) (t : Tpar) (v : FirstAngularIndex) : Half →L[ℝ] Neg :=
  sphereLowerDistributionalTranspose (GL mixed δ gen j t v)
local notation "GSL" => firstAngularGainSharpLow
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

/-- The transpose's true adjoint high graph follows from the selected lower
transpose diagram, NOT from forward compatibility alone. -/
theorem firstAngularGainSharpLow_upper (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (j : Fin 3) (t : Tpar) (htG : t ∈ ParamRoom δ) (htM : t ∈ ParamRoom mixed.δ)
    (v : FirstAngularIndex) (u : Hi) :
    GSL mixed δ gen j t v (IH u) = JL (GS j t v u) := by
  apply sphereSobolev_eq_of_dualPairing_eq (1/2 : ℝ)
  intro z
  calc
    _ = PP (IH u) (GL mixed δ gen j t v z) :=
      (sphereSobolevDualPairing_lower_distributionalTranspose
        (GL mixed δ gen j t v) z (IH u)).symm
    _ = PP (GS j t v u) (JL z) := firstAngularGain_low_pairing
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data mixed δ gen j t htG htM v u z
    _ = _ := v016_pairing_inclusion_symm _ _

lemma norm_firstAngularGainSharpLow_le (mixed : MRoom) (δ : ℝ) (gen : GRoom δ)
    (j : Fin 3) (t : Tpar) (v : FirstAngularIndex) :
    ‖GSL mixed δ gen j t v‖ ≤ ‖GL mixed δ gen j t v‖ :=
  norm_lowerDistributionalTranspose_le _

/-- Actual same-germ paired gain endpoints are produced before every original
profile and finite angular input, with the adjoint low graph and budget included. -/
def RetainedFirstAngularGainPairUniformProfileCaps
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0) : Prop :=
    ∃ mixed : MRoom, ∃ δ : ℝ, 0 < δ ∧ ∃ gen : GRoom δ,
      ∃ M : ℝ, 0 < M ∧ ∃ etaG : ℝ, 0 < etaG ∧ etaG ≤ data.eta0 ∧ etaG ≤ 1 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaG →
      ∀ x ∈ closedBall y0 ρ, x ∈ ball y0 ρ →
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
      CoordinateBootstrapJets.coordinateH8 (referenceNormalizedPrincipalDifference g g2 L q) x ≤
        eta*referenceRadius dr Ar p L x →
      (Tq dr Ar p q) x ∈ ParamRoom δ ∧
      (Tq dr Ar p q) x ∈ ParamRoom mixed.δ ∧
      (Tq dr Ar p q) x ∈ ParamRoom data.δ ∧
      ∀ j : Fin 3, ∀ v : FirstAngularIndex,
        ‖GL mixed δ gen j ((Tq dr Ar p q) x) v‖ ≤ M ∧
        ‖GH mixed j ((Tq dr Ar p q) x) v‖ ≤ M ∧
        ‖GS j ((Tq dr Ar p q) x) v‖ ≤ M ∧
        ‖GSL mixed δ gen j ((Tq dr Ar p q) x) v‖ ≤ M ∧
        ∀ u : Hi, GSL mixed δ gen j ((Tq dr Ar p q) x) v (IH u) =
          JL (GS j ((Tq dr Ar p q) x) v u)

theorem exists_retained_firstAngular_gain_pair_uniform_profile_caps
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0) :
    RetainedFirstAngularGainPairUniformProfileCaps
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 hL hKernel := by
  obtain ⟨mixed,δ,hδ,gen,hRows⟩ := exists_retained_secondRow_uniform_profile_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 hL hKernel
  rcases hRows with ⟨C2,_hC2,etaG,hEtaG,hEtaG0,hEtaG1,hRows⟩
  obtain ⟨M,hM,hCap⟩ := exists_firstAngularGain_pair_cap
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data mixed δ gen
  refine ⟨mixed,δ,hδ,gen,M,hM,etaG,hEtaG,hEtaG0,hEtaG1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaG x hx hxBall hb hs hH8
  have hR := hRows q hq dr hdr hdr1 Ar hAr p hp eta heta hetaG x hx hxBall hb hs hH8
  refine ⟨hR.1,hR.2.1,hR.2.2.1,?_⟩
  intro j v
  have hc := hCap _ hR.1 hR.2.1 j v
  exact ⟨hc.2.2,hc.1,hc.2.1,
    (norm_firstAngularGainSharpLow_le
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data mixed δ gen j _ v).trans hc.2.2,
    fun u => firstAngularGainSharpLow_upper
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data mixed δ gen j _ hR.1 hR.2.1 v u⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSFirstAngularGainPair
