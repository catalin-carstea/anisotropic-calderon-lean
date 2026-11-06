import Calderon.ActualZSAdjointReferenceIntegral
import Calderon.ActualHigherSCommonProfileRoomData

/-! The whole minus-four Z/Sdag integral estimate at fixed endpoint data. The
coefficient caps and the common room are obtained internally. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualZSAdjointFixedDataIntegral
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualHigherSAdjointFormation ActualZSAdjointReferenceIntegral
  ReferenceWeightedApproximation ReferenceDensityBounds ConformalDepth

private lemma signed_weighted_integrable (mu f : R3 → ℝ)
    (h : Integrable (fun x => mu x*f x)) :
    Integrable (fun x => mu x*((-4)*f x)) := by
  have heq : (fun x => mu x*((-4)*f x))=(fun x => (-4)*(mu x*f x)) := by
    funext x
    ring
  rw [heq]
  exact h.const_mul (-4)

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

/-- Exact original minus-four full physical Z/Sdag term, on the same actual data. -/
def originalSignedZAdjointDensity (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  (-4)*⟪(nativeZ hO hD hF g hg L q dr Ar p hdr hAr F).val x,
    higherSAdjointOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg data.δ0 data.germs g2 dr Ar p hdr hAr q F x⟫_ℝ
local notation "ZD" => originalSignedZAdjointDensity
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data
attribute [local irreducible] finiteCoreReferenceProfileEnergy
/-- Full actual minus-four Z/Sdag integral bound; positive constants precede all later profiles. -/
theorem exists_original_signed_Z_adjoint_integral_bound
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ CZS etaZS : ℝ, 0 < CZS ∧ 0 < etaZS ∧ etaZS ≤ data.eta0 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaZS →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      Integrable (fun x => referenceDensityFamily g L (q,x)*ZD g2 dr Ar p hdr hAr q F x) ∧
      |∫ x, referenceDensityFamily g L (q,x)*ZD g2 dr Ar p hdr hAr q F x| ≤
        CZS*eta*∫ x, referenceDensityFamily g L (q,x)*finiteCoreReferenceProfileEnergy
          hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x := by
  obtain ⟨dF,_hdF,_hdF0,_hdFrho,Cm,_hJac,_hAdj⟩ :=
    exists_retained_higherS_adjoint g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg hKernel data.δ0 data.δ0_pos data.germs
  obtain ⟨etaOld,heOld,_heOld1,hOld⟩ :=
    exists_native_Z_Sdag_reference_integral_bound g L y0 Φ B ε C ρ H a w hData
      hg hcalc hF hO hD τ0 hL hreg data.δ0 data.germs dF Cm
  obtain ⟨CZS,hCZS,hBound⟩ := hOld g2 hg2
  refine ⟨CZS,min etaOld data.eta0,hCZS,lt_min heOld data.eta0_pos,min_le_right _ _,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta he K hK hKball F hsupp hb hs
  have h := hBound q hq dr hdr hdr1 Ar hAr p hp eta heta
    (he.trans (min_le_left _ _)) K hK hKball F hsupp hb hs
  constructor
  · unfold originalSignedZAdjointDensity
    exact signed_weighted_integrable (fun x => referenceDensityFamily g L (q,x)) _ h.1
  · simpa only [originalSignedZAdjointDensity] using h.2

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualZSAdjointFixedDataIntegral
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualZSAdjointFixedDataIntegral.exists_original_signed_Z_adjoint_integral_bound
