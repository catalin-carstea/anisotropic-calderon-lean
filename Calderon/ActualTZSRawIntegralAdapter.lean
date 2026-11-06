import Calderon.ActualTSSignedCrossOriginalIntegral

/-! The original signed T/S bound with the factor four pulled outside
the integral, in the form used by the physical coercivity consumer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTZSRawIntegralAdapter
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  PrincipalCommutator ReferenceWeightedApproximation ReferenceDensityBounds ConformalDepth NormalizedPrincipalMetric

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
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

private theorem raw_integrable_and_four_integral (mu f : R3 → ℝ)
    (hf : Integrable (fun x => mu x * (4 * f x))) :
    Integrable (fun x => mu x * f x) ∧
    (∫ x, mu x * (4 * f x)) = 4 * (∫ x, mu x * f x) := by
  have hscale : (fun x : R3 => mu x * (4 * f x)) =
      (fun x => (4 : ℝ) * (mu x * f x)) := by
    funext x
    ring
  rw [hscale] at hf ⊢
  have hinv : (fun x : R3 => (1 / 4 : ℝ) * (4 * (mu x * f x))) =
      (fun x => mu x * f x) := by
    funext x
    ring
  refine ⟨?_, integral_const_mul _ _⟩
  simpa only [hinv] using hf.const_mul (1 / 4 : ℝ)

/-- The checked signed bound in Main's exact raw integral form. The original
principal-jet hypothesis is retained even though this bound does not need it. -/
theorem exists_original_signed_TZS_raw_integral_bound
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
  ∃ CTZS etaTZS : ℝ,0<CTZS ∧ 0<etaTZS ∧ etaTZS≤data.eta0 ∧
  ∀ q∈Icc (0:ℝ) 1,∀ dr:ℝ,∀ hdr:0<dr,dr≤1 →
  ∀ Ar:ℝ,∀ hAr:0<Ar,∀ p:ℕ,1≤p →
  ∀ eta:ℝ,0≤eta → eta≤etaTZS →
  ∀ K:Set R3,IsCompact K → K⊆ball y0 ρ →
  ∀ F:smoothCompactFiniteSphereCore hO hD,tsupport F.val⊆K →
  (∀ x∈K,1≤actualReferenceBeta g L q dr Ar p x) →
  (∀ x∈K,referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2≤eta) →
  (∀ x∈K,CoordinateBootstrapJets.coordinateH8
    (referenceNormalizedPrincipalDifference g g2 L q) x≤eta*referenceRadius dr Ar p L x) →
  let mu:R3→ℝ := fun x => referenceDensityFamily g L (q,x)
  let SO:R3→SphereL2 := ActualHigherSFormation.nativeHigherSOut hF hO hD
    g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 dr Ar p hdr hAr q hreg data.δ0 data.germs g2 F
  let SD:R3→SphereL2 := ActualHigherSAdjointFormation.higherSAdjointOut
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs g2 dr Ar p hdr hAr q F
  let cross:R3→ℝ := fun x =>
    ⟪(nativeT hO hD hF g hg L q dr Ar p hdr hAr F).val x,SO x⟫_ℝ-
    ⟪((nativeTdag hO hD hF g hg L q dr Ar p hdr hAr F)+
      (nativeZ hO hD hF g hg L q dr Ar p hdr hAr F)).val x,SD x⟫_ℝ
  Integrable (fun x => mu x*cross x) ∧
  |4*(∫ x,mu x*cross x)|≤CTZS*eta*(∫ x,mu x*
    finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x) := by
  obtain ⟨Ct,et,hCt,het,het0,Ht⟩ :=
    ActualTSSignedCrossOriginalIntegral.exists_original_signed_TS_integral_bound
      hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data hL hKernel g2 hg2
  refine ⟨Ct,et,hCt,het,het0,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaRoom K hK hKb F hFsupport hBeta hScale _hH8
  let mu:R3→ℝ := fun x => referenceDensityFamily g L (q,x)
  let SO:R3→SphereL2 := ActualHigherSFormation.nativeHigherSOut hF hO hD
    g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 dr Ar p hdr hAr q hreg data.δ0 data.germs g2 F
  let SD:R3→SphereL2 := ActualHigherSAdjointFormation.higherSAdjointOut
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs g2 dr Ar p hdr hAr q F
  let cross:R3→ℝ := fun x =>
    ⟪(nativeT hO hD hF g hg L q dr Ar p hdr hAr F).val x,SO x⟫_ℝ-
    ⟪((nativeTdag hO hD hF g hg L q dr Ar p hdr hAr F)+
      (nativeZ hO hD hF g hg L q dr Ar p hdr hAr F)).val x,SD x⟫_ℝ
  obtain ⟨hI,hBound⟩ :=
    Ht q hq dr hdr hdr1 Ar hAr p hp eta heta hetaRoom K hK hKb F hFsupport hBeta hScale
  change Integrable (fun x => mu x * (4 * cross x)) at hI
  change |∫ x, mu x * (4 * cross x)| ≤ _ at hBound
  obtain ⟨hRaw,hEq⟩ := raw_integrable_and_four_integral mu cross hI
  change Integrable (fun x => mu x * cross x) ∧ |4 * (∫ x, mu x * cross x)| ≤ _
  exact ⟨hRaw, by rw [← hEq]; exact hBound⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTZSRawIntegralAdapter

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTZSRawIntegralAdapter.exists_original_signed_TZS_raw_integral_bound
