import Calderon.CompactParameterReferenceDrift
import Calderon.JointRawCoefficientJetTransport

/-! Raw inverse/determinant smoothness is only local at positive points. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator NormalCoordinatesFrame

/-- Derive appended raw facts for any given exact same drift tuple; no existential or flow choice occurs. -/
theorem conformalReferenceFramedDriftData_raw_coefficient_jets
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : ConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w) :
    JointRawCoefficientMixedJetIdentities y0 ρ H a
      (referenceFramedNormalMatrixForCoefficients g L Φ) w ∧
    JointRawCoefficientNonradialBounds y0 ρ (referenceFramedNormalMatrixForCoefficients g L Φ) ∧
    JointRawCoefficientZeroRadialJets y0 ρ (referenceFramedNormalMatrixForCoefficients g L Φ) := by
  have hOld : ConformalReferencePositiveCoefficientData g L y0 Φ B ε C ρ H a w := hData.1
  rcases hOld with
    ⟨hNormal,hρ,hρε,hHDef,haDef,hwDef,hH,hPos,ha,hw,hSupport,hLocal,hZeroJet,hUE,hMixed⟩
  rcases hNormal with ⟨hEndpoint,hε,hC,hFrame,hBij,hG,hGeom,hFull⟩
  let G := referenceFramedNormalMatrixForCoefficients g L Φ
  have hGop : ContDiff ℝ ∞ (referenceFramedNormalOperatorForCoefficients g L Φ) :=
    hG.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))
  have hGmat : ContDiff ℝ ∞ G := operatorMatrixMap.contDiff.comp hGop
  have heq : ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ 4*ρ →
      ∀ r : ℝ, |r| ≤ 4*ρ → ∀ z : R3, ‖z‖ ≤ 2 →
        H ((q,(y,r)),z) = G ((q,(y,r)),z) ∧
        a ((q,(y,r)),z) = matrixPrincipalCoefficient G ((q,(y,r)),z) ∧
        w ((q,(y,r)),z) = matrixVolumeDensity G ((q,(y,r)),z) := by
    intro q hq y hy r hr z hz
    exact hLocal q hq y hy r hr z (by simpa only [mem_closedBall,dist_zero_right] using hz)
  have hIdent := jointRawCoefficientMixedJetIdentities_of_geometric_room
    H a G w hH ha hw hGmat hPos ρ hρ y0 heq
  have hBounds := jointRawCoefficientNonradialBounds_transfer y0 ρ H a G w hIdent hMixed
  have hZero := jointRawCoefficientZeroRadialJets_of_geometric_room H a G w ρ hρ y0 heq hZeroJet
  exact ⟨hIdent,hBounds,hZero⟩

/-- Select prior drift tuple exactly once, return its entire original Prop once followed by J9 facts. -/
theorem exists_compact_parameter_conformalReference_framed_drift_with_raw_nonradial_jets
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3) :
    ∃ (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
      (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
      (w : (ℝ × (R3 × ℝ)) × R3 → ℝ),
      ConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w ∧
      JointRawCoefficientMixedJetIdentities y0 ρ H a
        (referenceFramedNormalMatrixForCoefficients g L Φ) w ∧
      JointRawCoefficientNonradialBounds y0 ρ (referenceFramedNormalMatrixForCoefficients g L Φ) ∧
      JointRawCoefficientZeroRadialJets y0 ρ (referenceFramedNormalMatrixForCoefficients g L Φ) := by
  obtain ⟨Φ,B,ε,C,ρ,H,a,w,hData⟩ :=
    exists_compact_parameter_conformalReference_framed_drift g hg L y0
  have hRaw := conformalReferenceFramedDriftData_raw_coefficient_jets
    g L y0 Φ B ε C ρ H a w hData
  exact ⟨Φ,B,ε,C,ρ,H,a,w,hData,hRaw.1,hRaw.2.1,hRaw.2.2⟩

end OAI.AnisotropicCalderon.ConnectionError
