import Calderon.CompactParameterReferencePositiveCoefficients
import Calderon.ParameterNormalizedConformalDrift
import Calderon.MixedLinearDriftBounds

/-! UNCOMPILED author proposal. EXPANSION.md D1--D8 was saved before source.
The entire old positive-coefficient witness, including its same Phi/B, is retained. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator NormalCoordinatesFrame DirichletFamily

def ConformalReferencePositiveCoefficientData (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ) : Prop :=
  ConformalReferenceFramedNormalMetricData g L y0 Φ B ε C ∧
      0 < ρ ∧ 4*ρ ≤ ε ∧
      H = nearIdentityPositiveMatrixExtension (referenceFramedNormalOperatorForCoefficients g L Φ) ∧
      a = cutoffPrincipalCoefficient H ∧ w = cutoffVolumeDensity H ∧
      ContDiff ℝ ∞ H ∧ (∀ p, (H p).PosDef) ∧ ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ w ∧
      (∀ p : ℝ × (R3 × ℝ), ∀ z : R3, 3 ≤ ‖z‖ → a (p,z) = 0 ∧ w (p,z) = 0) ∧
      (∀ q ∈ Icc (0 : ℝ) 1, ∀ y, ‖y-y0‖ ≤ 4*ρ → ∀ r : ℝ, |r| ≤ 4*ρ →
        ∀ z ∈ closedBall (0 : R3) 2,
          H ((q,(y,r)),z) = referenceFramedNormalMatrixForCoefficients g L Φ ((q,(y,r)),z) ∧
          a ((q,(y,r)),z) = matrixPrincipalCoefficient
            (referenceFramedNormalMatrixForCoefficients g L Φ) ((q,(y,r)),z) ∧
          w ((q,(y,r)),z) = matrixVolumeDensity
            (referenceFramedNormalMatrixForCoefficients g L Φ) ((q,(y,r)),z)) ∧
      (∀ q ∈ Icc (0 : ℝ) 1, ∀ y, ‖y-y0‖ ≤ 2*ρ → ∀ z : R3, ‖z‖ ≤ 2 →
        H ((q,(y,0)),z) = 1 ∧ a ((q,(y,0)),z) = 1 ∧ w ((q,(y,0)),z) = 1 ∧
        HasDerivAt (fun r : ℝ => H ((q,(y,r)),z)) 0 0 ∧
        HasDerivAt (fun r : ℝ => a ((q,(y,r)),z)) 0 0 ∧
        HasDerivAt (fun r : ℝ => w ((q,(y,r)),z)) 0 0) ∧
      (∃ lam Lam : ℝ, ∀ p ∈
        Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ),
        TauCeti.PDE.UniformlyEllipticOn (closedBall (0 : R3) 1)
          (fun z => a (p,z)) lam Lam) ∧
      JointReferenceCoefficientMixedBounds y0 ρ H a w

def conformalReferenceFramedDriftBase (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (H : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ) :=
  parameterNormalizedConformalDriftBase H (fun p => (Φ p.1 p.2 1).1)
    (conformalReferenceGramFrameOperatorJoint g L)

def conformalReferenceFramedDrift (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (H : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ) :=
  parameterNormalizedConformalDrift H (fun p => (Φ p.1 p.2 1).1)
    (conformalReferenceGramFrameOperatorJoint g L) L

def conformalReferenceWeightedFramedDrift (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (H : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ) :=
  parameterWeightedNormalizedConformalDrift H (fun p => (Φ p.1 p.2 1).1)
    (conformalReferenceGramFrameOperatorJoint g L) w L

def referenceDriftCompactRoom (y0 : R3) (ρ : ℝ) : Set ((ℝ × (R3 × ℝ)) × R3) :=
  (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)) ×ˢ closedBall (0 : R3) 2

def ConformalReferenceFramedDriftData (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ) : Prop :=
  ConformalReferencePositiveCoefficientData g L y0 Φ B ε C ρ H a w ∧
  ContDiff ℝ ∞ (conformalReferenceFramedDriftBase g L Φ H) ∧
  ContDiff ℝ ∞ (conformalReferenceFramedDrift g L Φ H) ∧
  ContDiff ℝ ∞ (conformalReferenceWeightedFramedDrift g L Φ H w) ∧
  (∀ p, a p = w p • (H p)⁻¹) ∧
  (∀ p, conformalReferenceWeightedFramedDrift g L Φ H w p =
    w p • conformalReferenceFramedDrift g L Φ H p) ∧
  (∀ p, 3 ≤ ‖p.2‖ → conformalReferenceWeightedFramedDrift g L Φ H w p = 0) ∧
  (∀ q : ℝ, ∀ y z : R3,
    conformalReferenceFramedDrift g L Φ H ((q,(y,0)),z) = 0 ∧
    conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,0)),z) = 0) ∧
  (∀ q : ℝ, ∀ y z : R3,
    HasDerivAt (fun r : ℝ => conformalReferenceFramedDrift g L Φ H ((q,(y,r)),z))
      (-L • conformalReferenceFramedDriftBase g L Φ H ((q,(y,0)),z)) 0 ∧
    HasDerivAt (fun r : ℝ => conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,r)),z))
      (-L • (w ((q,(y,0)),z) • conformalReferenceFramedDriftBase g L Φ H ((q,(y,0)),z))) 0) ∧
  (∀ q ∈ Icc (0 : ℝ) 1, ∀ y, ‖y-y0‖ ≤ 2*ρ → ∀ z : R3, ‖z‖ ≤ 2 →
    HasDerivAt (fun r : ℝ => conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,r)),z))
      (-L • conformalReferenceFramedDriftBase g L Φ H ((q,(y,0)),z)) 0) ∧
  (∀ q ∈ Icc (0 : ℝ) 1, ∀ y, ‖y-y0‖ ≤ 4*ρ → ∀ r : ℝ, |r| ≤ 4*ρ →
    ∀ z ∈ closedBall (0 : R3) 2,
      referenceFramedNormalOperatorForCoefficients g L Φ ((q,(y,r)),z)
        (conformalReferenceFramedDrift g L Φ H ((q,(y,r)),z)) =
      (-L*r) • ((parameterFramedNormalizedEndpointDerivative (fun p => (Φ p.1 p.2 1).1)
        (conformalReferenceGramFrameOperatorJoint g L) ((q,(y,r)),z)).adjoint
          (gradient conformalReferenceCoordinateDepth
            (parameterFramedScaledEndpoint (fun p => (Φ p.1 p.2 1).1)
              (conformalReferenceGramFrameOperatorJoint g L) ((q,(y,r)),z))))) ∧
  CompactMixedLinearBounds
    (referenceCoefficientRadialReorder (conformalReferenceFramedDrift g L Φ H))
    (referenceCoefficientNonradialRoom y0 ρ) ρ ∧
  CompactMixedLinearBounds
    (referenceCoefficientRadialReorder (conformalReferenceWeightedFramedDrift g L Φ H w))
    (referenceCoefficientNonradialRoom y0 ρ) ρ ∧
  ∀ N : ℕ, ∃ D : ℝ, 0 ≤ D ∧
    (∀ j : ℕ, j ≤ N → ∀ p ∈ referenceDriftCompactRoom y0 ρ,
      ‖iteratedFDeriv ℝ j (conformalReferenceFramedDriftBase g L Φ H) p‖ ≤ D ∧
      ‖iteratedFDeriv ℝ j (conformalReferenceFramedDrift g L Φ H) p‖ ≤ D ∧
      ‖iteratedFDeriv ℝ j (conformalReferenceWeightedFramedDrift g L Φ H w) p‖ ≤ D) ∧
    ∀ p ∈ referenceDriftCompactRoom y0 ρ,
      ‖conformalReferenceFramedDrift g L Φ H p‖ ≤ D*|p.1.2.2| ∧
      ‖conformalReferenceWeightedFramedDrift g L Φ H w p‖ ≤ D*|p.1.2.2|

theorem exists_compact_parameter_conformalReference_framed_drift
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3) :
    ∃ (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
      (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
      (w : (ℝ × (R3 × ℝ)) × R3 → ℝ),
      ConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w := by
  obtain ⟨Φ,B,ε,C,ρ,H,a,w,hOld⟩ :=
    exists_compact_parameter_conformalReference_positive_coefficients g hg L y0
  have hSaved : ConformalReferencePositiveCoefficientData g L y0 Φ B ε C ρ H a w := hOld
  rcases hOld with
    ⟨hNormal,hρ,hρε,hHDef,haDef,hwDef,hH,hPos,ha,hw,hSupport,hLocal,hZeroJet,hUE,hMixed⟩
  rcases hNormal with ⟨hEndpoint,hε,hC,hFrame,hBij,hG,hGeom,hFull⟩
  rcases hEndpoint with ⟨_,_,_,_,_,_,_,hTheta,_,_,_⟩
  let Θ : ℝ × (R3 × R3) → R3 := fun p => (Φ p.1 p.2 1).1
  let F := conformalReferenceGramFrameOperatorJoint g L
  have hb : ContDiff ℝ ∞ (conformalReferenceFramedDriftBase g L Φ H) :=
    contDiff_parameterNormalizedConformalDriftBase H hH hPos Θ hTheta F hFrame
  have hd : ContDiff ℝ ∞ (conformalReferenceFramedDrift g L Φ H) :=
    contDiff_parameterNormalizedConformalDrift H hH hPos Θ hTheta F hFrame L
  have hbeta : ContDiff ℝ ∞ (conformalReferenceWeightedFramedDrift g L Φ H w) :=
    contDiff_parameterWeightedNormalizedConformalDrift H hH hPos Θ hTheta F hFrame w hw L
  have hPrincipal : ∀ p, a p = w p • (H p)⁻¹ := by
    intro p
    rw [haDef,hwDef]
    simp only [cutoffPrincipalCoefficient,cutoffVolumeDensity,matrixPrincipalCoefficient,smul_smul]
  have hBetaSupport : ∀ p, 3 ≤ ‖p.2‖ → conformalReferenceWeightedFramedDrift g L Φ H w p = 0 := by
    intro p hp
    change w p • conformalReferenceFramedDrift g L Φ H p = 0
    rw [(hSupport p.1 p.2 hp).2,zero_smul]
  have hZero : ∀ q : ℝ, ∀ y z : R3,
      conformalReferenceFramedDrift g L Φ H ((q,(y,0)),z) = 0 ∧
      conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,0)),z) = 0 :=
    fun q y z => parameterNormalizedConformalDrift_zero H Θ F w L q y z
  have hJets : ∀ q : ℝ, ∀ y z : R3,
      HasDerivAt (fun r : ℝ => conformalReferenceFramedDrift g L Φ H ((q,(y,r)),z))
        (-L • conformalReferenceFramedDriftBase g L Φ H ((q,(y,0)),z)) 0 ∧
      HasDerivAt (fun r : ℝ => conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,r)),z))
        (-L • (w ((q,(y,0)),z) • conformalReferenceFramedDriftBase g L Φ H ((q,(y,0)),z))) 0 :=
    fun q y z => hasDerivAt_parameterNormalizedConformalDrift_zero
      H hH hPos Θ hTheta F hFrame w hw L q y z
  have hJetsNormalized : ∀ q ∈ Icc (0 : ℝ) 1, ∀ y, ‖y-y0‖ ≤ 2*ρ → ∀ z : R3, ‖z‖ ≤ 2 →
      HasDerivAt (fun r : ℝ => conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,r)),z))
        (-L • conformalReferenceFramedDriftBase g L Φ H ((q,(y,0)),z)) 0 := by
    intro q hq y hy z hz
    have hj := (hJets q y z).2
    rw [(hZeroJet q hq y hy z hz).2.2.1,one_smul] at hj
    exact hj
  have hMetric : ∀ q ∈ Icc (0 : ℝ) 1, ∀ y, ‖y-y0‖ ≤ 4*ρ → ∀ r : ℝ, |r| ≤ 4*ρ →
      ∀ z ∈ closedBall (0 : R3) 2,
        referenceFramedNormalOperatorForCoefficients g L Φ ((q,(y,r)),z)
          (conformalReferenceFramedDrift g L Φ H ((q,(y,r)),z)) =
        (-L*r) • ((parameterFramedNormalizedEndpointDerivative Θ F ((q,(y,r)),z)).adjoint
          (gradient conformalReferenceCoordinateDepth (parameterFramedScaledEndpoint Θ F ((q,(y,r)),z)))) := by
    intro q hq y hy r hr z hz
    exact parameterNormalizedConformalDrift_local_metric_identity H hPos Θ
      (conformalReferenceOperatorJoint g L) F L ((q,(y,r)),z) (hLocal q hq y hy r hr z hz).1
  have hQ : IsCompact (referenceCoefficientNonradialRoom y0 ρ) :=
    isCompact_Icc.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hMixedD : CompactMixedLinearBounds
      (referenceCoefficientRadialReorder (conformalReferenceFramedDrift g L Φ H))
      (referenceCoefficientNonradialRoom y0 ρ) ρ :=
    compactMixedLinearBounds_of_zero_slice _ (contDiff_referenceCoefficientRadialReorder _ hd)
      _ hQ (fun p => (hZero p.1 p.2.1 p.2.2).1) ρ hρ.le
  have hMixedBeta : CompactMixedLinearBounds
      (referenceCoefficientRadialReorder (conformalReferenceWeightedFramedDrift g L Φ H w))
      (referenceCoefficientNonradialRoom y0 ρ) ρ :=
    compactMixedLinearBounds_of_zero_slice _ (contDiff_referenceCoefficientRadialReorder _ hbeta)
      _ hQ (fun p => (hZero p.1 p.2.1 p.2.2).2) ρ hρ.le
  have hS : IsCompact (referenceDriftCompactRoom y0 ρ) :=
    (isCompact_Icc.prod ((isCompact_closedBall _ _).prod isCompact_Icc)).prod
      (isCompact_closedBall _ _)
  have hBounds := exists_compact_parameterNormalizedConformalDrift_bounds H hH hPos
    Θ hTheta F hFrame w hw L (referenceDriftCompactRoom y0 ρ) hS
  refine ⟨Φ,B,ε,C,ρ,H,a,w,hSaved,hb,hd,hbeta,hPrincipal,?_,hBetaSupport,hZero,
    hJets,hJetsNormalized,hMetric,hMixedD,hMixedBeta,hBounds⟩
  intro p
  rfl

end OAI.AnisotropicCalderon.ConnectionError
