import Calderon.NativeFiniteHarmonicProductHighTangentialGraph
import Calderon.ActualReferenceGaugeTangentOperator
import Calderon.NativeRepackedCoefficientMultiplierTopology

/-! High graph of the finite gauge tangent operator, for the original tangent field. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)

attribute [local irreducible] referenceGaugeTangentSecondRemainderJetsFamily
  referenceGaugeTangentSecondEndpointFamily nativeFiniteHarmonicProductHighTangentialL
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL
  sphereThreeHalfTangentialDerivativeL sphereTangentialDerivativeL sphereSobolevInclusionL

def referenceGaugeTangentSecondFiniteHighFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (n : ℕ) (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  ∑ j : Fin 3, (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceGaugeTangentSecondRemainderJetsFamily g L Φ a y0 B ε C ρ H w hData hg 3 j p)).comp
      (nativeFiniteHarmonicProductHighTangentialL hcalc hF hO hD τ0 n Q j)

lemma referenceGaugeTangentSecondFiniteHighFamily_lower_graph
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (n : ℕ) (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ)) (f : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (referenceGaugeTangentSecondFiniteHighFamily g L y0 Φ B ε C ρ H a w hData hg
          hcalc hF hO hD τ0 n Q p f)) =
      referenceGaugeTangentSecondEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
        (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (coefficientRepackedJets 3 2 Q)
          (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
            (sphereSobolevPartialSum (3/2 : ℝ) n f))) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let u := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q (sphereSobolevPartialSum (3/2 : ℝ) n f)
  let F (k : ℕ) (j : Fin 3) := referenceGaugeTangentSecondRemainderJetsFamily
    g L Φ a y0 B ε C ρ H w hData hg k j p
  have hQ := congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
    A (sphereSobolevPartialSum (3/2 : ℝ) n f))
    (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 Q
      (coefficientRepackedJets 3 2 Q) (coefficientValue_repackedJets 3 2 Q).symm)
  have hTerm (j : Fin 3) :
      J (I (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (F 3 j)
        (nativeFiniteHarmonicProductHighTangentialL hcalc hF hO hD τ0 n Q j f))) =
      nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (F 2 j)
        (sphereTangentialDerivativeL hF hO hD j
          (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (coefficientRepackedJets 3 2 Q)
            (I (sphereSobolevPartialSum (3/2 : ℝ) n f)))) := by
    let v := nativeFiniteHarmonicProductHighTangentialL hcalc hF hO hD τ0 n Q j f
    have hCoeffValue : coefficientValue 3 (F 3 j) = coefficientValue 2 (F 2 j) := by
      funext x
      exact (coefficientValue_referenceGaugeTangentSecondRemainderJetsFamily
        g L Φ a y0 B ε C ρ H w hData hg 3 j p x).trans
        (coefficientValue_referenceGaugeTangentSecondRemainderJetsFamily
          g L Φ a y0 B ε C ρ H w hData hg 2 j p x).symm
    have hFirst := congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => A v)
      (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 (F 3 j) (F 2 j) hCoeffValue)
    have hSecond := congrArg (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A (I v))
      (nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0 (F 2 j))
    have hDerivative := congrArg J
      (sphereSobolevInclusionL_nativeFiniteHarmonicProductHighTangentialL hcalc hF hO hD τ0 n Q j f)
    have hCompatible := congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A u)
      (sphereTangentialDerivativeL_threehalf_half_compatibility hF hO hD j)
    have hInput := congrArg (sphereTangentialDerivativeL hF hO hD j) hQ
    exact (congrArg J hFirst).trans (hSecond.trans
      (congrArg (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (F 2 j))
        (hDerivative.trans (hCompatible.trans hInput))))
  simp only [referenceGaugeTangentSecondFiniteHighFamily,referenceGaugeTangentSecondEndpointFamily,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,map_sum]
  exact Finset.sum_congr rfl (fun j _ => hTerm j)

lemma contDiff_referenceGaugeTangentSecondFiniteHighFamily_of_value_graph
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (n : ℕ)
    (m : (ℝ × (R3 × ℝ)) × R3 → ℝ) (hm : ContDiff ℝ ∞ m)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p x, x ∉ K → m (p,x)=0)
    (Q : (ℝ × (R3 × ℝ)) → SmoothCoefficientJets 3)
    (hQ : ∀ p, coefficientValue 3 (Q p) = fun x => m (p,x)) :
    ContDiff ℝ ∞ (fun p => referenceGaugeTangentSecondFiniteHighFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n (Q p) p) := by
  apply ContDiff.sum
  intro j hj
  unfold referenceGaugeTangentSecondRemainderJetsFamily
  exact (contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
    (referenceGaugeTangentSecondRemainder g L Φ a j)
    (contDiff_referenceGaugeTangentSecondRemainder g L Φ a y0 B ε C ρ H w hData hg j)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceGaugeTangentSecondRemainder_support g L Φ a y0 B ε C ρ H w hData j)).clm_comp
      (contDiff_nativeFiniteHarmonicProductHighTangentialL_of_value_graph
        hcalc hF hO hD τ0 n j m hm K hK hz Q hQ)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecondFiniteHighFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecondFiniteHighFamily_lower_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceGaugeTangentSecondFiniteHighFamily_of_value_graph
