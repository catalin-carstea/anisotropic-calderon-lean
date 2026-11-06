import Calderon.ActualFiniteGaugeTangentHighGraph
import Calderon.ActualReferenceGaugeTangentDivergenceEndpoints
import Calderon.ActualReferenceGaugeReciprocalProductJets
import Calderon.SphereSobolevPartialSumOperator

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
FINITE-ADJOINT-PRODUCT-ASSEMBLY-EXPANSION-v001.md. Higher representative of the exact tangent defect. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceGaugeTangentSecondFiniteHighFamily
  referenceGaugeTangentSecondEndpointFamily referenceGaugeTangentSecondDivergenceThreeHalfMultiplierFamily
  referenceGaugeTangentSecondDivergenceHalfMultiplierFamily referenceGaugeTangentSecondDivergenceNegativeMultiplierFamily
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL sphereSobolevInclusionL
  sphereSobolevPartialSumL sphereLowerDistributionalTranspose

variable {K : Set (ℝ × (R3 × ℝ))}

def referenceGaugeTangentDefectFiniteHighFamily
    (G : ReferenceGaugeNormalReciprocalRoom g L Φ a K) (n : ℕ)
    (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  referenceGaugeTangentSecondFiniteHighFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    n (G.productJets 3 Q p) p +
  referenceGaugeTangentSecondFiniteHighFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    n (G.productJets 3 Q p) p +
  (referenceGaugeTangentSecondDivergenceThreeHalfMultiplierFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).comp
      ((nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (G.productJets 3 Q p)).comp
        (sphereSobolevPartialSumL (3/2 : ℝ) n))

lemma referenceGaugeTangentDefectFiniteHighFamily_lower_graph
    (G : ReferenceGaugeNormalReciprocalRoom g L Φ a K) (n : ℕ)
    (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ)) (f : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (referenceGaugeTangentDefectFiniteHighFamily
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n Q p f)) =
    (referenceGaugeTangentSecondEndpointFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p -
      sphereLowerDistributionalTranspose (referenceGaugeTangentSecondEndpointFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p))
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (G.productJets 3 Q p)
          (sphereSobolevPartialSum (3/2 : ℝ) n f))) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let H3 := G.productJets 3 Q p
  let v := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 H3 (sphereSobolevPartialSum (3/2 : ℝ) n f)
  let T := referenceGaugeTangentSecondEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let U := referenceGaugeTangentSecondFiniteHighFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n H3 p f
  let D3 := referenceGaugeTangentSecondDivergenceThreeHalfMultiplierFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let D1 := referenceGaugeTangentSecondDivergenceHalfMultiplierFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let Dn := referenceGaugeTangentSecondDivergenceNegativeMultiplierFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  have hInput : I v = nativeHalfCoefficientMulL hcalc hF hO hD τ0
      (coefficientRepackedJets 3 2 H3) (I (sphereSobolevPartialSum (3/2 : ℝ) n f)) :=
    congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
      A (sphereSobolevPartialSum (3/2 : ℝ) n f))
      (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 H3
        (coefficientRepackedJets 3 2 H3) (coefficientValue_repackedJets 3 2 H3).symm)
  have hT : J (I U) = T (I v) :=
    (referenceGaugeTangentSecondFiniteHighFamily_lower_graph
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n H3 p f).trans
        (congrArg T hInput.symm)
  have hDivGraph : J (I (D3 v)) = Dn (J (I v)) :=
    (congrArg J (congrArg
      (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => A v)
      (referenceGaugeTangentSecondDivergence_high_half_compatibility
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p))).trans
      (congrArg (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A (I v))
        (referenceGaugeTangentSecondDivergence_half_negative_compatibility
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p))
  have hPoint : referenceGaugeTangentDefectFiniteHighFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n Q p f = U+U+D3 v := by
    simp only [referenceGaugeTangentDefectFiniteHighFamily,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply,sphereSobolevPartialSumL_apply,U,D3,v,H3]
  have hLinear : J (I (U+U+D3 v)) = J (I U)+J (I U)+J (I (D3 v)) := by
    simp only [map_add]
  have hTransport : J (I U)+J (I U)+J (I (D3 v)) = T (I v)+T (I v)+Dn (J (I v)) :=
    congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x+z)
      (congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x+z) hT hT) hDivGraph
  have hActual : T (I v)+T (I v)+Dn (J (I v)) =
      (T-sphereLowerDistributionalTranspose T) (I v) := by
    have h := congrArg
      (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A (I v))
      (referenceGaugeTangentSecond_sub_transpose_eq_firstOrder_add_zeroOrder
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p)
    simpa only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,two_smul,two_nsmul] using h.symm
  exact (congrArg (fun z : SphereSobolev (3/2 : ℝ) => J (I z)) hPoint).trans
    (hLinear.trans (hTransport.trans hActual))

lemma contDiff_referenceGaugeTangentDefectFiniteHighFamily
    (G : ReferenceGaugeNormalReciprocalRoom g L Φ a K) (n : ℕ) (Q : SmoothCoefficientJets 3) :
    ContDiff ℝ ∞ (referenceGaugeTangentDefectFiniteHighFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n Q) := by
  have hT := contDiff_referenceGaugeTangentSecondFiniteHighFamily_of_value_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n
      (G.productScalar Q) (G.contDiff_productScalar Q) G.spatialSupport G.supportCompact
      (G.productScalar_zeroOutside Q) (G.productJets 3 Q) (by
        intro p
        funext x
        exact G.coefficientValue_productJets 3 Q p x)
  have hM : ContDiff ℝ ∞ (fun p => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (G.productJets 3 Q p)) :=
    contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
      (G.productScalar Q) (G.contDiff_productScalar Q) G.spatialSupport G.supportCompact
      (G.productScalar_zeroOutside Q)
  have hDivSmooth := contDiff_referenceGaugeTangentSecondDivergenceThreeHalfMultiplierFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  unfold referenceGaugeTangentDefectFiniteHighFamily
  exact (hT.add hT).add (hDivSmooth.clm_comp (hM.clm_comp contDiff_const))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentDefectFiniteHighFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentDefectFiniteHighFamily_lower_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceGaugeTangentDefectFiniteHighFamily
