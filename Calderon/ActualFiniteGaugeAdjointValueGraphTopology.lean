import Calderon.ActualFiniteGaugeAdjointRadialFamily
import Calderon.NativeRepackedCoefficientMultiplierTopology

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
FINITE-GAUGE-ADJOINT-VALUE-GRAPH-TOPOLOGY-EXPANSION-v001.md. Derive SAME moving coefficient norm topology. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric
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

variable {K : Set (ℝ × (R3 × ℝ))}


attribute [local irreducible] referenceFiniteHarmonicProductHighRadialFamily
  referenceGaugeTangentSecondFiniteHighFamily referenceGaugeTangentDefectFiniteHighFamily
  referenceGaugeTangentSecondDivergenceThreeHalfMultiplierFamily nativeThreeHalfCoefficientMulL
  sphereSobolevPartialSumL referenceStrongDriftFamily

lemma contDiff_referenceGaugeTangentDefectFiniteHighFamily_of_commonSupport
    (G : ReferenceGaugeNormalReciprocalRoom g L Φ a K) (n : ℕ)
    (m : (ℝ × (R3 × ℝ)) × R3 → ℝ) (hm : ContDiff ℝ ∞ m)
    (K1 : Set R3) (hK1 : IsCompact K1) (hz : ∀ p x, x ∉ K1 → m (p,x)=0)
    (Q : (ℝ × (R3 × ℝ)) → SmoothCoefficientJets 3)
    (hQ : ∀ p, coefficientValue 3 (Q p) = fun x => m (p,x)) :
    ContDiff ℝ ∞ (fun p => referenceGaugeTangentDefectFiniteHighFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n (Q p) p) := by
  let h : (ℝ × (R3 × ℝ)) × R3 → ℝ := fun p => G.scalar p * m p
  have hh : ContDiff ℝ ∞ h := G.smooth.mul hm
  have hhZ : ∀ p x, x ∉ G.spatialSupport → h (p,x)=0 := by
    intro p x hx
    change G.scalar (p,x)*m (p,x)=0
    rw [G.zeroOutside p x hx,zero_mul]
  let F : (ℝ × (R3 × ℝ)) → SmoothCoefficientJets 3 := fun p => G.productJets 3 (Q p) p
  have hFValue : ∀ p, coefficientValue 3 (F p) = fun x => h (p,x) := by
    intro p
    funext x
    exact (G.coefficientValue_productJets 3 (Q p) p x).trans
      (congrArg (fun t : ℝ => G.scalar (p,x)*t) (congrFun (hQ p) x))
  have hT := contDiff_referenceGaugeTangentSecondFiniteHighFamily_of_value_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n
      h hh G.spatialSupport G.supportCompact hhZ F hFValue
  have hM : ContDiff ℝ ∞ (fun p => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (F p)) := by
    have hEq (p : ℝ × (R3 × ℝ)) : F p =
        commonSupportCoefficientFamily 3 h hh G.spatialSupport G.supportCompact hhZ p := by
      apply smoothCoefficientJets_eq_of_coefficientValue_eq 3
      funext x
      exact (congrFun (hFValue p) x).trans
        (coefficientValue_commonSupportCoefficientFamily 3 h hh G.spatialSupport G.supportCompact hhZ p x).symm
    have hSmooth := contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
      h hh G.spatialSupport G.supportCompact hhZ
    have hFamily : (fun p => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (F p)) =
        fun p => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
          (commonSupportCoefficientFamily 3 h hh G.spatialSupport G.supportCompact hhZ p) :=
      funext (fun p => congrArg (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0) (hEq p))
    exact hFamily.symm ▸ hSmooth
  have hDiv := contDiff_referenceGaugeTangentSecondDivergenceThreeHalfMultiplierFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  unfold referenceGaugeTangentDefectFiniteHighFamily
  exact (hT.add hT).add (hDiv.clm_comp (hM.clm_comp contDiff_const))

lemma contDiffAt_referenceFiniteGaugeAdjointRadialFamily_of_value_graph
    (G : ReferenceGaugeNormalReciprocalRoom g L Φ a K) (n : ℕ)
    (m : (ℝ × (R3 × ℝ)) × R3 → ℝ) (hm : ContDiff ℝ ∞ m)
    (K1 : Set R3) (hK1 : IsCompact K1) (hz : ∀ p x, x ∉ K1 → m (p,x)=0)
    (Q : (ℝ × (R3 × ℝ)) → SmoothCoefficientJets 3)
    (hQ : ∀ p, coefficientValue 3 (Q p) = fun x => m (p,x)) (p : ℝ × (R3 × ℝ))
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2).IsInvertible) :
    ContDiffAt ℝ ∞ (fun z => referenceFiniteGaugeAdjointRadialFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n (Q z) z) p := by
  let h : (ℝ × (R3 × ℝ)) × R3 → ℝ := fun p => G.scalar p * m p
  have hh : ContDiff ℝ ∞ h := G.smooth.mul hm
  have hhZ : ∀ p x, x ∉ G.spatialSupport → h (p,x)=0 := by
    intro p x hx
    change G.scalar (p,x)*m (p,x)=0
    rw [G.zeroOutside p x hx,zero_mul]
  let F : (ℝ × (R3 × ℝ)) → SmoothCoefficientJets 3 := fun p => G.productJets 3 (Q p) p
  have hFValue : ∀ p, coefficientValue 3 (F p) = fun x => h (p,x) := by
    intro p
    funext x
    exact (G.coefficientValue_productJets 3 (Q p) p x).trans
      (congrArg (fun t : ℝ => G.scalar (p,x)*t) (congrFun (hQ p) x))
  have hC := contDiffAt_referenceFiniteHarmonicProductHighRadialFamily_of_value_graph
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n
      h hh G.spatialSupport G.supportCompact hhZ F hFValue p hi
  have hU := (contDiff_referenceGaugeTangentDefectFiniteHighFamily_of_commonSupport
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n m hm K1 hK1 hz Q hQ).contDiffAt (x := p)
  have hP : ContDiff ℝ ∞ (fun z => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 3 z)) := by
    unfold referenceGaugeNormalCoefficientJetsFamily
    exact contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
      (referenceGaugeNormalCoefficient g L Φ a)
      (contDiff_referenceGaugeNormalCoefficient g L Φ y0 B ε C ρ H a w hData hg)
      (Metric.closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (referenceGaugeNormalCoefficient_support g L Φ y0 B ε C ρ H a w hData)
  unfold referenceFiniteGaugeAdjointRadialFamily
  exact ((hP.contDiffAt (x := p)).clm_comp hC).add ((contDiffAt_snd.snd.pow 2).smul hU)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceGaugeTangentDefectFiniteHighFamily_of_commonSupport
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceFiniteGaugeAdjointRadialFamily_of_value_graph
