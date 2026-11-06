import Calderon.ActualFiniteHarmonicModelBZSecondAngular
import Calderon.ActualFiniteHarmonicModelPrincipalZWordScalarAction

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  ActualModelCommutatorWords PrincipalCommutator AmbientReferenceRaising
  ConformalDepth SmoothMetricFrame MovingFrameConnection CoordinateBootstrapJets ReferenceDensityBounds
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev bzScalarFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] bzScalarFunction

lemma nativeB_coreScalar_apply
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) (c : R3 → ℝ) (hc : ContDiff ℝ ∞ c)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR (coreScalar hO hD c hc F) x =
      c x • nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F x := by
  have hW : coreWeightOperator hO hD (besselWeight 1) (coreScalar hO hD c hc F) x =
      c x • coreWeightOperator hO hD (besselWeight 1) F x :=
    congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x)
      (scalarCentral_coreWeightOperator hO hD (besselWeight 1) c hc).eq
  rw [nativeB_firstNormalizedCoefficient_apply,nativeB_firstNormalizedCoefficient_apply,hW,map_smul]

lemma nativeB_nativeZ_scalar_angular_action
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    (nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR *
      nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR) F x =
      ∑ a : Fin 3, referenceFrameDerivative g1 L lam a
        (fun y => Real.log (referenceRadius δ R p L y)) x •
        nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR
          (coreDerivative hO hD hF a F) x := by
  have hZ : nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR =
      coreDefectAction hO hD hF g1 hg1 L lam δ R p hδ hR := by
    apply LinearMap.ext
    intro G
    apply Subtype.ext
    exact nativeZField_eq_coreAction hO hD hF g1 hg1 L lam δ R p hδ hR G
  rw [hZ]
  simp only [coreDefectAction,Module.End.mul_apply,LinearMap.sum_apply,map_sum,
    Submodule.coe_sum,Finset.sum_apply,nativeB_coreScalar_apply]

lemma nativeB_coefficientDerivative_nativeZ_scalar_angular_action
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j k : Fin 3) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    (nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR *
      coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection k))
        (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR)) F x =
      ∑ a : Fin 3, directionalFDeriv (coordinateDirection k)
        (referenceFrameDerivative g1 L lam a
          (fun y => Real.log (referenceRadius δ R p L y))) x •
        nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR
          (coreDerivative hO hD hF a F) x := by
  let c (a : Fin 3) : R3 → ℝ := directionalFDeriv (coordinateDirection k)
    (referenceFrameDerivative g1 L lam a (fun y => Real.log (referenceRadius δ R p L y)))
  have hc (a : Fin 3) : ContDiff ℝ ∞ (c a) :=
    contDiff_directionalFDeriv (coordinateDirection k) _
      (contDiff_referenceFrameDerivative g1 hg1 L lam a _
        (contDiff_log_referenceRadius_profile δ R L p hδ hR))
  have hZ : coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection k))
      (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR) =
      ∑ a : Fin 3, coreScalar hO hD (c a) (hc a) * coreDerivative hO hD hF a := by
    apply LinearMap.ext
    intro G
    apply Subtype.ext
    funext y
    rw [coefficientDerivative_nativeZ_firstNormalized_apply]
    have hs := nativeReferenceDefectFirstNormalizedCoefficient_word_sum hO hD hF
      g1 hg1 L lam δ R p hδ hR [k] y
    change directionalFDeriv (coordinateDirection k)
      (nativeReferenceDefectFirstNormalizedCoefficient hO hD hF g1 L lam δ R p) y =
        ∑ a : Fin 3, c a y • BoundedAngularShift.normalizedDerivative hF hO hD a at hs
    rw [hs]
    simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
      LinearMap.sum_apply,Module.End.mul_apply,Submodule.coe_sum,Finset.sum_apply,
      coreScalar,coreDerivative,coreNormalizedDerivative,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk]
  rw [hZ]
  simp only [Module.End.mul_apply,LinearMap.sum_apply,map_sum,
    Submodule.coe_sum,Finset.sum_apply,nativeB_coreScalar_apply,c]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
