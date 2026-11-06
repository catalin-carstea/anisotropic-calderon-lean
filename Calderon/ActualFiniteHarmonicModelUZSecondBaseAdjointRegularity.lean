import Calderon.ActualFiniteHarmonicModelUZSecondBaseAction
import Calderon.ActualOperatorValuedBaseAdjoint

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords
  SpectralWeightedGraph ActualScalarPrincipalAdjoint ActualNormalizedSecondModelErrorAssembly
  NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth ReferenceDensityBounds
  ActualOperatorValuedBaseAdjoint
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeSecondAdjointRegularityFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeSecondAdjointRegularityFunction

lemma contDiff_nativePrincipalZFirstAngularCoefficient
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (i j : Fin 3) :
    ContDiff ℝ ∞ (nativePrincipalZFirstAngularCoefficient hO hD hF g1 g2 hg1
      L lam δ R p i j) := by
  unfold nativePrincipalZFirstAngularCoefficient
  exact (ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g1 hg1
    L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam) hδ hR
    (fun a b => contDiff_referenceNormalizedPrincipalDifference_entry
      g1 g2 hg1 hg2 L lam a b) i j).smul
    (contDiff_nativeReferenceDefectFirstNormalizedCoefficient hO hD hF g1 hg1
      L lam δ R p hδ hR)

lemma coreWeightOperator_secondDerivative_apply
    (w : ℕ → ℝ) (i j : R3) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coreWeightOperator hO hD w
      (coreDirectionalDerivative hO hD i (coreDirectionalDerivative hO hD j F)) x =
      baseDirectionalDeriv i (baseDirectionalDeriv j
        (coreWeightOperator hO hD w F : R3 → SphereL2)) x := by
  have hi := congrArg
    (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) =>
      T (coreDirectionalDerivative hO hD j F))
    (coreWeightOperator_directionalDerivative_commute hO hD w i).eq
  have hj := congrArg
    (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F)
    (coreWeightOperator_directionalDerivative_commute hO hD w j).eq
  change coreWeightOperator hO hD w
      (coreDirectionalDerivative hO hD i (coreDirectionalDerivative hO hD j F)) =
    coreDirectionalDerivative hO hD i
      (coreWeightOperator hO hD w (coreDirectionalDerivative hO hD j F)) at hi
  change coreWeightOperator hO hD w (coreDirectionalDerivative hO hD j F) =
    coreDirectionalDerivative hO hD j (coreWeightOperator hO hD w F) at hj
  rw [hj] at hi
  exact congrArg (fun G : smoothCompactFiniteSphereCore hO hD => G x) hi

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
