import Calderon.ActualFiniteHarmonicModelReferenceZeroAngular
import Calderon.ActualFiniteHarmonicCoreDerivative

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SmoothMetricFrame
  AmbientReferenceRaising ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev referenceAdjointZeroRawFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] referenceAdjointZeroRawFunction

lemma coreWeight_two_eq_one_mul_degree_add_one :
    coreWeightOperator hO hD (besselWeight 2) =
      coreWeightOperator hO hD (besselWeight 1)*(coreDegree hO hD+1) := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  simp only [Module.End.mul_apply,LinearMap.add_apply,Module.End.one_apply,
    map_add,Submodule.coe_add,Pi.add_apply]
  rw [coreWeight_one_degree_apply hO hD F x]
  abel

lemma nativeReferenceAdjointZeroCoefficient_eq_raw
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) :
    nativeReferenceAdjointZeroCoefficient hO hD hF g hg L lam δ R p hδ hR =
      ∑ a : Fin 3, coreDerivative hO hD hF a *
        (-nativeReferenceConnectionAction hO hD g hg L lam a +
          nativeReferenceProfileScalar hO hD g hg L lam δ R p hδ hR a*(coreDegree hO hD-1)) := by
  unfold nativeReferenceAdjointZeroCoefficient
  apply Finset.sum_congr rfl
  intro a _
  have hP : Commute (coreWeightOperator hO hD (besselWeight 1))
      (nativeReferenceProfileScalar hO hD g hg L lam δ R p hδ hR a) := by
    exact scalarCentral_coreWeightOperator hO hD _ _ _
  rw [coreWeight_two_eq_one_mul_degree_add_one hO hD]
  rw [_root_.neg_one_smul ℝ (coreWeightOperator hO hD (besselWeight 1)*
    nativeReferenceConnectionAction hO hD g hg L lam a),
    two_smul ℝ (coreWeightOperator hO hD (besselWeight 1))]
  unfold coreDerivative
  have halg {R : Type} [Ring R] (d w a p n : R) (hp : Commute w p) :
      d*(-(w*a)+p*(w*(n+1)-(w+w))) = d*w*(-a+p*(n-1)) := by
    have he : p*(w*(n+1)-(w+w)) = (p*w)*(n-1) := by noncomm_ring
    rw [he,← hp.eq]
    noncomm_ring
  exact halg (coreNormalizedDerivative hO hD hF a)
    (coreWeightOperator hO hD (besselWeight 1))
    (nativeReferenceConnectionAction hO hD g hg L lam a)
    (nativeReferenceProfileScalar hO hD g hg L lam δ R p hδ hR a)
    (coreDegree hO hD) hP

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
