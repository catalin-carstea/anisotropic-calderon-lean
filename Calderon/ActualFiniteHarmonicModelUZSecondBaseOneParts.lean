import Calderon.ActualFiniteHarmonicModelUZSecondBaseAdjointRegularity
import Calderon.ActualOperatorValuedBaseAdjointSmooth

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords
  SpectralWeightedGraph ReferenceDensityBounds ActualOperatorValuedBaseAdjoint
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeSecondOnePartsFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeSecondOnePartsFunction
attribute [local irreducible] nativePrincipalZFirstAngularCoefficient
  nativePrincipalCoefficient nativeZ

theorem nativeUZSecondBaseTerm_one_parts
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (i j : Fin 3) (mu : R3 → ℝ) (hm : ContDiff ℝ ∞ mu)
    (F G : smoothCompactFiniteSphereCore hO hD) :
    (∫ x : R3, mu x * ⟪
      (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i j *
        nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR *
        coreDirectionalDerivative hO hD (coordinateDirection i) *
        coreDirectionalDerivative hO hD (coordinateDirection j)) F x, G x⟫_ℝ) =
      -(∫ x : R3, ⟪baseDirectionalDeriv (coordinateDirection i)
        (fun y => mu y • (ContinuousLinearMap.adjoint
          (nativePrincipalZFirstAngularCoefficient hO hD hF g1 g2 hg1
            L lam δ R p i j y)) (G y)) x,
        baseDirectionalDeriv (coordinateDirection j)
          (coreWeightOperator hO hD (besselWeight 1) F : R3 → SphereL2) x⟫_ℝ) := by
  have hparts := compact_operator_second_one_parts_adjoint
    (coordinateDirection i) (coordinateDirection j) mu
    (nativePrincipalZFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p i j)
    (coreWeightOperator hO hD (besselWeight 1) F : R3 → SphereL2)
    (G : R3 → SphereL2) hm
    (contDiff_nativePrincipalZFirstAngularCoefficient hO hD hF g1 g2 hg1 hg2
      L lam δ R p hδ hR i j)
    (coreWeightOperator hO hD (besselWeight 1) F).property.1 G.property.1
    (coreWeightOperator hO hD (besselWeight 1) F).property.2.1
  rw [← hparts]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [nativeUZSecondBaseTerm_angular_action hO hD hF g1 g2 hg1
    L lam δ R p i j hg2 hδ hR F x,
    coreWeightOperator_secondDerivative_apply]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
