import Calderon.ActualFiniteHarmonicModelUZSecondBaseOperator
import Calderon.ActualFiniteHarmonicModelPrincipalZFirstAngular

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords
  SpectralWeightedGraph ReferenceDensityBounds
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeUZSecondBaseActionFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeUZSecondBaseActionFunction

lemma nativeUZSecondBaseTerm_angular_action
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (L lam δ R : ℝ) (p : ℕ)
    (i j : Fin 3) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i j *
      nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR *
      coreDirectionalDerivative hO hD (coordinateDirection i) *
      coreDirectionalDerivative hO hD (coordinateDirection j)) F x =
      nativePrincipalZFirstAngularCoefficient hO hD hF g1 g2 hg1
        L lam δ R p i j x
          (coreWeightOperator hO hD (besselWeight 1)
            (coreDirectionalDerivative hO hD (coordinateDirection i)
              (coreDirectionalDerivative hO hD (coordinateDirection j) F)) x) := by
  change (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i j *
    nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR)
      (coreDirectionalDerivative hO hD (coordinateDirection i)
        (coreDirectionalDerivative hO hD (coordinateDirection j) F)) x = _
  exact nativePrincipalCoefficient_nativeZ_firstAngular_apply
    hO hD hF g1 g2 hg1 L lam δ R p i j hg2 hδ hR
      (coreDirectionalDerivative hO hD (coordinateDirection i)
        (coreDirectionalDerivative hO hD (coordinateDirection j) F)) x

lemma nativeUZSecondBaseOperator_angular_action
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    nativeUZSecondBaseOperator hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x =
      ∑ i : Fin 3, ∑ j : Fin 3,
        nativePrincipalZFirstAngularCoefficient hO hD hF g1 g2 hg1
          L lam δ R p i j x
            (coreWeightOperator hO hD (besselWeight 1)
              (coreDirectionalDerivative hO hD (coordinateDirection i)
                (coreDirectionalDerivative hO hD (coordinateDirection j) F)) x) := by
  unfold nativeUZSecondBaseOperator
  simp only [secondBaseRightProduct,LinearMap.sum_apply,Submodule.coe_sum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact nativeUZSecondBaseTerm_angular_action hO hD hF g1 g2 hg1
    L lam δ R p i j hg2 hδ hR F x

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
