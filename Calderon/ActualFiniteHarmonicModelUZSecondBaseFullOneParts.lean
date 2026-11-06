import Calderon.ActualFiniteHarmonicModelUZSecondBaseOneParts

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords
  SpectralWeightedGraph ReferenceDensityBounds ActualOperatorValuedBaseAdjoint
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeSecondFullOnePartsFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeSecondFullOnePartsFunction
attribute [local irreducible] nativePrincipalZFirstAngularCoefficient
  nativePrincipalCoefficient nativeZ

theorem nativeUZSecondBaseOperator_one_parts
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (mu : R3 → ℝ) (hm : ContDiff ℝ ∞ mu)
    (F G : smoothCompactFiniteSphereCore hO hD) :
    (∫ x : R3, mu x * ⟪
      nativeUZSecondBaseOperator hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x,
      G x⟫_ℝ) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        -(∫ x : R3, ⟪baseDirectionalDeriv (coordinateDirection i)
          (fun y => mu y • (ContinuousLinearMap.adjoint
            (nativePrincipalZFirstAngularCoefficient hO hD hF g1 g2 hg1
              L lam δ R p i j y)) (G y)) x,
          baseDirectionalDeriv (coordinateDirection j)
            (coreWeightOperator hO hD (besselWeight 1) F : R3 → SphereL2) x⟫_ℝ) := by
  let T (i j : Fin 3) : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
    nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i j *
      nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR *
      coreDirectionalDerivative hO hD (coordinateDirection i) *
      coreDirectionalDerivative hO hD (coordinateDirection j)
  have hInt (i j : Fin 3) : Integrable (fun x : R3 => mu x * ⟪T i j F x,G x⟫_ℝ) := by
    have ht := compact_inner_integrable (fun x : R3 => mu x • T i j F x)
      (G : R3 → SphereL2) (hm.smul (T i j F).property.1).continuous
      G.property.1.continuous G.property.2.1
    simpa only [real_inner_smul_left] using ht
  have hsum (x : R3) :
      nativeUZSecondBaseOperator hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x =
        ∑ i : Fin 3, ∑ j : Fin 3, T i j F x := by
    simp only [nativeUZSecondBaseOperator,secondBaseRightProduct,
      LinearMap.sum_apply,Submodule.coe_sum,Finset.sum_apply,T]
  calc
    _ = ∫ x : R3, ∑ i : Fin 3, ∑ j : Fin 3, mu x * ⟪T i j F x,G x⟫_ℝ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [hsum, sum_inner, Finset.mul_sum]
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : R3, mu x * ⟪T i j F x,G x⟫_ℝ := by
      rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hInt i j))]
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_finset_sum _ (fun j _ => hInt i j)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact nativeUZSecondBaseTerm_one_parts hO hD hF g1 g2 hg1 hg2
        L lam δ R p hδ hR i j mu hm F G

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
