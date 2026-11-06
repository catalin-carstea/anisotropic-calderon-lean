import Calderon.ActualFiniteHarmonicModelAngularSecondEnergyIntegral
import Calderon.ActualFiniteHarmonicModelPrincipalZWeightedScalarBounds
import Calderon.ActualFiniteHarmonicModelUZSecondBaseFullOneParts

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords SpectralWeightedGraph
  ReferenceDensityBounds ReferenceWeightedApproximation PrincipalCommutator
  BaseDensityAdjoint CoordinateBootstrapJets NormalizedPrincipalMetric ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeSecondEnergyBoundFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeSecondEnergyBoundFunction
attribute [local irreducible] nativePrincipalDefectScalarCoefficient finiteCoreSourceEnergy
  nativePrincipalCoefficient nativeZ

lemma nativeUZSecondBaseOperator_scalar_angular_action
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    nativeUZSecondBaseOperator hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3,
        nativePrincipalDefectScalarCoefficient g1 g2 L lam δ R p i j a x •
          coreDerivative hO hD hF a
            (coreDirectionalDerivative hO hD (coordinateDirection i)
              (coreDirectionalDerivative hO hD (coordinateDirection j) F)) x := by
  unfold nativeUZSecondBaseOperator
  simp only [secondBaseRightProduct,LinearMap.sum_apply,Submodule.coe_sum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i j *
    nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR)
      (coreDirectionalDerivative hO hD (coordinateDirection i)
        (coreDirectionalDerivative hO hD (coordinateDirection j) F)) x = _
  exact nativePrincipalCoefficient_nativeZ_scalar_angular_action hO hD hF g1 g2 hg1 hg2
    L lam δ R p hδ hR i j _ x

lemma nativeUZSecondBaseOperator_scalar_integral_sum
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (mu : R3 → ℝ) (hm : ContDiff ℝ ∞ mu)
    (F G : smoothCompactFiniteSphereCore hO hD) :
    (∫ x : R3, mu x * ⟪nativeUZSecondBaseOperator hO hD hF g1 g2 hg1
      L lam δ R p hg2 hδ hR F x,G x⟫_ℝ) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3,
        ∫ x : R3, mu x * nativePrincipalDefectScalarCoefficient g1 g2 L lam δ R p i j a x *
          ⟪coreDerivative hO hD hF a
            (coreDirectionalDerivative hO hD (coordinateDirection i)
              (coreDirectionalDerivative hO hD (coordinateDirection j) F)) x,G x⟫_ℝ := by
  let T (i j a : Fin 3) (x : R3) : ℝ :=
    mu x * nativePrincipalDefectScalarCoefficient g1 g2 L lam δ R p i j a x *
      ⟪coreDerivative hO hD hF a
        (coreDirectionalDerivative hO hD (coordinateDirection i)
          (coreDirectionalDerivative hO hD (coordinateDirection j) F)) x,G x⟫_ℝ
  have hInt (i j a : Fin 3) : Integrable (T i j a) := by
    let U := coreDerivative hO hD hF a
      (coreDirectionalDerivative hO hD (coordinateDirection i)
        (coreDirectionalDerivative hO hD (coordinateDirection j) F))
    have hc := contDiff_nativePrincipalDefectScalarCoefficient g1 g2 hg1 hg2
      L lam δ R p hδ hR i j a
    have ht := compact_inner_integrable
      (fun x => (mu x * nativePrincipalDefectScalarCoefficient g1 g2 L lam δ R p i j a x) • U x)
      (G : R3 → SphereL2) ((hm.mul hc).smul U.property.1).continuous
      G.property.1.continuous G.property.2.1
    simpa only [real_inner_smul_left,T,U] using ht
  calc
    _ = ∫ x : R3, ∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, T i j a x := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [nativeUZSecondBaseOperator_scalar_angular_action]
      simp only [sum_inner,real_inner_smul_left,Finset.mul_sum,mul_assoc,T]
    _ = _ := by
      rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ =>
        integrable_finset_sum _ (fun a _ => hInt i j a)))]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _ (fun a _ => hInt i j a))]
      apply Finset.sum_congr rfl
      intro j hj
      exact integral_finset_sum _ (fun a _ => hInt i j a)

theorem exists_nativeUZSecondBaseOperator_uniform_energy_bound
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R,
      ∀ p : ℕ, 1 ≤ p → ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g1 L lam δ R p x) →
      (∀ x ∈ K, coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x) →
      (∀ x ∈ K, referenceRadius δ R p L x * (actualReferenceBeta g1 L lam δ R p x)^2 ≤ eps) →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport (F : R3 → SphereL2) ⊆ K →
      |∫ x : R3, referenceDensityFamily g1 L (lam,x) *
        ⟪nativeUZSecondBaseOperator hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨C0,hC0,hcoeff⟩ := exists_nativePrincipalDefectWeightedScalar_uniform_bounds g1 g2 hg1 hg2 L hL K hK
  refine ⟨216*C0,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  let mu : R3 → ℝ := fun x => referenceDensityFamily g1 L (lam,x)
  let beta : R3 → ℝ := actualReferenceBeta g1 L lam δ R p
  let J : ℝ := ∫ x : R3, mu x*finiteCoreSourceEnergy hO hD (beta x) F x
  let T (i j a : Fin 3) : ℝ := ∫ x : R3,
    mu x * nativePrincipalDefectScalarCoefficient g1 g2 L lam δ R p i j a x *
      ⟪coreDerivative hO hD hF a
        (coreDirectionalDerivative hO hD (coordinateDirection i)
          (coreDirectionalDerivative hO hD (coordinateDirection j) F)) x,F x⟫_ℝ
  have hterm (i j a : Fin 3) : |T i j a| ≤ (8*C0*eps)*J := by
    apply coreDerivative_secondBase_scalar_integral_bound hO hD hF g1 hg1 L lam a i j C0 eps hC0.le heps beta
      (continuous_actualReferenceBeta g1 hg1 L lam δ R p hL hδ hR)
      (actualReferenceBeta_pos g1 hg1 L lam δ R p hL hδ hR hp)
      (nativePrincipalDefectScalarCoefficient g1 g2 L lam δ R p i j a)
      (contDiff_nativePrincipalDefectScalarCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR i j a)
      K ?_ ?_ F hsupp
    · intro x hx
      exact (hcoeff lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx
        (hb x hx) (hH8 x hx) (hsmall x hx) i j a).1
    · intro x hx
      exact (hcoeff lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx
        (hb x hx) (hH8 x hx) (hsmall x hx) i j a).2 i
  have hm : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  rw [nativeUZSecondBaseOperator_scalar_integral_sum hO hD hF g1 g2 hg1 hg2
    L lam δ R p hδ hR mu hm F F]
  change |∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, T i j a| ≤ _
  calc
    _ ≤ ∑ i : Fin 3, |∑ j : Fin 3, ∑ a : Fin 3, T i j a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |∑ a : Fin 3, T i j a| :=
      Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, |T i j a| :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, (8*C0*eps)*J :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun a _ => hterm i j a)))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
