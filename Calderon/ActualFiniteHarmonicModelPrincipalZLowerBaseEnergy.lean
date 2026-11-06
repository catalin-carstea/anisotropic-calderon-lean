import Calderon.ActualFiniteHarmonicModelAngularZeroEnergyIntegral
import Calderon.ActualFiniteHarmonicModelPrincipalZWordScalarBounds

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords SpectralWeightedGraph
  ReferenceDensityBounds ReferenceWeightedApproximation PrincipalCommutator
  BaseDensityAdjoint CoordinateBootstrapJets NormalizedPrincipalMetric ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev principalZLowerEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] principalZLowerEnergyFunction
attribute [local irreducible] nativePrincipalDefectWordScalarCoefficient finiteCoreSourceEnergy
  nativePrincipalCoefficient nativeZ

theorem exists_nativePrincipalZ_first_uniform_energy_bound
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
      ∀ i j k l : Fin 3,
      |∫ x : R3, referenceDensityFamily g1 L (lam,x) *
        ⟪(nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i j *
      coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection k))
        (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR)) (coreDirectionalDerivative hO hD (coordinateDirection l) F) x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨C0,hC0,hcoeff⟩ := exists_nativePrincipalDefectWordScalar_uniform_smallness
    g1 g2 hg1 hg2 L hL K hK
  refine ⟨12*C0,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp i j k l
  let mu : R3 → ℝ := fun x => referenceDensityFamily g1 L (lam,x)
  let beta : R3 → ℝ := actualReferenceBeta g1 L lam δ R p
  let U := (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i j *
      coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection k))
        (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR)) (coreDirectionalDerivative hO hD (coordinateDirection l) F)
  have hbpos : ∀ x, 0 < beta x := actualReferenceBeta_pos g1 hg1 L lam δ R p hL hδ hR hp
  have hbound (x : R3) : |mu x*⟪U x,F x⟫_ℝ| ≤
      (12*C0*eps)*(mu x*finiteCoreSourceEnergy hO hD (beta x) F x) := by
    have hm0 : 0 ≤ mu x := (referenceDensityFamily_pos g1 hg1 L (lam,x)).le
    by_cases hx : x ∈ K
    · have hact : U x = ∑ a : Fin 3,
          nativePrincipalDefectWordScalarCoefficient g1 g2 L lam δ R p i j a [k] x •
            coreDerivative hO hD hF a (coreDirectionalDerivative hO hD (coordinateDirection l) F) x :=
        nativePrincipalCoefficient_first_coefficientDerivative_nativeZ_scalar_action hO hD hF g1 g2 hg1 hg2
        L lam δ R p hδ hR i j k (coreDirectionalDerivative hO hD (coordinateDirection l) F) x
      have hterm (a : Fin 3) :
          |nativePrincipalDefectWordScalarCoefficient g1 g2 L lam δ R p i j a [k] x *
            ⟪coreDerivative hO hD hF a (coreDirectionalDerivative hO hD (coordinateDirection l) F) x,F x⟫_ℝ| ≤
          (4*C0*eps)*finiteCoreSourceEnergy hO hD (beta x) F x := by
        apply angular_first_scalar_le_sourceEnergy hO hD hF a l (beta x) C0 eps _
          (hbpos x) hC0.le heps ?_ F x
        exact (hcoeff lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx
          (hb x hx) (hH8 x hx) (hsmall x hx) i j a k k).1
      have hsum : |⟪U x,F x⟫_ℝ| ≤ (12*C0*eps)*finiteCoreSourceEnergy hO hD (beta x) F x := by
        rw [hact,sum_inner]
        simp only [real_inner_smul_left]
        calc
          _ ≤ ∑ a : Fin 3, |nativePrincipalDefectWordScalarCoefficient g1 g2 L lam δ R p i j a [k] x *
            ⟪coreDerivative hO hD hF a (coreDirectionalDerivative hO hD (coordinateDirection l) F) x,F x⟫_ℝ| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ a : Fin 3, (4*C0*eps)*finiteCoreSourceEnergy hO hD (beta x) F x :=
            Finset.sum_le_sum (fun a _ => hterm a)
          _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring
      rw [abs_mul,abs_of_nonneg hm0]
      calc
        _ ≤ mu x*((12*C0*eps)*finiteCoreSourceEnergy hO hD (beta x) F x) :=
          mul_le_mul_of_nonneg_left hsum hm0
        _ = _ := by ring
    · have hzF : F x = 0 := image_eq_zero_of_notMem_tsupport (fun hy => hx (hsupp hy))
      have hN := finiteCoreSourceEnergy_nonneg hO hD (beta x) (hbpos x).le F x
      simp only [hzF,inner_zero_right,mul_zero,abs_zero]
      positivity
  have hN : Integrable (fun x : R3 => mu x*finiteCoreSourceEnergy hO hD (beta x) F x) := by
    simpa only [mu,finiteCoreSourceEnergy] using
      integrable_native_core_source_norm hO hD g1 hg1 L lam beta
        (continuous_actualReferenceBeta g1 hg1 L lam δ R p hL hδ hR) hbpos F
  have hi := norm_integral_le_of_norm_le (f := fun x : R3 => mu x*⟪U x,F x⟫_ℝ)
    (hN.const_mul (12*C0*eps))
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hbound x))
  rw [integral_const_mul] at hi
  simpa only [Real.norm_eq_abs,mu,beta,U] using hi

theorem exists_nativePrincipalZ_second_uniform_energy_bound
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
      ∀ i j : Fin 3,
      |∫ x : R3, referenceDensityFamily g1 L (lam,x) *
        ⟪(nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i j *
      coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection i))
        (coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection j))
          (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR))) F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨C0,hC0,hcoeff⟩ := exists_nativePrincipalDefectWordScalar_uniform_smallness
    g1 g2 hg1 hg2 L hL K hK
  refine ⟨12*C0,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp i j
  let mu : R3 → ℝ := fun x => referenceDensityFamily g1 L (lam,x)
  let beta : R3 → ℝ := actualReferenceBeta g1 L lam δ R p
  let U := (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i j *
      coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection i))
        (coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection j))
          (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR))) F
  have hbpos : ∀ x, 0 < beta x := actualReferenceBeta_pos g1 hg1 L lam δ R p hL hδ hR hp
  have hbound (x : R3) : |mu x*⟪U x,F x⟫_ℝ| ≤
      (12*C0*eps)*(mu x*finiteCoreSourceEnergy hO hD (beta x) F x) := by
    have hm0 : 0 ≤ mu x := (referenceDensityFamily_pos g1 hg1 L (lam,x)).le
    by_cases hx : x ∈ K
    · have hact : U x = ∑ a : Fin 3,
          nativePrincipalDefectWordScalarCoefficient g1 g2 L lam δ R p i j a [i,j] x •
            coreDerivative hO hD hF a F x :=
        nativePrincipalCoefficient_second_coefficientDerivative_nativeZ_scalar_action hO hD hF g1 g2 hg1 hg2
        L lam δ R p hδ hR i j F x
      have hterm (a : Fin 3) :
          |nativePrincipalDefectWordScalarCoefficient g1 g2 L lam δ R p i j a [i,j] x *
            ⟪coreDerivative hO hD hF a F x,F x⟫_ℝ| ≤
          (4*C0*eps)*finiteCoreSourceEnergy hO hD (beta x) F x := by
        apply angular_zero_scalar_le_sourceEnergy hO hD hF a (beta x) C0 eps _
          (hbpos x) hC0.le heps ?_ F x
        exact (hcoeff lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx
          (hb x hx) (hH8 x hx) (hsmall x hx) i j a i j).2
      have hsum : |⟪U x,F x⟫_ℝ| ≤ (12*C0*eps)*finiteCoreSourceEnergy hO hD (beta x) F x := by
        rw [hact,sum_inner]
        simp only [real_inner_smul_left]
        calc
          _ ≤ ∑ a : Fin 3, |nativePrincipalDefectWordScalarCoefficient g1 g2 L lam δ R p i j a [i,j] x *
            ⟪coreDerivative hO hD hF a F x,F x⟫_ℝ| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ a : Fin 3, (4*C0*eps)*finiteCoreSourceEnergy hO hD (beta x) F x :=
            Finset.sum_le_sum (fun a _ => hterm a)
          _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring
      rw [abs_mul,abs_of_nonneg hm0]
      calc
        _ ≤ mu x*((12*C0*eps)*finiteCoreSourceEnergy hO hD (beta x) F x) :=
          mul_le_mul_of_nonneg_left hsum hm0
        _ = _ := by ring
    · have hzF : F x = 0 := image_eq_zero_of_notMem_tsupport (fun hy => hx (hsupp hy))
      have hN := finiteCoreSourceEnergy_nonneg hO hD (beta x) (hbpos x).le F x
      simp only [hzF,inner_zero_right,mul_zero,abs_zero]
      positivity
  have hN : Integrable (fun x : R3 => mu x*finiteCoreSourceEnergy hO hD (beta x) F x) := by
    simpa only [mu,finiteCoreSourceEnergy] using
      integrable_native_core_source_norm hO hD g1 hg1 L lam beta
        (continuous_actualReferenceBeta g1 hg1 L lam δ R p hL hδ hR) hbpos F
  have hi := norm_integral_le_of_norm_le (f := fun x : R3 => mu x*⟪U x,F x⟫_ℝ)
    (hN.const_mul (12*C0*eps))
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hbound x))
  rw [integral_const_mul] at hi
  simpa only [Real.norm_eq_abs,mu,beta,U] using hi

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
