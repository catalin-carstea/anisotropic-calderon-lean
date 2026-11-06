import Calderon.ActualFiniteHarmonicModelPrincipalHHalfWords
import Calderon.ActualFiniteHarmonicModelSecondBaseHalfFormEnergy
import Calderon.ActualFiniteHarmonicModelFirstBaseHalfFormEnergy
import Calderon.ActualFiniteHarmonicModelDensityDerivativeBound
import Calderon.ActualFiniteHarmonicModelDensityPairLinearMap

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords SpectralWeightedGraph
  ReferenceDensityBounds ReferenceWeightedApproximation PrincipalCommutator
  BaseDensityAdjoint CoordinateBootstrapJets NormalizedPrincipalMetric ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev hPrincipalEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] hPrincipalEnergyFunction
attribute [local irreducible] finiteCoreSourceEnergy nativeB nativeZ

theorem exists_nativeH_principal_commutator_uniform_energy_bound
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
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport (F : R3 → SphereL2) ⊆ K → ∀ l i k : Fin 3,
      |∫ x : R3, referenceDensityFamily g1 L (lam,x) *
        ⟪commutator
          (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l *
            coreDirectionalDerivative hO hD (coordinateDirection l))
          (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i k *
            coreDirectionalDerivative hO hD (coordinateDirection i) *
            coreDirectionalDerivative hO hD (coordinateDirection k)) F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨C0,hC0,hWords⟩ := exists_nativePrincipal_H_uniform_half_word_bounds hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨M,hM,hDensity⟩ := exists_referenceDensity_uniform_relative_coordinate_bound g1 hg1 L K hK
  refine ⟨(3*(2+M)+1)*C0,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp l i k
  let beta := actualReferenceBeta g1 L lam δ R p
  let d (s : Fin 3) := coreDirectionalDerivative hO hD (coordinateDirection s)
  let H := nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l
  let a := nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i k
  let A := H*coefficientDerivative (d l) a
  let B := a*coefficientDerivative (d k) H
  let C := a*coefficientDerivative (d i) H
  let Z := a*coefficientDerivative (d i) (coefficientDerivative (d k) H)
  let q := nativeCoreDensityPairLinearMap hO hD g1 hg1 L lam F
  let J := ∫ x : R3, referenceDensityFamily g1 L (lam,x)*finiteCoreSourceEnergy hO hD (beta x) F x
  have hpos (x : R3) : 0 < beta x := actualReferenceBeta_pos g1 hg1 L lam δ R p hL hδ hR hp x
  have hcont : Continuous beta := continuous_actualReferenceBeta g1 hg1 L lam δ R p hL hδ hR
  have hforms (x : R3) (hx : x ∈ K) (s t : Fin 3) (U V : smoothCompactFiniteSphereCore hO hD) :=
    hWords lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx (hb x hx) (hH8 x hx) (hsmall x hx) i k l s t U V
  have hmu (s : Fin 3) (x : R3) (hx : x ∈ K) : |directionalFDeriv (coordinateDirection s)
      (fun y => referenceDensityFamily g1 L (lam,y)) x| ≤ M*beta x*referenceDensityFamily g1 L (lam,x) := by
    calc
      _ ≤ M*referenceDensityFamily g1 L (lam,x) := hDensity lam hlam x hx s
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hM.le (hb x hx))
        (referenceDensityFamily_pos g1 hg1 L (lam,x)).le
  have hA : |q ((A*d i*d k) F)| ≤ ((2+M)*(C0*eps))*J := by
    apply nativeCore_second_base_half_form_energy_bound hO hD g1 hg1 L lam beta hcont hpos
      (C0*eps) M (mul_nonneg hC0.le heps) hM.le K A i k F hsupp
    · intro x hx U V
      simpa only [mul_assoc] using (hforms x hx l i U V).1
    · intro x hx U V
      simpa only [mul_assoc] using (hforms x hx l i U V).2.1
    · exact hmu i
  have hB : |q ((B*d i*d l) F)| ≤ ((2+M)*(C0*eps))*J := by
    apply nativeCore_second_base_half_form_energy_bound hO hD g1 hg1 L lam beta hcont hpos
      (C0*eps) M (mul_nonneg hC0.le heps) hM.le K B i l F hsupp
    · intro x hx U V
      simpa only [mul_assoc] using (hforms x hx k i U V).2.2.1
    · intro x hx U V
      simpa only [mul_assoc] using (hforms x hx k i U V).2.2.2.1
    · exact hmu i
  have hC : |q ((C*d k*d l) F)| ≤ ((2+M)*(C0*eps))*J := by
    apply nativeCore_second_base_half_form_energy_bound hO hD g1 hg1 L lam beta hcont hpos
      (C0*eps) M (mul_nonneg hC0.le heps) hM.le K C k l F hsupp
    · intro x hx U V
      simpa only [mul_assoc] using (hforms x hx i k U V).2.2.1
    · intro x hx U V
      simpa only [mul_assoc] using (hforms x hx i k U V).2.2.2.1
    · exact hmu k
  have hZ : |q ((Z*d l) F)| ≤ (C0*eps)*J := by
    apply nativeCore_first_base_half_form_energy_bound hO hD g1 hg1 L lam beta hcont hpos
      (C0*eps) (mul_nonneg hC0.le heps) K Z l F hsupp
    intro x hx U V
    simpa only [mul_assoc] using (hforms x hx k i U V).2.2.2.2
  have he : commutator (H*d l) (a*d i*d k) = A*d i*d k-Z*d l-B*d i*d l-C*d k*d l :=
    commutator_first_second (d l) (d i) (d k) H a
      (nativeH_commute_principal hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l i k)
      (coreDirectionalDerivative_commute hO hD _ _) (coreDirectionalDerivative_commute hO hD _ _)
  change |q ((commutator (H*d l) (a*d i*d k)) F)| ≤ _
  rw [he]
  simp only [LinearMap.sub_apply,map_sub]
  calc
    _ ≤ |q ((A*d i*d k) F)|+|q ((Z*d l) F)|+|q ((B*d i*d l) F)|+|q ((C*d k*d l) F)| := by
      exact (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
        (add_le_add (abs_sub _ _) le_rfl)) le_rfl)
    _ ≤ ((2+M)*(C0*eps))*J+(C0*eps)*J+((2+M)*(C0*eps))*J+((2+M)*(C0*eps))*J :=
      add_le_add (add_le_add (add_le_add hA hZ) hB) hC
    _ = _ := by ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
