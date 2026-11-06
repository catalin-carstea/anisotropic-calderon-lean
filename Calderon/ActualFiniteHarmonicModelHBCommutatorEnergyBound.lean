import Calderon.ActualFiniteHarmonicModelHBFirstBaseProducts
import Calderon.ActualFiniteHarmonicModelHBSecondBaseEnergyBound
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
private abbrev hbCommutatorEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] hbCommutatorEnergyFunction
attribute [local irreducible] finiteCoreSourceEnergy nativeB nativeZ

theorem exists_nativeHB_commutator_uniform_energy_bound
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
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport (F : R3 → SphereL2) ⊆ K → ∀ l i : Fin 3,
      |∫ x : R3, referenceDensityFamily g1 L (lam,x) *
        ⟪commutator
          (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l *
            coreDirectionalDerivative hO hD (coordinateDirection l))
          (nativeB hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR *
            coreDirectionalDerivative hO hD (coordinateDirection i)) F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨C1,hC1,hProducts⟩ := exists_nativeHB_first_base_uniform_half_threehalf_forms
    hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨C2,hC2,hSecond⟩ := exists_nativeHB_second_base_uniform_energy_bound
    hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨C2+2*C1,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp l i
  let beta := actualReferenceBeta g1 L lam δ R p
  let d (s : Fin 3) := coreDirectionalDerivative hO hD (coordinateDirection s)
  let H := nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l
  let B := nativeB hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR
  let q := nativeCoreDensityPairLinearMap hO hD g1 hg1 L lam F
  let J := ∫ x : R3, referenceDensityFamily g1 L (lam,x)*finiteCoreSourceEnergy hO hD (beta x) F x
  have hpos (x : R3) : 0 < beta x := actualReferenceBeta_pos g1 hg1 L lam δ R p hL hδ hR hp x
  have hcont : Continuous beta := continuous_actualReferenceBeta g1 hg1 L lam δ R p hL hδ hR
  have hsec : |q ((commutator H B*d l*d i) F)| ≤ (C2*eps)*J :=
    hSecond lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp l i l i
  have hfirst (T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (k : Fin 3)
      (hT : ∀ x ∈ K, ∀ U V : smoothCompactFiniteSphereCore hO hD,
        |⟪T U x,V x⟫_ℝ| ≤ (C1*eps)*
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x‖ *
          ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) V x‖) :
      |q ((T*d k) F)| ≤ (C1*eps)*J := by
    apply nativeCore_density_pair_energy_bound_of_support_local hO hD g1 hg1 L lam
      beta hcont hpos (C1*eps) (mul_nonneg hC1.le heps) K _ F hsupp
    intro x hx
    calc
      _ ≤ (C1*eps)*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (d k F) x‖ *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ := hT x hx (d k F) F
      _ = (C1*eps)*(‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (d k F) x‖ *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (norm_gradient_half_mul_threehalf_le_finiteCoreSourceEnergy hO hD (beta x) (hpos x) F x k)
        (mul_nonneg hC1.le heps)
  have hA : |q ((H*coefficientDerivative (d l) B*d i) F)| ≤ (C1*eps)*J :=
    hfirst _ i (fun x hx U V =>
      (hProducts lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx
        (hb x hx) (hH8 x hx) (hsmall x hx) l i l U V).1)
  have hB : |q ((B*coefficientDerivative (d i) H*d l) F)| ≤ (C1*eps)*J :=
    hfirst _ l (fun x hx U V =>
      (hProducts lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx
        (hb x hx) (hH8 x hx) (hsmall x hx) l i i U V).2)
  change |q (commutator (H*d l) (B*d i) F)| ≤ _
  rw [commutator_first_first (d l) (d i) H B (coreDirectionalDerivative_commute hO hD _ _)]
  simp only [LinearMap.sub_apply,LinearMap.add_apply,map_sub,map_add]
  calc
    _ ≤ |q ((commutator H B*d l*d i) F)|+|q ((H*coefficientDerivative (d l) B*d i) F)|+
        |q ((B*coefficientDerivative (d i) H*d l) F)| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (C2*eps)*J+(C1*eps)*J+(C1*eps)*J := add_le_add (add_le_add hsec hA) hB
    _ = _ := by ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
