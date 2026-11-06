import Calderon.ActualFiniteHarmonicModelSecondAngularBounds
import Calderon.ActualFiniteHarmonicModelReferenceFirstAngularAdjoint
import Calderon.ActualFiniteHarmonicModelPointwiseAngularAdjoints
import Calderon.ActualFiniteHarmonicModelSupportLocalEnergyIntegral

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords SpectralWeightedGraph
  ReferenceDensityBounds ReferenceWeightedApproximation PrincipalCommutator
  BaseDensityAdjoint CoordinateBootstrapJets NormalizedPrincipalMetric ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev referenceDWFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] referenceDWFunction
attribute [local irreducible] finiteCoreSourceEnergy nativeH nativeC

theorem exists_nativeReferenceFirst_coefficientDerivative_W_uniform_threehalf_forms
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R,
      ∀ p : ℕ, 1 ≤ p → ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x →
      referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ i j : Fin 3, ∀ U V : smoothCompactFiniteSphereCore hO hD,
      let B := nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR i
      let H0 := nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
      let d := coreDirectionalDerivative hO hD (coordinateDirection j)
      |⟪(B*coefficientDerivative d H0) U x,V x⟫_ℝ| ≤
        (C*eps*beta)*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) U x‖ *
          ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) V x‖ := by
  obtain ⟨CH,hCH,hHform⟩ := exists_nativeW_uniform_threehalf_half_form_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CB,hCB,hBnorm⟩ := exists_nativeReferenceFirstAngularAdjoint_uniform_half_norm_bound hO hD hF g1 hg1 L K hK
  refine ⟨CH*CB,mul_pos hCH hCB,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall i j U V B H0 d
  have hbpos : 0 < beta := by linarith
  let BA := nativeReferenceFirstAngularAdjoint hO hD hF g1 hg1 L lam i
  let u := ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) U x‖
  let v := ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) V x‖
  have hnB := hBnorm lam hlam x hx i V
  have ht := (hHform lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall j j U (BA V)).2.1
  change |⟪B (coefficientDerivative d H0 U) x,V x⟫_ℝ| ≤ _
  rw [nativeReferenceFirstCoefficient_pointwise_inner_adjoint]
  calc
    _ ≤ (CH*eps*beta)*u*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (BA V) x‖ := ht
    _ ≤ (CH*eps*beta)*u*(CB*v) :=
      mul_le_mul_of_nonneg_left hnB (by dsimp only [u]; positivity)
    _ = _ := by dsimp only [u,v]; ring

theorem exists_nativeReferenceFirst_coefficientDerivative_W_uniform_energy_integral_bound
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
      ∀ i j : Fin 3, ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport (F : R3 → SphereL2) ⊆ K →
      |∫ x : R3, referenceDensityFamily g1 L (lam,x) *
        ⟪(nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR i *
          coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection j))
            (nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)) F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨C,hC,hforms⟩ := exists_nativeReferenceFirst_coefficientDerivative_W_uniform_threehalf_forms hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall i j F hsupp
  let beta : R3 → ℝ := actualReferenceBeta g1 L lam δ R p
  have hcont : Continuous beta := continuous_actualReferenceBeta g1 hg1 L lam δ R p hL hδ hR
  have hpos : ∀ x, 0 < beta x := actualReferenceBeta_pos g1 hg1 L lam δ R p hL hδ hR hp
  apply nativeCore_density_pair_energy_bound_of_support_local hO hD g1 hg1 L lam
    beta hcont hpos (C*eps) (mul_nonneg hC.le heps) K _ F hsupp
  intro x hx
  let V := ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖
  have ht := hforms lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx
    (hb x hx) (hH8 x hx) (hsmall x hx) i j F F
  have hprod := beta_mul_threehalf_norm_sq_le_finiteCoreSourceEnergy hO hD
    (beta x) (hpos x).le F x
  calc
    _ ≤ (C*eps*beta x)*V*V := ht
    _ = (C*eps)*(beta x*V^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (mul_nonneg hC.le heps)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
