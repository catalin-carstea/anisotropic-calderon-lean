import Calderon.ActualFiniteHarmonicModelFullFirstDefectEnergy
import Calderon.ActualFiniteHarmonicModelDefectTEnergy
import Calderon.ActualFiniteHarmonicModelUZAdjointEnergyBound
import Calderon.ActualFiniteHarmonicModelFullCoefficientWords

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords SpectralWeightedGraph
  ReferenceDensityBounds ReferenceWeightedApproximation PrincipalCommutator
  SectionFiveErrorForms BaseDensityAdjoint CoordinateBootstrapJets NormalizedPrincipalMetric ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev fullErrorEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] fullErrorEnergyFunction
attribute [local irreducible] finiteCoreSourceEnergy nativeB nativeZ nativeU nativeUdag nativeT nativeTdag nativeH nativeH0 nativeC nativePrincipalCoefficient nativeFullErrorExpression

theorem exists_nativeFullErrorExpression_uniform_energy_bound
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
        ⟪nativeFullErrorExpression hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨CS,hCS,hS⟩ := exists_nativeFirstDefect_commutator_uniform_energy_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CD,hCD,hDform⟩ := exists_nativeDefect_T_uniform_energy_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CZ,hCZ,hZ⟩ := exists_nativeUZ_adjoint_sum_uniform_energy_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨CS+2*CD+2*CZ,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  let U := nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  let Ud := nativeUdag hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  let T := nativeT hO hD hF g1 hg1 L lam δ R p hδ hR
  let Td := nativeTdag hO hD hF g1 hg1 L lam δ R p hδ hR
  let Z := nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR
  let Zd := nativeZdag hO hD hF g1 hg1 L lam δ R p hδ hR
  let S := ActualModelCommutatorWords.commutator (2*(Td-T)+(Ud-U)) U
  let D0 := ActualModelCommutatorWords.commutator (Ud-U) T
  let Z0 := U*Z+Zd*Ud
  let q := nativeCoreDensityPairLinearMap hO hD g1 hg1 L lam F
  let J := ∫ x : R3, referenceDensityFamily g1 L (lam,x)*finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x
  have hs : |q (S F)| ≤ (CS*eps)*J := hS lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  have hd : |q (D0 F)| ≤ (CD*eps)*J := hDform lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  have hz : |q (Z0 F)| ≤ (CZ*eps)*J := hZ lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  rw [nativeFullErrorExpression_eq_reduced]
  unfold nativeReducedErrorExpression
  change |q ((S+2*D0-2*Z0) F)| ≤ _
  simp only [two_mul,LinearMap.add_apply,LinearMap.sub_apply,map_add,map_sub]
  let a := q (S F)
  let b := q (D0 F)
  let c := q (Z0 F)
  change |a+(b+b)-(c+c)| ≤ _
  calc
    _ ≤ |a|+2*|b|+2*|c| := by
      linarith [abs_sub (a+(b+b)) (c+c),abs_add_le a (b+b),abs_add_le b b,abs_add_le c c]
    _ ≤ (CS*eps)*J+2*((CD*eps)*J)+2*((CZ*eps)*J) :=
      add_le_add (add_le_add hs (mul_le_mul_of_nonneg_left hd (by norm_num))) (mul_le_mul_of_nonneg_left hz (by norm_num))
    _ = _ := by ring


theorem exists_nativeReducedErrorExpression_uniform_energy_bound
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
        ⟪nativeReducedErrorExpression hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨C,hC,hbound⟩ := exists_nativeFullErrorExpression_uniform_energy_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  rw [← nativeFullErrorExpression_eq_reduced]
  exact hbound lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp


theorem exists_nativeFullErrorCoefficientWords_uniform_energy_bound
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
        ⟪nativeFullErrorCoefficientWords hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨C,hC,hbound⟩ := exists_nativeFullErrorExpression_uniform_energy_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  rw [← nativeFullErrorExpression_eq_fullCoefficientWords]
  exact hbound lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
