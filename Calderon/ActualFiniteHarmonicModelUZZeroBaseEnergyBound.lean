import Calderon.ActualFiniteHarmonicModelBZEnergyIntegrals
import Calderon.ActualFiniteHarmonicModelPrincipalZLowerBaseEnergy
import Calderon.ActualFiniteHarmonicModelDensityPairLinearMap
import Calderon.ActualFiniteHarmonicModelUZZeroBaseOperator
import Calderon.ActualFiniteHarmonicModelCZEnergyIntegral

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords SpectralWeightedGraph
  ReferenceDensityBounds ReferenceWeightedApproximation PrincipalCommutator
  BaseDensityAdjoint CoordinateBootstrapJets NormalizedPrincipalMetric ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev uzZeroEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] uzZeroEnergyFunction
attribute [local irreducible] finiteCoreSourceEnergy nativeB nativeZ

theorem exists_nativeUZZeroBaseOperator_uniform_energy_bound
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
        ⟪nativeUZZeroBaseOperator hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨CP,hCP,hPrincipal⟩ := exists_nativePrincipalZ_second_uniform_energy_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CB,hCB,hBZ⟩ := exists_nativeBZ_uniform_energy_integral_bounds hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CC,hCC,hCZ⟩ := exists_nativeCZ_uniform_energy_integral_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨9*CP+3*CB+CC,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  let q := nativeCoreDensityPairLinearMap hO hD g1 hg1 L lam F
  let J := ∫ x : R3, referenceDensityFamily g1 L (lam,x)*
    finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x
  let d (i : Fin 3) := coreDirectionalDerivative hO hD (coordinateDirection i)
  let A := nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR
  let B (i : Fin 3) := nativeB hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR
  let Z := nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR
  let C0 := nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  let T (i j : Fin 3) := q ((A i j*coefficientDerivative (d i) (coefficientDerivative (d j) Z)) F)
  let U (i : Fin 3) := q ((B i*coefficientDerivative (d i) Z) F)
  let V := q ((C0*Z) F)
  have hT (i j : Fin 3) : |T i j| ≤ CP*eps*J :=
    hPrincipal lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp i j
  have hU (i : Fin 3) : |U i| ≤ CB*eps*J :=
    (hBZ lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp i i).2 i
  have hV : |V| ≤ CC*eps*J :=
    hCZ lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  have hsum : q (nativeUZZeroBaseOperator hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F) =
      (∑ i : Fin 3, ∑ j : Fin 3, T i j) + (∑ i : Fin 3, U i) + V := by
    simp only [nativeUZZeroBaseOperator,zeroBaseRightProduct,LinearMap.add_apply,
      LinearMap.sum_apply,map_add,map_sum,Module.End.mul_apply,T,U,V,A,B,C0,Z,d]
  change |q (nativeUZZeroBaseOperator hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F)| ≤ _
  rw [hsum]
  have hPsum : |∑ i : Fin 3, ∑ j : Fin 3, T i j| ≤ 9*CP*eps*J := by
    calc
      _ ≤ ∑ i : Fin 3, |∑ j : Fin 3, T i j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |T i j| :=
        Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, CP*eps*J :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hT i j))
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]; ring
  have hBsum : |∑ i : Fin 3, U i| ≤ 3*CB*eps*J := by
    calc
      _ ≤ ∑ i : Fin 3, |U i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 3, CB*eps*J := Finset.sum_le_sum (fun i _ => hU i)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]; ring
  calc
    _ ≤ |(∑ i : Fin 3, ∑ j : Fin 3, T i j)+(∑ i : Fin 3, U i)|+|V| := abs_add_le _ _
    _ ≤ (|∑ i : Fin 3, ∑ j : Fin 3, T i j|+|∑ i : Fin 3, U i|)+|V| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (9*CP*eps*J+3*CB*eps*J)+CC*eps*J := add_le_add (add_le_add hPsum hBsum) hV
    _ = _ := by ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
