import Calderon.ActualFiniteHarmonicModelHPrincipalEnergyBound
import Calderon.ActualFiniteHarmonicModelH0PrincipalPointwiseEnergy

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords SpectralWeightedGraph
  ReferenceDensityBounds ReferenceWeightedApproximation PrincipalCommutator
  SectionFiveErrorForms BaseDensityAdjoint CoordinateBootstrapJets NormalizedPrincipalMetric ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev fullPrincipalEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] fullPrincipalEnergyFunction
attribute [local irreducible] finiteCoreSourceEnergy nativeB nativeZ

theorem exists_nativeFirstDefect_principal_uniform_energy_bound
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
        ⟪ActualModelCommutatorWords.commutator
          (2 * (nativeTdag hO hD hF g1 hg1 L lam δ R p hδ hR -
            nativeT hO hD hF g1 hg1 L lam δ R p hδ hR) +
            (nativeUdag hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR -
            nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR))
          (∑ i : Fin 3, ∑ k : Fin 3,
            nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i k *
            coreDirectionalDerivative hO hD (coordinateDirection i) *
            coreDirectionalDerivative hO hD (coordinateDirection k)) F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨CH,hCH,hH⟩ := exists_nativeH_principal_commutator_uniform_energy_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨C0,hC0,hZero⟩ := exists_nativeH0_principal_commutator_pointwise_energy_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨27*CH+9*C0,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  let beta := actualReferenceBeta g1 L lam δ R p
  let d (s : Fin 3) := coreDirectionalDerivative hO hD (coordinateDirection s)
  let H := nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  let H0 := nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  let a := nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR
  let q := nativeCoreDensityPairLinearMap hO hD g1 hg1 L lam F
  let J := ∫ x : R3, referenceDensityFamily g1 L (lam,x)*finiteCoreSourceEnergy hO hD (beta x) F x
  let T (l i k : Fin 3) := q (ActualModelCommutatorWords.commutator (H l*d l) (a i k*d i*d k) F)
  let V (i k : Fin 3) := q (ActualModelCommutatorWords.commutator H0 (a i k*d i*d k) F)
  have hT (l i k : Fin 3) : |T l i k| ≤ CH*eps*J :=
    hH lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp l i k
  have hpos (x : R3) : 0 < beta x := actualReferenceBeta_pos g1 hg1 L lam δ R p hL hδ hR hp x
  have hcont : Continuous beta := continuous_actualReferenceBeta g1 hg1 L lam δ R p hL hδ hR
  have hV (i k : Fin 3) : |V i k| ≤ C0*eps*J := by
    apply nativeCore_density_pair_energy_bound_of_support_local hO hD g1 hg1 L lam beta hcont hpos
      (C0*eps) (mul_nonneg hC0.le heps) K (ActualModelCommutatorWords.commutator H0 (a i k*d i*d k) F) F hsupp
    intro x hx
    have ht := hZero lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx (hb x hx) (hH8 x hx) (hsmall x hx) i k F
    apply ht.trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC0.le heps)
    rw [finiteCoreSourceEnergy]
    exact angular_error_terms_le_sourceNormSquareIntegrand (beta x) _ _ _ _
  have hsT : |∑ l : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3, T l i k| ≤ 27*CH*eps*J := by
    calc
      _ ≤ ∑ l : Fin 3, |∑ i : Fin 3, ∑ k : Fin 3, T l i k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l : Fin 3, ∑ i : Fin 3, |∑ k : Fin 3, T l i k| :=
        Finset.sum_le_sum (fun l _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ l : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3, |T l i k| :=
        Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
      _ ≤ ∑ l : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3, CH*eps*J :=
        Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun k _ => hT l i k)))
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]; ring
  have hsV : |∑ i : Fin 3, ∑ k : Fin 3, V i k| ≤ 9*C0*eps*J := by
    calc
      _ ≤ ∑ i : Fin 3, |∑ k : Fin 3, V i k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 3, ∑ k : Fin 3, |V i k| := Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i : Fin 3, ∑ k : Fin 3, C0*eps*J := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun k _ => hV i k))
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]; ring
  rw [nativeFirstDefect_eq_modelFirstOrder]
  change |q (ActualModelCommutatorWords.commutator (modelFirstOrder d H H0)
    (∑ i : Fin 3, ∑ k : Fin 3, a i k*d i*d k) F)| ≤ _
  have he : q (ActualModelCommutatorWords.commutator (modelFirstOrder d H H0)
      (∑ i : Fin 3, ∑ k : Fin 3, a i k*d i*d k) F) =
      (∑ l : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3, T l i k)+(∑ i : Fin 3, ∑ k : Fin 3, V i k) := by
    unfold modelFirstOrder
    rw [ActualModelCommutatorWords.commutator_add_left,ActualModelCommutatorWords.commutator_sum_left]
    simp only [ActualModelCommutatorWords.commutator_sum_right,
      LinearMap.add_apply,LinearMap.sum_apply,map_sum,map_add,T,V]
  rw [he]
  calc
    _ ≤ |∑ l : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3, T l i k|+|∑ i : Fin 3, ∑ k : Fin 3, V i k| := abs_add_le _ _
    _ ≤ 27*CH*eps*J+9*C0*eps*J := add_le_add hsT hsV
    _ = _ := by ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
