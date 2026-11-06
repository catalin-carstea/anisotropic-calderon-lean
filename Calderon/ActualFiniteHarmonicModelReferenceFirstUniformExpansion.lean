import Calderon.ActualFiniteHarmonicModelReferenceFirstExpansions
import Calderon.ActualMixedDensityHigherCoefficientJets

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SmoothMetricFrame
  ActualMixedDensityHigherCoefficientJets ActualReferenceDDHigherGeometryJets
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

theorem exists_nativeReferenceFirst_uniform_linear_expansion
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ R : ℝ, ∀ p : ℕ, ∀ hδ : 0 < δ, ∀ hR : 0 < R,
      ∀ x ∈ K, ∀ j : Fin 3,
      HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF)
        (nativeReferenceFirstCoefficient hO hD hF g hg L lam δ R p hδ hR j) x C := by
  obtain ⟨M,hM,hbound⟩ := exists_mixed_background_coordinate_jet_bound g hg L K hK 0
  refine ⟨3*M,by have hm : 0 < M := lt_of_lt_of_le zero_lt_one hM; positivity,?_⟩
  intro lam hlam δ R p hδ hR x hx j
  have he := hasCoreScalarExpansionBound_nativeReferenceFirstCoefficient hO hD hF g hg L lam δ R p hδ hR j x
  apply hasCoreScalarExpansionBound_mono hO hD _ _ x _ _ he
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) =>
    (hbound lam hlam x hx).1 [] (by simp) a j)
  simpa only [coordinateFieldWordPartial,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] using hs

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
