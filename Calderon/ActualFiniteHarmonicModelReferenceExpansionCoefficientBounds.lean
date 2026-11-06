import Calderon.ActualFiniteHarmonicModelReferenceConnectionExpansion
import Calderon.ActualReferenceDDHigherGeometryJets
import Calderon.ActualReferenceDDHigherLogFrameJets

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SmoothMetricFrame
  AmbientReferenceRaising ConformalDepth MovingFrameConnection
  ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherLogFrameJets
  ActualHorizontalNormBridge ReferenceWeightedApproximation

theorem exists_nativeReferenceConnectionCoefficientMass_uniform_bound
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ a : Fin 3,
      nativeReferenceConnectionCoefficientMass g L lam a x ≤ C := by
  obtain ⟨M,hM,hm⟩ := exists_referenceDD_fixed_geometry_uniform_coordinate_word_bounds hO hD g hg L K hK 0
  refine ⟨5*M,by linarith,?_⟩
  intro lam hlam x hx a
  have he (b c : Fin 3) :
      |referenceFrameConnectionCoefficient g L lam x (referenceMetricGramFrame g L (lam,x) a) b c| ≤ M := by
    simpa only [coordinateFieldWordPartial] using (hm lam hlam x hx [] (by simp)).2.2.2.1 a b c
  have hs := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin 3))) =>
    Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Fin 3))) => he b c))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hs
  unfold nativeReferenceConnectionCoefficientMass
  linarith

theorem exists_nativeReferenceProfileScalar_uniform_coefficient_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      1 ≤ actualReferenceBeta g L lam δ R p x → ∀ a : Fin 3,
      |referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x| ≤
        C*actualReferenceBeta g L lam δ R p x := by
  obtain ⟨C,hC,hb⟩ := exists_referenceDD_logRadius_frame_uniform_coordinate_word_bounds g hg L hL K hK 0
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx hbeta a
  simpa only [coordinateFieldWordPartial,List.length_nil,Nat.add_zero,pow_one,actualReferenceBeta] using
    (hb lam hlam δ hδ hδ1 R hR p hp x hx hbeta [] (by simp)).1 a

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
