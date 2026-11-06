import Calderon.ActualFiniteHarmonicModelConnectionDerivativeExpansion
import Calderon.ActualFiniteHarmonicModelReferenceExpansionCoefficientBounds

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SmoothMetricFrame
  AmbientReferenceRaising ConformalDepth MovingFrameConnection PrincipalCommutator
  ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherLogFrameJets
  ActualHorizontalNormBridge ReferenceWeightedApproximation

theorem exists_nativeReferenceConnection_uniform_expansion_masses
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ A : ℝ, 0 < A ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K,
      (∀ a : Fin 3, nativeReferenceConnectionCoefficientMass g L lam a x ≤ A) ∧
      (∀ a b : Fin 3, nativeReferenceConnectionDerivativeMass g L lam a b x ≤ A) ∧
      (∀ a b c : Fin 3, |referenceFrameConnectionCoefficient g L lam x
        (referenceMetricGramFrame g L (lam,x) a) b c| ≤ A) := by
  obtain ⟨M,hM,hm⟩ := exists_referenceDD_fixed_geometry_uniform_coordinate_word_bounds hO hD g hg L K hK 1
  let A := 1+6*M+14*M^2
  have hMpos : 0 < M := by linarith
  have hMA : M ≤ A := by dsimp only [A]; nlinarith [sq_nonneg M]
  have h5 : 5*M ≤ A := by dsimp only [A]; nlinarith [sq_nonneg M]
  have h14 : 14*M^2 ≤ A := by dsimp only [A]; linarith
  refine ⟨A,by dsimp only [A]; positivity,?_⟩
  intro lam hlam x hx
  have hGamma (a b c : Fin 3) : |referenceFrameConnectionCoefficient g L lam x
      (referenceMetricGramFrame g L (lam,x) a) b c| ≤ M := by
    simpa only [coordinateFieldWordPartial] using (hm lam hlam x hx [] (by simp)).2.2.2.1 a b c
  have hFrame (a j : Fin 3) : |referenceMetricGramFrame g L (lam,x) a j| ≤ M := by
    simpa only [coordinateFieldWordPartial] using (hm lam hlam x hx [] (by simp)).2.1 a j
  have hDGamma (a b c j : Fin 3) : |directionalFDeriv (ReferenceDensityBounds.coordinateDirection j)
      (fun y => referenceFrameConnectionCoefficient g L lam y
        (referenceMetricGramFrame g L (lam,y) a) b c) x| ≤ M := by
    simpa only [coordinateFieldWordPartial] using (hm lam hlam x hx [j] (by simp)).2.2.2.1 a b c
  have hDFrameGamma (a z b c : Fin 3) :
      |referenceFrameDerivative g L lam a (fun y => referenceFrameConnectionCoefficient g L lam y
        (referenceMetricGramFrame g L (lam,y) z) b c) x| ≤ 3*M^2 := by
    rw [referenceFrameDerivative_eq_coordinate_sum]
    calc
      _ ≤ ∑ j : Fin 3, |referenceMetricGramFrame g L (lam,x) a j*
          directionalFDeriv (ReferenceDensityBounds.coordinateDirection j) (fun y => referenceFrameConnectionCoefficient g L lam y
            (referenceMetricGramFrame g L (lam,y) z) b c) x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin 3, M*M := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (hFrame a j) (hDGamma z b c j) (abs_nonneg _) hMpos.le
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]; ring
  refine ⟨?_,?_,?_⟩
  · intro a
    have hs := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin 3))) =>
      Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Fin 3))) => hGamma a b c))
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hs
    unfold nativeReferenceConnectionCoefficientMass
    linarith
  · intro a z
    have hs := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin 3))) =>
      Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Fin 3))) => hDFrameGamma a z b c))
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hs
    unfold nativeReferenceConnectionDerivativeMass
    nlinarith [sq_nonneg M]
  · intro a b c
    exact (hGamma a b c).trans hMA

theorem exists_nativeReferenceProfile_uniform_first_second_frame_bounds
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ J : ℝ, 0 < J ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      let beta := actualReferenceBeta g L lam δ R p x
      1 ≤ beta → ∀ a b : Fin 3,
      |referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x| ≤ J*beta ∧
      |referenceFrameDerivative g L lam a
        (referenceFrameDerivative g L lam b (fun y => Real.log (referenceRadius δ R p L y))) x| ≤ J*beta^2 := by
  obtain ⟨J,hJ,hb⟩ := exists_referenceDD_logRadius_frame_uniform_coordinate_word_bounds g hg L hL K hK 0
  refine ⟨J,hJ,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx beta hbeta a b
  have ht := hb lam hlam δ hδ hδ1 R hR p hp x hx hbeta [] (by simp)
  dsimp only [beta]
  constructor
  · simpa only [coordinateFieldWordPartial,List.length_nil,Nat.add_zero,pow_one,actualReferenceBeta] using ht.1 a
  · simpa only [coordinateFieldWordPartial,List.length_nil,Nat.add_zero,referenceFrameDerivative,directionalFDeriv,actualReferenceBeta] using ht.2 a b

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
