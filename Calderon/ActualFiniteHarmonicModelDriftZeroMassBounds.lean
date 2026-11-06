import Calderon.ActualFiniteHarmonicModelDriftZeroRaw
import Calderon.ActualFiniteHarmonicModelConnectionDerivativeMassBounds

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SmoothMetricFrame
  AmbientReferenceRaising ConformalDepth MovingFrameConnection ReferenceWeightedApproximation
  ActualNormalizedSecondMetricDrift ActualReferenceDDHigherGeometryJets

theorem exists_nativeDriftZeroRawMass_uniform_smallness
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta → referenceRadius δ R p L x*beta^2 ≤ eps →
      nativeDriftZeroRawMass g1 g2 L lam δ R p x ≤ C*eps := by
  obtain ⟨A,hA,hconn⟩ := exists_nativeReferenceConnection_uniform_expansion_masses hO hD g1 hg1 L K hK
  obtain ⟨J,hJ,hprof⟩ := exists_nativeReferenceProfile_uniform_first_second_frame_bounds g1 hg1 L hL K hK
  obtain ⟨B,hB,hdrift⟩ := exists_normalizedSecondDrift_uniform_coordinate_word_bounds g1 g2 hg1 hg2 L K hK 0
  have hBpos : 0 < B := by linarith
  refine ⟨3*B*(A+J),by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps x hx beta hb hsmall
  let r := referenceRadius δ R p L x
  have hr : 0 < r := referenceRadius_pos δ R p L x hδ hR
  have hb0 : 0 ≤ beta := by linarith
  have hrb : r*beta ≤ eps := by
    have ht : r*beta ≤ r*beta^2 := mul_le_mul_of_nonneg_left (by nlinarith : beta ≤ beta^2) hr.le
    exact ht.trans hsmall
  have hm (a : Fin 3) : nativeReferenceWeightedZeroRawMass g1 L lam δ R p a x ≤ (A+J)*beta := by
    have ha := (hconn lam hlam x hx).1 a
    have hj := (hprof lam hlam δ hδ hδ1 R hR p hp x hx hb a a).1
    have hab : A ≤ A*beta := le_mul_of_one_le_right hA.le hb
    unfold nativeReferenceWeightedZeroRawMass
    nlinarith
  have hd (a : Fin 3) : |normalizedSecondDriftFrameJoint g1 g2 L a (lam,x)| ≤ B := by
    simpa only [coordinateFieldWordPartial] using (hdrift lam hlam x hx [] (by simp)).2 a
  have hm0 (a : Fin 3) : 0 ≤ nativeReferenceWeightedZeroRawMass g1 L lam δ R p a x := by
    unfold nativeReferenceWeightedZeroRawMass nativeReferenceConnectionCoefficientMass
    positivity
  have ht (a : Fin 3) : |normalizedSecondDriftFrameJoint g1 g2 L a (lam,x)| *
      nativeReferenceWeightedZeroRawMass g1 L lam δ R p a x ≤ B*((A+J)*beta) :=
    mul_le_mul (hd a) (hm a) (hm0 a) hBpos.le
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) => ht a)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hs
  unfold nativeDriftZeroRawMass
  rw [abs_of_pos hr]
  calc
    _ ≤ r*(3*(B*((A+J)*beta))) := mul_le_mul_of_nonneg_left hs hr.le
    _ = (3*B*(A+J))*(r*beta) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hrb (by positivity)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
