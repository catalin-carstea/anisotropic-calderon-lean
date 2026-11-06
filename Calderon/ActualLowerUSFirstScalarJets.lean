import Calderon.ActualFiniteHarmonicModelFirstAngularCoefficientJets
import Calderon.ActualLowerUSWeightedScalarJets

/-! Author GPT-6.1 Sol. Before-code ../full-first-scalar-isolation-upfront-v001.md.
Complete REAL native scalar jets, before any LowMap instance declaration.
No cap callback, limit change, proof admission or compiler call by author. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
open ActualFiniteHarmonicModel ActualNormalizedSecondMetricDrift ActualNormalizedSecondModelErrorAssembly
  ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets
  ActualReferenceDDHigherCLMProducts ActualReferenceDDHigherProfileJets
  ReferenceDensityBounds ReferenceWeightedApproximation ConformalDepth NormalizedPrincipalMetric
  ActualScalarPrincipalAdjoint

/-- The whole original scalar, including the weighted connection contraction. -/
theorem nativeFirstScalarCoefficient_eq_radius_joint_background
    (g g2 : MatrixField) (L q dr Ar : ℝ) (p : ℕ) (j : Fin 3) :
    nativeFirstScalarCoefficient g g2 L q dr Ar p j =
      fun y => referenceRadius dr Ar p L y *
        (normalizedSecondDriftCoordinateJoint g g2 L j (q,y)+
          weightedFirstScalarBackground g g2 L j (q,y)) := by
  calc
    _ = fun y => referenceRadius dr Ar p L y *
        normalizedSecondDriftCoordinateJoint g g2 L j (q,y)+
          nativeReferenceWeightedFirstScalarCoefficient g L q dr Ar p
            (referenceNormalizedPrincipalDifference g g2 L q) j y := by
      funext y
      unfold nativeFirstScalarCoefficient nativeReferenceWeightedFirstScalarCoefficient
      ring
    _ = _ := by
      rw [nativeReferenceWeightedFirstScalarCoefficient_eq_radius_background]
      funext y
      ring

set_option diagnostics true in
/-- Full scalar first words from compact original geometry and radius jets.
One positive constant precedes q, every profile, point and angular size. -/
theorem exists_nativeFirstScalarCoefficient_uniform_word_bound
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (y0 : R3) (rho : ℝ) :
    ∃ CS : ℝ, 0 < CS ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
      ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 1 ≤ p →
      ∀ x ∈ closedBall y0 rho,
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      ∀ j : Fin 3, HasCoordinateWordJetBound 1
        (nativeFirstScalarCoefficient g g2 L q dr Ar p j) x
        (CS*referenceRadius dr Ar p L x) (actualReferenceBeta g L q dr Ar p x) 0 := by
  let K := closedBall y0 rho
  have hK : IsCompact K := isCompact_closedBall _ _
  let bg : Fin 3 → ℝ × R3 → ℝ := fun j z =>
    normalizedSecondDriftCoordinateJoint g g2 L j z+weightedFirstScalarBackground g g2 L j z
  have hBgSmooth (j : Fin 3) : ContDiff ℝ ∞ (bg j) :=
    (contDiff_normalizedSecondDriftCoordinateJoint g g2 hg hg2 L j).add
      (contDiff_weightedFirstScalarBackground g g2 hg hg2 L j)
  obtain ⟨M,hM,hBg⟩ := exists_parameter_coordinate_word_uniform_bound bg hBgSmooth K hK 1
  obtain ⟨Cr,hCr,hRadius⟩ := exists_referenceRadius_uniform_coordinate_word_bounds g hg L hL K hK 1
  let CS : ℝ := 2*Cr*M
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hCS : 0 < CS := by dsimp only [CS]; positivity
  refine ⟨CS,hCS,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp x hx hb j
  let r := referenceRadius dr Ar p L x
  let beta := actualReferenceBeta g L q dr Ar p x
  let rr := referenceRadius dr Ar p L
  let bj := fun y : R3 => bg j (q,y)
  have hr : 0 < r := referenceRadius_pos dr Ar p L x hdr hAr
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hrrS : ContDiff ℝ ∞ rr := contDiff_referenceRadius_actual dr Ar p L hdr hAr
  have hbjS : ContDiff ℝ ∞ bj := (hBgSmooth j).comp (contDiff_const.prodMk contDiff_id)
  have hBj : HasCoordinateWordJetBound 1 bj x M beta 0 := by
    intro word hw
    exact (hBg q hq x hx j word hw).trans
      (by simpa only [Nat.zero_add] using
        le_mul_of_one_le_right hM0 (one_le_pow₀ hb (n := word.length)))
  have hRj : HasCoordinateWordJetBound 1 rr x (Cr*r) beta 0 := by
    intro word hw
    simpa only [Real.norm_eq_abs,Nat.zero_add,mul_assoc,rr,r,beta,actualReferenceBeta] using
      (hRadius q hq dr hdr hdr1 Ar hAr p hp x hx word hw).1
  rw [nativeFirstScalarCoefficient_eq_radius_joint_background]
  have ht := hasCoordinateWordJetBound_mul 1 rr bj hrrS hbjS x (Cr*r) M beta 0 0
    (by positivity) hM0 hb0 hRj hBj
  convert ht using 1 <;> dsimp only [CS] <;> ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
