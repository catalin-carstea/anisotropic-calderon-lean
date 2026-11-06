import Calderon.ActualFiniteHarmonicModelBZSecondAngular
import Calderon.ActualFiniteHarmonicModelFirstNormalizedBounds
import Calderon.ActualReferenceDDHigherCLMProducts

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore BoundedAngularShift
  ActualNormalizedSecondModelCoefficients ActualReferenceDDHigherLogFrameJets
  AmbientReferenceRaising ReferenceWeightedApproximation NormalizedPrincipalMetric
  ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets
  ActualReferenceDDHigherCLMProducts ReferenceDensityBounds PrincipalCommutator
  ConformalDepth SmoothMetricFrame MovingFrameConnection CoordinateBootstrapJets
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

lemma contDiff_nativeReferenceDefectSecondAngularCoefficient
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) :
    ContDiff ℝ ∞ (nativeReferenceDefectSecondAngularCoefficient hO hD hF g L lam δ R p) := by
  let f (a : Fin 3) : R3 → ℝ :=
    referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y))
  have hf (a : Fin 3) : ContDiff ℝ ∞ (f a) :=
    contDiff_referenceFrameDerivative g hg L lam a _
      (contDiff_log_referenceRadius_profile δ R L p hδ hR)
  unfold nativeReferenceDefectSecondAngularCoefficient
  exact ContDiff.sum (fun a _ => (hf a).smul contDiff_const)

theorem exists_nativeReferenceDefectSecondAngularCoefficient_uniform_coordinate_word_bounds
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ x ∈ K, let beta := actualReferenceBeta g L lam δ R p x
      1 ≤ beta → ∀ w : List (Fin 3), w.length ≤ 2 →
      ‖coordinateFieldWordPartial w
        (nativeReferenceDefectSecondAngularCoefficient hO hD hF g L lam δ R p) x‖ ≤
          C * beta^(1+w.length) := by
  obtain ⟨J,hJ,hLog⟩ := exists_referenceDD_logRadius_frame_uniform_coordinate_word_bounds
    g hg L hL K hK 2
  let T (a : Fin 3) : SphereL2 →L[ℝ] SphereL2 :=
    (normalizedDerivative hF hO hD a).comp
      (ContinuousLinearMap.id ℝ SphereL2-inverseDegreeMultiplier hO hD)
  let M : ℝ := 1+∑ a : Fin 3, ‖T a‖
  let C : ℝ := 12*J*M
  have hM : 0 < M := by
    dsimp only [M]
    have ht : 0 ≤ ∑ a : Fin 3, ‖T a‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    linarith
  have hC : 0 < C := by dsimp only [C]; positivity
  have hT (a : Fin 3) : ‖T a‖ ≤ M := by
    have ht := Finset.single_le_sum (fun b _ => norm_nonneg (T b)) (Finset.mem_univ a)
    dsimp only [M]
    linarith
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx beta hb w hw
  have hb0 : 0 ≤ beta := le_trans zero_le_one hb
  let f (a : Fin 3) : R3 → ℝ :=
    referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y))
  have hfS (a : Fin 3) : ContDiff ℝ ∞ (f a) :=
    contDiff_referenceFrameDerivative g hg L lam a _
      (contDiff_log_referenceRadius_profile δ R L p hδ hR)
  have hfJ (a : Fin 3) : HasCoordinateWordJetBound 2 (f a) x J beta 1 := by
    intro v hv
    simpa only [Real.norm_eq_abs,f,beta,actualReferenceBeta] using
      (hLog lam hlam δ hδ hδ1 R hR p hp x hx hb v hv).1 a
  have hconstJ (a : Fin 3) : HasCoordinateWordJetBound 2
      (fun _ : R3 => T a) x M beta 0 :=
    hasCoordinateWordJetBound_const_normed 2 _ x M beta (hT a) hb0
  have hterm (a : Fin 3) : HasCoordinateWordJetBound 2
      (fun y => f a y • T a) x (4*J*M) beta 1 := by
    have ht := hasCoordinateWordJetBound_smul 2 (f a) (fun _ : R3 => T a)
      (hfS a) contDiff_const x J M beta 1 0 hJ.le hM.le hb0 (hfJ a) (hconstJ a)
    convert ht using 1 <;> norm_num
  have hsum := hasCoordinateWordJetBound_sum 2 (fun a y => f a y • T a)
    (fun a => (hfS a).smul contDiff_const) x (4*J*M) beta 1 hterm
  have hsum' : HasCoordinateWordJetBound 2
      (nativeReferenceDefectSecondAngularCoefficient hO hD hF g L lam δ R p)
      x C beta 1 := by
    convert hsum using 1 <;>
      first | rfl | (dsimp [C] <;> norm_num <;> ring)
  simpa only [Nat.add_comm] using hsum' w hw

theorem exists_nativeBZSecondAngularCoefficient_uniform_coordinate_word_smallness
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x →
      referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ j : Fin 3, ∀ w : List (Fin 3), w.length ≤ 2 →
      ‖coordinateFieldWordPartial w
        (fun y => (modelFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j y).comp
          (nativeReferenceDefectSecondAngularCoefficient hO hD hF g1 L lam δ R p y)) x‖ ≤
          (C * eps) * beta^w.length := by
  obtain ⟨CB,hCB,hB⟩ := exists_modelFirstNormalizedCoefficient_uniform_coordinate_word_smallness
    hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CZ,hCZ,hZ⟩ := exists_nativeReferenceDefectSecondAngularCoefficient_uniform_coordinate_word_bounds
    hO hD hF g1 hg1 L hL K hK
  let C : ℝ := 4*CB*CZ
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall j w hw
  have hbpos : 0 < beta := lt_of_lt_of_le zero_lt_one hb
  have hb0 : 0 ≤ beta := hbpos.le
  let B : R3 → SphereL2 →L[ℝ] SphereL2 :=
    modelFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j
  let Z : R3 → SphereL2 →L[ℝ] SphereL2 :=
    nativeReferenceDefectSecondAngularCoefficient hO hD hF g1 L lam δ R p
  have hBS : ContDiff ℝ ∞ B :=
    contDiff_modelFirstNormalizedCoefficient hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR
  have hZS : ContDiff ℝ ∞ Z :=
    contDiff_nativeReferenceDefectSecondAngularCoefficient hO hD hF g1 hg1
      L lam δ R p hδ hR
  have hBj : HasCoordinateWordJetBound 2 B x (CB*eps/beta) beta 0 := by
    intro v hv
    simpa only [B,beta,actualReferenceBeta,Nat.zero_add] using
      hB lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall j v hv
  have hZj : HasCoordinateWordJetBound 2 Z x CZ beta 1 := by
    intro v hv
    simpa only [Z,beta,actualReferenceBeta] using
      hZ lam hlam δ hδ hδ1 R hR p hp x hx hb v hv
  have hrate : 0 ≤ CB*eps/beta := div_nonneg (mul_nonneg hCB.le heps) hb0
  have hcomp := hasCoordinateWordJetBound_clm_comp 2 B Z hBS hZS x
    (CB*eps/beta) CZ beta 0 1 hrate hCZ.le hb0 hBj hZj
  have ht := hcomp w hw
  calc
    ‖coordinateFieldWordPartial w (fun y => (B y).comp (Z y)) x‖ ≤
        ((2:ℝ)^2*(CB*eps/beta)*CZ)*beta^(0+1+w.length) := ht
    _ = (C*eps)*beta^w.length := by
      simp only [Nat.zero_add,pow_add,pow_one,C]
      field_simp [ne_of_gt hbpos]
      ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
