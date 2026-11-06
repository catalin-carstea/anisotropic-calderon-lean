import Calderon.ActualFiniteHarmonicModelReferenceWeightedFirstRotation
import Calderon.ActualFiniteHarmonicModelFirstAngularCoefficientJets

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets ActualReferenceDDHigherCLMProducts
  ActualReferenceDDHigherLogFrameJets ActualMixedDensityHigherCoefficientJets
  ActualPhysicalMixedReferenceCancellation NormalizedPrincipalMetric
  CoordinateBootstrapJets ConformalDepth ReferenceWeightedApproximation
  SmoothMetricFrame MovingFrameConnection AmbientReferenceCovariantCore PrincipalCommutator ReferenceDensityBounds

lemma nativeReferenceWeightedFirstRotationCoefficient_eq_connection_sum
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ) (j s t : Fin 3) :
    nativeReferenceWeightedFirstRotationCoefficient g1 L lam δ R p
      (referenceNormalizedPrincipalDifference g1 g2 L lam) j s t =
      fun x => (1/2 : ℝ)*(∑ c : Fin 3, nativeFirstConnectionCoefficient g1 g2 L lam δ R p j c x*
        referenceFrameConnectionCoefficient g1 L lam x (referenceMetricGramFrame g1 L (lam,x) c) s t) := by
  funext x
  simp only [nativeReferenceWeightedFirstRotationCoefficient,nativeFirstConnectionCoefficient,Fin.sum_univ_three]
  ring

theorem exists_nativeWeightedFirst_degree_rotation_uniform_coordinate_word_bounds
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤ eps*referenceRadius δ R p L x →
      referenceRadius δ R p L x*beta^2 ≤ eps →
      ∀ w : List (Fin 3), w.length ≤ 2 → ∀ j s t : Fin 3,
      |coordinateFieldWordPartial w (nativeReferenceWeightedFirstDegreeCoefficient g1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) j) x| ≤ C*referenceRadius δ R p L x*beta^(1+w.length) ∧
      |coordinateFieldWordPartial w (nativeReferenceWeightedFirstRotationCoefficient g1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) j s t) x| ≤ C*referenceRadius δ R p L x*beta^w.length := by
  obtain ⟨J,hJ,hjets⟩ := exists_native_first_angular_coefficients_uniform_coordinate_word_bounds g1 g2 hg1 hg2 L hL K hK
  refine ⟨J+24*J^2,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall w hw j s t
  let r := referenceRadius δ R p L x
  have hr : 0 < r := referenceRadius_pos δ R p L x hδ hR
  have hb0 : 0 ≤ beta := by linarith
  let k (c : Fin 3) := nativeFirstConnectionCoefficient g1 g2 L lam δ R p j c
  let G (c : Fin 3) (y : R3) := referenceFrameConnectionCoefficient g1 L lam y
    (referenceMetricGramFrame g1 L (lam,y) c) s t
  have hkS (c : Fin 3) : ContDiff ℝ ∞ (k c) := contDiff_nativeFirstConnectionCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j c
  have hGS (c : Fin 3) : ContDiff ℝ ∞ (G c) :=
    contDiff_referenceFrameConnectionCoefficient_field g1 hg1 L lam _
      (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam c) s t
  have hkw (c : Fin 3) : HasCoordinateWordJetBound 2 (k c) x (J*r) beta 0 := by
    intro v hv
    simpa only [Real.norm_eq_abs,Nat.zero_add] using
      (hjets lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall v hv j t s c).2.2.2.1
  have hGw (c : Fin 3) : HasCoordinateWordJetBound 2 (G c) x J beta 0 := by
    intro v hv
    simpa only [Real.norm_eq_abs,Nat.zero_add] using
      (hjets lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall v hv j t s c).2.2.2.2.1
  have hprod (c : Fin 3) : HasCoordinateWordJetBound 2 (fun y => k c y*G c y) x (4*J^2*r) beta 0 := by
    have ht := hasCoordinateWordJetBound_mul 2 (k c) (G c) (hkS c) (hGS c) x (J*r) J beta 0 0
      (mul_nonneg hJ.le hr.le) hJ.le hb0 (hkw c) (hGw c)
    convert ht using 1 <;> ring
  have hs : HasCoordinateWordJetBound 2 (fun y => ∑ c : Fin 3, k c y*G c y) x (12*J^2*r) beta 0 := by
    have ht := hasCoordinateWordJetBound_sum 2 (fun c : Fin 3 => fun y => k c y*G c y)
      (fun c => (hkS c).mul (hGS c)) x (4*J^2*r) beta 0 hprod
    simpa only [Fintype.card_fin,Nat.cast_ofNat,show (3:ℝ)*(4*J^2*r)=12*J^2*r by ring] using ht
  have hh : HasCoordinateWordJetBound 2 (fun _ : R3 => (1/2 : ℝ)) x (1/2) beta 0 :=
    hasCoordinateWordJetBound_const 2 (1/2) x (1/2) beta (by norm_num) hb
  have ht := hasCoordinateWordJetBound_mul 2 (fun _ : R3 => (1/2 : ℝ))
    (fun y => ∑ c : Fin 3, k c y*G c y) contDiff_const (ContDiff.sum (fun c _ => (hkS c).mul (hGS c)))
    x (1/2) (12*J^2*r) beta 0 0 (by norm_num) (by positivity) hb0 hh hs
  have htw := ht w hw
  rw [nativeReferenceWeightedFirstRotationCoefficient_eq_connection_sum]
  constructor
  · have hd := (hjets lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall w hw j t s 0).2.2.1
    apply hd.trans
    have hc : J ≤ J+24*J^2 := by nlinarith [sq_nonneg J]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hr.le) (pow_nonneg hb0 _)
  · have htw' : |coordinateFieldWordPartial w (fun y => (1/2 : ℝ)*(∑ c : Fin 3, k c y*G c y)) x| ≤
        (24*J^2*r)*beta^w.length := by
      convert htw using 1 <;> simp only [Real.norm_eq_abs,Nat.zero_add] <;> ring
    apply htw'.trans
    have hc : 24*J^2 ≤ J+24*J^2 := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hr.le) (pow_nonneg hb0 _)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
