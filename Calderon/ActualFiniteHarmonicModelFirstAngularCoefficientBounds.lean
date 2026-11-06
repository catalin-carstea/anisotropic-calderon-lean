import Calderon.ActualFiniteHarmonicModelFirstAngularCoefficients
import Calderon.ActualReferenceDDHigherLogFrameJets
import Calderon.ActualMixedDensityHigherCoefficientJets

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherLogFrameJets
  ActualMixedDensityHigherCoefficientJets ActualPhysicalMixedFirst ActualPhysicalMixedNative
  ActualPhysicalMixedReferenceCancellation ActualNormalizedSecondModelErrorAssembly
  CoordinateBootstrapJets ConformalDepth ReferenceWeightedApproximation MetricOperator SmoothMetricFrame MovingFrameConnection
  AmbientReferenceRaising ReferenceDensityBounds NormalizedPrincipalMetric
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
theorem exists_native_first_angular_coefficients_uniform_bounds
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x →
      referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ j a b c : Fin 3,
      |physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x| ≤
        C * eps * referenceRadius δ R p L x ∧
      |nativeFirstDegreeCoefficient g1 g2 L lam δ R p j x| ≤
        C * referenceRadius δ R p L x * beta ∧
      |nativeFirstConnectionCoefficient g1 g2 L lam δ R p j c x| ≤
        C * referenceRadius δ R p L x ∧
      |referenceFrameConnectionCoefficient g1 L lam x (referenceMetricGramFrame g1 L (lam,x) c) b a| ≤ C := by
  obtain ⟨MF,hMF,hbackground⟩ := exists_mixed_background_coordinate_jet_bound g1 hg1 L K hK 0
  obtain ⟨MG,hMG,hframeGamma⟩ := exists_parameter_coordinate_word_uniform_bound
    (fun t : Fin 3 × Fin 3 × Fin 3 => fun z : ℝ × R3 => ActualHorizontalNormBridge.referenceFrameConnectionJoint g1 L
      (fun q : ℝ × R3 => referenceMetricGramFrame g1 L q t.1) z t.2.1 t.2.2)
    (fun t => ActualHorizontalNormBridge.contDiff_referenceFrameConnectionJoint g1 hg1 L
      (fun q : ℝ × R3 => referenceMetricGramFrame g1 L q t.1)
      (contDiff_referenceMetricGramFrame g1 hg1 L t.1) t.2.1 t.2.2) K hK 0
  let M : ℝ := MF+MG
  have hM : 1 ≤ M := by dsimp only [M]; linarith
  have hMFM : MF ≤ M := by dsimp only [M]; linarith
  have hMGM : MG ≤ M := by dsimp only [M]; linarith
  obtain ⟨J,hJ,hprofile⟩ := exists_referenceDD_logRadius_frame_uniform_coordinate_word_bounds g1 hg1 L hL K hK 0
  let C : ℝ := 1+6*M+180*J*M^3+60*M^3+M
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hM3 : 0 ≤ M^3 := pow_nonneg hM0 _
  have hJM3 : 0 ≤ J*M^3 := mul_nonneg hJ.le hM3
  have hCM : M ≤ C := by dsimp only [C]; nlinarith
  have hCmC : 6*M ≤ C := by dsimp only [C]; nlinarith
  have hCdC : 180*J*M^3 ≤ C := by dsimp only [C]; nlinarith
  have hCkC : 60*M^3 ≤ C := by dsimp only [C]; nlinarith
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall j a b c
  let r := referenceRadius δ R p L x
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  have hr : 0 < r := referenceRadius_pos δ R p L x hδ hR
  have hb0 : 0 ≤ beta := le_trans zero_le_one hb
  have hr1 : r ≤ 1 := by
    change r*beta^2 ≤ eps at hsmall
    have hpow : 1 ≤ beta^2 := one_le_pow₀ hb
    have ht : r ≤ r*beta^2 := le_mul_of_one_le_right hr.le hpow
    exact (ht.trans hsmall).trans heps1
  have her1 : eps*r ≤ 1 := by nlinarith
  have hbg := hbackground lam hlam x hx
  have hE (i k : Fin 3) : |referenceMetricGramFrame g1 L (lam,x) i k| ≤ M := by
    have ht : |referenceMetricGramFrame g1 L (lam,x) i k| ≤ MF := by
      simpa only [coordinateFieldWordPartial] using hbg.1 [] (by simp) i k
    exact ht.trans hMFM
  have hCo (i k : Fin 3) : |ActualHorizontalNormBridge.referenceCoFrameEntry g1 L i k (lam,x)| ≤ M := by
    have ht : |ActualHorizontalNormBridge.referenceCoFrameEntry g1 L i k (lam,x)| ≤ MF := by
      simpa only [coordinateFieldWordPartial] using hbg.2.1 [] (by simp) i k
    exact ht.trans hMFM
  have hGamma (i k l : Fin 3) : |referenceFrameConnectionCoefficient g1 L lam x
      (referenceMetricGramFrame g1 L (lam,x) i) k l| ≤ M := by
    have ht := hframeGamma lam hlam x hx (i,k,l) [] (by simp)
    have hgm : |referenceFrameConnectionCoefficient g1 L lam x
        (referenceMetricGramFrame g1 L (lam,x) i) k l| ≤ MG := by
      simpa only [coordinateFieldWordPartial,ActualHorizontalNormBridge.referenceFrameConnectionJoint_eq g1 hg1 L,Real.norm_eq_abs] using ht
    exact hgm.trans hMGM
  have hLog (i : Fin 3) : |referenceFrameDerivative g1 L lam i
      (fun y => Real.log (referenceRadius δ R p L y)) x| ≤ J*beta := by
    have ht := (hprofile lam hlam δ hδ hδ1 R hR p hp x hx hb [] (by simp)).1 i
    simpa only [coordinateFieldWordPartial,List.length_nil,Nat.add_zero,pow_one,beta,actualReferenceBeta] using ht
  have hEntryDifference (i k : Fin 3) : |h x i k| ≤ eps*r := by
    have ht := abs_actual_h_coordinateFieldWordPartial_le_of_H8 g1 g2 hg1 hg2 L lam x
      (eps*r) hH8 [] (by simp) i k
    simpa only [coordinateFieldWordPartial,h,r] using ht
  have hsum (f : Fin 3 → Fin 3 → ℝ) : |∑ i : Fin 3, ∑ k : Fin 3, f i k| ≤
      ∑ i : Fin 3, ∑ k : Fin 3, |f i k| :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
  have hQ (i k : Fin 3) : |physicalMixedQFrameCoefficient g1 L lam h i k x| ≤ 10*M^2 := by
    have hprod (s t : Fin 3) : |h x s t*ActualHorizontalNormBridge.referenceCoFrameEntry g1 L s i (lam,x)*
        ActualHorizontalNormBridge.referenceCoFrameEntry g1 L t k (lam,x)| ≤ eps*r*M^2 := by
      rw [abs_mul,abs_mul]
      calc
        _ ≤ (eps*r*M)*M := mul_le_mul
          (mul_le_mul (hEntryDifference s t) (hCo s i) (abs_nonneg _) (mul_nonneg heps hr.le))
          (hCo t k) (abs_nonneg _) (mul_nonneg (mul_nonneg heps hr.le) hM0)
        _ = _ := by ring
    have hmixed : |physicalMixedFrameCoefficient g1 L lam h i k x| ≤ 9*eps*r*M^2 := by
      unfold physicalMixedFrameCoefficient
      calc
        _ ≤ ∑ s : Fin 3, ∑ t : Fin 3,
          |h x s t*ActualHorizontalNormBridge.referenceCoFrameEntry g1 L s i (lam,x)*ActualHorizontalNormBridge.referenceCoFrameEntry g1 L t k (lam,x)| := hsum _
        _ ≤ ∑ s : Fin 3, ∑ t : Fin 3, eps*r*M^2 :=
          Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun t _ => hprod s t))
        _ = _ := by simp only [Fin.sum_univ_three]; ring
    rw [physicalMixedQFrameCoefficient_decomposition g1 hg1 L lam h i k x]
    have hdelta : |if i=k then (1 : ℝ) else 0| ≤ 1 := by split_ifs <;> norm_num
    have hMsq : 1 ≤ M^2 := one_le_pow₀ hM
    have hscale : eps*r*M^2 ≤ M^2 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right her1 (sq_nonneg M)
    calc
      _ ≤ |if i=k then (1 : ℝ) else 0|+|physicalMixedFrameCoefficient g1 L lam h i k x| := abs_add_le _ _
      _ ≤ 1+9*eps*r*M^2 := add_le_add hdelta hmixed
      _ ≤ 10*M^2 := by nlinarith
  have hmixedFirst (i k : Fin 3) : |physicalMixedFirstCoefficient g1 L lam h i k x| ≤ 6*M*eps*r :=
    physicalMixedFirstCoefficient_bound g1 L lam h x eps r M heps hr.le hM0 hEntryDifference hCo i k
  have hEta (i k : Fin 3) :
      |referenceFrameDerivative g1 L lam k (fun y => Real.log (referenceRadius δ R p L y)) x *
          referenceMetricGramFrame g1 L (lam,x) i j +
        referenceFrameDerivative g1 L lam i (fun y => Real.log (referenceRadius δ R p L y)) x *
          referenceMetricGramFrame g1 L (lam,x) k j| ≤ 2*J*M*beta := by
    calc
      _ ≤ |referenceFrameDerivative g1 L lam k (fun y => Real.log (referenceRadius δ R p L y)) x *
          referenceMetricGramFrame g1 L (lam,x) i j| +
        |referenceFrameDerivative g1 L lam i (fun y => Real.log (referenceRadius δ R p L y)) x *
          referenceMetricGramFrame g1 L (lam,x) k j| := abs_add_le _ _
      _ ≤ (J*beta)*M+(J*beta)*M := add_le_add
        (by rw [abs_mul]; exact mul_le_mul (hLog k) (hE i j) (abs_nonneg _) (mul_nonneg hJ.le hb0))
        (by rw [abs_mul]; exact mul_le_mul (hLog i) (hE k j) (abs_nonneg _) (mul_nonneg hJ.le hb0))
      _ = _ := by ring
  have hd : |nativeFirstDegreeCoefficient g1 g2 L lam δ R p j x| ≤ (180*J*M^3)*r*beta := by
    unfold nativeFirstDegreeCoefficient
    rw [abs_mul,abs_of_pos hr]
    calc
      _ ≤ r*(∑ i : Fin 3, ∑ k : Fin 3, |physicalMixedQFrameCoefficient g1 L lam h i k x *
        (referenceFrameDerivative g1 L lam k (fun y => Real.log (referenceRadius δ R p L y)) x *
          referenceMetricGramFrame g1 L (lam,x) i j +
          referenceFrameDerivative g1 L lam i (fun y => Real.log (referenceRadius δ R p L y)) x *
          referenceMetricGramFrame g1 L (lam,x) k j)|) := mul_le_mul_of_nonneg_left (hsum _) hr.le
      _ ≤ r*(∑ i : Fin 3, ∑ k : Fin 3, (10*M^2)*(2*J*M*beta)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun k _ => by
          rw [abs_mul]
          exact mul_le_mul (hQ i k) (hEta i k) (abs_nonneg _) (by positivity)))) hr.le
      _ = _ := by simp only [Fin.sum_univ_three]; ring
  have hk : |nativeFirstConnectionCoefficient g1 g2 L lam δ R p j c x| ≤ (60*M^3)*r := by
    unfold nativeFirstConnectionCoefficient
    rw [abs_mul,abs_of_pos hr]
    have hprod1 (i : Fin 3) : |physicalMixedQFrameCoefficient g1 L lam h i c x *
        referenceMetricGramFrame g1 L (lam,x) i j| ≤ (10*M^2)*M := by
      rw [abs_mul]; exact mul_le_mul (hQ i c) (hE i j) (abs_nonneg _) (by positivity)
    have hprod2 (i : Fin 3) : |physicalMixedQFrameCoefficient g1 L lam h c i x *
        referenceMetricGramFrame g1 L (lam,x) i j| ≤ (10*M^2)*M := by
      rw [abs_mul]; exact mul_le_mul (hQ c i) (hE i j) (abs_nonneg _) (by positivity)
    calc
      _ ≤ r*((∑ i : Fin 3, |physicalMixedQFrameCoefficient g1 L lam h i c x * referenceMetricGramFrame g1 L (lam,x) i j|)+
          (∑ i : Fin 3, |physicalMixedQFrameCoefficient g1 L lam h c i x * referenceMetricGramFrame g1 L (lam,x) i j|)) :=
        mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans
          (add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _))) hr.le
      _ ≤ r*((∑ i : Fin 3, (10*M^2)*M)+(∑ i : Fin 3, (10*M^2)*M)) :=
        mul_le_mul_of_nonneg_left (add_le_add (Finset.sum_le_sum (fun i _ => hprod1 i))
          (Finset.sum_le_sum (fun i _ => hprod2 i))) hr.le
      _ = _ := by simp only [Fin.sum_univ_three]; ring
  refine ⟨?_,?_,?_,(hGamma c b a).trans hCM⟩
  · exact (hmixedFirst a j).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCmC heps) hr.le)
  · exact hd.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCdC hr.le) hb0)
  · exact hk.trans (mul_le_mul_of_nonneg_right hCkC hr.le)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
