import Calderon.ActualNormalizedSecondMixedWeakPairing
import Calderon.ActualReferenceDDHigherGeometryJets

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualMixedDensityCoefficientJets
open SphereHarmonic SphereHilbertDecomposition SmoothSphereFields SmoothAngularApplication
  SmoothMetricFrame ReferenceDensityBounds PrincipalCommutator PerturbedDensityAdjoint
  ActualPhysicalMixedFirst ActualHorizontalNormBridge ActualReferenceDDHigherGeometryJets
  ActualNormalizedSecondModelErrorAssembly NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  ActualNormalizedSecondMixedCommutatorForm ActualNormalizedSecondMixedWeakPairing

/-- All actual compact background coefficients needed by this one differentiated word. -/
def MixedBackgroundFirstJetBound (g : MatrixField) (L lam : ℝ) (x : R3) (M : ℝ) : Prop :=
  (∀ a i : Fin 3, |referenceMetricGramFrame g L (lam,x) a i| ≤ M) ∧
  (∀ k a i : Fin 3, |directionalFDeriv (coordinateDirection k)
    (fun y => referenceMetricGramFrame g L (lam,y) a i) x| ≤ M) ∧
  (∀ u a : Fin 3, |referenceCoFrameEntry g L u a (lam,x)| ≤ M) ∧
  (∀ k u a : Fin 3, |directionalFDeriv (coordinateDirection k)
    (fun y => referenceCoFrameEntry g L u a (lam,y)) x| ≤ M) ∧
  (∀ k : Fin 3, |(referenceDensityFamily g L (lam,x))⁻¹ *
    directionalFDeriv (coordinateDirection k) (fun y => referenceDensityFamily g L (lam,y)) x| ≤ M)

/-- Literal first coordinate jets of actual normalized h, with the source weighted r budget.
This is not asserted from admissibility; the fixed-lambda application witness is open. -/
def MixedMetricFirstJetBound (g1 g2 : MatrixField) (L lam : ℝ)
    (x : R3) (eps radius : ℝ) : Prop :=
  (∀ u v : Fin 3, |referenceNormalizedPrincipalDifference g1 g2 L lam x u v| ≤ eps*radius) ∧
  (∀ k u v : Fin 3, |directionalFDeriv (coordinateDirection k)
    (fun y => referenceNormalizedPrincipalDifference g1 g2 L lam y u v) x| ≤ eps*radius)

/-- The coefficient of the retained weak derivative remainder, with actual density. -/
def mixedDensityDerivativeCoefficient (g1 g2 : MatrixField) (L lam : ℝ)
    (k i j a b : Fin 3) (x : R3) : ℝ :=
  (referenceDensityFamily g1 L (lam,x))⁻¹ * directionalFDeriv (coordinateDirection k)
    (fun y => referenceDensityFamily g1 L (lam,y)*mixedSecondWordCoefficient g1 g2 L lam i j a b y) x

lemma physicalMixedFirstCoefficient_directional_eq
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) (k a j : Fin 3) (x : R3) :
    directionalFDeriv (coordinateDirection k)
      (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j) x =
    2*∑ u : Fin 3,
      (directionalFDeriv (coordinateDirection k)
        (fun y => referenceNormalizedPrincipalDifference g1 g2 L lam y u j) x *
        referenceCoFrameEntry g1 L u a (lam,x) +
      referenceNormalizedPrincipalDifference g1 g2 L lam x u j *
        directionalFDeriv (coordinateDirection k) (fun y => referenceCoFrameEntry g1 L u a (lam,y)) x) := by
  have hh (u v : Fin 3) := contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam u v
  have hd (u : Fin 3) : ContDiff ℝ ∞ (fun y => referenceCoFrameEntry g1 L u a (lam,y)) :=
    (contDiff_referenceCoFrameEntry g1 hg1 L u a).comp (contDiff_const.prodMk contDiff_id)
  have ht (u : Fin 3) := (hh u j).mul (hd u)
  have hsum : directionalFDeriv (coordinateDirection k)
      (fun y => ∑ u : Fin 3, referenceNormalizedPrincipalDifference g1 g2 L lam y u j *
        referenceCoFrameEntry g1 L u a (lam,y)) x =
      ∑ u : Fin 3, directionalFDeriv (coordinateDirection k)
        (fun y => referenceNormalizedPrincipalDifference g1 g2 L lam y u j *
          referenceCoFrameEntry g1 L u a (lam,y)) x := by
    unfold directionalFDeriv
    rw [fderiv_fun_sum (fun u _ => (ht u).differentiable (by simp) x)]
    simp only [ContinuousLinearMap.sum_apply]
  have htwo (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) :
      directionalFDeriv (coordinateDirection k) (fun y => 2*f y) x =
        2*directionalFDeriv (coordinateDirection k) f x := by
    have h := directional_mul (coordinateDirection k) (fun _ : R3 => (2 : ℝ)) f contDiff_const hf x
    simpa only [directionalFDeriv,fderiv_const_apply,ContinuousLinearMap.zero_apply,zero_mul,zero_add] using h
  unfold physicalMixedFirstCoefficient
  rw [htwo _ (ContDiff.sum (fun u _ => ht u)),hsum]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  exact directional_mul (coordinateDirection k) _ _ (hh u j) (hd u) x

lemma abs_physicalMixedFirstCoefficient_directional_le
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) (x : R3) (eps radius M : ℝ)
    (heps : 0 ≤ eps) (hradius : 0 ≤ radius) (hM : 0 ≤ M)
    (hgeom : MixedBackgroundFirstJetBound g1 L lam x M)
    (hh : MixedMetricFirstJetBound g1 g2 L lam x eps radius) (k a j : Fin 3) :
    |directionalFDeriv (coordinateDirection k)
      (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j) x| ≤
      12*M*eps*radius := by
  have ht (u : Fin 3) :
      |directionalFDeriv (coordinateDirection k)
        (fun y => referenceNormalizedPrincipalDifference g1 g2 L lam y u j) x *
        referenceCoFrameEntry g1 L u a (lam,x) +
      referenceNormalizedPrincipalDifference g1 g2 L lam x u j *
        directionalFDeriv (coordinateDirection k) (fun y => referenceCoFrameEntry g1 L u a (lam,y)) x| ≤
      2*M*eps*radius := by
    calc
      _ ≤ |directionalFDeriv (coordinateDirection k)
          (fun y => referenceNormalizedPrincipalDifference g1 g2 L lam y u j) x *
          referenceCoFrameEntry g1 L u a (lam,x)| +
          |referenceNormalizedPrincipalDifference g1 g2 L lam x u j *
            directionalFDeriv (coordinateDirection k) (fun y => referenceCoFrameEntry g1 L u a (lam,y)) x| := abs_add_le _ _
      _ ≤ (eps*radius)*M+(eps*radius)*M := by
        simp only [abs_mul]
        exact add_le_add
          (mul_le_mul (hh.2 k u j) (hgeom.2.2.1 u a) (abs_nonneg _) (mul_nonneg heps hradius))
          (mul_le_mul (hh.1 u j) (hgeom.2.2.2.1 k u a) (abs_nonneg _) (mul_nonneg heps hradius))
      _ = _ := by ring
  rw [physicalMixedFirstCoefficient_directional_eq g1 g2 hg1 hg2 L lam k a j x,abs_mul]
  rw [show |(2 : ℝ)|=2 by norm_num]
  calc
    _ ≤ 2*∑ u : Fin 3, |directionalFDeriv (coordinateDirection k)
          (fun y => referenceNormalizedPrincipalDifference g1 g2 L lam y u j) x *
          referenceCoFrameEntry g1 L u a (lam,x) +
        referenceNormalizedPrincipalDifference g1 g2 L lam x u j *
          directionalFDeriv (coordinateDirection k) (fun y => referenceCoFrameEntry g1 L u a (lam,y)) x| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ 2*∑ _u : Fin 3, 2*M*eps*radius :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun u _ => ht u)) (by norm_num)
    _ = _ := by simp only [Fin.sum_univ_three]; ring

lemma mixedSecondWordCoefficient_directional_eq
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) (k i j a b : Fin 3) (x : R3) :
    let ea : R3 → ℝ := fun y => referenceMetricGramFrame g1 L (lam,y) a i
    let eb : R3 → ℝ := fun y => referenceMetricGramFrame g1 L (lam,y) b j
    let ma := physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a i
    let mb := physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) b j
    directionalFDeriv (coordinateDirection k) (mixedSecondWordCoefficient g1 g2 L lam i j a b) x =
      (2*directionalFDeriv (coordinateDirection k) ea x+directionalFDeriv (coordinateDirection k) ma x)*mb x +
      (2*ea x+ma x)*directionalFDeriv (coordinateDirection k) mb x +
      2*directionalFDeriv (coordinateDirection k) ma x*eb x +
      2*ma x*directionalFDeriv (coordinateDirection k) eb x := by
  dsimp only
  let ea : R3 → ℝ := fun y => referenceMetricGramFrame g1 L (lam,y) a i
  let eb : R3 → ℝ := fun y => referenceMetricGramFrame g1 L (lam,y) b j
  let ma := physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a i
  let mb := physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) b j
  have he (a i : Fin 3) : ContDiff ℝ ∞ (fun y => referenceMetricGramFrame g1 L (lam,y) a i) :=
    (contDiff_piLp_apply (p := 2) (i := i) : ContDiff ℝ ∞ (fun v : R3 => v i)).comp
      (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam a)
  have hm (a i : Fin 3) := contDiff_physicalMixedFirstCoefficient g1 hg1 L lam
    (referenceNormalizedPrincipalDifference g1 g2 L lam)
    (fun u v => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam u v) a i
  have h2 (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) :
      directionalFDeriv (coordinateDirection k) (fun y => 2*f y) x =
        2*directionalFDeriv (coordinateDirection k) f x := by
    have h := directional_mul (coordinateDirection k) (fun _ : R3 => (2 : ℝ)) f contDiff_const hf x
    simpa only [directionalFDeriv,fderiv_const_apply,ContinuousLinearMap.zero_apply,zero_mul,zero_add] using h
  change directionalFDeriv (coordinateDirection k) (fun y => (2*ea y+ma y)*mb y+2*ma y*eb y) x = _
  rw [directionalFDeriv_add (coordinateDirection k) _ _
    (((contDiff_const.mul (he a i)).add (hm a i)).mul (hm b j))
    ((contDiff_const.mul (hm a i)).mul (he b j)) x,
    directional_mul (coordinateDirection k) _ _ ((contDiff_const.mul (he a i)).add (hm a i)) (hm b j) x,
    directional_mul (coordinateDirection k) _ _ (contDiff_const.mul (hm a i)) (he b j) x,
    directionalFDeriv_add (coordinateDirection k) _ _ (contDiff_const.mul (he a i)) (hm a i) x,
    h2 ea (he a i),h2 ma (hm a i)]
  dsimp [ea,eb,ma,mb]
  ring

lemma abs_mixedSecondWordCoefficient_directional_le
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) (x : R3) (eps radius M : ℝ)
    (heps : 0 ≤ eps) (hradius : 0 ≤ radius) (hM : 0 ≤ M)
    (hgeom : MixedBackgroundFirstJetBound g1 L lam x M)
    (hh : MixedMetricFirstJetBound g1 g2 L lam x eps radius) (k i j a b : Fin 3) :
    |directionalFDeriv (coordinateDirection k) (mixedSecondWordCoefficient g1 g2 L lam i j a b) x| ≤
      72*M^2*eps*radius+144*M^2*eps^2*radius^2 := by
  let ma : R3 → ℝ := physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a i
  let mb : R3 → ℝ := physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) b j
  let ea : R3 → ℝ := fun y => referenceMetricGramFrame g1 L (lam,y) a i
  let eb : R3 → ℝ := fun y => referenceMetricGramFrame g1 L (lam,y) b j
  let dma := directionalFDeriv (coordinateDirection k) ma x
  let dmb := directionalFDeriv (coordinateDirection k) mb x
  let dea := directionalFDeriv (coordinateDirection k) ea x
  let deb := directionalFDeriv (coordinateDirection k) eb x
  have hma : |ma x| ≤ 6*M*eps*radius :=
    physicalMixedFirstCoefficient_bound g1 L lam _ x eps radius M heps hradius hM hh.1 hgeom.2.2.1 a i
  have hmb : |mb x| ≤ 6*M*eps*radius :=
    physicalMixedFirstCoefficient_bound g1 L lam _ x eps radius M heps hradius hM hh.1 hgeom.2.2.1 b j
  have hdma : |dma| ≤ 12*M*eps*radius :=
    abs_physicalMixedFirstCoefficient_directional_le g1 g2 hg1 hg2 L lam x eps radius M heps hradius hM hgeom hh k a i
  have hdmb : |dmb| ≤ 12*M*eps*radius :=
    abs_physicalMixedFirstCoefficient_directional_le g1 g2 hg1 hg2 L lam x eps radius M heps hradius hM hgeom hh k b j
  have hea : |ea x| ≤ M := hgeom.1 a i
  have heb : |eb x| ≤ M := hgeom.1 b j
  have hdea : |dea| ≤ M := hgeom.2.1 k a i
  have hdeb : |deb| ≤ M := hgeom.2.1 k b j
  have hlinD : |2*dea+dma| ≤ 2*M+12*M*eps*radius := by
    have h := abs_add_le (2*dea) dma
    rw [abs_mul] at h
    norm_num at h
    nlinarith only [h,hdea,hdma]
  have hlinV : |2*ea x+ma x| ≤ 2*M+6*M*eps*radius := by
    have h := abs_add_le (2*ea x) (ma x)
    rw [abs_mul] at h
    norm_num at h
    nlinarith only [h,hea,hma]
  have h1 : |(2*dea+dma)*mb x| ≤ (2*M+12*M*eps*radius)*(6*M*eps*radius) := by
    rw [abs_mul]
    exact mul_le_mul hlinD hmb (abs_nonneg _) (by positivity)
  have h2 : |(2*ea x+ma x)*dmb| ≤ (2*M+6*M*eps*radius)*(12*M*eps*radius) := by
    rw [abs_mul]
    exact mul_le_mul hlinV hdmb (abs_nonneg _) (by positivity)
  have h3 : |2*dma*eb x| ≤ (2*(12*M*eps*radius))*M := by
    simp only [abs_mul]
    norm_num
    exact mul_le_mul (mul_le_mul_of_nonneg_left hdma (by norm_num)) heb (abs_nonneg _) (by positivity)
  have h4 : |2*ma x*deb| ≤ (2*(6*M*eps*radius))*M := by
    simp only [abs_mul]
    norm_num
    exact mul_le_mul (mul_le_mul_of_nonneg_left hma (by norm_num)) hdeb (abs_nonneg _) (by positivity)
  rw [mixedSecondWordCoefficient_directional_eq g1 g2 hg1 hg2 L lam k i j a b x]
  dsimp only
  change |(2*dea+dma)*mb x+(2*ea x+ma x)*dmb+2*dma*eb x+2*ma x*deb| ≤ _
  have ht1 := abs_add_le ((2*dea+dma)*mb x) ((2*ea x+ma x)*dmb)
  have ht2 := abs_add_le ((2*dea+dma)*mb x+(2*ea x+ma x)*dmb) (2*dma*eb x)
  have ht3 := abs_add_le ((2*dea+dma)*mb x+(2*ea x+ma x)*dmb+2*dma*eb x) (2*ma x*deb)
  nlinarith only [h1,h2,h3,h4,ht1,ht2,ht3]

lemma mixedDensityDerivativeCoefficient_eq
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) (k i j a b : Fin 3) (x : R3) :
    mixedDensityDerivativeCoefficient g1 g2 L lam k i j a b x =
      directionalFDeriv (coordinateDirection k) (mixedSecondWordCoefficient g1 g2 L lam i j a b) x +
      ((referenceDensityFamily g1 L (lam,x))⁻¹ *
        directionalFDeriv (coordinateDirection k) (fun y => referenceDensityFamily g1 L (lam,y)) x) *
        mixedSecondWordCoefficient g1 g2 L lam i j a b x := by
  have hmu : ContDiff ℝ ∞ (fun y : R3 => referenceDensityFamily g1 L (lam,y)) :=
    (contDiff_referenceDensityFamily g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  have hc := contDiff_mixedSecondWordCoefficient g1 g2 hg1 hg2 L lam i j a b
  have hp := (referenceDensityFamily_pos g1 hg1 L (lam,x)).ne'
  unfold mixedDensityDerivativeCoefficient
  rw [directional_mul (coordinateDirection k) _ _ hmu hc x]
  field_simp [hp]
  ring

lemma contDiff_mixedDensityDerivativeCoefficient
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) (k i j a b : Fin 3) :
    ContDiff ℝ ∞ (mixedDensityDerivativeCoefficient g1 g2 L lam k i j a b) := by
  have hslice : ContDiff ℝ ∞ (fun y : R3 => (lam,y)) := contDiff_const.prodMk contDiff_id
  have hmu := (contDiff_referenceDensityFamily g1 hg1 L).comp hslice
  have hc := contDiff_mixedSecondWordCoefficient g1 g2 hg1 hg2 L lam i j a b
  unfold mixedDensityDerivativeCoefficient
  exact ((contDiff_referenceDensityFamily_inv g1 hg1 L).comp hslice).mul
    (contDiff_directionalFDeriv (coordinateDirection k) _ (hmu.mul hc))

lemma abs_mixedDensityDerivativeCoefficient_le
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) (x : R3) (eps radius M : ℝ)
    (heps : 0 ≤ eps) (hradius : 0 ≤ radius) (hM : 1 ≤ M) (hsmall : eps*radius ≤ 1)
    (hgeom : MixedBackgroundFirstJetBound g1 L lam x M)
    (hh : MixedMetricFirstJetBound g1 g2 L lam x eps radius) (k i j a b : Fin 3) :
    |mixedDensityDerivativeCoefficient g1 g2 L lam k i j a b x| ≤ 276*M^3*eps*radius := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have ht0 : 0 ≤ eps*radius := mul_nonneg heps hradius
  have htsq : (eps*radius)^2 ≤ eps*radius := by nlinarith
  have hdc := abs_mixedSecondWordCoefficient_directional_le g1 g2 hg1 hg2 L lam x eps radius M heps hradius hM0 hgeom hh k i j a b
  have hc := abs_mixedSecondWordCoefficient_le g1 g2 L lam x eps radius M heps hradius hM0 hh.1 hgeom.2.2.1 hgeom.1 i j a b
  have hdcLin : |directionalFDeriv (coordinateDirection k) (mixedSecondWordCoefficient g1 g2 L lam i j a b) x| ≤ 216*M^2*eps*radius := by
    have h := mul_le_mul_of_nonneg_left htsq (by positivity : 0 ≤ 144*M^2)
    nlinarith only [hdc,h]
  have hcLin : |mixedSecondWordCoefficient g1 g2 L lam i j a b x| ≤ 60*M^2*eps*radius := by
    have h := mul_le_mul_of_nonneg_left htsq (by positivity : 0 ≤ 36*M^2)
    nlinarith only [hc,h]
  have hlog := hgeom.2.2.2.2 k
  have hprod : |((referenceDensityFamily g1 L (lam,x))⁻¹ *
      directionalFDeriv (coordinateDirection k) (fun y => referenceDensityFamily g1 L (lam,y)) x) *
      mixedSecondWordCoefficient g1 g2 L lam i j a b x| ≤ M*(60*M^2*eps*radius) := by
    rw [abs_mul]
    exact mul_le_mul hlog hcLin (abs_nonneg _) hM0
  have hraise : 216*M^2*eps*radius ≤ 216*M^3*eps*radius := by
    have h := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ 216*M^2*eps*radius)
    nlinarith only [h]
  rw [mixedDensityDerivativeCoefficient_eq g1 g2 hg1 hg2 L lam k i j a b x]
  exact (abs_add_le _ _).trans ((add_le_add hdcLin hprod).trans (by nlinarith only [hraise]))

/-- Actual geometry chooses the entire M before g2, h-budget, delta, p or R. -/
theorem exists_mixed_background_first_jet_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K,
      MixedBackgroundFirstJetBound g L lam x M := by
  obtain ⟨MF,hMF,hF⟩ := exists_parameter_coordinate_word_uniform_bound
    (fun t : Fin 3 × Fin 3 => fun z : ℝ × R3 => referenceMetricGramFrame g L z t.1 t.2)
    (fun t => (contDiff_piLp_apply (p := 2) (i := t.2) : ContDiff ℝ ∞ (fun v : R3 => v t.2)).comp
      (contDiff_referenceMetricGramFrame g hg L t.1)) K hK 1
  obtain ⟨MC,hMC,hC⟩ := exists_parameter_coordinate_word_uniform_bound
    (fun t : Fin 3 × Fin 3 => referenceCoFrameEntry g L t.1 t.2)
    (fun t => contDiff_referenceCoFrameEntry g hg L t.1 t.2) K hK 1
  obtain ⟨MD,hMD,hD⟩ := exists_uniform_bound_finite_family
    (fun k : Fin 3 => fun z : ℝ × R3 => (referenceDensityFamily g L z)⁻¹ *
      familyDirectionalDeriv k (referenceDensityFamily g L) z)
    (fun k => ((contDiff_referenceDensityFamily_inv g hg L).mul
      (contDiff_familyDirectionalDeriv k _ (contDiff_referenceDensityFamily g hg L))).continuous) K hK
  let M : ℝ := MF+MC+MD
  have hFM : MF ≤ M := by dsimp [M]; linarith
  have hCM : MC ≤ M := by dsimp [M]; linarith
  have hDM : MD ≤ M := by dsimp [M]; linarith
  refine ⟨M,by dsimp [M]; linarith,?_⟩
  intro lam hlam x hx
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro a i
    have h := (hF lam hlam x hx (a,i) [] (by simp)).trans hFM
    simpa only [coordinateFieldWordPartial,Real.norm_eq_abs] using h
  · intro k a i
    have h := (hF lam hlam x hx (a,i) [k] (by simp)).trans hFM
    simpa only [coordinateFieldWordPartial,Real.norm_eq_abs] using h
  · intro u a
    have h := (hC lam hlam x hx (u,a) [] (by simp)).trans hCM
    simpa only [coordinateFieldWordPartial,Real.norm_eq_abs] using h
  · intro k u a
    have h := (hC lam hlam x hx (u,a) [k] (by simp)).trans hCM
    simpa only [coordinateFieldWordPartial,Real.norm_eq_abs] using h
  · intro k
    have h := (hD lam hlam x hx k).trans hDM
    simpa only [familyDirectionalDeriv] using h

end OAI.AnisotropicCalderon.ActualMixedDensityCoefficientJets
