import Calderon.ActualMixedDensityHigherCoefficientJets

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualMixedDensityRaisingCoefficientJets
open SphereHarmonic SphereHilbertDecomposition SmoothSphereFields SmoothAngularApplication
  SmoothMetricFrame ReferenceDensityBounds PrincipalCommutator ActualPhysicalMixedFirst ActualHorizontalNormBridge
  ActualReferenceDDHigherGeometryJets ActualCoordinateOrderedH8 CoordinateBootstrapJets
  ActualMixedDensityHigherCoefficientJets ActualNormalizedSecondModelErrorAssembly
  ActualRawMixedPrincipalCollection NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth

/-- The actual W-density lowering coefficient against B_i+2t_i raising.
The sign in physicalMixedDensityCorrection and the ordered mixed factor are retained. -/
def mixedDensityRaisingCoefficient (g1 g2 : MatrixField) (L lam : ℝ)
    (i a b : Fin 3) (x : R3) : ℝ :=
  physicalMixedDensityCorrection g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a x *
    (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) b i x +
      2*referenceMetricGramFrame g1 L (lam,x) b i)

def mixedDensityCorrectionJetConstant (N : ℕ) : ℝ :=
  18*(2 : ℝ)^N*((2 : ℝ)^(N+1))^2

def mixedDensityRaisingCoefficientJetConstant (N : ℕ) : ℝ :=
  18*((2 : ℝ)^N)^2*((2 : ℝ)^(N+1))^2*(6*(2 : ℝ)^N+2)

/-- Exact native density correction; the whole mu derivative remains in every term. -/
lemma physicalMixedDensityCorrection_eq_weighted_divergence
    (g1 g2 : MatrixField) (L lam : ℝ) (a : Fin 3) :
    physicalMixedDensityCorrection g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a =
      fun x => -(∑ j : Fin 3, (referenceDensityFamily g1 L (lam,x))⁻¹ *
        directionalFDeriv (coordinateDirection j)
          (fun y => referenceDensityFamily g1 L (lam,y) *
            physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j y) x) := by
  funext x
  unfold physicalMixedDensityCorrection frameDensityCorrection
  simp only [neg_mul,Finset.mul_sum,← Finset.sum_neg_distrib]

lemma contDiff_mixedDensityRaisingCoefficient
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) (i a b : Fin 3) :
    ContDiff ℝ ∞ (mixedDensityRaisingCoefficient g1 g2 L lam i a b) := by
  have hh (u v : Fin 3) := contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam u v
  have he : ContDiff ℝ ∞ (fun y => referenceMetricGramFrame g1 L (lam,y) b i) :=
    (contDiff_piLp_apply (p := 2) (i := i) : ContDiff ℝ ∞ (fun v : R3 => v i)).comp
      (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam b)
  unfold mixedDensityRaisingCoefficient
  exact (contDiff_physicalMixedDensityCorrection g1 hg1 L lam _ hh a).mul
    ((contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _ hh b i).add (contDiff_const.mul he))

/-- Higher actual W-density scalar jets, derived from H8 and genuine actual
mu/mu-inverse/coframe words. No density derivative is dropped. -/
theorem abs_physicalMixedDensityCorrection_coordinate_word_le
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) (x : R3) (eps radius M : ℝ) (N : ℕ) (hN : N+1 ≤ 8)
    (heps : 0 ≤ eps) (hradius : 0 ≤ radius) (hM : 0 ≤ M)
    (hgeom : MixedBackgroundCoordinateJetBound g1 L lam x M (N+1))
    (hH8 : coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤ eps*radius)
    (w : List (Fin 3)) (hw : w.length ≤ N) (a : Fin 3) :
    |coordinateFieldWordPartial w
      (physicalMixedDensityCorrection g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a) x| ≤
      mixedDensityCorrectionJetConstant N*M^3*eps*radius := by
  let mu : R3 → ℝ := fun y => referenceDensityFamily g1 L (lam,y)
  let mui : R3 → ℝ := fun y => (referenceDensityFamily g1 L (lam,y))⁻¹
  let m : Fin 3 → R3 → ℝ := fun j => physicalMixedFirstCoefficient g1 L lam
    (referenceNormalizedPrincipalDifference g1 g2 L lam) a j
  let dm : Fin 3 → R3 → ℝ := fun j => directionalFDeriv (coordinateDirection j) (fun y => mu y*m j y)
  let q : Fin 3 → R3 → ℝ := fun j y => mui y*dm j y
  let B : ℝ := 6*(2 : ℝ)^(N+1)*M*eps*radius
  let A : ℝ := (2 : ℝ)^(N+1)*M*B
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hm : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  have hmi : ContDiff ℝ ∞ mui :=
    (contDiff_referenceDensityFamily_inv g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  have hmc (j : Fin 3) : ContDiff ℝ ∞ (m j) := contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
    (fun u v => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam u v) a j
  have hdm (j : Fin 3) : ContDiff ℝ ∞ (dm j) :=
    contDiff_directionalFDeriv (coordinateDirection j) _ (hm.mul (hmc j))
  have hq (j : Fin 3) : ContDiff ℝ ∞ (q j) := hmi.mul (hdm j)
  have hprod (j : Fin 3) (v : List (Fin 3)) (hv : v.length ≤ N+1) :
      |coordinateFieldWordPartial v (fun y => mu y*m j y) x| ≤ A := by
    have h := abs_coordinateFieldWordPartial_mul_le v mu (m j) hm (hmc j) x M B hM hB
      (fun z hz => hgeom.2.2.1 z (le_trans hz hv))
      (fun z hz => abs_physicalMixedFirstCoefficient_coordinate_word_le g1 g2 hg1 hg2 L lam x
        eps radius M (N+1) hN heps hradius hM hgeom hH8 z (le_trans hz hv) a j)
    have hpow : (2 : ℝ)^v.length ≤ (2 : ℝ)^(N+1) := pow_le_pow_right₀ (by norm_num) hv
    exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hM) hB)
  have ht (j : Fin 3) : |coordinateFieldWordPartial w (q j) x| ≤ (2 : ℝ)^N*M*A := by
    have hdj (v : List (Fin 3)) (hv : v.length ≤ w.length) :
        |coordinateFieldWordPartial v (dm j) x| ≤ A := by
      have h := hprod j (v++[j]) (by simp only [List.length_append,List.length_singleton]; omega)
      simpa only [coordinateFieldWordPartial_append,coordinateFieldWordPartial,dm] using h
    have h := abs_coordinateFieldWordPartial_mul_le w mui (dm j) hmi (hdm j) x M A hM hA
      (fun v hv => hgeom.2.2.2 v (by omega)) hdj
    have hpow : (2 : ℝ)^w.length ≤ (2 : ℝ)^N := pow_le_pow_right₀ (by norm_num) hw
    exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hM) hA)
  have hdEq : physicalMixedDensityCorrection g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a =
      fun y => (-1 : ℝ)*(∑ j : Fin 3, q j y) := by
    rw [physicalMixedDensityCorrection_eq_weighted_divergence]
    funext y
    dsimp [q,dm,mui,mu,m]
    ring
  rw [hdEq,coordinateFieldWordPartial_const_mul w (-1) _ (ContDiff.sum (fun j _ => hq j)),
    coordinateFieldWordPartial_sum w q hq,abs_mul]
  rw [show |(-1 : ℝ)|=1 by norm_num,one_mul]
  calc
    _ ≤ ∑ j : Fin 3, |coordinateFieldWordPartial w (q j) x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 3, (2 : ℝ)^N*M*A := Finset.sum_le_sum (fun j _ => ht j)
    _ = _ := by simp only [Fin.sum_univ_three]; dsimp [A,B,mixedDensityCorrectionJetConstant]; ring

/-- All actual gamma=d_a(m_bi+2e_bi) coordinate jets needed by this E1 block.
The actual small quadratic h term is allocated only under epsilon*r<=1. -/
theorem abs_mixedDensityRaisingCoefficient_coordinate_word_le
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) (x : R3) (eps radius M : ℝ) (N : ℕ) (hN : N+1 ≤ 8)
    (heps : 0 ≤ eps) (hradius : 0 ≤ radius) (hM : 0 ≤ M) (hsmall : eps*radius ≤ 1)
    (hgeom : MixedBackgroundCoordinateJetBound g1 L lam x M (N+1))
    (hH8 : coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤ eps*radius)
    (w : List (Fin 3)) (hw : w.length ≤ N) (i a b : Fin 3) :
    |coordinateFieldWordPartial w (mixedDensityRaisingCoefficient g1 g2 L lam i a b) x| ≤
      mixedDensityRaisingCoefficientJetConstant N*M^4*eps*radius := by
  let d : R3 → ℝ := physicalMixedDensityCorrection g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a
  let m : R3 → ℝ := physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) b i
  let e : R3 → ℝ := fun y => referenceMetricGramFrame g1 L (lam,y) b i
  let A : ℝ := mixedDensityCorrectionJetConstant N*M^3*eps*radius
  let B : ℝ := (6*(2 : ℝ)^N+2)*M
  have hA : 0 ≤ A := by dsimp [A,mixedDensityCorrectionJetConstant]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hh (u v : Fin 3) := contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam u v
  have hd : ContDiff ℝ ∞ d := contDiff_physicalMixedDensityCorrection g1 hg1 L lam _ hh a
  have hm : ContDiff ℝ ∞ m := contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _ hh b i
  have he : ContDiff ℝ ∞ e :=
    (contDiff_piLp_apply (p := 2) (i := i) : ContDiff ℝ ∞ (fun v : R3 => v i)).comp
      (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam b)
  have hgeomN : MixedBackgroundCoordinateJetBound g1 L lam x M N :=
    ⟨fun v hv => hgeom.1 v (by omega),fun v hv => hgeom.2.1 v (by omega),
      fun v hv => hgeom.2.2.1 v (by omega),fun v hv => hgeom.2.2.2 v (by omega)⟩
  have hdj (v : List (Fin 3)) (hv : v.length ≤ w.length) : |coordinateFieldWordPartial v d x| ≤ A :=
    abs_physicalMixedDensityCorrection_coordinate_word_le g1 g2 hg1 hg2 L lam x eps radius M N hN
      heps hradius hM hgeom hH8 v (le_trans hv hw) a
  have hfj (v : List (Fin 3)) (hv : v.length ≤ w.length) :
      |coordinateFieldWordPartial v (fun y => m y+2*e y) x| ≤ B := by
    have hmv := abs_physicalMixedFirstCoefficient_coordinate_word_le g1 g2 hg1 hg2 L lam x
      eps radius M N (by omega) heps hradius hM hgeomN hH8 v (le_trans hv hw) b i
    have hev := hgeom.1 v (by omega) b i
    have hs := mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ 6*(2 : ℝ)^N*M)
    rw [coordinateFieldWordPartial_add v m _ hm (contDiff_const.mul he),
      coordinateFieldWordPartial_const_mul v 2 e he]
    calc
      _ ≤ |coordinateFieldWordPartial v m x|+|2*coordinateFieldWordPartial v e x| := abs_add_le _ _
      _ ≤ 6*(2 : ℝ)^N*M*eps*radius+2*M := by
        rw [abs_mul,show |(2 : ℝ)|=2 by norm_num]
        exact add_le_add hmv (mul_le_mul_of_nonneg_left hev (by norm_num))
      _ ≤ B := by dsimp [B]; nlinarith only [hs]
  have h := abs_coordinateFieldWordPartial_mul_le w d (fun y => m y+2*e y) hd
    (hm.add (contDiff_const.mul he)) x A B hA hB hdj hfj
  have hpow : (2 : ℝ)^w.length ≤ (2 : ℝ)^N := pow_le_pow_right₀ (by norm_num) hw
  change |coordinateFieldWordPartial w (fun y => d y*(m y+2*e y)) x| ≤ _
  calc
    _ ≤ (2 : ℝ)^w.length*A*B := h
    _ ≤ (2 : ℝ)^N*A*B := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hA) hB
    _ = _ := by dsimp [A,B,mixedDensityCorrectionJetConstant,mixedDensityRaisingCoefficientJetConstant]; ring

end OAI.AnisotropicCalderon.ActualMixedDensityRaisingCoefficientJets
