import Calderon.ActualMixedDensityCoefficientJets
import Calderon.ActualCoordinateOrderedH8

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualMixedDensityHigherCoefficientJets
open SphereHarmonic SphereHilbertDecomposition SmoothSphereFields SmoothAngularApplication
  SmoothMetricFrame PerturbedDensityAdjoint ReferenceDensityBounds PrincipalCommutator ActualPhysicalMixedFirst ActualHorizontalNormBridge
  ActualReferenceDDHigherGeometryJets ActualCoordinateOrderedH8 CoordinateBootstrapJets
  ActualMixedDensityCoefficientJets ActualNormalizedSecondModelErrorAssembly
  ActualNormalizedSecondMixedCommutatorForm NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth

/-- Literal ordered coordinate words agree with the selected source H8 word convention. -/
lemma coordinateFieldWordPartial_eq_source_word
    (w : List (Fin 3)) (f : R3 → ℝ) :
    coordinateFieldWordPartial w f = coordinateWordPartial w f := by
  induction w with
  | nil => rfl
  | cons k w ih =>
    simp only [coordinateFieldWordPartial,coordinateWordPartial,coordinateDerivative,ih]

lemma coordinateFieldWordPartial_append
    (u v : List (Fin 3)) (f : R3 → ℝ) :
    coordinateFieldWordPartial (u++v) f =
      coordinateFieldWordPartial u (coordinateFieldWordPartial v f) := by
  induction u with
  | nil => rfl
  | cons k u ih => simp only [List.cons_append,coordinateFieldWordPartial,ih]

lemma coordinateFieldWordPartial_add
    (w : List (Fin 3)) (f g : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    coordinateFieldWordPartial w (fun y => f y+g y) =
      fun y => coordinateFieldWordPartial w f y+coordinateFieldWordPartial w g y := by
  induction w with
  | nil => rfl
  | cons k w ih =>
    rw [coordinateFieldWordPartial,ih]
    funext y
    exact directionalFDeriv_add (coordinateDirection k) _ _
      (contDiff_coordinateFieldWordPartial w f hf) (contDiff_coordinateFieldWordPartial w g hg) y

lemma coordinateFieldWordPartial_const_mul
    (w : List (Fin 3)) (c : ℝ) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) :
    coordinateFieldWordPartial w (fun y => c*f y) =
      fun y => c*coordinateFieldWordPartial w f y := by
  induction w with
  | nil => rfl
  | cons k w ih =>
    rw [coordinateFieldWordPartial,ih]
    funext y
    have hd := directional_mul (coordinateDirection k) (fun _ : R3 => c)
      (coordinateFieldWordPartial w f) contDiff_const (contDiff_coordinateFieldWordPartial w f hf) y
    simpa only [coordinateFieldWordPartial,directionalFDeriv,fderiv_const_apply,ContinuousLinearMap.zero_apply,zero_mul,zero_add] using hd

lemma coordinateFieldWordPartial_sum
    {ι : Type*} [Fintype ι] (w : List (Fin 3)) (f : ι → R3 → ℝ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    coordinateFieldWordPartial w (fun y => ∑ i : ι, f i y) =
      fun y => ∑ i : ι, coordinateFieldWordPartial w (f i) y := by
  classical
  induction w with
  | nil => rfl
  | cons k w ih =>
    rw [coordinateFieldWordPartial,ih]
    funext y
    unfold directionalFDeriv
    rw [fderiv_fun_sum (fun i _ =>
      (contDiff_coordinateFieldWordPartial w (f i) (hf i)).differentiable (by simp) y)]
    simp only [ContinuousLinearMap.sum_apply,coordinateFieldWordPartial,directionalFDeriv]

/-- A pointwise coordinate product jet bound derived from the exact ordinary
Leibniz rule. It assumes component jets, not a desired product remainder estimate. -/
theorem abs_coordinateFieldWordPartial_mul_le
    (w : List (Fin 3)) (f g : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : R3) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfj : ∀ v : List (Fin 3), v.length ≤ w.length → |coordinateFieldWordPartial v f x| ≤ A)
    (hgj : ∀ v : List (Fin 3), v.length ≤ w.length → |coordinateFieldWordPartial v g x| ≤ B) :
    |coordinateFieldWordPartial w (fun y => f y*g y) x| ≤ (2 : ℝ)^w.length*A*B := by
  induction w using List.reverseRecOn generalizing f g with
  | nil =>
    simpa only [coordinateFieldWordPartial,List.length_nil,pow_zero,one_mul,abs_mul] using
      mul_le_mul (hfj [] (by simp)) (hgj [] (by simp)) (abs_nonneg _) hA
  | append_singleton w k ih =>
    let df : R3 → ℝ := directionalFDeriv (coordinateDirection k) f
    let dg : R3 → ℝ := directionalFDeriv (coordinateDirection k) g
    have hdf := contDiff_directionalFDeriv (coordinateDirection k) f hf
    have hdg := contDiff_directionalFDeriv (coordinateDirection k) g hg
    have hfprev (v : List (Fin 3)) (hv : v.length ≤ w.length) : |coordinateFieldWordPartial v f x| ≤ A :=
      hfj v (by simp only [List.length_append,List.length_singleton]; omega)
    have hgprev (v : List (Fin 3)) (hv : v.length ≤ w.length) : |coordinateFieldWordPartial v g x| ≤ B :=
      hgj v (by simp only [List.length_append,List.length_singleton]; omega)
    have hdfj (v : List (Fin 3)) (hv : v.length ≤ w.length) : |coordinateFieldWordPartial v df x| ≤ A := by
      have ht := hfj (v++[k]) (by simp only [List.length_append,List.length_singleton]; omega)
      simpa only [coordinateFieldWordPartial_append,coordinateFieldWordPartial,df] using ht
    have hdgj (v : List (Fin 3)) (hv : v.length ≤ w.length) : |coordinateFieldWordPartial v dg x| ≤ B := by
      have ht := hgj (v++[k]) (by simp only [List.length_append,List.length_singleton]; omega)
      simpa only [coordinateFieldWordPartial_append,coordinateFieldWordPartial,dg] using ht
    have hfirst := ih df g hdf hg hdfj hgprev
    have hsecond := ih f dg hf hdg hfprev hdgj
    have hp : directionalFDeriv (coordinateDirection k) (fun y => f y*g y) =
        fun y => df y*g y+f y*dg y := by
      funext y
      exact directional_mul (coordinateDirection k) f g hf hg y
    rw [coordinateFieldWordPartial_append]
    change |coordinateFieldWordPartial w
      (directionalFDeriv (coordinateDirection k) (fun y => f y*g y)) x| ≤
      (2 : ℝ)^(w++[k]).length*A*B
    rw [hp,coordinateFieldWordPartial_add w _ _ (hdf.mul hg) (hf.mul hdg)]
    calc
      _ ≤ |coordinateFieldWordPartial w (fun y => df y*g y) x|+
          |coordinateFieldWordPartial w (fun y => f y*dg y) x| := abs_add_le _ _
      _ ≤ (2 : ℝ)^w.length*A*B+(2 : ℝ)^w.length*A*B := add_le_add hfirst hsecond
      _ = _ := by simp only [List.length_append,List.length_singleton,pow_succ]; ring

lemma abs_actual_h_coordinateFieldWordPartial_le_of_H8
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) (x : R3) (A : ℝ)
    (hH8 : coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤ A)
    (w : List (Fin 3)) (hw : w.length ≤ 8) (u v : Fin 3) :
    |coordinateFieldWordPartial w (fun y => referenceNormalizedPrincipalDifference g1 g2 L lam y u v) x| ≤ A := by
  rw [coordinateFieldWordPartial_eq_source_word]
  exact abs_coordinateWordPartial_component_le_of_H8 w hw _
    (fun i j => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i j) x u v A hH8

/-- The actual compact background coordinate jets used by m, c and mu-weighted q.
Every word is ordinary-coordinate; density inverse smoothness is paid natively. -/
def MixedBackgroundCoordinateJetBound (g : MatrixField) (L lam : ℝ)
    (x : R3) (M : ℝ) (N : ℕ) : Prop :=
  (∀ w : List (Fin 3), w.length ≤ N → ∀ a i : Fin 3,
    |coordinateFieldWordPartial w (fun y => referenceMetricGramFrame g L (lam,y) a i) x| ≤ M) ∧
  (∀ w : List (Fin 3), w.length ≤ N → ∀ u a : Fin 3,
    |coordinateFieldWordPartial w (fun y => referenceCoFrameEntry g L u a (lam,y)) x| ≤ M) ∧
  (∀ w : List (Fin 3), w.length ≤ N →
    |coordinateFieldWordPartial w (fun y => referenceDensityFamily g L (lam,y)) x| ≤ M) ∧
  (∀ w : List (Fin 3), w.length ≤ N →
    |coordinateFieldWordPartial w (fun y => (referenceDensityFamily g L (lam,y))⁻¹) x| ≤ M)

def mixedSecondWordJetConstant (N : ℕ) : ℝ :=
  24*((2 : ℝ)^N)^2+36*((2 : ℝ)^N)^3

def mixedDensityDerivativeJetConstant (N : ℕ) : ℝ :=
  (2 : ℝ)^N*(2 : ℝ)^(N+1)*mixedSecondWordJetConstant (N+1)

/-- Entire actual M is selected before h, epsilon, radius and profile parameters. -/
theorem exists_mixed_background_coordinate_jet_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (K : Set R3) (hK : IsCompact K) (N : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K,
      MixedBackgroundCoordinateJetBound g L lam x M N := by
  obtain ⟨MF,hMF,hF⟩ := exists_parameter_coordinate_word_uniform_bound
    (fun t : Fin 3 × Fin 3 => fun z : ℝ × R3 => referenceMetricGramFrame g L z t.1 t.2)
    (fun t => (contDiff_piLp_apply (p := 2) (i := t.2) : ContDiff ℝ ∞ (fun v : R3 => v t.2)).comp
      (contDiff_referenceMetricGramFrame g hg L t.1)) K hK N
  obtain ⟨MC,hMC,hC⟩ := exists_parameter_coordinate_word_uniform_bound
    (fun t : Fin 3 × Fin 3 => referenceCoFrameEntry g L t.1 t.2)
    (fun t => contDiff_referenceCoFrameEntry g hg L t.1 t.2) K hK N
  obtain ⟨MD,hMD,hD⟩ := exists_parameter_coordinate_word_uniform_bound
    (fun _t : Unit => referenceDensityFamily g L)
    (fun _ => contDiff_referenceDensityFamily g hg L) K hK N
  obtain ⟨MI,hMI,hI⟩ := exists_parameter_coordinate_word_uniform_bound
    (fun _t : Unit => fun z : ℝ × R3 => (referenceDensityFamily g L z)⁻¹)
    (fun _ => contDiff_referenceDensityFamily_inv g hg L) K hK N
  let M : ℝ := MF+MC+MD+MI
  have hFM : MF ≤ M := by dsimp [M]; linarith
  have hCM : MC ≤ M := by dsimp [M]; linarith
  have hDM : MD ≤ M := by dsimp [M]; linarith
  have hIM : MI ≤ M := by dsimp [M]; linarith
  refine ⟨M,by dsimp [M]; linarith,?_⟩
  intro lam hlam x hx
  refine ⟨?_,?_,?_,?_⟩
  · intro w hw a i
    have ht := (hF lam hlam x hx (a,i) w hw).trans hFM
    simpa only [Real.norm_eq_abs] using ht
  · intro w hw u a
    have ht := (hC lam hlam x hx (u,a) w hw).trans hCM
    simpa only [Real.norm_eq_abs] using ht
  · intro w hw
    have ht := (hD lam hlam x hx () w hw).trans hDM
    simpa only [Real.norm_eq_abs] using ht
  · intro w hw
    have ht := (hI lam hlam x hx () w hw).trans hIM
    simpa only [Real.norm_eq_abs] using ht

/-- Higher jets of the literal actual mixed first coefficient, derived from
source H8 and genuine actual coframe jets. -/
theorem abs_physicalMixedFirstCoefficient_coordinate_word_le
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) (x : R3) (eps radius M : ℝ) (N : ℕ) (hN : N ≤ 8)
    (heps : 0 ≤ eps) (hradius : 0 ≤ radius) (hM : 0 ≤ M)
    (hgeom : MixedBackgroundCoordinateJetBound g1 L lam x M N)
    (hH8 : coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤ eps*radius)
    (w : List (Fin 3)) (hw : w.length ≤ N) (a j : Fin 3) :
    |coordinateFieldWordPartial w
      (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j) x| ≤
      6*(2 : ℝ)^N*M*eps*radius := by
  have hh (u v : Fin 3) := contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam u v
  have hc (u : Fin 3) : ContDiff ℝ ∞ (fun y => referenceCoFrameEntry g1 L u a (lam,y)) :=
    (contDiff_referenceCoFrameEntry g1 hg1 L u a).comp (contDiff_const.prodMk contDiff_id)
  have hpow : (2 : ℝ)^w.length ≤ (2 : ℝ)^N := pow_le_pow_right₀ (by norm_num) hw
  have ht (u : Fin 3) :
      |coordinateFieldWordPartial w
        (fun y => referenceNormalizedPrincipalDifference g1 g2 L lam y u j *
          referenceCoFrameEntry g1 L u a (lam,y)) x| ≤ (2 : ℝ)^N*(eps*radius)*M := by
    have hb := abs_coordinateFieldWordPartial_mul_le w _ _ (hh u j) (hc u) x (eps*radius) M
      (mul_nonneg heps hradius) hM
      (fun v hv => abs_actual_h_coordinateFieldWordPartial_le_of_H8 g1 g2 hg1 hg2 L lam x _ hH8
        v (le_trans (le_trans hv hw) hN) u j)
      (fun v hv => hgeom.2.1 v (le_trans hv hw) u a)
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpow (mul_nonneg heps hradius)) hM)
  unfold physicalMixedFirstCoefficient
  rw [coordinateFieldWordPartial_const_mul w 2 _ (ContDiff.sum (fun u _ => (hh u j).mul (hc u))),
    coordinateFieldWordPartial_sum w _ (fun u => (hh u j).mul (hc u)),abs_mul]
  rw [show |(2 : ℝ)|=2 by norm_num]
  calc
    _ ≤ 2*∑ u : Fin 3, |coordinateFieldWordPartial w
        (fun y => referenceNormalizedPrincipalDifference g1 g2 L lam y u j *
          referenceCoFrameEntry g1 L u a (lam,y)) x| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ 2*∑ _u : Fin 3, (2 : ℝ)^N*(eps*radius)*M :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun u _ => ht u)) (by norm_num)
    _ = _ := by simp only [Fin.sum_univ_three]; ring

/-- All coordinate coefficient jets of the actual retained second word,
with the small quadratic h contribution allocated honestly by epsilon*r<=1. -/
theorem abs_mixedSecondWordCoefficient_coordinate_word_le
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) (x : R3) (eps radius M : ℝ) (N : ℕ) (hN : N ≤ 8)
    (heps : 0 ≤ eps) (hradius : 0 ≤ radius) (hM : 0 ≤ M) (hsmall : eps*radius ≤ 1)
    (hgeom : MixedBackgroundCoordinateJetBound g1 L lam x M N)
    (hH8 : coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤ eps*radius)
    (w : List (Fin 3)) (hw : w.length ≤ N) (i j a b : Fin 3) :
    |coordinateFieldWordPartial w (mixedSecondWordCoefficient g1 g2 L lam i j a b) x| ≤
      mixedSecondWordJetConstant N*M^2*eps*radius := by
  let ma : R3 → ℝ := physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a i
  let mb : R3 → ℝ := physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) b j
  let ea : R3 → ℝ := fun y => referenceMetricGramFrame g1 L (lam,y) a i
  let eb : R3 → ℝ := fun y => referenceMetricGramFrame g1 L (lam,y) b j
  let q : ℝ := (2 : ℝ)^N
  let t : ℝ := eps*radius
  let D : ℝ := 6*q*M*t
  have ht : 0 ≤ t := mul_nonneg heps hradius
  have hD : 0 ≤ D := by dsimp [D,q]; positivity
  have he (a i : Fin 3) : ContDiff ℝ ∞ (fun y => referenceMetricGramFrame g1 L (lam,y) a i) :=
    (contDiff_piLp_apply (p := 2) (i := i) : ContDiff ℝ ∞ (fun v : R3 => v i)).comp
      (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam a)
  have hm (a i : Fin 3) := contDiff_physicalMixedFirstCoefficient g1 hg1 L lam
    (referenceNormalizedPrincipalDifference g1 g2 L lam)
    (fun u v => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam u v) a i
  have hma (v : List (Fin 3)) (hv : v.length ≤ w.length) : |coordinateFieldWordPartial v ma x| ≤ D := by
    simpa only [ma,D,q,t,mul_assoc] using abs_physicalMixedFirstCoefficient_coordinate_word_le
      g1 g2 hg1 hg2 L lam x eps radius M N hN heps hradius hM hgeom hH8 v (le_trans hv hw) a i
  have hmb (v : List (Fin 3)) (hv : v.length ≤ w.length) : |coordinateFieldWordPartial v mb x| ≤ D := by
    simpa only [mb,D,q,t,mul_assoc] using abs_physicalMixedFirstCoefficient_coordinate_word_le
      g1 g2 hg1 hg2 L lam x eps radius M N hN heps hradius hM hgeom hH8 v (le_trans hv hw) b j
  have hea (v : List (Fin 3)) (hv : v.length ≤ w.length) : |coordinateFieldWordPartial v ea x| ≤ M :=
    hgeom.1 v (le_trans hv hw) a i
  have heb (v : List (Fin 3)) (hv : v.length ≤ w.length) : |coordinateFieldWordPartial v eb x| ≤ M :=
    hgeom.1 v (le_trans hv hw) b j
  have hfbound (v : List (Fin 3)) (hv : v.length ≤ w.length) :
      |coordinateFieldWordPartial v (fun y => 2*ea y+ma y) x| ≤ 2*M+D := by
    rw [coordinateFieldWordPartial_add v _ _ (contDiff_const.mul (he a i)) (hm a i),
      coordinateFieldWordPartial_const_mul v 2 ea (he a i)]
    calc
      _ ≤ |2*coordinateFieldWordPartial v ea x|+|coordinateFieldWordPartial v ma x| := abs_add_le _ _
      _ ≤ 2*M+D := by
        rw [abs_mul,show |(2 : ℝ)|=2 by norm_num]
        exact add_le_add (mul_le_mul_of_nonneg_left (hea v hv) (by norm_num)) (hma v hv)
  have hpow : (2 : ℝ)^w.length ≤ q := pow_le_pow_right₀ (by norm_num) hw
  have hfirst := abs_coordinateFieldWordPartial_mul_le w (fun y => 2*ea y+ma y) mb
    ((contDiff_const.mul (he a i)).add (hm a i)) (hm b j) x (2*M+D) D (by positivity) hD hfbound hmb
  have hsecond := abs_coordinateFieldWordPartial_mul_le w ma eb (hm a i) (he b j) x D M hD hM hma heb
  have hfLe : |coordinateFieldWordPartial w (fun y => (2*ea y+ma y)*mb y) x| ≤ q*(2*M+D)*D :=
    hfirst.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow (by positivity)) hD)
  have hsLe : |coordinateFieldWordPartial w (fun y => ma y*eb y) x| ≤ q*D*M :=
    hsecond.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hD) hM)
  have hcEq : mixedSecondWordCoefficient g1 g2 L lam i j a b =
      fun y => (2*ea y+ma y)*mb y+2*(ma y*eb y) := by
    funext y
    dsimp [mixedSecondWordCoefficient,ea,eb,ma,mb]
    ring
  rw [hcEq,coordinateFieldWordPartial_add w _ _
    (((contDiff_const.mul (he a i)).add (hm a i)).mul (hm b j))
    (contDiff_const.mul ((hm a i).mul (he b j))),
    coordinateFieldWordPartial_const_mul w 2 _ ((hm a i).mul (he b j))]
  have ht2 : t^2 ≤ t := by change t ≤ 1 at hsmall; nlinarith
  have hquad := mul_le_mul_of_nonneg_left ht2 (by positivity : 0 ≤ 36*q^3*M^2)
  calc
    _ ≤ |coordinateFieldWordPartial w (fun y => (2*ea y+ma y)*mb y) x|+
        |2*coordinateFieldWordPartial w (fun y => ma y*eb y) x| := abs_add_le _ _
    _ ≤ q*(2*M+D)*D+2*(q*D*M) := by
      rw [abs_mul,show |(2 : ℝ)|=2 by norm_num]
      exact add_le_add hfLe (mul_le_mul_of_nonneg_left hsLe (by norm_num))
    _ = 24*q^2*M^2*t+36*q^3*M^2*t^2 := by dsimp [D]; ring
    _ ≤ 24*q^2*M^2*t+36*q^3*M^2*t := add_le_add le_rfl hquad
    _ = _ := by dsimp [mixedSecondWordJetConstant,q,t]; ring

/-- Genuine differentiated weighted coefficient jets: all derivatives of mu,
mu inverse and c are retained. One additional h derivative is paid by N+1<=8. -/
theorem abs_mixedDensityDerivativeCoefficient_coordinate_word_le
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) (x : R3) (eps radius M : ℝ) (N : ℕ) (hN : N+1 ≤ 8)
    (heps : 0 ≤ eps) (hradius : 0 ≤ radius) (hM : 0 ≤ M) (hsmall : eps*radius ≤ 1)
    (hgeom : MixedBackgroundCoordinateJetBound g1 L lam x M (N+1))
    (hH8 : coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤ eps*radius)
    (w : List (Fin 3)) (hw : w.length ≤ N) (k i j a b : Fin 3) :
    |coordinateFieldWordPartial w (mixedDensityDerivativeCoefficient g1 g2 L lam k i j a b) x| ≤
      mixedDensityDerivativeJetConstant N*M^4*eps*radius := by
  let mu : R3 → ℝ := fun y => referenceDensityFamily g1 L (lam,y)
  let mui : R3 → ℝ := fun y => (referenceDensityFamily g1 L (lam,y))⁻¹
  let c : R3 → ℝ := mixedSecondWordCoefficient g1 g2 L lam i j a b
  let dmc : R3 → ℝ := directionalFDeriv (coordinateDirection k) (fun y => mu y*c y)
  let C : ℝ := mixedSecondWordJetConstant (N+1)*M^2*eps*radius
  let A : ℝ := (2 : ℝ)^(N+1)*M*C
  have hC : 0 ≤ C := by dsimp [C,mixedSecondWordJetConstant]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hm : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  have hmi : ContDiff ℝ ∞ mui :=
    (contDiff_referenceDensityFamily_inv g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  have hc : ContDiff ℝ ∞ c :=
    OAI.AnisotropicCalderon.ActualNormalizedSecondMixedWeakPairing.contDiff_mixedSecondWordCoefficient g1 g2 hg1 hg2 L lam i j a b
  have hdmc : ContDiff ℝ ∞ dmc := contDiff_directionalFDeriv (coordinateDirection k) _ (hm.mul hc)
  have hprod (v : List (Fin 3)) (hv : v.length ≤ N+1) :
      |coordinateFieldWordPartial v (fun y => mu y*c y) x| ≤ A := by
    have hp := abs_coordinateFieldWordPartial_mul_le v mu c hm hc x M C hM hC
      (fun z hz => hgeom.2.2.1 z (le_trans hz hv))
      (fun z hz => abs_mixedSecondWordCoefficient_coordinate_word_le g1 g2 hg1 hg2 L lam x
        eps radius M (N+1) hN heps hradius hM hsmall hgeom hH8 z (le_trans hz hv) i j a b)
    have hpow : (2 : ℝ)^v.length ≤ (2 : ℝ)^(N+1) := pow_le_pow_right₀ (by norm_num) hv
    exact hp.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hM) hC)
  have hdc (v : List (Fin 3)) (hv : v.length ≤ w.length) : |coordinateFieldWordPartial v dmc x| ≤ A := by
    have hp := hprod (v++[k]) (by simp only [List.length_append,List.length_singleton]; omega)
    simpa only [coordinateFieldWordPartial_append,coordinateFieldWordPartial,dmc] using hp
  have hp := abs_coordinateFieldWordPartial_mul_le w mui dmc hmi hdmc x M A hM hA
    (fun v hv => hgeom.2.2.2 v (by omega)) hdc
  have hpow : (2 : ℝ)^w.length ≤ (2 : ℝ)^N := pow_le_pow_right₀ (by norm_num) hw
  change |coordinateFieldWordPartial w (fun y => mui y*dmc y) x| ≤ _
  calc
    _ ≤ (2 : ℝ)^w.length*M*A := hp
    _ ≤ (2 : ℝ)^N*M*A := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hM) hA
    _ = _ := by dsimp [A,C,mixedDensityDerivativeJetConstant]; ring

end OAI.AnisotropicCalderon.ActualMixedDensityHigherCoefficientJets
