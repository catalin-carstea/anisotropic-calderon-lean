import Calderon.ActualFiniteHarmonicModelSecondAngularReversedForms
import Calderon.ActualFiniteHarmonicModelZeroAngularBounds

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
  ActualNormalizedSphereRotation ActualReferenceDDNormalizedCoefficient
  ActualReferenceDDSpectralTransport ActualReferenceDDHigherSpectralGraphs
  ActualNormalizedSecondModelErrorAssembly ActualPhysicalMixedProfile
  ActualPhysicalMixedConnection ActualPhysicalPureAngular
  ActualNormalizedSecondDriftAngularAllocation ActualNormalizedSecondDriftWeightedCoefficients
  ReferenceDensityBounds NormalizedPrincipalMetric
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev cReversedFormFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] cReversedFormFunction

def nativeCReversedFormBound (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (x : R3) : ℝ :=
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  ‖referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g1 hg1 L lam δ R p h x‖ +
  (∑ a : Fin 3, 2*|physicalMixedProfileCoefficient g1 L lam δ R p h a x| *
    ‖ContinuousLinearMap.id ℝ SphereL2-inverseDegreeMultiplier hO hD‖) +
  (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
    2*|physicalMixedConnectionCoefficient g1 L lam h a b c x| *‖normalizedRotation hO hD b c‖) +
  (∑ a : Fin 3, ∑ b : Fin 3, 8*|physicalPureAngularCoefficient g1 L lam δ R p h a b x|) +
  ‖normalizedSecondDriftZeroNormalizedCoefficient hO hD g1 g2 hg1 L lam δ R p x‖

lemma abs_inner_nativeC_le_reversed_form_bound
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    |⟪nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x,G x⟫_ℝ| ≤
      nativeCReversedFormBound hO hD g1 g2 hg1 L lam δ R p x *
        ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ := by
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  let K0 := referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g1 hg1 L lam δ R p h x
  let J0 := normalizedSecondDriftZeroNormalizedCoefficient hO hD g1 g2 hg1 L lam δ R p x
  let Q : SphereL2 →L[ℝ] SphereL2 := ContinuousLinearMap.id ℝ SphereL2-inverseDegreeMultiplier hO hD
  let prof (a : Fin 3) := physicalMixedProfileCoefficient g1 L lam δ R p h a x
  let conn (a b c : Fin 3) := physicalMixedConnectionCoefficient g1 L lam h a b c x
  let pure (a b : Fin 3) := physicalPureAngularCoefficient g1 L lam δ R p h a b x
  let W := coreWeightOperator hO hD (besselWeight 2) F x
  let H := ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖
  let V := ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖
  let TP (a : Fin 3) := prof a * ⟪normalizedRaising hF hO hD a (Q W),G x⟫_ℝ
  let TC (a b c : Fin 3) := conn a b c *
    ⟪normalizedRaising hF hO hD a (normalizedRotation hO hD b c W),G x⟫_ℝ
  let TU (a b : Fin 3) := pure a b * ⟪normalizedRaising hF hO hD a
    (normalizedRaising hF hO hD b ((ContinuousLinearMap.id ℝ SphereL2+inverseDegreeMultiplier hO hD) W)),G x⟫_ℝ
  have hK : PreservesSphereSpectralGraphs hO hD K0 :=
    preservesSphereSpectralGraphs_referenceWeightedZeroBaseNormalizedCoefficientTrace
      hO hD g1 hg1 L lam δ R p h x
  have hJ : PreservesSphereSpectralGraphs hO hD J0 :=
    preservesSphereSpectralGraphs_coordinateWord_normalizedSecondDriftZeroNormalizedCoefficient
      hO hD g1 g2 hg1 hg2 L lam δ R p hδ hR [] x
  have hQ : PreservesSphereSpectralGraphs hO hD Q :=
    preservesSphereSpectralGraphs_sub hO hD _ _ (preservesSphereSpectralGraphs_id hO hD)
      (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD)
  have hKb : |⟪K0 W,G x⟫_ℝ| ≤ ‖K0‖*H*V :=
    abs_inner_preserving_weight_two_le_half_threehalf hO hD K0 hK F G x
  have hJb : |⟪J0 W,G x⟫_ℝ| ≤ ‖J0‖*H*V :=
    abs_inner_preserving_weight_two_le_half_threehalf hO hD J0 hJ F G x
  have hP (a : Fin 3) : |TP a| ≤ (2*|prof a| *‖Q‖)*H*V := by
    dsimp only [TP]
    rw [abs_mul]
    have ht := mul_le_mul_of_nonneg_left
      (abs_inner_normalizedRaising_weight_two_le_half_threehalf hO hD hF a Q hQ F G x)
      (abs_nonneg (prof a))
    calc
      _ ≤ |prof a| *((2*‖Q‖)*H*V) := ht
      _ = _ := by ring
  have hC (a b c : Fin 3) : |TC a b c| ≤
      (2*|conn a b c| *‖normalizedRotation hO hD b c‖)*H*V := by
    dsimp only [TC]
    rw [abs_mul]
    have ht := mul_le_mul_of_nonneg_left
      (abs_inner_normalizedRaising_weight_two_le_half_threehalf hO hD hF a
        (normalizedRotation hO hD b c) (preservesSphereSpectralGraphs_normalizedRotation hO hD b c) F G x)
      (abs_nonneg (conn a b c))
    calc
      _ ≤ |conn a b c| *((2*‖normalizedRotation hO hD b c‖)*H*V) := ht
      _ = _ := by ring
  have hU (a b : Fin 3) : |TU a b| ≤ (8*|pure a b|)*H*V := by
    dsimp only [TU]
    rw [abs_mul]
    have ht := mul_le_mul_of_nonneg_left
      (abs_inner_normalizedRaising_twice_weight_two_le_half_threehalf hO hD hF a b F G x)
      (abs_nonneg (pure a b))
    calc
      _ ≤ |pure a b| *(8*H*V) := ht
      _ = _ := by ring
  have hPsum : |∑ a : Fin 3, TP a| ≤ (∑ a : Fin 3, 2*|prof a| *‖Q‖)*H*V := by
    calc
      _ ≤ ∑ a : Fin 3, |TP a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Fin 3, (2*|prof a| *‖Q‖)*H*V := Finset.sum_le_sum (fun a _ => hP a)
      _ = _ := by simp only [Finset.sum_mul]
  have hCsum : |∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, TC a b c| ≤ (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, 2*|conn a b c| *‖normalizedRotation hO hD b c‖)*H*V := by
    calc
      _ ≤ ∑ a : Fin 3, |∑ b : Fin 3, ∑ c : Fin 3, TC a b c| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, |∑ c : Fin 3, TC a b c| := Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, |TC a b c| := Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => Finset.abs_sum_le_sum_abs _ _))
      _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, (2*|conn a b c| *‖normalizedRotation hO hD b c‖)*H*V := Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => Finset.sum_le_sum (fun c _ => hC a b c)))
      _ = _ := by simp only [Finset.sum_mul]
  have hUsum : |∑ a : Fin 3, ∑ b : Fin 3, TU a b| ≤ (∑ a : Fin 3, ∑ b : Fin 3, 8*|pure a b|)*H*V := by
    calc
      _ ≤ ∑ a : Fin 3, |∑ b : Fin 3, TU a b| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, |TU a b| := Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, (8*|pure a b|)*H*V := Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hU a b))
      _ = _ := by simp only [Finset.sum_mul]
  have hact : ⟪nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x,G x⟫_ℝ =
      ⟪K0 W,G x⟫_ℝ + (∑ a : Fin 3, TP a) +
      (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, TC a b c) +
      (∑ a : Fin 3, ∑ b : Fin 3, TU a b) + ⟪J0 W,G x⟫_ℝ := by
    rw [nativeC_secondAngularCoefficient_apply]
    simp only [nativeCSecondAngularCoefficient,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
      inner_add_left,sum_inner,real_inner_smul_left,TP,TC,TU,K0,J0,Q,prof,conn,pure,W,h]
  rw [hact]
  calc
    _ ≤ |⟪K0 W,G x⟫_ℝ| + |∑ a : Fin 3, TP a| +
        |∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, TC a b c| +
        |∑ a : Fin 3, ∑ b : Fin 3, TU a b| + |⟪J0 W,G x⟫_ℝ| :=
      (abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    _ ≤ ‖K0‖*H*V + (∑ a : Fin 3, 2*|prof a| *‖Q‖)*H*V +
        (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
          2*|conn a b c| *‖normalizedRotation hO hD b c‖)*H*V +
        (∑ a : Fin 3, ∑ b : Fin 3, 8*|pure a b|)*H*V + ‖J0‖*H*V :=
      add_le_add (add_le_add (add_le_add (add_le_add hKb hPsum) hCsum) hUsum) hJb
    _ = _ := by dsimp only [nativeCReversedFormBound,K0,J0,Q,prof,conn,pure,H,V,h]; ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
