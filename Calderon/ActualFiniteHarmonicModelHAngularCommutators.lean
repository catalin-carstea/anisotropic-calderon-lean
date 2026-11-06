import Calderon.ActualFiniteHarmonicModelHFirstAngularShift
import Calderon.ActualFiniteHarmonicModelScalarShiftCommutators

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SmoothMetricFrame MovingFrameConnection
  AmbientReferenceCovariantCore ActualPhysicalMixedFirst NormalizedPrincipalMetric
  NormalizedPrincipalMetricSmooth ActualAngularCoefficientCommutator
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeHInnerCommutatorFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeHInnerCommutatorFunction
lemma nativeH_degree_commutator
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (l : Fin 3) :
    let f : Fin 3 → Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := fun a =>
      coreScalar hO hD (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a l)
        (contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
          (fun i k => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i k) a l) +
        (2 : ℝ) • nativeReferenceFrameScalar hO hD g1 hg1 L lam a l
    ActualModelCommutatorWords.commutator (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l)
      (coreDegree hO hD) = -(∑ a : Fin 3, f a*(coreDerivative hO hD hF a-coreRaising hO hD hF a)) := by
  dsimp only
  let H := nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l
  let V := nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR
  let E (a : Fin 3) := nativeReferenceFrameScalar hO hD g1 hg1 L lam a l
  let m (a : Fin 3) := coreScalar hO hD
    (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a l)
    (contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
      (fun i k => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i k) a l)
  let P (a : Fin 3) := coreDerivative hO hD hF a+coreRaising hO hD hF a
  let S := ∑ a : Fin 3, ((2 : ℝ) • E a)*P a
  let f (a : Fin 3) := m a+(2 : ℝ) • E a
  let v (a : Fin 3) (x : R3) : ℝ := 2*referenceMetricGramFrame g1 L (lam,x) a l
  have hv (a : Fin 3) : ContDiff ℝ ∞ (v a) :=
    contDiff_const.mul ((contDiff_piLp_apply (p := 2) (i := l) :
      ContDiff ℝ ∞ (fun z : R3 => z l)).comp (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam a))
  have hframe2 (a : Fin 3) : coreScalar hO hD (v a) (hv a) = (2 : ℝ) • E a := by
    apply LinearMap.ext
    intro F
    apply Subtype.ext
    funext x
    change (2*referenceMetricGramFrame g1 L (lam,x) a l) • F x =
      (2 : ℝ) • (referenceMetricGramFrame g1 L (lam,x) a l • F x)
    rw [smul_smul]
  have hH : H=V-S := nativeH_eq_nativeV_sub_reference_first_angular_terms
    hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l
  let Y := coreDegree hO hD
  have hV : ActualModelCommutatorWords.commutator V Y =
      -(∑ a : Fin 3, m a*(coreDerivative hO hD hF a-coreRaising hO hD hF a)) :=
    nativeV_degree_commutator hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l
  have hS : ActualModelCommutatorWords.commutator S Y =
      ∑ a : Fin 3, ((2 : ℝ) • E a)*(coreDerivative hO hD hF a-coreRaising hO hD hF a) := by
    have ht := coreScalar_shift_sum_degree_commutator hO hD hF v hv
    dsimp only at ht
    simpa only [hframe2] using ht
  have hsub : ActualModelCommutatorWords.commutator H Y =
      ActualModelCommutatorWords.commutator V Y-ActualModelCommutatorWords.commutator S Y := by
    rw [hH]
    unfold ActualModelCommutatorWords.commutator
    apply LinearMap.ext
    intro F
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub]
    abel
  rw [hsub,hV,hS]
  simp only [f,add_mul,Finset.sum_add_distrib,neg_add_rev]
  abel


lemma nativeH_raising_commutator
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (l : Fin 3) (b : Fin 3) :
    let f : Fin 3 → Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := fun a =>
      coreScalar hO hD (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a l)
        (contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
          (fun i k => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i k) a l) +
        (2 : ℝ) • nativeReferenceFrameScalar hO hD g1 hg1 L lam a l
    let d := coreScalar hO hD (nativeFirstDegreeCoefficient g1 g2 L lam δ R p l)
      (contDiff_nativeFirstDegreeCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR l)
    ActualModelCommutatorWords.commutator (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l)
      (coreRaising hO hD hF b) = -((2 : ℝ) • d)*coreRaising hO hD hF b -
        ∑ a : Fin 3, f a*ActualModelCommutatorWords.commutator (coreDerivative hO hD hF a) (coreRaising hO hD hF b) := by
  dsimp only
  let H := nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l
  let V := nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR
  let E (a : Fin 3) := nativeReferenceFrameScalar hO hD g1 hg1 L lam a l
  let m (a : Fin 3) := coreScalar hO hD
    (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a l)
    (contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
      (fun i k => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i k) a l)
  let P (a : Fin 3) := coreDerivative hO hD hF a+coreRaising hO hD hF a
  let S := ∑ a : Fin 3, ((2 : ℝ) • E a)*P a
  let f (a : Fin 3) := m a+(2 : ℝ) • E a
  let v (a : Fin 3) (x : R3) : ℝ := 2*referenceMetricGramFrame g1 L (lam,x) a l
  have hv (a : Fin 3) : ContDiff ℝ ∞ (v a) :=
    contDiff_const.mul ((contDiff_piLp_apply (p := 2) (i := l) :
      ContDiff ℝ ∞ (fun z : R3 => z l)).comp (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam a))
  have hframe2 (a : Fin 3) : coreScalar hO hD (v a) (hv a) = (2 : ℝ) • E a := by
    apply LinearMap.ext
    intro F
    apply Subtype.ext
    funext x
    change (2*referenceMetricGramFrame g1 L (lam,x) a l) • F x =
      (2 : ℝ) • (referenceMetricGramFrame g1 L (lam,x) a l • F x)
    rw [smul_smul]
  have hH : H=V-S := nativeH_eq_nativeV_sub_reference_first_angular_terms
    hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l
  let Y := coreRaising hO hD hF b
  let d := coreScalar hO hD (nativeFirstDegreeCoefficient g1 g2 L lam δ R p l)
    (contDiff_nativeFirstDegreeCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR l)
  have hV : ActualModelCommutatorWords.commutator V Y = -((2 : ℝ) • d)*Y-
      ∑ a : Fin 3, m a*ActualModelCommutatorWords.commutator (coreDerivative hO hD hF a) Y :=
    nativeV_raising_commutator hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l b
  have hS : ActualModelCommutatorWords.commutator S Y =
      ∑ a : Fin 3, ((2 : ℝ) • E a)*ActualModelCommutatorWords.commutator (coreDerivative hO hD hF a) Y := by
    have ht := coreScalar_shift_sum_raising_commutator hO hD hF v hv b
    dsimp only at ht
    simpa only [hframe2] using ht
  have hsub : ActualModelCommutatorWords.commutator H Y =
      ActualModelCommutatorWords.commutator V Y-ActualModelCommutatorWords.commutator S Y := by
    rw [hH]
    unfold ActualModelCommutatorWords.commutator
    apply LinearMap.ext
    intro F
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub]
    abel
  rw [hsub,hV,hS]
  simp only [f,add_mul,Finset.sum_add_distrib]
  abel


lemma nativeH_connection_commutator
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (l : Fin 3) (c : Fin 3) :
    let f : Fin 3 → Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := fun a =>
      coreScalar hO hD (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a l)
        (contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
          (fun i k => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i k) a l) +
        (2 : ℝ) • nativeReferenceFrameScalar hO hD g1 hg1 L lam a l
    let Gamma : Fin 3 → Fin 3 → Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := fun b a =>
      coreScalar hO hD (fun x => referenceFrameConnectionCoefficient g1 L lam x
        (referenceMetricGramFrame g1 L (lam,x) c) b a)
        (contDiff_referenceFrameConnectionCoefficient_field g1 hg1 L lam _
          (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam c) b a)
    ActualModelCommutatorWords.commutator (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l)
      (nativeReferenceConnectionAction hO hD g1 hg1 L lam c) =
      ∑ a : Fin 3, ∑ b : Fin 3, f a*Gamma b a*(coreDerivative hO hD hF b+coreRaising hO hD hF b) := by
  dsimp only
  let H := nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l
  let V := nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR
  let E (a : Fin 3) := nativeReferenceFrameScalar hO hD g1 hg1 L lam a l
  let m (a : Fin 3) := coreScalar hO hD
    (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a l)
    (contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
      (fun i k => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i k) a l)
  let P (a : Fin 3) := coreDerivative hO hD hF a+coreRaising hO hD hF a
  let S := ∑ a : Fin 3, ((2 : ℝ) • E a)*P a
  let f (a : Fin 3) := m a+(2 : ℝ) • E a
  let v (a : Fin 3) (x : R3) : ℝ := 2*referenceMetricGramFrame g1 L (lam,x) a l
  have hv (a : Fin 3) : ContDiff ℝ ∞ (v a) :=
    contDiff_const.mul ((contDiff_piLp_apply (p := 2) (i := l) :
      ContDiff ℝ ∞ (fun z : R3 => z l)).comp (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam a))
  have hframe2 (a : Fin 3) : coreScalar hO hD (v a) (hv a) = (2 : ℝ) • E a := by
    apply LinearMap.ext
    intro F
    apply Subtype.ext
    funext x
    change (2*referenceMetricGramFrame g1 L (lam,x) a l) • F x =
      (2 : ℝ) • (referenceMetricGramFrame g1 L (lam,x) a l • F x)
    rw [smul_smul]
  have hH : H=V-S := nativeH_eq_nativeV_sub_reference_first_angular_terms
    hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l
  let Y := nativeReferenceConnectionAction hO hD g1 hg1 L lam c
  let Gamma (b a : Fin 3) := coreScalar hO hD (fun x => referenceFrameConnectionCoefficient g1 L lam x
    (referenceMetricGramFrame g1 L (lam,x) c) b a)
    (contDiff_referenceFrameConnectionCoefficient_field g1 hg1 L lam _
      (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam c) b a)
  have hV : ActualModelCommutatorWords.commutator V Y =
      ∑ a : Fin 3, ∑ b : Fin 3, m a*Gamma b a*P b :=
    nativeV_connection_commutator hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l c
  have hS : ActualModelCommutatorWords.commutator S Y =
      -(∑ a : Fin 3, ∑ b : Fin 3, ((2 : ℝ) • E a)*Gamma b a*P b) := by
    have ht := coreScalar_shift_sum_connection_commutator hO hD hF v hv g1 hg1 L lam c
    dsimp only at ht
    simpa only [hframe2] using ht
  have hsub : ActualModelCommutatorWords.commutator H Y =
      ActualModelCommutatorWords.commutator V Y-ActualModelCommutatorWords.commutator S Y := by
    rw [hH]
    unfold ActualModelCommutatorWords.commutator
    apply LinearMap.ext
    intro F
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub]
    abel
  rw [hsub,hV,hS]
  change (∑ a : Fin 3, ∑ b : Fin 3, m a * Gamma b a * P b) -
    -(∑ a : Fin 3, ∑ b : Fin 3, ((2 : ℝ) • E a) * Gamma b a * P b) =
      ∑ a : Fin 3, ∑ b : Fin 3, f a * Gamma b a * P b
  apply LinearMap.ext
  intro F
  simp only [f, Fin.sum_univ_three, LinearMap.sub_apply, LinearMap.neg_apply,
    LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply]
  abel

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
