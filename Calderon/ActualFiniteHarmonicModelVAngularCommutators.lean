import Calderon.ActualFiniteHarmonicModelFirstAngularCoefficients
import Calderon.ActualAngularCoefficientCommutator
import Calderon.ActualFiniteHarmonicModelDegreeShiftCommutator
import Calderon.ActualFiniteHarmonicModelRaisingCommute
import Calderon.ActualFiniteHarmonicModelConnectionCommutator
import Mathlib.Algebra.Module.LinearMap.End

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  ActualPhysicalMixedFirst ActualScalarPrincipalAdjoint NaturalAngularAdjoint NormalizedPrincipalMetric
  NormalizedPrincipalMetricSmooth ActualNormalizedSecondModelErrorAssembly ReferenceDensityBounds
  AmbientReferenceCovariantCore SmoothMetricFrame MovingFrameConnection ActualModelCommutatorWords
  ActualAngularCoefficientCommutator
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeVInnerCommutatorFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeVInnerCommutatorFunction
lemma scalarCentral_nativeReferenceConnectionAction
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (c : Fin 3) :
    ScalarCentral hO hD (nativeReferenceConnectionAction hO hD g hg L lam c) := by
  unfold nativeReferenceConnectionAction
  apply scalarCentral_smul hO hD
  apply scalarCentral_sum hO hD
  intro a ha
  apply scalarCentral_sum hO hD
  intro b hb
  apply scalarCentral_mul hO hD
  · exact scalarCentral_coreScalar hO hD _ _
  · exact scalarCentral_coreRotation hO hD _ _


lemma nativeV_degree_commutator
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (l : Fin 3) :
    let m : Fin 3 → Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := fun a =>
      coreScalar hO hD (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a l)
        (contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
          (fun i k => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i k) a l)
    ActualModelCommutatorWords.commutator (nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR)
      (coreDegree hO hD) = -(∑ a : Fin 3, m a*(coreDerivative hO hD hF a-coreRaising hO hD hF a)) := by
  dsimp only
  let N := coreDegree hO hD
  let V := nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR
  let sig := coreScalar hO hD (nativeFirstScalarCoefficient g1 g2 L lam δ R p l)
    (contDiff_nativeFirstScalarCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR l)
  let a1 := coreScalar hO hD (fun x => adjointFirstCoefficient coordinateDirection
      (fun y => referenceDensityFamily g1 L (lam,y))
      (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) x l)
    (contDiff_modelAdjointFirstCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR l)
  let d := coreScalar hO hD (nativeFirstDegreeCoefficient g1 g2 L lam δ R p l)
    (contDiff_nativeFirstDegreeCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR l)
  let m (a : Fin 3) := coreScalar hO hD
    (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a l)
    (contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
      (fun i k => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i k) a l)
  let P (a : Fin 3) := coreDerivative hO hD hF a+coreRaising hO hD hF a
  let S := a1-(2 : ℝ) • sig
  let E := (2 : ℝ) • d
  have hV : V=S-E*N-(∑ a : Fin 3, m a*P a) :=
    nativeV_eq_full_angular_coefficients hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l
  let Y := N
  have hY : ScalarCentral hO hD Y := scalarCentral_coreWeightOperator hO hD (fun k => (k : ℝ))
  have ha1 : Commute a1 Y := (hY _ _).symm
  have hsig : Commute sig Y := (hY _ _).symm
  have hd : Commute d Y := (hY _ _).symm
  have hm (a : Fin 3) : Commute (m a) Y := (hY _ _).symm
  have hS : Commute S Y := by
    change S*Y=Y*S
    apply LinearMap.ext
    intro F
    have h1 : a1 (Y F)=Y (a1 F) := congrArg
      (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F) ha1.eq
    have h2 : sig (Y F)=Y (sig F) := congrArg
      (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F) hsig.eq
    change a1 (Y F)-(2 : ℝ) • sig (Y F)=Y (a1 F-(2 : ℝ) • sig F)
    rw [map_sub,map_smul,h1,h2]
  have hE : Commute E Y := by
    change ((2 : ℝ) • d)*Y=Y*((2 : ℝ) • d)
    simp only [two_smul,add_mul,mul_add,hd.eq]
  have hgen := ActualAngularCoefficientCommutator.defectFirstAngularCoefficient_commutator_left
    S E N Y m P hS hE hm
  rw [← hV] at hgen
  have hNN : ActualModelCommutatorWords.commutator N N=0 := by
    apply LinearMap.ext
    intro F
    apply Subtype.ext
    funext x
    change N (N F) x-N (N F) x=0
    exact _root_.sub_self _
  have hRN (a : Fin 3) : ActualModelCommutatorWords.commutator (coreRaising hO hD hF a) N =
      -coreRaising hO hD hF a := by
    have hanti : ActualModelCommutatorWords.commutator (coreRaising hO hD hF a) N =
        -ActualModelCommutatorWords.commutator N (coreRaising hO hD hF a) := by
      unfold ActualModelCommutatorWords.commutator
      abel
    rw [hanti,coreDegree_raising_commutator hO hD hF a]
  have hPN (a : Fin 3) : ActualModelCommutatorWords.commutator (P a) N =
      coreDerivative hO hD hF a-coreRaising hO hD hF a := by
    have hDN : ActualModelCommutatorWords.commutator (coreDerivative hO hD hF a) N = coreDerivative hO hD hF a :=
      coreDerivative_degree_commutator hO hD hF a
    have ht := ActualModelCommutatorWords.commutator_add_left
      (coreDerivative hO hD hF a) (coreRaising hO hD hF a) N
    rw [hDN,hRN a] at ht
    apply LinearMap.ext
    intro F
    apply Subtype.ext
    funext x
    have hx := congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x) ht
    simpa only [P,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.neg_apply,Submodule.coe_add,
      Submodule.coe_sub,Submodule.coe_neg,Pi.add_apply,Pi.sub_apply,Pi.neg_apply,_root_.sub_eq_add_neg] using hx
  have hgen' : ActualModelCommutatorWords.commutator V N =
      0-∑ a : Fin 3, m a*(coreDerivative hO hD hF a-coreRaising hO hD hF a) := by
    simpa only [Y,hNN,hPN,mul_zero,neg_zero] using hgen
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  have he := congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x) hgen'
  simpa only [V,N,m,LinearMap.sub_apply,LinearMap.neg_apply,LinearMap.zero_apply,
    Submodule.coe_sub,Submodule.coe_neg,Submodule.coe_zero,Pi.sub_apply,Pi.neg_apply,Pi.zero_apply,_root_.zero_sub] using he


lemma nativeV_raising_commutator
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (l : Fin 3) (b : Fin 3) :
    let m : Fin 3 → Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := fun a =>
      coreScalar hO hD (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a l)
        (contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
          (fun i k => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i k) a l)
    let d := coreScalar hO hD (nativeFirstDegreeCoefficient g1 g2 L lam δ R p l)
      (contDiff_nativeFirstDegreeCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR l)
    ActualModelCommutatorWords.commutator (nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR)
      (coreRaising hO hD hF b) = -((2 : ℝ) • d)*coreRaising hO hD hF b -
        ∑ a : Fin 3, m a*ActualModelCommutatorWords.commutator (coreDerivative hO hD hF a) (coreRaising hO hD hF b) := by
  dsimp only
  let N := coreDegree hO hD
  let V := nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR
  let sig := coreScalar hO hD (nativeFirstScalarCoefficient g1 g2 L lam δ R p l)
    (contDiff_nativeFirstScalarCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR l)
  let a1 := coreScalar hO hD (fun x => adjointFirstCoefficient coordinateDirection
      (fun y => referenceDensityFamily g1 L (lam,y))
      (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) x l)
    (contDiff_modelAdjointFirstCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR l)
  let d := coreScalar hO hD (nativeFirstDegreeCoefficient g1 g2 L lam δ R p l)
    (contDiff_nativeFirstDegreeCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR l)
  let m (a : Fin 3) := coreScalar hO hD
    (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a l)
    (contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
      (fun i k => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i k) a l)
  let P (a : Fin 3) := coreDerivative hO hD hF a+coreRaising hO hD hF a
  let S := a1-(2 : ℝ) • sig
  let E := (2 : ℝ) • d
  have hV : V=S-E*N-(∑ a : Fin 3, m a*P a) :=
    nativeV_eq_full_angular_coefficients hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l
  let Y := coreRaising hO hD hF b
  have hY : ScalarCentral hO hD Y := scalarCentral_coreRaising hO hD hF b
  have ha1 : Commute a1 Y := (hY _ _).symm
  have hsig : Commute sig Y := (hY _ _).symm
  have hd : Commute d Y := (hY _ _).symm
  have hm (a : Fin 3) : Commute (m a) Y := (hY _ _).symm
  have hS : Commute S Y := by
    change S*Y=Y*S
    apply LinearMap.ext
    intro F
    have h1 : a1 (Y F)=Y (a1 F) := congrArg
      (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F) ha1.eq
    have h2 : sig (Y F)=Y (sig F) := congrArg
      (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F) hsig.eq
    change a1 (Y F)-(2 : ℝ) • sig (Y F)=Y (a1 F-(2 : ℝ) • sig F)
    rw [map_sub,map_smul,h1,h2]
  have hE : Commute E Y := by
    change ((2 : ℝ) • d)*Y=Y*((2 : ℝ) • d)
    simp only [two_smul,add_mul,mul_add,hd.eq]
  have hgen := ActualAngularCoefficientCommutator.defectFirstAngularCoefficient_commutator_left
    S E N Y m P hS hE hm
  rw [← hV] at hgen
  have hNR : ActualModelCommutatorWords.commutator N Y = Y :=
    coreDegree_raising_commutator hO hD hF b
  have hPR (a : Fin 3) : ActualModelCommutatorWords.commutator (P a) Y =
      ActualModelCommutatorWords.commutator (coreDerivative hO hD hF a) Y := by
    have hRR : ActualModelCommutatorWords.commutator (coreRaising hO hD hF a) Y=0 :=
      ActualAngularCoefficientCommutator.commutator_eq_zero_of_commute _ _ (coreRaising_commute hO hD hF a b)
    simpa only [hRR,add_zero] using ActualModelCommutatorWords.commutator_add_left
      (coreDerivative hO hD hF a) (coreRaising hO hD hF a) Y
  simpa only [hNR,hPR] using hgen


lemma nativeV_connection_commutator
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (l : Fin 3) (c : Fin 3) :
    let m : Fin 3 → Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := fun a =>
      coreScalar hO hD (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a l)
        (contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
          (fun i k => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i k) a l)
    let Gamma : Fin 3 → Fin 3 → Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := fun b a =>
      coreScalar hO hD (fun x => referenceFrameConnectionCoefficient g1 L lam x
        (referenceMetricGramFrame g1 L (lam,x) c) b a)
        (contDiff_referenceFrameConnectionCoefficient_field g1 hg1 L lam _
          (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam c) b a)
    ActualModelCommutatorWords.commutator (nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR)
      (nativeReferenceConnectionAction hO hD g1 hg1 L lam c) =
      ∑ a : Fin 3, ∑ b : Fin 3, m a*Gamma b a*(coreDerivative hO hD hF b+coreRaising hO hD hF b) := by
  dsimp only
  let N := coreDegree hO hD
  let V := nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR
  let sig := coreScalar hO hD (nativeFirstScalarCoefficient g1 g2 L lam δ R p l)
    (contDiff_nativeFirstScalarCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR l)
  let a1 := coreScalar hO hD (fun x => adjointFirstCoefficient coordinateDirection
      (fun y => referenceDensityFamily g1 L (lam,y))
      (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) x l)
    (contDiff_modelAdjointFirstCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR l)
  let d := coreScalar hO hD (nativeFirstDegreeCoefficient g1 g2 L lam δ R p l)
    (contDiff_nativeFirstDegreeCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR l)
  let m (a : Fin 3) := coreScalar hO hD
    (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a l)
    (contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
      (fun i k => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i k) a l)
  let P (a : Fin 3) := coreDerivative hO hD hF a+coreRaising hO hD hF a
  let S := a1-(2 : ℝ) • sig
  let E := (2 : ℝ) • d
  have hV : V=S-E*N-(∑ a : Fin 3, m a*P a) :=
    nativeV_eq_full_angular_coefficients hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l
  let Y := nativeReferenceConnectionAction hO hD g1 hg1 L lam c
  let Gamma (b a : Fin 3) := coreScalar hO hD (fun x => referenceFrameConnectionCoefficient g1 L lam x
    (referenceMetricGramFrame g1 L (lam,x) c) b a)
    (contDiff_referenceFrameConnectionCoefficient_field g1 hg1 L lam _
      (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam c) b a)
  have hY : ScalarCentral hO hD Y := scalarCentral_nativeReferenceConnectionAction hO hD g1 hg1 L lam c
  have ha1 : Commute a1 Y := (hY _ _).symm
  have hsig : Commute sig Y := (hY _ _).symm
  have hd : Commute d Y := (hY _ _).symm
  have hm (a : Fin 3) : Commute (m a) Y := (hY _ _).symm
  have hS : Commute S Y := by
    change S*Y=Y*S
    apply LinearMap.ext
    intro F
    have h1 : a1 (Y F)=Y (a1 F) := congrArg
      (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F) ha1.eq
    have h2 : sig (Y F)=Y (sig F) := congrArg
      (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F) hsig.eq
    change a1 (Y F)-(2 : ℝ) • sig (Y F)=Y (a1 F-(2 : ℝ) • sig F)
    rw [map_sub,map_smul,h1,h2]
  have hE : Commute E Y := by
    change ((2 : ℝ) • d)*Y=Y*((2 : ℝ) • d)
    simp only [two_smul,add_mul,mul_add,hd.eq]
  have hgen := ActualAngularCoefficientCommutator.defectFirstAngularCoefficient_commutator_left
    S E N Y m P hS hE hm
  rw [← hV] at hgen
  have hNY : ActualModelCommutatorWords.commutator N Y=0 :=
    ActualAngularCoefficientCommutator.commutator_eq_zero_of_commute _ _
      (coreDegree_nativeReferenceConnection_commute hO hD g1 hg1 L lam c)
  have hYP (a : Fin 3) : ActualModelCommutatorWords.commutator Y (P a) =
      ∑ b : Fin 3, Gamma b a*P b := by
    apply LinearMap.ext
    intro F
    apply Subtype.ext
    funext x
    have he := congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x)
      (ActualModelCommutatorWords.commutator_add_right Y (coreDerivative hO hD hF a) (coreRaising hO hD hF a))
    change ActualModelCommutatorWords.commutator Y (P a) F x =
      ActualModelCommutatorWords.commutator Y (coreDerivative hO hD hF a) F x+
      ActualModelCommutatorWords.commutator Y (coreRaising hO hD hF a) F x at he
    rw [nativeReferenceConnection_derivative_commutator hO hD hF g1 hg1 L lam c a F x,
      nativeReferenceConnection_raising_commutator hO hD hF g1 hg1 L lam c a F x] at he
    dsimp only [Gamma,P]
    simp only [LinearMap.sum_apply,LinearMap.add_apply,Module.End.mul_apply,coreScalar,LinearMap.coe_mk,AddHom.coe_mk,
      Submodule.coe_mk,Submodule.coe_sum,Submodule.coe_add,Finset.sum_apply,Pi.add_apply]
    simpa only [smul_add,Finset.sum_add_distrib] using he
  have hPY (a : Fin 3) : ActualModelCommutatorWords.commutator (P a) Y = -(∑ b : Fin 3, Gamma b a*P b) := by
    have hanti : ActualModelCommutatorWords.commutator (P a) Y =
        -ActualModelCommutatorWords.commutator Y (P a) := by
      unfold ActualModelCommutatorWords.commutator
      abel
    rw [hanti,hYP a]
  have hgen' : ActualModelCommutatorWords.commutator V Y =
      0-∑ a : Fin 3, m a*-(∑ b : Fin 3, Gamma b a*P b) := by
    simpa only [hNY,hPY,mul_zero,neg_zero] using hgen
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  have he := congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x) hgen'
  simpa only [V,Y,m,Gamma,P,LinearMap.sub_apply,LinearMap.neg_apply,LinearMap.zero_apply,
    LinearMap.sum_apply,LinearMap.add_apply,Module.End.mul_apply,coreScalar,LinearMap.coe_mk,AddHom.coe_mk,
    Submodule.coe_mk,Submodule.coe_sub,Submodule.coe_neg,Submodule.coe_zero,Submodule.coe_sum,Submodule.coe_add,
    Pi.sub_apply,Pi.neg_apply,Pi.zero_apply,Pi.add_apply,Finset.sum_apply,smul_neg,Finset.smul_sum,smul_smul,
    Finset.sum_neg_distrib,_root_.zero_sub,_root_.neg_neg] using he

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
