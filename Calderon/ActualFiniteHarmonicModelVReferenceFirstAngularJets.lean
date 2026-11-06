import Calderon.ActualFirstAngularCommutatorPointwise
import Calderon.ActualFiniteHarmonicModelVReferenceFirstForms
import Calderon.ActualFiniteHarmonicModelDerivativeRaisingCommutator
import Calderon.ActualFiniteHarmonicModelFirstAngularJets
import Calderon.ActualFiniteHarmonicModelFirstBalancedAngularJets

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift BalancedAngularShift
  ActualAngularDerivativeRaisingCommutator ActualPhysicalMixedFirst NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  SmoothMetricFrame MovingFrameConnection AmbientReferenceCovariantCore PrincipalCommutator ReferenceDensityBounds
  ActualReferenceDDHigherCLMProducts ActualReferenceDDHigherGeometryJets ActualReferenceDDSpectralTransport SectionFiveErrorForms
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeVRFirstAngularJetsFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeVRFirstAngularJetsFunction
def nativeVReferenceFirstAngularCoefficient
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (l i : Fin 3) : R3 → SphereL2 →L[ℝ] SphereL2 :=
  fun x => -(∑ b : Fin 3, (referenceMetricGramFrame g1 L (lam,x) b i *
    (2*nativeFirstDegreeCoefficient g1 g2 L lam δ R p l x)) • normalizedRaising hF hO hD b) -
    ∑ b : Fin 3, ∑ a : Fin 3, (referenceMetricGramFrame g1 L (lam,x) b i *
      physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a l x) •
        normalizedDerivativeRaisingCommutator hF hO hD a b

lemma contDiff_nativeVReferenceFirstAngularCoefficient
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (l i : Fin 3) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    ContDiff ℝ ∞ (nativeVReferenceFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i) := by
  have he (b : Fin 3) : ContDiff ℝ ∞ (fun y => referenceMetricGramFrame g1 L (lam,y) b i) :=
    (contDiff_piLp_apply (p := 2) (i := i) : ContDiff ℝ ∞ (fun z : R3 => z i)).comp
      (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam b)
  have hd := contDiff_nativeFirstDegreeCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR l
  have hm (a : Fin 3) := contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
    (fun s t => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam s t) a l
  unfold nativeVReferenceFirstAngularCoefficient
  exact (ContDiff.sum (fun b _ => ((he b).mul (contDiff_const.mul hd)).smul contDiff_const)).neg.sub
    (ContDiff.sum (fun b _ => ContDiff.sum (fun a _ => ((he b).mul (hm a)).smul contDiff_const)))

def nativeVReferenceFirstBalancedAngularCoefficient
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (l i : Fin 3) : R3 → SphereL2 →L[ℝ] SphereL2 :=
  fun x => -(∑ b : Fin 3, (referenceMetricGramFrame g1 L (lam,x) b i *
    (2*nativeFirstDegreeCoefficient g1 g2 L lam δ R p l x)) • balancedRaising hF hO hD b) -
    ∑ b : Fin 3, ∑ a : Fin 3, (referenceMetricGramFrame g1 L (lam,x) b i *
      physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a l x) •
        normalizedDerivativeRaisingCommutator hF hO hD a b

lemma contDiff_nativeVReferenceFirstBalancedAngularCoefficient
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (l i : Fin 3) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    ContDiff ℝ ∞ (nativeVReferenceFirstBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i) := by
  have he (b : Fin 3) : ContDiff ℝ ∞ (fun y => referenceMetricGramFrame g1 L (lam,y) b i) :=
    (contDiff_piLp_apply (p := 2) (i := i) : ContDiff ℝ ∞ (fun z : R3 => z i)).comp
      (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam b)
  have hd := contDiff_nativeFirstDegreeCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR l
  have hm (a : Fin 3) := contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
    (fun s t => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam s t) a l
  unfold nativeVReferenceFirstBalancedAngularCoefficient
  exact (ContDiff.sum (fun b _ => ((he b).mul (contDiff_const.mul hd)).smul contDiff_const)).neg.sub
    (ContDiff.sum (fun b _ => ContDiff.sum (fun a _ => ((he b).mul (hm a)).smul contDiff_const)))

lemma nativeVReferenceFirst_angularCoefficient_apply
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (l i : Fin 3) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    (ActualModelCommutatorWords.commutator (nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR) (nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR i)) F x =
      (nativeVReferenceFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i) x (coreWeightOperator hO hD (besselWeight 1) F x) := by
  have hDerivative (a : Fin 3) : normalizedDerivative hF hO hD a
      (coreWeightOperator hO hD (besselWeight 1) F x)=coreDerivative hO hD hF a F x := rfl
  have hRaising (a : Fin 3) : normalizedRaising hF hO hD a
      (coreWeightOperator hO hD (besselWeight 1) F x)=coreRaising hO hD hF a F x := rfl
  have hDR (a b : Fin 3) : normalizedDerivativeRaisingCommutator hF hO hD a b
      (coreWeightOperator hO hD (besselWeight 1) F x)=
        ActualModelCommutatorWords.commutator (coreDerivative hO hD hF a) (coreRaising hO hD hF b) F x :=
    (coreDerivative_coreRaising_commutator_apply hO hD hF a b F x).symm
  rw [nativeV_referenceFirst_commutator_eq_angular_words]
  dsimp only
  simp only [nativeVReferenceFirstAngularCoefficient,nativeReferenceFrameScalar,coreScalar,
    Module.End.mul_apply,LinearMap.neg_apply,LinearMap.sub_apply,LinearMap.sum_apply,LinearMap.smul_apply,
    LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk,Submodule.coe_neg,Submodule.coe_sub,
    Submodule.coe_sum,Submodule.coe_smul,Finset.sum_apply,Pi.neg_apply,Pi.sub_apply,Pi.smul_apply,
    ContinuousLinearMap.neg_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply,hRaising,hDR,smul_smul,mul_assoc]

lemma coefficientDerivative_nativeVReferenceFirst_angular_apply
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (l i : Fin 3) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (v : R3) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD v)
      (ActualModelCommutatorWords.commutator (nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR) (nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR i)) F x =
      directionalFDeriv v (nativeVReferenceFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i) x (coreWeightOperator hO hD (besselWeight 1) F x) := by
  let U : smoothCompactFiniteSphereCore hO hD := coreWeightOperator hO hD (besselWeight 1) F
  have hact : (fun y => (ActualModelCommutatorWords.commutator (nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR) (nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR i)) F y) = (fun y => (nativeVReferenceFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i) y (U y)) :=
    funext (fun y => nativeVReferenceFirst_angularCoefficient_apply hO hD hF g1 g2 hg1 L lam δ R p l i hg2 hδ hR F y)
  have hW : coreWeightOperator hO hD (besselWeight 1) (coreDirectionalDerivative hO hD v F) x =
      directionalFDeriv v (U : R3 → SphereL2) x :=
    congrArg (fun X : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => X F x)
      (coreWeightOperator_directionalDerivative_commute hO hD (besselWeight 1) v).eq
  change directionalFDeriv v (fun y => (ActualModelCommutatorWords.commutator (nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR) (nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR i)) F y) x-
    (ActualModelCommutatorWords.commutator (nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR) (nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR i)) (coreDirectionalDerivative hO hD v F) x = _
  rw [hact,nativeVReferenceFirst_angularCoefficient_apply hO hD hF g1 g2 hg1 L lam δ R p l i hg2 hδ hR (coreDirectionalDerivative hO hD v F) x]
  rw [directionalFDeriv_clm_apply v (nativeVReferenceFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i) (U : R3 → SphereL2)
    (contDiff_nativeVReferenceFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i hg2 hδ hR) U.property.1 x,hW]
  abel


lemma coefficientDerivative_second_nativeVReferenceFirst_angular_apply
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (l i : Fin 3) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (v u : R3) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD v)
      (ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD u)
        (ActualModelCommutatorWords.commutator (nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR) (nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR i))) F x =
      directionalFDeriv v (directionalFDeriv u (nativeVReferenceFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i)) x
        (coreWeightOperator hO hD (besselWeight 1) F x) := by
  let U : smoothCompactFiniteSphereCore hO hD := coreWeightOperator hO hD (besselWeight 1) F
  let A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
    ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD u) (ActualModelCommutatorWords.commutator (nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR) (nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR i))
  have ha (G : smoothCompactFiniteSphereCore hO hD) (y : R3) :
      A G y=directionalFDeriv u (nativeVReferenceFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i) y (coreWeightOperator hO hD (besselWeight 1) G y) :=
    coefficientDerivative_nativeVReferenceFirst_angular_apply hO hD hF g1 g2 hg1 L lam δ R p l i hg2 hδ hR u G y
  have hact : (fun y => A F y)=(fun y => directionalFDeriv u (nativeVReferenceFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i) y (U y)) := funext (ha F)
  have hW : coreWeightOperator hO hD (besselWeight 1) (coreDirectionalDerivative hO hD v F) x =
      directionalFDeriv v (U : R3 → SphereL2) x :=
    congrArg (fun X : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => X F x)
      (coreWeightOperator_directionalDerivative_commute hO hD (besselWeight 1) v).eq
  change directionalFDeriv v (fun y => A F y) x-A (coreDirectionalDerivative hO hD v F) x = _
  rw [hact,ha (coreDirectionalDerivative hO hD v F) x]
  rw [directionalFDeriv_clm_apply v (directionalFDeriv u (nativeVReferenceFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i)) (U : R3 → SphereL2)
    (contDiff_directionalFDeriv u _ (contDiff_nativeVReferenceFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i hg2 hδ hR)) U.property.1 x,hW]
  abel


lemma coordinateFieldWordPartial_nativeVReferenceFirst_angular_inner_half
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (l i : Fin 3) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (w : List (Fin 3)) (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪coordinateFieldWordPartial w (nativeVReferenceFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i) x (coreWeightOperator hO hD (besselWeight 1) F x),G x⟫_ℝ =
      ⟪coordinateFieldWordPartial w (nativeVReferenceFirstBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i) x
        (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
  let u := F x
  let u1 := coreWeightOperator hO hD (besselWeight 1) F x
  let uh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x
  let v := G x
  let vh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x
  let HN := nativeVReferenceFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i
  let HB := nativeVReferenceFirstBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i
  have hHN : ContDiff ℝ ∞ HN := contDiff_nativeVReferenceFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i hg2 hδ hR
  have hHB : ContDiff ℝ ∞ HB := contDiff_nativeVReferenceFirstBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i hg2 hδ hR
  have hu1 : (u,u1) ∈ sphereBesselGraph hO hD 1 := coreWeightOperator_graph hO hD (besselWeight 1) F x
  have huh : (u,uh) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x
  have hvh : (v,vh) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) G x
  have hub : (uh,u1) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := by
    intro n
    rw [hu1 n,huh n,smul_smul,← besselWeight_add]
    norm_num
  have hDerivative (a : Fin 3) : ⟪normalizedDerivative hF hO hD a u1,v⟫_ℝ =
      ⟪balancedDerivative hF hO hD a uh,vh⟫_ℝ :=
    balancedDerivative_inner_realization hF hO hD a u uh _ v vh huh
      (normalizedDerivative_graph hF hO hD a u u1 hu1) hvh
  have hRaising (a : Fin 3) : ⟪normalizedRaising hF hO hD a u1,v⟫_ℝ =
      ⟪balancedRaising hF hO hD a uh,vh⟫_ℝ :=
    balancedRaising_inner_realization hF hO hD a u uh _ v vh huh
      (normalizedRaising_graph hF hO hD a u u1 hu1) hvh
  have hDR (a b : Fin 3) : ⟪normalizedDerivativeRaisingCommutator hF hO hD a b u1,v⟫_ℝ =
      ⟪normalizedDerivativeRaisingCommutator hF hO hD a b uh,vh⟫_ℝ :=
    spectralGraph_inner_symm hO hD (besselWeight (1/2 : ℝ))
      (normalizedDerivativeRaisingCommutator hF hO hD a b uh)
      (normalizedDerivativeRaisingCommutator hF hO hD a b u1) v vh
      (preservesSphereSpectralGraphs_normalizedDerivativeRaisingCommutator hO hD hF a b _ uh u1 hub) hvh
  have hinner (y : R3) : ⟪HN y u1,v⟫_ℝ = ⟪HB y uh,vh⟫_ℝ := by
    simp only [HN,HB,nativeVReferenceFirstAngularCoefficient,nativeVReferenceFirstBalancedAngularCoefficient,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,inner_add_left,inner_sub_left,
      inner_neg_left,real_inner_smul_left,sum_inner,hDerivative,hRaising,hDR,mul_add,mul_sub]
  let J1 : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ SphereL2 u1)
  let J2 : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ vh).comp (ContinuousLinearMap.apply ℝ SphereL2 uh)
  have hfunc : (fun y => J1 (HN y))=(fun y => J2 (HB y)) := by
    funext y
    change ⟪v,HN y u1⟫_ℝ = ⟪vh,HB y uh⟫_ℝ
    rw [real_inner_comm (HN y u1) v,real_inner_comm (HB y uh) vh]
    exact hinner y
  have hfixed (A : R3 → SphereL2 →L[ℝ] SphereL2) (hA : ContDiff ℝ ∞ A)
      (J : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ) :
      coordinateFieldWordPartial w (fun y => J (A y))=fun y => J (coordinateFieldWordPartial w A y) := by
    induction w with
    | nil => rfl
    | cons k w ih =>
      change directionalFDeriv (coordinateDirection k) (coordinateFieldWordPartial w (fun y => J (A y)))=
        fun y => J (directionalFDeriv (coordinateDirection k) (coordinateFieldWordPartial w A) y)
      rw [ih]
      funext y
      exact ActualReferenceDecomposition.directionalFDeriv_fixed_map J (coordinateFieldWordPartial w A)
        (contDiff_coordinateFieldWordPartial w A hA) (coordinateDirection k) y
  have hw := congrArg (fun z : R3 → ℝ => coordinateFieldWordPartial w z) hfunc
  rw [hfixed HN hHN J1,hfixed HB hHB J2] at hw
  have he := congrFun hw x
  change ⟪v,coordinateFieldWordPartial w HN x u1⟫_ℝ = ⟪vh,coordinateFieldWordPartial w HB x uh⟫_ℝ at he
  rw [real_inner_comm (coordinateFieldWordPartial w HN x u1) v,
    real_inner_comm (coordinateFieldWordPartial w HB x uh) vh] at he
  exact he

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
