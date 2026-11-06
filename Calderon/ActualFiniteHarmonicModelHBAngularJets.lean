import Calderon.ActualFirstAngularCommutatorPointwise
import Calderon.ActualFiniteHarmonicModelHBFirstAngularWords
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
private abbrev nativeHBAngularJetsFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeHBAngularJetsFunction
def nativeHBAngularCoefficient
  (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
  (L lam δ R : ℝ) (p : ℕ) (l i : Fin 3) : R3 → SphereL2 →L[ℝ] SphereL2 := by
  intro x
  let m (a j : Fin 3) := physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x
  let f (a : Fin 3) := m a l+2*referenceMetricGramFrame g1 L (lam,x) a l
  let d (j : Fin 3) := nativeFirstDegreeCoefficient g1 g2 L lam δ R p j x
  let k (j c : Fin 3) := nativeFirstConnectionCoefficient g1 g2 L lam δ R p j c x
  let Gamma (c b a : Fin 3) := referenceFrameConnectionCoefficient g1 L lam x
    (referenceMetricGramFrame g1 L (lam,x) c) b a
  exact
    -(∑ a : Fin 3, (d i*f a) • (normalizedDerivative hF hO hD a-normalizedRaising hF hO hD a)) +
    (∑ c : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3,
      (k i c*f a*Gamma c b a) • (normalizedDerivative hF hO hD b+normalizedRaising hF hO hD b)) -
    (∑ b : Fin 3, (m b i*(2*d l)) • normalizedRaising hF hO hD b) -
    (∑ b : Fin 3, ∑ a : Fin 3, (m b i*f a) • normalizedDerivativeRaisingCommutator hF hO hD a b)


def nativeHBBalancedAngularCoefficient
  (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
  (L lam δ R : ℝ) (p : ℕ) (l i : Fin 3) : R3 → SphereL2 →L[ℝ] SphereL2 := by
  intro x
  let m (a j : Fin 3) := physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x
  let f (a : Fin 3) := m a l+2*referenceMetricGramFrame g1 L (lam,x) a l
  let d (j : Fin 3) := nativeFirstDegreeCoefficient g1 g2 L lam δ R p j x
  let k (j c : Fin 3) := nativeFirstConnectionCoefficient g1 g2 L lam δ R p j c x
  let Gamma (c b a : Fin 3) := referenceFrameConnectionCoefficient g1 L lam x
    (referenceMetricGramFrame g1 L (lam,x) c) b a
  exact
    -(∑ a : Fin 3, (d i*f a) • (balancedDerivative hF hO hD a-balancedRaising hF hO hD a)) +
    (∑ c : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3,
      (k i c*f a*Gamma c b a) • (balancedDerivative hF hO hD b+balancedRaising hF hO hD b)) -
    (∑ b : Fin 3, (m b i*(2*d l)) • balancedRaising hF hO hD b) -
    (∑ b : Fin 3, ∑ a : Fin 3, (m b i*f a) • normalizedDerivativeRaisingCommutator hF hO hD a b)


lemma contDiff_nativeHBAngularCoefficient
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (l i : Fin 3) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    ContDiff ℝ ∞ (nativeHBAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i) := by
  have hm (a j : Fin 3) : ContDiff ℝ ∞
      (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j) :=
    contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
      (fun k t => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam k t) a j
  have he (a j : Fin 3) : ContDiff ℝ ∞ (fun y => referenceMetricGramFrame g1 L (lam,y) a j) :=
    (contDiff_piLp_apply (p := 2) (i := j) : ContDiff ℝ ∞ (fun z : R3 => z j)).comp
      (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam a)
  have hf (a : Fin 3) := (hm a l).add ((contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => (2 : ℝ))).mul (he a l))
  have hd (j : Fin 3) := contDiff_nativeFirstDegreeCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j
  have hk (j c : Fin 3) := contDiff_nativeFirstConnectionCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j c
  have hGamma (c b a : Fin 3) : ContDiff ℝ ∞ (fun y => referenceFrameConnectionCoefficient g1 L lam y
      (referenceMetricGramFrame g1 L (lam,y) c) b a) :=
    contDiff_referenceFrameConnectionCoefficient_field g1 hg1 L lam _
      (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam c) b a
  unfold nativeHBAngularCoefficient
  exact (((ContDiff.sum (fun a _ => ((hd i).mul (hf a)).smul contDiff_const)).neg.add
      (ContDiff.sum (fun c _ => ContDiff.sum (fun a _ => ContDiff.sum (fun b _ =>
        (((hk i c).mul (hf a)).mul (hGamma c b a)).smul contDiff_const))))).sub
      (ContDiff.sum (fun b _ => ((hm b i).mul (contDiff_const.mul (hd l))).smul contDiff_const))).sub
      (ContDiff.sum (fun b _ => ContDiff.sum (fun a _ => ((hm b i).mul (hf a)).smul contDiff_const)))


lemma contDiff_nativeHBBalancedAngularCoefficient
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (l i : Fin 3) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    ContDiff ℝ ∞ (nativeHBBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i) := by
  have hm (a j : Fin 3) : ContDiff ℝ ∞
      (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j) :=
    contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
      (fun k t => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam k t) a j
  have he (a j : Fin 3) : ContDiff ℝ ∞ (fun y => referenceMetricGramFrame g1 L (lam,y) a j) :=
    (contDiff_piLp_apply (p := 2) (i := j) : ContDiff ℝ ∞ (fun z : R3 => z j)).comp
      (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam a)
  have hf (a : Fin 3) := (hm a l).add ((contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => (2 : ℝ))).mul (he a l))
  have hd (j : Fin 3) := contDiff_nativeFirstDegreeCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j
  have hk (j c : Fin 3) := contDiff_nativeFirstConnectionCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j c
  have hGamma (c b a : Fin 3) : ContDiff ℝ ∞ (fun y => referenceFrameConnectionCoefficient g1 L lam y
      (referenceMetricGramFrame g1 L (lam,y) c) b a) :=
    contDiff_referenceFrameConnectionCoefficient_field g1 hg1 L lam _
      (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam c) b a
  unfold nativeHBBalancedAngularCoefficient
  exact (((ContDiff.sum (fun a _ => ((hd i).mul (hf a)).smul contDiff_const)).neg.add
      (ContDiff.sum (fun c _ => ContDiff.sum (fun a _ => ContDiff.sum (fun b _ =>
        (((hk i c).mul (hf a)).mul (hGamma c b a)).smul contDiff_const))))).sub
      (ContDiff.sum (fun b _ => ((hm b i).mul (contDiff_const.mul (hd l))).smul contDiff_const))).sub
      (ContDiff.sum (fun b _ => ContDiff.sum (fun a _ => ((hm b i).mul (hf a)).smul contDiff_const)))


lemma nativeHB_angularCoefficient_apply
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (l i : Fin 3) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    (ActualModelCommutatorWords.commutator (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l) (nativeB hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR)) F x =
      (nativeHBAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i) x (coreWeightOperator hO hD (besselWeight 1) F x) := by
  have hDerivative (a : Fin 3) : normalizedDerivative hF hO hD a
      (coreWeightOperator hO hD (besselWeight 1) F x)=coreDerivative hO hD hF a F x := rfl
  have hRaising (a : Fin 3) : normalizedRaising hF hO hD a
      (coreWeightOperator hO hD (besselWeight 1) F x)=coreRaising hO hD hF a F x := rfl
  have hDR (a b : Fin 3) : normalizedDerivativeRaisingCommutator hF hO hD a b
      (coreWeightOperator hO hD (besselWeight 1) F x)=
        ActualModelCommutatorWords.commutator (coreDerivative hO hD hF a) (coreRaising hO hD hF b) F x :=
    (coreDerivative_coreRaising_commutator_apply hO hD hF a b F x).symm
  let m (a j : Fin 3) := physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j
  let e (a : Fin 3) := fun y : R3 => referenceMetricGramFrame g1 L (lam,y) a l
  let d (j : Fin 3) := nativeFirstDegreeCoefficient g1 g2 L lam δ R p j
  let k (c : Fin 3) := nativeFirstConnectionCoefficient g1 g2 L lam δ R p i c
  let Gamma (c b a : Fin 3) := fun y : R3 => referenceFrameConnectionCoefficient g1 L lam y
    (referenceMetricGramFrame g1 L (lam,y) c) b a
  have hm (a j : Fin 3) : ContDiff ℝ ∞ (m a j) :=
    contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
      (fun s t => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam s t) a j
  have he (a : Fin 3) : ContDiff ℝ ∞ (e a) :=
    (contDiff_piLp_apply (p := 2) (i := l) : ContDiff ℝ ∞ (fun z : R3 => z l)).comp
      (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam a)
  have hd (j : Fin 3) : ContDiff ℝ ∞ (d j) :=
    contDiff_nativeFirstDegreeCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j
  have hk (c : Fin 3) : ContDiff ℝ ∞ (k c) :=
    contDiff_nativeFirstConnectionCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR i c
  have hGamma (c b a : Fin 3) : ContDiff ℝ ∞ (Gamma c b a) :=
    contDiff_referenceFrameConnectionCoefficient_field g1 hg1 L lam _
      (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam c) b a
  have hraw := ActualFirstAngularCommutatorPointwise.core_four_angular_blocks_apply
    hO hD (d i) (d l) (fun a => m a l) (fun b => m b i) e k Gamma
    (hd i) (hd l) (fun a => hm a l) (fun b => hm b i) he hk hGamma
    (fun a => coreDerivative hO hD hF a-coreRaising hO hD hF a)
    (fun b => coreDerivative hO hD hF b+coreRaising hO hD hF b)
    (fun b => coreRaising hO hD hF b)
    (fun a b => ActualModelCommutatorWords.commutator (coreDerivative hO hD hF a) (coreRaising hO hD hF b)) F x
  dsimp only at hraw
  have hwords := congrArg (fun X : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => (X F).val x)
    (nativeH_nativeB_commutator_eq_first_angular_words hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l i)
  dsimp only at hwords
  have hact := hwords.trans hraw
  simpa only [nativeHBAngularCoefficient,m,e,d,k,Gamma,nativeReferenceFrameScalar,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,hDerivative,hRaising,hDR,
    LinearMap.add_apply,LinearMap.sub_apply,Submodule.coe_add,Submodule.coe_sub,
    Pi.add_apply,Pi.sub_apply,Finset.sum_apply] using hact


lemma coefficientDerivative_nativeHB_angular_apply
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (l i : Fin 3) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (v : R3) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD v)
      (ActualModelCommutatorWords.commutator (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l) (nativeB hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR)) F x =
      directionalFDeriv v (nativeHBAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i) x (coreWeightOperator hO hD (besselWeight 1) F x) := by
  let U : smoothCompactFiniteSphereCore hO hD := coreWeightOperator hO hD (besselWeight 1) F
  have hact : (fun y => (ActualModelCommutatorWords.commutator (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l) (nativeB hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR)) F y) = (fun y => (nativeHBAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i) y (U y)) :=
    funext (fun y => nativeHB_angularCoefficient_apply hO hD hF g1 g2 hg1 L lam δ R p l i hg2 hδ hR F y)
  have hW : coreWeightOperator hO hD (besselWeight 1) (coreDirectionalDerivative hO hD v F) x =
      directionalFDeriv v (U : R3 → SphereL2) x :=
    congrArg (fun X : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => X F x)
      (coreWeightOperator_directionalDerivative_commute hO hD (besselWeight 1) v).eq
  change directionalFDeriv v (fun y => (ActualModelCommutatorWords.commutator (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l) (nativeB hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR)) F y) x-
    (ActualModelCommutatorWords.commutator (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l) (nativeB hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR)) (coreDirectionalDerivative hO hD v F) x = _
  rw [hact,nativeHB_angularCoefficient_apply hO hD hF g1 g2 hg1 L lam δ R p l i hg2 hδ hR (coreDirectionalDerivative hO hD v F) x]
  rw [directionalFDeriv_clm_apply v (nativeHBAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i) (U : R3 → SphereL2)
    (contDiff_nativeHBAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i hg2 hδ hR) U.property.1 x,hW]
  abel


lemma coefficientDerivative_second_nativeHB_angular_apply
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (l i : Fin 3) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (v u : R3) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD v)
      (ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD u)
        (ActualModelCommutatorWords.commutator (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l) (nativeB hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR))) F x =
      directionalFDeriv v (directionalFDeriv u (nativeHBAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i)) x
        (coreWeightOperator hO hD (besselWeight 1) F x) := by
  let U : smoothCompactFiniteSphereCore hO hD := coreWeightOperator hO hD (besselWeight 1) F
  let A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
    ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD u) (ActualModelCommutatorWords.commutator (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l) (nativeB hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR))
  have ha (G : smoothCompactFiniteSphereCore hO hD) (y : R3) :
      A G y=directionalFDeriv u (nativeHBAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i) y (coreWeightOperator hO hD (besselWeight 1) G y) :=
    coefficientDerivative_nativeHB_angular_apply hO hD hF g1 g2 hg1 L lam δ R p l i hg2 hδ hR u G y
  have hact : (fun y => A F y)=(fun y => directionalFDeriv u (nativeHBAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i) y (U y)) := funext (ha F)
  have hW : coreWeightOperator hO hD (besselWeight 1) (coreDirectionalDerivative hO hD v F) x =
      directionalFDeriv v (U : R3 → SphereL2) x :=
    congrArg (fun X : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => X F x)
      (coreWeightOperator_directionalDerivative_commute hO hD (besselWeight 1) v).eq
  change directionalFDeriv v (fun y => A F y) x-A (coreDirectionalDerivative hO hD v F) x = _
  rw [hact,ha (coreDirectionalDerivative hO hD v F) x]
  rw [directionalFDeriv_clm_apply v (directionalFDeriv u (nativeHBAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i)) (U : R3 → SphereL2)
    (contDiff_directionalFDeriv u _ (contDiff_nativeHBAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i hg2 hδ hR)) U.property.1 x,hW]
  abel


lemma coordinateFieldWordPartial_nativeHB_angular_inner_half
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (l i : Fin 3) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (w : List (Fin 3)) (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪coordinateFieldWordPartial w (nativeHBAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i) x (coreWeightOperator hO hD (besselWeight 1) F x),G x⟫_ℝ =
      ⟪coordinateFieldWordPartial w (nativeHBBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i) x
        (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
  let u := F x
  let u1 := coreWeightOperator hO hD (besselWeight 1) F x
  let uh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x
  let v := G x
  let vh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x
  let HN := nativeHBAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i
  let HB := nativeHBBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i
  have hHN : ContDiff ℝ ∞ HN := contDiff_nativeHBAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i hg2 hδ hR
  have hHB : ContDiff ℝ ∞ HB := contDiff_nativeHBBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l i hg2 hδ hR
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
    simp only [HN,HB,nativeHBAngularCoefficient,nativeHBBalancedAngularCoefficient,
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
