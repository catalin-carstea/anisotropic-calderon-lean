import Calderon.ActualFiniteHarmonicModelReferenceZeroAngular
import Calderon.ActualFiniteHarmonicModelFirstBalancedAngularJets

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic SphereHilbertDecomposition ActualFiniteHarmonicCore SpectralWeightedGraph
  BoundedAngularShift BalancedAngularShift ActualReferenceDDHigherGeometryJets ActualReferenceParallelRaising ActualReferenceDDSpectralTransport
  ActualReferenceModelTrace AmbientReferenceRaising SmoothMetricFrame MovingFrameConnection
  ReferenceDensityBounds NormalizedPrincipalMetric PrincipalCommutator ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev referenceZeroBalancedFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] referenceZeroBalancedFunction

lemma coreWeight_half_one_apply
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
      (coreWeightOperator hO hD (besselWeight 1) F) x =
        coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x := by
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  change SpectralCoreRegularity.sphereHarmonicCoordinate hO hD k
    (coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
      (coreWeightOperator hO hD (besselWeight 1) F) x) =
    SpectralCoreRegularity.sphereHarmonicCoordinate hO hD k (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x)
  rw [(coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ))
      (coreWeightOperator hO hD (besselWeight 1) F) x) k,
    (coreWeightOperator_graph hO hD (besselWeight 1) F x) k,
    (coreWeightOperator_graph hO hD (besselWeight (3/2 : ℝ)) F x) k,smul_smul,
    ← SectionFiveErrorForms.besselWeight_add]
  norm_num

def nativeReferenceZeroDefectBalancedAngularCoefficient
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) : R3 → SphereL2 →L[ℝ] SphereL2 :=
  fun x => (2 : ℝ) • ∑ a : Fin 3,
    (((balancedDerivative hF hO hD a).comp
      (-(normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) a)) +
        (referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x) •
          (ContinuousLinearMap.id ℝ SphereL2 - (2 : ℝ) • inverseDegreeMultiplier hO hD))) -
      ((balancedRaising hF hO hD a).comp
        ((normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) a)) +
          (referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x) •
            (ContinuousLinearMap.id ℝ SphereL2 - inverseDegreeMultiplier hO hD))))

lemma contDiff_nativeReferenceZeroDefectBalancedAngularCoefficient
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) :
    ContDiff ℝ ∞ (nativeReferenceZeroDefectBalancedAngularCoefficient hO hD hF g hg L lam δ R p) := by
  have hA (a : Fin 3) := contDiff_normalizedReferenceAngularConnection_frame hO hD g hg L lam a
  have hf (a : Fin 3) := contDiff_referenceFrameDerivative g hg L lam a _
    (contDiff_log_referenceRadius_profile δ R L p hδ hR)
  unfold nativeReferenceZeroDefectBalancedAngularCoefficient
  apply (contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => (2 : ℝ))).smul
  apply ContDiff.sum
  intro a _
  exact (contDiff_const.clm_comp ((hA a).neg.add ((hf a).smul contDiff_const))).sub
    (contDiff_const.clm_comp ((hA a).add ((hf a).smul contDiff_const)))

lemma coordinateFieldWordPartial_referenceZeroDefect_inner_threehalf_half
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (w : List (Fin 3)) (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪coordinateFieldWordPartial w
        (nativeReferenceZeroDefectAngularCoefficient hO hD hF g hg L lam δ R p) x
        (coreWeightOperator hO hD (besselWeight 2) F x), G x⟫_ℝ =
      ⟪coordinateFieldWordPartial w
        (nativeReferenceZeroDefectBalancedAngularCoefficient hO hD hF g hg L lam δ R p) x
        (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
  let u := coreWeightOperator hO hD (besselWeight 1) F x
  let u2 := coreWeightOperator hO hD (besselWeight 2) F x
  let uh := coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x
  let v := G x
  let vh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x
  let HN := nativeReferenceZeroDefectAngularCoefficient hO hD hF g hg L lam δ R p
  let HB := nativeReferenceZeroDefectBalancedAngularCoefficient hO hD hF g hg L lam δ R p
  have hu1 : (u,u2) ∈ sphereBesselGraph hO hD 1 := by
    dsimp only [u,u2]
    rw [← coreWeight_one_twice_apply hO hD F x]
    exact coreWeightOperator_graph hO hD (besselWeight 1)
      (coreWeightOperator hO hD (besselWeight 1) F) x
  have huh : (u,uh) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := by
    dsimp only [u,uh]
    rw [← coreWeight_half_one_apply hO hD F x]
    exact coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ))
      (coreWeightOperator hO hD (besselWeight 1) F) x
  have hvh : (v,vh) ∈ sphereBesselGraph hO hD (1/2 : ℝ) :=
    coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) G x
  have hd (a : Fin 3) (M : SphereL2 →L[ℝ] SphereL2)
      (hM : PreservesSphereSpectralGraphs hO hD M) :
      ⟪normalizedDerivative hF hO hD a (M u2),v⟫_ℝ =
        ⟪balancedDerivative hF hO hD a (M uh),vh⟫_ℝ :=
    balancedDerivative_inner_realization hF hO hD a (M u) (M uh) _ v vh
      (hM _ u uh huh) (normalizedDerivative_graph hF hO hD a (M u) (M u2)
        (hM _ u u2 hu1)) hvh
  have hr (a : Fin 3) (M : SphereL2 →L[ℝ] SphereL2)
      (hM : PreservesSphereSpectralGraphs hO hD M) :
      ⟪normalizedRaising hF hO hD a (M u2),v⟫_ℝ =
        ⟪balancedRaising hF hO hD a (M uh),vh⟫_ℝ :=
    balancedRaising_inner_realization hF hO hD a (M u) (M uh) _ v vh
      (hM _ u uh huh) (normalizedRaising_graph hF hO hD a (M u) (M u2)
        (hM _ u u2 hu1)) hvh
  have hId : PreservesSphereSpectralGraphs hO hD (ContinuousLinearMap.id ℝ SphereL2) := by
    intro weight z z' hz
    exact hz
  have hd0 (a : Fin 3) : ⟪normalizedDerivative hF hO hD a u2,v⟫_ℝ =
      ⟪balancedDerivative hF hO hD a uh,vh⟫_ℝ := by
    simpa only [ContinuousLinearMap.id_apply] using hd a _ hId
  have hr0 (a : Fin 3) : ⟪normalizedRaising hF hO hD a u2,v⟫_ℝ =
      ⟪balancedRaising hF hO hD a uh,vh⟫_ℝ := by
    simpa only [ContinuousLinearMap.id_apply] using hr a _ hId
  have hI := preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD
  have hdI (a : Fin 3) := hd a (inverseDegreeMultiplier hO hD) hI
  have hrI (a : Fin 3) := hr a (inverseDegreeMultiplier hO hD) hI
  have hA (y : R3) (a : Fin 3) := preservesSphereSpectralGraphs_normalizedReferenceAngularConnection
    hO hD g L lam y (referenceMetricGramFrame g L (lam,y) a)
  have hdA (y : R3) (a : Fin 3) := hd a _ (hA y a)
  have hrA (y : R3) (a : Fin 3) := hr a _ (hA y a)
  have hinner (y : R3) : ⟪HN y u2,v⟫_ℝ = ⟪HB y uh,vh⟫_ℝ := by
    dsimp only [HN,HB]
    unfold nativeReferenceZeroDefectAngularCoefficient nativeReferenceZeroDefectBalancedAngularCoefficient
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.sum_apply,ContinuousLinearMap.id_apply,map_add,map_sub,map_neg,map_smul,
      inner_add_left,inner_sub_left,inner_neg_left,sum_inner,real_inner_smul_left]
    simp_rw [hd0,hr0,hdI,hrI,hdA,hrA]
  have hHN : ContDiff ℝ ∞ HN :=
    contDiff_nativeReferenceZeroDefectAngularCoefficient hO hD hF g hg L lam δ R p hδ hR
  have hHB : ContDiff ℝ ∞ HB :=
    contDiff_nativeReferenceZeroDefectBalancedAngularCoefficient hO hD hF g hg L lam δ R p hδ hR
  let J1 : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ SphereL2 u2)
  let J2 : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ :=
    (innerSL ℝ vh).comp (ContinuousLinearMap.apply ℝ SphereL2 uh)
  have hfunc : (fun y => J1 (HN y)) = fun y => J2 (HB y) := by
    funext y
    change ⟪v,HN y u2⟫_ℝ = ⟪vh,HB y uh⟫_ℝ
    rw [real_inner_comm (HN y u2) v,real_inner_comm (HB y uh) vh]
    exact hinner y
  have hfixed (A : R3 → SphereL2 →L[ℝ] SphereL2) (hA : ContDiff ℝ ∞ A)
      (J : (SphereL2 →L[ℝ] SphereL2) →L[ℝ] ℝ) :
      coordinateFieldWordPartial w (fun y => J (A y)) =
        fun y => J (coordinateFieldWordPartial w A y) := by
    induction w with
    | nil => rfl
    | cons k w ih =>
      change directionalFDeriv (coordinateDirection k)
        (coordinateFieldWordPartial w (fun y => J (A y))) =
          fun y => J (directionalFDeriv (coordinateDirection k) (coordinateFieldWordPartial w A) y)
      rw [ih]
      funext y
      exact ActualReferenceDecomposition.directionalFDeriv_fixed_map J
        (coordinateFieldWordPartial w A) (contDiff_coordinateFieldWordPartial w A hA)
        (coordinateDirection k) y
  have hw := congrArg (fun f : R3 → ℝ => coordinateFieldWordPartial w f) hfunc
  rw [hfixed HN hHN J1,hfixed HB hHB J2] at hw
  have he := congrFun hw x
  change ⟪v,coordinateFieldWordPartial w HN x u2⟫_ℝ =
    ⟪vh,coordinateFieldWordPartial w HB x uh⟫_ℝ at he
  rw [real_inner_comm (coordinateFieldWordPartial w HN x u2) v,
    real_inner_comm (coordinateFieldWordPartial w HB x uh) vh] at he
  exact he

lemma nativeReferenceZeroDefect_inner_threehalf_half
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪(2 * (nativeReferenceAdjointZeroCoefficient hO hD hF g hg L lam δ R p hδ hR -
      nativeReferenceZeroCoefficient hO hD hF g hg L lam δ R p hδ hR)) F x, G x⟫_ℝ =
      ⟪nativeReferenceZeroDefectBalancedAngularCoefficient hO hD hF g hg L lam δ R p x
        (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
  rw [nativeReferenceZeroDefect_secondAngularCoefficient_apply hO hD hF g hg L lam δ R p hδ hR F x]
  exact coordinateFieldWordPartial_referenceZeroDefect_inner_threehalf_half hO hD hF g hg
    L lam δ R p hδ hR [] F G x

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
