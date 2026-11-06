import Calderon.ActualFiniteHarmonicModelVBAngularTerms
import Calderon.ActualFirstAngularCoefficientCollection
import Calderon.ActualFiniteHarmonicModelReferenceWeights

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  ActualPhysicalMixedReferenceCancellation ActualPhysicalMixedFirst ActualNormalizedSecondMetricDrift
  ActualNormalizedSecondModelErrorAssembly ActualScalarPrincipalAdjoint NaturalAngularAdjoint
  AmbientReferenceRaising AmbientReferenceCovariantCore ReferenceDensityBounds
  NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth SmoothMetricFrame MovingFrameConnection
  ConformalDepth PrincipalCommutator ActualReferenceParallelRaising ActualFirstAngularCoefficientCollection
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeFirstAngularASTFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeFirstAngularASTFunction
def nativeFirstScalarCoefficient
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) : R3 → ℝ := fun x =>
  referenceRadius δ R p L x * normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x) -
    referenceRadius δ R p L x * ∑ a : Fin 3, ∑ b : Fin 3,
      physicalMixedQFrameCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a b x *
        (referenceConnectionFamily g1 L (lam,x) (referenceMetricGramFrame g1 L (lam,x) a)
          (referenceMetricGramFrame g1 L (lam,x) b)) j

def nativeFirstDegreeCoefficient
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) : R3 → ℝ := fun x =>
  referenceRadius δ R p L x * ∑ a : Fin 3, ∑ b : Fin 3,
    physicalMixedQFrameCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a b x *
      (referenceFrameDerivative g1 L lam b (fun y => Real.log (referenceRadius δ R p L y)) x *
          referenceMetricGramFrame g1 L (lam,x) a j +
        referenceFrameDerivative g1 L lam a (fun y => Real.log (referenceRadius δ R p L y)) x *
          referenceMetricGramFrame g1 L (lam,x) b j)

def nativeFirstConnectionCoefficient
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ) (j c : Fin 3) : R3 → ℝ := fun x =>
  referenceRadius δ R p L x *
    ((∑ a : Fin 3, physicalMixedQFrameCoefficient g1 L lam
        (referenceNormalizedPrincipalDifference g1 g2 L lam) a c x * referenceMetricGramFrame g1 L (lam,x) a j) +
      (∑ b : Fin 3, physicalMixedQFrameCoefficient g1 L lam
        (referenceNormalizedPrincipalDifference g1 g2 L lam) c b x * referenceMetricGramFrame g1 L (lam,x) b j))
lemma contDiff_nativeFirstScalarCoefficient
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) :
    ContDiff ℝ ∞ (nativeFirstScalarCoefficient g1 g2 L lam δ R p j) := by
  have hr := contDiff_referenceRadius_actual δ R p L hδ hR
  have hq (a b : Fin 3) : ContDiff ℝ ∞
      (physicalMixedQFrameCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a b) :=
    contDiff_physicalMixedQFrameCoefficient g1 hg1 L lam _
      (fun i k => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i k) a b
  have he (a : Fin 3) : ContDiff ℝ ∞ (fun x => referenceMetricGramFrame g1 L (lam,x) a j) :=
    (contDiff_piLp_apply (p := 2) (i := j) : ContDiff ℝ ∞ (fun v : R3 => v j)).comp
      (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam a)
  have hgamma (a b : Fin 3) : ContDiff ℝ ∞ (fun x =>
      (referenceConnectionFamily g1 L (lam,x) (referenceMetricGramFrame g1 L (lam,x) a)
        (referenceMetricGramFrame g1 L (lam,x) b)) j) :=
    (contDiff_piLp_apply (p := 2) (i := j) : ContDiff ℝ ∞ (fun v : R3 => v j)).comp
      ((((contDiff_referenceConnectionFamily g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)).clm_apply
        (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam a)).clm_apply
          (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam b))
  have hdrift : ContDiff ℝ ∞ (fun x : R3 => normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x)) :=
    (contDiff_normalizedSecondDriftCoordinateJoint g1 g2 hg1 hg2 L j).comp
      (contDiff_const.prodMk contDiff_id)
  unfold nativeFirstScalarCoefficient
  exact (hr.mul hdrift).sub (hr.mul (ContDiff.sum (fun a _ =>
    ContDiff.sum (fun b _ => (hq a b).mul (hgamma a b)))))


lemma contDiff_nativeFirstDegreeCoefficient
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) :
    ContDiff ℝ ∞ (nativeFirstDegreeCoefficient g1 g2 L lam δ R p j) := by
  have hr := contDiff_referenceRadius_actual δ R p L hδ hR
  have hq (a b : Fin 3) : ContDiff ℝ ∞
      (physicalMixedQFrameCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a b) :=
    contDiff_physicalMixedQFrameCoefficient g1 hg1 L lam _
      (fun i k => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i k) a b
  have he (a : Fin 3) : ContDiff ℝ ∞ (fun x => referenceMetricGramFrame g1 L (lam,x) a j) :=
    (contDiff_piLp_apply (p := 2) (i := j) : ContDiff ℝ ∞ (fun v : R3 => v j)).comp
      (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam a)
  have hp (a : Fin 3) : ContDiff ℝ ∞
      (referenceFrameDerivative g1 L lam a (fun y => Real.log (referenceRadius δ R p L y))) :=
    contDiff_referenceFrameDerivative g1 hg1 L lam a _
      (contDiff_log_referenceRadius_profile δ R L p hδ hR)
  unfold nativeFirstDegreeCoefficient
  exact hr.mul (ContDiff.sum (fun a _ => ContDiff.sum (fun b _ =>
    (hq a b).mul (((hp b).mul (he a)).add ((hp a).mul (he b))))))


lemma contDiff_nativeFirstConnectionCoefficient
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (j c : Fin 3) :
    ContDiff ℝ ∞ (nativeFirstConnectionCoefficient g1 g2 L lam δ R p j c) := by
  have hr := contDiff_referenceRadius_actual δ R p L hδ hR
  have hq (a b : Fin 3) : ContDiff ℝ ∞
      (physicalMixedQFrameCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a b) :=
    contDiff_physicalMixedQFrameCoefficient g1 hg1 L lam _
      (fun i k => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i k) a b
  have he (a : Fin 3) : ContDiff ℝ ∞ (fun x => referenceMetricGramFrame g1 L (lam,x) a j) :=
    (contDiff_piLp_apply (p := 2) (i := j) : ContDiff ℝ ∞ (fun v : R3 => v j)).comp
      (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam a)
  unfold nativeFirstConnectionCoefficient
  exact hr.mul ((ContDiff.sum (fun a _ => (hq a c).mul (he a))).add
    (ContDiff.sum (fun b _ => (hq c b).mul (he b))))


lemma nativeB_eq_full_angular_coefficients
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) :
    nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR =
    coreScalar hO hD (nativeFirstScalarCoefficient g1 g2 L lam δ R p j)
      (contDiff_nativeFirstScalarCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j) +
    coreScalar hO hD (nativeFirstDegreeCoefficient g1 g2 L lam δ R p j)
      (contDiff_nativeFirstDegreeCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j) * coreDegree hO hD +
    (∑ c : Fin 3, coreScalar hO hD (nativeFirstConnectionCoefficient g1 g2 L lam δ R p j c)
      (contDiff_nativeFirstConnectionCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j c) *
      nativeReferenceConnectionAction hO hD g1 hg1 L lam c) +
    ∑ a : Fin 3, coreScalar hO hD
        (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j)
        (contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
          (fun i k => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i k) a j) * coreRaising hO hD hF a := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  change nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F x = _
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.sum_apply,
    Module.End.mul_apply,coreScalar,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk,
    Submodule.coe_add,Submodule.coe_sub,Submodule.coe_smul,Submodule.coe_sum,
    Finset.sum_apply,Pi.add_apply,Pi.sub_apply,Pi.smul_apply]
  rw [nativeB_apply_eq_full_angular_terms hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j F x]
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  let r := referenceRadius δ R p L x
  let drift := normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x)
  let q (a b : Fin 3) := physicalMixedQFrameCoefficient g1 L lam h a b x
  let gamma (a b : Fin 3) := (referenceConnectionFamily g1 L (lam,x)
    (referenceMetricGramFrame g1 L (lam,x) a) (referenceMetricGramFrame g1 L (lam,x) b)) j
  let eta (a b : Fin 3) :=
    referenceFrameDerivative g1 L lam b (fun y => Real.log (referenceRadius δ R p L y)) x *
      referenceMetricGramFrame g1 L (lam,x) a j +
    referenceFrameDerivative g1 L lam a (fun y => Real.log (referenceRadius δ R p L y)) x *
      referenceMetricGramFrame g1 L (lam,x) b j
  let e (a : Fin 3) := referenceMetricGramFrame g1 L (lam,x) a j
  let m (a : Fin 3) := physicalMixedFirstCoefficient g1 L lam h a j x
  have hc := ActualFirstAngularCoefficientCollection.firstAngularCoefficient_collection r drift q gamma eta e m
    (F x) (coreDegree hO hD F x)
    (fun c => normalizedReferenceAngularConnection hO hD g1 L lam x (referenceMetricGramFrame g1 L (lam,x) c)
      (coreWeightOperator hO hD (besselWeight 1) F x))
    (fun a => coreRaising hO hD hF a F x)
  simpa only [nativeFirstScalarCoefficient,nativeFirstDegreeCoefficient,nativeFirstConnectionCoefficient,
    nativeReferenceConnectionAction_apply_eq_normalized,h,r,drift,q,gamma,eta,e,m] using hc


lemma nativeV_eq_full_angular_coefficients
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) :
    nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR =
    coreScalar hO hD
      (fun x => adjointFirstCoefficient coordinateDirection (fun y => referenceDensityFamily g1 L (lam,y))
        (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) x j)
      (contDiff_modelAdjointFirstCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j) -
    (2 : ℝ) • (coreScalar hO hD (nativeFirstScalarCoefficient g1 g2 L lam δ R p j)
      (contDiff_nativeFirstScalarCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j)) -
    ((2 : ℝ) • (coreScalar hO hD (nativeFirstDegreeCoefficient g1 g2 L lam δ R p j)
      (contDiff_nativeFirstDegreeCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j))) * coreDegree hO hD -
    ∑ a : Fin 3, coreScalar hO hD
        (physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j)
        (contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
          (fun i k => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i k) a j) * (coreDerivative hO hD hF a+coreRaising hO hD hF a) := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  change nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F x = _
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.sum_apply,
    Module.End.mul_apply,coreScalar,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk,
    Submodule.coe_add,Submodule.coe_sub,Submodule.coe_smul,Submodule.coe_sum,
    Finset.sum_apply,Pi.add_apply,Pi.sub_apply,Pi.smul_apply]
  rw [nativeV_apply_eq_full_angular_terms hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j F x]
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  let r := referenceRadius δ R p L x
  let drift := normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x)
  let q (a b : Fin 3) := physicalMixedQFrameCoefficient g1 L lam h a b x
  let gamma (a b : Fin 3) := (referenceConnectionFamily g1 L (lam,x)
    (referenceMetricGramFrame g1 L (lam,x) a) (referenceMetricGramFrame g1 L (lam,x) b)) j
  let eta (a b : Fin 3) :=
    referenceFrameDerivative g1 L lam b (fun y => Real.log (referenceRadius δ R p L y)) x *
      referenceMetricGramFrame g1 L (lam,x) a j +
    referenceFrameDerivative g1 L lam a (fun y => Real.log (referenceRadius δ R p L y)) x *
      referenceMetricGramFrame g1 L (lam,x) b j
  let e (a : Fin 3) := referenceMetricGramFrame g1 L (lam,x) a j
  let m (a : Fin 3) := physicalMixedFirstCoefficient g1 L lam h a j x
  let a1 := adjointFirstCoefficient coordinateDirection (fun y => referenceDensityFamily g1 L (lam,y))
    (actualPrincipalMatrix g1 L lam δ R p h) x j
  have hc := ActualFirstAngularCoefficientCollection.defectFirstAngularCoefficient_collection r drift a1 q gamma eta m
    (F x) (coreDegree hO hD F x) (fun a => coreDerivative hO hD hF a F x)
    (fun a => coreRaising hO hD hF a F x)
  simpa only [nativeFirstScalarCoefficient,nativeFirstDegreeCoefficient,h,r,drift,q,gamma,eta,m,a1,
    mul_sub,sub_smul,smul_sub,smul_smul,mul_assoc] using hc

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
