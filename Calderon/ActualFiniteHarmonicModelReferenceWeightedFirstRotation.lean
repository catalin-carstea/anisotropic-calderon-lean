import Calderon.ActualFiniteHarmonicModelReferenceWeightedFirstScalars
import Calderon.ActualFiniteHarmonicModelNormalizedConnectionAdjoint
import Calderon.ActualReferenceFirstRotationCollection
import Calderon.ActualAngularFiniteCoefficientDerivative
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
  ActualNormalizedSphereRotation ActualReferenceParallelRaising ActualReferenceDDNormalizedCoefficient
  ActualReferenceDDHigherSpectralGraphs ActualPhysicalMixedReferenceCancellation AmbientReferenceRaising
  AmbientReferenceCovariantCore SmoothMetricFrame MovingFrameConnection PrincipalCommutator
  ConformalDepth NaturalAngularAdjoint ReferenceDensityBounds
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeReferenceWeightedFirstFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeReferenceWeightedFirstFunction

lemma referenceWeightedFirstBaseNormalizedCoefficient_fixed_rotation
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (j : Fin 3) (x : R3) :
    referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j x =
    nativeReferenceWeightedFirstScalarCoefficient g L lam δ R p h j x • inverseDegreeMultiplier hO hD +
      nativeReferenceWeightedFirstDegreeCoefficient g L lam δ R p h j x •
        (ContinuousLinearMap.id ℝ SphereL2-inverseDegreeMultiplier hO hD) +
      (∑ s : Fin 3, ∑ t : Fin 3,
        nativeReferenceWeightedFirstRotationCoefficient g L lam δ R p h j s t x •
          normalizedRotation hO hD s t) := by
  have hcol := ActualReferenceFirstRotationCollection.first_base_fixed_rotation_collection
    (M := SphereL2 →L[ℝ] SphereL2) (referenceRadius δ R p L x)
    (fun a b => physicalMixedQFrameCoefficient g L lam h a b x)
    (fun a b => (referenceConnectionFamily g L (lam,x)
      (referenceMetricGramFrame g L (lam,x) a) (referenceMetricGramFrame g L (lam,x) b)) j)
    (fun a b => referenceFrameDerivative g L lam b (fun y => Real.log (referenceRadius δ R p L y)) x *
        referenceMetricGramFrame g L (lam,x) a j +
      referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x *
        referenceMetricGramFrame g L (lam,x) b j)
    (fun a => referenceMetricGramFrame g L (lam,x) a j)
    (fun a s t => referenceFrameConnectionCoefficient g L lam x (referenceMetricGramFrame g L (lam,x) a) s t)
    (inverseDegreeMultiplier hO hD) (ContinuousLinearMap.id ℝ SphereL2-inverseDegreeMultiplier hO hD)
    (fun s t => normalizedRotation hO hD s t)
  simpa only [referenceWeightedFirstBaseNormalizedCoefficient,normalizedReferenceAngularConnection,
    nativeReferenceWeightedFirstScalarCoefficient,nativeReferenceWeightedFirstDegreeCoefficient,
    nativeReferenceWeightedFirstRotationCoefficient] using hcol

lemma referenceWeightedFirstBaseNormalizedCoefficient_adjoint_fixed_rotation
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (j : Fin 3) (x : R3) :
    ContinuousLinearMap.adjoint (referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j x) =
    nativeReferenceWeightedFirstScalarCoefficient g L lam δ R p h j x • inverseDegreeMultiplier hO hD +
      nativeReferenceWeightedFirstDegreeCoefficient g L lam δ R p h j x •
        (ContinuousLinearMap.id ℝ SphereL2-inverseDegreeMultiplier hO hD) -
      (∑ s : Fin 3, ∑ t : Fin 3,
        nativeReferenceWeightedFirstRotationCoefficient g L lam δ R p h j s t x •
          normalizedRotation hO hD s t) := by
  have hAdScalar (r : ℝ) (T : SphereL2 →L[ℝ] SphereL2) :
      ContinuousLinearMap.adjoint (r • T)=r • ContinuousLinearMap.adjoint T := by
    simpa only [starRingEnd_apply,star_trivial] using
      map_smulₛₗ (ContinuousLinearMap.adjoint :
        (SphereL2 →L[ℝ] SphereL2) ≃ₗᵢ⋆[ℝ] (SphereL2 →L[ℝ] SphereL2)) r T
  let Ad : (SphereL2 →L[ℝ] SphereL2) →+ (SphereL2 →L[ℝ] SphereL2) :=
    (ContinuousLinearMap.adjoint :
      (SphereL2 →L[ℝ] SphereL2) ≃ₗᵢ⋆[ℝ] (SphereL2 →L[ℝ] SphereL2)).toLinearEquiv.toLinearMap.toAddMonoidHom
  have hAdAdd (S T : SphereL2 →L[ℝ] SphereL2) :
      ContinuousLinearMap.adjoint (S+T)=ContinuousLinearMap.adjoint S+ContinuousLinearMap.adjoint T :=
    map_add Ad S T
  have hAdSub (S T : SphereL2 →L[ℝ] SphereL2) :
      ContinuousLinearMap.adjoint (S-T)=ContinuousLinearMap.adjoint S-ContinuousLinearMap.adjoint T :=
    map_sub Ad S T
  have hAdSum (T : Fin 3 → (SphereL2 →L[ℝ] SphereL2)) :
      ContinuousLinearMap.adjoint (∑ c : Fin 3, T c)=∑ c : Fin 3, ContinuousLinearMap.adjoint (T c) := by
    change Ad (∑ c : Fin 3, T c)=∑ c : Fin 3, Ad (T c)
    exact map_sum Ad T Finset.univ
  rw [referenceWeightedFirstBaseNormalizedCoefficient_fixed_rotation hO hD g hg L lam δ R p h j x]
  simp only [hAdAdd,hAdSub,hAdScalar,hAdSum,ContinuousLinearMap.adjoint_id,
    inverseDegreeMultiplier_adjoint_eq hO hD,normalizedRotation_adjoint_eq_neg hO hD,
    smul_neg,Finset.sum_neg_distrib]
  simp only [sub_eq_add_neg]

lemma weightedAngularAdjointDerivative_referenceWeightedFirst_coreWeight_one_apply
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hh : ContDiff ℝ ∞ h) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    let mu := fun y : R3 => referenceDensityFamily g L (lam,y)
    weightedAngularAdjointDerivative (coordinateDirection j) mu
      (referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j) x
      (coreWeightOperator hO hD (besselWeight 1) F x) =
        directionalFDeriv (coordinateDirection j)
          (fun y => mu y * nativeReferenceWeightedFirstScalarCoefficient g L lam δ R p h j y) x • F x +
        directionalFDeriv (coordinateDirection j)
          (fun y => mu y * nativeReferenceWeightedFirstDegreeCoefficient g L lam δ R p h j y) x • coreDegree hO hD F x -
        (∑ s : Fin 3, ∑ t : Fin 3,
          directionalFDeriv (coordinateDirection j)
            (fun y => mu y * nativeReferenceWeightedFirstRotationCoefficient g L lam δ R p h j s t y) x •
              coreRotation hO hD s t F x) := by
  dsimp only
  let mu := fun y : R3 => referenceDensityFamily g L (lam,y)
  let sigma := nativeReferenceWeightedFirstScalarCoefficient g L lam δ R p h j
  let d := nativeReferenceWeightedFirstDegreeCoefficient g L lam δ R p h j
  let tau (s t : Fin 3) := nativeReferenceWeightedFirstRotationCoefficient g L lam δ R p h j s t
  let K := referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j
  let I := inverseDegreeMultiplier hO hD
  let J := ContinuousLinearMap.id ℝ SphereL2-I
  let c : (Fin 2 ⊕ (Fin 3 × Fin 3)) → R3 → ℝ := fun z y =>
    match z with
    | Sum.inl n => if n=0 then mu y*sigma y else mu y*d y
    | Sum.inr st => mu y*tau st.1 st.2 y
  let T : (Fin 2 ⊕ (Fin 3 × Fin 3)) → (SphereL2 →L[ℝ] SphereL2) := fun z =>
    match z with
    | Sum.inl n => if n=0 then I else J
    | Sum.inr st => -normalizedRotation hO hD st.1 st.2
  have hmu : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hsigma : ContDiff ℝ ∞ sigma :=
    contDiff_nativeReferenceWeightedFirstScalarCoefficient g hg L lam δ R p h hh hδ hR j
  have hd : ContDiff ℝ ∞ d :=
    contDiff_nativeReferenceWeightedFirstDegreeCoefficient g hg L lam δ R p h hh hδ hR j
  have htau (s t : Fin 3) : ContDiff ℝ ∞ (tau s t) :=
    contDiff_nativeReferenceWeightedFirstRotationCoefficient g hg L lam δ R p h hh hδ hR j s t
  have hc (z : Fin 2 ⊕ (Fin 3 × Fin 3)) : ContDiff ℝ ∞ (c z) := by
    cases z with
    | inl n =>
      by_cases hn : n=0
      · simpa only [c,hn,if_true] using hmu.mul hsigma
      · simpa only [c,hn,if_false] using hmu.mul hd
    | inr st => exact hmu.mul (htau st.1 st.2)
  have hfield : (fun y : R3 => mu y • angularAdjoint K y) =
      (fun y : R3 => ∑ z : Fin 2 ⊕ (Fin 3 × Fin 3), c z y • T z) := by
    funext y
    change mu y • ContinuousLinearMap.adjoint (K y) = _
    rw [referenceWeightedFirstBaseNormalizedCoefficient_adjoint_fixed_rotation
      hO hD g hg L lam δ R p h j y]
    simp only [Fintype.sum_sum_type,Fin.sum_univ_two,Fintype.sum_prod_type,c,T,J,
      ite_true,if_neg (by decide : (1 : Fin 2) ≠ 0),
      smul_add,smul_sub,smul_smul,Finset.smul_sum,smul_neg,Finset.sum_neg_distrib]
    dsimp only [sigma,d,tau,I,mu]
    simp only [sub_eq_add_neg]
  have hcal := ActualAngularFiniteCoefficientDerivative.directionalFDeriv_fixed_scalar_sum
    (1 : ℝ) c hc T (coordinateDirection j) x
  simp only [one_smul] at hcal
  rw [← hfield] at hcal
  have he := congrArg (fun A : SphereL2 →L[ℝ] SphereL2 =>
    A (coreWeightOperator hO hD (besselWeight 1) F x)) hcal
  have hi : I (coreWeightOperator hO hD (besselWeight 1) F x)=F x :=
    inverseDegreeMultiplier_of_besselGraph hO hD _ _
      (coreWeightOperator_graph hO hD (besselWeight 1) F x)
  have hdegree : J (coreWeightOperator hO hD (besselWeight 1) F x)=coreDegree hO hD F x := by
    dsimp only [J]
    rw [ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,hi]
    exact coreWeight_one_sub_self_eq_degree hO hD F x
  simpa only [weightedAngularAdjointDerivative,K,Fintype.sum_sum_type,Fin.sum_univ_two,
    Fintype.sum_prod_type,c,T,ite_true,if_neg (by decide : (1 : Fin 2) ≠ 0),
    ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply,hi,hdegree,
    ← coreRotation_apply_eq_normalizedRotation hO hD,
    smul_neg,Finset.sum_neg_distrib,sub_eq_add_neg,mu,sigma,d,tau] using he

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
