import Calderon.ProfileRadiusJets
import Calderon.ActualFiniteHarmonicModelConnectionFrameDerivative
import Calderon.ActualFiniteHarmonicModelConnectionSymmetric
import Calderon.ActualFiniteHarmonicModelConnectionCommutator

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
  ActualReferenceParallelRaising ActualReferenceDDNormalizedCoefficient
  AmbientReferenceRaising AmbientReferenceCovariantCore SmoothMetricFrame MovingFrameConnection
  PrincipalCommutator ConformalDepth RadiusProfile
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeRawCovectorZeroFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeRawCovectorZeroFunction

def nativeReferenceProfileFrameDerivative
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) (a b : Fin 3) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  coreScalar hO hD
    (referenceFrameDerivative g L lam a
      (referenceFrameDerivative g L lam b (fun y => Real.log (referenceRadius δ R p L y))))
    (contDiff_referenceFrameDerivative g hg L lam a _
      (contDiff_referenceFrameDerivative g hg L lam b _
        (_root_.OAI.AnisotropicCalderon.ConformalDepth.contDiff_log_referenceRadius_profile δ R L p hδ hR)))

def nativeReferenceCovectorZeroRawAction
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) (a b : Fin 3) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := by
  let A (c : Fin 3) := nativeReferenceConnectionAction hO hD g hg L lam c
  let P (c : Fin 3) := nativeReferenceProfileScalar hO hD g hg L lam δ R p hδ hR c
  let N := coreDegree hO hD
  let Gamma (c : Fin 3) := coreScalar hO hD
    (fun y => referenceFrameConnectionCoefficient g L lam y (referenceMetricGramFrame g L (lam,y) a) c b)
    (contDiff_referenceFrameConnectionCoefficient_field g hg L lam _
      (contDiff_referenceMetricGramFrame_slice g hg L lam a) c b)
  exact nativeReferenceConnectionFrameDerivative hO hD g hg L lam a b +
    nativeReferenceProfileFrameDerivative hO hD g hg L lam δ R p hδ hR a b * N +
    A a * (A b+P b*N) - (∑ c : Fin 3, Gamma c*(A c+P c*N)) +
    P a * (A b+P b*N) * N

lemma referenceWeightedZeroBaseNormalizedCoefficient_coreWeight_one_apply
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) (a : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    referenceWeightedZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p a x
      (coreWeightOperator hO hD (besselWeight 1) F x) =
      (nativeReferenceConnectionAction hO hD g hg L lam a +
        nativeReferenceProfileScalar hO hD g hg L lam δ R p hδ hR a * coreDegree hO hD) F x := by
  have hi : inverseDegreeMultiplier hO hD (coreWeightOperator hO hD (besselWeight 1) F x)=F x :=
    inverseDegreeMultiplier_of_besselGraph hO hD _ _
      (coreWeightOperator_graph hO hD (besselWeight 1) F x)
  have hd := coreWeight_one_sub_self_eq_degree hO hD F x
  unfold referenceWeightedZeroBaseNormalizedCoefficient
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply]
  rw [hi,hd,← nativeReferenceConnectionAction_apply_eq_normalized hO hD g hg L lam a F x]
  rfl


lemma nativeReferenceWeightedZeroRaw_coreWeight_one_apply
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) (a : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    let Z := nativeReferenceConnectionAction hO hD g hg L lam a +
      nativeReferenceProfileScalar hO hD g hg L lam δ R p hδ hR a * coreDegree hO hD
    coreWeightOperator hO hD (besselWeight 1) (Z F) x =
      Z (coreWeightOperator hO hD (besselWeight 1) F) x := by
  dsimp only
  let W := coreWeightOperator hO hD (besselWeight 1)
  let A := nativeReferenceConnectionAction hO hD g hg L lam a
  let P := nativeReferenceProfileScalar hO hD g hg L lam δ R p hδ hR a
  have hP : Commute W P := by
    dsimp only [W,P,nativeReferenceProfileScalar]
    exact scalarCentral_coreWeightOperator hO hD (besselWeight 1) _ _
  have hPE := congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) =>
    T (coreDegree hO hD F) x) hP.eq
  change W (P (coreDegree hO hD F)) x=P (W (coreDegree hO hD F)) x at hPE
  have hAW : A (W F) x=normalizedReferenceAngularConnection hO hD g L lam x
      (referenceMetricGramFrame g L (lam,x) a) (coreWeightOperator hO hD (besselWeight 2) F x) := by
    dsimp only [A,W]
    rw [nativeReferenceConnectionAction_apply_eq_normalized hO hD g hg L lam a
      (coreWeightOperator hO hD (besselWeight 1) F) x,coreWeight_one_twice_apply hO hD F x]
  have hNW : coreDegree hO hD (W F) x=
      coreWeightOperator hO hD (besselWeight 2) F x-W F x := by
    rw [← coreWeight_one_sub_self_eq_degree hO hD (W F) x]
    dsimp only [W]
    rw [coreWeight_one_twice_apply hO hD F x]
  change W ((A+P*coreDegree hO hD) F) x=(A+P*coreDegree hO hD) (W F) x
  simp only [LinearMap.add_apply,Module.End.mul_apply,map_add,Submodule.coe_add,Pi.add_apply]
  rw [hPE,hAW]
  dsimp only [W,A] at ⊢
  rw [coreWeight_nativeReferenceConnectionAction_apply hO hD g hg L lam a F x]
  simp only [P,nativeReferenceProfileScalar,coreScalar,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk]
  rw [coreWeight_one_degree_apply hO hD F x,hNW]


lemma referenceCovectorZeroBaseNormalizedCoefficient_coreWeight_two_apply
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) (a b : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    referenceCovectorZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p a b x
      (coreWeightOperator hO hD (besselWeight 2) F x) =
        nativeReferenceCovectorZeroRawAction hO hD g hg L lam δ R p hδ hR a b F x := by
  let I := inverseDegreeMultiplier hO hD
  let U := coreWeightOperator hO hD (besselWeight 1) F
  let V := coreWeightOperator hO hD (besselWeight 2) F x
  let A (c : Fin 3) := nativeReferenceConnectionAction hO hD g hg L lam c
  let P (c : Fin 3) := nativeReferenceProfileScalar hO hD g hg L lam δ R p hδ hR c
  let Z (c : Fin 3) := A c+P c*coreDegree hO hD
  let B (c : Fin 3) := referenceWeightedZeroBaseNormalizedCoefficient hO hD g hg L lam δ R p c x
  have hUV : (U x,V) ∈ sphereBesselGraph hO hD 1 := by
    dsimp only [U,V]
    rw [← coreWeight_one_twice_apply hO hD F x]
    exact coreWeightOperator_graph hO hD (besselWeight 1)
      (coreWeightOperator hO hD (besselWeight 1) F) x
  have hi2 : I V=U x := inverseDegreeMultiplier_of_besselGraph hO hD _ _ hUV
  have hi1 : I (U x)=F x := inverseDegreeMultiplier_of_besselGraph hO hD _ _
    (coreWeightOperator_graph hO hD (besselWeight 1) F x)
  have hd : U x-F x=coreDegree hO hD F x := coreWeight_one_sub_self_eq_degree hO hD F x
  have hZ (c : Fin 3) (G : smoothCompactFiniteSphereCore hO hD) :
      B c (coreWeightOperator hO hD (besselWeight 1) G x)=Z c G x :=
    referenceWeightedZeroBaseNormalizedCoefficient_coreWeight_one_apply hO hD g hg L lam δ R p hδ hR c G x
  have hBU (c : Fin 3) : B c (U x)=Z c F x := by
    simpa only [U] using hZ c F
  have hZ2 (c : Fin 3) : B c V=Z c U x := by
    have he := hZ c U
    simpa only [U,coreWeight_one_twice_apply hO hD F x,V] using he
  have hWZ (c : Fin 3) : coreWeightOperator hO hD (besselWeight 1) (Z c F) x=Z c U x :=
    nativeReferenceWeightedZeroRaw_coreWeight_one_apply hO hD g hg L lam δ R p hδ hR c F x
  have hcomp : normalizedReferenceAngularConnection hO hD g L lam x
      (referenceMetricGramFrame g L (lam,x) a) (B b V)=A a (Z b F) x := by
    rw [hZ2 b,← hWZ b]
    exact (nativeReferenceConnectionAction_apply_eq_normalized hO hD g hg L lam a (Z b F) x).symm
  have hCoreDiff : U-F=coreDegree hO hD F := by
    apply Subtype.ext
    funext y
    change coreWeightOperator hO hD (besselWeight 1) F y-F y=coreDegree hO hD F y
    exact coreWeight_one_sub_self_eq_degree hO hD F y
  have hLast : B b V-B b (U x)=Z b (coreDegree hO hD F) x := by
    rw [hZ2 b,hZ b F]
    have he := congrArg (fun G : smoothCompactFiniteSphereCore hO hD => G x) (map_sub (Z b) U F)
    change Z b (U-F) x=Z b U x-Z b F x at he
    rw [← he,hCoreDiff]
  change directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
      (fun y => normalizedReferenceAngularConnection hO hD g L lam y (referenceMetricGramFrame g L (lam,y) b)) x (I V) +
    directionalFDeriv (referenceMetricGramFrame g L (lam,x) a)
      (referenceFrameDerivative g L lam b (fun y => Real.log (referenceRadius δ R p L y))) x •
      (I V-I (I V)) +
    normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) a) (B b V) -
    (∑ c : Fin 3, referenceFrameConnectionCoefficient g L lam x (referenceMetricGramFrame g L (lam,x) a) c b • B c (I V)) +
    referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x •
      (B b V-B b (I V)) = _
  rw [hi2,hi1,hd,hcomp,hLast,nativeReferenceConnectionFrameDerivative_normalized_apply hO hD g hg L lam a b F x]
  simp only [hBU]
  unfold nativeReferenceCovectorZeroRawAction
  dsimp only
  simp only [A,P,Z,nativeReferenceProfileFrameDerivative,nativeReferenceProfileScalar,
    LinearMap.add_apply,LinearMap.sub_apply,LinearMap.sum_apply,Module.End.mul_apply,
    coreScalar,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk,Submodule.coe_add,Submodule.coe_sub,
    Submodule.coe_sum,Pi.add_apply,Pi.sub_apply,Finset.sum_apply,referenceFrameDerivative,directionalFDeriv]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
