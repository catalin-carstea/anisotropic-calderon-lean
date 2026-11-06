import Calderon.ActualFiniteHarmonicModelSecondAngularPairingBasis

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift BalancedAngularShift
  ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets ActualReferenceDDHigherCLMProducts
  ActualReferenceDDHigherSpectralGraphs ActualReferenceDDSpectralTransport ActualReferenceDDNormalizedCoefficient
  ActualReferenceParallelRaising ActualNormalizedSphereRotation ActualScalarPrincipalAdjoint NaturalAngularAdjoint
  ActualNormalizedSecondModelErrorAssembly ActualNormalizedSecondDriftNativeAdjunction
  ActualNormalizedSecondDriftDefectCoefficients ActualNormalizedSecondDriftDefectWeightedJets ActualNormalizedSecondMetricDrift
  ActualPhysicalMixedFirst ActualPhysicalMixedProfile ActualPhysicalMixedConnection ActualPhysicalPureAngular
  ReferenceDensityBounds NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  SmoothMetricFrame MovingFrameConnection PrincipalCommutator ConformalDepth SectionFiveErrorForms
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeWSymmetricFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeWSymmetricFunction
lemma nativeW_symmetric_inner_half_at
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (F G : smoothCompactFiniteSphereCore hO hD) (x y : R3) :
    ⟪nativeWSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p y
        (coreWeightOperator hO hD (besselWeight 2) F x),G x⟫_ℝ +
      ⟪F x,nativeWSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p y
        (coreWeightOperator hO hD (besselWeight 2) G x)⟫_ℝ =
    ⟪nativeWSymmetricHalfAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p y
        (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
  let u := F x
  let v := G x
  let u1 := coreWeightOperator hO hD (besselWeight 1) F x
  let v1 := coreWeightOperator hO hD (besselWeight 1) G x
  let u2 := coreWeightOperator hO hD (besselWeight 2) F x
  let v2 := coreWeightOperator hO hD (besselWeight 2) G x
  let uh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x
  let vh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x
  let I := inverseDegreeMultiplier hO hD
  let Id := ContinuousLinearMap.id ℝ SphereL2
  let J := nativeWSecondPairing hO hD F G x
  let Q := nativeWHalfPairing hO hD F G x
  have hJ (A : SphereL2 →L[ℝ] SphereL2) : J A = ⟪A u2,v⟫_ℝ+⟪u,A v2⟫_ℝ := by
    change ⟪v,A u2⟫_ℝ+⟪u,A v2⟫_ℝ = _
    rw [real_inner_comm (A u2) v]
  have hQ (A : SphereL2 →L[ℝ] SphereL2) : Q A = ⟪A uh,vh⟫_ℝ := by
    change ⟪vh,A uh⟫_ℝ = _
    rw [real_inner_comm (A uh) vh]
  have hJ_I2 : J (I.comp I) = (2 : ℝ)*Q I :=
    nativeW_pairing_inverse_square hO hD F G x
  have hJprofile (a : Fin 3) :
      J ((normalizedDerivative hF hO hD a).comp (Id-(2 : ℝ) • I)) =
        J ((normalizedRaising hF hO hD a).comp (Id-I)) :=
    nativeW_pairing_profile hO hD hF F G x a
  have hJconnection (a b c : Fin 3) :
      J ((normalizedRotation hO hD b c).comp ((normalizedDerivative hF hO hD a).comp (Id-I))) =
        -J ((normalizedRaising hF hO hD a).comp (normalizedRotation hO hD b c)) :=
    nativeW_pairing_connection hO hD hF F G x a b c
  have hJpure (a b : Fin 3) :
      J ((normalizedDerivative hF hO hD b).comp ((normalizedDerivative hF hO hD a).comp (Id-I))) =
        J ((normalizedRaising hF hO hD a).comp ((normalizedRaising hF hO hD b).comp (Id+I))) :=
    nativeW_pairing_pure hO hD hF F G x a b
  have hJrotation (b c : Fin 3) : J ((normalizedRotation hO hD b c).comp I) = 0 :=
    nativeW_pairing_rotation hO hD F G x b c
  have hJDensity (a : Fin 3) : J ((normalizedDerivative hF hO hD a).comp I) =
      Q (balancedDerivative hF hO hD a+balancedRaising hF hO hD a) :=
    nativeW_pairing_density hO hD hF F G x a
  have hJdiagonal (A : SphereL2 →L[ℝ] SphereL2) (hA : PreservesSphereSpectralGraphs hO hD A) :
      J (A.comp I) = Q (A+ContinuousLinearMap.adjoint A) :=
    nativeW_pairing_diagonal hO hD F G x A hA
  have hJzero (A : SphereL2 →L[ℝ] SphereL2) (hA : PreservesSphereSpectralGraphs hO hD A) :
      J (ContinuousLinearMap.adjoint A) = J A :=
    nativeW_pairing_zero hO hD F G x A hA
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  have hh : ContDiff ℝ ∞ h := contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam
  let mu : R3 → ℝ := fun z => referenceDensityFamily g1 L (lam,z)
  have hmu : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  let B (j : Fin 3) := referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p h j
  have hB (j : Fin 3) : ContDiff ℝ ∞ (B j) :=
    contDiff_referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p hδ hR h hh j
  have hBg (j : Fin 3) (y : R3) : PreservesSphereSpectralGraphs hO hD (B j y) :=
    preservesSphereSpectralGraphs_referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p h j y
  let Y (j : Fin 3) := weightedAngularAdjointDerivative (coordinateDirection j) mu (B j)
  have hYg (j : Fin 3) (y : R3) : PreservesSphereSpectralGraphs hO hD (Y j y) :=
    preservesSphereSpectralGraphs_directionalFDeriv hO hD
      (fun z => mu z • angularAdjoint (B j) z)
      (hmu.smul (contDiff_angularAdjoint (B j) (hB j)))
      (fun z => preservesSphereSpectralGraphs_smul hO hD _ _
        (preservesSphereSpectralGraphs_adjoint hO hD (B j z) (hBg j z))) y (coordinateDirection j)
  let B0 := referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g1 hg1 L lam δ R p h
  have hB0g (y : R3) : PreservesSphereSpectralGraphs hO hD (B0 y) :=
    preservesSphereSpectralGraphs_referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g1 hg1 L lam δ R p h y
  let WN := nativeWSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p
  let WS := nativeWSymmetricHalfAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p
  have hinner (y : R3) : J (WN y) = Q (WS y) := by
    dsimp only [WN,WS]
    unfold nativeWSecondAngularCoefficient nativeWSymmetricHalfAngularCoefficient
    dsimp only
    change J (_ : SphereL2 →L[ℝ] SphereL2) = Q (_ : SphereL2 →L[ℝ] SphereL2)
    have hY (j : Fin 3) : J ((Y j y).comp I) = Q (Y j y+ContinuousLinearMap.adjoint (Y j y)) :=
      hJdiagonal (Y j y) (hYg j y)
    have hZero := hJzero (B0 y) (hB0g y)
    dsimp only [I,Id] at hJ_I2 hJprofile hJconnection hJpure hJrotation hJDensity
    dsimp only [Y,B,mu,h,I] at hY
    dsimp only [B0,h] at hZero
    simp only [map_add,map_sub,map_smul,map_sum,hJ_I2,hJprofile,hJconnection,hJpure,hJrotation,hJDensity,
      hY,hZero,neg_smul,smul_neg,neg_neg,zero_smul,smul_zero,
      Finset.sum_const_zero,sub_self,add_zero]
    simp only [map_add,map_smul,smul_eq_mul]
    ring
  have he := hinner y
  rw [hJ,hQ] at he
  exact he

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
