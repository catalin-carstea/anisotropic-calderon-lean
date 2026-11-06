import Calderon.ActualPhysicalDensityErrorDecomposition
import Calderon.ActualDensitySigmaRadiusDoubleAction
import Calderon.ActualNativePhysicalModelInputDictionary
import Calderon.ActualNativePhysicalModelRaisingDictionary
import Calderon.ActualOriginalFiniteReferenceModelDefinitions
import Calderon.ActualFiniteCoreSobolevRepresentation
import Calderon.ActualFiniteHarmonicModelConnectionSymmetric
import Calderon.SphereSobolevAngularRaisingThreeHalfGraph

/-! Full before-source expansion and verified API bundle:
actual-finite-physical-model-dictionary-author-oct19-v001/BEFORE-SOURCE-RECEIPT.json.
Concrete original finite-input dictionary. No quantitative or transfer-existence claim. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore
  ActualFiniteHarmonicModel ActualFiniteHarmonicAmbient SpectralCoreRegularity
  SpectralWeightedGraph SphereHilbertDecomposition NormalCoordinatesFrame SmoothMetricFrame MovingFrameConnection AmbientReferenceRaising
  ActualReferenceModelTrace ActualReferenceParallelRaising ActualPhysicalMixedNative
  ActualPhysicalPureAngular ActualNormalizedSecondMetricDrift
  ActualNormalizedSecondDriftAngularAllocation ActualNormalizedSecondModelErrorAssembly
  ReferenceDensityBounds NormalizedPrincipalMetric ConformalDepth RadiusProfile
  AngularShiftGraph HarmonicDerivativeOperator SmoothSphereRotationProjection
  PrincipalCommutator BoundedAngularShift

lemma finiteCoreSobolevLift_negative_half_eq_zero_inclusion
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (F : smoothCompactFiniteSphereCore hO hD) (y : R3) :
    finiteCoreSobolevLift hO hD (-(1/2 : ℝ)) F y =
      sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD (F.val y)) := by
  apply sphereSobolev_ext (-(1/2 : ℝ))
  intro k
  rw [sphereSobolevCoefficientL_finiteCoreSobolevLift,
    sphereSobolevCoefficientL_inclusion,sphereSobolevCoefficientL_zeroEquiv]

lemma referenceLowerWeightedHorizontalAction_finiteCoreSobolevLift
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q δ A : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hA : 0 < A)
    (F : smoothCompactFiniteSphereCore hO hD) (y : R3) (i : Fin 3) :
    referenceLowerHorizontalAction g L q (finiteCoreSobolevLift hO hD (1/2 : ℝ) F) y i +
      referenceRadiusHorizontalLogDerivative g L q (referenceRadius δ A p L) y i •
        sphereSobolevShiftedDegreeL (1/2 : ℝ)
          (finiteCoreSobolevLift hO hD (1/2 : ℝ) F y) =
      finiteCoreSobolevLift hO hD (-(1/2 : ℝ))
        (coreReferenceInput hO hD g hg L q δ A p i hδ hA F) y := by
  let U := finiteCoreSobolevLift hO hD (1/2 : ℝ) F
  let X := referenceMetricGramFrame g L (q,y) i
  let f := referenceRadiusHorizontalLogDerivative g L q (referenceRadius δ A p L) y i
  let Gamma := fun a b : Fin 3 => referenceFrameConnectionCoefficient g L q y X a b
  have hFrame : conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i) = X :=
    (congrArg (fun T : R3 →L[ℝ] R3 => T (coordinateVector i))
      (conformalReferenceGramFrameOperatorJoint_eq_frameOperator g L (q,y))).trans
        ((frameOperator_coordinateVector _ i).trans
          (conformalReferenceGramFrame_eq_referenceMetricGramFrame g L q y i))
  have hScalar : f = referenceFrameDerivative g L q i
      (fun x => Real.log (referenceRadius δ A p L x)) y := by
    dsimp only [f]
    unfold referenceRadiusHorizontalLogDerivative referenceFrameDerivative
    exact congrArg (fderiv ℝ (fun x => Real.log (referenceRadius δ A p L x)) y) hFrame
  have hUSmooth : ContDiff ℝ ∞ U := contDiff_finiteCoreSobolevLift hO hD (1/2 : ℝ) F
  have hUDiff := hUSmooth.differentiable (by simp) y
  have hFDiff := F.property.1.differentiable (by simp) y
  apply sphereSobolev_ext (-(1/2 : ℝ))
  intro k
  let c := sphereHarmonicCoordinate hO hD k
  let v := c (F.val y)
  have hFunction : (fun x : R3 => sphereSobolevCoefficientL (1/2 : ℝ) k (U x)) =
      (fun x : R3 => c (F.val x)) :=
    funext (fun x => sphereSobolevCoefficientL_finiteCoreSobolevLift hO hD (1/2 : ℝ) F x k)
  have hNativeDerivative := congrArg
    (fun T : R3 →L[ℝ] harmonicSphereSubspace k => T X)
    (((sphereSobolevCoefficientL (1/2 : ℝ) k).hasFDerivAt.comp y hUDiff.hasFDerivAt).fderiv)
  have hFunctionDerivative := congrArg
    (fun V : R3 → harmonicSphereSubspace k => fderiv ℝ V y X) hFunction
  have hCoreDerivative := congrArg
    (fun T : R3 →L[ℝ] harmonicSphereSubspace k => T X)
    (fderiv_sphereHarmonicCoordinate hO hD k F.val y hFDiff)
  have hBase : sphereSobolevCoefficientL (1/2 : ℝ) k (fderiv ℝ U y X) =
      c (fderiv ℝ F.val y X) := by
    simpa (config := { instances := true }) only [ContinuousLinearMap.comp_apply,c]
      using hNativeDerivative.symm.trans (hFunctionDerivative.trans hCoreDerivative)
  have hUValue : sphereSobolevCoefficientL (1/2 : ℝ) k (U y) = v :=
    sphereSobolevCoefficientL_finiteCoreSobolevLift hO hD (1/2 : ℝ) F y k
  have hCoeffIndex : (sphereSobolevCoefficientL (-(1/2 : ℝ)) k :
      SphereSobolev (-(1/2 : ℝ)) →L[ℝ] harmonicSphereSubspace k) =
      sphereSobolevCoefficientL ((1/2 : ℝ)-1) k := by
    change sphereSobolevCoefficientL (-(1/2 : ℝ)) k =
      sphereSobolevCoefficientL ((1/2 : ℝ)-1) k
    rw [show (1/2 : ℝ)-1 = (-(1/2 : ℝ)) by norm_num]
  have hRot (a b : Fin 3) : sphereSobolevCoefficientL (-(1/2 : ℝ)) k
      (sphereSobolevRotationL (1/2 : ℝ) a b (U y)) = harmonicSphereRotation k a b v := by
    have hMap := congrArg
      (fun T : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] harmonicSphereSubspace k =>
        T (sphereSobolevRotationL (1/2 : ℝ) a b (U y))) hCoeffIndex
    exact hMap.trans ((sphereSobolevCoefficientL_rotation (1/2 : ℝ) a b k (U y)).trans
      (congrArg (harmonicSphereRotation k a b) hUValue))
  have hDegree : sphereSobolevCoefficientL (-(1/2 : ℝ)) k
      (sphereSobolevShiftedDegreeL (1/2 : ℝ) (U y)) = (k : ℝ) • v := by
    have hMap := congrArg
      (fun T : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] harmonicSphereSubspace k =>
        T (sphereSobolevShiftedDegreeL (1/2 : ℝ) (U y))) hCoeffIndex
    exact hMap.trans ((sphereSobolevCoefficientL_shiftedDegree (1/2 : ℝ) k (U y)).trans
      (congrArg (fun w : harmonicSphereSubspace k => (k : ℝ) • w) hUValue))
  have hHorizontal : sphereSobolevCoefficientL (-(1/2 : ℝ)) k
      (referenceLowerHorizontalAction g L q U y i) =
      c (fderiv ℝ F.val y X) + (1/2 : ℝ) •
        ∑ a : Fin 3, ∑ b : Fin 3, Gamma a b • harmonicSphereRotation k a b v := by
    simp (config := { instances := true }) only
      [referenceLowerHorizontalAction,referenceLowerHorizontalAngularL,
        ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
        map_add,map_smul,map_sum,sphereSobolevCoefficientL_inclusion,hBase,hRot,Gamma,X]
  have hCoreHorizontal : c ((coreReferenceHorizontal hO hD g hg L q i F).val y) =
      c (fderiv ℝ F.val y X) + (1/2 : ℝ) •
        ∑ a : Fin 3, ∑ b : Fin 3, Gamma a b • harmonicSphereRotation k a b v := by
    have h := congrArg c (coreReferenceHorizontal_apply hO hD g hg L q i F y)
    simpa (config := { instances := true }) only
      [coreFrameHorizontalAction,map_add,map_smul,map_sum,coreRotation,
        coreBlockOperator_coordinate,c,X,Gamma,v] using h
  have hCoreDegree : c ((coreDegree hO hD F).val y) = (k : ℝ) • v :=
    coreWeightOperator_graph hO hD (fun n => (n : ℝ)) F y k
  have hInput : c ((coreReferenceInput hO hD g hg L q δ A p i hδ hA F).val y) =
      c ((coreReferenceHorizontal hO hD g hg L q i F).val y) +
        f • c ((coreDegree hO hD F).val y) := by
    simp (config := { instances := true }) only
      [coreReferenceInput,LinearMap.add_apply,Module.End.mul_apply,coreScalar,
        LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk,Submodule.coe_add,
        Pi.add_apply,map_add,map_smul,← hScalar,c]
  have hBoth := congrArg₂ (fun a b : harmonicSphereSubspace k => a+f • b) hHorizontal hDegree
  have hCoreBoth := congrArg₂ (fun a b : harmonicSphereSubspace k => a+f • b)
    hCoreHorizontal hCoreDegree
  simpa (config := { instances := true }) only
    [map_add,map_smul,sphereSobolevCoefficientL_finiteCoreSobolevLift,U,f,c]
    using hBoth.trans (hCoreBoth.symm.trans hInput.symm)


lemma sphereSobolevAngularCoordinateTranspose_threeHalf_finiteCore
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (F : smoothCompactFiniteSphereCore hO hD) (y : R3) (i : Fin 3) :
    sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i
      (finiteCoreSobolevLift hO hD (3/2 : ℝ) F y) =
    finiteCoreSobolevLift hO hD (1/2 : ℝ) (coreRaising hO hD hF i F) y := by
  let Z := sphereSobolevZeroEquiv hO hD
  let I30 := sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
  let I10 := sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let u := finiteCoreSobolevLift hO hD (3/2 : ℝ) F y
  let A := sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i
  have hInput : I30 u = Z (F.val y) :=
    (finiteCoreSobolevLift_representation hO hD (3/2 : ℝ) (by norm_num) F).2.2.2.1 y
  have hGraph := sphereSobolevAngularCoordinateTransposeL_threeHalf_raisingGraph
    hF hO hD i u
  change (Z.symm (I30 u),Z.symm (I10 (A u))) ∈ sphereRaisingGraph hF hO hD i at hGraph
  rw [hInput,Z.symm_apply_apply] at hGraph
  have hOutput : Z.symm (I10 (A u)) = (coreRaising hO hD hF i F).val y :=
    sphereRaisingGraph_output_unique hF hO hD i (F.val y) _ _ hGraph
      (coreRaising_graph hO hD hF i F y)
  have hOutputZ := congrArg Z hOutput
  have hCoarse : I10 (A u) = Z ((coreRaising hO hD hF i F).val y) :=
    (Z.apply_symm_apply (I10 (A u))).symm.trans hOutputZ
  have hTarget : I10 (finiteCoreSobolevLift hO hD (1/2 : ℝ)
      (coreRaising hO hD hF i F) y) = Z ((coreRaising hO hD hF i F).val y) :=
    (finiteCoreSobolevLift_representation hO hD (1/2 : ℝ) (by norm_num)
      (coreRaising hO hD hF i F)).2.2.2.1 y
  exact (sphereSobolevInclusionL_injective (1/2 : ℝ) 0 (by norm_num))
    (hCoarse.trans hTarget.symm)

lemma normalizedReferenceAngularConnection_finiteCore
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L q : ℝ) (F : smoothCompactFiniteSphereCore hO hD)
    (y X : R3) :
    normalizedReferenceAngularConnection hO hD g L q y X
      ((coreWeightOperator hO hD (besselWeight 1) F).val y) =
    (1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3,
      referenceFrameConnectionCoefficient g L q y X a b •
        (coreRotation hO hD a b F).val y := by
  have hGraph := normalizedReferenceAngularConnection_graph hO hD g L q y X
    (F.val y) ((coreWeightOperator hO hD (besselWeight 1) F).val y)
    (coreWeightOperator_graph hO hD (besselWeight 1) F y)
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  change sphereHarmonicCoordinate hO hD k
      (normalizedReferenceAngularConnection hO hD g L q y X
        ((coreWeightOperator hO hD (besselWeight 1) F).val y)) =
    sphereHarmonicCoordinate hO hD k ((1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3,
      referenceFrameConnectionCoefficient g L q y X a b • (coreRotation hO hD a b F).val y)
  rw [hGraph k]
  simp only [harmonicReferenceAngularConnection,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply,map_smul,map_sum,coreRotation,coreBlockOperator_coordinate]

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

include hData hcalc τ0 in
lemma sphereSobolevAngularCoordinateTranspose_half_finiteCore
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (i : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) :
    sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
      (finiteCoreSobolevLift hO hD (1/2 : ℝ) F y) =
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD ((coreRaising hO hD hF i F).val y)) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  have hCompatibility := referenceAngularCoordinateTranspose_high_lower_inclusion
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy i
      (finiteCoreSobolevLift hO hD (3/2 : ℝ) F y)
  have hInput := sphereSobolevInclusionL_finiteCoreSobolevLift hO hD
    (3/2 : ℝ) (1/2 : ℝ) (by norm_num) F y
  have hRaise := sphereSobolevAngularCoordinateTranspose_threeHalf_finiteCore hF hO hD F y i
  have hIncluded := congrArg J hRaise
  have hLift := sphereSobolevInclusionL_finiteCoreSobolevLift hO hD
    (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (coreRaising hO hD hF i F) y
  have hNegative := finiteCoreSobolevLift_negative_half_eq_zero_inclusion hO hD
    (coreRaising hO hD hF i F) y
  have hInputApplied := congrArg
    (sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i) hInput
  exact hInputApplied.symm.trans (hCompatibility.symm.trans
    (hIncluded.trans (hLift.trans hNegative)))

lemma referenceWeightedCovectorSecondField_finiteCore
    (hg : IsAdmissibleMetric g) (q δ A : ℝ) (p : ℕ) (hδ : 0 < δ) (hA : 0 < A)
    (F : smoothCompactFiniteSphereCore hO hD)
    (r : FiniteHarmonicAmbientRepresentative hO hD F) (y : R3) (i j : Fin 3) :
    let G := fun k : Fin 3 => coreReferenceInput hO hD g hg L q δ A p k hδ hA F
    referenceWeightedCovectorSecondField hO hD g hg L q δ A p i j
      (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) y =
    (coreReferenceInput hO hD g hg L q δ A p i hδ hA (G j)).val y -
      ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q y
        (referenceMetricGramFrame g L (q,y) i) k j • (G k).val y := by
  intro G
  let X := referenceMetricGramFrame g L (q,y) i
  let f := referenceFrameDerivative g L q i (fun x => Real.log (referenceRadius δ A p L x)) y
  have hInput (k : Fin 3) :
      referenceWeightedInputField hO hD g hg L q 1 k
        (fun x => Real.log (referenceRadius δ A p L x))
        (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) = (G k).val :=
    funext (coreReferenceInput_representative hO hD g hg L q δ A p k hδ hA F r)
  have hDerivative := congrArg (fun v : R3 → SphereL2 => directionalFDeriv X v y) (hInput j)
  have hBessel := coreReferenceWeightedBessel_representative hO hD g hg L q δ A p j hδ hA F r y
  have hAngular := normalizedReferenceAngularConnection_finiteCore hO hD g L q (G j) y X
  have hDegree := coreWeight_one_sub_self_eq_degree hO hD (G j) y
  have hCore : (coreReferenceInput hO hD g hg L q δ A p i hδ hA (G j)).val y =
      fderiv ℝ (G j).val y X +
      (1/2 : ℝ) • (∑ a : Fin 3, ∑ b : Fin 3,
        referenceFrameConnectionCoefficient g L q y X a b • (coreRotation hO hD a b (G j)).val y) +
      f • (coreDegree hO hD (G j)).val y := by
    simp only [coreReferenceInput,LinearMap.add_apply,Module.End.mul_apply,coreScalar,
      LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk,Submodule.coe_add,Pi.add_apply,
      coreReferenceHorizontal_apply,coreFrameHorizontalAction,f,X]
  unfold referenceWeightedCovectorSecondField
  rw [hDerivative,hBessel,hAngular]
  have hInputPoint (k : Fin 3) := congrFun (hInput k) y
  simp_rw [hInputPoint]
  rw [hDegree,hCore]
  change (fderiv ℝ (G j).val y X + _) - _ + f • _ =
    (fderiv ℝ (G j).val y X + _ + f • _) - _
  abel

lemma referenceDensityCovariantWeightedSecond_finiteCore
    (hg : IsAdmissibleMetric g) (q δ A : ℝ) (p : ℕ) (hδ : 0 < δ) (hA : 0 < A)
    (F : smoothCompactFiniteSphereCore hO hD)
    (r : FiniteHarmonicAmbientRepresentative hO hD F) (y : R3) (i j : Fin 3) :
    let R := referenceRadius δ A p L
    let u := finiteCoreSobolevLift hO hD (3/2 : ℝ) F
    let D := fun k x => referenceHighWeightedHorizontalAction g L q R u x k
    let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    let K := (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)).comp
      (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap
    referenceLowerWeightedHorizontalAction g L q R (D j) y i -
      (∑ k : Fin 3, referenceFrameConnectionCoefficient g L q y
        (referenceMetricGramFrame g L (q,y) i) k j • J (D k y)) =
    K (referenceWeightedCovectorSecondField hO hD g hg L q δ A p i j
      (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) y) := by
  intro R u D J K
  let G := fun k : Fin 3 => coreReferenceInput hO hD g hg L q δ A p k hδ hA F
  have hInputLift (k : Fin 3) : D k = finiteCoreSobolevLift hO hD (1/2 : ℝ) (G k) := by
    funext x
    exact referenceHighWeightedHorizontalAction_finiteCoreSobolevLift hO hD g hg L q δ A p
      hδ hA F x k
  have hLow := referenceLowerWeightedHorizontalAction_finiteCoreSobolevLift hO hD g hg L q δ A p
    hδ hA (G j) y i
  have hFirst : referenceLowerWeightedHorizontalAction g L q R (D j) y i =
      K ((coreReferenceInput hO hD g hg L q δ A p i hδ hA (G j)).val y) := by
    rw [hInputLift j]
    exact hLow.trans (finiteCoreSobolevLift_negative_half_eq_zero_inclusion hO hD _ y)
  have hIncluded (k : Fin 3) : J (D k y) = K ((G k).val y) := by
    rw [congrFun (hInputLift k) y]
    exact (sphereSobolevInclusionL_finiteCoreSobolevLift hO hD
      (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (G k) y).trans
      (finiteCoreSobolevLift_negative_half_eq_zero_inclusion hO hD (G k) y)
  have hCovector := referenceWeightedCovectorSecondField_finiteCore g L hO hD hg q δ A p hδ hA F r y i j
  rw [hFirst,hCovector]
  simp only [map_sub,map_sum,map_smul]
  exact congrArg (fun v : SphereSobolev (-(1/2 : ℝ)) =>
      K ((coreReferenceInput hO hD g hg L q δ A p i hδ hA (G j)).val y)-v)
    (Finset.sum_congr rfl (fun k _ => congrArg
      (fun v : SphereSobolev (-(1/2 : ℝ)) =>
        referenceFrameConnectionCoefficient g L q y (referenceMetricGramFrame g L (q,y) i) k j • v)
      (hIncluded k)))

lemma referencePhysicalDensity_weighted_covector_finiteCore
    (hg : IsAdmissibleMetric g) (g2 : MatrixField)
    (q δ A : ℝ) (p : ℕ) (hδ : 0 < δ) (hA : 0 < A)
    (F : smoothCompactFiniteSphereCore hO hD)
    (r : FiniteHarmonicAmbientRepresentative hO hD F) (y : R3) :
    let R := referenceRadius δ A p L
    let u := finiteCoreSobolevLift hO hD (3/2 : ℝ) F
    let D := fun k x => referenceHighWeightedHorizontalAction g L q R u x k
    let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    let K := (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)).comp
      (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap
    K (referenceWeightedCovectorTrace hO hD g hg L q δ A p
      (referenceNormalizedPrincipalDifference g g2 L q)
      (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) y) =
    R y • (∑ i : Fin 3, ∑ j : Fin 3,
      referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
        (referenceLowerWeightedHorizontalAction g L q R (D j) y i -
          ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q y
            (referenceMetricGramFrame g L (q,y) i) k j • J (D k y))) := by
  intro R u D J K
  simp only [referenceWeightedCovectorTrace,map_smul,map_sum]
  apply congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => R y • z)
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← referenceDensityPrincipalFrameCoefficient_eq_physicalMixedQFrameCoefficient g g2 L q y i j]
  exact congrArg
    (fun z : SphereSobolev (-(1/2 : ℝ)) => referenceDensityPrincipalFrameCoefficient g g2 L q y i j • z)
    (referenceDensityCovariantWeightedSecond_finiteCore g L hO hD hg q δ A p hδ hA F r y i j).symm

include hData hcalc τ0 in
lemma referencePhysicalDensity_sigma_mixed_finiteCore
    (hg : IsAdmissibleMetric g) (g2 : MatrixField) (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (δ A : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hA : 0 < A)
    (F : smoothCompactFiniteSphereCore hO hD)
    (r : FiniteHarmonicAmbientRepresentative hO hD F) (y : R3) (hy : ‖y-y0‖ ≤ ρ) :
    let R := referenceRadius δ A p L
    let u := finiteCoreSobolevLift hO hD (3/2 : ℝ) F
    let D := fun k x => referenceHighWeightedHorizontalAction g L q R u x k
    let K := (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)).comp
      (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap
    K (physicalMixedNativeRaising hF hO hD g hg L q δ A p
      (referenceNormalizedPrincipalDifference g g2 L q)
      (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) y) =
    (2 : ℝ) • (∑ i : Fin 3, ∑ j : Fin 3,
      (referenceDensityPrincipalFrameCoefficient g g2 L q y i j -
        if i=j then (1 : ℝ) else 0) •
        sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i (D j y)) := by
  intro R u D K
  let G := fun k : Fin 3 => coreReferenceInput hO hD g hg L q δ A p k hδ hA F
  have hInputLift (k : Fin 3) : D k y = finiteCoreSobolevLift hO hD (1/2 : ℝ) (G k) y :=
    referenceHighWeightedHorizontalAction_finiteCoreSobolevLift hO hD g hg L q δ A p hδ hA F y k
  have hValue (i j : Fin 3) : K (normalizedRaising hF hO hD i
      (referenceWeightedBesselField hO hD g hg L q 1 j
        (fun x => Real.log (referenceRadius δ A p L x))
        (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) y)) =
      sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i (D j y) := by
    have hBessel := coreReferenceWeightedBessel_representative hO hD g hg L q δ A p j hδ hA F r y
    have hNative : normalizedRaising hF hO hD i
        (referenceWeightedBesselField hO hD g hg L q 1 j
          (fun x => Real.log (referenceRadius δ A p L x))
          (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) y) =
        (coreRaising hO hD hF i (G j)).val y := by
      rw [hBessel]
      rfl
    rw [hNative,hInputLift j]
    exact (sphereSobolevAngularCoordinateTranspose_half_finiteCore
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy i (G j)).symm
  simp only [physicalMixedNativeRaising,map_sum,map_smul,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← referenceDensityPrincipalFrameCoefficient_sub_kronecker_eq_physicalMixedFrameCoefficient
    g g2 hg L q y i j,hValue i j]

include hData hcalc τ0 in
lemma referencePhysicalDensity_sigma_double_finiteCore
    (hg : IsAdmissibleMetric g) (g2 : MatrixField) (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (δ A : ℝ) (p : ℕ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (r : FiniteHarmonicAmbientRepresentative hO hD F) (y : R3) (hy : ‖y-y0‖ ≤ ρ) :
    let u := finiteCoreSobolevLift hO hD (3/2 : ℝ) F
    let K := (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)).comp
      (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap
    K (physicalPureAngularRaising hF hO hD g L q δ A p
      (referenceNormalizedPrincipalDifference g g2 L q)
      (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) y) =
    (referenceRadius δ A p L y)⁻¹ • (∑ i : Fin 3, ∑ j : Fin 3,
      (referenceDensityPrincipalFrameCoefficient g g2 L q y i j -
        if i=j then (1 : ℝ) else 0) •
        sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
          (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j (u y))) := by
  intro u K
  have hValue (i j : Fin 3) : K (ambientDoubleRaisingField hF hO hD i j
      (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) y) =
      sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
        (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j (u y)) := by
    have hBessel := coreWeightRaising_eq_ambientRaisingBesselField hO hD hF j F r y
    have hNative : ambientDoubleRaisingField hF hO hD i j
        (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) y =
        (coreRaising hO hD hF i (coreRaising hO hD hF j F)).val y := by
      unfold ambientDoubleRaisingField
      rw [← hBessel]
      rfl
    have hHigh := sphereSobolevAngularCoordinateTranspose_threeHalf_finiteCore hF hO hD F y j
    rw [hNative,hHigh]
    exact (sphereSobolevAngularCoordinateTranspose_half_finiteCore
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy i
      (coreRaising hO hD hF j F)).symm
  rw [referenceDensitySigmaDoubleAngularAction_eq_physicalPureAngularCoefficient_sum
    hF hO hD g g2 hg L q δ A p y (u y)]
  simp only [physicalPureAngularRaising,map_sum,map_smul]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
    congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) =>
      physicalPureAngularCoefficient g L q δ A p
        (referenceNormalizedPrincipalDifference g g2 L q) i j y • z) (hValue i j)))

lemma referencePhysicalDensity_weighted_drift_finiteCore
    (hg : IsAdmissibleMetric g) (g2 : MatrixField)
    (q δ A : ℝ) (p : ℕ) (hδ : 0 < δ) (hA : 0 < A)
    (F : smoothCompactFiniteSphereCore hO hD)
    (r : FiniteHarmonicAmbientRepresentative hO hD F) (y : R3) :
    let R := referenceRadius δ A p L
    let u := finiteCoreSobolevLift hO hD (3/2 : ℝ) F
    let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    let K := (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)).comp
      (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap
    K (normalizedSecondWeightedDriftField hO hD g g2 hg L q δ A p
      (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) y) =
    R y • (∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) •
      J (referenceHighWeightedHorizontalAction g L q R u y i)) := by
  intro R u J K
  have hValue (i : Fin 3) : K
      (referenceWeightedInputField hO hD g hg L q 1 i
        (fun x => Real.log (referenceRadius δ A p L x))
        (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) y) =
      J (referenceHighWeightedHorizontalAction g L q R u y i) := by
    let G := coreReferenceInput hO hD g hg L q δ A p i hδ hA F
    have hAmbient := coreReferenceInput_representative hO hD g hg L q δ A p i hδ hA F r y
    have hHigh := referenceHighWeightedHorizontalAction_finiteCoreSobolevLift hO hD g hg L q δ A p
      hδ hA F y i
    have hHighTyped : referenceHighWeightedHorizontalAction g L q R u y i =
        finiteCoreSobolevLift hO hD (1/2 : ℝ) G y := hHigh
    rw [hAmbient,hHighTyped]
    exact ((sphereSobolevInclusionL_finiteCoreSobolevLift hO hD
      (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) G y).trans
      (finiteCoreSobolevLift_negative_half_eq_zero_inclusion hO hD G y)).symm
  simp only [normalizedSecondWeightedDriftField,map_smul,map_sum]
  apply congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => R y • z)
  exact Finset.sum_congr rfl (fun i _ => congrArg
    (fun z : SphereSobolev (-(1/2 : ℝ)) => normalizedSecondDriftFrameJoint g g2 L i (q,y) • z)
    (hValue i))

include hData hcalc τ0 in
theorem referencePhysicalDensity_principal_drift_finiteCore_eq_nativeU
    (hg : IsAdmissibleMetric g) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (δ A : ℝ) (p : ℕ) (hδ : 0 < δ) (hA : 0 < A)
    (F : smoothCompactFiniteSphereCore hO hD) (y : R3) (hy : ‖y-y0‖ ≤ ρ) :
    let R : R3 → ℝ := referenceRadius δ A p L
    let u : R3 → SphereSobolev (3/2 : ℝ) := finiteCoreSobolevLift hO hD (3/2 : ℝ) F
    let D : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun (k : Fin 3) (x : R3) => referenceHighWeightedHorizontalAction g L q R u x k
    let J : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    let K : SphereL2 →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)).comp
      (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap
    let Ah : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i
    let Al : Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
    let Q : Fin 3 → Fin 3 → ℝ := fun i j : Fin 3 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j
    let sigma : Fin 3 → Fin 3 → ℝ := fun i j : Fin 3 => Q i j-if i=j then (1 : ℝ) else 0
    let b : Fin 3 → ℝ := fun i : Fin 3 => normalizedSecondDriftFrameJoint g g2 L i (q,y)
    let CovD : Fin 3 → Fin 3 → SphereSobolev (-(1/2 : ℝ)) := fun i j : Fin 3 => referenceLowerWeightedHorizontalAction g L q R (D j) y i-
      ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q y
        (referenceMetricGramFrame g L (q,y) i) k j • J (D k y)
    let USigma : SphereSobolev (-(1/2 : ℝ)) := (2 : ℝ) • (∑ i : Fin 3, ∑ j : Fin 3, sigma i j • Al i (D j y))+
      (R y)⁻¹ • (∑ i : Fin 3, ∑ j : Fin 3, sigma i j • Al i (Ah j (u y)))
    let UD : SphereSobolev (-(1/2 : ℝ)) := R y • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • CovD i j)+
      R y • (∑ i : Fin 3, b i • J (D i y))
    K ((nativeU hO hD hF g g2 hg L q δ A p hg2 hδ hA F).val y) = USigma+UD := by
  intro R u D J K Ah Al Q sigma b CovD USigma UD
  let r := coreAmbientRepresentative hO hD F
  let G := representativeAmbient hO hD r
  let hG := contDiff_representativeAmbient hO hD r
  let h := referenceNormalizedPrincipalDifference g g2 L q
  have hCov := referencePhysicalDensity_weighted_covector_finiteCore g L hO hD
    hg g2 q δ A p hδ hA F r y
  have hMix := referencePhysicalDensity_sigma_mixed_finiteCore
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
    hg g2 hreg q hq δ A p hδ hA F r y hy
  have hPure := referencePhysicalDensity_sigma_double_finiteCore
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
    hg g2 hreg q hq δ A p F r y hy
  have hDrift := referencePhysicalDensity_weighted_drift_finiteCore g L hO hD
    hg g2 q δ A p hδ hA F r y
  have hNative : normalizedSecondModelError hF hO hD g g2 hg L q δ A p G hG y =
      (nativeU hO hD hF g g2 hg L q δ A p hg2 hδ hA F).val y :=
    nativeUField_representative hO hD hF g g2 hg L q δ A p hg2 hδ hA F r y
  have hExpand : K (normalizedSecondModelError hF hO hD g g2 hg L q δ A p G hG y) =
      K (referenceWeightedCovectorTrace hO hD g hg L q δ A p h G hG y)+
      K (physicalMixedNativeRaising hF hO hD g hg L q δ A p h G hG y)+
      K (physicalPureAngularRaising hF hO hD g L q δ A p h G hG y)+
      K (normalizedSecondWeightedDriftField hO hD g g2 hg L q δ A p G hG y) := by
    simp only [normalizedSecondModelError,map_add,h]
  have hCombined := (congrArg K hNative).symm.trans hExpand
  have hPair := congrArg₂ (fun a b : SphereSobolev (-(1/2 : ℝ)) => a+b) hCov hMix
  have hTriple := congrArg₂ (fun a b : SphereSobolev (-(1/2 : ℝ)) => a+b) hPair hPure
  have hFour := congrArg₂ (fun a b : SphereSobolev (-(1/2 : ℝ)) => a+b) hTriple hDrift
  have hRegroup {V : Type} [AddCommGroup V] (a b c d : V) :
      a+b+c+d = (b+c)+(a+d) := by abel
  let zCov : SphereSobolev (-(1/2 : ℝ)) := K
    (referenceWeightedCovectorTrace hO hD g hg L q δ A p h G hG y)
  let zMix : SphereSobolev (-(1/2 : ℝ)) := K
    (physicalMixedNativeRaising hF hO hD g hg L q δ A p h G hG y)
  let zPure : SphereSobolev (-(1/2 : ℝ)) := K
    (physicalPureAngularRaising hF hO hD g L q δ A p h G hG y)
  let zDrift : SphereSobolev (-(1/2 : ℝ)) := K
    (normalizedSecondWeightedDriftField hO hD g g2 hg L q δ A p G hG y)
  let vCov : SphereSobolev (-(1/2 : ℝ)) :=
    R y • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • CovD i j)
  let vMix : SphereSobolev (-(1/2 : ℝ)) :=
    (2 : ℝ) • (∑ i : Fin 3, ∑ j : Fin 3, sigma i j • Al i (D j y))
  let vPure : SphereSobolev (-(1/2 : ℝ)) :=
    (R y)⁻¹ • (∑ i : Fin 3, ∑ j : Fin 3, sigma i j • Al i (Ah j (u y)))
  let vDrift : SphereSobolev (-(1/2 : ℝ)) :=
    R y • (∑ i : Fin 3, b i • J (D i y))
  have hStart : K ((nativeU hO hD hF g g2 hg L q δ A p hg2 hδ hA F).val y) =
      zCov+zMix+zPure+zDrift := hCombined
  have hCovTyped : zCov = vCov := hCov
  have hMixTyped : zMix = vMix := hMix
  have hPureTyped : zPure = vPure := by
    simpa only [zPure,vPure,R,u,K,h,G,hG,sigma,Q,Al,Ah] using hPure
  have hDriftTyped : zDrift = vDrift := hDrift
  have hPairTyped : zCov+zMix = vCov+vMix := congrArg₂
    (fun a b : SphereSobolev (-(1/2 : ℝ)) => a+b) hCovTyped hMixTyped
  have hTripleTyped : zCov+zMix+zPure = vCov+vMix+vPure := congrArg₂
    (fun a b : SphereSobolev (-(1/2 : ℝ)) => a+b) hPairTyped hPureTyped
  have hFourTyped : zCov+zMix+zPure+zDrift = vCov+vMix+vPure+vDrift := congrArg₂
    (fun a b : SphereSobolev (-(1/2 : ℝ)) => a+b) hTripleTyped hDriftTyped
  have hOrder : vCov+vMix+vPure+vDrift = (vMix+vPure)+(vCov+vDrift) :=
    hRegroup vCov vMix vPure vDrift
  have hPhysical : (vMix+vPure)+(vCov+vDrift) = USigma+UD := rfl
  calc
    _ = zCov+zMix+zPure+zDrift := hStart
    _ = vCov+vMix+vPure+vDrift := hFourTyped
    _ = (vMix+vPure)+(vCov+vDrift) := hOrder
    _ = USigma+UD := hPhysical

lemma referenceNativeMovingAdjointHighMixedCorrection_finiteCore_split
    (hg : IsAdmissibleMetric g) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (F : smoothCompactFiniteSphereCore hO hD) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (ell : R3 →L[ℝ] ℝ) :
    let u : SphereSobolev (3/2 : ℝ) := finiteCoreSobolevLift hO hD (3/2 : ℝ) F y
    let I : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
    let J : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    let K : SphereL2 →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)).comp
      (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap
    let Ah : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i
    let Al : Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
    let Fh : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) := fun i : Fin 3 => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (3/2 : ℝ) ((q,y),ell) i
    let Fl : Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun i : Fin 3 => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (1/2 : ℝ) ((q,y),ell) i
    let JF : SphereSobolev (-(1/2 : ℝ)) := ∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
      (Al i (I (Fh j u))+J (Fl i (Ah j u)))
    J (referenceNativeMovingAdjointHighMixedCorrection
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 g2 q y ell u) =
      K ((nativeModelRaisingDrift hO hD hF g g2 hg hg2 L q F).val y)+JF := by
  intro u I J K Ah Al Fh Fl JF
  have hPhysical := referenceNativeMovingAdjointHighMixedCorrection_negative_inclusion
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 g2 hreg q hq y hy ell u
  have hA (i : Fin 3) : J (Ah i u) = K ((coreRaising hO hD hF i F).val y) :=
    (congrArg J (sphereSobolevAngularCoordinateTranspose_threeHalf_finiteCore hF hO hD F y i)).trans
      ((sphereSobolevInclusionL_finiteCoreSobolevLift hO hD
        (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (coreRaising hO hD hF i F) y).trans
        (finiteCoreSobolevLift_negative_half_eq_zero_inclusion hO hD
          (coreRaising hO hD hF i F) y))
  have hDrift : (∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) • J (Ah i u)) =
      K ((nativeModelRaisingDrift hO hD hF g g2 hg hg2 L q F).val y) := by
    simp only [nativeModelRaisingDrift,LinearMap.sum_apply,Module.End.mul_apply,coreScalar,
      LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk,Submodule.coe_sum,Finset.sum_apply,
      map_sum,map_smul]
    exact Finset.sum_congr rfl (fun i _ => congrArg
      (fun z : SphereSobolev (-(1/2 : ℝ)) => normalizedSecondDriftFrameJoint g g2 L i (q,y) • z)
      (hA i))
  exact hPhysical.trans ((congrArg (fun v : SphereSobolev (-(1/2 : ℝ)) => JF+v) hDrift).trans
    (add_comm JF (K ((nativeModelRaisingDrift hO hD hF g g2 hg hg2 L q F).val y))))



end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.finiteCoreSobolevLift_negative_half_eq_zero_inclusion
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerWeightedHorizontalAction_finiteCoreSobolevLift
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevAngularCoordinateTranspose_threeHalf_finiteCore
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.normalizedReferenceAngularConnection_finiteCore
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevAngularCoordinateTranspose_half_finiteCore
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceWeightedCovectorSecondField_finiteCore
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceDensityCovariantWeightedSecond_finiteCore
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalDensity_weighted_covector_finiteCore
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalDensity_sigma_mixed_finiteCore
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalDensity_sigma_double_finiteCore
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalDensity_weighted_drift_finiteCore
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalDensity_principal_drift_finiteCore_eq_nativeU
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNativeMovingAdjointHighMixedCorrection_finiteCore_split
