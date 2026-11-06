import Calderon.NativeCoefficientRotationProductRule
import Calderon.SphereSobolevTangentialEndpointCompatibility
import Calderon.ActualReferenceLowerBoundaryTranspose

/-! The right multiplier graph stays explicit. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap NativeCoefficientBoundaryMultiplier
  NativeHalfSmoothMultiplier

variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

lemma nativeHalfCoefficientMulL_comm_apply
    (F G : SmoothCoefficientJets 2) (u : SphereSobolev (1/2 : ℝ)) :
    nativeHalfCoefficientMulL hcalc hF hO hD τ0 F
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 G u) =
    nativeHalfCoefficientMulL hcalc hF hO hD τ0 G
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 F u) := by
  let I : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev 0 :=
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let Z : SphereL2 ≃ₗᵢ[ℝ] SphereSobolev 0 := sphereSobolevZeroEquiv hO hD
  let M (Q : SmoothCoefficientJets 2) : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    nativeHalfCoefficientMulL hcalc hF hO hD τ0 Q
  let C (Q : SmoothCoefficientJets 2) : SphereL2 →L[ℝ] SphereL2 :=
    sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData Q))
  let v : SphereL2 := Z.symm (I u)
  have hValue (Q : SmoothCoefficientJets 2) (w : SphereSobolev (1/2 : ℝ)) :
      I (M Q w) = Z (C Q (Z.symm (I w))) :=
    sphereSobolevInclusionL_nativeHalfCoefficientMulL_value hcalc hF hO hD τ0 Q w
  have hPair (Q K : SmoothCoefficientJets 2) :
      I (M Q (M K u)) = Z (C Q (C K v)) :=
    (hValue Q (M K u)).trans
      ((congrArg (fun z : SphereSobolev 0 => Z (C Q (Z.symm z))) (hValue K u)).trans
        (congrArg (fun w : SphereL2 => Z (C Q w)) (Z.symm_apply_apply (C K v))))
  have hComm : C F (C G v) = C G (C F v) :=
    sphereContinuousScalarMulL_comm_apply
      (smoothSphereValue (coefficientSmoothData F)) (smoothSphereValue (coefficientSmoothData G)) v
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) 0 (by norm_num)
  exact (hPair F G).trans ((congrArg Z hComm).trans (hPair G F).symm)

lemma nativeNegativeHalfCoefficientMulL_comm_apply
    (F G : SmoothCoefficientJets 2) (u : SphereSobolev (-(1/2 : ℝ))) :
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F
      (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 G u) =
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 G
      (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F u) := by
  have hComm : (nativeHalfCoefficientMulL hcalc hF hO hD τ0 F).comp
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 G) =
    (nativeHalfCoefficientMulL hcalc hF hO hD τ0 G).comp
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 F) :=
    ContinuousLinearMap.ext (nativeHalfCoefficientMulL_comm_apply hcalc hF hO hD τ0 F G)
  have hAdj := congrArg
    (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => ContinuousLinearMap.adjoint A) hComm
  simp only [ContinuousLinearMap.adjoint_comp] at hAdj
  exact congrArg
    (fun A : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A u) hAdj.symm

lemma sphereLowerDistributionalTranspose_comp_nativeHalfCoefficientMulL
    (A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (G : SmoothCoefficientJets 2) :
    sphereLowerDistributionalTranspose (A.comp (nativeHalfCoefficientMulL hcalc hF hO hD τ0 G)) =
      (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 G).comp (sphereLowerDistributionalTranspose A) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolev_eq_of_dualPairing_eq (1/2 : ℝ)
  intro v
  have h1 := sphereSobolevDualPairing_lower_distributionalTranspose
    (A.comp (nativeHalfCoefficientMulL hcalc hF hO hD τ0 G)) v u
  have h2 := sphereSobolevDualPairing_lower_distributionalTranspose A
    (nativeHalfCoefficientMulL hcalc hF hO hD τ0 G v) u
  have h3 : sphereSobolevDualPairing (1/2 : ℝ) v
      (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 G (sphereLowerDistributionalTranspose A u)) =
    sphereSobolevDualPairing (1/2 : ℝ)
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 G v) (sphereLowerDistributionalTranspose A u) := by
    exact ContinuousLinearMap.adjoint_inner_right
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 G) v (sphereLowerDistributionalTranspose A u)
  exact h1.symm.trans (h2.trans h3.symm)

def nativeLowerRightMultiplierSkewPart
    (A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (G : SmoothCoefficientJets 2) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  A.comp (nativeHalfCoefficientMulL hcalc hF hO hD τ0 G) -
    sphereLowerDistributionalTranspose (A.comp (nativeHalfCoefficientMulL hcalc hF hO hD τ0 G))

lemma sphereSobolevDualPairing_nativeLowerRightMultiplierSkewPart
    (A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (G : SmoothCoefficientJets 2) (u v : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevDualPairing (1/2 : ℝ) v
      (nativeLowerRightMultiplierSkewPart hcalc hF hO hD τ0 A G u) =
    -sphereSobolevDualPairing (1/2 : ℝ) u
      (nativeLowerRightMultiplierSkewPart hcalc hF hO hD τ0 A G v) := by
  have h1 := sphereSobolevDualPairing_lower_distributionalTranspose
    (A.comp (nativeHalfCoefficientMulL hcalc hF hO hD τ0 G)) u v
  have h2 := sphereSobolevDualPairing_lower_distributionalTranspose
    (A.comp (nativeHalfCoefficientMulL hcalc hF hO hD τ0 G)) v u
  simp only [nativeLowerRightMultiplierSkewPart,ContinuousLinearMap.sub_apply,
    sphereSobolevDualPairing,inner_sub_right] at h1 h2 ⊢
  linarith

def nativeCoefficientRotationFieldL (F : Fin 3 → Fin 3 → SmoothCoefficientJets 2) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (F i j)).comp
      (sphereSobolevRotationL (1/2 : ℝ) j i)

lemma nativeCoefficientRotationField_commutator_nativeMultiplier
    (F : Fin 3 → Fin 3 → SmoothCoefficientJets 2) (G : SmoothCoefficientJets 2)
    (H : Fin 3 → Fin 3 → SmoothCoefficientJets 2)
    (hH : ∀ i j (x : UnitSphere), coefficientValue 2 (H i j) x.val =
      SmoothSphereRotation.sphereRotationDerivative j i (coefficientValue 2 G) x.val) :
    (nativeCoefficientRotationFieldL hcalc hF hO hD τ0 F).comp
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 G) -
    (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 G).comp
      (nativeCoefficientRotationFieldL hcalc hF hO hD τ0 F) =
    (∑ i : Fin 3, ∑ j : Fin 3,
      (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (F i j)).comp
        (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (H i j))).comp
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)) := by
  let M : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    nativeHalfCoefficientMulL hcalc hF hO hD τ0 G
  let N (Q : SmoothCoefficientJets 2) : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 Q
  let R (i j : Fin 3) : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevRotationL (1/2 : ℝ) j i
  let I : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let V : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    nativeCoefficientRotationFieldL hcalc hF hO hD τ0 F
  have hField (v : SphereSobolev (1/2 : ℝ)) : V v =
      ∑ i : Fin 3, ∑ j : Fin 3, N (F i j) (R i j v) := by
    unfold V nativeCoefficientRotationFieldL
    simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply]
    dsimp only [N,R]
  apply ContinuousLinearMap.ext
  intro u
  let x (i j : Fin 3) : SphereSobolev (-(1/2 : ℝ)) := N (F i j) (R i j (M u))
  let y (i j : Fin 3) : SphereSobolev (-(1/2 : ℝ)) := N G (N (F i j) (R i j u))
  let z (i j : Fin 3) : SphereSobolev (-(1/2 : ℝ)) := N (F i j) (N (H i j) (I u))
  have hTerm (i j : Fin 3) : x i j - y i j = z i j := by
    have hp : R i j (M u) = N G (R i j u) + N (H i j) (I u) :=
      congrArg (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T u)
        (sphereSobolevRotationL_nativeCoefficient_product_rule hcalc hF hO hD τ0 G (H i j) j i (hH i j))
    have hc : N (F i j) (N G (R i j u)) = N G (N (F i j) (R i j u)) :=
      nativeNegativeHalfCoefficientMulL_comm_apply hcalc hF hO hD τ0 (F i j) G (R i j u)
    have hExpand : x i j = y i j + z i j :=
      (congrArg (N (F i j)) hp).trans
        (((N (F i j)).map_add (N G (R i j u)) (N (H i j) (I u))).trans
          (congrArg (fun w : SphereSobolev (-(1/2 : ℝ)) => w + z i j) hc))
    exact (congrArg (fun w : SphereSobolev (-(1/2 : ℝ)) => w-y i j) hExpand).trans
      (by abel)
  have hLeft : V (M u) - N G (V u) =
      (∑ i : Fin 3, ∑ j : Fin 3, x i j) - ∑ i : Fin 3, ∑ j : Fin 3, y i j := by
    have hMap : N G (∑ i : Fin 3, ∑ j : Fin 3, N (F i j) (R i j u)) =
        ∑ i : Fin 3, ∑ j : Fin 3, y i j := by
      simp only [map_sum]
      dsimp only [y]
    exact congrArg₂ (fun v w : SphereSobolev (-(1/2 : ℝ)) => v-w)
      (hField (M u)) ((congrArg (N G) (hField u)).trans hMap)
  have hSum : ((∑ i : Fin 3, ∑ j : Fin 3, x i j) - ∑ i : Fin 3, ∑ j : Fin 3, y i j) =
      ∑ i : Fin 3, ∑ j : Fin 3, z i j := by
    calc
      _ = ∑ i : Fin 3, ((∑ j : Fin 3, x i j) - ∑ j : Fin 3, y i j) :=
        (Finset.sum_sub_distrib
          (fun i : Fin 3 => ∑ j : Fin 3, x i j)
          (fun i : Fin 3 => ∑ j : Fin 3, y i j)).symm
      _ = ∑ i : Fin 3, ∑ j : Fin 3, (x i j-y i j) :=
        Finset.sum_congr rfl (fun i hi =>
          (Finset.sum_sub_distrib (fun j : Fin 3 => x i j) (fun j : Fin 3 => y i j)).symm)
      _ = ∑ i : Fin 3, ∑ j : Fin 3, z i j :=
        Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => hTerm i j))
  have hRight : ((∑ i : Fin 3, ∑ j : Fin 3, (N (F i j)).comp (N (H i j))).comp I) u =
      ∑ i : Fin 3, ∑ j : Fin 3, z i j := by
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.sum_apply]
    dsimp only [z]
  exact hLeft.trans (hSum.trans hRight.symm)

lemma nativeLowerRightMultiplier_defect_eq_skew_add_commutator
    (A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (Z : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (G : SmoothCoefficientJets 2)
    (hAt : sphereLowerDistributionalTranspose A = -A-Z.comp
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)))
    (hCommZ : ∀ u : SphereSobolev (-(1/2 : ℝ)),
      Z (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 G u) =
        nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 G (Z u)) :
    (A-sphereLowerDistributionalTranspose A).comp
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 G) =
    nativeLowerRightMultiplierSkewPart hcalc hF hO hD τ0 A G +
      (A.comp (nativeHalfCoefficientMulL hcalc hF hO hD τ0 G)-
        (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 G).comp A) := by
  let P : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    nativeHalfCoefficientMulL hcalc hF hO hD τ0 G
  let N : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 G
  let I : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := sphereLowerDistributionalTranspose A
  have hAtValue (v : SphereSobolev (1/2 : ℝ)) : T v = -A v-Z (I v) :=
    congrArg (fun K : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => K v) hAt
  have hTrans : sphereLowerDistributionalTranspose (A.comp P) = N.comp T :=
    sphereLowerDistributionalTranspose_comp_nativeHalfCoefficientMulL hcalc hF hO hD τ0 A G
  apply ContinuousLinearMap.ext
  intro u
  let a : SphereSobolev (-(1/2 : ℝ)) := A (P u)
  let b : SphereSobolev (-(1/2 : ℝ)) := N (A u)
  let z : SphereSobolev (-(1/2 : ℝ)) := N (Z (I u))
  have hIp : I (P u) = N (I u) :=
    congrArg (fun K : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => K u)
      (nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0 G)
  have hZ : Z (I (P u)) = z := (congrArg Z hIp).trans (hCommZ (I u))
  have hTP : T (P u) = -a-z :=
    (hAtValue (P u)).trans (congrArg (fun v : SphereSobolev (-(1/2 : ℝ)) => -a-v) hZ)
  have hNT : N (T u) = -b-z :=
    (congrArg N (hAtValue u)).trans
      ((N.map_sub (-A u) (Z (I u))).trans
        (congrArg (fun v : SphereSobolev (-(1/2 : ℝ)) => v-z) (N.map_neg (A u))))
  have hSkew : nativeLowerRightMultiplierSkewPart hcalc hF hO hD τ0 A G u = a-N (T u) := by
    have ht : sphereLowerDistributionalTranspose (A.comp P) u = N (T u) :=
      congrArg (fun K : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => K u) hTrans
    exact congrArg (fun v : SphereSobolev (-(1/2 : ℝ)) => a-v) ht
  have hSkewValue : nativeLowerRightMultiplierSkewPart hcalc hF hO hD τ0 A G u = a-(-b-z) :=
    hSkew.trans (congrArg (fun v : SphereSobolev (-(1/2 : ℝ)) => a-v) hNT)
  have hL : ((A-T).comp P) u = a-(-a-z) :=
    congrArg (fun v : SphereSobolev (-(1/2 : ℝ)) => a-v) hTP
  have hR : (nativeLowerRightMultiplierSkewPart hcalc hF hO hD τ0 A G +
      (A.comp P-N.comp A)) u = (a-(-b-z))+(a-b) :=
    congrArg (fun v : SphereSobolev (-(1/2 : ℝ)) => v+(a-b)) hSkewValue
  have hAlg : a-(-a-z) = (a-(-b-z))+(a-b) := by abel
  exact hL.trans (hAlg.trans hR.symm)

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.nativeHalfCoefficientMulL_comm_apply
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.nativeNegativeHalfCoefficientMulL_comm_apply
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereLowerDistributionalTranspose_comp_nativeHalfCoefficientMulL
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.nativeLowerRightMultiplierSkewPart
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevDualPairing_nativeLowerRightMultiplierSkewPart
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.nativeCoefficientRotationFieldL
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.nativeCoefficientRotationField_commutator_nativeMultiplier
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.nativeLowerRightMultiplier_defect_eq_skew_add_commutator
