import Calderon.ActualHorizontalSobolevConnection
import Calderon.NativeFiniteHarmonicProductHighRotationGraph
import Calderon.NativeThreeHalfUnitCoefficient
import Calderon.SphereSobolevPartialSumOperator

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
FINITE-HIGH-HORIZONTAL-FIRST-SECTION-EXPANSION-v001.md. Original frame, connection and finite input section. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeHarmonicLiftCompletion NativeThreeHalfCoefficientMultiplier
  SmoothMetricFrame MovingFrameConnection AmbientReferenceCovariantCore

attribute [local irreducible] nativeFiniteHarmonicProductHighRotationL nativeThreeHalfCoefficientMulL
  sphereSobolevInclusionL sphereSobolevPartialSumL referenceMetricGramFrame referenceFrameConnectionCoefficient
  referenceHighHorizontalAction referenceHighHorizontalAngularL

def referenceFiniteHighHorizontalSection
    (g : MatrixField) (L : ℝ) (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (n : ℕ) (q : ℝ) (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (i : Fin 3) :
    SphereSobolev (3/2 : ℝ) :=
  sphereSobolevPartialSumL (3/2 : ℝ) n (fderiv ℝ u y (referenceMetricGramFrame g L (q,y) i)) +
    (1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3,
      referenceFrameConnectionCoefficient g L q y (referenceMetricGramFrame g L (q,y) i) a b •
        nativeFiniteHarmonicProductHighRotationL hcalc hF hO hD τ0 n (unitSphereCoefficientJets 3) a b (u y)

lemma sphereSobolevInclusionL_referenceFiniteHighHorizontalSection
    (g : MatrixField) (L : ℝ) (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (n : ℕ) (q : ℝ) (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (i : Fin 3)
    (hu : DifferentiableAt ℝ u y) :
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (referenceFiniteHighHorizontalSection g L hcalc hF hO hD τ0 n q u y i) =
    referenceHighHorizontalAction g L q
      (fun x => sphereSobolevPartialSumL (3/2 : ℝ) n (u x)) y i := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let P := sphereSobolevPartialSumL (3/2 : ℝ) n
  let e := referenceMetricGramFrame g L (q,y) i
  let Γ : Fin 3 → Fin 3 → ℝ := fun a b => referenceFrameConnectionCoefficient g L q y e a b
  have hDerivative : I (P (fderiv ℝ u y e)) =
      I (fderiv ℝ (fun x => P (u x)) y e) := by
    have hD := congrArg (fun A : R3 →L[ℝ] SphereSobolev (3/2 : ℝ) => I (A e))
      (P.hasFDerivAt.comp y hu.hasFDerivAt).fderiv
    simpa only [Function.comp_def,ContinuousLinearMap.comp_apply] using hD.symm
  have hInput : nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (unitSphereCoefficientJets 3)
      (sphereSobolevPartialSum (3/2 : ℝ) n (u y)) = P (u y) :=
    (congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) =>
      A (sphereSobolevPartialSum (3/2 : ℝ) n (u y)))
      (nativeThreeHalfCoefficientMulL_unitSphereCoefficientJets hcalc hF hO hD τ0)).trans
        (sphereSobolevPartialSumL_apply (3/2 : ℝ) n (u y)).symm
  have hRotation (a b : Fin 3) : I
      (nativeFiniteHarmonicProductHighRotationL hcalc hF hO hD τ0 n (unitSphereCoefficientJets 3) a b (u y)) =
      sphereSobolevRotationL (3/2 : ℝ) a b (P (u y)) :=
    (sphereSobolevInclusionL_nativeFiniteHarmonicProductHighRotationL
      hcalc hF hO hD τ0 n (unitSphereCoefficientJets 3) a b (u y)).trans
      (congrArg (sphereSobolevRotationL (3/2 : ℝ) a b) hInput)
  have hAngular : (1/2 : ℝ) • (∑ a : Fin 3, ∑ b : Fin 3, Γ a b • I
      (nativeFiniteHarmonicProductHighRotationL hcalc hF hO hD τ0 n (unitSphereCoefficientJets 3) a b (u y))) =
      (1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3, Γ a b • sphereSobolevRotationL (3/2 : ℝ) a b (P (u y)) :=
    congrArg (fun z : SphereSobolev (1/2 : ℝ) => (1/2 : ℝ) • z)
      (Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
        congrArg (fun z : SphereSobolev (1/2 : ℝ) => Γ a b • z) (hRotation a b))))
  have hCombined := congrArg₂ (fun z t : SphereSobolev (1/2 : ℝ) => z+t) hDerivative hAngular
  simpa only [referenceFiniteHighHorizontalSection,referenceHighHorizontalAction,referenceHighHorizontalAngularL,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,map_add,map_smul,map_sum,I,P,e,Γ] using hCombined

lemma contDiffAt_referenceFiniteHighHorizontalSection
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (n : ℕ) (q : ℝ) (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (i : Fin 3)
    (hu : ContDiffAt ℝ ∞ u y) :
    ContDiffAt ℝ ∞ (fun x => referenceFiniteHighHorizontalSection g L hcalc hF hO hD τ0 n q u x i) y := by
  have hDerivativeSmooth := (hu.fderiv_right (m := ∞) (by simp)).clm_apply
    (contDiff_referenceMetricGramFrame_slice g hg L q i).contDiffAt
  have hBase := (sphereSobolevPartialSumL (3/2 : ℝ) n).contDiff.contDiffAt.comp y hDerivativeSmooth
  have hAngular : ContDiffAt ℝ ∞ (fun x => (1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3,
      referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) a b •
        nativeFiniteHarmonicProductHighRotationL hcalc hF hO hD τ0 n (unitSphereCoefficientJets 3) a b (u x)) y := by
    apply ContDiffAt.const_smul
    apply ContDiffAt.sum
    intro a ha
    apply ContDiffAt.sum
    intro b hb
    exact (contDiff_referenceFrameConnectionCoefficient_field g hg L q
      (fun x => referenceMetricGramFrame g L (q,x) i)
      (contDiff_referenceMetricGramFrame_slice g hg L q i) a b).contDiffAt.smul
        ((nativeFiniteHarmonicProductHighRotationL hcalc hF hO hD τ0 n (unitSphereCoefficientJets 3) a b).contDiff.contDiffAt.comp y hu)
  unfold referenceFiniteHighHorizontalSection
  exact hBase.add hAngular

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceFiniteHighHorizontalSection
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevInclusionL_referenceFiniteHighHorizontalSection
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceFiniteHighHorizontalSection
