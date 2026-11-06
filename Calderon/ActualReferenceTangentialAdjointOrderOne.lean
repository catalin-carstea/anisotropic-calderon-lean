import Calderon.NativeOrderOneCoefficientMultiplierTopology
import Calderon.NativeOrderOneScalarRotationAdjunction
import Calderon.ActualJointReferenceCoefficientData
import Calderon.NativeBoundaryCoefficientFamilies

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeBoundaryCoefficientFamilies
  NativeOrderOneCoefficientMultiplier NativeOrderOneScalarRotationAdjunction

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def tangentRotationCoefficientFunction
    (a : E × R3 → Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) : E × R3 → ℝ :=
  fun p => tangentCoefficientFunction a i p * p.2 j

lemma contDiff_tangentRotationCoefficientFunction
    (a : E × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a) (i j : Fin 3) :
    ContDiff ℝ ∞ (tangentRotationCoefficientFunction a i j) := by
  have hX (k : Fin 3) : ContDiff ℝ ∞ (fun p : E × R3 => p.2 k) :=
    (EuclideanSpace.proj k : R3 →L[ℝ] ℝ).contDiff.comp contDiff_snd
  have hNormal : ContDiff ℝ ∞ (normalCoefficientFunction a) := by
    unfold normalCoefficientFunction
    exact ContDiff.sum fun k hk => ContDiff.sum fun l hl =>
      ((hX k).mul (contDiff_pi.mp (contDiff_pi.mp ha k) l)).mul (hX l)
  have hTangent : ContDiff ℝ ∞ (tangentCoefficientFunction a i) := by
    unfold tangentCoefficientFunction
    exact (ContDiff.sum fun k hk =>
      (hX k).mul (contDiff_pi.mp (contDiff_pi.mp ha k) i)).sub (hNormal.mul (hX i))
  exact hTangent.mul (hX j)

lemma tangentRotationCoefficientFunction_support
    (a : E × R3 → Matrix (Fin 3) (Fin 3) ℝ) (K : Set R3)
    (hz : ∀ p x, x ∉ K → a (p,x) = 0) (i j : Fin 3) (p : E) (x : R3) (hx : x ∉ K) :
    tangentRotationCoefficientFunction a i j (p,x) = 0 := by
  unfold tangentRotationCoefficientFunction tangentCoefficientFunction normalCoefficientFunction
  rw [hz p x hx]
  simp

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
  (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceTangentialOrderOneFamily
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (p : ℝ × (R3 × ℝ)) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  ∑ i : Fin 3, ∑ j : Fin 3, nativeOrderOneScalarRotationL hO hD
    (commonSupportCoefficientFamily 3 (tangentRotationCoefficientFunction a i j)
      (contDiff_tangentRotationCoefficientFunction a
        (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1 i j)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (tangentRotationCoefficientFunction_support a (closedBall (0 : R3) 3)
        (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 i j) p) j i

def referenceTangentialAdjointOrderOneFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  ∑ i : Fin 3, ∑ j : Fin 3, nativeOrderOneScalarRotationAdjointL hcalc hF hO hD τ0
    (commonSupportCoefficientFamily 3 (tangentRotationCoefficientFunction a i j)
      (contDiff_tangentRotationCoefficientFunction a
        (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1 i j)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (tangentRotationCoefficientFunction_support a (closedBall (0 : R3) 3)
        (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 i j) p)
    (commonSupportCoefficientFamily 2 (tangentRotationCoefficientFunction a i j)
      (contDiff_tangentRotationCoefficientFunction a
        (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1 i j)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (tangentRotationCoefficientFunction_support a (closedBall (0 : R3) 3)
        (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 i j) p)
    (coefficientValue_commonSupportCoefficientFamily_order_eq 3 2 (tangentRotationCoefficientFunction a i j)
      (contDiff_tangentRotationCoefficientFunction a
        (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1 i j)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (tangentRotationCoefficientFunction_support a (closedBall (0 : R3) 3)
        (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 i j) p) j i

lemma contDiff_referenceTangentialAdjointOrderOneFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContDiff ℝ ∞ (referenceTangentialAdjointOrderOneFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  unfold referenceTangentialAdjointOrderOneFamily
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  unfold nativeOrderOneScalarRotationAdjointL
  exact (contDiff_const.clm_comp
    (contDiff_nativeOrderOneCoefficientMulL_commonSupport hcalc hF hO hD τ0
      (tangentRotationCoefficientFunction a i j)
      (contDiff_tangentRotationCoefficientFunction a
        (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1 i j)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (tangentRotationCoefficientFunction_support a (closedBall (0 : R3) 3)
        (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 i j))).neg

lemma inner_referenceTangentialOrderOneFamily_adjoint
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (u v : SphereSobolev 1) :
    ⟪(sphereSobolevZeroEquiv hO hD).symm
        (referenceTangentialOrderOneFamily g L y0 Φ B ε C ρ H a w hData hO hD p u),
      (sphereSobolevZeroEquiv hO hD).symm (sphereSobolevInclusionL 1 0 (by norm_num) v)⟫_ℝ =
    ⟪(sphereSobolevZeroEquiv hO hD).symm (sphereSobolevInclusionL 1 0 (by norm_num) u),
      (sphereSobolevZeroEquiv hO hD).symm
        (referenceTangentialAdjointOrderOneFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p v)⟫_ℝ := by
  unfold referenceTangentialOrderOneFamily referenceTangentialAdjointOrderOneFamily
  simp only [ContinuousLinearMap.sum_apply,map_sum,inner_sum, sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact inner_nativeOrderOneScalarRotation_adjoint hcalc hF hO hD τ0 _ _ _ j i u v

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.tangentRotationCoefficientFunction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_tangentRotationCoefficientFunction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.tangentRotationCoefficientFunction_support
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTangentialOrderOneFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTangentialAdjointOrderOneFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceTangentialAdjointOrderOneFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.inner_referenceTangentialOrderOneFamily_adjoint
