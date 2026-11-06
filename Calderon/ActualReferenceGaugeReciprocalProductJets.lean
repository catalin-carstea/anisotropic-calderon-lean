import Calderon.ActualReferenceGaugeNormalReciprocalRoom
import Calderon.NativeThreeHalfCoefficientProduct

/-! Literal reciprocal-times-frozen-Q before extension. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeThreeHalfCoefficientMultiplier

variable {g : MatrixField} {L : ℝ}
  {Φ : ℝ → (R3 × R3) → ℝ → R3 × R3}
  {a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ}
  {K : Set (ℝ × (R3 × ℝ))}

def productScalar (G : ReferenceGaugeNormalReciprocalRoom g L Φ a K)
    (Q : SmoothCoefficientJets 3) (p : (ℝ × (R3 × ℝ)) × R3) : ℝ :=
  G.scalar p * coefficientValue 3 Q p.2

lemma contDiff_productScalar (G : ReferenceGaugeNormalReciprocalRoom g L Φ a K)
    (Q : SmoothCoefficientJets 3) : ContDiff ℝ ∞ (G.productScalar Q) :=
  G.smooth.mul ((contDiff_coefficientValue 3 Q).comp contDiff_snd)

lemma productScalar_zeroOutside (G : ReferenceGaugeNormalReciprocalRoom g L Φ a K)
    (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ)) (x : R3) (hx : x ∉ G.spatialSupport) :
    G.productScalar Q (p,x) = 0 := by
  unfold productScalar
  rw [G.zeroOutside p x hx,zero_mul]

def productJets (G : ReferenceGaugeNormalReciprocalRoom g L Φ a K) (k : ℕ)
    (Q : SmoothCoefficientJets 3) : (ℝ × (R3 × ℝ)) → SmoothCoefficientJets k :=
  commonSupportCoefficientFamily k (G.productScalar Q) (G.contDiff_productScalar Q)
    G.spatialSupport G.supportCompact (G.productScalar_zeroOutside Q)

lemma coefficientValue_productJets (G : ReferenceGaugeNormalReciprocalRoom g L Φ a K)
    (k : ℕ) (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ)) (x : R3) :
    coefficientValue k (G.productJets k Q p) x = G.scalar (p,x) * coefficientValue 3 Q x :=
  coefficientValue_commonSupportCoefficientFamily k (G.productScalar Q) (G.contDiff_productScalar Q)
    G.spatialSupport G.supportCompact (G.productScalar_zeroOutside Q) p x

lemma nativeThreeHalfCoefficientMulL_productJets
    (G : ReferenceGaugeNormalReciprocalRoom g L Φ a K)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ)) :
    nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (G.productJets 3 Q p) =
      (G.threeHalfMultiplier hcalc hF hO hD τ0 p).comp
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q) := by
  apply (nativeThreeHalfCoefficientMulL_comp_of_value_product
    hcalc hF hO hD τ0 (G.jets 3 p) Q (G.productJets 3 Q p) ?_).symm
  funext x
  exact (G.coefficientValue_productJets 3 Q p x).trans
    (congrArg (fun t : ℝ => t * coefficientValue 3 Q x) (G.coefficientValue_jets 3 p x).symm)

end OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom

#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.productScalar
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.contDiff_productScalar
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.productScalar_zeroOutside
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.productJets
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.coefficientValue_productJets
#print axioms OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom.nativeThreeHalfCoefficientMulL_productJets
