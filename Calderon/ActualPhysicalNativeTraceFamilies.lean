import Calderon.NativeSmoothBallSobolevFamily
import Calderon.ActualPhysicalBoundaryChainRule
import Calderon.NativeH2ThreeHalfValueTrace

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
ACTUAL-PHYSICAL-NATIVE-TRACE-FAMILY-EXPANSION-v001.md. Same physical pullback and native trace. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeH2ThreeHalfValueTrace ConnectionError

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3))
  (hEnd : ConformalReferenceGeodesicEndpointData g L y0 Φ B)

theorem contDiff_referencePhysicalPullback_smoothBallSobolev
    (hcalc : FixedSobolevCalculus) (k : ℕ) (u : SmoothData) :
    ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) => smoothBallSobolev k
      (referencePhysicalPullbackData g hg L y0 Φ B hEnd p.1 p.2.1 p.2.2 u)) := by
  let G : (ℝ × (R3 × ℝ)) × R3 → ℝ := fun pz =>
    u.1 (referenceFramedPhysicalEndpoint g L Φ (pz.1.1,(pz.1.2,pz.2)))
  have hTheta : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hEnd.2.2.2.2.2.2.2.1
  have hG : ContDiff ℝ ∞ G := u.2.comp
    ((contDiff_referenceFramedPhysicalEndpoint g hg L Φ hTheta).comp
      (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd)))
  have hEqual : (fun p => smoothBallSobolev k
      ⟨fun z => G (p,z), SpatialJetFields.contDiff_spatial_slice G hG p⟩) =
      (fun p : ℝ × (R3 × ℝ) => smoothBallSobolev k
        (referencePhysicalPullbackData g hg L y0 Φ B hEnd p.1 p.2.1 p.2.2 u)) := by
    funext p
    rfl
  rw [← hEqual]
  exact contDiff_smoothBallSobolev_of_joint hcalc k G hG

theorem contDiff_referencePhysicalNativeThreeHalfTrace
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (u : SmoothData) :
    ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) =>
      nativeThreeHalfValueTraceL hcalc hF hO hD τ0
        (smoothBallSobolev 2
          (referencePhysicalPullbackData g hg L y0 Φ B hEnd p.1 p.2.1 p.2.2 u))) := by
  exact (nativeThreeHalfValueTraceL hcalc hF hO hD τ0).contDiff.comp
    (contDiff_referencePhysicalPullback_smoothBallSobolev g hg L y0 Φ B hEnd hcalc 2 u)

attribute [local irreducible] nativeThreeHalfValueTraceL smoothBallSobolev referencePhysicalPullbackData

theorem contDiffAt_referenceMovingPhysicalNativeThreeHalfTrace
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (q : ℝ) (R : R3 → ℝ) (y : R3)
    (u : SmoothData) (hR : ContDiffAt ℝ ∞ R y) :
    ContDiffAt ℝ ∞ (fun x : R3 =>
      nativeThreeHalfValueTraceL hcalc hF hO hD τ0
        (smoothBallSobolev 2
          (referencePhysicalPullbackData g hg L y0 Φ B hEnd q x (R x) u))) y := by
  trace "moving physical native trace: proof entered"
  let F : (ℝ × (R3 × ℝ)) → SphereSobolev (3/2 : ℝ) := fun p =>
    nativeThreeHalfValueTraceL hcalc hF hO hD τ0
      (smoothBallSobolev 2
        (referencePhysicalPullbackData g hg L y0 Φ B hEnd p.1 p.2.1 p.2.2 u))
  let T : R3 → ℝ × (R3 × ℝ) := fun x => (q,(x,R x))
  have hFactual : ContDiff ℝ ∞ F :=
    contDiff_referencePhysicalNativeThreeHalfTrace g hg L y0 Φ B hEnd hcalc hF hO hD τ0 u
  have hT : ContDiffAt ℝ ∞ T y :=
    contDiffAt_const.prodMk (contDiffAt_id.prodMk hR)
  trace "moving physical native trace: typed factors"
  have hComp : ContDiffAt ℝ ∞ (F ∘ T) y := hFactual.contDiffAt.comp y hT
  trace "moving physical native trace: composed"
  exact hComp

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referencePhysicalPullback_smoothBallSobolev
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referencePhysicalNativeThreeHalfTrace
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceMovingPhysicalNativeThreeHalfTrace
