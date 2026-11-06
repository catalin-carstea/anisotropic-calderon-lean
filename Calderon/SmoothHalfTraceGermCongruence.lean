import Calderon.NativeFullSharpHalfTrace
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology
namespace OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
open EnergyBridge DirichletFamily SphereHarmonic SpectralWeightedGraph

theorem smoothHalfTrace_eq_of_eventuallyEq_closedBall
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (f g : SmoothData)
    (hNear : ∀ x ∈ closedBall (0 : R3) 1, f.1 =ᶠ[𝓝 x] g.1) :
    smoothHalfTrace hF hO hD τ0 f = smoothHalfTrace hF hO hD τ0 g := by
  have hValue : smoothSphereValue f = smoothSphereValue g := by
    ext x
    have hx : x.val ∈ closedBall (0 : R3) 1 := sphere_subset_closedBall x.property
    exact (hNear x.val hx).eq_of_nhds
  apply sphereSobolev_ext (1/2 : ℝ)
  intro k
  rw [sphereSobolevCoefficientL_smoothHalfTrace,sphereSobolevCoefficientL_smoothHalfTrace,
    τ0.valueTrace_smooth,τ0.valueTrace_smooth,hValue]

end OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
#print axioms OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion.smoothHalfTrace_eq_of_eventuallyEq_closedBall
