import Calderon.ActualWholeCoverFinitePhysicalOutputGraph
import Calderon.ActualOriginalFiniteSourceL2Graph
import Calderon.ActualNativeOutputCompression
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open SphereHarmonic SpectralCoreRegularity ActualFiniteHarmonicCore
  EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap ConformalDepth
attribute [local irreducible] sphereSobolevInclusionL finiteCoreSobolevLift nativePacketPhysicalDensityOperator

theorem sphereSobolevInclusionL_finiteCoreSobolevLift_fiveHalf
    (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (A:smoothCompactFiniteSphereCore hO hD) (y:R3):
    sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
      (finiteCoreSobolevLift hO hD (5/2:ℝ) A y)=
      finiteCoreSobolevLift hO hD (3/2:ℝ) A y := by
  apply sphereSobolevInclusionL_injective (3/2:ℝ) 0 (by norm_num)
  have hTrans:=congrArg (fun T:SphereSobolev (5/2:ℝ)→L[ℝ] SphereSobolev 0=>
      T (finiteCoreSobolevLift hO hD (5/2:ℝ) A y))
    (sphereSobolevInclusionL_trans (5/2:ℝ) (3/2:ℝ) 0 (by norm_num) (by norm_num))
  have h5: sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num)
      (finiteCoreSobolevLift hO hD (5/2:ℝ) A y)=sphereSobolevZeroEquiv hO hD ((A:R3→SphereL2) y):=
    (finiteCoreSobolevLift_representation hO hD (5/2:ℝ) (by norm_num) A).2.2.2.1 y
  have h3:sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num)
      (finiteCoreSobolevLift hO hD (3/2:ℝ) A y)=sphereSobolevZeroEquiv hO hD ((A:R3→SphereL2) y):=
    (finiteCoreSobolevLift_representation hO hD (3/2:ℝ) (by norm_num) A).2.2.2.1 y
  exact hTrans.trans (h5.trans h3.symm)


theorem exists_native_cover_uniform_finite_core_physical_outputs
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (hKernel:UnitBallValueTraceKernel tau0)
    (S:KnownSideSourceData) (L:ℝ) (hL:0 < L) (cover:NativeNormalCover S L)
    (hCenter:∀ i:Fin cover.count,∀ y∈(cover.packet i).centers,‖y-(cover.packet i).y0‖ < (cover.packet i).rho):
    ∃ p0:ℕ,2 ≤ p0 ∧ ∃ eps0:ℝ,0 < eps0 ∧ eps0 ≤ 1 ∧
      ∀ p:ℕ,p0 ≤ p → ∀ q∈Icc (0:ℝ) cover.dilationCeiling,
      ∀ delta:ℝ,0 < delta → delta ≤ 1 → ∀ Rstar:ℝ,0 < Rstar →
      ∀ eps:ℝ,0 ≤ eps → eps ≤ eps0 → CurrentRadiusBootstrap S L q delta Rstar eps p →
      (∀ y∈cylinder,referenceRadius delta Rstar p L y < cover.radiusCeiling) ∧
      ∀ A:smoothCompactFiniteSphereCore hO hD,tsupport (A:R3→SphereL2)⊆interior cylinder →
      ∃ f:R3→SphereL2,ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f⊆tsupport (A:R3→SphereL2) ∧
        ∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
          sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (f y))=
          nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
            (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y := by
  obtain ⟨p0,hp0,eps0,heps0,heps01,H⟩:=exists_native_cover_uniform_actual_whole_finite_physical_graph
    hcalc hreg hF hO hD tau0 hKernel S L hL cover hCenter
  refine ⟨p0,hp0,eps0,heps0,heps01,?_⟩
  intro p hp q hq delta hd hd1 Rstar hRs eps heps heps0' hBoot
  obtain ⟨hRadius,HGraph⟩:=H p hp q hq delta hd hd1 Rstar hRs eps heps heps0' hBoot
  refine ⟨hRadius,?_⟩
  intro A hSupp
  let u:=finiteCoreSobolevLift hO hD (5/2:ℝ) A
  have hU:=finiteCoreSobolevLift_representation hO hD (5/2:ℝ) (by norm_num) A
  have hU0:tsupport u⊆tsupport (A:R3→SphereL2):=hU.2.2.1
  have hLow:(fun y=>sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (u y))=
      finiteCoreSobolevLift hO hD (3/2:ℝ) A:=by
    funext y
    exact sphereSobolevInclusionL_finiteCoreSobolevLift_fiveHalf hO hD A y
  have hOut:=HGraph u hU.1 hU.2.1 (hU0.trans hSupp)
  dsimp only at hOut
  obtain ⟨F,f,_hF,hf,hfc,hfs,hfg,_hLimit⟩:=hOut
  refine ⟨f,hf,hfc,hfs.trans hU0,?_⟩
  intro i y hy
  exact (hfg i y hy).trans (congrArg (fun v:R3→SphereSobolev (3/2:ℝ)=>
    nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p v i y) hLow)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
