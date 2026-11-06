-- PRIVATE WORKING; exact witness code approved by Root.         
-- Complete independent witness argument; no physical-coercivity proof.
-- No native/semantic/final grant; Root owns later checks.         
import Calderon.ActualNativeValueTraceExistence
import Calderon.CollaboratorUnitBallValueTraceKernelOct17
import Calderon.ActualFullEPhysicalEndpoints
import Calderon.ActualChosenCoverFiniteCoercivityGlobalMain

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask.MainPhysicalCoercivityAssembly
open Set Metric MeasureTheory
open scoped ContDiff Topology
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ActualFullEGainedAssembly

-- WITNESS SELECTION ONLY, independent of unfinished T/S and U/S integration.
-- The same tau0 and the same function of (S,L,cover) serve both ordered directions.
theorem exists_native_trace_and_cover_endpoint_rooms :
    ∃ tau0 : UnitBallValueTrace, UnitBallValueTraceKernel tau0 ∧
    ∀ (S : KnownSideSourceData) (L : ℝ), 0 < L →
    ∀ cover : NativeNormalCover S L,
    ∃ Rooms : ∀ i : Fin cover.count,
      OAI.AnisotropicCalderon.ConnectionError.ReferenceGaugeNormalReciprocalRoom S.g1 L (cover.packet i).Phi (cover.packet i).a
        (Icc (0 : ℝ) 1 ×ˢ (closedBall (cover.packet i).y0 (cover.packet i).rho ×ˢ
          Icc (-(cover.packet i).rho) (cover.packet i).rho)),
    Nonempty (∀ i : Fin cover.count,
      FullEPhysicalEndpointRoom S.g1 L (cover.packet i).y0 (cover.packet i).Phi
        (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
        (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
        S.g1_admissible fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
        denseSphereHarmonics tau0 (Rooms i) fixedDirichletRegularity) := by
  classical
  obtain ⟨tau0⟩ := OAI.AnisotropicCalderon.MixedKernelConstructionTask.nonempty_unitBallValueTrace
  have hKernel : UnitBallValueTraceKernel tau0 := DirichletFamily.unitBallValueTraceKernel tau0
  refine ⟨tau0,hKernel,?_⟩
  intro S L hL cover
  have hPacket (i : Fin cover.count) := exists_actual_fullE_physical_endpoint_room
    S.g1 L (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B
    (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
    (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
    S.g1_admissible fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
    denseSphereHarmonics tau0 hL fixedDirichletRegularity hKernel
  let Rooms := fun i : Fin cover.count => Classical.choose (hPacket i)
  refine ⟨Rooms,?_⟩
  exact ⟨fun i => Classical.choice (Classical.choose_spec (hPacket i))⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask.MainPhysicalCoercivityAssembly
