import Calderon.ActualOriginalFiniteSourceL2Graph
import Calderon.ActualEligibleDensityWholeFiniteGraph
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open SphereHarmonic ActualFiniteHarmonicCore WeightedBaseSpectral ReferenceDensityBounds
  SpectralCoreRegularity SpectralWeightedGraph SphereHilbertDecomposition EnergyBridge DirichletFamily
  DirichletFamily.DriftBootstrap ConformalDepth
attribute [local irreducible] nativeDensitySphereL2L sphereSobolevInclusionL sphereSobolevPartialSumL
  harmonicSphereSubspace finiteCoreSobolevLift nativePacketPhysicalDensityOperator

theorem finite_physical_coercive_bound_on_actual_partial_sums
    (hcalc:FixedSobolevCalculus) (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (S:KnownSideSourceData) (L q delta Rstar c:ℝ) (p:ℕ) (cover:NativeNormalCover S L)
    (chi:R3→ℝ) (u:R3→SphereSobolev (3/2:ℝ))
    (hCore:∀ n:ℕ,∃ A:smoothCompactFiniteSphereCore hO hD,
      (∀ y:R3,finiteCoreSobolevLift hO hD (3/2:ℝ) A y=sphereSobolevPartialSumL (3/2:ℝ) n (u y)) ∧
      tsupport (A:R3→SphereL2)⊆tsupport chi ∧ ∀ y:R3,sphereMean ((A:R3→SphereL2) y)=0)
    (F:ℕ→R3→SphereL2)
    (hFData:∀ n:ℕ,ContDiff ℝ ∞ (F n) ∧ HasCompactSupport (F n) ∧ tsupport (F n)⊆tsupport chi ∧
      ∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
        sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (F n y))=
        nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
          (fun z => sphereSobolevPartialSumL (3/2:ℝ) n (u z)) i y)
    (hFinite:∀ A:smoothCompactFiniteSphereCore hO hD,tsupport (A:R3→SphereL2)⊆tsupport chi →
      (∀ y:R3,sphereMean ((A:R3→SphereL2) y)=0) →
      ∀ V:R3→SphereL2,ContDiff ℝ ∞ V → HasCompactSupport V → tsupport V⊆tsupport chi →
      (∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
        sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (V y))=
        nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
          (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y) →
      c*(∫ y,referenceDensityFamily S.g1 L (q,y)*‖(A:R3→SphereL2) y‖^2) ≤
        ∫ y,referenceDensityFamily S.g1 L (q,y)*‖V y‖^2):
    ∀ n:ℕ,c*(∫ y,referenceDensityFamily S.g1 L (q,y)*
      ‖nativeDensitySphereL2L hO hD (sphereSobolevPartialSumL (3/2:ℝ) n (u y))‖^2) ≤
      ∫ y,referenceDensityFamily S.g1 L (q,y)*‖F n y‖^2 := by
  intro n
  obtain ⟨A,hLift,hSupp,hMean⟩ := hCore n
  have hLiftEq:finiteCoreSobolevLift hO hD (3/2:ℝ) A=
      (fun z => sphereSobolevPartialSumL (3/2:ℝ) n (u z)) := funext hLift
  have hGraph:∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (F n y))=
        nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
          (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y := by
    intro i y hy
    exact ((hFData n).2.2.2 i y hy).trans (congrArg (fun v:R3→SphereSobolev (3/2:ℝ) =>
      nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p v i y) hLiftEq.symm)
  have h:=hFinite A hSupp hMean (F n) (hFData n).1 (hFData n).2.1 (hFData n).2.2.1 hGraph
  have hValue:(A:R3→SphereL2)=(fun y => nativeDensitySphereL2L hO hD (sphereSobolevPartialSumL (3/2:ℝ) n (u y))) := by
    funext y
    exact (nativeDensitySphereL2L_finiteCoreSobolevLift hO hD A y).symm.trans
      (congrArg (nativeDensitySphereL2L hO hD) (hLift y))
  simpa only [hValue] using h

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
