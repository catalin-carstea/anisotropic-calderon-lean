import Calderon.ActualFinitePhysicalCoreCoercivity
import Calderon.ActualOriginalDensityNormFromPhysicalGraph
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
  harmonicSphereSubspace finiteCoreSobolevLift nativePacketPhysicalDensityOperator referenceBaseLift

theorem exists_original_density_norm_bound_of_actual_finite_physical_graph
    (hcalc:FixedSobolevCalculus) (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (S:KnownSideSourceData) (L:ℝ) (cover:NativeNormalCover S L):
    ∃ C:ℝ,0 < C ∧ ∀ q∈Icc (0:ℝ) cover.dilationCeiling,
      ∀ (delta Rstar c D:ℝ) (p:ℕ),0 < c →
      ∀ (chi:R3→ℝ) (hchi:ContDiff ℝ ∞ chi) (hchic:HasCompactSupport chi), tsupport chi⊆interior cylinder → range chi⊆Icc (0:ℝ) 1 →
      ∀ (Psi:R3→SphereSobolev (3/2:ℝ)) (hPsi:ContDiff ℝ ∞ Psi),
      ∀ (U5:R3→SphereSobolev (5/2:ℝ)),ContDiff ℝ ∞ U5 → HasCompactSupport U5 →
      (fun y => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U5 y))=normalizedThreeHalfSourceField chi Psi →
      ∀ (F:ℕ→R3→SphereL2) (f:R3→SphereL2) (hf:ContDiff ℝ ∞ f) (hfc:HasCompactSupport f),
      ‖referenceBaseLift S.g1 S.g1_admissible L q f hf.continuous hfc‖ ≤ D →
      Tendsto (fun n:ℕ => ∫ y,referenceDensityFamily S.g1 L (q,y)*‖F n y-f y‖^2) atTop (𝓝 0) →
      (∀ n:ℕ,∃ A:smoothCompactFiniteSphereCore hO hD,
      (∀ y:R3,finiteCoreSobolevLift hO hD (3/2:ℝ) A y=sphereSobolevPartialSumL (3/2:ℝ) n (normalizedThreeHalfSourceField chi Psi y)) ∧
      tsupport (A:R3→SphereL2)⊆tsupport chi ∧ ∀ y:R3,sphereMean ((A:R3→SphereL2) y)=0) →
      (∀ n:ℕ,ContDiff ℝ ∞ (F n) ∧ HasCompactSupport (F n) ∧ tsupport (F n)⊆tsupport chi ∧
      ∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
        sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (F n y))=
        nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
          (fun z => sphereSobolevPartialSumL (3/2:ℝ) n (normalizedThreeHalfSourceField chi Psi z)) i y) →
      (∀ A:smoothCompactFiniteSphereCore hO hD,tsupport (A:R3→SphereL2)⊆tsupport chi →
      (∀ y:R3,sphereMean ((A:R3→SphereL2) y)=0) →
      ∀ V:R3→SphereL2,ContDiff ℝ ∞ V → HasCompactSupport V → tsupport V⊆tsupport chi →
      (∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
        sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (V y))=
        nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
          (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y) →
      c*(∫ y,referenceDensityFamily S.g1 L (q,y)*‖(A:R3→SphereL2) y‖^2) ≤
        ∫ y,referenceDensityFamily S.g1 L (q,y)*‖V y‖^2) →
      ‖referenceBaseLift S.g1 S.g1_admissible L q (fun y => chi y • nativeDensitySphereL2L hO hD (Psi y))
        (hchi.continuous.smul ((nativeDensitySphereL2L hO hD).continuous.comp hPsi.continuous)) hchic.smul_right‖ ≤ D/Real.sqrt c+C := by
  obtain ⟨C,hC,HC⟩ := exists_uniform_original_density_norm_bound_of_finite_physical_graph hO hD S.g1 S.g1_admissible L 3
  refine ⟨C,hC,?_⟩
  intro q hq delta Rstar c D p hc chi hchi hchic hSupp hRange Psi hPsi U5 hU5 hU5c hEq F f hf hfc hNorm hOutput hCore hFData hFinite
  let u:R3→SphereSobolev (3/2:ℝ) := normalizedThreeHalfSourceField chi Psi
  let T:SphereSobolev (3/2:ℝ)→L[ℝ] SphereL2 := nativeDensitySphereL2L hO hD
  have hCoreSaved:=hCore
  choose A hLift hASupp hMean using hCore
  let Us:ℕ→R3→SphereL2 := fun n => (A n:R3→SphereL2)
  have hUs (n:ℕ):Continuous (Us n) := (A n).property.1.continuous
  have hUsc (n:ℕ):HasCompactSupport (Us n) := (A n).property.2.1
  have hValue (n:ℕ):Us n=(fun y => T (sphereSobolevPartialSumL (3/2:ℝ) n (u y))) := by
    funext y
    exact (nativeDensitySphereL2L_finiteCoreSobolevLift hO hD (A n) y).symm.trans
      (congrArg T (hLift n y))
  have hSource:=tendsto_weighted_nativeDensitySphereL2L_partialSum_of_fiveHalf
    S.g1 S.g1_admissible L q hO hD U5 hU5 hU5c u hEq
  have hSource':Tendsto (fun n:ℕ => ∫ y,referenceDensityFamily S.g1 L (q,y)*
      ‖Us n y-chi y • (T (Psi y)-T (sphereSobolevConstantOne (3/2:ℝ)))‖^2) atTop (𝓝 0) := by
    simpa only [hValue,T,u,nativeDensitySphereL2L_normalized_source] using hSource
  have hFiniteAll:=finite_physical_coercive_bound_on_actual_partial_sums hcalc hF hO hD tau0 S L q delta Rstar c p cover
    chi u hCoreSaved F hFData hFinite
  have hFiniteUs:∀ n:ℕ,c*(∫ y,referenceDensityFamily S.g1 L (q,y)*‖Us n y‖^2) ≤
      ∫ y,referenceDensityFamily S.g1 L (q,y)*‖F n y‖^2 := by
    intro n
    simpa only [hValue,T] using hFiniteAll n
  have hBall:tsupport chi⊆closedBall (0:R3) 3 := by
    intro y hy
    rw [mem_closedBall_zero_iff]
    exact (norm_le_two_of_mem_cylinder y (interior_subset (hSupp hy))).trans (by norm_num)
  exact HC q ⟨hq.1,hq.2.trans cover.dilation_le_one⟩ chi hchi.continuous hchic hBall hRange Psi hPsi.continuous
    f hf.continuous hfc c D hc hNorm Us F hUs hUsc (fun n => (hFData n).1.continuous)
    (fun n => (hFData n).2.1) hSource' hOutput hFiniteUs

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
